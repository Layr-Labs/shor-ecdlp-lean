import ShorECDLP.Submission.Entrant.MainA

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! Merged corner writes for C and its negation: one shared table traversal per addition (see the submission note).
Record-shift transport, in-place corner semantics, scratch-level row and ledgers. -/


/-! Record-shift transport.

If a reference program `A ++ B ++ C₀ ++ pad(n) ++ E` has the same final state for every record
list, and a block `B'` agrees with `B` (for every record list) on every state reachable after `A`,
then `A ++ B' ++ C₀ ++ pad(n') ++ E` has that same final state for every record list. The padding
wire is shown clean from the reference's record-independence alone. -/

namespace ShorECDLP.Entrant.RecordShift
open ECDSAAdd

/-- Missing records read as `false`, so trailing `false` records are inert. -/
theorem run_pad_false (p : Program) (l : List Bool) (k : Nat) (s : State) :
    run p (l ++ List.replicate k false) s = run p l s := by
  induction p generalizing l k s with
  | nil => rfl
  | cons i p ih =>
    cases i with
    | X t => exact ih l k _
    | CX c t => exact ih l k _
    | CCX a b t => exact ih l k _
    | measureX t c₀ c₁ =>
      cases l with
      | nil =>
        cases k with
        | zero => rfl
        | succ k =>
          change run p (List.replicate k false) (measureAndCorrect t c₀ c₁ false s) =
            run p ([]) (measureAndCorrect t c₀ c₁ false s)
          simpa using ih ([]) k (measureAndCorrect t c₀ c₁ false s)
      | cons b l => exact ih l k _

/-- Exactly `k` records, padding with `false`. -/
def fit (l : List Bool) (k : Nat) : List Bool := l.take k ++ List.replicate (k - (l.take k).length) false

theorem fit_length (l : List Bool) (k : Nat) : (fit l k).length = k := by
  simp only [fit, List.length_append, List.length_replicate, List.length_take]
  omega

theorem run_fit (p : Program) (l : List Bool) (s : State) :
    run p (fit l (measurementCount p)) s = run p l s := by
  rw [fit, run_pad_false, run_take]

theorem run_no_records' (p : Program) (hm : measurementCount p = 0) (m : List Bool) (s : State) :
    run p m s = run p ([]) s := by
  rw [← run_take p m s, hm, List.take_zero]

theorem run_append' (p q : Program) (m : List Bool) (s : State) :
    run (p ++ q) m s = run q (m.drop (measurementCount p)) (run p m s) := by
  rw [run_append, run_take]

theorem gates_phase (p : Program) (hp : measurementCount p = 0) (m : List Bool) (s : State) :
    (run p m s).phase = s.phase := by
  induction p generalizing s with
  | nil => rfl
  | cons i p ih =>
    cases i with
    | X t => exact ih (by simpa [measurementCount] using hp) _
    | CX c t => exact ih (by simpa [measurementCount] using hp) _
    | CCX a b t => exact ih (by simpa [measurementCount] using hp) _
    | measureX t c₀ c₁ => simp [measurementCount] at hp

def pad (q : Wire) (n : Nat) : Program := List.replicate n (.measureX q ([]) ([]))

theorem pad_counts (q : Wire) (n : Nat) : measurementCount (pad q n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pad, List.replicate_succ, measurementCount] at ih ⊢; omega

theorem pad_clean (q : Wire) (n : Nat) (m : List Bool) (s : State) (h : s.basis q = false) :
    run (pad q n) m s = s := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih =>
    have he : (measureAndCorrect q ([]) ([]) (m.headD false) s) = s := by
      apply State.extensionality
      · simp [measureAndCorrect, correct, h]
      · funext w
        by_cases hw : w = q
        · subst hw; simp [measureAndCorrect, correct, writeBit, h]
        · simp [measureAndCorrect, correct, writeBit, hw]
    change run (pad q n) m.tail (measureAndCorrect q ([]) ([]) (m.headD false) s) = s
    rw [he]; exact ih _

/-- One record decides the phase kick of a dirty padding wire. -/
theorem pad_first (q : Wire) (n : Nat) (β : Bool) (s : State) :
    run (pad q (n+1)) ([β]) s = ⟨s.phase ^^ (β && s.basis q), writeBit s.basis q false⟩ := by
  change run (pad q n) ([]) (measureAndCorrect q ([]) ([]) β s) = _
  rw [pad_clean q n _ _ (by simp [measureAndCorrect, correct, writeBit])]
  simp [measureAndCorrect, correct]

theorem run_split (X Y : Program) (l rest : List Bool) (hl : l.length = measurementCount X) (s : State) :
    run (X ++ Y) (l ++ rest) s = run Y rest (run X l s) := by
  rw [run_append, List.take_left' hl, List.drop_left' hl]

theorem shift_padding (A B B' C₀ E : Program) (q : Wire) (n n' : Nat) (hn : 0 < n)
    (hE : measurementCount E = 0)
    (s₀ t : State)
    (href : ∀ m, run (A ++ B ++ C₀ ++ pad q n ++ E) m s₀ = t)
    (hB : ∀ mA mB mB', run B' mB' (run A mA s₀) = run B mB (run A mA s₀)) :
    ∀ m, run (A ++ B' ++ C₀ ++ pad q n' ++ E) m s₀ = t := by
  -- the reference read on an explicitly laid-out record list
  have layout : ∀ (mA mB mC mP : List Bool),
      run (A ++ B ++ C₀ ++ pad q n ++ E)
        (fit mA (measurementCount A) ++ (fit mB (measurementCount B) ++ (fit mC (measurementCount C₀) ++ mP))) s₀ =
        run E ([]) (run (pad q n) mP (run C₀ mC (run B mB (run A mA s₀)))) := by
    intro mA mB mC mP
    simp only [List.append_assoc]
    rw [run_split _ _ _ _ (fit_length _ _), run_fit, run_split _ _ _ _ (fit_length _ _), run_fit,
      run_split _ _ _ _ (fit_length _ _), run_fit, run_append', run_no_records' E hE]
  -- the padding wire is clean on every reachable state
  have clean : ∀ mA mB mC, (run C₀ mC (run B mB (run A mA s₀))).basis q = false := by
    intro mA mB mC
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have h1 := (layout mA mB mC ([true])).symm.trans (href _)
    have h0 := (layout mA mB mC ([false])).symm.trans (href _)
    rw [pad_first] at h1 h0
    have p1 := congrArg State.phase h1
    have p0 := congrArg State.phase h0
    rw [gates_phase E hE] at p1 p0
    have := p1.trans p0.symm
    simp only [Bool.true_and, Bool.false_and, Bool.xor_false] at this
    revert this
    cases (run C₀ mC (run B mB (run A mA s₀))).phase <;>
      cases (run C₀ mC (run B mB (run A mA s₀))).basis q <;> simp
  intro m
  simp only [List.append_assoc]
  rw [run_append' A, run_append' B', run_append' C₀, run_append' (pad q n'), run_no_records' E hE,
    hB m ([]) _, pad_clean q n' _ _ (clean m ([]) _)]
  have r := (layout m ([]) (m.drop (measurementCount A + measurementCount B')) ([])).symm.trans (href _)
  rw [pad_clean q n _ _ (clean m ([]) _)] at r
  simpa only [List.drop_drop, Nat.add_comm] using r

end ShorECDLP.Entrant.RecordShift


/-! In-place semantics of the merged `C`/`-C` corner block.

The reference corner block (`thirdCorners`) writes `C` under `infinitySelect ⊕ doubleSelect` and
`-C` under `genericSelect ⊕ equalNegY`, with two controlled table traversals. `fourCorners` writes
`C` once under `infinitySelect ⊕ doubleSelect ⊕ genericSelect ⊕ equalNegY`. The `-C` corner is
recovered with controlled `y`-negations: the existing negation is controlled by
`equalNegY ⊕ genericSelect`, and one more negation under `equalNegY` follows the shared write. -/

namespace ShorECDLP.Entrant.WEX
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
noncomputable section
set_option maxHeartbeats 4000000

/-- The `y`-negation controlled by `equalNegY`. -/
def negH (L : ControlledPointLayout) : Program :=
  (negateYLayout L).program L.core.equalNegY ECDSAAdd.p SquareReduction.c

/-- One table write of `C` serving the `C` and `-C` corners. -/
def fourWrite (L : ControlledPointLayout) (C : Point) : Program :=
  [.CX L.infinitySelect L.doubleSelect, .CX L.genericSelect L.doubleSelect,
    .CX L.core.equalNegY L.doubleSelect] ++ maskedPointConstant L.doubleSelect L.point C ++
  [.CX L.core.equalNegY L.doubleSelect, .CX L.genericSelect L.doubleSelect,
    .CX L.infinitySelect L.doubleSelect]

/-- Merged corner block: two negations, the doubled point, and one shared `C` write. -/
def fourCorners (L : ControlledPointLayout) (C : Point) : Program :=
  [.CX L.genericSelect L.core.equalNegY] ++ negH L ++ [.CX L.genericSelect L.core.equalNegY] ++
  ([.CX L.doubleSelect L.core.equalNegY] ++ maskedPointConstant L.core.equalNegY L.point (C+C) ++
    [.CX L.doubleSelect L.core.equalNegY]) ++
  fourWrite L C ++ negH L

theorem negH_counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (negH L) = 1022 ∧ measurementCount (negH L) = 1022 := by
  have widths := negateYLayout_widths L hw
  exact negate_256_counts (negateYLayout L) L.core.equalNegY ECDSAAdd.p SquareReduction.c
    widths.2 widths.1

/-! ### Small run facts -/

theorem cx_off_state (c t : Wire) (s : State) (hc : s.basis c = false) :
    (⟨s.phase, writeBit s.basis t (s.basis t ^^ s.basis c)⟩ : State) = s := by
  apply State.extensionality
  · rfl
  · funext w
    by_cases hw : w = t
    · subst hw; simp [writeBit, hc]
    · simp [writeBit, hw]

theorem cx_off_run (c t : Wire) (P : Program) (m : List Bool) (s : State)
    (hc : s.basis c = false) : run ([.CX c t] ++ P) m s = run P m s := by
  rw [List.singleton_append]
  change run P m ⟨s.phase, writeBit s.basis t (s.basis t ^^ s.basis c)⟩ = run P m s
  rw [cx_off_state c t s hc]

theorem cx_run_basis (c t : Wire) (P : Program) (m : List Bool) (s : State) :
    run ([.CX c t] ++ P) m s = run P m ⟨s.phase, writeBit s.basis t (s.basis t ^^ s.basis c)⟩ := by
  rw [List.singleton_append]
  rfl

theorem prefix_replace (p q rest : Program)
    (hc : measurementCount p = measurementCount q)
    (he : ∀ m st, run p m st = run q m st) (m : List Bool) (st : State) :
    run (p ++ rest) m st = run (q ++ rest) m st := by
  simpa using run_replace_inside [] rest p q hc he m st

theorem point_flag_away (L : ControlledPointLayout) (hn : L.wires.Nodup) (q : Wire)
    (hq : q ∈ L.inPlaceFlags) : q ∉ PointAddLayout.pointWires L.point := by
  intro bad
  have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
  have hb := List.count_pos_iff.mpr bad
  have hf := List.count_pos_iff.mpr hq
  simp only [dialogUsedWires, List.count_append] at h
  omega

theorem point_pool_away (L : ControlledPointLayout) (hn : L.wires.Nodup) (q : Wire)
    (hq : q ∈ L.dialogPool) : q ∉ PointAddLayout.pointWires L.point := by
  intro bad
  have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
  have hb := List.count_pos_iff.mpr bad
  have hf := List.count_pos_iff.mpr hq
  simp only [dialogUsedWires, List.count_append] at h
  omega

theorem point_nodup' (L : ControlledPointLayout) (hn : L.wires.Nodup) :
    (PointAddLayout.pointWires L.point).Nodup :=
  (L.dialogUsed_nodup hn).of_append_left.of_append_left.of_append_left

theorem flags_distinct (L : ControlledPointLayout) (hn : L.wires.Nodup) :
    L.infinitySelect ≠ L.doubleSelect ∧ L.genericSelect ≠ L.doubleSelect ∧
      L.core.equalNegY ≠ L.doubleSelect ∧ L.genericSelect ≠ L.core.equalNegY ∧
      L.doubleSelect ≠ L.core.equalNegY := by
  have sep := dialogFlag_separation (L := L) hn
  simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> simp_all

/-- A disabled mask is the identity. -/
theorem mask_off_state (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (c : Wire) (hc : c ∈ L.inPlaceFlags) (C : Point) (m : List Bool) (s : State)
    (hs : s.basis c = false) : run (maskedPointConstant c L.point C) m s = s := by
  have e := maskedPointConstant_correct c L.point C (point_nodup' L hn) (point_flag_away L hn c hc)
    hw.inputX hw.inputY s m
  rw [hs] at e
  have id : PointEffect L.point false 0 0 s s :=
    ⟨rfl, fun _ _ => rfl, by simp, by simp, by simp⟩
  simpa using pointEffect_eq e id

theorem mask_off_run (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (c : Wire) (hc : c ∈ L.inPlaceFlags) (C : Point) (P : Program) (m : List Bool) (s : State)
    (hs : s.basis c = false) : run (maskedPointConstant c L.point C ++ P) m s = run P m s := by
  rw [run_append, (maskedPointConstant_counts c L.point C).2, List.drop_zero,
    mask_off_state L hw hn c hc C _ s hs]

/-- A mask changes only point wires. -/
theorem mask_outside (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (c : Wire) (hc : c ∈ L.inPlaceFlags) (C : Point) (m : List Bool) (s : State)
    (q : Wire) (hq : q ∉ PointAddLayout.pointWires L.point) :
    (run (maskedPointConstant c L.point C) m s).basis q = s.basis q :=
  (maskedPointConstant_correct c L.point C (point_nodup' L hn) (point_flag_away L hn c hc)
    hw.inputX hw.inputY s m).outside q hq

/-! ### The controlled negation -/

theorem negH_aux (L : ControlledPointLayout) (hw : L.Widths) (s : State)
    (hclean : ECDSAAdd.regValue L.dialogPool s.basis = 0) (q : Wire)
    (hq : q ∈ (negateYLayout L).work ++ [(negateYLayout L).cin, (negateYLayout L).zero]) :
    s.basis q = false := by
  rw [negateYLayout_pool L hw] at hq
  exact (ECDSAAdd.Arithmetic.regValue_zero _ _).mp hclean q (List.mem_of_mem_take hq)

theorem negH_effect (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (s : State) (m : List Bool) (hY : ECDSAAdd.regValue L.point.y s.basis < ECDSAAdd.p)
    (hclean : ECDSAAdd.regValue L.dialogPool s.basis = 0) :
    (run (negH L) m s).phase = s.phase ∧
    ECDSAAdd.regValue L.point.y (run (negH L) m s).basis =
      (if s.basis L.core.equalNegY then (ECDSAAdd.p - ECDSAAdd.regValue L.point.y s.basis) % ECDSAAdd.p
        else ECDSAAdd.regValue L.point.y s.basis) ∧
    ∀ q, q ∉ L.point.y → (run (negH L) m s).basis q = s.basis q := by
  have width := negateYLayout_widths L hw
  have aux := negH_aux L hw s hclean
  exact (negateYLayout L).program_correct L.core.equalNegY (negateYLayout_nodup L hw hn) width.2
    (by rw [width.1]; decide) ECDSAAdd.p SquareReduction.c (ECDSAAdd.regValue L.point.y s.basis)
    (by rw [width.1]; norm_num [ECDSAAdd.p, SquareReduction.c]) (by norm_num [SquareReduction.c]) hY
    s m rfl ((ECDSAAdd.Arithmetic.regValue_zero _ _).mpr (fun q hq => aux q (by simp [hq])))
    (aux _ (by simp)) (aux _ (by simp))

theorem pool_not_y (L : ControlledPointLayout) (hn : L.wires.Nodup) (q : Wire)
    (hq : q ∈ L.dialogPool) : q ∉ L.point.y := fun hy =>
  point_pool_away L hn q hq (by simp [PointAddLayout.pointWires, hy])

theorem negH_clean (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (s : State) (m : List Bool) (hY : ECDSAAdd.regValue L.point.y s.basis < ECDSAAdd.p)
    (hclean : ECDSAAdd.regValue L.dialogPool s.basis = 0) :
    ECDSAAdd.regValue L.dialogPool (run (negH L) m s).basis = 0 := by
  have e := negH_effect L hw hn s m hY hclean
  rw [ECDSAAdd.Arithmetic.regValue_zero] at hclean ⊢
  intro q hq
  rw [e.2.2 q (pool_not_y L hn q hq)]
  exact hclean q hq

/-- A disabled negation is the identity. -/
theorem negH_off_state (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (s : State) (m : List Bool) (hY : ECDSAAdd.regValue L.point.y s.basis < ECDSAAdd.p)
    (hclean : ECDSAAdd.regValue L.dialogPool s.basis = 0)
    (hq : s.basis L.core.equalNegY = false) : run (negH L) m s = s := by
  have e := negH_effect L hw hn s m hY hclean
  rw [hq] at e
  simp only [Bool.false_eq_true, if_false] at e
  apply State.extensionality
  · exact e.1
  · funext w
    by_cases hy : w ∈ L.point.y
    · exact Bridge.regValue_bits L.point.y _ _ (by simpa only [Bridge.regValueB_eq] using e.2.1) w hy
    · exact e.2.2 w hy

theorem negH_off_run (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (P : Program) (m : List Bool) (s : State)
    (hY : ECDSAAdd.regValue L.point.y s.basis < ECDSAAdd.p)
    (hclean : ECDSAAdd.regValue L.dialogPool s.basis = 0)
    (hq : s.basis L.core.equalNegY = false) :
    run (negH L ++ P) m s = run P (m.drop 1022) s := by
  rw [run_append, (negH_counts L hw).2, negH_off_state L hw hn s _ hY hclean hq]

/-- Mirror of `negative_corner_clear`: XOR a point into a cleared word, then negate. -/
theorem positive_corner_negate (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (D : Point) (st : State) (hY : ECDSAAdd.regValue L.point.y st.basis < ECDSAAdd.p)
    (hclean : ECDSAAdd.regValue L.dialogPool st.basis = 0)
    (hzero : st.basis L.core.equalNegY = true → Holds.holds st.basis L.point (0 : Point)) (m : List Bool) :
    run (maskedPointConstant L.core.equalNegY L.point D ++ negH L) m st =
      run (maskedPointConstant L.core.equalNegY L.point (-D)) ([]) st := by
  have hpoint := point_nodup' L hn
  have hH : L.core.equalNegY ∈ L.inPlaceFlags := by simp [inPlaceFlags]
  have hq := point_flag_away L hn _ hH
  let u := run (maskedPointConstant L.core.equalNegY L.point D) ([]) st
  have eu := maskedPointConstant_correct _ L.point D hpoint hq hw.inputX hw.inputY st ([])
  have eo := maskedPointConstant_correct _ L.point (-D) hpoint hq hw.inputX hw.inputY st ([])
  have hqU : u.basis L.core.equalNegY = st.basis L.core.equalNegY := eu.outside _ hq
  have hYu : ECDSAAdd.regValue L.point.y u.basis < ECDSAAdd.p := by
    change ECDSAAdd.regValue L.point.y
      (run (maskedPointConstant L.core.equalNegY L.point D) ([]) st).basis < ECDSAAdd.p
    rw [eu.y]
    cases hb : st.basis L.core.equalNegY with
    | false => simpa using hY
    | true =>
      have hz := (point_holds _ _ _).mp (hzero hb)
      rw [hz.2.2]
      simpa [pointY, ECDSAAdd.Secp256k1.coordinates] using (point_coordinates_lt D).2
  have hcu : ECDSAAdd.regValue L.dialogPool u.basis = 0 := by
    rw [ECDSAAdd.Arithmetic.regValue_zero] at hclean ⊢
    intro q hq'
    change (run (maskedPointConstant L.core.equalNegY L.point D) ([]) st).basis q = false
    rw [eu.outside q (point_pool_away L hn q hq')]
    exact hclean q hq'
  have eN := negH_effect L hw hn u m hYu hcu
  let v := run (negH L) m u
  let old := run (maskedPointConstant L.core.equalNegY L.point (-D)) ([]) st
  have hxy := (List.nodup_append'.mp (List.nodup_cons.mp hpoint).2).2.2
  have hfinite : L.point.finite ∉ L.point.y := fun hm =>
    (List.nodup_cons.mp hpoint).1 (List.mem_append_right _ hm)
  have hfiniteEq : v.basis L.point.finite = old.basis L.point.finite := by
    change (run (negH L) m u).basis L.point.finite = old.basis L.point.finite
    rw [eN.2.2 _ hfinite, eu.finite, eo.finite, ECDSAAdd.ShorPort.pointFinite_neg]
  have hxEq : ECDSAAdd.regValue L.point.x v.basis = ECDSAAdd.regValue L.point.x old.basis := by
    have hx : ECDSAAdd.regValue L.point.x v.basis = ECDSAAdd.regValue L.point.x u.basis := by
      apply ECDSAAdd.Arithmetic.regValue_congr
      intro w hw'
      exact eN.2.2 w (List.disjoint_left.mp hxy hw')
    rw [hx, eu.x, eo.x, ECDSAAdd.ShorPort.pointX_neg]
  have hyEq : ECDSAAdd.regValue L.point.y v.basis = ECDSAAdd.regValue L.point.y old.basis := by
    change ECDSAAdd.regValue L.point.y (run (negH L) m u).basis = _
    rw [eN.2.1, hqU, eo.y]
    cases hb : st.basis L.core.equalNegY with
    | false =>
      simp only [Bool.false_eq_true, if_false]
      rw [eu.y, hb]
      simp
    | true =>
      have hz := (point_holds _ _ _).mp (hzero hb)
      simp only [if_true]
      rw [eu.y, hb, hz.2.2]
      simp only [if_true]
      have h0 : pointY (0 : Point) = 0 := rfl
      rw [h0, Nat.zero_xor, Nat.zero_xor, pointY_neg_mod]
  have heq : v = old := by
    apply State.extensionality
    · exact (eN.1.trans eu.phase).trans eo.phase.symm
    funext w
    by_cases hf : w = L.point.finite
    · subst w; exact hfiniteEq
    by_cases hxm : w ∈ L.point.x
    · exact Bridge.regValue_bits L.point.x _ _ (by simpa only [Bridge.regValueB_eq] using hxEq) w hxm
    by_cases hym : w ∈ L.point.y
    · exact Bridge.regValue_bits L.point.y _ _ (by simpa only [Bridge.regValueB_eq] using hyEq) w hym
    have hout : w ∉ PointAddLayout.pointWires L.point := by
      simpa only [PointAddLayout.pointWires, List.mem_cons, List.mem_append, not_or] using ⟨⟨hf,hxm⟩,hym⟩
    exact ((eN.2.2 w hym).trans (eu.outside w hout)).trans (eo.outside w hout).symm
  rw [run_append, (maskedPointConstant_counts _ L.point D).2, List.take_zero, List.drop_zero]
  exact heq

/-! ### Per-block behaviour on the corner states -/

theorem run_free_left (p q : Program) (hp : measurementCount p = 0) (m : List Bool) (s : State) :
    run (p ++ q) m s = run q m (run p ([]) s) := by
  rw [run_append, hp, List.take_zero, List.drop_zero]

theorem run_free_right (p q : Program) (hq : measurementCount q = 0) (m : List Bool) (s : State) :
    run (p ++ q) m s = run q ([]) (run p m s) := by
  rw [run_append, run_no_records q hq, run_take]

theorem cx_state (c t : Wire) (m : List Bool) (s : State) :
    run [.CX c t] m s = ⟨s.phase, writeBit s.basis t (s.basis t ^^ s.basis c)⟩ := rfl

theorem writeBit_other (b : BasisState) (t w : Wire) (v : Bool) (h : w ≠ t) :
    writeBit b t v w = b w := by
  simp [writeBit, Function.update, h]

theorem writeBit_same (b : BasisState) (t : Wire) (v : Bool) : writeBit b t v t = v := by
  simp [writeBit]

theorem writeBit_twice (b : BasisState) (t : Wire) (v w : Bool) :
    writeBit (writeBit b t v) t w = writeBit b t w := by
  funext q; by_cases h : q = t <;> simp [writeBit, Function.update, h]

theorem writeBit_self (b : BasisState) (t : Wire) : writeBit b t (b t) = b := by
  funext q; by_cases h : q = t <;> simp [writeBit, Function.update, h]

/-- A selector sandwich: `pre` toggles `t` by `X`, the mask runs under `t`, `post` toggles back. -/
theorem selector_effect (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (t : Wire) (ht : t ∈ L.inPlaceFlags) (C : Point) (s : State) (X : Bool)
    (pre post : Program)
    (hpre : run pre ([]) s = ⟨s.phase, writeBit s.basis t (s.basis t ^^ X)⟩)
    (hpost : ∀ u : State, (∀ q ∈ L.inPlaceFlags, q ≠ t → u.basis q = s.basis q) →
      run post ([]) u = ⟨u.phase, writeBit u.basis t (u.basis t ^^ X)⟩) :
    PointEffect L.point ((s.basis t ^^ X) && pointFinite C)
      (if (s.basis t ^^ X) then pointX C else 0) (if (s.basis t ^^ X) then pointY C else 0) s
      (run post ([]) (run (maskedPointConstant t L.point C) ([]) (run pre ([]) s))) := by
  have hpoint := point_nodup' L hn
  have htp := point_flag_away L hn t ht
  have hs1t : (run pre ([]) s).basis t = (s.basis t ^^ X) := by
    rw [hpre]; exact writeBit_same _ _ _
  have hs1o : ∀ w, w ≠ t → (run pre ([]) s).basis w = s.basis w := by
    intro w hwt; rw [hpre]; exact writeBit_other _ _ _ _ hwt
  have hs1p : (run pre ([]) s).phase = s.phase := by rw [hpre]
  have e := maskedPointConstant_correct t L.point C hpoint htp hw.inputX hw.inputY (run pre ([]) s) ([])
  rw [hs1t] at e
  generalize hu : run (maskedPointConstant t L.point C) ([]) (run pre ([]) s) = u at e
  have hut : u.basis t = (s.basis t ^^ X) := (e.outside t htp).trans hs1t
  have hflags : ∀ q ∈ L.inPlaceFlags, q ≠ t → u.basis q = s.basis q := fun q hq hqt =>
    (e.outside q (point_flag_away L hn q hq)).trans (hs1o q hqt)
  have hfin := hpost u hflags
  have hpost_t : (run post ([]) u).basis t = s.basis t := by
    rw [hfin]; simp only [writeBit_same, hut, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
  have hpost_o : ∀ w, w ≠ t → (run post ([]) u).basis w = u.basis w := by
    intro w hwt; rw [hfin]; exact writeBit_other _ _ _ _ hwt
  have hft : L.point.finite ≠ t := fun h => htp (h ▸ by simp [PointAddLayout.pointWires])
  have hxt : ∀ w ∈ L.point.x, w ≠ t := fun w hw' h => htp (h ▸ by simp [PointAddLayout.pointWires, hw'])
  have hyt : ∀ w ∈ L.point.y, w ≠ t := fun w hw' h => htp (h ▸ by simp [PointAddLayout.pointWires, hw'])
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hfin]; exact e.phase.trans hs1p
  · intro w hw'
    by_cases hwt : w = t
    · subst hwt; exact hpost_t
    · rw [hpost_o w hwt]; exact (e.outside w hw').trans (hs1o w hwt)
  · rw [hpost_o _ hft, e.finite, hs1o _ hft]
  · have h1 : ECDSAAdd.regValue L.point.x (run post ([]) u).basis = ECDSAAdd.regValue L.point.x u.basis :=
      ECDSAAdd.Arithmetic.regValue_congr _ _ _ (fun w hw' => hpost_o w (hxt w hw'))
    have h2 : ECDSAAdd.regValue L.point.x (run pre ([]) s).basis = ECDSAAdd.regValue L.point.x s.basis :=
      ECDSAAdd.Arithmetic.regValue_congr _ _ _ (fun w hw' => hs1o w (hxt w hw'))
    rw [h1, e.x, h2]
  · have h1 : ECDSAAdd.regValue L.point.y (run post ([]) u).basis = ECDSAAdd.regValue L.point.y u.basis :=
      ECDSAAdd.Arithmetic.regValue_congr _ _ _ (fun w hw' => hpost_o w (hyt w hw'))
    have h2 : ECDSAAdd.regValue L.point.y (run pre ([]) s).basis = ECDSAAdd.regValue L.point.y s.basis :=
      ECDSAAdd.Arithmetic.regValue_congr _ _ _ (fun w hw' => hs1o w (hyt w hw'))
    rw [h1, e.y, h2]


theorem three_cx_run (a b c t : Wire) (ha : a ≠ t) (hb : b ≠ t) (hc : c ≠ t) (m : List Bool) (s : State) :
    run [.CX a t, .CX b t, .CX c t] m s =
      ⟨s.phase, writeBit s.basis t (((s.basis t ^^ s.basis a) ^^ s.basis b) ^^ s.basis c)⟩ := by
  change (⟨s.phase, writeBit (writeBit (writeBit s.basis t (s.basis t ^^ s.basis a)) t
      (writeBit s.basis t (s.basis t ^^ s.basis a) t ^^ writeBit s.basis t (s.basis t ^^ s.basis a) b)) t
      (writeBit (writeBit s.basis t (s.basis t ^^ s.basis a)) t
        (writeBit s.basis t (s.basis t ^^ s.basis a) t ^^ writeBit s.basis t (s.basis t ^^ s.basis a) b) t ^^
       writeBit (writeBit s.basis t (s.basis t ^^ s.basis a)) t
        (writeBit s.basis t (s.basis t ^^ s.basis a) t ^^ writeBit s.basis t (s.basis t ^^ s.basis a) b) c)⟩ : State) = _
  simp only [writeBit_same, writeBit_twice, writeBit_other _ _ _ _ hb, writeBit_other _ _ _ _ hc]

/-- Run-level shape of the shared write. -/
theorem fourWrite_shape (L : ControlledPointLayout) (C : Point) (n : List Bool) (s : State) :
    run (fourWrite L C) n s =
      run [.CX L.core.equalNegY L.doubleSelect, .CX L.genericSelect L.doubleSelect,
          .CX L.infinitySelect L.doubleSelect] ([])
        (run (maskedPointConstant L.doubleSelect L.point C) ([])
          (run [.CX L.infinitySelect L.doubleSelect, .CX L.genericSelect L.doubleSelect,
            .CX L.core.equalNegY L.doubleSelect] ([]) s)) := by
  rw [fourWrite, run_free_right _ _ rfl, run_free_left _ _ rfl,
    run_no_records _ (maskedPointConstant_counts _ _ _).2]

/-- The shared write XORs `C` under `doubleSelect ⊕ infinitySelect ⊕ genericSelect ⊕ equalNegY`. -/
theorem fourWrite_effect (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (n : List Bool) (s : State) :
    let X := ((s.basis L.doubleSelect ^^ s.basis L.infinitySelect) ^^ s.basis L.genericSelect) ^^
      s.basis L.core.equalNegY
    PointEffect L.point (X && pointFinite C) (if X then pointX C else 0) (if X then pointY C else 0) s
      (run (fourWrite L C) n s) := by
  intro X
  have d := flags_distinct L hn
  have key := selector_effect L hw hn L.doubleSelect (by simp [inPlaceFlags]) C s
    ((s.basis L.infinitySelect ^^ s.basis L.genericSelect) ^^ s.basis L.core.equalNegY)
    ([.CX L.infinitySelect L.doubleSelect, .CX L.genericSelect L.doubleSelect,
      .CX L.core.equalNegY L.doubleSelect] : Program)
    ([.CX L.core.equalNegY L.doubleSelect, .CX L.genericSelect L.doubleSelect,
      .CX L.infinitySelect L.doubleSelect] : Program)
    (by rw [three_cx_run _ _ _ _ d.1 d.2.1 d.2.2.1]; simp only [Bool.xor_assoc])
    (by
      intro u hu
      rw [three_cx_run _ _ _ _ d.2.2.1 d.2.1 d.1,
        hu _ (by simp [inPlaceFlags]) d.1, hu _ (by simp [inPlaceFlags]) d.2.1,
        hu _ (by simp [inPlaceFlags]) d.2.2.1]
      cases u.basis L.doubleSelect <;> cases s.basis L.infinitySelect <;>
        cases s.basis L.genericSelect <;> cases s.basis L.core.equalNegY <;> rfl)
  have hX : (s.basis L.doubleSelect ^^ ((s.basis L.infinitySelect ^^ s.basis L.genericSelect) ^^
      s.basis L.core.equalNegY)) = X := by simp only [X, Bool.xor_assoc]
  rw [hX] at key
  rw [fourWrite_shape]
  exact key

/-- The doubled-point block XORs `C+C` under `equalNegY ⊕ doubleSelect`. -/
theorem zblock_effect (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (n : List Bool) (s : State) :
    PointEffect L.point ((s.basis L.core.equalNegY ^^ s.basis L.doubleSelect) && pointFinite (C+C))
      (if (s.basis L.core.equalNegY ^^ s.basis L.doubleSelect) then pointX (C+C) else 0)
      (if (s.basis L.core.equalNegY ^^ s.basis L.doubleSelect) then pointY (C+C) else 0) s
      (run ([.CX L.doubleSelect L.core.equalNegY] ++ maskedPointConstant L.core.equalNegY L.point (C+C) ++
        [.CX L.doubleSelect L.core.equalNegY]) n s) := by
  have d := flags_distinct L hn
  have key := selector_effect L hw hn L.core.equalNegY (by simp [inPlaceFlags]) (C+C) s
    (s.basis L.doubleSelect) ([.CX L.doubleSelect L.core.equalNegY] : Program)
    ([.CX L.doubleSelect L.core.equalNegY] : Program)
    rfl
    (by intro u hu; rw [cx_state, hu _ (by simp [inPlaceFlags]) d.2.2.2.2])
  rw [run_free_right _ _ rfl, run_free_left _ _ rfl,
    run_no_records _ (maskedPointConstant_counts _ _ _).2]
  exact key

/-- Two states agreeing on phase, on all non-point wires and on the three point fields are equal. -/
theorem point_state_eq (L : ControlledPointLayout) (t u : State) (hp : t.phase = u.phase)
    (ho : ∀ w ∉ PointAddLayout.pointWires L.point, t.basis w = u.basis w)
    (hf : t.basis L.point.finite = u.basis L.point.finite)
    (hx : ECDSAAdd.regValue L.point.x t.basis = ECDSAAdd.regValue L.point.x u.basis)
    (hy : ECDSAAdd.regValue L.point.y t.basis = ECDSAAdd.regValue L.point.y u.basis) : t = u := by
  apply State.extensionality _ _ hp
  funext w
  by_cases hfw : w = L.point.finite
  · subst w; exact hf
  by_cases hxm : w ∈ L.point.x
  · exact Bridge.regValue_bits L.point.x _ _ (by simpa only [Bridge.regValueB_eq] using hx) w hxm
  by_cases hym : w ∈ L.point.y
  · exact Bridge.regValue_bits L.point.y _ _ (by simpa only [Bridge.regValueB_eq] using hy) w hym
  apply ho
  simpa only [PointAddLayout.pointWires, List.mem_cons, List.mem_append, not_or] using ⟨⟨hfw, hxm⟩, hym⟩

/-- Append one more mask to a point effect. -/
theorem effect_mask_step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    {F : Bool} {X Y : Nat} {s t : State} (h : PointEffect L.point F X Y s t)
    (c : Wire) (hc : c ∈ L.inPlaceFlags) (P : Point) :
    PointEffect L.point (F ^^ (s.basis c && pointFinite P)) (X ^^^ (if s.basis c then pointX P else 0))
      (Y ^^^ (if s.basis c then pointY P else 0)) s (run (maskedPointConstant c L.point P) ([]) t) := by
  have e := maskedPointConstant_correct c L.point P (point_nodup' L hn) (point_flag_away L hn c hc)
    hw.inputX hw.inputY t ([])
  rw [h.outside c (point_flag_away L hn c hc)] at e
  exact h.trans e

theorem effect_refl (L : ControlledPointLayout) (s : State) : PointEffect L.point false 0 0 s s :=
  ⟨rfl, fun _ _ => rfl, by simp, by simp, by simp⟩

/-- The reference corner block as one point effect. -/
theorem dialogCorners_effect (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (s : State) :
    let O := s.basis L.infinitySelect
    let D := s.basis L.doubleSelect
    let I := s.basis L.genericSelect
    let H := s.basis L.core.equalNegY
    PointEffect L.point
      (((((((false ^^ (O && pointFinite C)) ^^ (D && pointFinite C)) ^^ (D && pointFinite (C+C))) ^^
        (I && pointFinite (-C))) ^^ (H && pointFinite (-(C+C)))) ^^ (H && pointFinite (-C))))
      ((((((0 ^^^ (if O then pointX C else 0)) ^^^ (if D then pointX C else 0)) ^^^
        (if D then pointX (C+C) else 0)) ^^^ (if I then pointX (-C) else 0)) ^^^
        (if H then pointX (-(C+C)) else 0)) ^^^ (if H then pointX (-C) else 0))
      ((((((0 ^^^ (if O then pointY C else 0)) ^^^ (if D then pointY C else 0)) ^^^
        (if D then pointY (C+C) else 0)) ^^^ (if I then pointY (-C) else 0)) ^^^
        (if H then pointY (-(C+C)) else 0)) ^^^ (if H then pointY (-C) else 0))
      s (run (pointDialogCorners L C) ([]) s) := by
  intro O D I H
  have e0 := effect_refl L s
  have e1 := effect_mask_step L hw hn e0 L.infinitySelect (by simp [inPlaceFlags]) C
  have e2 := effect_mask_step L hw hn e1 L.doubleSelect (by simp [inPlaceFlags]) C
  have e3 := effect_mask_step L hw hn e2 L.doubleSelect (by simp [inPlaceFlags]) (C+C)
  have e4 := effect_mask_step L hw hn e3 L.genericSelect (by simp [inPlaceFlags]) (-C)
  have e5 := effect_mask_step L hw hn e4 L.core.equalNegY (by simp [inPlaceFlags]) (-(C+C))
  have e6 := effect_mask_step L hw hn e5 L.core.equalNegY (by simp [inPlaceFlags]) (-C)
  have hrun : run (pointDialogCorners L C) ([]) s =
      run (maskedPointConstant L.core.equalNegY L.point (-C)) ([])
       (run (maskedPointConstant L.core.equalNegY L.point (-(C+C))) ([])
        (run (maskedPointConstant L.genericSelect L.point (-C)) ([])
         (run (maskedPointConstant L.doubleSelect L.point (C+C)) ([])
          (run (maskedPointConstant L.doubleSelect L.point C) ([])
           (run (maskedPointConstant L.infinitySelect L.point C) ([]) s))))) := by
    simp only [pointDialogCorners, pointInPlaceCorners, dialogExceptionPoint, run_append,
      maskedPointConstant_counts, measurementCount_append, List.take_nil, List.drop_nil, Nat.add_zero]
  rw [hrun]
  exact e6


/-- The doubled-point block of `fourCorners`. -/
def zblock (L : ControlledPointLayout) (C : Point) : Program :=
  [.CX L.doubleSelect L.core.equalNegY] ++ maskedPointConstant L.core.equalNegY L.point (C+C) ++
    [.CX L.doubleSelect L.core.equalNegY]

theorem fourCorners_split (L : ControlledPointLayout) (C : Point) (m : List Bool) (st : State) :
    ∃ m1 m2 : List Bool, run (fourCorners L C) m st =
      run (negH L) m2 (run (fourWrite L C) ([]) (run (zblock L C) ([])
        (run [.CX L.genericSelect L.core.equalNegY] ([])
          (run (negH L) m1 (run [.CX L.genericSelect L.core.equalNegY] ([]) st))))) := by
  have h5 : measurementCount (fourWrite L C) = 0 := by
    simp [fourWrite, measurementCount_append, maskedPointConstant_counts, measurementCount]
  have h4 : measurementCount (zblock L C) = 0 := by
    simp [zblock, measurementCount_append, maskedPointConstant_counts, measurementCount]
  refine ⟨m.take (measurementCount ([.CX L.genericSelect L.core.equalNegY] ++ negH L ++
      [.CX L.genericSelect L.core.equalNegY] ++ zblock L C ++ fourWrite L C)),
    m.drop (measurementCount ([.CX L.genericSelect L.core.equalNegY] ++ negH L ++
      [.CX L.genericSelect L.core.equalNegY] ++ zblock L C ++ fourWrite L C)), ?_⟩
  change run ([.CX L.genericSelect L.core.equalNegY] ++ negH L ++
      [.CX L.genericSelect L.core.equalNegY] ++ zblock L C ++ fourWrite L C ++ negH L) m st = _
  rw [run_append, run_free_right _ _ h5, run_free_right _ _ h4, run_free_right _ _ rfl,
    run_free_left _ _ rfl]

theorem flag_not_pool (L : ControlledPointLayout) (hn : L.wires.Nodup) (q : Wire)
    (hq : q ∈ L.inPlaceFlags) : q ∉ L.dialogPool := by
  intro bad
  have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
  have hb := List.count_pos_iff.mpr bad
  have hf := List.count_pos_iff.mpr hq
  simp only [dialogUsedWires, List.count_append] at h
  omega

theorem pointFinite_zero' : pointFinite (0 : Point) = false := rfl
theorem pointX_zero' : pointX (0 : Point) = 0 := rfl
theorem pointY_zero' : pointY (0 : Point) = 0 := rfl

/-- On every corner state, the merged block equals the reference mask chain. -/
theorem fourCorners_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (st : State)
    (hY : ECDSAAdd.regValue L.point.y st.basis < ECDSAAdd.p)
    (hclean : ECDSAAdd.regValue L.dialogPool st.basis = 0)
    (hH : st.basis L.core.equalNegY = true → Holds.holds st.basis L.point (-(C+C)))
    (hI : st.basis L.genericSelect = true → Holds.holds st.basis L.point (-C))
    (hHx : st.basis L.core.equalNegY = true → st.basis L.infinitySelect = false ∧
      st.basis L.doubleSelect = false ∧ st.basis L.genericSelect = false)
    (hIx : st.basis L.genericSelect = true → st.basis L.infinitySelect = false ∧
      st.basis L.doubleSelect = false)
    (hYout : ECDSAAdd.regValue L.point.y (run (pointDialogCorners L C) ([]) st).basis < ECDSAAdd.p)
    (m : List Bool) :
    run (fourCorners L C) m st = run (pointDialogCorners L C) ([]) st := by
  obtain ⟨m1, m2, hsplit⟩ := fourCorners_split L C m st
  rw [hsplit]
  have d := flags_distinct L hn
  have pH := point_flag_away L hn L.core.equalNegY (by simp [inPlaceFlags])
  have pI := point_flag_away L hn L.genericSelect (by simp [inPlaceFlags])
  have hHy : L.core.equalNegY ∉ L.point.y := fun h => pH (by simp [PointAddLayout.pointWires, h])
  have hIy : L.genericSelect ∉ L.point.y := fun h => pI (by simp [PointAddLayout.pointWires, h])
  have hHpool := flag_not_pool L hn L.core.equalNegY (by simp [inPlaceFlags])
  have hfy : L.point.finite ∉ L.point.y := fun h =>
    (List.nodup_cons.mp (point_nodup' L hn)).1 (List.mem_append_right _ h)
  have hxy : ∀ w ∈ L.point.x, w ∉ L.point.y := fun w hw' =>
    List.disjoint_left.mp (List.nodup_append'.mp (List.nodup_cons.mp (point_nodup' L hn)).2).2.2 hw'
  have notY : ∀ w, w ∉ PointAddLayout.pointWires L.point → w ∉ L.point.y := fun w hw' h =>
    hw' (by simp [PointAddLayout.pointWires, h])
  -- s1: equalNegY ^= genericSelect
  generalize hs1 : run [.CX L.genericSelect L.core.equalNegY] ([]) st = s1
  rw [cx_state] at hs1
  have s1p : s1.phase = st.phase := by rw [← hs1]
  have s1H : s1.basis L.core.equalNegY = (st.basis L.core.equalNegY ^^ st.basis L.genericSelect) := by
    rw [← hs1]; exact writeBit_same _ _ _
  have s1o : ∀ w, w ≠ L.core.equalNegY → s1.basis w = st.basis w := by
    intro w hwH; rw [← hs1]; exact writeBit_other _ _ _ _ hwH
  have s1y : ECDSAAdd.regValue L.point.y s1.basis = ECDSAAdd.regValue L.point.y st.basis :=
    ECDSAAdd.Arithmetic.regValue_congr _ _ _ (fun w hw' => s1o w (fun h => hHy (h ▸ hw')))
  have s1c : ECDSAAdd.regValue L.dialogPool s1.basis = 0 := by
    rw [ECDSAAdd.Arithmetic.regValue_zero] at hclean ⊢
    intro w hw'; rw [s1o w (fun h => hHpool (h ▸ hw'))]; exact hclean w hw'
  -- s2: first negation
  generalize hs2 : run (negH L) m1 s1 = s2
  have e2 := negH_effect L hw hn s1 m1 (s1y ▸ hY) s1c
  rw [hs2, s1H, s1y] at e2
  -- s3: restore equalNegY
  generalize hs3 : run [.CX L.genericSelect L.core.equalNegY] ([]) s2 = s3
  rw [cx_state] at hs3
  have s3p : s3.phase = st.phase := by rw [← hs3]; exact e2.1.trans s1p
  have s3o : ∀ w, w ∉ L.point.y → s3.basis w = st.basis w := by
    intro w hwy
    rw [← hs3]
    dsimp only
    by_cases hwH : w = L.core.equalNegY
    · subst hwH
      rw [writeBit_same, e2.2.2 _ hHy, e2.2.2 _ hIy, s1H, s1o _ d.2.2.2.1]
      cases st.basis L.core.equalNegY <;> cases st.basis L.genericSelect <;> rfl
    · rw [writeBit_other _ _ _ _ hwH, e2.2.2 w hwy, s1o w hwH]
  have s3y : ECDSAAdd.regValue L.point.y s3.basis = ECDSAAdd.regValue L.point.y s2.basis := by
    rw [← hs3]
    exact ECDSAAdd.Arithmetic.regValue_congr _ _ _
      (fun w hw' => writeBit_other _ _ _ _ (fun h => hHy (h ▸ hw')))
  -- s4, s5: the two mask blocks
  have e4 := zblock_effect L hw hn C ([]) s3
  have e5 := fourWrite_effect L hw hn C ([]) (run (zblock L C) ([]) s3)
  change PointEffect _ _ _ _ _ (run (zblock L C) ([]) s3) at e4
  generalize hs4 : run (zblock L C) ([]) s3 = s4 at e4 e5
  generalize hs5 : run (fourWrite L C) ([]) s4 = s5 at e5
  have flag4 : ∀ q ∈ L.inPlaceFlags, s4.basis q = st.basis q := fun q hq =>
    (e4.outside q (point_flag_away L hn q hq)).trans (s3o q (notY q (point_flag_away L hn q hq)))
  rw [flag4 _ (by simp [inPlaceFlags]), flag4 _ (by simp [inPlaceFlags]),
    flag4 _ (by simp [inPlaceFlags]), flag4 _ (by simp [inPlaceFlags])] at e5
  rw [s3o _ hHy, s3o _ (notY _ (point_flag_away L hn _ (by simp [inPlaceFlags])))] at e4
  have out5 : ∀ w ∉ PointAddLayout.pointWires L.point, s5.basis w = st.basis w := fun w hw' =>
    ((e5.outside w hw').trans (e4.outside w hw')).trans (s3o w (notY w hw'))
  have c5 : ECDSAAdd.regValue L.dialogPool s5.basis = 0 := by
    rw [ECDSAAdd.Arithmetic.regValue_zero] at hclean ⊢
    intro w hw'; rw [out5 w (point_pool_away L hn w hw')]; exact hclean w hw'
  -- the reference
  have eT := dialogCorners_effect L hw hn C st
  generalize hT : run (pointDialogCorners L C) ([]) st = T at eT hYout
  have f5 : s5.basis L.point.finite = ((st.basis L.point.finite ^^
      ((st.basis L.core.equalNegY ^^ st.basis L.doubleSelect) && pointFinite (C+C))) ^^
      ((((st.basis L.doubleSelect ^^ st.basis L.infinitySelect) ^^ st.basis L.genericSelect) ^^
        st.basis L.core.equalNegY) && pointFinite C)) := by
    rw [e5.finite, e4.finite, s3o _ hfy]
  have x5 : ECDSAAdd.regValue L.point.x s5.basis = (ECDSAAdd.regValue L.point.x st.basis ^^^
      (if (st.basis L.core.equalNegY ^^ st.basis L.doubleSelect) then pointX (C+C) else 0)) ^^^
      (if (((st.basis L.doubleSelect ^^ st.basis L.infinitySelect) ^^ st.basis L.genericSelect) ^^
        st.basis L.core.equalNegY) then pointX C else 0) := by
    rw [e5.x, e4.x, ECDSAAdd.Arithmetic.regValue_congr _ _ _ (fun w hw' => s3o w (hxy w hw'))]
  have y5 : ECDSAAdd.regValue L.point.y s5.basis = (ECDSAAdd.regValue L.point.y s2.basis ^^^
      (if (st.basis L.core.equalNegY ^^ st.basis L.doubleSelect) then pointY (C+C) else 0)) ^^^
      (if (((st.basis L.doubleSelect ^^ st.basis L.infinitySelect) ^^ st.basis L.genericSelect) ^^
        st.basis L.core.equalNegY) then pointY C else 0) := by
    rw [e5.y, e4.y, s3y]
  rw [e2.2.1] at y5
  -- final comparison, by the corner case
  have finish : ∀ (hy5 : ECDSAAdd.regValue L.point.y s5.basis < ECDSAAdd.p)
      (hf : s5.basis L.point.finite = T.basis L.point.finite)
      (hx : ECDSAAdd.regValue L.point.x s5.basis = ECDSAAdd.regValue L.point.x T.basis)
      (hy : ECDSAAdd.regValue L.point.y (run (negH L) m2 s5).basis = ECDSAAdd.regValue L.point.y T.basis),
      run (negH L) m2 s5 = T := by
    intro hy5 hf hx hy
    have e6 := negH_effect L hw hn s5 m2 hy5 c5
    apply point_state_eq L _ _ ?_ ?_ ?_ ?_ hy
    · rw [e6.1, e5.phase, e4.phase, s3p, eT.phase]
    · intro w hw'; rw [e6.2.2 w (notY w hw'), out5 w hw', eT.outside w hw']
    · rw [e6.2.2 _ hfy, hf]
    · rw [← hx]; exact ECDSAAdd.Arithmetic.regValue_congr _ _ _ (fun w hw' => e6.2.2 w (hxy w hw'))
  have s5H : s5.basis L.core.equalNegY = st.basis L.core.equalNegY := out5 _ pH
  have xx : ∀ a b : Nat, a ^^^ (a ^^^ b) = b := fun a b => by
    rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  have lc : ∀ a b c : Nat, a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := fun a b c => by
    rw [← Nat.xor_assoc, Nat.xor_comm a b, Nat.xor_assoc]
  dsimp only at eT
  cases hIv : st.basis L.genericSelect <;> cases hHv : st.basis L.core.equalNegY
  · -- ordinary, infinity and doubling corners: no negation is enabled
    rw [hIv, hHv] at f5 x5 y5 eT
    rw [hHv] at s5H
    have hyT : ECDSAAdd.regValue L.point.y s5.basis = ECDSAAdd.regValue L.point.y T.basis := by
      rw [y5, eT.y]
      cases st.basis L.doubleSelect <;> cases st.basis L.infinitySelect <;>
        simp [Nat.xor_assoc, xx, lc, Nat.xor_comm]
    have hy5 := hyT ▸ hYout
    refine finish hy5 ?_ ?_ ?_
    · rw [f5, eT.finite]
      cases st.basis L.doubleSelect <;> cases st.basis L.infinitySelect <;>
        cases pointFinite C <;> cases pointFinite (C+C) <;> simp
    · rw [x5, eT.x]
      cases st.basis L.doubleSelect <;> cases st.basis L.infinitySelect <;>
        simp [Nat.xor_assoc, xx, lc, Nat.xor_comm]
    · rw [(negH_effect L hw hn s5 m2 hy5 c5).2.1, s5H]
      simpa using hyT
  · -- the exception corner `-(C+C)`
    obtain ⟨hO, hD, _⟩ := hHx hHv
    have hv := (point_holds _ _ _).mp (hH hHv)
    rw [hIv, hHv, hO, hD] at f5 x5 y5 eT
    rw [hHv] at s5H
    have hy5v : ECDSAAdd.regValue L.point.y s5.basis = pointY C := by
      rw [y5, hv.2.2, pointY_neg_twice_mod]
      simp [Nat.xor_self]
    have hy5 : ECDSAAdd.regValue L.point.y s5.basis < ECDSAAdd.p := hy5v ▸ (point_coordinates_lt C).2
    refine finish hy5 ?_ ?_ ?_
    · rw [f5, eT.finite, hv.1, ECDSAAdd.ShorPort.pointFinite_neg, ECDSAAdd.ShorPort.pointFinite_neg]
      cases pointFinite C <;> cases pointFinite (C+C) <;> simp
    · rw [x5, eT.x, hv.2.1, ECDSAAdd.ShorPort.pointX_neg, ECDSAAdd.ShorPort.pointX_neg]
      simp [Nat.xor_assoc, xx]
    · rw [(negH_effect L hw hn s5 m2 hy5 c5).2.1, s5H, hy5v, eT.y, hv.2.2]
      simp [Nat.xor_assoc, xx, pointY_neg_mod]
  · -- the inverse corner `-C`
    obtain ⟨hO, hD⟩ := hIx hIv
    have hv := (point_holds _ _ _).mp (hI hIv)
    rw [hIv, hHv, hO, hD] at f5 x5 y5 eT
    rw [hHv] at s5H
    have hy5v : ECDSAAdd.regValue L.point.y s5.basis = 0 := by
      rw [y5, hv.2.2, pointY_neg_twice_mod]
      simp [Nat.xor_self]
    have hy5 : ECDSAAdd.regValue L.point.y s5.basis < ECDSAAdd.p := by
      rw [hy5v]; norm_num [ECDSAAdd.p]
    refine finish hy5 ?_ ?_ ?_
    · rw [f5, eT.finite, hv.1, ECDSAAdd.ShorPort.pointFinite_neg]
      cases pointFinite C <;> simp
    · rw [x5, eT.x, hv.2.1, ECDSAAdd.ShorPort.pointX_neg]
      simp [Nat.xor_self]
    · rw [(negH_effect L hw hn s5 m2 hy5 c5).2.1, s5H, hy5v, eT.y, hv.2.2]
      simp [Nat.xor_self]
  · exact absurd hIv (by rw [(hHx hHv).2.2]; decide)


/-- On the boundary state of the corner block, the merged corners agree with the reference corners
for all record lists. -/
theorem fourCorners_second [DecidableEq Point] (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (R C : Point) (hc : C ≠ 0) (b : Bool) (f : BasisState)
    (ho : f L.infinitySelect = dialogInfinity b R)
    (hd : f L.doubleSelect = dialogDouble b R C)
    (hi : f L.genericSelect = dialogInversePoint b R C)
    (hh : f L.core.equalNegY = dialogException b R C)
    (st : State) (hs : PointDialogBoundary L (if dialogOrdinary b R C then R+C else R) b f st.basis)
    (m m' : List Bool) :
    run (fourCorners L C) m st = run (secondCorners L C) m' st := by
  have flag : ∀ q ∈ L.inPlaceFlags, st.basis q = f q := hs.flags
  have hO := (flag _ (by simp [inPlaceFlags])).trans ho
  have hD := (flag _ (by simp [inPlaceFlags])).trans hd
  have hIf := (flag _ (by simp [inPlaceFlags])).trans hi
  have hHf := (flag _ (by simp [inPlaceFlags])).trans hh
  have values := (point_holds _ _ _).mp hs.point
  have hY : ECDSAAdd.regValue L.point.y st.basis < ECDSAAdd.p := by
    rw [values.2.2]; exact (point_coordinates_lt _).2
  have hclean := hs.clean
  -- the exceptional corners keep the register at `R`
  have ordFalse : ∀ (h : dialogOrdinary b R C = false), Holds.holds st.basis L.point R := by
    intro h; have hp := hs.point; rw [h] at hp; simpa using hp
  have hHR : st.basis L.core.equalNegY = true → b = true ∧ dialogExceptionEnabled C ∧
      R = dialogExceptionPoint C := by
    intro hb
    have := hHf.symm.trans hb
    simp only [dialogException, Bool.and_eq_true, decide_eq_true_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  have hIR : st.basis L.genericSelect = true → b = true ∧ R = -C := by
    intro hb
    have := hIf.symm.trans hb
    simp only [dialogInversePoint, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this
  have hcorner : st.basis L.core.equalNegY = true → Holds.holds st.basis L.point (-(C+C)) := by
    intro hb
    obtain ⟨hb', _, hR⟩ := hHR hb
    have hG : dialogOrdinary b R C = false := by
      apply Bool.eq_false_iff.mpr
      intro hg
      exact ((dialogOrdinary_true b R C hc).mp hg).2.2.2.2 hR
    simpa only [hR, dialogExceptionPoint] using ordFalse hG
  have hInv : st.basis L.genericSelect = true → Holds.holds st.basis L.point (-C) := by
    intro hb
    obtain ⟨hb', hR⟩ := hIR hb
    have hG : dialogOrdinary b R C = false := by
      apply Bool.eq_false_iff.mpr
      intro hg
      exact ((dialogOrdinary_true b R C hc).mp hg).2.2.2.1 hR
    simpa only [hR] using ordFalse hG
  have hHx : st.basis L.core.equalNegY = true → st.basis L.infinitySelect = false ∧
      st.basis L.doubleSelect = false ∧ st.basis L.genericSelect = false := by
    intro hb
    obtain ⟨hb', ⟨e0, eC, eN⟩, hR⟩ := hHR hb
    refine ⟨?_, ?_, ?_⟩
    · rw [hO]; simp [dialogInfinity, hR, e0]
    · rw [hD]; simp [dialogDouble, hR, eC]
    · rw [hIf]; simp [dialogInversePoint, hR, eN]
  have hIx : st.basis L.genericSelect = true → st.basis L.infinitySelect = false ∧
      st.basis L.doubleSelect = false := by
    intro hb
    obtain ⟨hb', hR⟩ := hIR hb
    refine ⟨?_, ?_⟩
    · rw [hO]; simp [dialogInfinity, hR, hc]
    · rw [hD, dialogDouble, hR]
      by_cases h : C = -C
      · have h0 : decide (C ≠ -C) = false := decide_eq_false (fun hne => hne h)
        rw [h0]; simp
      · have h' : -C ≠ C := fun e => h e.symm
        simp [h']
  -- the reference output is a valid point
  have href := singleRowCorners_eq L hw hn C st hY hclean hcorner ([])
  have hb := singleRowCorners_boundary L hw hn R C hc b f ho hd hi hh st ([]) hs
  have hYout : ECDSAAdd.regValue L.point.y (run (pointDialogCorners L C) ([]) st).basis < ECDSAAdd.p := by
    rw [← href]
    rw [((point_holds _ _ _).mp hb.2.point).2.2]
    exact (point_coordinates_lt _).2
  rw [← secondCorners_run L hn C m' st, singleRowCorners_eq L hw hn C st hY hclean hcorner m']
  exact fourCorners_eq L hw hn C st hY hclean hcorner hInv hHx hIx hYout m

end
end ShorECDLP.Entrant.WEX

/-! ## Scratch-level merged corners and the row transport -/

namespace ShorECDLP.Entrant.WEX
open ShorECDLP.Challenge ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant ECDSAAdd.Secp256k1 ECDSAAdd.ShorPort
open ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Arithmetic.CompressedPointDialog
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem fourCorners_third [DecidableEq Point] (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (R C : Point) (hc : C ≠ 0) (b : Bool) (f : BasisState)
    (ho : f L.infinitySelect = dialogInfinity b R)
    (hd : f L.doubleSelect = dialogDouble b R C)
    (hi : f L.genericSelect = dialogInversePoint b R C)
    (hh : f L.core.equalNegY = dialogException b R C)
    (st : State) (hs : PointDialogBoundary L (if dialogOrdinary b R C then R+C else R) b f st.basis)
    (m m' : List Bool) :
    run (fourCorners L C) m st = run (thirdCorners L C) m' st := by
  rw [thirdCorners_run L hw hn C m' st]
  exact fourCorners_second L hw hn R C hc b f ho hd hi hh st hs m m'

def scrNegE : Program := [.CX streamLayout.genericSelect streamLayout.core.equalNegY]
def scrW1 : Program := [.CX streamLayout.infinitySelect streamLayout.doubleSelect,
  .CX streamLayout.genericSelect streamLayout.doubleSelect, .CX streamLayout.core.equalNegY streamLayout.doubleSelect]
def scrW2 : Program := [.CX streamLayout.core.equalNegY streamLayout.doubleSelect,
  .CX streamLayout.genericSelect streamLayout.doubleSelect, .CX streamLayout.infinitySelect streamLayout.doubleSelect]

/-- Merged corners, doubled point read from the output scratch. -/
def scrECorners (rows : Nat → Fin 32768) : WCode 32768 :=
  wLiteral scrNegE ++ wLiteral scrNegP ++ wLiteral scrNegE ++
  wLiteral scrSw1 ++ wLiteral (ccxList streamLayout.core.equalNegY scrDWires scrDTargets) ++ wLiteral scrSw1 ++
  wLiteral scrW1 ++
  wPoint streamLayout.doubleSelect streamLayout.point (wBit rows .infinity) (wFields rows .x) (wFields rows .y) ++
  wLiteral scrW2 ++ wLiteral scrNegP

/-- Merged corners, doubled point read by a table lookup (instantiation bridge only). -/
def scrFCorners (rows : Nat → Fin 32768) : WCode 32768 :=
  wLiteral scrNegE ++ wLiteral scrNegP ++ wLiteral scrNegE ++
  wLiteral scrSw1 ++ sfxDp rows ++ wLiteral scrSw1 ++
  wLiteral scrW1 ++
  wPoint streamLayout.doubleSelect streamLayout.point (wBit rows .infinity) (wFields rows .x) (wFields rows .y) ++
  wLiteral scrW2 ++ wLiteral scrNegP

theorem scrFCorners_inst (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (address : Nat) (C : Point)
    (h : RowReads read (rows address) C) :
    (specialize (scrFCorners rows) address).instantiate read = fourCorners streamLayout C := by
  have hxl : streamLayout.point.x.length = 256 := streamLayout_widths.inputX
  have hyl : streamLayout.point.y.length = 256 := streamLayout_widths.inputY
  have fC : read (bitRef (rows address) .infinity 0) = !pointFinite C := by
    rw [h.bit _ 0 (by decide), infinity_bit]
  have fD : read (bitRef (rows address) .doubleInfinity 0) = !pointFinite (C+C) := by
    rw [h.bit _ 0 (by decide), doubleInfinity_bit]
  have xC := fieldBits_reads h .x _ (field_x C)
  have yC := fieldBits_reads h .y _ (field_y C)
  have xD := fieldBits_reads h .doubleX _ (field_doubleX C)
  have yD := fieldBits_reads h .doubleY _ (field_doubleY C)
  rw [← hxl] at xC xD
  rw [← hyl] at yC yD
  simp only [scrFCorners, sfxDp, specialize_append, specialize_point, specialize_literal,
    wBit, wFields, Tmpl.instantiate_append, Tmpl.instantiate_lit,
    maskedPointT_inst read _ streamLayout.point _ _ _ C fC xC yC,
    maskedPointT_inst read _ streamLayout.point _ _ _ (C+C) fD xD yD]
  simp only [fourCorners, fourWrite, negH, scrNegP, scrNegE, scrSw1, scrW1, scrW2, List.append_assoc,
    List.cons_append, List.nil_append]

theorem scrFCorners_inst2 (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (a : Nat) :
    (specialize (scrFCorners rows) a).instantiate read =
      scrNegE ++ (scrNegP ++ (scrNegE ++ (scrSw1 ++ (cBits streamLayout.core.equalNegY scrDTargets
        (portBits read (scrShortBits rows) a ++ portBits read (scrDExtraBits rows) a) ++ (scrSw1 ++ (scrW1 ++
        (cBits streamLayout.doubleSelect scrDTargets (portBits read (scrCPorts rows) a) ++ (scrW2 ++ scrNegP)))))))) := by
  have e0 : sfxDp rows = [.lookup (some streamLayout.core.equalNegY) (scrDPointPorts rows)] := rfl
  have e1 : wPoint streamLayout.doubleSelect streamLayout.point (wBit rows .infinity) (wFields rows .x) (wFields rows .y) =
      [.lookup (some streamLayout.doubleSelect) (scrCPorts rows)] := rfl
  have hD := scrDPointPorts_targets rows
  have hB := scrDPointPorts_bits read rows a
  simp only [scrFCorners, e0, e1, specialize_append, Tmpl.instantiate_append, specialize_literal, Tmpl.instantiate_lit,
    scr_lookup_some_inst, hD, hB, scrCPorts, scr_point_targets, List.append_assoc]

theorem scrECorners_inst (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (a : Nat) :
    (specialize (scrECorners rows) a).instantiate read =
      scrNegE ++ (scrNegP ++ (scrNegE ++ (scrSw1 ++ (ccxList streamLayout.core.equalNegY scrDWires scrDTargets ++
        (scrSw1 ++ (scrW1 ++
        (cBits streamLayout.doubleSelect scrDTargets (portBits read (scrCPorts rows) a) ++ (scrW2 ++ scrNegP)))))))) := by
  have e1 : wPoint streamLayout.doubleSelect streamLayout.point (wBit rows .infinity) (wFields rows .x) (wFields rows .y) =
      [.lookup (some streamLayout.doubleSelect) (scrCPorts rows)] := rfl
  simp only [scrECorners, e1, specialize_append, Tmpl.instantiate_append, specialize_literal, Tmpl.instantiate_lit,
    scr_lookup_some_inst, scrCPorts, scr_point_targets, List.append_assoc]

theorem scrE_flags :
    (∀ q ∈ ECDSAAdd.wires scrNegE, q ∈ [streamLayout.control, streamLayout.core.generic, streamLayout.infinitySelect,
      streamLayout.doubleSelect, streamLayout.genericSelect, streamLayout.core.equalNegY]) ∧
    (∀ q ∈ ECDSAAdd.wires scrW1, q ∈ [streamLayout.control, streamLayout.core.generic, streamLayout.infinitySelect,
      streamLayout.doubleSelect, streamLayout.genericSelect, streamLayout.core.equalNegY]) ∧
    (∀ q ∈ ECDSAAdd.wires scrW2, q ∈ [streamLayout.control, streamLayout.core.generic, streamLayout.infinitySelect,
      streamLayout.doubleSelect, streamLayout.genericSelect, streamLayout.core.equalNegY]) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro q hq <;>
    simp [scrNegE, scrW1, scrW2, ECDSAAdd.wires, ECDSAAdd.Instr.wires] at hq ⊢ <;>
    tauto

theorem scrE_cornerSim (S : List Wire) (K kD kC : List Bool) (hS : S = scrAllWires)
    (hmapD : scrDWires.map (xMask S K) = kD) :
    ScrSim S K
      (scrNegE ++ (scrNegP ++ (scrNegE ++ (scrSw1 ++ (ccxList streamLayout.core.equalNegY scrDWires scrDTargets ++
        (scrSw1 ++ (scrW1 ++ (cBits streamLayout.doubleSelect scrDTargets kC ++ (scrW2 ++ scrNegP)))))))))
      (scrNegE ++ (scrNegP ++ (scrNegE ++ (scrSw1 ++ (cBits streamLayout.core.equalNegY scrDTargets kD ++
        (scrSw1 ++ (scrW1 ++ (cBits streamLayout.doubleSelect scrDTargets kC ++ (scrW2 ++ scrNegP))))))))) := by
  subst hS
  have hneg := scrD_negSim K
  have hs := scrD_swSim K
  have fl := scrE_flags
  have hE := ScrSim.disjoint scrAllWires K scrNegE (fun w hw' => scrAll_flag_avoid w hw' _ fl.1)
  have hW1 := ScrSim.disjoint scrAllWires K scrW1 (fun w hw' => scrAll_flag_avoid w hw' _ fl.2.1)
  have hW2 := ScrSim.disjoint scrAllWires K scrW2 (fun w hw' => scrAll_flag_avoid w hw' _ fl.2.2)
  have hcc := scrD_ccxSim K kD hmapD
  have hC := scrD_cbitsSim K kC streamLayout.doubleSelect
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  exact hE.append (hneg.append (hE.append (hs.1.append (hcc.append (hs.1.append (hW1.append (hC.append
    (hW2.append hneg))))))))

/-- In-place middle comparisons shared by both suffixes. -/
def midIP (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (a : Nat) : Program :=
  pointDialogGenericFlag streamLayout ++
    (xBits scrPairTargets (portBits read (scrPairBits rows (wBit rows .y)) a) ++ (scrP1 ++
      ((xBits scrPairTargets (portBits read (scrPairBits rows (wBit rows .y)) a) ++ [.X (yLow streamLayout)]) ++
      (xBits scrShortTargets (portBits read (scrShortBits rows) a) ++
        (scrP2 ++ xBits scrShortTargets (portBits read (scrShortBits rows) a))))))

/-- Flag clears before the padding. -/
def tail0 : Program :=
  zeroFlag streamLayout.point.finite streamLayout.control streamLayout.genericSelect ++
    ([.CX streamLayout.control streamLayout.core.equalX] ++ [.CX streamLayout.control streamLayout.core.double])

theorem scrE_sim (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (a : Nat) :
    ScrSim scrAllWires ((portBits read (scrPairBits rows (wBit rows .y)) a ++ portBits read (scrShortBits rows) a) ++
        portBits read (scrDExtraBits rows) a)
      ((scrNegE ++ (scrNegP ++ (scrNegE ++ (scrSw1 ++ (ccxList streamLayout.core.equalNegY scrDWires scrDTargets ++
        (scrSw1 ++ (scrW1 ++ (cBits streamLayout.doubleSelect scrDTargets (portBits read (scrCPorts rows) a) ++
          (scrW2 ++ scrNegP))))))))) ++
       (pointDialogGenericFlag streamLayout ++
       (cxList scrPairWires scrPairTargets ++ (scrP1 ++ ((cxList scrPairWires scrPairTargets ++ [.X (yLow streamLayout)]) ++
        (cxList scrShortWires scrShortTargets ++ (scrP2 ++ cxList scrShortWires scrShortTargets)))))))
      ((scrNegE ++ (scrNegP ++ (scrNegE ++ (scrSw1 ++ (cBits streamLayout.core.equalNegY scrDTargets
        (portBits read (scrShortBits rows) a ++ portBits read (scrDExtraBits rows) a) ++
        (scrSw1 ++ (scrW1 ++ (cBits streamLayout.doubleSelect scrDTargets (portBits read (scrCPorts rows) a) ++
          (scrW2 ++ scrNegP))))))))) ++ midIP read rows a) := by
  have hm := scrD_maps read rows a
  exact (scrE_cornerSim _ _ _ _ rfl hm.2.2).append (scrD_midSim _ _ _ _ rfl hm.1 hm.2.1)

/-- Output half with the merged corners; the padding drops by the 1,022 extra negation records. -/
def portSuffixCodeE (rows : Nat → Fin 32768) : WCode 32768 :=
  [.lookup none (scrDPorts rows)] ++ scrECorners rows ++ wLiteral (pointDialogGenericFlag streamLayout) ++
  scrDMiddle ++ [.lookup none (scrDPorts rows)] ++
  wLiteral (zeroFlag streamLayout.point.finite streamLayout.control streamLayout.genericSelect) ++
  wLiteral ([.CX streamLayout.control streamLayout.core.equalX]) ++
  wLiteral ([.CX streamLayout.control streamLayout.core.double]) ++
  wLiteral (Arith.padding (streamLayout.core.poolWire 0) 48842)

theorem portSuffixE_inst (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (a : Nat) :
    (specialize (portSuffixCodeE rows) a).instantiate read =
      xBits scrAllWires ((portBits read (scrPairBits rows (wBit rows .y)) a ++ portBits read (scrShortBits rows) a) ++
        portBits read (scrDExtraBits rows) a) ++
      ((specialize (scrECorners rows) a).instantiate read ++ (pointDialogGenericFlag streamLayout ++
       (cxList scrPairWires scrPairTargets ++ (scrP1 ++ ((cxList scrPairWires scrPairTargets ++ [.X (yLow streamLayout)]) ++
        (cxList scrShortWires scrShortTargets ++ (scrP2 ++ cxList scrShortWires scrShortTargets))))))) ++
      xBits scrAllWires ((portBits read (scrPairBits rows (wBit rows .y)) a ++ portBits read (scrShortBits rows) a) ++
        portBits read (scrDExtraBits rows) a) ++
      (zeroFlag streamLayout.point.finite streamLayout.control streamLayout.genericSelect ++
        ([.CX streamLayout.control streamLayout.core.equalX] ++ ([.CX streamLayout.control streamLayout.core.double] ++
          Arith.padding (streamLayout.core.poolWire 0) 48842))) := by
  simp only [portSuffixCodeE, scrDMiddle, specialize_append, Tmpl.instantiate_append, scr_lookup_inst, specialize_literal,
    Tmpl.instantiate_lit, scr_chain_inst, scrDPorts_targets, scrDPorts_bits, List.append_assoc]

theorem portSuffixE_inplace (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (a : Nat) (C : Point)
    (row : RowReads read (rows a) C) (m : List Bool) (s : State) (hs : ∀ w ∈ scrAllWires, s.basis w = false) :
    run ((specialize (portSuffixCodeE rows) a).instantiate read) m s =
      run (fourCorners streamLayout C ++ midIP read rows a ++ tail0 ++
        Arith.padding (streamLayout.core.poolWire 0) 48842) m s := by
  rw [portSuffixE_inst, scrECorners_inst, scr_sandwich_append _ _ _ _ _ (scrE_sim read rows a) m s hs,
    ← scrFCorners_inst2, scrFCorners_inst read rows a C row]
  simp only [tail0, List.append_assoc]

theorem portSuffixD_inplace (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (a : Nat) (C : Point)
    (row : RowReads read (rows a) C) (m : List Bool) (s : State) (hs : ∀ w ∈ scrAllWires, s.basis w = false) :
    run ((specialize (portSuffixCodeD rows) a).instantiate read) m s =
      run (thirdCorners streamLayout C ++ midIP read rows a ++ tail0 ++
        Arith.padding (streamLayout.core.poolWire 0) 49864) m s := by
  rw [portSuffixD_inst, scrDCorners_inst, scr_sandwich_append _ _ _ _ _ (scrD_sim read rows a) m s hs]
  have eC : scrNegP ++ (scrSw1 ++ (cBits streamLayout.core.equalNegY scrDTargets
        (portBits read (scrShortBits rows) a ++ portBits read (scrDExtraBits rows) a) ++ (scrSw1 ++ (scrSw2 ++
        (cBits streamLayout.doubleSelect scrDTargets (portBits read (scrCPorts rows) a) ++ (scrSw2 ++ (scrSw3 ++
        (cBits streamLayout.core.equalNegY scrDTargets (portBits read (scrNPorts rows) a) ++ scrSw3)))))))) =
      thirdCorners streamLayout C := by
    rw [← scrCorners_inst2, scrCorners_inst read rows a C row]
  rw [eC]
  simp only [midIP, tail0, List.append_assoc]

def portFiniteE (rows : Nat → Fin 32768) : WCode 32768 :=
  portPrefixCode rows ++ wGeneric streamLayout rows ++ portSuffixCodeE rows

def portRowCodeE (rows : Nat → Fin 32768) : WCode 32768 :=
  wLiteral ([.X 838]) ++ portFiniteE rows ++ wLiteral ([.X 838])


theorem mid_replace (A B B' E : Program) (hE : measurementCount E = 0) (s : State)
    (h : ∀ k n, run B n (run A k s) = run B' n (run A k s)) (m : List Bool) :
    run (A ++ B ++ E) m s = run (A ++ B' ++ E) m s := by
  rw [RecordShift.run_append' (A ++ B), RecordShift.run_append' (A ++ B'),
    RecordShift.run_no_records' E hE (m.drop (measurementCount (A ++ B))),
    RecordShift.run_no_records' E hE (m.drop (measurementCount (A ++ B'))),
    RecordShift.run_append' A, RecordShift.run_append' A, h]

attribute [local irreducible] streamLayout ECDSAAdd.regValue ECDSAAdd.run in
theorem portRowE_of_3 (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (address : Nat)
    (R : Point) {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (hr : RowReads read (rows address) (.some hc))
    (h₁ : cy ≠ -cy) (h₂ : exceptionBit (.some hc) = true)
    (hD : (.some hc : Point)+.some hc ≠ 0)
    (hDo : ShorECDLP.order • ((.some hc : Point)+.some hc) = 0)
    (s : BasisState) (hs : PointDialogBoundary streamLayout R true (fun _=>false) (flipInfinity s))
    (t : State) (href : ∀ m, run ((specialize (portRowCode3 rows) address).instantiate read) m ⟨false,s⟩ = t)
    (m : List Bool) :
    run ((specialize (portRowCodeE rows) address).instantiate read) m ⟨false,s⟩ = t := by
  classical
  have hw := streamLayout_widths
  have hn := streamLayout_nodup
  have hop := WEXUnlookup.row_opposite read rows address hc hr h₁
  have hpe := WEXUnlookup.prefixCode_equiv read streamLayout hw hn rows address hop
  have hpi := WEXUnlookup.referencePrefix_inst read streamLayout hw rows address hc hr h₁ h₂ hD hDo
  have hG : (specialize (wGeneric streamLayout rows) address).instantiate read = Arith.genericS streamLayout cx cy := by
    rw [specialize_generic]
    exact Arith.genericT_inst streamLayout hc hr
  have hclean0 : ∀ w ∈ scrWires, (⟨false, flipInfinity s⟩ : State).basis w = false :=
    fun w hw' => (regValue_zero _ _).mp hs.clean w (scrWires_pool w hw')
  let P0' := (specialize (portPrefixCode rows) address).instantiate read
  let P0 := (specialize (WEXUnlookup.prefixCode streamLayout rows) address).instantiate read
  let G0 := (specialize (wGeneric streamLayout rows) address).instantiate read
  let BD := (specialize (portSuffixCodeD rows) address).instantiate read
  let BE := (specialize (portSuffixCodeE rows) address).instantiate read
  let C : Point := .some hc
  have hC0 : C ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  let O := dialogInfinity true R
  let D := dialogDouble true R C
  let I := dialogInversePoint true R C
  let H := dialogException true R C
  let Gf := dialogOrdinary true R C
  let E := true && decide (dialogExceptionEnabled C)
  let K := true && decide (cy≠-cy)
  have reads := dialogFlagState_read streamLayout hn O D I Gf E H K
  let A : Program := ([.X 838] : Program) ++ P0' ++ G0
  -- the semantic corner boundary after the prefix and the generic block
  have hbound : ∀ k, PointDialogBoundary streamLayout (if Gf then R + C else R) true
      (dialogFlagState streamLayout O D I Gf E H K) (run A k ⟨false,s⟩).basis := by
    intro k
    have h7 := Arith.boundary_genericS streamLayout hw hn R true (dialogFlagState streamLayout O D I Gf E H K) hc
      (fun hg => ((dialogOrdinary_true true R C hC0).mp (reads.2.2.2.1.symm.trans hg)).2)
    rw [reads.2.2.2.1] at h7
    have hP (k' : List Bool) : PointDialogBoundary streamLayout R true (dialogFlagState streamLayout O D I Gf E H K)
        (run P0 k' ⟨false, flipInfinity s⟩).basis := by
      have hb := (WEXUnlookup.prefixS_checked streamLayout hw hn R hc true ⟨false, flipInfinity s⟩ k' hs).2
      have he := hpe.2 k' ⟨false, flipInfinity s⟩
      rw [hpi] at he
      change PointDialogBoundary streamLayout R true (dialogFlagState streamLayout O D I Gf E H K)
        (run ((specialize (WEXUnlookup.prefixCode streamLayout rows) address).instantiate read) k' ⟨false, flipInfinity s⟩).basis
      rw [← he]
      exact hb
    obtain ⟨k1, k2, hA⟩ := portRun_split ([.X 838] : Program) P0' G0 ⟨false,s⟩ ⟨false, flipInfinity s⟩
      (fun n => flip_run _ n) k
    change PointDialogBoundary _ _ _ _ (run (([.X 838] : Program) ++ P0' ++ G0) k ⟨false,s⟩).basis
    rw [hA]
    have hpp : run P0' k2 ⟨false, flipInfinity s⟩ = run P0 k2 ⟨false, flipInfinity s⟩ :=
      portPrefix_run read rows address hop k2 _ hclean0
    rw [hpp]
    have hG' : G0 = Arith.genericS streamLayout cx cy := hG
    have hu := (h7 (run P0 k2 ⟨false, flipInfinity s⟩) k1 (hP _)).2
    rw [← hG'] at hu
    exact hu
  have hscr : ∀ k, ∀ w ∈ scrAllWires, (run A k ⟨false,s⟩).basis w = false := fun k w hw' =>
    (regValue_zero _ _).mp (hbound k).clean w (scrAll_pool w hw')
  have e3 : (specialize (portRowCode3 rows) address).instantiate read = A ++ BD ++ ([.X 838] : Program) := by
    simp only [portRowCode3, portFinite3, specialize_append, specialize_literal, Tmpl.instantiate_append,
      Tmpl.instantiate_lit, A, P0', G0, BD, List.append_assoc]
  have e4 : (specialize (portRowCodeE rows) address).instantiate read = A ++ BE ++ ([.X 838] : Program) := by
    simp only [portRowCodeE, portFiniteE, specialize_append, specialize_literal, Tmpl.instantiate_append,
      Tmpl.instantiate_lit, A, P0', G0, BE, List.append_assoc]
  have hX : measurementCount ([.X 838] : Program) = 0 := rfl
  -- both rows in their in-place form
  have r3 : ∀ m, run (A ++ thirdCorners streamLayout C ++ (midIP read rows address ++ tail0) ++
      RecordShift.pad (streamLayout.core.poolWire 0) 49864 ++ ([.X 838] : Program)) m ⟨false,s⟩ = t := by
    intro m
    rw [← href m, e3]
    have := mid_replace A BD (thirdCorners streamLayout C ++ midIP read rows address ++ tail0 ++
      Arith.padding (streamLayout.core.poolWire 0) 49864) ([.X 838] : Program) hX ⟨false,s⟩
      (fun k n => portSuffixD_inplace read rows address C hr n _ (hscr k)) m
    rw [this]
    simp only [RecordShift.pad, Arith.padding, List.append_assoc]
  have r4 := RecordShift.shift_padding A (thirdCorners streamLayout C) (fourCorners streamLayout C)
    (midIP read rows address ++ tail0) ([.X 838] : Program) (streamLayout.core.poolWire 0) 49864 48842
    (by norm_num) hX ⟨false,s⟩ t r3
    (fun mA mB mB' => fourCorners_third streamLayout hw hn R C hC0 true
      (dialogFlagState streamLayout O D I Gf E H K) reads.1 reads.2.1 reads.2.2.1 reads.2.2.2.2.2.1
      (run A mA ⟨false,s⟩) (hbound mA) mB' mB) m
  rw [e4, mid_replace A BE (fourCorners streamLayout C ++ midIP read rows address ++ tail0 ++
      Arith.padding (streamLayout.core.poolWire 0) 48842) ([.X 838] : Program) hX ⟨false,s⟩
      (fun k n => portSuffixE_inplace read rows address C hr n _ (hscr k)) m]
  rw [← r4]
  simp only [RecordShift.pad, Arith.padding, List.append_assoc]

/-- Any record-independent result of the frontier row transfers to the merged-corner row. -/
theorem portRowE_transport (a : Nat) (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (s : BasisState) (hs : liveReady s) (t : ECDSAAdd.State)
    (href : ∀ m, ECDSAAdd.run ((specialize (normalizeW (portRowCode3 probeRows)) a).instantiate
      (readConstant coeffs Q)) m ⟨false,s⟩ = t) (m : List Bool) :
    ECDSAAdd.run ((specialize (normalizeW (portRowCodeE probeRows)) a).instantiate (readConstant coeffs Q)) m ⟨false,s⟩ = t := by
  rw [specialize_normalize_run]
  have href' : ∀ m, ECDSAAdd.run ((specialize (portRowCode3 probeRows) a).instantiate (readConstant coeffs Q))
      m ⟨false,s⟩ = t := fun m => by rw [← specialize_normalize_run]; exact href m
  let C := Single.Physical.tablePoint coeffs Q a
  have hC : C ≠ 0 := hn _
  have hord : ShorECDLP.order • C = 0 := Single.Physical.tablePoint_order coeffs Q hQ a
  obtain ⟨P,hP⟩ := hs.1.2
  have work : ECDSAAdd.regValue streamLayout.work s = 0 :=
    (regValue_zero _ _).mpr (fun w hw => hs.2.1 w (List.mem_append_left _ hw))
  have h838 : (838 : Wire) ∉ streamLayout.work := by
    intro hm; have h := streamWork_lower _ hm; norm_num at h
  have pool : ECDSAAdd.regValue streamLayout.work (flipInfinity s) = 0 :=
    (reg_update_outside _ _ _ _ h838).trans work
  have clean (w : Wire) (hw : w ∈ streamLayout.inPlaceFlags ++ streamLayout.dialogPool) :
      flipInfinity s w = false := (regValue_zero _ _).mp pool w (one_boundary_work_subset streamLayout hw)
  have initial : PointDialogBoundary streamLayout (Bridge.toB P) true (fun _=>false) (flipInfinity s) := by
    refine ⟨flipInfinity_holds s (Bridge.toB P) (StreamPoint.of_coordinates s P hs.1.1.1.1 hP),?_,?_,?_⟩
    · simpa [streamLayout_control,flipInfinity,ECDSAAdd.writeBit] using hs.1.1.1.2
    · intro w hw; exact clean w (by simp [hw])
    · exact (regValue_zero _ _).mpr (fun w hw => clean w (by simp [hw]))
  cases he : Bridge.toB C with
  | zero =>
    have hzero : C = 0 := congrArg ECDSAAdd.ShorPort.toA he
    exact (hC hzero).elim
  | @some cx cy hc =>
    have ce : C = toA (.some hc) := congrArg toA he
    have hr : RowReads (readConstant coeffs Q) (probeRows a) (.some hc) :=
      readConstant_rowReads coeffs Q _ _ ce
    have ho : ShorECDLP.order • (.some hc : Point) = 0 := by rw [← he]; exact hord
    have hp2 := torsion_unit_remainder_ne_zero (.some hc) ShorECDLP.order 2
      (WeierstrassCurve.Affine.Point.some_ne_zero hc) ho (by norm_num [ShorECDLP.order])
    have hp3 := torsion_unit_remainder_ne_zero (.some hc) ShorECDLP.order 3
      (WeierstrassCurve.Affine.Point.some_ne_zero hc) ho (by norm_num [ShorECDLP.order])
    have hd : (.some hc : Point)+.some hc ≠ 0 := by simpa only [two_nsmul] using hp2
    have ht : (.some hc : Point)+.some hc+.some hc ≠ 0 := by
      simpa only [show (3 : Nat) = 2+1 from rfl,succ_nsmul,two_nsmul] using hp3
    have en := enables_true hc hd ht
    have hdo : ShorECDLP.order • ((.some hc : Point)+.some hc) = 0 := by rw [nsmul_add,ho,zero_add]
    exact portRowE_of_3 (readConstant coeffs Q) probeRows a (Bridge.toB P) hc hr en.1 en.2 hd hdo s initial t href' m

end
end ShorECDLP.Entrant.WEX

/-! ## Ledgers of the merged-corner row -/

namespace ShorECDLP.Entrant.WEX
open ShorECDLP.Challenge ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant ECDSAAdd.Secp256k1 ECDSAAdd.ShorPort
open ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Arithmetic.CompressedPointDialog
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local irreducible] Arith.padding

def sfxZ0 : WCode 32768 := wLiteral (zeroFlag streamLayout.point.finite streamLayout.control streamLayout.genericSelect) ++
  wLiteral ([.CX streamLayout.control streamLayout.core.equalX]) ++
  wLiteral ([.CX streamLayout.control streamLayout.core.double])
def sfxPadE : WCode 32768 := wLiteral (Arith.padding (streamLayout.core.poolWire 0) 48842)
def sfxPadD : WCode 32768 := wLiteral (Arith.padding (streamLayout.core.poolWire 0) 49864)

theorem suffixE_split (rows : Nat → Fin 32768) :
    portSuffixCodeE rows = sfxL rows ++ (scrECorners rows ++ (sfxF ++ (scrDMiddle ++ (sfxL rows ++ (sfxZ0 ++ sfxPadE))))) ∧
    portSuffixCodeD rows = sfxL rows ++ (scrDCorners rows ++ (sfxF ++ (scrDMiddle ++ (sfxL rows ++ (sfxZ0 ++ sfxPadD))))) := by
  constructor
  · simp only [portSuffixCodeE, sfxL, sfxF, sfxZ0, sfxPadE, List.append_assoc]
  · simp only [portSuffixCodeD, sfxL, sfxF, sfxZ0, sfxPadD, List.append_assoc]

theorem cornersE_split (rows : Nat → Fin 32768) :
    scrECorners rows = wLiteral scrNegE ++ (wLiteral scrNegP ++ (wLiteral scrNegE ++ (wLiteral scrSw1 ++
      (sfxCC ++ (wLiteral scrSw1 ++ (wLiteral scrW1 ++ ([.lookup (some streamLayout.doubleSelect) (scrCPorts rows)] ++
      (wLiteral scrW2 ++ wLiteral scrNegP)))))))) := by
  simp only [scrECorners, sfxCC, List.append_assoc]; rfl

theorem cornersD_split (rows : Nat → Fin 32768) :
    scrDCorners rows = wLiteral scrNegP ++ (wLiteral scrSw1 ++ (sfxCC ++ (wLiteral scrSw1 ++ (wLiteral scrSw2 ++
      ([.lookup (some streamLayout.doubleSelect) (scrCPorts rows)] ++ (wLiteral scrSw2 ++ (wLiteral scrSw3 ++
      ([.lookup (some streamLayout.core.equalNegY) (scrNPorts rows)] ++ wLiteral scrSw3)))))))) := by
  simp only [scrDCorners, sfxCC, scrNegP, scrSw1, scrSw2, scrSw3, List.append_assoc]; rfl

theorem suffixE_member (rows : Nat → Fin 32768) (i : WInstr 32768) (h : i ∈ portSuffixCodeE rows) :
    i = WInstr.literal scrNegE ∨ i = WInstr.literal scrW1 ∨ i = WInstr.literal scrW2 ∨
    i = WInstr.literal (Arith.padding (streamLayout.core.poolWire 0) 48842) ∨ i ∈ portSuffixCodeD rows := by
  have hs := suffixE_split rows
  rw [hs.1, cornersE_split] at h
  rw [hs.2, cornersD_split]
  simp only [List.mem_append, wLiteral, sfxPadE, sfxPadD, List.mem_singleton, List.mem_cons, List.not_mem_nil,
    or_false] at h ⊢
  tauto

theorem flag_literal_facts (p : ECDSAAdd.Program)
    (hw : ∀ q ∈ ECDSAAdd.wires p, q ∈ streamLayout.inPlaceFlags) (hp : GatePhysical p) :
    ECDSAAdd.wires p ⊆ streamLayout.dialogUsedWires.toFinset ∧ GatePhysical p ∧
      ECDSAAdd.wires p ⊆ sourceSupport.toFinset := by
  refine ⟨?_, hp, ?_⟩
  · intro q hq
    exact List.mem_toFinset.mpr (by simp [dialogUsedWires, hw q hq])
  · intro q hq
    exact List.mem_toFinset.mpr (streamFlagsPoint_source (List.mem_append_left _ (hw q hq)))

theorem cx_flags_physical (l : List (Wire × Wire)) (h : ∀ e ∈ l, e.1 ≠ e.2) :
    GatePhysical (l.map fun e => Instr.CX e.1 e.2) := by
  intro i hi
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hi
  simpa [ECDSAAdd.RecordedQuantum.PhysicalInstr] using h e he

theorem newLiteral_facts :
    (ECDSAAdd.wires scrNegE ⊆ streamLayout.dialogUsedWires.toFinset ∧ GatePhysical scrNegE ∧
      ECDSAAdd.wires scrNegE ⊆ sourceSupport.toFinset) ∧
    (ECDSAAdd.wires scrW1 ⊆ streamLayout.dialogUsedWires.toFinset ∧ GatePhysical scrW1 ∧
      ECDSAAdd.wires scrW1 ⊆ sourceSupport.toFinset) ∧
    (ECDSAAdd.wires scrW2 ⊆ streamLayout.dialogUsedWires.toFinset ∧ GatePhysical scrW2 ∧
      ECDSAAdd.wires scrW2 ⊆ sourceSupport.toFinset) := by
  have d := flags_distinct streamLayout streamLayout_nodup
  refine ⟨flag_literal_facts _ ?_ ?_, flag_literal_facts _ ?_ ?_, flag_literal_facts _ ?_ ?_⟩
  · intro q hq; simp [scrNegE, ECDSAAdd.wires, ECDSAAdd.Instr.wires] at hq; rcases hq with rfl | rfl <;> simp [inPlaceFlags]
  · exact cx_flags_physical [(streamLayout.genericSelect, streamLayout.core.equalNegY)] (by simpa using d.2.2.2.1)
  · intro q hq; simp [scrW1, ECDSAAdd.wires, ECDSAAdd.Instr.wires] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> simp [inPlaceFlags]
  · exact cx_flags_physical [(streamLayout.infinitySelect, streamLayout.doubleSelect),
      (streamLayout.genericSelect, streamLayout.doubleSelect), (streamLayout.core.equalNegY, streamLayout.doubleSelect)]
      (by simp [d.1, d.2.1, d.2.2.1])
  · intro q hq; simp [scrW2, ECDSAAdd.wires, ECDSAAdd.Instr.wires] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> simp [inPlaceFlags]
  · exact cx_flags_physical [(streamLayout.core.equalNegY, streamLayout.doubleSelect),
      (streamLayout.genericSelect, streamLayout.doubleSelect), (streamLayout.infinitySelect, streamLayout.doubleSelect)]
      (by simp [d.1, d.2.1, d.2.2.1])

theorem padE_facts :
    ECDSAAdd.wires (Arith.padding (streamLayout.core.poolWire 0) 48842) ⊆ streamLayout.dialogUsedWires.toFinset ∧
      GatePhysical (Arith.padding (streamLayout.core.poolWire 0) 48842) ∧
      ECDSAAdd.wires (Arith.padding (streamLayout.core.poolWire 0) 48842) ⊆ sourceSupport.toFinset := by
  have hq (q : Wire) (h : q ∈ ECDSAAdd.wires (Arith.padding (streamLayout.core.poolWire 0) 48842)) :
      q = streamLayout.core.poolWire 0 := by
    simpa only [Finset.mem_singleton] using Arith.padding_support _ _ h
  have hpool : streamLayout.core.poolWire 0 ∈ streamLayout.dialogPool :=
    ECDSAAdd.Frontier.Square5Placement.pool_member streamLayout streamLayout_widths 0 (by decide)
  refine ⟨?_, Arith.padding_physical _ _, ?_⟩
  · intro q h
    rw [hq q h]
    exact List.mem_toFinset.mpr (List.mem_append_right _ hpool)
  · intro q h
    rw [hq q h]
    apply List.mem_toFinset.mpr
    apply (sourceSupport_mem _).mpr
    right; decide +kernel

theorem lit_facts_placed (p : ECDSAAdd.Program)
    (h : ECDSAAdd.wires p ⊆ streamLayout.dialogUsedWires.toFinset) :
    PlacedPair windowBits windowPaths windowRoot (WInstr.literal (n := 32768) p) := by
  intro w hw hq
  exact window_reserved_outside_used w hw (List.mem_toFinset.mp (h hq))

theorem wlit_counts (p : ECDSAAdd.Program) :
    literalToffolis (wLiteral (n := 32768) p) = ECDSAAdd.toffoliCount p ∧
    literalRecords (wLiteral (n := 32768) p) = ECDSAAdd.measurementCount p ∧
    traversals (wLiteral (n := 32768) p) = 0 ∧
    literalSlotSum (wLiteral (n := 32768) p) = ECDSAAdd.Challenge.gateSlots p ∧
    portTotal (wLiteral (n := 32768) p) = 0 ∧
    literalToffolis (normalizeW (wLiteral (n := 32768) p)) =
      ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram p) := by
  refine ⟨?_, ?_, rfl, ?_, rfl, ?_⟩ <;> simp [wLiteral, literalToffolis, literalRecords, literalSlotSum,
    normalizeW, normalizeWInstr]

theorem lookup_counts (c : Option Wire) (ports : List (LookupPort 32768)) :
    literalToffolis ([.lookup c ports] : WCode 32768) = 0 ∧
    literalRecords ([.lookup c ports] : WCode 32768) = 0 ∧
    traversals ([.lookup c ports] : WCode 32768) = 1 ∧
    literalSlotSum ([.lookup c ports] : WCode 32768) = 0 ∧
    portTotal ([.lookup c ports] : WCode 32768) = ports.length ∧
    literalToffolis (normalizeW ([.lookup c ports] : WCode 32768)) = 0 := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, rfl⟩
  simp [portTotal]

theorem norm_zero (p : ECDSAAdd.Program) (h : ECDSAAdd.toffoliCount p = 0) :
    ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram p) = 0 :=
  Nat.le_zero.mp (h ▸ ECDSAAdd.Baselines.normalize_toffoli p)

theorem cornersE_counts (rows : Nat → Fin 32768) :
    literalToffolis (scrECorners rows) = literalToffolis (scrDCorners rows) + 1022 ∧
    literalRecords (scrECorners rows) = literalRecords (scrDCorners rows) + 1022 ∧
    traversals (scrECorners rows) + 1 = traversals (scrDCorners rows) ∧
    literalSlotSum (scrECorners rows) + 4 =
      literalSlotSum (scrDCorners rows) + ECDSAAdd.Challenge.gateSlots scrNegP + 8 ∧
    portTotal (scrECorners rows) + 513 = portTotal (scrDCorners rows) ∧
    literalToffolis (normalizeW (scrECorners rows)) ≤ literalToffolis (normalizeW (scrDCorners rows)) + 1022 := by
  have hn := negH_counts streamLayout streamLayout_widths
  change ECDSAAdd.toffoliCount scrNegP = 1022 ∧ ECDSAAdd.measurementCount scrNegP = 1022 at hn
  have hx : streamLayout.point.x.length = 256 := streamLayout_widths.inputX
  have hy : streamLayout.point.y.length = 256 := streamLayout_widths.inputY
  have hcl : (scrCPorts rows).length = 513 := by simp [scrCPorts, hx, hy]
  have hnl : (scrNPorts rows).length = 513 := by simp [scrNPorts, hx, hy]
  have hdw : scrDWires.length = 513 := by simp [scrDWires, scrShortWires_length, scrDExtraWires_length]
  have hdt : scrDTargets.length = 513 := by simp [scrDTargets, hx, hy]
  have hcc : ECDSAAdd.toffoliCount (ccxList streamLayout.core.equalNegY scrDWires scrDTargets) = 513 := by
    rw [ccxList_toffoli, hdw, hdt]; rfl
  have hcs : ECDSAAdd.Challenge.gateSlots (ccxList streamLayout.core.equalNegY scrDWires scrDTargets) = 513 := by
    rw [ccxList_slots, hdw, hdt]; rfl
  have hcr := ccxList_records streamLayout.core.equalNegY scrDWires scrDTargets
  have nP := ECDSAAdd.Baselines.normalize_toffoli scrNegP
  have nC := ECDSAAdd.Baselines.normalize_toffoli (ccxList streamLayout.core.equalNegY scrDWires scrDTargets)
  have tE : ECDSAAdd.toffoliCount scrNegE = 0 := rfl
  have tS1 : ECDSAAdd.toffoliCount scrSw1 = 0 := rfl
  have tS2 : ECDSAAdd.toffoliCount scrSw2 = 0 := rfl
  have tS3 : ECDSAAdd.toffoliCount scrSw3 = 0 := rfl
  have tW1 : ECDSAAdd.toffoliCount scrW1 = 0 := rfl
  have tW2 : ECDSAAdd.toffoliCount scrW2 = 0 := rfl
  have mE : ECDSAAdd.measurementCount scrNegE = 0 := rfl
  have mS1 : ECDSAAdd.measurementCount scrSw1 = 0 := rfl
  have mS2 : ECDSAAdd.measurementCount scrSw2 = 0 := rfl
  have mS3 : ECDSAAdd.measurementCount scrSw3 = 0 := rfl
  have mW1 : ECDSAAdd.measurementCount scrW1 = 0 := rfl
  have mW2 : ECDSAAdd.measurementCount scrW2 = 0 := rfl
  have gE : ECDSAAdd.Challenge.gateSlots scrNegE = 1 := rfl
  have gS1 : ECDSAAdd.Challenge.gateSlots scrSw1 = 1 := rfl
  have gS2 : ECDSAAdd.Challenge.gateSlots scrSw2 = 1 := rfl
  have gS3 : ECDSAAdd.Challenge.gateSlots scrSw3 = 1 := rfl
  have gW1 : ECDSAAdd.Challenge.gateSlots scrW1 = 3 := rfl
  have gW2 : ECDSAAdd.Challenge.gateSlots scrW2 = 3 := rfl
  have cc := wlit_counts (ccxList streamLayout.core.equalNegY scrDWires scrDTargets)
  rw [cornersE_split, cornersD_split]
  simp only [literalToffolis_append, literalRecords_append, traversals_append, literalSlotSum_append',
    portTotal_append', portLit_append, (wlit_counts _).1, (wlit_counts _).2.1, (wlit_counts _).2.2.1,
    (wlit_counts _).2.2.2.1, (wlit_counts _).2.2.2.2.1, (wlit_counts _).2.2.2.2.2,
    (lookup_counts _ _).1, (lookup_counts _ _).2.1, (lookup_counts _ _).2.2.1, (lookup_counts _ _).2.2.2.1,
    (lookup_counts _ _).2.2.2.2.1, (lookup_counts _ _).2.2.2.2.2, sfxCC,
    norm_zero _ tE, norm_zero _ tS1, norm_zero _ tS2, norm_zero _ tS3, norm_zero _ tW1, norm_zero _ tW2,
    tE, tS1, tS2, tS3, tW1, tW2, mE, mS1, mS2, mS3, mW1, mW2, gE, gS1, gS2, gS3, gW1, gW2,
    hn.1, hn.2, hcc, hcs, hcr, hcl, hnl]
  exact ⟨True.intro, True.intro, True.intro, by omega, True.intro, by omega⟩

theorem pad_counts_E :
    literalToffolis sfxPadE = 0 ∧ literalRecords sfxPadE = 48842 ∧ traversals sfxPadE = 0 ∧
    literalSlotSum sfxPadE = 48842 ∧ portTotal sfxPadE = 0 ∧ literalToffolis (normalizeW sfxPadE) = 0 := by
  have w := wlit_counts (Arith.padding (streamLayout.core.poolWire 0) 48842)
  have pc := Arith.padding_counts (streamLayout.core.poolWire 0) 48842
  have ps := Arith.padding_slots (streamLayout.core.poolWire 0) 48842
  unfold sfxPadE
  rw [w.1, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2.1, w.2.2.2.2.2, pc.1, pc.2, ps, norm_zero _ pc.1]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem pad_counts_D :
    literalToffolis sfxPadD = 0 ∧ literalRecords sfxPadD = 49864 ∧ traversals sfxPadD = 0 ∧
    literalSlotSum sfxPadD = 49864 ∧ portTotal sfxPadD = 0 ∧ literalToffolis (normalizeW sfxPadD) = 0 := by
  have w := wlit_counts (Arith.padding (streamLayout.core.poolWire 0) 49864)
  have pc := Arith.padding_counts (streamLayout.core.poolWire 0) 49864
  have ps := Arith.padding_slots (streamLayout.core.poolWire 0) 49864
  unfold sfxPadD
  rw [w.1, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2.1, w.2.2.2.2.2, pc.1, pc.2, ps, norm_zero _ pc.1]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

attribute [local irreducible] sfxPadE sfxPadD

theorem suffixE_counts (rows : Nat → Fin 32768) :
    literalToffolis (portSuffixCodeE rows) = literalToffolis (portSuffixCodeD rows) + 1022 ∧
    literalRecords (portSuffixCodeE rows) = literalRecords (portSuffixCodeD rows) ∧
    traversals (portSuffixCodeE rows) + 1 = traversals (portSuffixCodeD rows) ∧
    literalSlotSum (portSuffixCodeE rows) + 1026 =
      literalSlotSum (portSuffixCodeD rows) + ECDSAAdd.Challenge.gateSlots scrNegP + 8 ∧
    portTotal (portSuffixCodeE rows) + 513 = portTotal (portSuffixCodeD rows) ∧
    literalToffolis (normalizeW (portSuffixCodeE rows)) ≤ literalToffolis (normalizeW (portSuffixCodeD rows)) + 1022 := by
  have c := cornersE_counts rows
  have e := pad_counts_E
  have d := pad_counts_D
  have hs := suffixE_split rows
  rw [hs.1, hs.2]
  simp only [literalToffolis_append, literalRecords_append, traversals_append, literalSlotSum_append',
    portTotal_append', portLit_append, e.1, e.2.1, e.2.2.1, e.2.2.2.1, e.2.2.2.2.1, e.2.2.2.2.2,
    d.1, d.2.1, d.2.2.1, d.2.2.2.1, d.2.2.2.2.1, d.2.2.2.2.2]
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem portRowE_shape (rows : Nat → Fin 32768) :
    let H : WCode 32768 := portPrefixCode rows ++ wGeneric streamLayout rows
    let X : WCode 32768 := wLiteral ([.X 838])
    portRowCodeE rows = X ++ (H ++ portSuffixCodeE rows) ++ X ∧
    portRowCode3 rows = X ++ (H ++ portSuffixCodeD rows) ++ X := by
  dsimp only
  constructor
  · simp only [portRowCodeE, portFiniteE]
  · simp only [portRowCode3, portFinite3]

theorem portRowE_member (rows : Nat → Fin 32768) (i : WInstr 32768) (hi : i ∈ portRowCodeE rows) :
    i = WInstr.literal scrNegE ∨ i = WInstr.literal scrW1 ∨ i = WInstr.literal scrW2 ∨
    i = WInstr.literal (Arith.padding (streamLayout.core.poolWire 0) 48842) ∨ i ∈ portRowCode3 rows := by
  have hs := portRowE_shape rows
  dsimp only at hs
  rw [hs.1] at hi
  rw [hs.2]
  simp only [List.mem_append] at hi ⊢
  rcases hi with (hi | (hi | hi)) | hi
  · tauto
  · tauto
  · rcases suffixE_member rows i hi with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · tauto
  · tauto

theorem portRowE_measures (rows : Nat → Fin 32768) :
    literalToffolis (portRowCodeE rows) = literalToffolis (portRowCode3 rows) + 1022 ∧
    literalRecords (portRowCodeE rows) = literalRecords (portRowCode3 rows) ∧
    traversals (portRowCodeE rows) + 1 = traversals (portRowCode3 rows) ∧
    literalSlotSum (portRowCodeE rows) + 1026 =
      literalSlotSum (portRowCode3 rows) + ECDSAAdd.Challenge.gateSlots scrNegP + 8 ∧
    portTotal (portRowCodeE rows) + 513 = portTotal (portRowCode3 rows) ∧
    literalToffolis (normalizeW (portRowCodeE rows)) ≤ literalToffolis (normalizeW (portRowCode3 rows)) + 1022 := by
  have hs := portRowE_shape rows
  dsimp only at hs
  rw [hs.1, hs.2]
  have c := suffixE_counts rows
  simp only [literalToffolis_append, literalRecords_append, traversals_append, literalSlotSum_append',
    portTotal_append', portLit_append]
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem portRowE_placed (rows : Nat → Fin 32768) :
    ∀ i ∈ portRowCodeE rows, PlacedPair windowBits windowPaths windowRoot i := by
  intro i hi
  have f := newLiteral_facts
  rcases portRowE_member rows i hi with rfl | rfl | rfl | rfl | h
  · exact lit_facts_placed _ f.1.1
  · exact lit_facts_placed _ f.2.1.1
  · exact lit_facts_placed _ f.2.2.1
  · exact lit_facts_placed _ padE_facts.1
  · exact portRow3_placed rows i h

theorem portRowE_physical (rows : Nat → Fin 32768) :
    ∀ p, WInstr.literal p ∈ portRowCodeE rows → GatePhysical p := by
  intro p hp
  have f := newLiteral_facts
  rcases portRowE_member rows _ hp with he | he | he | he | h
  · cases he; exact f.1.2.1
  · cases he; exact f.2.1.2.1
  · cases he; exact f.2.2.2.1
  · cases he; exact padE_facts.2.1
  · exact portRow3_physical rows p h

theorem portRowE_literal_source (p : ECDSAAdd.Program) (hp : WInstr.literal p ∈ portRowCodeE probeRows) :
    ECDSAAdd.wires p ⊆ sourceSupport.toFinset := by
  have f := newLiteral_facts
  rcases portRowE_member probeRows _ hp with he | he | he | he | h
  · cases he; exact f.1.2.2
  · cases he; exact f.2.1.2.2
  · cases he; exact f.2.2.2.2
  · cases he; exact padE_facts.2.2
  · exact portRow3_literal_source p h

theorem portE_nat_sub (a b : Nat) (h : a + 1 = b) (hb : b = 16) : a = 15 := by omega

theorem portRowE_traversals' (rows : Nat → Fin 32768) : traversals (portRowCodeE rows) = 15 :=
  portE_nat_sub _ _ (portRowE_measures rows).2.2.1 (portRow3_traversals' rows)

theorem portRowE_traversals : traversals (normalizeW (portRowCodeE probeRows)) = 15 := by
  rw [traversals_normalize]
  exact portRowE_traversals' probeRows

theorem portRowE_literalRecords (rows : Nat → Fin 32768) : literalRecords (portRowCodeE rows) = 1556899 :=
  (portRowE_measures rows).2.1.trans (portRow3_literalRecords rows)

theorem portE_records_arith (a b k : Nat) (ha : a = 1556899) (hb : b = 15) (l : Nat) (hl : l = k) :
    a + b * (2 ^ l - 1) = 1556899 + 15 * (2 ^ k - 1) := by
  subst ha hb hl
  rfl

theorem portE_records15 (a b l : Nat) (ha : a = 1556899) (hb : b = 15) (hl : l = 15) :
    a + b * (2 ^ l - 1) = 2048404 := by
  subst ha hb hl
  rfl

theorem portRowE_records : codeRecords windowBits windowPaths windowRoot
    (normalizeW (portRowCodeE probeRows)) = 2048404 := by
  have layouts := pair_layouts_of_placed windowBits windowPaths windowRoot _
    (by simp [windowBits,windowPaths]) (pair_placed_normalize _ _ _ _ (portRowE_placed probeRows))
  rw [codeRecords_eq _ _ _ _ layouts,literalRecords_normalize,traversals_normalize]
  exact portE_records15 _ _ _ (portRowE_literalRecords _) (portRowE_traversals' _) (by simp [windowBits])

theorem portRowE_sourceLookupOK : (normalizeW (portRowCodeE probeRows)).all sourceLookupOK = true := by
  apply List.all_eq_true.mpr
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  cases i with
  | literal p => rfl
  | lookup c ports =>
    rcases portRowE_member probeRows _ hi with he | he | he | he | h
    · cases he
    · cases he
    · cases he
    · cases he
    · exact List.all_eq_true.mp portRow3_sourceLookupOK _ (List.mem_map.mpr ⟨_, h, rfl⟩)

theorem portRowE_literal_slots_bound : literalSlotSum (portRowCodeE probeRows) ≤ 50021565 := by
  have h := (portRowE_measures probeRows).2.2.2.1
  have h3 := portRow3_literal_slots_bound
  have hn := negate_slots_bound streamLayout.core.equalNegY
  change ECDSAAdd.Challenge.gateSlots scrNegP ≤ 20000 at hn
  omega

theorem portRowE_portTotal : portTotal (portRowCodeE probeRows) ≤ 20000 := by
  have h := (portRowE_measures probeRows).2.2.2.2.1
  have h3 := portRow3_portTotal
  omega

theorem portE_nat_count (a b b' t : Nat) (h : a + b + 16 * t ≤ 2164414 + 16 * t) (hb : b' ≤ b + 1022) :
    a + b' + 15 * t ≤ 2165436 + 15 * t := by omega

theorem portRowE_count_upper (k : Nat) :
    2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram windowSignProgram) +
      literalToffolis (normalizeW (portRowCodeE probeRows)) + 15 * (2^k-1) ≤
      2165436 + 15 * (2^k-1) :=
  portE_nat_count _ _ _ _ (portRow3_count_upper k) (portRowE_measures probeRows).2.2.2.2.2

theorem portRowE_width_placed (k : Nat) (hk : k ≤ 15) (rows : Nat → Fin 32768) :
    ∀ i ∈ portRowCodeE rows, PlacedPair (widthBits k) windowPaths windowRoot i := by
  intro i hi
  have hp := portRowE_placed rows i hi
  cases i with
  | literal p =>
    intro w hw
    exact hp w ((List.Sublist.cons₂ windowRoot (width_sublist k hk)).subset hw)
  | lookup c ports =>
    refine ⟨(List.Sublist.cons₂ _ (width_sublist k hk)).nodup hp.1, hp.2.1, hp.2.2.1, ?_⟩
    apply List.disjoint_left.mpr
    intro w hw ht
    exact List.disjoint_left.mp hp.2.2.2
      ((List.Sublist.cons₂ _ (List.Sublist.cons₂ _ (width_sublist k hk))).subset hw) ht

theorem portRowE_width_records (k : Nat) (hk : k ≤ 15) :
    codeRecords (widthBits k) windowPaths windowRoot (normalizeW (portRowCodeE probeRows)) =
      1556899 + 15 * (2 ^ k - 1) := by
  have layouts := pair_layouts_of_placed (widthBits k) windowPaths windowRoot _
    (by simpa [widthBits,windowPaths] using hk) (pair_placed_normalize _ _ _ _ (portRowE_width_placed k hk probeRows))
  rw [codeRecords_eq _ _ _ _ layouts,literalRecords_normalize,traversals_normalize]
  exact portE_records_arith _ _ _ (portRowE_literalRecords _) (portRowE_traversals' _) _ (by simp [widthBits])


/-! ### The merged corners on top of the measured-clear entry prefix -/

def portFinite5 (rows : Nat → Fin 32768) : WCode 32768 :=
  portPrefixCode4 rows ++ wGeneric streamLayout rows ++ portSuffixCodeE rows

def portRowCode5 (rows : Nat → Fin 32768) : WCode 32768 :=
  wLiteral ([.X 838]) ++ portFinite5 rows ++ wLiteral ([.X 838])

theorem portRow5_run_eq (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (address : Nat)
    (s : BasisState) (hr : s windowRoot = true) (m : List Bool) :
    ECDSAAdd.run ((specialize (portRowCode5 rows) address).instantiate read) m ⟨false,s⟩ =
      ECDSAAdd.run ((specialize (portRowCodeE rows) address).instantiate read) m ⟨false,s⟩ := by
  let P' := (specialize (portPrefixCode4 rows) address).instantiate read
  let P := (specialize (portPrefixCode rows) address).instantiate read
  let R := (specialize (wGeneric streamLayout rows) address).instantiate read ++
    (specialize (portSuffixCodeE rows) address).instantiate read ++ ([.X 838] : ECDSAAdd.Program)
  have e1 : (specialize (portRowCode5 rows) address).instantiate read = ([.X 838] : ECDSAAdd.Program) ++ P' ++ R := by
    simp only [portRowCode5, portFinite5, specialize_append, specialize_literal, Tmpl.instantiate_append,
      Tmpl.instantiate_lit, P', R, List.append_assoc]
  have e2 : (specialize (portRowCodeE rows) address).instantiate read = ([.X 838] : ECDSAAdd.Program) ++ P ++ R := by
    simp only [portRowCodeE, portFiniteE, specialize_append, specialize_literal, Tmpl.instantiate_append,
      Tmpl.instantiate_lit, P, R, List.append_assoc]
  rw [e1, e2]
  apply portSuffix_middle _ _ _ _ (portPrefix4_records read rows address) ⟨false,s⟩
  intro k n
  rw [flip_run]
  apply portPrefix4_eq3 read rows address n
  change flipInfinity s windowRoot = true
  simpa [flipInfinity, ECDSAAdd.writeBit, Function.update, windowRoot] using hr

/-- Any record-independent result of the promoted row transfers to the merged-corner row. -/
theorem portRow5_transport (a : Nat) (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (s : BasisState) (hs : liveReady s) (t : ECDSAAdd.State)
    (href : ∀ m, ECDSAAdd.run ((specialize (normalizeW (portRowCode4 probeRows)) a).instantiate
      (readConstant coeffs Q)) m ⟨false,s⟩ = t) (m : List Bool) :
    ECDSAAdd.run ((specialize (normalizeW (portRowCode5 probeRows)) a).instantiate (readConstant coeffs Q)) m ⟨false,s⟩ = t := by
  rw [specialize_normalize_run, portRow5_run_eq _ _ _ s hs.2.2 m, ← specialize_normalize_run]
  apply portRowE_transport a coeffs Q hQ hn s hs t _ m
  intro m'
  rw [specialize_normalize_run, ← portRow4_run_eq _ _ _ s hs.2.2 m', ← specialize_normalize_run]
  exact href m'

theorem portRow5_shape (rows : Nat → Fin 32768) :
    let H : WCode 32768 := portPrefixCode4 rows ++ wGeneric streamLayout rows
    let X : WCode 32768 := wLiteral ([.X 838])
    portRowCode5 rows = X ++ (H ++ portSuffixCodeE rows) ++ X ∧
    portRowCode4 rows = X ++ (H ++ portSuffixCodeD rows) ++ X := by
  dsimp only
  constructor
  · simp only [portRowCode5, portFinite5]
  · simp only [portRowCode4, portFinite4]

theorem portRow5_member (rows : Nat → Fin 32768) (i : WInstr 32768) (hi : i ∈ portRowCode5 rows) :
    i = WInstr.literal scrNegE ∨ i = WInstr.literal scrW1 ∨ i = WInstr.literal scrW2 ∨
    i = WInstr.literal (Arith.padding (streamLayout.core.poolWire 0) 48842) ∨ i ∈ portRowCode4 rows := by
  have hs := portRow5_shape rows
  dsimp only at hs
  rw [hs.1] at hi
  rw [hs.2]
  simp only [List.mem_append] at hi ⊢
  rcases hi with (hi | (hi | hi)) | hi
  · tauto
  · tauto
  · rcases suffixE_member rows i hi with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · tauto
  · tauto

theorem portRow5_measures (rows : Nat → Fin 32768) :
    literalToffolis (portRowCode5 rows) = literalToffolis (portRowCode4 rows) + 1022 ∧
    literalRecords (portRowCode5 rows) = literalRecords (portRowCode4 rows) ∧
    traversals (portRowCode5 rows) + 1 = traversals (portRowCode4 rows) ∧
    literalSlotSum (portRowCode5 rows) + 1026 =
      literalSlotSum (portRowCode4 rows) + ECDSAAdd.Challenge.gateSlots scrNegP + 8 ∧
    portTotal (portRowCode5 rows) + 513 = portTotal (portRowCode4 rows) ∧
    literalToffolis (normalizeW (portRowCode5 rows)) ≤ literalToffolis (normalizeW (portRowCode4 rows)) + 1022 := by
  have hs := portRow5_shape rows
  dsimp only at hs
  rw [hs.1, hs.2]
  have c := suffixE_counts rows
  simp only [literalToffolis_append, literalRecords_append, traversals_append, literalSlotSum_append',
    portTotal_append', portLit_append]
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem portRow5_placed :
    ∀ i ∈ portRowCode5 probeRows, PlacedPair windowBits windowPaths windowRoot i := by
  intro i hi
  have f := newLiteral_facts
  rcases portRow5_member probeRows i hi with rfl | rfl | rfl | rfl | h
  · exact lit_facts_placed _ f.1.1
  · exact lit_facts_placed _ f.2.1.1
  · exact lit_facts_placed _ f.2.2.1
  · exact lit_facts_placed _ padE_facts.1
  · exact portRow4_placed probeRows i h

theorem portRow5_physical : ∀ p, WInstr.literal p ∈ portRowCode5 probeRows → GatePhysical p := by
  intro p hp
  have f := newLiteral_facts
  rcases portRow5_member probeRows _ hp with he | he | he | he | h
  · cases he; exact f.1.2.1
  · cases he; exact f.2.1.2.1
  · cases he; exact f.2.2.2.1
  · cases he; exact padE_facts.2.1
  · exact portRow4_physical p h

theorem portRow5_literal_source (p : ECDSAAdd.Program) (hp : WInstr.literal p ∈ portRowCode5 probeRows) :
    ECDSAAdd.wires p ⊆ sourceSupport.toFinset := by
  have f := newLiteral_facts
  rcases portRow5_member probeRows _ hp with he | he | he | he | h
  · cases he; exact f.1.2.2
  · cases he; exact f.2.1.2.2
  · cases he; exact f.2.2.2.2
  · cases he; exact padE_facts.2.2
  · exact portRow4_literal_source p h

theorem portRow5_traversals' : traversals (portRowCode5 probeRows) = 15 :=
  portE_nat_sub _ _ (portRow5_measures probeRows).2.2.1 portRow4_traversals'

theorem portRow5_traversals : traversals (normalizeW (portRowCode5 probeRows)) = 15 := by
  rw [traversals_normalize]
  exact portRow5_traversals'

theorem portRow5_literalRecords : literalRecords (portRowCode5 probeRows) = 1556899 :=
  (portRow5_measures probeRows).2.1.trans portRow4_literalRecords

theorem portRow5_records : codeRecords windowBits windowPaths windowRoot
    (normalizeW (portRowCode5 probeRows)) = 2048404 := by
  have layouts := pair_layouts_of_placed windowBits windowPaths windowRoot _
    (by simp [windowBits,windowPaths]) (pair_placed_normalize _ _ _ _ portRow5_placed)
  rw [codeRecords_eq _ _ _ _ layouts,literalRecords_normalize,traversals_normalize]
  exact portE_records15 _ _ _ portRow5_literalRecords portRow5_traversals' (by simp [windowBits])

theorem portRow5_sourceLookupOK : (normalizeW (portRowCode5 probeRows)).all sourceLookupOK = true := by
  apply List.all_eq_true.mpr
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  cases i with
  | literal p => rfl
  | lookup c ports =>
    rcases portRow5_member probeRows _ hi with he | he | he | he | h
    · cases he
    · cases he
    · cases he
    · cases he
    · exact List.all_eq_true.mp portRow4_sourceLookupOK _ (List.mem_map.mpr ⟨_, h, rfl⟩)

theorem portRow5_literal_slots_bound : literalSlotSum (portRowCode5 probeRows) ≤ 50021565 := by
  have h := (portRow5_measures probeRows).2.2.2.1
  have h4 := portRow4_literal_slots_bound
  have hn := negate_slots_bound streamLayout.core.equalNegY
  change ECDSAAdd.Challenge.gateSlots scrNegP ≤ 20000 at hn
  omega

theorem portRow5_portTotal : portTotal (portRowCode5 probeRows) ≤ 20000 := by
  have h := (portRow5_measures probeRows).2.2.2.2.1
  have h4 := portRow4_portTotal
  omega

theorem portRow5_count_upper (k : Nat) :
    2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram windowSignProgram) +
      literalToffolis (normalizeW (portRowCode5 probeRows)) + 15 * (2^k-1) ≤
      2165436 + 15 * (2^k-1) :=
  portE_nat_count _ _ _ _ (portRow4_count_upper k) (portRow5_measures probeRows).2.2.2.2.2

theorem portRow5_width_placed (k : Nat) (hk : k ≤ 15) :
    ∀ i ∈ portRowCode5 probeRows, PlacedPair (widthBits k) windowPaths windowRoot i := by
  intro i hi
  have hp := portRow5_placed i hi
  cases i with
  | literal p =>
    intro w hw
    exact hp w ((List.Sublist.cons₂ windowRoot (width_sublist k hk)).subset hw)
  | lookup c ports =>
    refine ⟨(List.Sublist.cons₂ _ (width_sublist k hk)).nodup hp.1, hp.2.1, hp.2.2.1, ?_⟩
    apply List.disjoint_left.mpr
    intro w hw ht
    exact List.disjoint_left.mp hp.2.2.2
      ((List.Sublist.cons₂ _ (List.Sublist.cons₂ _ (width_sublist k hk))).subset hw) ht

theorem portRow5_width_records (k : Nat) (hk : k ≤ 15) :
    codeRecords (widthBits k) windowPaths windowRoot (normalizeW (portRowCode5 probeRows)) =
      1556899 + 15 * (2 ^ k - 1) := by
  have layouts := pair_layouts_of_placed (widthBits k) windowPaths windowRoot _
    (by simpa [widthBits,windowPaths] using hk) (pair_placed_normalize _ _ _ _ (portRow5_width_placed k hk))
  rw [codeRecords_eq _ _ _ _ layouts,literalRecords_normalize,traversals_normalize]
  exact portE_records_arith _ _ _ portRow5_literalRecords portRow5_traversals' _ (by simp [widthBits])

end
end ShorECDLP.Entrant.WEX
