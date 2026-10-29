import ShorECDLP.Submission.Entrant.FastOracle
import ShorECDLP.Submission.Entrant.V2.Gates

/-! EDITABLE. Fixed template gates for `fastCPA`.

Every constant-dependent gate is an `X` gate enabled by one protected table bit.  The
doubling branch reads the protected `doubleInfinity/doubleX/doubleY` fields of its own
row; the backward pass uses a separate row holding the negated point. -/

namespace ShorECDLP.Secp256k1.V2
open Quantum Challenge Arithmetic NaiveChallenge

/-! ## Packed load of the doubled table point -/

def dpackedGate {n : Nat} (row : Fin n) (w : Wire) (i : Nat) : List (TemplateGate n) :=
  if i = 0 then [.whenBit ⟨row, .doubleInfinity, 0⟩ false (.X w)]
  else if h : i < 257 then [.whenBit ⟨row, .doubleX, ⟨i-1, by omega⟩⟩ true (.X w)]
  else if h : i < 513 then [.whenBit ⟨row, .doubleY, ⟨i-257, by omega⟩⟩ true (.X w)]
  else []

def dpackedLoadGates {n : Nat} (row : Fin n) : List Wire → Nat → List (TemplateGate n)
  | [], _ => []
  | w :: ws, i => dpackedGate row w i ++ dpackedLoadGates row ws (i+1)

theorem dpackedGate_source {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (w : Wire) (i : Nat) :
    (dpackedGate row w i).flatMap (TemplateGate.instantiate (readConstant coeffs Q)) =
      if (encode (constantPoint Q (coeffs row) + constantPoint Q (coeffs row))).val.testBit i
        = true then [.X w] else [] := by
  let P := constantPoint Q (coeffs row) + constantPoint Q (coeffs row)
  change (dpackedGate row w i).flatMap (TemplateGate.instantiate (readConstant coeffs Q)) =
      if (encode P).val.testBit i = true then [.X w] else []
  by_cases hz : i = 0
  · subst i
    simp only [dpackedGate, ↓reduceIte, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, TemplateGate.instantiate, readConstant]
    change (if (fieldValue P .infinity).testBit 0 = false then _ else _) = _
    cases hP : P with
    | zero => rfl
    | @some x y h =>
      have ht := finiteFlag_encode_some h
      change (encode (.some h)).val % 2 = 1 at ht
      change (if Nat.testBit 0 0 = false then _ else _) = _
      simp only [Nat.testBit_zero, ht]
      rfl
  · by_cases hx : i < 257
    · have he := packed_x_bit P ⟨i-1, by omega⟩
      have hi : i-1+1=i := by omega
      simp only [hi] at he
      simp only [dpackedGate, if_neg hz, dif_pos hx, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, TemplateGate.instantiate, readConstant]
      change (if (fieldValue P .x).testBit (i-1) = true then _ else _) = _
      rw [he]
    · by_cases hy : i < 513
      · have he := packed_y_bit P ⟨i-257, by omega⟩
        have hi : i-257+257=i := by omega
        simp only [hi] at he
        simp only [dpackedGate, if_neg hz, dif_neg hx, dif_pos hy, List.flatMap_cons,
          List.flatMap_nil, List.append_nil, TemplateGate.instantiate, readConstant]
        change (if (fieldValue P .y).testBit (i-257) = true then _ else _) = _
        rw [he]
      · have hb : (encode P).val.testBit i = false := Nat.testBit_eq_false_of_lt
          ((encode P).isLt.trans_le (Nat.pow_le_pow_right (by decide) (by
            change 513 ≤ i; omega)))
        simp only [dpackedGate, if_neg hz, dif_neg hx, dif_neg hy,
          List.flatMap_nil, hb, Bool.false_eq_true, if_false]

theorem dpackedLoadGates_source_aux {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (ws : List Wire) (i : Nat) :
    (dpackedLoadGates row ws i).flatMap (TemplateGate.instantiate (readConstant coeffs Q)) =
      loadConst ws ((encode (constantPoint Q (coeffs row) +
        constantPoint Q (coeffs row))).val / 2^i) := by
  induction ws generalizing i with
  | nil => rfl
  | cons w ws ih =>
    simp only [dpackedLoadGates, List.flatMap_append, dpackedGate_source, ih,
      Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq, loadConst,
      Nat.div_div_eq_div_mul, pow_succ]

theorem dpackedLoadGates_source {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (ws : List Wire) :
    (dpackedLoadGates row ws 0).flatMap (TemplateGate.instantiate (readConstant coeffs Q)) =
      loadConst ws (encode (constantPoint Q (coeffs row) + constantPoint Q (coeffs row))).val := by
  simpa only [pow_zero, Nat.div_one] using dpackedLoadGates_source_aux coeffs Q row ws 0

/-! ## Gates -/

def fastBlockGates {n : Nat} (control flag anc : Wire) (K : List (TemplateGate n))
    (cand outReg : List Wire) : List (TemplateGate n) :=
  [TemplateGate.literal (.CCX control flag anc)] ++ K ++
    (controlledCopyReg anc cand outReg).map TemplateGate.literal ++ K.reverse ++
    [TemplateGate.literal (.CCX control flag anc)]

def fastSetupGates {n : Nat} (row : Fin n) (pointReg : List Wire) (pw : Wire) :
    List (TemplateGate n) :=
  (pointAddCoordinateCopies pointReg pw).map TemplateGate.literal ++
    pointFlagGates row pointReg pw

def fastOutGates {n : Nat} (row : Fin n) (control : Wire) (pointReg outReg : List Wire)
    (workStart : Wire) : List (TemplateGate n) :=
  let pw := controlledPointAddPointWorkStart workStart
  let cand := pointAddCandidate pw
  (fastPass control pointReg outReg).map TemplateGate.literal ++
    fastSetupGates row pointReg pw ++
    (fastBlockGates control (pointAddGenericFlag pw) workStart
        (genericPointGates row pw ++
          (packFinitePoint (pointAddT2 pw) (pointAddT4 pw) cand).map TemplateGate.literal)
        cand outReg ++
      fastBlockGates control (pointAddDoubleFlag pw) workStart (dpackedLoadGates row cand 0)
        cand outReg ++
      fastBlockGates control (pointAddInfinityFlag pw) workStart (packedLoadGates row cand 0)
        cand outReg) ++
    (fastSetupGates row pointReg pw).reverse

theorem fastBlockGates_source {n : Nat} (read : ConstantBit n → Bool) (control flag anc : Wire)
    (K : List (TemplateGate n)) (cand outReg : List Wire) :
    (fastBlockGates control flag anc K cand outReg).flatMap (TemplateGate.instantiate read) =
      fastBlock control flag anc (K.flatMap (TemplateGate.instantiate read)) cand outReg := by
  simp only [fastBlockGates, fastBlock, List.flatMap_append, template_reverse,
    literalGates_instantiate]
  rfl

theorem fastOutGates_source {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (control : Wire) (pointReg outReg : List Wire) (workStart : Wire) :
    (fastOutGates row control pointReg outReg workStart).flatMap
      (TemplateGate.instantiate (readConstant coeffs Q)) =
      fastOut control pointReg outReg workStart (constantPoint Q (coeffs row)) := by
  simp only [fastOutGates, fastSetupGates, List.flatMap_append, template_reverse,
    literalGates_instantiate, fastBlockGates_source, pointFlagGates_source,
    genericPointGates_source, packedLoadGates_source, dpackedLoadGates_source]
  rfl

def fastCPAGates {n : Nat} (row negRow : Fin n) (control : Wire) (pointReg : List Wire)
    (workStart : Wire) : List (TemplateGate n) :=
  let temp := controlledPointAddTemp workStart
  let auxStart := controlledPointAddAuxStart workStart
  fastOutGates row control pointReg temp auxStart ++
    (pointSwapReg pointReg temp).map TemplateGate.literal ++
    (fastOutGates negRow control pointReg temp auxStart).reverse

theorem fastCPAGates_source {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row negRow : Fin n) (control : Wire) (pointReg : List Wire) (workStart : Wire)
    (hneg : constantPoint Q (coeffs negRow) = -constantPoint Q (coeffs row)) :
    (fastCPAGates row negRow control pointReg workStart).flatMap
      (TemplateGate.instantiate (readConstant coeffs Q)) =
      fastCPA control pointReg workStart (constantPoint Q (coeffs row)) := by
  simp only [fastCPAGates, List.flatMap_append, template_reverse, literalGates_instantiate,
    fastOutGates_source, hneg]
  rfl

def fastScalarGates {n : Nat} (pointReg : List Wire) (workStart : Wire) :
    List Wire → List (Fin n × Fin n) → List (TemplateGate n)
  | c :: cs, r :: rs => fastCPAGates r.1 r.2 c pointReg workStart ++
      fastScalarGates pointReg workStart cs rs
  | _, _ => []

theorem fastScalarGates_source {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (pointReg : List Wire) (workStart : Wire) :
    ∀ (controls : List Wire) (rows : List (Fin n × Fin n)),
      (∀ r ∈ rows, constantPoint Q (coeffs r.2) = -constantPoint Q (coeffs r.1)) →
      (fastScalarGates pointReg workStart controls rows).flatMap
        (TemplateGate.instantiate (readConstant coeffs Q)) =
      fastCore pointReg workStart controls (rows.map (fun r => constantPoint Q (coeffs r.1))) := by
  intro controls
  induction controls with
  | nil => intro rows _; cases rows <;> rfl
  | cons c cs ih =>
    intro rows hrows
    cases rows with
    | nil => rfl
    | cons r rs =>
      simp only [fastScalarGates, List.flatMap_append,
        fastCPAGates_source coeffs Q r.1 r.2 c pointReg workStart (hrows r List.mem_cons_self),
        ih rs (fun r' hr' => hrows r' (List.mem_cons_of_mem _ hr')), List.map_cons, fastCore]

/-! ## Constant slots are `X` gates -/

def XSlot {n : Nat} : TemplateGate n → Prop
  | .literal _ => True
  | .whenBit _ _ g => ∃ w, g = .X w

def XSlots {n : Nat} (gs : List (TemplateGate n)) : Prop := ∀ g ∈ gs, XSlot g

@[simp] theorem xSlots_append {n : Nat} (a b : List (TemplateGate n)) :
    XSlots (a ++ b) ↔ XSlots a ∧ XSlots b := by
  simp only [XSlots, List.mem_append, or_imp, forall_and]

@[simp] theorem xSlots_reverse {n : Nat} (a : List (TemplateGate n)) :
    XSlots a.reverse ↔ XSlots a := by simp only [XSlots, List.mem_reverse]

@[simp] theorem xSlots_literal {n : Nat} (c : Circuit) :
    XSlots (c.map (TemplateGate.literal (tableSize := n))) := by
  intro g hg
  obtain ⟨g, _, rfl⟩ := List.mem_map.mp hg
  trivial

@[simp] theorem xSlots_singleton {n : Nat} (g : Gate) :
    XSlots [TemplateGate.literal (tableSize := n) g] := by
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  trivial

@[simp] theorem xSlots_fieldLoad {n : Nat} (row : Fin n) (field : PointField)
    (ws : List Wire) (i : Nat) : XSlots (fieldLoadGates row field ws i) := by
  induction ws generalizing i with
  | nil => simp [XSlots, fieldLoadGates]
  | cons w ws ih =>
    simp only [fieldLoadGates, xSlots_append]
    refine ⟨?_, ih _⟩
    split
    · intro g hg; simp only [List.mem_singleton] at hg; subst hg; exact ⟨w, rfl⟩
    · simp [XSlots]

@[simp] theorem xSlots_packedLoad {n : Nat} (row : Fin n) (ws : List Wire) (i : Nat) :
    XSlots (packedLoadGates row ws i) := by
  induction ws generalizing i with
  | nil => simp [XSlots, packedLoadGates]
  | cons w ws ih =>
    simp only [packedLoadGates, xSlots_append]
    refine ⟨?_, ih _⟩
    unfold packedGate
    split
    · intro g hg; simp only [List.mem_singleton] at hg; subst hg; exact ⟨w, rfl⟩
    · split
      · intro g hg; simp only [List.mem_singleton] at hg; subst hg; exact ⟨w, rfl⟩
      · split
        · intro g hg; simp only [List.mem_singleton] at hg; subst hg; exact ⟨w, rfl⟩
        · simp [XSlots]

@[simp] theorem xSlots_dpackedLoad {n : Nat} (row : Fin n) (ws : List Wire) (i : Nat) :
    XSlots (dpackedLoadGates row ws i) := by
  induction ws generalizing i with
  | nil => simp [XSlots, dpackedLoadGates]
  | cons w ws ih =>
    simp only [dpackedLoadGates, xSlots_append]
    refine ⟨?_, ih _⟩
    unfold dpackedGate
    split
    · intro g hg; simp only [List.mem_singleton] at hg; subst hg; exact ⟨w, rfl⟩
    · split
      · intro g hg; simp only [List.mem_singleton] at hg; subst hg; exact ⟨w, rfl⟩
      · split
        · intro g hg; simp only [List.mem_singleton] at hg; subst hg; exact ⟨w, rfl⟩
        · simp [XSlots]

theorem xSlots_fastCPAGates {n : Nat} (row negRow : Fin n) (control : Wire)
    (pointReg : List Wire) (workStart : Wire) :
    XSlots (fastCPAGates row negRow control pointReg workStart) := by
  simp only [fastCPAGates, fastOutGates, fastSetupGates, fastBlockGates, pointFlagGates,
    genericPointGates, fieldSubConstGates, xSlots_append, xSlots_reverse, xSlots_literal,
    xSlots_singleton, xSlots_fieldLoad, xSlots_packedLoad, xSlots_dpackedLoad, and_self]

theorem xSlots_templateT {n : Nat} (gs : List (TemplateGate n)) (h : XSlots gs)
    (read : ConstantBit n → Bool) :
    templateT gs = tCount (gs.flatMap (TemplateGate.instantiate read)) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have hg := h g List.mem_cons_self
    have ht := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    rw [List.flatMap_cons, tCount_append, ← ht]
    simp only [templateT, List.map_cons, List.sum_cons]
    congr 1
    cases g with
    | literal g => simp [TemplateGate.instantiate, slotGate, tCount]
    | whenBit r b g =>
      obtain ⟨w, rfl⟩ := hg
      simp only [TemplateGate.instantiate, slotGate]
      split <;> simp [tCount, tCost]

theorem xSlots_wellFormed {n : Nat} (gs : List (TemplateGate n)) (h : XSlots gs)
    (read : ConstantBit n → Bool)
    (hw : CircuitWellFormed (gs.flatMap (TemplateGate.instantiate read))) :
    ∀ g ∈ gs, g.WellFormed := by
  intro g hg
  have hx := h g hg
  cases g with
  | literal g => exact hw g (List.mem_flatMap.mpr ⟨_, hg, by simp [TemplateGate.instantiate]⟩)
  | whenBit r b g =>
    obtain ⟨w, rfl⟩ := hx
    trivial

/-! ## Resources of the template gates -/

theorem fastCPAGates_instantiate {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row negRow : Fin n) (control : Wire) (pointReg : List Wire) (workStart : Wire) :
    (fastCPAGates row negRow control pointReg workStart).flatMap
      (TemplateGate.instantiate (readConstant coeffs Q)) =
      fastOut control pointReg (controlledPointAddTemp workStart)
          (controlledPointAddAuxStart workStart) (constantPoint Q (coeffs row)) ++
        pointSwapReg pointReg (controlledPointAddTemp workStart) ++
        (fastOut control pointReg (controlledPointAddTemp workStart)
          (controlledPointAddAuxStart workStart) (constantPoint Q (coeffs negRow))).reverse := by
  simp only [fastCPAGates, List.flatMap_append, template_reverse, literalGates_instantiate,
    fastOutGates_source]

theorem fastCPAGates_templateT {n : Nat} (row negRow : Fin n) (control : Wire)
    (pointReg : List Wire) (workStart : Wire) (hP : pointReg.length = pointWidth) :
    templateT (fastCPAGates row negRow control pointReg workStart) = 22257271064 := by
  rw [xSlots_templateT _ (xSlots_fastCPAGates row negRow control pointReg workStart)
    (readConstant (fun _ : Fin n => qCoefficient) G), fastCPAGates_instantiate]
  exact fastCPA2_tCount control pointReg workStart _ _ hP

theorem fastCPAGates_wellFormed {n : Nat} (row negRow : Fin n) (control : Wire)
    (pointReg : List Wire) (workStart : Wire)
    (hn : ([control] ++ pointReg ++ controlledPointAddWork workStart).Nodup) :
    ∀ g ∈ fastCPAGates row negRow control pointReg workStart, g.WellFormed := by
  apply xSlots_wellFormed _ (xSlots_fastCPAGates row negRow control pointReg workStart)
    (readConstant (fun _ : Fin n => qCoefficient) G)
  rw [fastCPAGates_instantiate]
  let temp := controlledPointAddTemp workStart
  let auxStart := controlledPointAddAuxStart workStart
  let work := controlledPointAddOutWork auxStart
  have houtNodup : ([control] ++ pointReg ++ temp ++ work).Nodup := by
    simpa [temp, auxStart, work, controlledPointAddWork, controlledPointAddTemp,
      controlledPointAddAuxStart, List.append_assoc] using hn
  have h0 : (control :: (pointReg ++ temp ++ work)).Nodup := by
    simpa [List.append_assoc] using houtNodup
  have hswapNodup : (pointReg ++ temp).Nodup :=
    (List.nodup_append.mp (List.nodup_cons.mp h0).2).1
  rw [circuitWellFormed_append, circuitWellFormed_append]
  exact ⟨⟨(fastOut_structural _ _ _ _ _ houtNodup).1,
    pointSwapReg_wellFormed _ _ hswapNodup⟩,
    Arithmetic.wellFormed_reverse (fastOut_structural _ _ _ _ _ houtNodup).1⟩

theorem dpackedLoadGates_length_le {n : Nat} (row : Fin n) (ws : List Wire) (i : Nat) :
    (dpackedLoadGates row ws i).length ≤ ws.length := by
  induction ws generalizing i with
  | nil => rfl
  | cons w ws ih =>
    have h : (dpackedGate row w i).length ≤ 1 := by
      unfold dpackedGate
      split <;> (try split) <;> (try split) <;> simp
    simp only [dpackedLoadGates, List.length_append, List.length_cons]
    have := ih (i+1)
    omega

theorem fastOutGates_length_le {n : Nat} (row : Fin n) (control : Wire)
    (pointReg outReg : List Wire) (workStart : Wire) (hP : pointReg.length = pointWidth) :
    (fastOutGates row control pointReg outReg workStart).length ≤ 34000100000 := by
  have h1 := controlledCopyReg_length_le control pointReg outReg
  have h2 := pointAddCoordinateCopies_length_le pointReg
    (controlledPointAddPointWorkStart workStart)
  have h3 := pointFlagGates_length_le row pointReg (controlledPointAddPointWorkStart workStart)
  have h4 := genericPointGates_length_le row (controlledPointAddPointWorkStart workStart)
  have h5 := packFinitePoint_length_le (pointAddT2 (controlledPointAddPointWorkStart workStart))
    (pointAddT4 (controlledPointAddPointWorkStart workStart))
    (pointAddCandidate (controlledPointAddPointWorkStart workStart))
  have h6 := controlledCopyReg_length_le workStart
    (pointAddCandidate (controlledPointAddPointWorkStart workStart)) outReg
  have h7 := dpackedLoadGates_length_le row
    (pointAddCandidate (controlledPointAddPointWorkStart workStart)) 0
  have h8 := packedLoadGates_length_le row
    (pointAddCandidate (controlledPointAddPointWorkStart workStart)) 0
  simp only [pointAddCandidate_length] at h6 h7 h8
  rw [hP] at h1
  simp only [fastOutGates, fastSetupGates, fastBlockGates, fastPass, List.length_append,
    List.length_reverse, List.length_map, List.length_cons, List.length_nil]
  simp only [pointWidth] at h1
  omega

theorem fastCPAGates_length_le {n : Nat} (row negRow : Fin n) (control : Wire)
    (pointReg : List Wire) (workStart : Wire) (hP : pointReg.length = pointWidth) :
    (fastCPAGates row negRow control pointReg workStart).length ≤ 68000300000 := by
  have h1 := fastOutGates_length_le row control pointReg (controlledPointAddTemp workStart)
    (controlledPointAddAuxStart workStart) hP
  have h2 := fastOutGates_length_le negRow control pointReg (controlledPointAddTemp workStart)
    (controlledPointAddAuxStart workStart) hP
  have h3 := pointSwapReg_length_le pointReg (controlledPointAddTemp workStart)
  rw [hP] at h3
  simp only [fastCPAGates, List.length_append, List.length_reverse, List.length_map]
  simp only [pointWidth] at h3
  omega

theorem fastScalarGates_templateT {n : Nat} (pointReg : List Wire) (workStart : Wire)
    (hP : pointReg.length = pointWidth) :
    ∀ (cs : List Wire) (rs : List (Fin n × Fin n)),
      templateT (fastScalarGates pointReg workStart cs rs) =
        min cs.length rs.length * 22257271064 := by
  intro cs
  induction cs with
  | nil => intro rs; cases rs <;> simp [fastScalarGates, templateT]
  | cons c cs ih =>
    intro rs
    cases rs with
    | nil => simp [fastScalarGates, templateT]
    | cons r rs =>
      simp only [fastScalarGates, templateT_append, fastCPAGates_templateT _ _ _ _ _ hP, ih,
        List.length_cons]
      omega

theorem fastScalarGates_length_le {n : Nat} (pointReg : List Wire) (workStart : Wire)
    (hP : pointReg.length = pointWidth) :
    ∀ (cs : List Wire) (rs : List (Fin n × Fin n)),
      (fastScalarGates pointReg workStart cs rs).length ≤ cs.length * 68000300000 := by
  intro cs
  induction cs with
  | nil => intro rs; cases rs <;> simp [fastScalarGates]
  | cons c cs ih =>
    intro rs
    cases rs with
    | nil => simp [fastScalarGates]
    | cons r rs =>
      have h1 := fastCPAGates_length_le r.1 r.2 c pointReg workStart hP
      have h2 := ih rs
      simp only [fastScalarGates, List.length_append, List.length_cons]
      nlinarith

theorem fastScalarGates_wellFormed {n : Nat} (pointReg : List Wire) (workStart : Wire)
    (cs : List Wire) (rs : List (Fin n × Fin n))
    (hn : (cs ++ (pointReg ++ controlledPointAddWork workStart)).Nodup) :
    ∀ g ∈ fastScalarGates pointReg workStart cs rs, g.WellFormed := by
  induction cs generalizing rs with
  | nil => simp [fastScalarGates]
  | cons c cs ih =>
    cases rs with
    | nil => simp [fastScalarGates]
    | cons r rs =>
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · apply fastCPAGates_wellFormed r.1 r.2 c pointReg workStart ?_ g hg
        have hs := List.nodup_append.mp hn
        have hc : c ∉ pointReg ++ controlledPointAddWork workStart := by
          intro hc
          exact hs.2.2 c List.mem_cons_self c hc rfl
        simpa only [List.singleton_append, List.append_assoc] using
          (List.nodup_cons.mpr ⟨hc, hs.2.1⟩)
      · exact ih rs hn.tail g hg

theorem fastScalarGates_usesOnly {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (pointReg : List Wire) (workStart : Wire) (cs : List Wire) (rs : List (Fin n × Fin n))
    (hn : (cs ++ (pointReg ++ controlledPointAddWork workStart)).Nodup) :
    CircuitUsesOnly (cs ++ (pointReg ++ controlledPointAddWork workStart))
      ((fastScalarGates pointReg workStart cs rs).flatMap
        (TemplateGate.instantiate (readConstant coeffs Q))) := by
  induction cs generalizing rs with
  | nil => cases rs <;> exact fun g hg => by simp [fastScalarGates] at hg
  | cons c cs ih =>
    cases rs with
    | nil => exact fun g hg => by simp [fastScalarGates] at hg
    | cons r rs =>
      have hs := List.nodup_append.mp hn
      have hc : c ∉ pointReg ++ controlledPointAddWork workStart := by
        intro hc
        exact hs.2.2 c List.mem_cons_self c hc rfl
      have hn1 : ([c] ++ pointReg ++ controlledPointAddWork workStart).Nodup := by
        simpa only [List.singleton_append, List.append_assoc] using
          (List.nodup_cons.mpr ⟨hc, hs.2.1⟩)
      let temp := controlledPointAddTemp workStart
      let auxStart := controlledPointAddAuxStart workStart
      let work := controlledPointAddOutWork auxStart
      have houtNodup : ([c] ++ pointReg ++ temp ++ work).Nodup := by
        simpa [temp, auxStart, work, controlledPointAddWork, controlledPointAddTemp,
          controlledPointAddAuxStart, List.append_assoc] using hn1
      have hsupport : [c] ++ pointReg ++ controlledPointAddWork workStart =
          [c] ++ pointReg ++ temp ++ work := by
        simp [temp, auxStart, work, controlledPointAddWork, List.append_assoc]
      have hf := (fastOut_structural c pointReg temp auxStart
        (constantPoint Q (coeffs r.1)) houtNodup).2
      have hb := (fastOut_structural c pointReg temp auxStart
        (constantPoint Q (coeffs r.2)) houtNodup).2
      have hswap : CircuitUsesOnly ([c] ++ pointReg ++ temp ++ work) (pointSwapReg pointReg temp) := by
        apply usesOnly_mono (pointSwapReg_usesOnly' pointReg temp)
        intro w hw
        simp only [List.mem_append] at hw ⊢
        tauto
      have hhead : CircuitUsesOnly ([c] ++ pointReg ++ controlledPointAddWork workStart)
          ((fastCPAGates r.1 r.2 c pointReg workStart).flatMap
            (TemplateGate.instantiate (readConstant coeffs Q))) := by
        rw [fastCPAGates_instantiate, hsupport]
        exact usesOnly_append (usesOnly_append hf hswap) (usesOnly_reverse hb)
      have htail := ih rs hn.tail
      simp only [fastScalarGates, List.flatMap_append]
      refine usesOnly_append (usesOnly_mono hhead ?_) (usesOnly_mono htail ?_)
      · intro w hw
        simp only [List.mem_append, List.mem_cons] at hw ⊢
        tauto
      · intro w hw
        simp only [List.mem_append, List.mem_cons] at hw ⊢
        tauto

end ShorECDLP.Secp256k1.V2
