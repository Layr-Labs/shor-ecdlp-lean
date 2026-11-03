import ShorECDLP.Submission.Entrant.Corners

/-! Output scratch as a masked site.

The output half loads its comparison scratch, writes the doubled-point corner from that
scratch (`ccxList`), writes the `C` corner with a controlled table traversal, compares, and
unloads the scratch with a second traversal. Both corner writes XOR into the accumulator under
selector flags that neither block changes, so they commute. Moving the `C` corner in front of
the scratch load leaves a literal-only middle, and the scratch becomes a masked site whose
unload the block compiler lowers to a measured clear. -/

namespace ShorECDLP.Entrant.WEX
open ShorECDLP.Challenge ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant ECDSAAdd.Secp256k1 ECDSAAdd.ShorPort
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

/-! ### Two controlled XOR blocks under restored flags commute -/

theorem xMask_off (T : List Wire) (k : List Bool) (q : Wire) (h : q ∉ T) : xMask T k q = false :=
  xMask_outside T k q h

/-- `[CX b a] ++ cBits a T k ++ [CX b a]` XORs `k` into `T` under `a ⊕ b` and restores `a`. -/
theorem swapBlock_run (a b : Wire) (T : List Wire) (k : List Bool) (m : List Bool) (s : State)
    (hab : a ≠ b) (ha : a ∉ T) (hb : b ∉ T) :
    run ([.CX b a] ++ (cBits a T k ++ [.CX b a])) m s =
      ⟨s.phase, fun q => s.basis q ^^ ((s.basis a ^^ s.basis b) && xMask T k q)⟩ := by
  rw [run_append, run_append]
  simp only [measurementCount, cBits_records, List.drop_zero, List.take_zero]
  have hcx : ∀ (c t : Wire) (m' : List Bool) (u : State),
      run [.CX c t] m' u = ⟨u.phase, writeBit u.basis t (u.basis t ^^ u.basis c)⟩ := fun _ _ _ _ => rfl
  rw [hcx, cBits_run a T k _ _ ha, hcx]
  apply congrArg (State.mk s.phase)
  funext q
  have hba : b ≠ a := fun e => hab e.symm
  by_cases hq : q = a
  · subst hq
    simp [writeBit, xMask_off T k _ ha, xMask_off T k _ hb, Function.update_of_ne hba]
  · simp [writeBit, Function.update_of_ne hq, Function.update_of_ne hba]

/-- `[CX c b, CX d b, CX a b] ++ cBits b T k ++ [CX a b, CX d b, CX c b]` XORs `k` into `T`
under `b ⊕ c ⊕ d ⊕ a` and restores `b`. -/
theorem selectBlock_run (a b c d : Wire) (T : List Wire) (k : List Bool) (m : List Bool) (s : State)
    (hab : a ≠ b) (hcb : c ≠ b) (hdb : d ≠ b) (hb : b ∉ T) (ha : a ∉ T) (hc : c ∉ T) (hd : d ∉ T) :
    run ([.CX c b, .CX d b, .CX a b] ++ (cBits b T k ++ [.CX a b, .CX d b, .CX c b])) m s =
      ⟨s.phase, fun q => s.basis q ^^ (((s.basis b ^^ s.basis c) ^^ s.basis d ^^ s.basis a) && xMask T k q)⟩ := by
  rw [run_append, run_append]
  simp only [measurementCount, cBits_records, List.drop_zero, List.take_zero]
  have h3 : ∀ (m' : List Bool) (u : State), run [.CX c b, .CX d b, .CX a b] m' u =
      ⟨u.phase, writeBit u.basis b (((u.basis b ^^ u.basis c) ^^ u.basis d) ^^ u.basis a)⟩ := by
    intro m' u
    show (⟨u.phase, _⟩ : State) = _
    simp only [writeBit, Function.update_self, Function.update_of_ne hcb, Function.update_of_ne hdb,
      Function.update_of_ne hab, Function.update_idem]
  have h3' : ∀ (m' : List Bool) (u : State), run [.CX a b, .CX d b, .CX c b] m' u =
      ⟨u.phase, writeBit u.basis b (((u.basis b ^^ u.basis a) ^^ u.basis d) ^^ u.basis c)⟩ := by
    intro m' u
    show (⟨u.phase, _⟩ : State) = _
    simp only [writeBit, Function.update_self, Function.update_of_ne hcb, Function.update_of_ne hdb,
      Function.update_of_ne hab, Function.update_idem]
  rw [h3, cBits_run b T k _ _ hb, h3']
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq : q = b
  · subst hq
    simp only [writeBit, Function.update_self, Function.update_of_ne hab, Function.update_of_ne hcb,
      Function.update_of_ne hdb, xMask_off T k _ hb, xMask_off T k _ ha, xMask_off T k _ hc, xMask_off T k _ hd,
      Bool.and_false, Bool.xor_false]
    try (cases s.basis q <;> cases s.basis a <;> cases s.basis c <;> cases s.basis d <;> rfl)
  · simp only [writeBit, Function.update_of_ne hq, Function.update_of_ne hab, Function.update_of_ne hcb,
      Function.update_of_ne hdb, Function.update_self, xMask_off T k _ ha, xMask_off T k _ hc,
      xMask_off T k _ hd, Bool.and_false, Bool.xor_false]

/-- Two flag-restoring XOR blocks into a common target register commute. -/
theorem xorBlocks_comm (P Q : Program) (T : List Wire) (f g : BasisState → Bool) (kP kQ : List Bool)
    (hP : ∀ m s, run P m s = ⟨s.phase, fun q => s.basis q ^^ (f s.basis && xMask T kP q)⟩)
    (hQ : ∀ m s, run Q m s = ⟨s.phase, fun q => s.basis q ^^ (g s.basis && xMask T kQ q)⟩)
    (hf : ∀ (x : BasisState) (h : Wire → Bool), (∀ q, h q = true → q ∈ T) →
      f (fun q => x q ^^ h q) = f x)
    (hg : ∀ (x : BasisState) (h : Wire → Bool), (∀ q, h q = true → q ∈ T) →
      g (fun q => x q ^^ h q) = g x)
    (hm : ∀ k q, xMask T k q = true → q ∈ T)
    (hPm : measurementCount P = 0) (hQm : measurementCount Q = 0) (m : List Bool) (s : State) :
    run (P ++ Q) m s = run (Q ++ P) m s := by
  rw [run_append, run_append, hPm, hQm, hP, hQ, hQ, hP]
  have hP' : ∀ q, (f s.basis && xMask T kP q) = true → q ∈ T := fun q h => hm kP q (Bool.and_elim_right h)
  have hQ' : ∀ q, (g s.basis && xMask T kQ q) = true → q ∈ T := fun q h => hm kQ q (Bool.and_elim_right h)
  simp only
  rw [hg s.basis _ hP', hf s.basis _ hQ']
  apply congrArg (State.mk s.phase)
  funext q
  cases s.basis q <;> cases (f s.basis && xMask T kP q) <;> cases (g s.basis && xMask T kQ q) <;> rfl

theorem xMask_mem (T : List Wire) (k : List Bool) (q : Wire) (h : xMask T k q = true) : q ∈ T := by
  by_contra hq
  rw [xMask_off T k q hq] at h
  exact Bool.false_ne_true h

/-! ### The corner blocks of the output half -/

theorem corner_wires :
    streamLayout.core.equalNegY ≠ streamLayout.doubleSelect ∧
    streamLayout.infinitySelect ≠ streamLayout.doubleSelect ∧
    streamLayout.genericSelect ≠ streamLayout.doubleSelect ∧
    streamLayout.core.equalNegY ∉ scrDTargets ∧ streamLayout.doubleSelect ∉ scrDTargets ∧
    streamLayout.infinitySelect ∉ scrDTargets ∧ streamLayout.genericSelect ∉ scrDTargets := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

/-- The doubled-point corner block and the `C` corner block commute. -/
theorem corners_swap (kD kC : List Bool) (m : List Bool) (s : State) :
    run ((scrSw1 ++ (cBits streamLayout.core.equalNegY scrDTargets kD ++ scrSw1)) ++
        (scrW1 ++ (cBits streamLayout.doubleSelect scrDTargets kC ++ scrW2))) m s =
      run ((scrW1 ++ (cBits streamLayout.doubleSelect scrDTargets kC ++ scrW2)) ++
        (scrSw1 ++ (cBits streamLayout.core.equalNegY scrDTargets kD ++ scrSw1))) m s := by
  obtain ⟨h1, h2, h3, ha, hb, hc, hd⟩ := corner_wires
  apply xorBlocks_comm _ _ scrDTargets
    (fun x => x streamLayout.core.equalNegY ^^ x streamLayout.doubleSelect)
    (fun x => ((x streamLayout.doubleSelect ^^ x streamLayout.infinitySelect) ^^ x streamLayout.genericSelect) ^^
      x streamLayout.core.equalNegY) kD kC
  · intro m s
    exact swapBlock_run _ _ scrDTargets kD m s h1 ha hb
  · intro m s
    exact selectBlock_run _ _ _ _ scrDTargets kC m s h1 h2 h3 hb ha hc hd
  · intro x h hh
    have e1 : h streamLayout.core.equalNegY = false := by
      cases e : h streamLayout.core.equalNegY
      · rfl
      · exact absurd (hh _ e) ha
    have e2 : h streamLayout.doubleSelect = false := by
      cases e : h streamLayout.doubleSelect
      · rfl
      · exact absurd (hh _ e) hb
    simp only [e1, e2, Bool.xor_false]
  · intro x h hh
    have z : ∀ w, w ∉ scrDTargets → h w = false := fun w hw => by
      cases e : h w
      · rfl
      · exact absurd (hh _ e) hw
    simp only [z _ ha, z _ hb, z _ hc, z _ hd, Bool.xor_false]
  · exact xMask_mem scrDTargets
  · simp [scrSw1, measurementCount, cBits_records, measurementCount_append]
  · simp [scrW1, scrW2, measurementCount, cBits_records, measurementCount_append]

/-! ### The new output half -/

/-- The literal middle of the output scratch site. -/
def scrFMid : WCode 32768 :=
  wLiteral scrSw1 ++ sfxCC ++ wLiteral scrSw1 ++ wLiteral scrNegP ++ sfxF ++ scrDMiddle

theorem scrFMid_litOnly : LitOnly scrFMid := by
  have hz := litOnly_zeroWith (n := 32768)
    (wPairTailBare (yLow streamLayout) streamLayout.infinitySelect streamLayout.core.equalNegY)
    (fun w => litOnly_wLiteral _) streamLayout.control (pairPorts streamLayout)
  unfold scrFMid scrDMiddle sfxCC sfxF
  repeat' first
    | exact litOnly_wLiteral _
    | exact hz
    | apply litOnly_append

def scrFArith : Program := litConcat scrFMid

def scrFSite (rows : Nat → Fin 32768) : WEXUnlookup.MaskedSite 32768 := ⟨windowRoot, scrDPorts rows, scrFArith⟩

theorem scrFSite_code (rows : Nat → Fin 32768) :
    (scrFSite rows).code = [.lookup (some windowRoot) (scrDPorts rows)] ++ wLiteral scrFArith ++
      [.lookup (some windowRoot) (scrDPorts rows)] := rfl

/-- The `C` corner, now ahead of the scratch window. -/
def cornersPre (rows : Nat → Fin 32768) : WCode 32768 :=
  wLiteral scrNegE ++ wLiteral scrNegP ++ wLiteral scrNegE ++ wLiteral scrW1 ++
    [.lookup (some streamLayout.doubleSelect) (scrCPorts rows)] ++ wLiteral scrW2

def portSuffixCodeF (rows : Nat → Fin 32768) : WCode 32768 :=
  cornersPre rows ++ (scrFSite rows).code ++ sfxZ0 ++ sfxPadE

/-- The middle in the form used by the scratch simulation. -/
def fMidProg : Program :=
  scrSw1 ++ (ccxList streamLayout.core.equalNegY scrDWires scrDTargets ++ (scrSw1 ++ (scrNegP ++
    (pointDialogGenericFlag streamLayout ++
      (cxList scrPairWires scrPairTargets ++ (scrP1 ++ ((cxList scrPairWires scrPairTargets ++ [.X (yLow streamLayout)]) ++
        (cxList scrShortWires scrShortTargets ++ (scrP2 ++ cxList scrShortWires scrShortTargets)))))))))

theorem scrFArith_eq : scrFArith = fMidProg := by
  rw [scrFArith, ← litOnly_inst scrFMid scrFMid_litOnly 0 (fun _ => false)]
  simp only [scrFMid, scrDMiddle, sfxCC, sfxF, specialize_append, Tmpl.instantiate_append, specialize_literal,
    Tmpl.instantiate_lit, scr_chain_inst, fMidProg, List.append_assoc]

def preProg (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (a : Nat) : Program :=
  scrNegE ++ (scrNegP ++ (scrNegE ++ (scrW1 ++
    (cBits streamLayout.doubleSelect scrDTargets (portBits read (scrCPorts rows) a) ++ scrW2))))

theorem portSuffixF_inst (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (a : Nat) :
    (specialize (portSuffixCodeF rows) a).instantiate read =
      preProg read rows a ++
      (cBits windowRoot scrAllWires (portBits read (scrDPorts rows) a) ++
        (fMidProg ++ cBits windowRoot scrAllWires (portBits read (scrDPorts rows) a))) ++
      (tail0 ++ Arith.padding (streamLayout.core.poolWire 0) 48842) := by
  simp only [portSuffixCodeF, cornersPre, scrFSite_code, sfxZ0, sfxPadE, tail0, preProg, specialize_append,
    Tmpl.instantiate_append, specialize_literal, Tmpl.instantiate_lit, scr_lookup_some_inst, scrDPorts_targets,
    scrCPorts, scr_point_targets, scrFArith_eq, List.append_assoc]

theorem scrAll_negP : ∀ a ∈ scrAllWires, a ∉ ECDSAAdd.wires scrNegP :=
  neg_disjoint (negateYLayout streamLayout) streamLayout.core.equalNegY ECDSAAdd.p SquareReduction.c
    (negateYLayout_widths streamLayout streamLayout_widths).2 scrAllWires scrAll_neg

theorem avoid_append {S : List Wire} {p q : Program} (hp : ∀ w ∈ S, w ∉ ECDSAAdd.wires p)
    (hq : ∀ w ∈ S, w ∉ ECDSAAdd.wires q) : ∀ w ∈ S, w ∉ ECDSAAdd.wires (p ++ q) := by
  intro w hw h
  rw [ECDSAAdd.wires_append, Finset.mem_union] at h
  exact h.elim (hp w hw) (hq w hw)

theorem scrAll_negE : ∀ w ∈ scrAllWires, w ∉ ECDSAAdd.wires scrNegE :=
  fun w hw => scrAll_flag_avoid w hw _ scrE_flags.1
theorem scrAll_W1 : ∀ w ∈ scrAllWires, w ∉ ECDSAAdd.wires scrW1 :=
  fun w hw => scrAll_flag_avoid w hw _ scrE_flags.2.1
theorem scrAll_W2 : ∀ w ∈ scrAllWires, w ∉ ECDSAAdd.wires scrW2 :=
  fun w hw => scrAll_flag_avoid w hw _ scrE_flags.2.2
theorem scrAll_cC (k : List Bool) :
    ∀ w ∈ scrAllWires, w ∉ ECDSAAdd.wires (cBits streamLayout.doubleSelect scrDTargets k) := by
  intro w hw h
  rcases cBits_wires _ scrDTargets _ w h with e | e
  · subst e
    exact scrAll_flags _ hw (by simp)
  · exact scrAll_d_targets w hw e

/-- Scratch wires avoid the corner prefix. -/
theorem scrAll_pre (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (a : Nat) :
    ∀ w ∈ scrAllWires, w ∉ ECDSAAdd.wires (preProg read rows a) :=
  avoid_append scrAll_negE (avoid_append scrAll_negP (avoid_append scrAll_negE (avoid_append scrAll_W1
    (avoid_append (scrAll_cC _) scrAll_W2))))

theorem pre_sandwich (P M M' Z : Program) (S : List Wire) (K : List Bool) (sim : ScrSim S K M M')
    (hP : ∀ w ∈ S, w ∉ ECDSAAdd.wires P) (m : List Bool) (s : State) (hs : ∀ w ∈ S, s.basis w = false) :
    run (P ++ (xBits S K ++ (M ++ xBits S K)) ++ Z) m s = run (P ++ M' ++ Z) m s := by
  rw [List.append_assoc P, List.append_assoc P, run_append P, run_append P]
  have hs' : ∀ w ∈ S, (run P (m.take (measurementCount P)) s).basis w = false := fun w hw => by
    rw [run_preserves_outside _ _ _ _ (hP w hw)]; exact hs w hw
  have e : xBits S K ++ (M ++ xBits S K) ++ Z = xBits S K ++ M ++ xBits S K ++ Z := by
    simp only [List.append_assoc]
  rw [e, scr_sandwich_append S K M M' Z sim _ _ hs']

theorem windowRoot_not_scrAll : windowRoot ∉ scrAllWires := by
  intro h
  exact scrAll_not_of [windowRoot] (by decide +kernel) windowRoot h List.mem_cons_self

theorem root_flags : windowRoot ∉ [streamLayout.control, streamLayout.core.generic, streamLayout.infinitySelect,
    streamLayout.doubleSelect, streamLayout.genericSelect, streamLayout.core.equalNegY] := by decide +kernel

theorem root_targets : windowRoot ∉ scrDTargets := by decide +kernel

theorem root_negWires : ∀ a ∈ [windowRoot], a ∉ (negateYLayout streamLayout).wires streamLayout.core.equalNegY := by
  decide +kernel

theorem root_negAll : ∀ a ∈ [windowRoot], a ∉ ECDSAAdd.wires scrNegP :=
  neg_disjoint (negateYLayout streamLayout) streamLayout.core.equalNegY ECDSAAdd.p SquareReduction.c
    (negateYLayout_widths streamLayout streamLayout_widths).2 ([windowRoot] : List Wire) root_negWires

theorem root_neg : windowRoot ∉ ECDSAAdd.wires scrNegP := root_negAll windowRoot List.mem_cons_self

theorem root_flagged (p : Program) (hp : ∀ q ∈ ECDSAAdd.wires p, q ∈ [streamLayout.control,
    streamLayout.core.generic, streamLayout.infinitySelect, streamLayout.doubleSelect, streamLayout.genericSelect,
    streamLayout.core.equalNegY]) : ∀ w ∈ ([windowRoot] : List Wire), w ∉ ECDSAAdd.wires p := by
  intro w hw h
  rw [List.mem_singleton.mp hw] at h
  exact root_flags (hp _ h)

theorem root_cC (k : List Bool) :
    ∀ w ∈ ([windowRoot] : List Wire), w ∉ ECDSAAdd.wires (cBits streamLayout.doubleSelect scrDTargets k) := by
  intro w hw h
  rw [List.mem_singleton.mp hw] at h
  rcases cBits_wires _ scrDTargets _ _ h with e | e
  · exact root_flags (e ▸ (by simp))
  · exact root_targets e

theorem root_pre (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (a : Nat) :
    windowRoot ∉ ECDSAAdd.wires (preProg read rows a) :=
  (avoid_append (root_flagged _ scrE_flags.1) (avoid_append root_negAll (avoid_append (root_flagged _ scrE_flags.1)
    (avoid_append (root_flagged _ scrE_flags.2.1) (avoid_append (root_cC _) (root_flagged _ scrE_flags.2.2))))))
    windowRoot List.mem_cons_self

theorem scrFMid_sub (p : Program) (hp : WInstr.literal p ∈ scrFMid) :
    WInstr.literal p ∈ portRowCode3 probeRows := by
  have hD : ∀ i ∈ scrDCorners probeRows ++ sfxF ++ scrDMiddle, i ∈ portRowCode3 probeRows := by
    intro i hi
    have hs : i ∈ portSuffixCodeD probeRows := by
      rw [(suffixE_split probeRows).2]
      simp only [List.mem_append] at hi ⊢
      tauto
    simp only [portRowCode3, portFinite3, List.mem_append]
    tauto
  apply hD
  unfold scrFMid at hp
  simp only [List.mem_append] at hp ⊢
  rcases hp with ((((h | h) | h) | h) | h) | h
  · left; left
    rw [List.mem_singleton.mp h]
    simp [scrDCorners, wLiteral, scrSw1]
  · left; left
    simp only [sfxCC, wLiteral, List.mem_singleton] at h
    rw [h]
    simp [scrDCorners, wLiteral]
  · left; left
    rw [List.mem_singleton.mp h]
    simp [scrDCorners, wLiteral, scrSw1]
  · left; left
    rw [List.mem_singleton.mp h]
    simp [scrDCorners, wLiteral, scrNegP]
  · left; right; exact h
  · right; exact h

theorem root_mid : windowRoot ∉ ECDSAAdd.wires fMidProg := by
  rw [← scrFArith_eq]
  exact litConcat_avoid scrFMid windowRoot (fun p hp => portRow3_literal_root p (scrFMid_sub p hp))

/-- With the window root set and clean scratch, the new output half has the merged-corner
in-place form. -/
theorem portSuffixF_inplace (read : ConstantBit 32768 → Bool) (rows : Nat → Fin 32768) (a : Nat) (C : Point)
    (row : RowReads read (rows a) C) (m : List Bool) (s : State) (hr : s.basis windowRoot = true)
    (hs : ∀ w ∈ scrAllWires, s.basis w = false) :
    run ((specialize (portSuffixCodeF rows) a).instantiate read) m s =
      run (fourCorners streamLayout C ++ midIP read rows a ++ tail0 ++
        Arith.padding (streamLayout.core.poolWire 0) 48842) m s := by
  let K := portBits read (scrDPorts rows) a
  let Z := tail0 ++ Arith.padding (streamLayout.core.poolWire 0) 48842
  rw [portSuffixF_inst]
  -- the controlled loads act as plain loads under the window root
  rw [portSuffix_middle (preProg read rows a)
      (cBits windowRoot scrAllWires K ++ (fMidProg ++ cBits windowRoot scrAllWires K))
      (xBits scrAllWires K ++ (fMidProg ++ xBits scrAllWires K)) Z
      (by simp [measurementCount_append, cBits_records, xBits_records]) s
      (fun k n => cBits_sandwich_run windowRoot scrAllWires K fMidProg n _ windowRoot_not_scrAll root_mid
        (by rw [run_preserves_outside _ _ _ _ (root_pre read rows a)]; exact hr)) m]
  -- the scratch simulation of the literal middle
  have hm := scrD_maps read rows a
  have hK : K = (portBits read (scrPairBits rows (wBit rows .y)) a ++ portBits read (scrShortBits rows) a) ++
      portBits read (scrDExtraBits rows) a := scrDPorts_bits read rows a
  have sim : ScrSim scrAllWires K fMidProg
      (scrSw1 ++ (cBits streamLayout.core.equalNegY scrDTargets
        (portBits read (scrShortBits rows) a ++ portBits read (scrDExtraBits rows) a) ++
        (scrSw1 ++ (scrNegP ++ midIP read rows a)))) := by
    rw [hK]
    exact (scrD_swSim _).1.append ((scrD_ccxSim _ _ hm.2.2).append ((scrD_swSim _).1.append
      ((scrD_negSim _).append (scrD_midSim _ _ _ _ rfl hm.1 hm.2.1))))
  rw [pre_sandwich _ _ _ _ _ _ sim (scrAll_pre read rows a) m s hs]
  -- reorder the two corner blocks
  rw [← scrFCorners_inst read rows a C row, scrFCorners_inst2]
  have sw := fun k n => (corners_swap (portBits read (scrShortBits rows) a ++ portBits read (scrDExtraBits rows) a)
    (portBits read (scrCPorts rows) a) n (run (scrNegE ++ (scrNegP ++ scrNegE)) k s)).symm
  have h := portSuffix_middle (scrNegE ++ (scrNegP ++ scrNegE))
    ((scrW1 ++ (cBits streamLayout.doubleSelect scrDTargets (portBits read (scrCPorts rows) a) ++ scrW2)) ++
      (scrSw1 ++ (cBits streamLayout.core.equalNegY scrDTargets
        (portBits read (scrShortBits rows) a ++ portBits read (scrDExtraBits rows) a) ++ scrSw1)))
    ((scrSw1 ++ (cBits streamLayout.core.equalNegY scrDTargets
        (portBits read (scrShortBits rows) a ++ portBits read (scrDExtraBits rows) a) ++ scrSw1)) ++
      (scrW1 ++ (cBits streamLayout.doubleSelect scrDTargets (portBits read (scrCPorts rows) a) ++ scrW2)))
    (scrNegP ++ midIP read rows a ++ Z)
    (by simp [measurementCount_append, cBits_records, scrSw1, scrW1, scrW2, measurementCount]) s sw m
  simp only [preProg, Z, List.append_assoc] at h ⊢
  exact h

end
end ShorECDLP.Entrant.WEX
