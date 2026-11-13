import ShorECDLP.Submission.Entrant.StackBase
import ShorECDLP.Submission.Entrant.MixedFirst

/-! Bridge for the mixed (joint) first load: the reordering lemma on StackBase's kernel objects. -/
namespace ShorECDLP.Entrant.Single.Distribution
open Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge ShorECDLP.Paper2607_13816
open ShorECDLP.Paper2607_13816.ChallengeMigration ShorECDLP.Entrant.Single
noncomputable section
attribute [local irreducible] fourierOutcomes
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
variable [b : WindowBody] [ledger : ProducerResources b]

theorem list_sum_swap {A B M : Type} [AddCommMonoid M] (xs : List A) (ys : List B) (f : A → B → M) :
    (xs.map (fun x => (ys.map (fun y => f x y)).sum)).sum =
    (ys.map (fun y => (xs.map (fun x => f x y)).sum)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    rw [← List.sum_map_add]

theorem pathEnd_translate (path : List (DigitWindow × List Bool)) (inputs : List (List Bool))
    (A B : Point) : pathEnd path inputs (A + B) = pathEnd path inputs A + B := by
  induction path generalizing inputs A with
  | nil => cases inputs <;> rfl
  | cons w path ih =>
    cases inputs with
    | nil => rfl
    | cons i is =>
      simp only [pathEnd]
      rw [show A + B + w.1.point (boolWordToNat i) = (A + w.1.point (boolWordToNat i)) + B by abel]
      exact ih is _

theorem inputWords_cons_sum {M : Type} [AddCommMonoid M] (w : Nat) (ws : List Nat)
    (g : List (List Bool) → M) :
    ((inputWords (w :: ws)).map g).sum =
      ((fourierOutcomes w).map (fun input =>
        ((inputWords ws).map (fun rest => g (input :: rest))).sum)).sum := by
  simp only [inputWords, List.map_flatMap, flat_sum, List.map_map, Function.comp_def]

theorem mixed_branch_state
    (step : DigitWindow → List Bool → List Bool → State →ₗ[ℂ] State)
    (root : BasisState) (dwL dwR : DigitWindow) (bL bR : List Bool)
    (lbp rbp : List (DigitWindow × List Bool))
    (hstep : ∀ w ∈ lbp ++ rbp, ∀ prior P,
      step w.1 prior w.2 (ket (pointWrite P root)) =
        (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ w.1.width) •
          ((fourierOutcomes w.1.width).map (fun input =>
            fourierBitAmplitude .inverse input.reverse prior w.2 •
              ket (pointWrite (P + w.1.point (boolWordToNat input)) root))).sum)
    (J : State)
    (hJ : J = (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ (dwL.width + dwR.width)) •
        ((fourierOutcomes dwL.width).map (fun inL =>
          ((fourierOutcomes dwR.width).map (fun inR =>
            (fourierBitAmplitude .inverse inL.reverse List.nil bL *
              fourierBitAmplitude .inverse inR.reverse List.nil bR) •
              ket (pointWrite (dwL.point (boolWordToNat inL) + dwR.point (boolWordToNat inR)) root))).sum)).sum) :
    axisBranch step rbp (bR.reverse ++ List.nil) (axisBranch step lbp (bL.reverse ++ List.nil) J) =
      twoInputState root ((dwL, bL) :: lbp) ((dwR, bR) :: rbp) 0 := by
  classical
  subst hJ
  have hL : ∀ P, axisBranch step lbp (bL.reverse ++ List.nil) (ket (pointWrite P root)) =
      pointKernel root lbp (bL.reverse ++ List.nil) P := fun P =>
    axisBranch_point step root lbp (fun w hw => hstep w (List.mem_append_left _ hw)) _ P
  have hR : ∀ P, axisBranch step rbp (bR.reverse ++ List.nil) (ket (pointWrite P root)) =
      pointKernel root rbp (bR.reverse ++ List.nil) P := fun P =>
    axisBranch_point step root rbp (fun w hw => hstep w (List.mem_append_right _ hw)) _ P
  simp only [map_smul, map_list_sum, List.map_map, Function.comp_def, hL, hR, pointKernel_inputs]
  unfold twoInputState
  simp only [pathWidths, List.map_cons, inputWords_cons_sum, inputWeight, pathEnd]
  simp only [List.smul_sum, List.map_map, Function.comp_def, smul_smul]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  conv_rhs => rw [list_sum_swap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro b hb
  apply congrArg List.sum
  apply List.map_congr_left
  intro x hx
  apply congrArg List.sum
  apply List.map_congr_left
  intro y hy
  have hp : pathEnd lbp x (dwL.point (boolWordToNat a) + dwR.point (boolWordToNat b)) =
      pathEnd lbp x (0 + dwL.point (boolWordToNat a)) + dwR.point (boolWordToNat b) := by
    rw [zero_add]
    exact pathEnd_translate lbp x _ _
  rw [hp, pow_add]
  congr 1
  ring


/-- The mixed order of operations, stated on model branches: after the joint first section the
left bodies run on the left head records and the right bodies on the right head records. -/
theorem mixed_modelBranch_state {n : Nat} {read : ConstantBit n → Bool}
    (root : BasisState) (dwL dwR : DigitWindow) (bL bR : List Bool)
    (lbp rbp : List (WindowModel read × List Bool))
    (hrule : ∀ w ∈ lbp ++ rbp, PointRule root w.1)
    (J : State)
    (hJ : J = (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ (dwL.width + dwR.width)) •
        ((fourierOutcomes dwL.width).map (fun inL =>
          ((fourierOutcomes dwR.width).map (fun inR =>
            (fourierBitAmplitude .inverse inL.reverse List.nil bL *
              fourierBitAmplitude .inverse inR.reverse List.nil bR) •
              ket (pointWrite (dwL.point (boolWordToNat inL) + dwR.point (boolWordToNat inR)) root))).sum)).sum) :
    modelBranch rbp (bR.reverse ++ List.nil) (modelBranch lbp (bL.reverse ++ List.nil) J) =
      twoInputState root ((dwL, bL) :: logicalPath modelDigit lbp)
        ((dwR, bR) :: logicalPath modelDigit rbp) 0 := by
  classical
  subst hJ
  have hL : ∀ P, modelBranch lbp (bL.reverse ++ List.nil) (ket (pointWrite P root)) =
      pointKernel root (logicalPath modelDigit lbp) (bL.reverse ++ List.nil) P := fun P =>
    modelBranch_point modelDigit root lbp
      (fun w hw prior P => hrule w (List.mem_append_left _ hw) prior w.2 P) _ P
  have hR : ∀ P, modelBranch rbp (bR.reverse ++ List.nil) (ket (pointWrite P root)) =
      pointKernel root (logicalPath modelDigit rbp) (bR.reverse ++ List.nil) P := fun P =>
    modelBranch_point modelDigit root rbp
      (fun w hw prior P => hrule w (List.mem_append_right _ hw) prior w.2 P) _ P
  simp only [map_smul, map_list_sum, List.map_map, Function.comp_def, hL, hR, pointKernel_inputs]
  unfold twoInputState
  simp only [pathWidths, List.map_cons, inputWords_cons_sum, inputWeight, pathEnd]
  simp only [List.smul_sum, List.map_map, Function.comp_def, smul_smul]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  conv_rhs => rw [list_sum_swap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro b hb
  apply congrArg List.sum
  apply List.map_congr_left
  intro x hx
  apply congrArg List.sum
  apply List.map_congr_left
  intro y hy
  have hp : pathEnd (logicalPath modelDigit lbp) x (dwL.point (boolWordToNat a) + dwR.point (boolWordToNat b)) =
      pathEnd (logicalPath modelDigit lbp) x (0 + dwL.point (boolWordToNat a)) + dwR.point (boolWordToNat b) := by
    rw [zero_add]
    exact pathEnd_translate _ x _ _
  rw [hp, pow_add]
  congr 1
  ring


/-- Ideal four-segment instrument: left head, right head, left bodies, right bodies. -/
def idealMixed {n : Nat} {read : ConstantBit n → Bool}
    (WA WB : WindowModel read) (LB RB : List (WindowModel read))
    (terminal : List Bool → List Bool → Instrument) : Instrument :=
  idealAxis [WA] List.nil (fun tagA =>
    idealAxis [WB] List.nil (fun tagB =>
      idealAxis LB tagA (fun lhs => idealAxis RB tagB (fun rhs => terminal lhs rhs))))

theorem idealMixed_mass {n : Nat} {read : ConstantBit n → Bool}
    (WA WB : WindowModel read) (LB RB : List (WindowModel read))
    (terminal : List Bool → List Bool → Instrument) (ψ : State) :
    (idealMixed WA WB LB RB terminal).bornMass ψ =
      ((fourierOutcomes WA.physical.wires.length).map (fun bA =>
        ((fourierOutcomes WB.physical.wires.length).map (fun bB =>
          ((outputPaths LB).map (fun lbp => ((outputPaths RB).map (fun rbp =>
            (terminal ((lbp.map Prod.snd).flatten.reverse ++ (bA.reverse ++ List.nil))
              ((rbp.map Prod.snd).flatten.reverse ++ (bB.reverse ++ List.nil))).bornMass
              (modelBranch rbp (bB.reverse ++ List.nil)
                (modelBranch lbp (bA.reverse ++ List.nil)
                  (WB.step List.nil bB (WA.step List.nil bA ψ)))))).sum)).sum)).sum)).sum := by
  have hnil : ∀ (prior : List Bool) (K : List Bool → Instrument), idealAxis ([] : List (WindowModel read)) prior K = K prior :=
    fun _ _ => rfl
  unfold idealMixed
  rw [idealAxis_cons_mass]
  simp only [hnil]
  apply congrArg List.sum
  apply List.map_congr_left
  intro bA hbA
  rw [idealAxis_cons_mass]
  simp only [hnil]
  apply congrArg List.sum
  apply List.map_congr_left
  intro bB hbB
  rw [idealAxis_paths_mass]
  apply congrArg List.sum
  apply List.map_congr_left
  intro lbp hlbp
  rw [idealAxis_paths_mass]


/-- Summing a head bank and the output paths of an axis tail is summing over one long word. -/
theorem sum_head_paths {n : Nat} {read : ConstantBit n → Bool} {M : Type} [AddCommMonoid M]
    (w : Nat) (WS : List (WindowModel read)) (f : List Bool → M) :
    ((fourierOutcomes w).map (fun b => ((outputPaths WS).map (fun lbp =>
        f (b ++ (lbp.map Prod.snd).flatten))).sum)).sum =
      ((fourierOutcomes (w + precision WS)).map f).sum := by
  rw [outputPaths_zip]
  simp only [List.map_map, Function.comp_def]
  have hw : (fourierOutcomes (w + precision WS)).map f =
      ((inputWords (w :: WS.map (fun x => x.physical.wires.length))).map
        (fun outputs => f outputs.flatten)) := by
    have h := inputWords_flatten (w :: WS.map (fun x => x.physical.wires.length))
    simp only [List.sum_cons, precision] at h ⊢
    rw [← h, List.map_map]
    rfl
  rw [hw, inputWords_cons_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro b hb
  apply congrArg List.sum
  apply List.map_congr_left
  intro ins hins
  have hl : ins.length = WS.length := by
    have := (inputWords_mem _ _).mp hins
    simpa using congrArg List.length this
  rw [List.map_snd_zip (by omega)]
  simp only [List.flatten_cons]


/-- The joint-first-load closed form fed to the reordering lemma. -/
def jointClosedForm (dwL dwR : DigitWindow) (bA bB : List Bool) (root : BasisState) : State :=
  (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ (dwL.width + dwR.width)) •
    ((fourierOutcomes dwL.width).map (fun inL =>
      ((fourierOutcomes dwR.width).map (fun inR =>
        (fourierBitAmplitude .inverse inL.reverse List.nil bA *
          fourierBitAmplitude .inverse inR.reverse List.nil bB) •
          ket (pointWrite (dwL.point (boolWordToNat inL) + dwR.point (boolWordToNat inR)) root))).sum)).sum

theorem mixed_kernel {n : Nat} {read : ConstantBit n → Bool}
    (Q : Point) (root : BasisState) (ψ : State)
    (WA WB : WindowModel read) (LB RB : List (WindowModel read))
    (dwL dwR : DigitWindow)
    (hfirst : ∀ bA ∈ fourierOutcomes dwL.width, ∀ bB ∈ fourierOutcomes dwR.width,
      WB.step List.nil bB (WA.step List.nil bA ψ) = jointClosedForm dwL dwR bA bB root)
    (hpoint : ∀ w ∈ LB ++ RB, PointRule root w)
    (hheadL : ∀ v, dwL.point v + dwL.bias = (v * 2 ^ precision LB) • G)
    (hheadR : ∀ v, dwR.point v + dwR.bias = (v * 2 ^ precision RB) • Q)
    (hLB : ModelWeights G LB) (hRB : ModelWeights Q RB)
    (hbias : dwL.bias + (LB.map WindowModel.bias).sum + (dwR.bias + (RB.map WindowModel.bias).sum) = 0) :
    ∀ bA ∈ fourierOutcomes dwL.width, ∀ bB ∈ fourierOutcomes dwR.width,
      ∀ lbp ∈ outputPaths LB, ∀ rbp ∈ outputPaths RB,
        modelBranch rbp (bB.reverse ++ List.nil) (modelBranch lbp (bA.reverse ++ List.nil)
          (WB.step List.nil bB (WA.step List.nil bA ψ))) =
        idealPointState Q root (dwL.width + precision LB) (dwR.width + precision RB)
          (bA ++ (lbp.map Prod.snd).flatten) (bB ++ (rbp.map Prod.snd).flatten) := by
  intro bA hbA bB hbB lbp hlbp rbp hrbp
  rw [hfirst bA hbA bB hbB]
  have hrule : ∀ w ∈ lbp ++ rbp, PointRule root w.1 := by
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · apply hpoint w.1 (List.mem_append_left _ _)
      rw [← outputPath_models LB lbp hlbp]
      exact List.mem_map.mpr ⟨w, hw, rfl⟩
    · apply hpoint w.1 (List.mem_append_right _ _)
      rw [← outputPath_models RB rbp hrbp]
      exact List.mem_map.mpr ⟨w, hw, rfl⟩
  rw [mixed_modelBranch_state root dwL dwR bA bB lbp rbp hrule (jointClosedForm dwL dwR bA bB root) rfl]
  have hlen := outputPath_lengths LB lbp hlbp
  have hren := outputPath_lengths RB rbp hrbp
  have hbA' := (fourierOutcomes_mem _ _).mp hbA
  have hbB' := (fourierOutcomes_mem _ _).mp hbB
  rw [twoInputState_ideal_of_weights Q root ((dwL, bA) :: logicalPath modelDigit lbp)
    ((dwR, bB) :: logicalPath modelDigit rbp) 0
    (by
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact hbA'
      · exact hlen w hw)
    (by
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact hbB'
      · exact hren w hw)
    DigitWindow.bias DigitWindow.bias
    ⟨by
        intro v
        simp only [outputPath_widths LB lbp hlbp]
        exact hheadL v,
      outputPath_weights G LB hLB lbp hlbp⟩
    ⟨by
        intro v
        simp only [outputPath_widths RB rbp hrbp]
        exact hheadR v,
      outputPath_weights Q RB hRB rbp hrbp⟩
    (by
      unfold biasSum
      simp only [List.map_cons, List.sum_cons]
      have h1 := outputPath_bias LB lbp hlbp
      have h2 := outputPath_bias RB rbp hrbp
      unfold biasSum at h1 h2
      rw [h1, h2]
      exact hbias.symm)]
  have hwl : (pathWidths (logicalPath modelDigit lbp)).sum = precision LB := by
    rw [outputPath_widths LB lbp hlbp]; rfl
  have hwr : (pathWidths (logicalPath modelDigit rbp)).sum = precision RB := by
    rw [outputPath_widths RB rbp hrbp]; rfl
  have hsl : (logicalPath modelDigit lbp).map Prod.snd = lbp.map Prod.snd := by
    simp [logicalPath, List.map_map, Function.comp_def]
  have hsr : (logicalPath modelDigit rbp).map Prod.snd = rbp.map Prod.snd := by
    simp [logicalPath, List.map_map, Function.comp_def]
  have e1 : (pathWidths ((dwL, bA) :: logicalPath modelDigit lbp)).sum = dwL.width + precision LB := by
    show (dwL.width :: pathWidths (logicalPath modelDigit lbp)).sum = _
    rw [List.sum_cons, hwl]
  have e2 : (pathWidths ((dwR, bB) :: logicalPath modelDigit rbp)).sum = dwR.width + precision RB := by
    show (dwR.width :: pathWidths (logicalPath modelDigit rbp)).sum = _
    rw [List.sum_cons, hwr]
  rw [e1, e2]
  simp only [List.map_cons, List.flatten_cons, hsl, hsr]


theorem idealMixed_event_mass {n : Nat} {read : ConstantBit n → Bool}
    (Q : Point) (root : BasisState) (ψ : State)
    (WA WB : WindowModel read) (LB RB : List (WindowModel read))
    (dwL dwR : DigitWindow)
    (hwA : WA.physical.wires.length = dwL.width) (hwB : WB.physical.wires.length = dwR.width)
    (hfirst : ∀ bA ∈ fourierOutcomes dwL.width, ∀ bB ∈ fourierOutcomes dwR.width,
      WB.step List.nil bB (WA.step List.nil bA ψ) = jointClosedForm dwL dwR bA bB root)
    (hpoint : ∀ w ∈ LB ++ RB, PointRule root w)
    (hheadL : ∀ v, dwL.point v + dwL.bias = (v * 2 ^ precision LB) • G)
    (hheadR : ∀ v, dwR.point v + dwR.bias = (v * 2 ^ precision RB) • Q)
    (hLB : ModelWeights G LB) (hRB : ModelWeights Q RB)
    (hbias : dwL.bias + (LB.map WindowModel.bias).sum + (dwR.bias + (RB.map WindowModel.bias).sum) = 0)
    (J : Instrument) (hJ : ∀ φ, J.bornMass φ = normSq φ) (accept : Nat → Nat → Bool) :
    (idealMixed WA WB LB RB (fun lhs rhs =>
      if accept (fourierWordLSB lhs.reverse) (fourierWordLSB rhs.reverse) then J else List.nil)).bornMass ψ =
      idealEventMass Q root (dwL.width + precision LB) (dwR.width + precision RB) accept := by
  classical
  have hker := mixed_kernel Q root ψ WA WB LB RB dwL dwR hfirst hpoint hheadL hheadR hLB hRB hbias
  let F : List Bool → List Bool → ℝ := fun x y =>
    if accept (fourierWordLSB x) (fourierWordLSB y) then
      normSq (idealPointState Q root (dwL.width + precision LB) (dwR.width + precision RB) x y) else 0
  rw [idealMixed_mass, hwA, hwB]
  have step1 : ((fourierOutcomes dwL.width).map (fun bA =>
        ((fourierOutcomes dwR.width).map (fun bB =>
          ((outputPaths LB).map (fun lbp => ((outputPaths RB).map (fun rbp =>
            (if accept (fourierWordLSB (((lbp.map Prod.snd).flatten.reverse ++ (bA.reverse ++ List.nil)).reverse))
                (fourierWordLSB (((rbp.map Prod.snd).flatten.reverse ++ (bB.reverse ++ List.nil)).reverse))
              then J else List.nil).bornMass
              (modelBranch rbp (bB.reverse ++ List.nil)
                (modelBranch lbp (bA.reverse ++ List.nil)
                  (WB.step List.nil bB (WA.step List.nil bA ψ)))))).sum)).sum)).sum)).sum =
      ((fourierOutcomes dwL.width).map (fun bA =>
        ((fourierOutcomes dwR.width).map (fun bB =>
          ((outputPaths LB).map (fun lbp => ((outputPaths RB).map (fun rbp =>
            F (bA ++ (lbp.map Prod.snd).flatten) (bB ++ (rbp.map Prod.snd).flatten))).sum)).sum)).sum)).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro bA hbA
    apply congrArg List.sum
    apply List.map_congr_left
    intro bB hbB
    apply congrArg List.sum
    apply List.map_congr_left
    intro lbp hlbp
    apply congrArg List.sum
    apply List.map_congr_left
    intro rbp hrbp
    rw [hker bA hbA bB hbB lbp hlbp rbp hrbp]
    simp only [List.reverse_append, List.reverse_reverse, List.append_nil, F]
    split_ifs
    · exact hJ _
    · simp [Instrument.bornMass]
  rw [step1]
  have hinner : ∀ x : List Bool,
      ((fourierOutcomes dwR.width).map (fun bB => ((outputPaths RB).map (fun rbp =>
        F x (bB ++ (rbp.map Prod.snd).flatten))).sum)).sum =
      ((fourierOutcomes (dwR.width + precision RB)).map (F x)).sum :=
    fun x => sum_head_paths dwR.width RB (F x)
  have h2 : (fourierOutcomes dwL.width).map (fun bA =>
        ((fourierOutcomes dwR.width).map (fun bB =>
          ((outputPaths LB).map (fun lbp => ((outputPaths RB).map (fun rbp =>
            F (bA ++ (lbp.map Prod.snd).flatten) (bB ++ (rbp.map Prod.snd).flatten))).sum)).sum)).sum) =
      (fourierOutcomes dwL.width).map (fun bA =>
        ((outputPaths LB).map (fun lbp =>
          ((fourierOutcomes (dwR.width + precision RB)).map (F (bA ++ (lbp.map Prod.snd).flatten))).sum)).sum) := by
    apply List.map_congr_left
    intro bA hbA
    rw [list_sum_swap]
    apply congrArg List.sum
    apply List.map_congr_left
    intro lbp hlbp
    exact hinner _
  rw [h2]
  have h3 := sum_head_paths dwL.width LB
    (fun x => ((fourierOutcomes (dwR.width + precision RB)).map (F x)).sum)
  rw [h3]
  unfold idealEventMass
  rfl


/-! ### The four physical segments -/

section MixedProgram
variable {n : Nat}

abbrev mixS1 (WA : Window n) (start : Nat) : Nat := start + axisCount [WA]
abbrev mixS2 (WA WB : Window n) (start : Nat) : Nat := mixS1 WA start + axisCount [WB]
abbrev mixS3 (WA WB : Window n) (LB : List (Window n)) (start : Nat) : Nat :=
  mixS2 WA WB start + axisCount LB
abbrev mixS4 (WA WB : Window n) (LB RB : List (Window n)) (start : Nat) : Nat :=
  mixS3 WA WB LB start + axisCount RB

theorem mixS2_ge (WA WB : Window n) (start : Nat) :
    start + WA.count + WA.wires.length ≤ mixS2 WA WB start := by
  unfold mixS2 mixS1 axisCount; omega

theorem mixS3_ge (WA WB : Window n) (LB : List (Window n)) (start : Nat) :
    mixS1 WA start + WB.count + WB.wires.length ≤ mixS3 WA WB LB start := by
  unfold mixS3 mixS2 axisCount; omega

/-- Records of the left head bank, newest first, lifted to the start of the left bodies. -/
def mixPriorL (WA WB : Window n) (start : Nat) : List (Fin (mixS2 WA WB start)) :=
  (nextPrior WA.count WA.wires.length (List.nil : List (Fin start))).map
    (Fin.castLE (mixS2_ge WA WB start))

/-- Records of the right head bank, newest first, lifted to the start of the right bodies. -/
def mixPriorR (WA WB : Window n) (LB : List (Window n)) (start : Nat) :
    List (Fin (mixS3 WA WB LB start)) :=
  (nextPrior WB.count WB.wires.length (List.nil : List (Fin (mixS1 WA start)))).map
    (Fin.castLE (mixS3_ge WA WB LB start))

/-- The head segment: the left head bank (with the joint load inside). -/
def mixHead (WA : Window n) (start : Nat) : Straight n start (mixS1 WA start) :=
  axis [WA] start List.nil

/-- Right head bank, then the left bodies, then the right bodies. -/
def mixTail (WA WB : Window n) (LB RB : List (Window n)) (start : Nat) :
    Straight n (mixS1 WA start) (mixS4 WA WB LB RB start) :=
  (axis [WB] (mixS1 WA start) List.nil).append
    ((axis LB (mixS2 WA WB start) (mixPriorL WA WB start)).append
      (axis RB (mixS3 WA WB LB start) (mixPriorR WA WB LB start)))

end MixedProgram


section MixedTagged
variable {n : Nat} {read : ConstantBit n → Bool}

def mixProgram (WA WB : Window n) (LB RB : List (Window n)) (start : Nat) :
    Straight n start (mixS4 WA WB LB RB start) :=
  (mixHead WA start).append (mixTail WA WB LB RB start)

/-- Physical branches of the four segments, tagged with the two Fourier words
(left = left bodies over the left head, right = right bodies over the right head). -/
def taggedMixed (WA WB : WindowModel read) (LB RB : List (WindowModel read))
    (start : Nat) (history : Fin start → Bool) :
    List ((List Bool × List Bool) × InstrumentBranch) :=
  (taggedAxis [WA] start history List.nil).flatMap (fun a =>
    (taggedAxis [WB] (mixS1 WA.physical start)
      (historyAfter (mixS1 WA.physical start) history a.2.history) List.nil).flatMap (fun b =>
      (taggedAxis LB (mixS2 WA.physical WB.physical start)
        (historyAfter (mixS2 WA.physical WB.physical start)
          (historyAfter (mixS1 WA.physical start) history a.2.history) b.2.history)
        (mixPriorL WA.physical WB.physical start)).flatMap (fun l =>
        (taggedAxis RB (mixS3 WA.physical WB.physical (LB.map WindowModel.physical) start)
          (historyAfter (mixS3 WA.physical WB.physical (LB.map WindowModel.physical) start)
            (historyAfter (mixS2 WA.physical WB.physical start)
              (historyAfter (mixS1 WA.physical start) history a.2.history) b.2.history)
            l.2.history)
          (mixPriorR WA.physical WB.physical (LB.map WindowModel.physical) start)).map (fun r =>
          ((l.1, r.1), a.2.seq (b.2.seq (l.2.seq r.2)))))))

theorem mixData_tagged (WA WB : WindowModel read) (LB RB : List (WindowModel read))
    (start : Nat) (history : Fin start → Bool) :
    ((mixProgram WA.physical WB.physical (LB.map WindowModel.physical)
      (RB.map WindowModel.physical) start).instantiate read history).run =
      (taggedMixed WA WB LB RB start history).map Prod.snd := by
  unfold mixProgram mixHead mixTail taggedMixed
  simp only [append_run_history]
  have hA : ((axis [WA.physical] start List.nil).instantiate read history).run =
      (taggedAxis [WA] start history List.nil).map Prod.snd := axis_run_tagged [WA] start history List.nil
  have hB : ∀ (s : Nat) (h : Fin s → Bool), ((axis [WB.physical] s List.nil).instantiate read h).run =
      (taggedAxis [WB] s h List.nil).map Prod.snd := fun s h => axis_run_tagged [WB] s h List.nil
  simp only [hA, hB, axis_run_tagged]
  simp only [List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def]

end MixedTagged


section MixedPriors
variable {n : Nat}

theorem mixS1_le_mixS2 (WA WB : Window n) (start : Nat) : mixS1 WA start ≤ mixS2 WA WB start := by
  unfold mixS2; omega

theorem mixS2_le_mixS3 (WA WB : Window n) (LB : List (Window n)) (start : Nat) :
    mixS2 WA WB start ≤ mixS3 WA WB LB start := by
  unfold mixS3; omega

/-- After one head bank ran with branch history `arith ++ bits`, its stored prior reads exactly the
(newest-first) outcome, whatever later records follow. -/
theorem priorBank_map (W : Window n) {s e : Nat} (history : Fin s → Bool) (arith bits other : List Bool)
    (ha : arith.length = W.count) (hb : bits.length = W.wires.length)
    (he : s + axisCount [W] ≤ e) :
    ((nextPrior W.count W.wires.length (List.nil : List (Fin s))).map
      (Fin.castLE (by unfold axisCount at he; omega : s + W.count + W.wires.length ≤ e))).map
      (historyAfter e (historyAfter (s + axisCount [W]) history (arith ++ bits ++ List.nil)) other) =
      bits.reverse := by
  have key := nextPrior_map W.count W.wires.length (List.nil : List (Fin s)) history arith bits ha hb
  rw [List.map_map]
  have hfun : (historyAfter e (historyAfter (s + axisCount [W]) history (arith ++ bits ++ List.nil)) other) ∘
        (Fin.castLE (by unfold axisCount at he; omega : s + W.count + W.wires.length ≤ e)) =
      historyAfter (s + W.count + W.wires.length) (historyAfter (s + W.count) history arith) bits := by
    funext i
    simp only [Function.comp_apply, Fin.castLE]
    rw [historyAfter_old (historyAfter (s + axisCount [W]) history (arith ++ bits ++ List.nil)) other he
      ⟨i.val, by have := i.isLt; unfold axisCount; omega⟩]
    have hl : List.ofFn (historyAfter (s + W.count) history arith) = List.ofFn history ++ arith :=
      historyAfter_list history arith (by omega)
    show (List.ofFn history ++ (arith ++ bits ++ List.nil))[i.val]?.getD false =
      (List.ofFn (historyAfter (s + W.count) history arith) ++ bits)[i.val]?.getD false
    rw [hl]
    simp only [List.append_assoc, List.append_nil]
  rw [hfun, key]
  simp

theorem mixPriorL_map (WA WB : Window n) (start : Nat) (history : Fin start → Bool)
    (arith bits other : List Bool) (ha : arith.length = WA.count) (hb : bits.length = WA.wires.length) :
    (mixPriorL WA WB start).map
      (historyAfter (mixS2 WA WB start)
        (historyAfter (mixS1 WA start) history (arith ++ bits ++ List.nil)) other) = bits.reverse :=
  priorBank_map WA history arith bits other ha hb (mixS1_le_mixS2 WA WB start)

theorem mixPriorR_map (WA WB : Window n) (LB : List (Window n)) (start : Nat)
    (history : Fin (mixS1 WA start) → Bool)
    (arith bits other : List Bool) (ha : arith.length = WB.count) (hb : bits.length = WB.wires.length) :
    (mixPriorR WA WB LB start).map
      (historyAfter (mixS3 WA WB LB start)
        (historyAfter (mixS2 WA WB start) history (arith ++ bits ++ List.nil)) other) = bits.reverse :=
  priorBank_map WB history arith bits other ha hb (mixS2_le_mixS3 WA WB LB start)

end MixedPriors


section MixedMass
variable {n : Nat} {read : ConstantBit n → Bool}

/-- Physical branches of the four segments, selected by a terminal instrument on the two Fourier words. -/
def selectedMixed (WA WB : WindowModel read) (LB RB : List (WindowModel read))
    (start : Nat) (history : Fin start → Bool)
    (terminal : List Bool → List Bool → Instrument) : Instrument :=
  (taggedMixed WA WB LB RB start history).flatMap (fun a => (terminal a.1.1 a.1.2).map a.2.seq)

/-- One window's physical branch: arithmetic record, then its Fourier outcome. -/
theorem taggedAxis_single_data (W : WindowModel read) {start : Nat} (history : Fin start → Bool)
    (prior : List (Fin start)) (t : List Bool × InstrumentBranch)
    (ht : t ∈ taggedAxis [W] start history prior) :
    ∃ arith bits : List Bool, arith.length = W.physical.count ∧ bits.length = W.physical.wires.length ∧
      t.2.history = arith ++ bits ++ List.nil ∧ t.1 = bits.reverse ++ prior.map history := by
  obtain ⟨a, ha, ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨bits, hb, ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨b, hbt, rfl⟩ := List.mem_map.mp ht
  simp only [taggedAxis, List.mem_singleton] at hbt
  subst hbt
  have hla : a.history.length = W.physical.count := by
    have h := straight_history_length _ read history a ha
    omega
  have hlb := (fourierOutcomes_mem _ _).mp hb
  refine ⟨a.history, bits, hla, hlb, ?_, ?_⟩
  · simp [InstrumentBranch.seq]
  · simp only
    rw [nextPrior_map _ _ _ _ _ _ hla hlb]

theorem mix_level_LR (LB RB : List (WindowModel read)) {s2 : Nat} (hAB : Fin s2 → Bool)
    (priorL : List (Fin s2))
    (priorR : List (Fin (s2 + axisCount (LB.map WindowModel.physical)))) (tagB : List Bool)
    (hprior : ∀ other : List Bool,
      priorR.map (historyAfter (s2 + axisCount (LB.map WindowModel.physical)) hAB other) = tagB)
    (terminal : List Bool → List Bool → Instrument) (φ : State) (hφ : Ready (LB ++ RB) φ) :
    Instrument.bornMass ((taggedAxis LB s2 hAB priorL).flatMap (fun l =>
      (taggedAxis RB (s2 + axisCount (LB.map WindowModel.physical))
        (historyAfter (s2 + axisCount (LB.map WindowModel.physical)) hAB l.2.history) priorR).flatMap
          (fun r => (terminal l.1 r.1).map (l.2.seq r.2).seq))) φ =
    (idealAxis LB (priorL.map hAB) (fun lhs => idealAxis RB tagB (terminal lhs))).bornMass φ := by
  rw [← selectedAxis_mass LB s2 hAB priorL (fun lhs => idealAxis RB tagB (terminal lhs)) φ
    (Ready.append_left LB RB φ hφ)]
  simp only [selectedAxis, flat_mass, prefixed_mass]
  apply congrArg List.sum
  apply List.map_congr_left
  intro l hl
  have h := selectedAxis_mass RB _ (historyAfter _ hAB l.2.history) priorR (terminal l.1) (l.2.kraus φ)
    (taggedAxis_ready_tail LB RB s2 hAB priorL l hl φ hφ)
  rw [hprior] at h
  simp only [selectedAxis, flat_mass, prefixed_mass] at h
  simp only [InstrumentBranch.seq, LinearMap.comp_apply]
  exact h

theorem mix_level_B (WB : WindowModel read) (LB RB : List (WindowModel read)) {s1 : Nat}
    (hA : Fin s1 → Bool)
    (priorL : List (Fin (s1 + axisCount [WB.physical])))
    (priorR : List (Fin (s1 + axisCount [WB.physical] + axisCount (LB.map WindowModel.physical))))
    (tagA : List Bool)
    (hpriorL : ∀ other : List Bool,
      priorL.map (historyAfter (s1 + axisCount [WB.physical]) hA other) = tagA)
    (hpriorR : ∀ b ∈ taggedAxis [WB] s1 hA List.nil, ∀ other : List Bool,
      priorR.map (historyAfter (s1 + axisCount [WB.physical] + axisCount (LB.map WindowModel.physical))
        (historyAfter (s1 + axisCount [WB.physical]) hA b.2.history) other) = b.1)
    (terminal : List Bool → List Bool → Instrument) (φ : State)
    (hφ : Ready (WB :: (LB ++ RB)) φ) :
    Instrument.bornMass ((taggedAxis [WB] s1 hA List.nil).flatMap (fun b =>
      (taggedAxis LB (s1 + axisCount [WB.physical])
        (historyAfter (s1 + axisCount [WB.physical]) hA b.2.history) priorL).flatMap (fun l =>
        (taggedAxis RB (s1 + axisCount [WB.physical] + axisCount (LB.map WindowModel.physical))
          (historyAfter (s1 + axisCount [WB.physical] + axisCount (LB.map WindowModel.physical))
            (historyAfter (s1 + axisCount [WB.physical]) hA b.2.history) l.2.history) priorR).flatMap (fun r =>
          (terminal l.1 r.1).map (b.2.seq (l.2.seq r.2)).seq)))) φ =
    (idealAxis [WB] List.nil (fun tagB =>
      idealAxis LB tagA (fun lhs => idealAxis RB tagB (terminal lhs)))).bornMass φ := by
  have hsel := selectedAxis_mass [WB] s1 hA List.nil
    (fun tagB => idealAxis LB tagA (fun lhs => idealAxis RB tagB (terminal lhs))) φ
    (Ready.append_left [WB] (LB ++ RB) φ hφ)
  simp only [List.map_nil] at hsel
  rw [← hsel]
  simp only [selectedAxis, flat_mass, prefixed_mass]
  apply congrArg List.sum
  apply List.map_congr_left
  intro b hb
  have h := mix_level_LR LB RB (historyAfter _ hA b.2.history) priorL priorR b.1 (hpriorR b hb)
    terminal (b.2.kraus φ) (taggedAxis_ready_tail [WB] (LB ++ RB) s1 hA List.nil b hb φ hφ)
  rw [hpriorL] at h
  simp only [flat_mass, prefixed_mass, InstrumentBranch.seq, LinearMap.comp_apply] at h ⊢
  exact h

/-- Exact physical-to-ideal selected-event mass of the four-segment mixed program. -/
theorem selectedMixed_mass (WA WB : WindowModel read) (LB RB : List (WindowModel read))
    (start : Nat) (history : Fin start → Bool)
    (terminal : List Bool → List Bool → Instrument) (ψ : State)
    (hψ : Ready (WA :: WB :: (LB ++ RB)) ψ) :
    (selectedMixed WA WB LB RB start history terminal).bornMass ψ =
      (idealMixed WA WB LB RB terminal).bornMass ψ := by
  have hsel := selectedAxis_mass [WA] start history List.nil
    (fun tagA => idealAxis [WB] List.nil (fun tagB =>
      idealAxis LB tagA (fun lhs => idealAxis RB tagB (terminal lhs)))) ψ
    (Ready.append_left [WA] (WB :: (LB ++ RB)) ψ hψ)
  simp only [List.map_nil] at hsel
  unfold idealMixed
  rw [← hsel]
  unfold selectedMixed taggedMixed
  simp only [List.flatMap_assoc, List.flatMap_map]
  unfold selectedAxis
  rw [flat_mass, flat_mass]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  rw [prefixed_mass]
  obtain ⟨arithA, bitsA, hlA, hlbA, hhA, htA⟩ := taggedAxis_single_data WA history List.nil a ha
  have h := mix_level_B WB LB RB (historyAfter (mixS1 WA.physical start) history a.2.history)
    (mixPriorL WA.physical WB.physical start)
    (mixPriorR WA.physical WB.physical (LB.map WindowModel.physical) start) a.1
    (by
      intro other
      have hm := mixPriorL_map WA.physical WB.physical start history arithA bitsA other hlA hlbA
      rw [hhA, htA]
      exact hm.trans (by simp))
    (by
      intro b hb other
      obtain ⟨arithB, bitsB, hlB, hlbB, hhB, htB⟩ :=
        taggedAxis_single_data WB (historyAfter (mixS1 WA.physical start) history a.2.history) List.nil b hb
      have hm := mixPriorR_map WA.physical WB.physical (LB.map WindowModel.physical) start
        (historyAfter (mixS1 WA.physical start) history a.2.history) arithB bitsB other hlB hlbB
      rw [hhB, htB]
      exact hm.trans (by simp))
    terminal (a.2.kraus ψ)
    (taggedAxis_ready_tail [WA] (WB :: (LB ++ RB)) start history List.nil a ha ψ hψ)
  simp only [flat_mass, prefixed_mass, InstrumentBranch.seq, LinearMap.comp_apply] at h ⊢
  exact h

end MixedMass


section MixedFilter
variable {n : Nat} {read : ConstantBit n → Bool}

/-- Physical branches of the four segments, forgetting the model structure. -/
def mixedData (WA WB : Window n) (LB RB : List (Window n)) (read : ConstantBit n → Bool)
    (start : Nat) (history : Fin start → Bool) : Instrument :=
  ((mixProgram WA WB LB RB start).instantiate read history).run

theorem selectedMixed_constant (WA WB : WindowModel read) (LB RB : List (WindowModel read))
    (start : Nat) (history : Fin start → Bool) (J : Instrument) :
    selectedMixed WA WB LB RB start history (fun _ _ => J) =
      (mixedData WA.physical WB.physical (LB.map WindowModel.physical) (RB.map WindowModel.physical)
        read start history).seq J := by
  unfold mixedData
  rw [mixData_tagged]
  simp only [selectedMixed, Instrument.seq, List.flatMap_map]

theorem taggedMixed_readWords (WA WB : WindowModel read) (LB RB : List (WindowModel read))
    (start : Nat) (history : Fin start → Bool)
    (t : (List Bool × List Bool) × InstrumentBranch)
    (ht : t ∈ taggedMixed WA WB LB RB start history) (after : List Bool) :
    ShorECDLP.Challenge.readWord (List.ofFn history ++ t.2.history ++ after)
      (axisPositions [WA.physical] start ++
        axisPositions (LB.map WindowModel.physical) (mixS2 WA.physical WB.physical start)) =
        some (fourierWordLSB t.1.1.reverse) ∧
    ShorECDLP.Challenge.readWord (List.ofFn history ++ t.2.history ++ after)
      (axisPositions [WB.physical] (mixS1 WA.physical start) ++
        axisPositions (RB.map WindowModel.physical)
          (mixS3 WA.physical WB.physical (LB.map WindowModel.physical) start)) =
        some (fourierWordLSB t.1.2.reverse) := by
  unfold taggedMixed at ht
  obtain ⟨a, ha, ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨b, hb, ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨l, hl, ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ht
  obtain ⟨arithA, bitsA, hlA, hlbA, hhA, htA⟩ := taggedAxis_single_data WA history List.nil a ha
  obtain ⟨arithB, bitsB, hlB, hlbB, hhB, htB⟩ :=
    taggedAxis_single_data WB (historyAfter (mixS1 WA.physical start) history a.2.history) List.nil b hb
  obtain ⟨bitsL, hTL, htL⟩ := taggedAxis_transcript LB _ _ _ l hl
  obtain ⟨bitsR, hTR, htR⟩ := taggedAxis_transcript RB _ _ _ r hr
  have hlenA := taggedAxis_history_length [WA] start history List.nil a ha
  have hlenB := taggedAxis_history_length [WB] _ _ List.nil b hb
  have hlenL := taggedAxis_history_length LB _ _ _ l hl
  have hpL := mixPriorL_map WA.physical WB.physical start history arithA bitsA b.2.history hlA hlbA
  have hpR := mixPriorR_map WA.physical WB.physical (LB.map WindowModel.physical) start
    (historyAfter (mixS1 WA.physical start) history a.2.history) arithB bitsB l.2.history hlB hlbB
  have e1 : l.1.reverse = bitsA ++ bitsL := by
    rw [htL, hhA, hpL]; simp
  have e2 : r.1.reverse = bitsB ++ bitsR := by
    rw [htR, hhB, hpR]; simp
  have hTA : Transcript ([WA.physical].map (fun w => (w.count, w.wires.length))) a.2.history
      (bitsA ++ List.nil) := by
    rw [hhA]; exact Transcript.cons _ _ _ _ _ _ _ hlA hlbA Transcript.nil
  have hTB : Transcript ([WB.physical].map (fun w => (w.count, w.wires.length))) b.2.history
      (bitsB ++ List.nil) := by
    rw [hhB]; exact Transcript.cons _ _ _ _ _ _ _ hlB hlbB Transcript.nil
  have mA := hTA.actual_bits (List.ofFn history) (b.2.history ++ (l.2.history ++ r.2.history) ++ after)
  have mB := hTB.actual_bits (List.ofFn history ++ a.2.history) (l.2.history ++ r.2.history ++ after)
  have mL := hTL.actual_bits (List.ofFn history ++ a.2.history ++ b.2.history) (r.2.history ++ after)
  have mR := hTR.actual_bits (List.ofFn history ++ a.2.history ++ b.2.history ++ l.2.history) after
  simp only [List.length_append, List.length_ofFn, hlenA, hlenB, hlenL] at mA mB mL mR
  simp only [List.append_assoc] at mA mB mL mR
  simp only [InstrumentBranch.seq, List.append_assoc]
  have hA2 := mA
  have hB2 := mB
  have hL2 := mL
  have hR2 := mR
  simp only [List.append_nil, List.map_cons, List.map_nil] at hA2 hB2 hL2 hR2
  simp only [axisPositions, List.map_map, Function.comp_def, List.map_cons, List.map_nil] at hL2 hR2 ⊢
  constructor
  · rw [e1]
    apply readWord_of_actual_bits
    rw [List.map_append, List.map_append]
    exact congrArg₂ (· ++ ·) hA2 hL2
  · rw [e2]
    apply readWord_of_actual_bits
    rw [List.map_append, List.map_append]
    exact congrArg₂ (· ++ ·) hB2 hR2

/-- Filtering the real sparse transcript is exactly selecting the two Fourier words
(left = left head then left bodies, right = right head then right bodies). -/
theorem selectedMixed_fixed_filter (WA WB : WindowModel read) (LB RB : List (WindowModel read))
    (J : Instrument) (accept : Nat → Nat → Bool) :
    selectedMixed WA WB LB RB 0 Fin.elim0 (fun lhs rhs =>
      if accept (fourierWordLSB lhs.reverse) (fourierWordLSB rhs.reverse) then J else List.nil) =
      ((mixedData WA.physical WB.physical (LB.map WindowModel.physical) (RB.map WindowModel.physical)
        read 0 Fin.elim0).seq J).filter (fun b =>
        pairAccept
          (axisPositions [WA.physical] 0 ++
            axisPositions (LB.map WindowModel.physical) (mixS2 WA.physical WB.physical 0))
          (axisPositions [WB.physical] (mixS1 WA.physical 0) ++
            axisPositions (RB.map WindowModel.physical)
              (mixS3 WA.physical WB.physical (LB.map WindowModel.physical) 0)) accept b.history) := by
  rw [← selectedMixed_constant WA WB LB RB 0 Fin.elim0 J]
  rw [selectedMixed, selectedMixed, List.filter_flatMap]
  apply List.flatMap_congr
  intro a ha
  have hp (b : InstrumentBranch) :
      pairAccept
        (axisPositions [WA.physical] 0 ++
          axisPositions (LB.map WindowModel.physical) (mixS2 WA.physical WB.physical 0))
        (axisPositions [WB.physical] (mixS1 WA.physical 0) ++
          axisPositions (RB.map WindowModel.physical)
            (mixS3 WA.physical WB.physical (LB.map WindowModel.physical) 0))
        accept (a.2.seq b).history =
        accept (fourierWordLSB a.1.1.reverse) (fourierWordLSB a.1.2.reverse) := by
    have h := taggedMixed_readWords WA WB LB RB 0 Fin.elim0 a ha b.history
    simp only [List.ofFn_zero, List.nil_append] at h
    simp only [pairAccept, InstrumentBranch.seq, h.1, h.2, Option.bind_some,
      Option.map_some, Option.getD_some]
  rw [List.filter_map]
  simp only [Function.comp_def, hp]
  split <;> simp_all

/-- Physical arithmetic records have no effect on the selected joint event (mixed first load). -/
theorem physicalMixed_event_mass (Q : Point) (root : BasisState) (ψ : State)
    (WA WB : WindowModel read) (LB RB : List (WindowModel read)) (dwL dwR : DigitWindow)
    (hwA : WA.physical.wires.length = dwL.width) (hwB : WB.physical.wires.length = dwR.width)
    (hfirst : ∀ bA ∈ fourierOutcomes dwL.width, ∀ bB ∈ fourierOutcomes dwR.width,
      WB.step List.nil bB (WA.step List.nil bA ψ) = jointClosedForm dwL dwR bA bB root)
    (hpoint : ∀ w ∈ LB ++ RB, PointRule root w)
    (hheadL : ∀ v, dwL.point v + dwL.bias = (v * 2 ^ precision LB) • G)
    (hheadR : ∀ v, dwR.point v + dwR.bias = (v * 2 ^ precision RB) • Q)
    (hLB : ModelWeights G LB) (hRB : ModelWeights Q RB)
    (hbias : dwL.bias + (LB.map WindowModel.bias).sum + (dwR.bias + (RB.map WindowModel.bias).sum) = 0)
    (hready : Ready (WA :: WB :: (LB ++ RB)) ψ)
    (start : Nat) (history : Fin start → Bool)
    (J : Instrument) (hJ : ∀ φ, J.bornMass φ = normSq φ) (accept : Nat → Nat → Bool) :
    (selectedMixed WA WB LB RB start history (fun lhs rhs =>
      if accept (fourierWordLSB lhs.reverse) (fourierWordLSB rhs.reverse) then J else List.nil)).bornMass ψ =
      idealEventMass Q root (dwL.width + precision LB) (dwR.width + precision RB) accept := by
  rw [selectedMixed_mass WA WB LB RB start history _ ψ hready]
  exact idealMixed_event_mass Q root ψ WA WB LB RB dwL dwR hwA hwB hfirst hpoint hheadL hheadR
    hLB hRB hbias J hJ accept

end MixedFilter


section HeadModels
variable {n : Nat}

/-- Extra Hadamards inside a window program: the ideal map pre-composes them. -/
theorem coherent_prepare {start finish : Nat} (ws : List Wire) (p : Straight n start finish)
    (read : ConstantBit n → Bool) (history : Fin start → Bool)
    (ideal : State →ₗ[ℂ] State) (V : BasisState → Prop)
    (h : CoherentlyImplementsOn (p.instantiate read history) ideal V)
    (hV : ∀ s, V s → SupportedOn V (Quantum.run (ws.map Gate.H) (ket s))) :
    CoherentlyImplementsOn ((prepareOuterBank ws p).instantiate read history)
      (ideal.comp (Quantum.run (ws.map Gate.H))) V := by
  obtain ⟨cs, halign, hmass⟩ := h
  refine ⟨cs, ?_, hmass⟩
  rw [prepare_run, List.forall₂_map_left_iff]
  refine halign.imp (fun b c hb s hs => ?_)
  change b.kraus (Quantum.run (ws.map Gate.H) (ket s)) =
    c • ideal (Quantum.run (ws.map Gate.H) (ket s))
  exact hb.on_supported (hV s hs)

/-- A program of Hadamards only implements them, on every input. -/
theorem coherent_prepare_done {start : Nat} (ws : List Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    CoherentlyImplementsOn
      ((prepareOuterBank ws (Straight.done : Straight n start start)).instantiate read history)
      (Quantum.run (ws.map Gate.H)) (fun _ => True) := by
  refine ⟨[1], ?_, by simp⟩
  rw [prepare_run]
  simp only [Straight.instantiate, AdaptiveCircuit.run, List.map_cons, List.map_nil]
  exact List.Forall₂.cons (fun s _ => by simp [InstrumentBranch.seq]) List.Forall₂.nil

end HeadModels


section MixedSlots
variable {n : Nat}

theorem mixHead_slots (WA : Window n) (start : Nat) :
    (mixHead WA start).gateSlots = (axis [WA] start List.nil).gateSlots := rfl

theorem mixTail_slots (WA WB : Window n) (LB RB : List (Window n)) (start : Nat) :
    (mixTail WA WB LB RB start).gateSlots =
      (axis [WB] (mixS1 WA start) List.nil).gateSlots +
        ((axis LB (mixS2 WA WB start) (mixPriorL WA WB start)).gateSlots +
          (axis RB (mixS3 WA WB LB start) (mixPriorR WA WB LB start)).gateSlots) := by
  unfold mixTail
  simp only [Straight.gateSlots_append]

end MixedSlots

end
end ShorECDLP.Entrant.Single.Distribution
