import ShorECDLP.Submission.«2607_13816».Arithmetic.ZeroAllowedResources
import ShorECDLP.Submission.«2607_13816».Challenge.RegisterEquality
import ShorECDLP.Submission.«2607_13816».Challenge.WindowBody

/-! Adaptive zero guards, based on VerifiedQC/ShorECDLP, streaming-dev, PR #551,
Apache-2.0; see LICENSE and NOTICE. -/
set_option maxRecDepth 4096

namespace ShorECDLP.Entrant.ZeroAdaptive
open ShorECDLP Classical Quantum Paper2607_13816 Paper2607_13816.ChallengeMigration

def reg : List Wire := 263 :: List.range' 264 255
def scratch : List Wire := List.range' 7 254
def cx : Circuit := [.CX 837 263]
theorem layout : EqConstLayout reg 837 scratch := by
  unfold reg scratch EqConstLayout McxVChainLayout
  decide +kernel
private theorem clean_initial (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) : Clean scratch s := by
  intro w hw
  apply hs.1 w
  simp [scratch] at hw ⊢
  omega
private theorem cx_clean (s : BasisState) (hs : Clean scratch s) : Clean scratch (Classical.run cx s) := by
  intro w hw
  have hn : w ≠ 263 := by simp [scratch] at hw; dsimp only [Wire] at *; omega
  simpa [cx, Classical.run, Classical.applyGate, upd, hn] using hs w hw

def prepare : AdaptiveCircuit := (computeEqConstAdaptive reg 0 837 scratch).seq (.unitary cx .done)
def restore : AdaptiveCircuit := (AdaptiveCircuit.unitary cx .done).seq (computeEqConstAdaptive reg 0 837 scratch)

theorem prepare_coherent : CoherentlyImplementsOn prepare (Quantum.run fig15ZeroPrepare) (Clean scratch) := by
  have h := coherentSequenceCircuits
    (computeEqConstAdaptive_coherent reg 0 837 scratch layout)
    (CoherentlyImplementsOn.unitary cx (fun _ => True))
    (computeEqConst_HPFree _ _ _ _) (fun _ _ => trivial)
  simpa only [prepare, fig15ZeroPrepare, nonzeroInputPrepare, reg, scratch, cx] using h

theorem restore_coherent : CoherentlyImplementsOn restore (Quantum.run fig15ZeroRestore) (Clean scratch) := by
  have h := coherentSequenceCircuits
    (CoherentlyImplementsOn.unitary cx (Clean scratch))
    (computeEqConstAdaptive_coherent reg 0 837 scratch layout)
    (by simp [cx, HPFree]) cx_clean
  simpa only [restore, fig15ZeroRestore, nonzeroInputRestore, reg, scratch, cx, AdaptiveCircuit.seq] using h


private theorem restore_hp : HPFree fig15ZeroRestore := by
  rw [fig15ZeroRestore, nonzeroInputRestore, hpFree_append]
  exact ⟨by simp [HPFree], computeEqConst_HPFree _ _ _ _⟩

def division : AdaptiveCircuit := (prepare.seq secp256k1InPlaceDivision).seq restore
def multiplication : AdaptiveCircuit := (prepare.seq secp256k1InPlaceMultiplication).seq restore

private theorem output_clean (f : BasisState → BasisState) (s : BasisState)
    (hs : Secp256k1ZeroAllowedInputValid s)
    (frame : ∀ w, w ∉ List.range' 580 256 → f (fig15ZeroPrepareState s) w = fig15ZeroPrepareState s w) :
    Clean scratch (f (fig15ZeroPrepareState s)) := by
  intro w hw
  have hn : w ∉ List.range' 580 256 := by simp [scratch] at hw ⊢; omega
  rw [frame w hn]
  apply (fig15ZeroPrepareState_ready s hs).1.1 w
  simp [scratch] at hw ⊢
  omega

private theorem wrapper_coherent (program : AdaptiveCircuit) (ideal : BasisState → BasisState)
    (h : CoherentlyImplementsOn program (Finsupp.lmapDomain ℂ ℂ ideal) Secp256k1InPlaceInputValid)
    (hout : ∀ s, Secp256k1ZeroAllowedInputValid s → Clean scratch (ideal (fig15ZeroPrepareState s))) :
    CoherentlyImplementsOn ((prepare.seq program).seq restore)
      (Finsupp.lmapDomain ℂ ℂ (fun s => Classical.run fig15ZeroRestore (ideal (fig15ZeroPrepareState s))))
      Secp256k1ZeroAllowedInputValid := by
  have hp : CoherentlyImplementsOn prepare (Quantum.run fig15ZeroPrepare) Secp256k1ZeroAllowedInputValid := by
    obtain ⟨cs, hc, hm⟩ := prepare_coherent
    exact ⟨cs, hc.imp (fun _ _ hb s hs => hb s (clean_initial s hs)), hm⟩
  have first := hp.seq h (by
    intro s hs
    rw [Quantum.run_ket_agrees_classical _ _ (by
      rw [fig15ZeroPrepare, nonzeroInputPrepare, hpFree_append]
      exact ⟨computeEqConst_HPFree _ _ _ _, by simp [HPFree]⟩), fig15ZeroPrepare_run s hs]
    exact supportedOn_ket _ _ (fig15ZeroPrepareState_ready s hs))
  have all := first.seq restore_coherent (by
    intro s hs
    simp only [LinearMap.comp_apply]
    rw [Quantum.run_ket_agrees_classical _ _ (by
      rw [fig15ZeroPrepare, nonzeroInputPrepare, hpFree_append]
      exact ⟨computeEqConst_HPFree _ _ _ _, by simp [HPFree]⟩), fig15ZeroPrepare_run s hs]
    simpa [ket] using supportedOn_ket _ _ (hout s hs))
  apply all.congrIdeal
  intro s hs
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    Quantum.run_ket_agrees_classical _ _ (by
      rw [fig15ZeroPrepare, nonzeroInputPrepare, hpFree_append]
      exact ⟨computeEqConst_HPFree _ _ _ _, by simp [HPFree]⟩), fig15ZeroPrepare_run s hs]
  have hl (f : BasisState → BasisState) (st : BasisState) :
      (Finsupp.lmapDomain ℂ ℂ f) (ket st) = ket (f st) := by simp [ket]
  rw [hl, hl]
  exact Quantum.run_ket_agrees_classical _ _ restore_hp

theorem division_coherent : CoherentlyImplementsOn division
    (Finsupp.lmapDomain ℂ ℂ zeroAllowedDivisionOutputState) Secp256k1ZeroAllowedInputValid := by
  apply wrapper_coherent _ _ secp256k1InPlaceDivision_coherent
  intro s hs
  apply output_clean _ s hs
  intro w hw
  rw [fig15DivisionOutputState_eq _ (fig15ZeroPrepareState_ready s hs)]
  simp [hw]

theorem multiplication_coherent : CoherentlyImplementsOn multiplication
    (Finsupp.lmapDomain ℂ ℂ zeroAllowedMultiplicationOutputState) Secp256k1ZeroAllowedInputValid := by
  apply wrapper_coherent _ _ secp256k1InPlaceMultiplication_coherent
  intro s hs
  apply output_clean _ s hs
  intro w hw
  rw [fig15MultiplicationOutputState_eq _ (fig15ZeroPrepareState_ready s hs)]
  simp [hw]


theorem division_counts : division.tCount = 246064973 ∧ division.measurementCount = 14707815 := by
  simp [division, prepare, restore, adaptive_tCount_seq, modularMeasurements_seq,
    AdaptiveCircuit.tCount, AdaptiveCircuit.measurementCount, tCost, reg, scratch, cx,
    computeEqConstAdaptive_tCount, computeEqConstAdaptive_measurementCount,
    mcxVChainAdaptiveToffoliCost, mcxVChainMeasurementCost,
    secp256k1InPlaceDivision_T, secp256k1InPlaceDivision_measurements]

theorem multiplication_counts : multiplication.tCount = 246064973 ∧ multiplication.measurementCount = 14707815 := by
  simp [multiplication, prepare, restore, adaptive_tCount_seq, modularMeasurements_seq,
    AdaptiveCircuit.tCount, AdaptiveCircuit.measurementCount, tCost, reg, scratch, cx,
    computeEqConstAdaptive_tCount, computeEqConstAdaptive_measurementCount,
    mcxVChainAdaptiveToffoliCost, mcxVChainMeasurementCost,
    secp256k1InPlaceMultiplication_T, secp256k1InPlaceMultiplication_measurements]

noncomputable section
/-- Five sequential field-word queries, each loaded and cleared around its modular addition. -/
def coordinateSource (x y : Nat → Nat) : AdaptiveCircuit :=
  ((((((((fig14LookupX (fun a => (ShorECDLP.p-x a)%ShorECDLP.p)).seq
    (signedPointLookupY (fun a => (ShorECDLP.p-y a)%ShorECDLP.p))).seq
    division).seq fig14SquareSubtract).seq
    (fig14LookupX (fun a => (3*x a)%ShorECDLP.p))).seq
    multiplication).seq fig14Negate).seq
    (fig14LookupX (fun a => x a%ShorECDLP.p))).seq
    (signedPointLookupY (fun a => (ShorECDLP.p-y a)%ShorECDLP.p))

private theorem lookup_coherent_seq (a b : AdaptiveCircuit) (f g : BasisState → BasisState)
    (ha : CoherentlyImplementsOn a (Finsupp.lmapDomain ℂ ℂ f) PointLookupValid)
    (hb : CoherentlyImplementsOn b (Finsupp.lmapDomain ℂ ℂ g) PointLookupValid)
    (hf : ∀ s, PointLookupValid s → PointLookupValid (f s)) :
    CoherentlyImplementsOn (a.seq b) (Finsupp.lmapDomain ℂ ℂ (fun s => g (f s))) PointLookupValid := by
  have h := ha.seq hb (by
    intro s hs
    simpa [ket] using supportedOn_ket PointLookupValid (f s) (hf s hs))
  apply h.congrIdeal
  intro s hs
  simp [LinearMap.comp_apply,ket]

private theorem lookup_restrict {program : AdaptiveCircuit} {ideal : Quantum.State →ₗ[ℂ] Quantum.State}
    (h : CoherentlyImplementsOn program ideal Secp256k1ZeroAllowedInputValid) :
    CoherentlyImplementsOn program ideal PointLookupValid := by
  obtain ⟨cs,ha,hm⟩ := h
  exact ⟨cs,ha.imp (fun b c hb s hs => hb s hs.1),hm⟩

private theorem lookup_division_ready (s : BasisState) (hs : PointLookupValid s) :
    PointLookupValid (zeroAllowedDivisionOutputState s) := by
  refine ⟨fig14Division_ready s hs.1,?_⟩
  rw [zeroAllowedDivisionOutputState_frame s hs.1]
  simpa using hs.2
private theorem lookup_multiplication_ready (s : BasisState) (hs : PointLookupValid s) :
    PointLookupValid (zeroAllowedMultiplicationOutputState s) := by
  refine ⟨fig14Multiplication_ready s hs.1,?_⟩
  rw [zeroAllowedMultiplicationOutputState_frame s hs.1]
  simpa using hs.2
private theorem lookup_square_ready (s : BasisState) (hs : PointLookupValid s) :
    PointLookupValid (fig14SquareSubtractState s) :=
  ⟨fig14SquareSubtractState_ready s hs.1,
    ((fig14SquareSubtractState_correct s hs.1).2 836 (by decide +kernel)).trans hs.2⟩
private theorem lookup_negate_ready (s : BasisState) (hs : PointLookupValid s) :
    PointLookupValid (fig14NegateState s) :=
  ⟨fig14NegateState_ready s hs.1,
    ((fig14NegateState_correct s hs.1).2 836 (by decide +kernel)).trans hs.2⟩

theorem coordinateSource_coherent (x y : Nat → Nat) :
    CoherentlyImplementsOn (coordinateSource x y)
      (Finsupp.lmapDomain ℂ ℂ (signedLookupCoordinateState x y)) PointLookupValid := by
  have hk (k : Nat) : k%ShorECDLP.p<ShorECDLP.p := Nat.mod_lt _ ShorECDLP.Secp256k1.p_prime.pos
  let p1 := fig14LookupX (fun a => (ShorECDLP.p-x a)%ShorECDLP.p)
  let f1 := fig14LookupXState (fun a => (ShorECDLP.p-x a)%ShorECDLP.p)
  have h1 : CoherentlyImplementsOn p1 (Finsupp.lmapDomain ℂ ℂ f1) PointLookupValid := fig14LookupX_coherent _ (fun _ => hk _)
  have r1 : ∀ s, PointLookupValid s → PointLookupValid (f1 s) := fig14LookupXState_ready _ (fun _ => hk _)
  let p2 := signedPointLookupY (fun a => (ShorECDLP.p-y a)%ShorECDLP.p)
  let f2 := signedPointLookupYState (fun a => (ShorECDLP.p-y a)%ShorECDLP.p)
  have h2 : CoherentlyImplementsOn p2 (Finsupp.lmapDomain ℂ ℂ f2) PointLookupValid := signedPointLookupY_coherent _ (fun _ => hk _)
  have r2 : ∀ s, PointLookupValid s → PointLookupValid (f2 s) := signedPointLookupYState_ready _ (fun _ => hk _)
  let p3 := division
  let f3 := zeroAllowedDivisionOutputState
  have h3 : CoherentlyImplementsOn p3 (Finsupp.lmapDomain ℂ ℂ f3) PointLookupValid := lookup_restrict division_coherent
  have r3 : ∀ s, PointLookupValid s → PointLookupValid (f3 s) := lookup_division_ready
  let p4 := fig14SquareSubtract
  let f4 := fig14SquareSubtractState
  have h4 : CoherentlyImplementsOn p4 (Finsupp.lmapDomain ℂ ℂ f4) PointLookupValid := lookup_restrict fig14SquareSubtract_coherent
  have r4 : ∀ s, PointLookupValid s → PointLookupValid (f4 s) := lookup_square_ready
  let p5 := fig14LookupX (fun a => (3*x a)%ShorECDLP.p)
  let f5 := fig14LookupXState (fun a => (3*x a)%ShorECDLP.p)
  have h5 : CoherentlyImplementsOn p5 (Finsupp.lmapDomain ℂ ℂ f5) PointLookupValid := fig14LookupX_coherent _ (fun _ => hk _)
  have r5 : ∀ s, PointLookupValid s → PointLookupValid (f5 s) := fig14LookupXState_ready _ (fun _ => hk _)
  let p6 := multiplication
  let f6 := zeroAllowedMultiplicationOutputState
  have h6 : CoherentlyImplementsOn p6 (Finsupp.lmapDomain ℂ ℂ f6) PointLookupValid := lookup_restrict multiplication_coherent
  have r6 : ∀ s, PointLookupValid s → PointLookupValid (f6 s) := lookup_multiplication_ready
  let p7 := fig14Negate
  let f7 := fig14NegateState
  have h7 : CoherentlyImplementsOn p7 (Finsupp.lmapDomain ℂ ℂ f7) PointLookupValid := lookup_restrict fig14Negate_coherent
  have r7 : ∀ s, PointLookupValid s → PointLookupValid (f7 s) := lookup_negate_ready
  let p8 := fig14LookupX (fun a => x a%ShorECDLP.p)
  let f8 := fig14LookupXState (fun a => x a%ShorECDLP.p)
  have h8 : CoherentlyImplementsOn p8 (Finsupp.lmapDomain ℂ ℂ f8) PointLookupValid := fig14LookupX_coherent _ (fun _ => hk _)
  have r8 : ∀ s, PointLookupValid s → PointLookupValid (f8 s) := fig14LookupXState_ready _ (fun _ => hk _)
  let p9 := signedPointLookupY (fun a => (ShorECDLP.p-y a)%ShorECDLP.p)
  let f9 := signedPointLookupYState (fun a => (ShorECDLP.p-y a)%ShorECDLP.p)
  have h9 : CoherentlyImplementsOn p9 (Finsupp.lmapDomain ℂ ℂ f9) PointLookupValid := signedPointLookupY_coherent _ (fun _ => hk _)
  have c2 := lookup_coherent_seq _ _ _ _ h1 h2 r1
  have v2 := fun s hs => r2 _ (r1 s hs)
  have c3 := lookup_coherent_seq _ _ _ _ c2 h3 v2
  have v3 := fun s hs => r3 _ (v2 s hs)
  have c4 := lookup_coherent_seq _ _ _ _ c3 h4 v3
  have v4 := fun s hs => r4 _ (v3 s hs)
  have c5 := lookup_coherent_seq _ _ _ _ c4 h5 v4
  have v5 := fun s hs => r5 _ (v4 s hs)
  have c6 := lookup_coherent_seq _ _ _ _ c5 h6 v5
  have v6 := fun s hs => r6 _ (v5 s hs)
  have c7 := lookup_coherent_seq _ _ _ _ c6 h7 v6
  have v7 := fun s hs => r7 _ (v6 s hs)
  have c8 := lookup_coherent_seq _ _ _ _ c7 h8 v7
  have v8 := fun s hs => r8 _ (v7 s hs)
  have c9 := lookup_coherent_seq _ _ _ _ c8 h9 v8
  exact c9




open ShorECDLP.Challenge ShorECDLP.Secp256k1
attribute [local irreducible] divisionProgram multiplicationProgram equalityProgram
  secp256k1InPlaceDivision secp256k1InPlaceMultiplication

def zDivisionProgram (n start : Nat) : (count : Nat) × Straight n start (start+count) :=
  let a := equalityProgram n start reg 0 837 scratch
  let b := divisionProgram n (start+a.1)
  appendCompiled a (prependCompiled cx (appendCompiled b
    (prependCompiled cx (equalityProgram n (start+a.1+b.1) reg 0 837 scratch))))

def zMultiplicationProgram (n start : Nat) : (count : Nat) × Straight n start (start+count) :=
  let a := equalityProgram n start reg 0 837 scratch
  let b := multiplicationProgram n (start+a.1)
  appendCompiled a (prependCompiled cx (appendCompiled b
    (prependCompiled cx (equalityProgram n (start+a.1+b.1) reg 0 837 scratch))))

theorem zDivisionProgram_run (n start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (zDivisionProgram n start) read history = division.run := by
  unfold zDivisionProgram division prepare restore
  dsimp only
  rw [adaptive_seq_assoc, adaptive_seq_assoc]
  apply appendCompiled_run_eq _ _ read history (computeEqConstAdaptive reg 0 837 scratch) (AdaptiveCircuit.unitary cx (secp256k1InPlaceDivision.seq (AdaptiveCircuit.unitary cx (computeEqConstAdaptive reg 0 837 scratch))))
  · exact equalityProgram_run _ _ _ _ _ _ _ _
  · intro h
    apply prependCompiled_run_eq
    apply appendCompiled_run_eq _ _ read h secp256k1InPlaceDivision (AdaptiveCircuit.unitary cx (computeEqConstAdaptive reg 0 837 scratch))
    · exact divisionProgram_run _ _ _ _
    · intro h
      apply prependCompiled_run_eq
      exact equalityProgram_run _ _ _ _ _ _ _ _

theorem zMultiplicationProgram_run (n start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (zMultiplicationProgram n start) read history = multiplication.run := by
  unfold zMultiplicationProgram multiplication prepare restore
  dsimp only
  rw [adaptive_seq_assoc, adaptive_seq_assoc]
  apply appendCompiled_run_eq _ _ read history (computeEqConstAdaptive reg 0 837 scratch) (AdaptiveCircuit.unitary cx (secp256k1InPlaceMultiplication.seq (AdaptiveCircuit.unitary cx (computeEqConstAdaptive reg 0 837 scratch))))
  · exact equalityProgram_run _ _ _ _ _ _ _ _
  · intro h
    apply prependCompiled_run_eq
    apply appendCompiled_run_eq _ _ read h secp256k1InPlaceMultiplication (AdaptiveCircuit.unitary cx (computeEqConstAdaptive reg 0 837 scratch))
    · exact multiplicationProgram_run _ _ _ _
    · intro h
      apply prependCompiled_run_eq
      exact equalityProgram_run _ _ _ _ _ _ _ _

theorem zDivisionProgram_tCount (n start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (zDivisionProgram n start) read history = division.tCount := by
  unfold zDivisionProgram division prepare restore
  dsimp only
  rw [adaptive_seq_assoc, adaptive_seq_assoc]
  apply appendCompiled_tCount_eq _ _ read history (computeEqConstAdaptive reg 0 837 scratch) (AdaptiveCircuit.unitary cx (secp256k1InPlaceDivision.seq (AdaptiveCircuit.unitary cx (computeEqConstAdaptive reg 0 837 scratch))))
  · exact equalityProgram_tCount _ _ _ _ _ _ _ _
  · intro h
    apply prependCompiled_tCount_eq
    apply appendCompiled_tCount_eq _ _ read h secp256k1InPlaceDivision (AdaptiveCircuit.unitary cx (computeEqConstAdaptive reg 0 837 scratch))
    · exact divisionProgram_tCount _ _ _ _
    · intro h
      apply prependCompiled_tCount_eq
      exact equalityProgram_tCount _ _ _ _ _ _ _ _

theorem zMultiplicationProgram_tCount (n start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (zMultiplicationProgram n start) read history = multiplication.tCount := by
  unfold zMultiplicationProgram multiplication prepare restore
  dsimp only
  rw [adaptive_seq_assoc, adaptive_seq_assoc]
  apply appendCompiled_tCount_eq _ _ read history (computeEqConstAdaptive reg 0 837 scratch) (AdaptiveCircuit.unitary cx (secp256k1InPlaceMultiplication.seq (AdaptiveCircuit.unitary cx (computeEqConstAdaptive reg 0 837 scratch))))
  · exact equalityProgram_tCount _ _ _ _ _ _ _ _
  · intro h
    apply prependCompiled_tCount_eq
    apply appendCompiled_tCount_eq _ _ read h secp256k1InPlaceMultiplication (AdaptiveCircuit.unitary cx (computeEqConstAdaptive reg 0 837 scratch))
    · exact multiplicationProgram_tCount _ _ _ _
    · intro h
      apply prependCompiled_tCount_eq
      exact equalityProgram_tCount _ _ _ _ _ _ _ _
def adaptiveCoordinateSources (Q : Point) (w : OddWindow) : List AdaptiveCircuit :=
  [fig14LookupX (fun l => baseFieldValue (windowPoint Q w l) .negX),
   signedPointLookupY (fun l => baseFieldValue (windowPoint Q w l) .negY),
   division, fig14SquareSubtract,
   fig14LookupX (fun l => baseFieldValue (windowPoint Q w l) .tripleX),
   multiplication, fig14Negate,
   fig14LookupX (fun l => baseFieldValue (windowPoint Q w l) .x),
   signedPointLookupY (fun l => baseFieldValue (windowPoint Q w l) .negY)]

theorem adaptiveCoordinateSources_eq (Q : Point) (w : OddWindow) :
    sequenceCircuit (adaptiveCoordinateSources Q w) =
      coordinateSource (fun l => fieldValue (windowPoint Q w l) .x)
        (fun l => fieldValue (windowPoint Q w l) .y) := by
  have hx (P : Point) : baseFieldValue P .x = fieldValue P .x := rfl
  have hn (P : Point) : baseFieldValue P .negX = fieldValue P .negX := rfl
  have hy (P : Point) : baseFieldValue P .negY = fieldValue P .negY := rfl
  have ht (P : Point) : baseFieldValue P .tripleX = fieldValue P .tripleX := rfl
  simp only [adaptiveCoordinateSources, hx, hn, hy, ht, sequenceCircuit, coordinateSource,
    adaptive_seq_assoc, adaptive_seq_done, field_negX, field_negY, field_tripleX, field_x_mod]

def adaptiveCoordinateSegments : List (FixedSegment 32768) :=
  [fieldLookupAddProgram .negX (List.range' 263 256), signedFieldProgram .negY,
   zDivisionProgram 32768, pointSquareProgram 32768,
   fieldLookupAddProgram .tripleX (List.range' 263 256), zMultiplicationProgram 32768,
   xNegateProgram 32768, fieldLookupAddProgram .x (List.range' 263 256), signedFieldProgram .negY]

def adaptiveCoordinateProgram (start : Nat) : (count : Nat) × Straight 32768 start (start+count) :=
  sequenceProgram 32768 adaptiveCoordinateSegments start

theorem adaptiveCoordinateProgram_run (w : OddWindow) (start : Nat) (Q : Point) (hQ : order • Q = 0)
    (history : Fin start → Bool) :
    compiledRun (adaptiveCoordinateProgram start) (readConstant (oddWindowCoefficients w) Q) history =
      (coordinateSource (fun l => fieldValue (windowPoint Q w l) .x)
        (fun l => fieldValue (windowPoint Q w l) .y)).run := by
  unfold adaptiveCoordinateProgram
  rw [← adaptiveCoordinateSources_eq]
  apply sequenceProgram_run
  unfold adaptiveCoordinateSegments adaptiveCoordinateSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))))))
  · intro cursor h
    exact fig14LookupX_compiled w .negX cursor Q hQ h
  · intro cursor h
    exact signedFieldProgram_run w .negY cursor Q hQ h
  · intro cursor h
    exact zDivisionProgram_run 32768 cursor _ h
  · intro cursor h
    exact pointSquareProgram_run 32768 cursor _ h
  · intro cursor h
    exact fig14LookupX_compiled w .tripleX cursor Q hQ h
  · intro cursor h
    exact zMultiplicationProgram_run 32768 cursor _ h
  · intro cursor h
    exact xNegateProgram_run 32768 cursor _ h
  · intro cursor h
    exact fig14LookupX_compiled w .x cursor Q hQ h
  · intro cursor h
    exact signedFieldProgram_run w .negY cursor Q hQ h

theorem adaptiveCoordinateProgram_tCount (w : OddWindow) (start : Nat) (Q : Point) (hQ : order • Q = 0)
    (history : Fin start → Bool) :
    compiledTCount (adaptiveCoordinateProgram start) (readConstant (oddWindowCoefficients w) Q) history =
      (coordinateSource (fun l => fieldValue (windowPoint Q w l) .x)
        (fun l => fieldValue (windowPoint Q w l) .y)).tCount := by
  unfold adaptiveCoordinateProgram
  rw [← adaptiveCoordinateSources_eq]
  apply sequenceProgram_tCount
  unfold adaptiveCoordinateSegments adaptiveCoordinateSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))))))
  · intro cursor h
    exact fieldLookupAddProgram_tCount_source w .negX _ cursor Q hQ (by simp) h
  · intro cursor h
    exact signedFieldProgram_tCount w .negY cursor Q hQ h
  · intro cursor h
    exact zDivisionProgram_tCount 32768 cursor _ h
  · intro cursor h
    exact pointSquareProgram_tCount 32768 cursor _ h
  · intro cursor h
    exact fieldLookupAddProgram_tCount_source w .tripleX _ cursor Q hQ (by simp) h
  · intro cursor h
    exact zMultiplicationProgram_tCount 32768 cursor _ h
  · intro cursor h
    exact xNegateProgram_tCount 32768 cursor _ h
  · intro cursor h
    exact fieldLookupAddProgram_tCount_source w .x _ cursor Q hQ (by simp) h
  · intro cursor h
    exact signedFieldProgram_tCount w .negY cursor Q hQ h


def sharedAdaptiveCoordinateProgram (w : OddWindow) (start : Nat) :
    (count : Nat) × Straight 983040 start (start+count) :=
  reindexCompiled (windowIndex w) (adaptiveCoordinateProgram start)

theorem sharedAdaptiveCoordinateProgram_run (w : OddWindow) (start : Nat) (Q : Point)
    (hQ : order • Q = 0) (history : Fin start → Bool) :
    compiledRun (sharedAdaptiveCoordinateProgram w start) (readConstant coefficientAt Q) history =
      (coordinateSource (fun l => fieldValue (windowPoint Q w l) .x)
        (fun l => fieldValue (windowPoint Q w l) .y)).run := by
  unfold sharedAdaptiveCoordinateProgram reindexCompiled compiledRun
  rw [reindexStraight_instantiate, readConstant_reindex _ _ _ Q (coefficientAt_window w)]
  exact adaptiveCoordinateProgram_run w start Q hQ history

theorem sharedAdaptiveCoordinateProgram_tCount (w : OddWindow) (start : Nat) (Q : Point)
    (hQ : order • Q = 0) (history : Fin start → Bool) :
    compiledTCount (sharedAdaptiveCoordinateProgram w start) (readConstant coefficientAt Q) history =
      (coordinateSource (fun l => fieldValue (windowPoint Q w l) .x)
        (fun l => fieldValue (windowPoint Q w l) .y)).tCount := by
  unfold sharedAdaptiveCoordinateProgram reindexCompiled compiledTCount
  rw [reindexStraight_instantiate, readConstant_reindex _ _ _ Q (coefficientAt_window w)]
  exact adaptiveCoordinateProgram_tCount w start Q hQ history

end
end ShorECDLP.Entrant.ZeroAdaptive
