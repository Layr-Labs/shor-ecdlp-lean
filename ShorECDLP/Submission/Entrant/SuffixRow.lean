import ShorECDLP.Submission.Entrant.FusedRow
import ShorECDLP.Submission.Entrant.SuffixSite

/-! The fused row with the output scratch as a seventh masked site. -/

section
namespace ShorECDLP.Entrant.WEXUnlookup
open Quantum Challenge AndGadget WEXCredit Paper2607_13816 Paper2607_13816.ChallengeMigration WEX
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
attribute [local irreducible] ECDSAAdd.run

def rowPostF : Code 32768 := [.plain (WEX.cornersPre probeRows), .masked (WEX.scrFSite probeRows),
  .plain (WEX.sfxZ0 ++ WEX.sfxPadE), .plain (wLiteral [.X 838])]

def row3F : Code 32768 := rowPre ++ (generic2 probeRows ++ rowPostF)

theorem erase_rowPostF : erase rowPostF = WEX.portSuffixCodeF probeRows ++ wLiteral [.X 838] := by
  simp [rowPostF, erase, Block.code, WEX.portSuffixCodeF, List.append_assoc]

theorem erase_rowPost : erase rowPost = portSuffixCodeE probeRows ++ wLiteral [.X 838] := by
  simp [rowPost, erase, Block.code]

/-! ### The window root survives placed code -/

theorem root_keep_instr (read : ConstantBit 32768 → Bool) (i : WInstr 32768) (a : Nat)
    (hp : PlacedPair windowBits windowPaths windowRoot i) (m : List Bool) (s : ECDSAAdd.State) :
    (ECDSAAdd.run ((specialize [i] a).instantiate read) m s).basis windowRoot = s.basis windowRoot := by
  cases i with
  | literal p =>
    have e : (specialize ([.literal p] : WCode 32768) a).instantiate read = p := by
      change (specialize (wLiteral p) a).instantiate read = p
      simp only [specialize_literal, Tmpl.instantiate_lit]
    rw [e]
    exact ECDSAAdd.run_preserves_outside _ _ _ _ (hp windowRoot List.mem_cons_self)
  | lookup c ps =>
    have hr : windowRoot ∉ portTargets ps := fun h => hp.2.2.2 List.mem_cons_self h
    cases c with
    | none =>
      have e : (specialize ([.lookup none ps] : WCode 32768) a).instantiate read =
          xBits (portTargets ps) (portBits read ps a) := scr_lookup_inst read ps a
      rw [e, xBits_run]
      simp [xMask_outside _ _ _ hr]
    | some c =>
      have hc : c ∉ portTargets ps := fun h => hp.2.2.2 (List.mem_cons_of_mem _ List.mem_cons_self) h
      rw [scr_lookup_some_inst, cBits_run _ _ _ _ _ hc]
      simp [xMask_outside _ _ _ hr]

theorem root_keep (read : ConstantBit 32768 → Bool) (code : WCode 32768) (a : Nat)
    (hp : ∀ i ∈ code, PlacedPair windowBits windowPaths windowRoot i) (m : List Bool) (s : ECDSAAdd.State) :
    (ECDSAAdd.run ((specialize code a).instantiate read) m s).basis windowRoot = s.basis windowRoot := by
  induction code generalizing m s with
  | nil =>
    rw [show (specialize ([] : WCode 32768) a).instantiate read = [] from rfl]
    simp [ECDSAAdd.run]
  | cons i code ih =>
    have e : (i :: code : WCode 32768) = [i] ++ code := rfl
    rw [e, specialize_append, Tmpl.instantiate_append, ECDSAAdd.run_append,
      ih (fun j hj => hp j (List.mem_cons_of_mem _ hj)),
      root_keep_instr read i a (hp i List.mem_cons_self)]

theorem erase_placed (code : Code 32768) (h : ∀ b ∈ code, BlockGeometry b) :
    ∀ i ∈ erase code, PlacedPair windowBits windowPaths windowRoot i := by
  intro i hi
  obtain ⟨b, hb, hib⟩ := List.mem_flatMap.mp hi
  have g := h b hb
  cases b with
  | plain code => exact g.1 i hib
  | masked site => exact placed_implies_pair _ _ _ _ (g.placed i hib)

theorem rowPreGen_root (read : ConstantBit 32768 → Bool) (a : Nat) (m : List Bool) (s : ECDSAAdd.State) :
    (ECDSAAdd.run (reference read a (rowPre ++ generic2 probeRows)) m s).basis windowRoot = s.basis windowRoot := by
  apply root_keep read _ a
  apply erase_placed
  intro b hb
  apply row2_geometry
  rw [row2_split]
  simp only [List.mem_append] at hb ⊢
  tauto

/-! ### The new output half at the generic exit -/

theorem cornersPre_inst (read : ConstantBit 32768 → Bool) (a : Nat) :
    (specialize (WEX.cornersPre probeRows) a).instantiate read = WEX.preProg read probeRows a := by
  simp only [WEX.cornersPre, WEX.preProg, specialize_append, Tmpl.instantiate_append, specialize_literal,
    Tmpl.instantiate_lit, scr_lookup_some_inst, WEX.scrCPorts, scr_point_targets, List.append_assoc]

theorem scrFSite_clean (read : ConstantBit 32768 → Bool) (a : Nat) (m : List Bool) (t : ECDSAAdd.State)
    (hr : t.basis windowRoot = true) (hs : ∀ w ∈ scrAllWires, t.basis w = false) :
    Clean (portTargets (WEX.scrFSite probeRows).ports)
      (ECDSAAdd.run ((specialize (WEX.scrFSite probeRows).code a).instantiate read) m t).basis := by
  let K := portBits read (scrDPorts probeRows) a
  have e : (specialize (WEX.scrFSite probeRows).code a).instantiate read =
      cBits windowRoot scrAllWires K ++ (WEX.fMidProg ++ cBits windowRoot scrAllWires K) := by
    simp only [WEX.scrFSite_code, specialize_append, Tmpl.instantiate_append, scr_lookup_some_inst,
      specialize_literal, Tmpl.instantiate_lit, scrDPorts_targets, WEX.scrFArith_eq, K, List.append_assoc]
  have hm := scrD_maps read probeRows a
  have hK : K = (portBits read (scrPairBits probeRows (wBit probeRows .y)) a ++
      portBits read (scrShortBits probeRows) a) ++ portBits read (scrDExtraBits probeRows) a :=
    scrDPorts_bits read probeRows a
  have sim : ScrSim scrAllWires K WEX.fMidProg
      (scrSw1 ++ (cBits streamLayout.core.equalNegY scrDTargets
        (portBits read (scrShortBits probeRows) a ++ portBits read (scrDExtraBits probeRows) a) ++
        (scrSw1 ++ (scrNegP ++ midIP read probeRows a)))) := by
    rw [hK]
    exact (scrD_swSim _).1.append ((scrD_ccxSim _ _ hm.2.2).append ((scrD_swSim _).1.append
      ((scrD_negSim _).append (scrD_midSim _ _ _ _ rfl hm.1 hm.2.1))))
  have hc : ∀ w ∈ scrAllWires, (ECDSAAdd.run ((specialize (WEX.scrFSite probeRows).code a).instantiate read) m t).basis w
      = false := by
    rw [e, cBits_sandwich_run windowRoot scrAllWires K _ m t WEX.windowRoot_not_scrAll WEX.root_mid hr,
      ← List.append_assoc, scr_sandwich _ _ _ _ sim m t hs]
    exact (sim.step m t hs).2
  intro w hw
  have hw' : w ∈ scrAllWires := by
    change w ∈ portTargets (scrDPorts probeRows) at hw
    rwa [scrDPorts_targets] at hw
  exact hc w hw'

theorem suffixFE_records (read : ConstantBit 32768 → Bool) (a : Nat) :
    ECDSAAdd.measurementCount ((specialize (WEX.portSuffixCodeF probeRows) a).instantiate read) =
      ECDSAAdd.measurementCount ((specialize (portSuffixCodeE probeRows) a).instantiate read) := by
  rw [WEX.portSuffixF_inst, portSuffixE_inst, scrECorners_inst]
  simp only [WEX.preProg, WEX.fMidProg, tail0, ECDSAAdd.measurementCount_append, cBits_records, xBits_records,
    ccxList_records, cxList_records]
  omega

theorem ref_root (read : ConstantBit 32768 → Bool) (a : Nat) (code : Code 32768)
    (hc : ∀ b ∈ code, b ∈ row2) (m : List Bool) (st : ECDSAAdd.State) :
    (ECDSAAdd.run (reference read a code) m st).basis windowRoot = st.basis windowRoot :=
  root_keep read _ a (erase_placed code (fun b hb => row2_geometry b (hc b hb))) m st

theorem rowPre_sub : ∀ b ∈ rowPre, b ∈ row2 := by
  intro b hb; rw [row2_split]; exact List.mem_append_left _ hb

theorem generic2_sub : ∀ b ∈ generic2 probeRows, b ∈ row2 := by
  intro b hb; rw [row2_split]; exact List.mem_append_right _ (List.mem_append_left _ hb)

theorem reference_generic (read : ConstantBit 32768 → Bool) (a : Nat)
    {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy) (hr : RowReads read (probeRows a) (.some hc)) :
    reference read a (generic streamLayout probeRows) = Arith.genericS streamLayout cx cy := by
  rw [reference, erase_generic, specialize_generic]
  exact Arith.genericT_inst streamLayout hc hr

/-- From the row-entry boundary, the row with the output site is safe and keeps the reference run. -/
theorem rowF_facts (read : ConstantBit 32768 → Bool) (address : Nat)
    (R : Point) {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (hr : RowReads read (probeRows address) (.some hc))
    (h₁ : cy ≠ -cy) (h₂ : exceptionBit (.some hc) = true)
    (hD : (.some hc : Point)+.some hc ≠ 0)
    (hDo : ShorECDLP.order • ((.some hc : Point)+.some hc) = 0)
    (s : BasisState) (hs : PointDialogBoundary streamLayout R true (fun _=>false) (flipInfinity s))
    (hroot : s windowRoot = true) :
    Safe read address row3F ⟨false,s⟩ ∧
      ∀ m, ECDSAAdd.run (reference read address row3F) m ⟨false,s⟩ =
        ECDSAAdd.run (reference read address row2) m ⟨false,s⟩ := by
  let st0 : ECDSAAdd.State := ⟨false,s⟩
  let P := reference read address rowPre
  let G := reference read address (generic2 probeRows)
  have h7 := Arith.boundary_genericS streamLayout streamLayout_widths streamLayout_nodup R true
    (flags streamLayout R (.some hc) true cy) hc (flags_generic R hc)
  -- the state after the prefix and the generic block, for any records
  have exitFacts : ∀ m n, (ECDSAAdd.run G n (ECDSAAdd.run P m st0)).basis windowRoot = true ∧
      ∀ w ∈ scrAllWires, (ECDSAAdd.run G n (ECDSAAdd.run P m st0)).basis w = false := by
    intro m n
    have hb1 := rowPre_boundary read address R hc hr h₁ h₂ hD hDo s hs hroot m
    constructor
    · rw [ref_root read address _ generic2_sub, ref_root read address _ rowPre_sub]
      exact hroot
    · intro w hw
      have hgen := (generic2_cases read address probeRows R true (flags streamLayout R (.some hc) true cy)
        hc hr (flags_generic R hc) _ hb1).2 n
      change ECDSAAdd.run (reference read address (generic2 probeRows)) n _ = _ at hgen
      change (ECDSAAdd.run (reference read address (generic2 probeRows)) n (ECDSAAdd.run P m st0)).basis w = false
      rw [hgen, reference_generic read address hc hr]
      exact (regValue_zero _ _).mp (h7 _ n hb1).2.clean w (scrAll_pool w hw)
  have r2 := row2_facts read address R hc hr h₁ h₂ hD hDo s hs hroot
  have eF : reference read address rowPostF =
      (specialize (WEX.portSuffixCodeF probeRows) address).instantiate read ++ ([.X 838] : ECDSAAdd.Program) := by
    simp only [reference, erase_rowPostF, specialize_append, Tmpl.instantiate_append, specialize_literal,
      Tmpl.instantiate_lit]
  have eE : reference read address rowPost =
      (specialize (portSuffixCodeE probeRows) address).instantiate read ++ ([.X 838] : ECDSAAdd.Program) := by
    simp only [reference, erase_rowPost, specialize_append, Tmpl.instantiate_append, specialize_literal,
      Tmpl.instantiate_lit]
  constructor
  · have old := r2.1
    rw [row2_split] at old
    unfold row3F
    apply safe_append _ _ _ _ _ (safe_left _ _ _ _ _ old)
    intro m _
    have hb1 := rowPre_boundary read address R hc hr h₁ h₂ hD hDo s hs hroot m
    apply safe_append _ _ _ _ _ (generic2_cases read address probeRows R true (flags streamLayout R (.some hc) true cy)
      hc hr (flags_generic R hc) _ hb1).1
    intro n _
    obtain ⟨hr2, hc2⟩ := exitFacts m n
    simp only [rowPostF, Safe, BlockSafe]
    refine ⟨True.intro, fun k _ => ⟨fun j => ?_, fun j _ => ⟨True.intro, fun _ _ => ⟨True.intro, fun _ _ => True.intro⟩⟩⟩⟩
    have ek : blockReference read address (Block.plain (WEX.cornersPre probeRows)) = WEX.preProg read probeRows address := by
      simp only [blockReference, Block.code, cornersPre_inst]
    rw [ek]
    apply scrFSite_clean read address j
    · rw [ECDSAAdd.run_preserves_outside _ _ _ _ (WEX.root_pre read probeRows address)]
      exact hr2
    · intro w hw
      rw [ECDSAAdd.run_preserves_outside _ _ _ _ (WEX.scrAll_pre read probeRows address w hw)]
      exact hc2 w hw
  · intro m
    rw [row3F, row2_split, reference_append, reference_append, reference_append, reference_append, eF, eE]
    have e1 : ∀ X : ECDSAAdd.Program, P ++ (G ++ (X ++ ([.X 838] : ECDSAAdd.Program))) =
        (P ++ G) ++ X ++ ([.X 838] : ECDSAAdd.Program) := fun X => by simp only [List.append_assoc]
    change ECDSAAdd.run (P ++ (G ++ _)) m st0 = ECDSAAdd.run (P ++ (G ++ _)) m st0
    rw [e1, e1]
    apply portSuffix_middle _ _ _ _ (suffixFE_records read address) st0
    intro k n
    rw [ECDSAAdd.run_append P G]
    obtain ⟨hr2, hc2⟩ := exitFacts (k.take (ECDSAAdd.measurementCount P)) (k.drop (ECDSAAdd.measurementCount P))
    rw [WEX.portSuffixF_inplace read probeRows address _ hr n _ hr2 hc2,
      portSuffixE_inplace read probeRows address _ hr n _ hc2]

end
end ShorECDLP.Entrant.WEXUnlookup
