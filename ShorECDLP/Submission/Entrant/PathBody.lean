import ShorECDLP.Submission.Entrant.PathBank

/-! ### Geometry of the fused row on the pool bank -/

namespace ShorECDLP.Entrant.PathShare
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 40000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

theorem plain_geoP (B : Bank) (hbits : ∀ w ∈ B.bits, w ∈ windowBits) (code : WCode 32768)
    (hold : ∀ i ∈ code, PlacedPair windowBits windowPaths windowRoot i)
    (hlit : ∀ i ∈ code, ∃ p, i = .literal p) : LitAvoid B.bits code := by
  intro i hi
  obtain ⟨p, rfl⟩ := hlit i hi
  refine ⟨p, rfl, ?_⟩
  intro w hw
  apply hold _ hi w
  rcases List.mem_cons.mp hw with h | h
  · simp [h]
  · simp [hbits w h]

theorem site_geoP (B : Bank) (hbits : ∀ w ∈ B.bits, w ∈ windowBits) (hbn : B.bits.Nodup)
    (hpaths : B.paths = pathBank) (site : MaskedSite 32768) (hold : WEXUnlookup.SiteGeometry site)
    (hlit : ∀ p, WInstr.literal p ∈ site.code → ∀ w ∈ pathBank, w ∉ ECDSAAdd.wires p)
    (hlook : ∀ c ps, WInstr.lookup c ps ∈ site.code →
      (∀ w ∈ pathBank, w ∉ portTargets ps) ∧ ∀ q ∈ c, q ∉ pathBank) :
    SiteGeoP B site := by
  refine ⟨?_, hold.kind⟩
  intro i hi
  have ho := hold.placed i hi
  rw [hpaths]
  cases i with
  | literal p =>
    intro w hw
    simp only [List.mem_cons, List.mem_append, or_assoc] at hw
    rcases hw with h | h | h
    · exact ho w (by simp [h])
    · exact ho w (by simp [hbits w h])
    · exact hlit p hi w h
  | lookup c ps =>
    dsimp only [Placed] at ho ⊢
    obtain ⟨hT, hC⟩ := hlook c ps hi
    have hq : lookupRoot windowRoot c ∉ pathBank := by
      cases c with
      | none => exact pathBank_window windowRoot (by simp)
      | some q => exact hC q (Option.mem_def.mpr rfl)
    have hqb : lookupRoot windowRoot c ∉ windowBits := by
      have h0 := ho.1
      rw [List.cons_append] at h0
      have := (List.nodup_cons.mp h0).1
      exact fun h => this (List.mem_append_left _ h)
    refine ⟨?_, ho.2.1, ?_⟩
    · rw [List.cons_append, List.nodup_cons]
      refine ⟨fun h => ?_, ?_⟩
      · rcases List.mem_append.mp h with h | h
        · exact hqb (hbits _ h)
        · exact hq h
      · rw [List.nodup_append]
        refine ⟨hbn, pathBank_nodup, ?_⟩
        intro a ha b hb e
        subst e
        exact pathBank_window a (by simp [hbits a ha]) hb
    · apply List.disjoint_left.mpr
      intro w hw ht
      simp only [List.mem_cons, List.mem_append, or_assoc] at hw
      rcases hw with h | h | h | h
      · exact List.disjoint_left.mp ho.2.2 (by simp [h]) ht
      · exact List.disjoint_left.mp ho.2.2 (by simp [h]) ht
      · exact List.disjoint_left.mp ho.2.2 (by simp [hbits w h]) ht
      · exact hT w h ht

theorem row2_masked_cases (site : MaskedSite 32768) (hb : Block.masked site ∈ row2) :
    site = WEX.scrInSite probeRows ∨ site = pairSite (wFields probeRows .negX) (wFields probeRows .negY) ∨
      site = constSite streamLayout streamLayout.point.x (wFields probeRows .tripleX) ∨
      site = pairSite (wFields probeRows .x) (wFields probeRows .negY) ∨ site = scrDSite := by
  rw [row2_split, generic2_list] at hb
  simp only [rowPre, rowPost, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    Block.masked.injEq, reduceCtorEq, false_or] at hb
  tauto

def isLit {n} : WInstr n → Bool
  | .literal _ => true
  | .lookup _ _ => false

def plainLit {n} : Block n → Bool
  | .plain c => c.all isLit
  | .masked _ => true

theorem row2_plainLit : row2.all plainLit = true := by
  decide +kernel

theorem row2_plain_lit (code : WCode 32768) (hb : Block.plain code ∈ row2) : WEX.LitOnly code := by
  have h : code.all isLit = true := List.all_eq_true.mp row2_plainLit _ hb
  intro i hi
  have hi' := List.all_eq_true.mp h i hi
  cases i with
  | literal p => exact ⟨p, rfl⟩
  | lookup c ps => simp [isLit] at hi'

theorem row2_geoP (B : Bank) (hbits : ∀ w ∈ B.bits, w ∈ windowBits) (hbn : B.bits.Nodup)
    (hpaths : B.paths = pathBank) : ∀ b ∈ row2, BlockGeoP B b := by
  intro b hb
  have old := WEXUnlookup.row2_geometry b hb
  cases b with
  | plain code => exact plain_geoP B hbits code old.1 (row2_plain_lit code hb)
  | masked site =>
    have avoid : Avoids site.code := by
      rcases row2_masked_cases site hb with rfl | rfl | rfl | rfl | rfl
      · exact scrIn_avoids
      · exact pair_avoid _ _
      · exact triple_avoid
      · exact pair_avoid _ _
      · exact scrD_avoids
    exact site_geoP B hbits hbn hpaths site old avoid.1 avoid.2

theorem row2_geo15 : ∀ b ∈ row2, BlockGeoP bank15 b :=
  row2_geoP bank15 (fun _ h => h) (by decide +kernel) rfl

theorem row2_geo14 : ∀ b ∈ row2, BlockGeoP bank14 b :=
  row2_geoP bank14 (by decide +kernel) (by decide +kernel) rfl


end
end ShorECDLP.Entrant.PathShare

/-! ### Supports and the compact labels without the old path bank -/

namespace ShorECDLP.Entrant.PathShare
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 40000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-- The body's source labels without the fifteen retired path wires. -/
def retired (w : Nat) : Prop := 10000 ≤ w ∧ w < 10015
instance : DecidablePred retired := fun w => inferInstanceAs (Decidable (10000 ≤ w ∧ w < 10015))

def newSource : List Wire := sourceSupport.filter (fun w => decide (¬retired w))

theorem newSource_mem (w : Nat) :
    w ∈ newSource ↔ (fixedPort w ∨ oldWork w) ∧ ¬retired w := by
  rw [newSource, List.mem_filter, sourceSupport_mem, decide_eq_true_eq]

theorem newSource_of_bounds (xs : List Wire)
    (h : ∀ w ∈ xs, (fixedPort w ∨ oldWork w) ∧ ¬retired w) : xs ⊆ newSource :=
  fun w hw => (newSource_mem w).mpr (h w hw)

theorem newSource_of_old (w : Nat) (h1 : w ∈ sourceSupport) (h2 : w ∉ windowPaths) : w ∈ newSource := by
  rw [newSource_mem]
  refine ⟨(sourceSupport_mem w).mp h1, fun h => h2 ?_⟩
  unfold retired at h
  simp only [windowPaths, List.mem_range'_1]
  omega

/-- Swap the retired path labels with the sources of the top fifteen compact labels. -/
def tauWire (w : Nat) : Nat :=
  if 10000 ≤ w ∧ w < 10012 then w + 5644
  else if 10012 ≤ w ∧ w < 10015 then w + 9802
  else if 15644 ≤ w ∧ w < 15656 then w - 5644
  else if 19814 ≤ w ∧ w < 19817 then w - 9802
  else w

theorem tauWire_involutive : Function.Involutive tauWire := by
  intro w
  unfold tauWire
  split_ifs <;> omega

def tau : Wire ≃ Wire := ⟨tauWire, tauWire, tauWire_involutive, tauWire_involutive⟩

/-- Compact labels: the old compaction after the swap. -/
def pi : Wire ≃ Wire := tau.trans compactPerm

theorem pi_apply (w : Wire) : pi w = compactWire (tauWire w) := rfl

theorem pi_fixed (w : Wire) (h : fixedPort w) : pi w = w := by
  have ht : tauWire w = w := by unfold tauWire fixedPort at *; split_ifs <;> omega
  rw [pi_apply, ht]
  exact compactPerm_fixed w h

theorem pi_hot (i : Fin 128) : pi (hot i) = hot i := by
  have hi := i.isLt
  have ht : tauWire (hot i) = hot i := by unfold tauWire hot; split_ifs <;> omega
  rw [pi_apply, ht]
  exact compactPerm_hot i

theorem pi_bound (w : Nat) (hw : w ∈ newSource) : compactWire (tauWire w) < 1619 := by
  obtain ⟨h1, h2⟩ := (newSource_mem w).mp hw
  unfold retired at h2
  by_cases hA : 15644 ≤ w ∧ w < 15656
  · have ht : tauWire w = w - 5644 := by unfold tauWire; split_ifs <;> omega
    have ho : oldWork (w - 5644) := by unfold oldWork; omega
    rw [ht, compactWire, if_pos ho]
    unfold freeAt oldRank
    split_ifs <;> omega
  by_cases hB : 19814 ≤ w ∧ w < 19817
  · have ht : tauWire w = w - 9802 := by unfold tauWire; split_ifs <;> omega
    have ho : oldWork (w - 9802) := by unfold oldWork; omega
    rw [ht, compactWire, if_pos ho]
    unfold freeAt oldRank
    split_ifs <;> omega
  have ht : tauWire w = w := by unfold tauWire; split_ifs <;> omega
  rw [ht]
  rcases h1 with hf | ho
  · have he : compactWire w = w := compactPerm_fixed w hf
    rw [he]
    unfold fixedPort at hf
    omega
  · rw [compactWire, if_pos ho]
    unfold oldWork at ho
    unfold freeAt oldRank
    split_ifs <;> omega

theorem pi_point (w : Wire) (h : w ∈ pointLogicalWires) : pi w = w := by
  apply pi_fixed
  simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1] at h
  unfold fixedPort; dsimp only [Wire] at *; omega

theorem pi_address (w : Wire) (h : w ∈ streamAddress) : pi w = w := by
  apply pi_fixed
  exact Or.inr (Or.inr (Or.inr (by simpa [streamAddress] using h)))

def pull2 (s : BasisState) : BasisState := relabelBasis pi.symm s

theorem pull2_at (s : BasisState) (w : Wire) (h : fixedPort w) : pull2 s w = s w := by
  simp only [pull2,relabelBasis,Equiv.symm_symm,pi_fixed w h]

theorem pull2_hot (s : BasisState) (i : Fin 128) : pull2 s (hot i) = s (hot i) := by
  simp only [pull2,relabelBasis,Equiv.symm_symm,pi_hot]

theorem pull2_write (P : ShorECDLP.Secp256k1.Point) (s : BasisState) :
    pull2 (pointWrite P s) = pointWrite P (pull2 s) := by
  funext w
  by_cases hw : w ∈ pointLogicalWires
  · have he := pi_point w hw
    simp only [pull2,relabelBasis,Equiv.symm_symm,pointWrite,he,if_pos hw]
  · have hn : pi w ∉ pointLogicalWires := by
      intro hh
      have he := pi_point _ hh
      have : pi w = w := pi.injective he
      exact hw (this ▸ hh)
    simp only [pull2,relabelBasis,Equiv.symm_symm,pointWrite,if_neg hw,if_neg hn]

theorem push2_write (P : ShorECDLP.Secp256k1.Point) (s : BasisState) :
    relabelBasis pi (pointWrite P (pull2 s)) = pointWrite P s := by
  have h := congrArg (relabelBasis pi) (pull2_write P s)
  have hi (t : BasisState) : relabelBasis pi (pull2 t) = t := by
    simpa only [pull2,Equiv.symm_symm] using relabelBasis_symm pi.symm t
  rw [hi] at h
  exact h.symm

theorem pull2_coordinates (s : BasisState) :
    pointStateCoordinates (pull2 s) = pointStateCoordinates s := by
  have he (ws : List Wire) (hw : ∀ w ∈ ws, fixedPort w) :
      wireValues ws (pull2 s) = wireValues ws s := by
    apply List.map_congr_left
    intro w hm; exact pull2_at s w (hw w hm)
  have hx := he (List.range' 263 256) (by
    intro w hw; exact Or.inl (List.mem_range'_1.mp hw))
  have hy := he (List.range' 580 256) (by
    intro w hw
    have hw := List.mem_range'_1.mp hw
    apply Or.inr; apply Or.inl; dsimp only [Wire] at *; omega)
  simp only [pointStateCoordinates,hx,hy,pull2_at s 838 (by decide +kernel)]

theorem pull2_digit (s : BasisState) : windowRawDigit 0 (pull2 s) = windowRawDigit 0 s := by
  have he : wireValues (List.range' 855 15) (pull2 s) = wireValues (List.range' 855 15) s := by
    apply List.map_congr_left
    intro w hw
    apply pull2_at
    have hw := List.mem_range'_1.mp hw
    apply Or.inr; apply Or.inr; apply Or.inr; dsimp only [Wire] at *; omega
  simp only [windowRawDigit,windowAddressBits,windowBankStart,Nat.mul_zero,Nat.add_zero,he,
    pull2_at s 870 (by decide +kernel)]

def ready2 (s : BasisState) : Prop := windowReady (pull2 s) ∧ MeasuredClear.HotClean hot s

theorem ready2_active (s : BasisState) (h : ready2 s) : s 836 = true := by
  simpa only [pull2_at s 836 (by decide +kernel)] using windowReady_active (pull2 s) h.1

theorem ready2_write (P : ShorECDLP.Secp256k1.Point) (s : BasisState) (h : ready2 s) :
    ready2 (pointWrite P s) := by
  refine ⟨?_, pointWrite_hot P s h.2⟩
  rw [pull2_write]
  exact windowReady_write P (pull2 s) h.1

theorem pull2_address (s : BasisState) (v : Wire) (hv : v ∈ streamAddress) (b : Bool) :
    pull2 (s[v ↦ b]) = (pull2 s)[v ↦ b] := by
  have hh' : pi.symm v = v := by
    rw [Equiv.symm_apply_eq]; exact (pi_address v hv).symm
  simp only [pull2,relabelBasis_upd,hh']

theorem ready2_address (s : BasisState) (h : ready2 s)
    (v : Wire) (hv : v ∈ streamAddress) (b : Bool) : ready2 (s[v ↦ b]) := by
  refine ⟨?_, ?_⟩
  · rw [pull2_address s v hv b]
    exact windowReady_address (pull2 s) h.1 v hv b
  · intro i
    have hn : hot i ≠ v := fun he => hot_outside_address i (he.symm ▸ hv)
    exact (upd_other s v b hn).trans (h.2 i)

theorem pull2_first (s : BasisState) (h : FirstWindowInput s) : FirstWindowInput (pull2 s) := by
  constructor
  · simpa only [pull2_at s 836 (by decide +kernel)] using h.1
  · intro w hw ha
    change s (pi w) = false
    apply h.2
    · intro hh
      have hfix : pi 836 = 836 := pi_fixed _ (by decide +kernel)
      exact hw (pi.injective (hh.trans hfix.symm))
    · intro hh
      have hfix := pi_address _ hh
      have he : pi w = w := pi.injective hfix
      exact ha (he ▸ hh)

theorem ready2_first (s : BasisState) (h : FirstWindowInput s) (P : ShorECDLP.Secp256k1.Point) :
    ready2 (pointWrite P s) := by
  refine ⟨?_, ?_⟩
  · rw [pull2_write]
    exact windowReady_first (pull2 s) (pull2_first s h) P
  · apply pointWrite_hot P s
    intro i
    apply h.2
    · have hi := i.isLt
      simp only [hot]
      dsimp only [Wire] at *
      omega
    · exact hot_outside_address i

def state2 (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point) (s : BasisState) : BasisState :=
  relabelBasis pi (bodyState coeffs Q (pull2 s))

theorem state2_correct (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point)
    (s : BasisState) (hs : ready2 s) (P : ShorECDLP.Secp256k1.Point)
    (hP : pointStateCoordinates s = fig14PointEncoding P) :
    state2 coeffs Q s = pointWrite
      (P + if s 836 then
        (if s 870 then constantPoint Q (coeffs ⟨signedTableAddress 32768
          (windowRawDigit 0 s),signedTableAddress_bound 32768 _ (windowRawDigit_bound 0 s)⟩)
         else -constantPoint Q (coeffs ⟨signedTableAddress 32768
          (windowRawDigit 0 s),signedTableAddress_bound 32768 _ (windowRawDigit_bound 0 s)⟩))
        else 0) s := by
  unfold state2
  rw [bodyState_correct coeffs Q (pull2 s) hs.1 P ((pull2_coordinates s).trans hP),push2_write]
  simp only [pull2_at s 836 (by decide +kernel),pull2_at s 870 (by decide +kernel),pull2_digit]

/-- Transport a coherent source body to the new compact labels. -/
theorem relabel2_coherent {s e : Nat} (p : Straight 32768 s e) (coeffs : Fin 32768 → PointCoeff)
    (Q : ShorECDLP.Secp256k1.Point) (history : Fin s → Bool)
    (hc : CoherentlyImplementsOn (p.instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)) Ready) :
    CoherentlyImplementsOn ((relabelStraight pi p).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (state2 coeffs Q))
      (fun s => ready2 s ∧ ∃ P, pointStateCoordinates s = fig14PointEncoding P) := by
  have h := hc.relabel pi
  have hr : CoherentlyImplementsOn
      ((p.instantiate (readConstant coeffs Q) history).relabel pi)
      ((relabelState pi).comp ((Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)).comp
        (relabelState pi.symm)))
      (fun s => ready2 s ∧ ∃ P, pointStateCoordinates s = fig14PointEncoding P) := by
    obtain ⟨cs,aligned,mass⟩ := h
    refine ⟨cs,aligned.imp ?_,mass⟩
    intro b c hb s hs
    apply hb s
    refine ⟨hs.1.1,?_⟩
    intro i
    exact (pull2_hot s i).trans (hs.1.2 i)
  have he := hr.congrIdeal (secondIdeal := Finsupp.lmapDomain ℂ ℂ (state2 coeffs Q))
    (by intro s _; simp [state2,pull2,LinearMap.comp_apply,relabelState,ket])
  rw [relabelStraight_instantiate]
  exact he

theorem relabel2_support {s e : Nat} (p : Straight 32768 s e)
    (h : ChallengeMigration.straightWires p ⊆ newSource) :
    ChallengeMigration.straightWires (relabelStraight pi p) ⊆ List.range 1619 := by
  rw [straightWires_relabel]
  intro w hw
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
  exact List.mem_range.mpr ((pi_apply v).trans_lt (pi_bound v (h hv)))

theorem base_support2 : completeBatchedSupport ⊆ List.range 1619 := by
  intro w hw
  simp only [completeBatchedSupport,resetWires,List.mem_cons,List.mem_append,
    List.mem_range,List.mem_range'_1,List.not_mem_nil,or_false] at hw
  apply List.mem_range.mpr
  dsimp only [Wire] at *; omega

end
end ShorECDLP.Entrant.PathShare

/-! ### The width-15 body on the pool bank -/

namespace ShorECDLP.Entrant.PathShare.W15
open Quantum Challenge AndGadget WEXCredit Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
open ShorECDLP.Entrant.Schedule33.Flexible ShorECDLP.Entrant.PathShare
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

theorem lay15 : ∀ b ∈ row2, BlockLay bank15 b := fun b hb => geo_lay bank15 bank15_ok b (row2_geo15 b hb)

theorem old15_lay : ∀ b ∈ row2, BlockLay old15 b := by
  intro b hb
  have hg := WEXUnlookup.row2_geometry b hb
  cases b with
  | plain code =>
    exact pair_layouts_of_placed _ _ _ _ (by simp [old15,windowBits,windowPaths]) (pair_placed_normalize _ _ _ _ hg.1)
  | masked site =>
    have hp : ∀ i ∈ site.prefix, PlacedPair windowBits windowPaths windowRoot i := fun i hi =>
      placed_implies_pair _ _ _ _ (hg.placed i (List.mem_append_left _ hi))
    exact ⟨pair_layouts_of_placed _ _ _ _ (by simp [old15,windowBits,windowPaths]) (pair_placed_normalize _ _ _ _ hp),
      WEXUnlookup.site_high_layout site hg⟩

theorem recordsP_old15 (code : Code 32768) : recordsP old15 code = WEXUnlookup.records code := by
  induction code with
  | nil => rfl
  | cons b code ih =>
    simp only [recordsP, WEXUnlookup.records, ih]
    cases b <;> rfl

theorem row2_recordsP : recordsP bank15 row2 = 1757978 := by
  rw [recordsP_eq bank15 old15 rfl rfl row2 lay15 old15_lay, recordsP_old15]
  exact WEXUnlookup.row2_records

theorem codeTP15 (code : Code 32768) : codeTP bank15 code = WEXUnlookup.ccx code := by
  induction code with
  | nil => rfl
  | cons b code ih =>
    have hl : 2 ^ bank15.bits.length - 1 = 32767 := by simp [bank15, windowBits]
    have hn : (tableAddressTree bank15.high 0 1).internalNodes = 255 := WEXUnlookup.high_nodes
    simp only [codeTP, WEXUnlookup.ccx, ih]
    cases b <;> simp only [blockTP, WEXUnlookup.blockCCX, hl, hn]

theorem program_slots_old15 (code : Code 32768) (hl : ∀ b ∈ code, BlockLay old15 b) (start : Nat) :
    (WEXUnlookup.program code start).gateSlots = codeSP old15 code := by
  induction code generalizing start with
  | nil => rfl
  | cons b code ih =>
    have hb : (WEXUnlookup.blockProgram b start).gateSlots = (blockProgP old15 b start).gateSlots := by
      cases b <;> rfl
    rw [WEXUnlookup.program, castFinish_gateSlots, Straight.gateSlots_append, ih (fun d hd => hl d (by simp [hd])),
      hb, blockProgP_slots old15 b (hl b (by simp))]
    rfl

attribute [local irreducible] programP blockProgP clearP WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  WEX.literalToffolis WEX.normalizeW ccx Nat.add Nat.mul

def addFixedP (start : Nat) : Straight 32768 start (start+1757978) :=
  castFinish (congrArg (fun m => start+m) row2_recordsP) (programP bank15 row2 start)

theorem addFixedP_run (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((addFixedP start).instantiate read history).run = (sourceCodeP bank15 read row2).run := by
  rw [addFixedP,castFinish_instantiate,programP_run]

theorem addFixedP_tCount (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((addFixedP start).instantiate read history).tCount = 7*ccx row2 := by
  rw [addFixedP,castFinish_instantiate,programP_tCount read bank15 row2 lay15,codeTP15]

theorem addFixedP_slots (start : Nat) : (addFixedP start).gateSlots =
    codeSlots windowBits (normalizeW (erase row2)) + 250725868 := by
  rw [addFixedP,castFinish_gateSlots,programP_slots bank15 row2 lay15,codeSP_congr bank15 old15 rfl rfl,
    ← program_slots_old15 row2 old15_lay start]
  exact WEXUnlookup.row2_slots start

theorem addFixedP_wellFormed (start : Nat) : (addFixedP start).WellFormed := by
  rw [addFixedP,castFinish_wellFormed]
  exact programP_wellFormed bank15 bank15_ok row2 row2_geo15 row2_physical start

theorem addFixedP_residue (start : Nat) : residue (addFixedP start) = 0 := by
  rw [addFixedP,residue_cast]
  exact programP_residue bank15 row2 start

theorem addFixedP_credit (start : Nat) : ProgramCredit (addFixedP start) (ccx row2) := by
  have hz := addFixedP_residue start
  refine ⟨hz,?_⟩
  have he := exact_t (addFixedP start) hz (fun _ => false) (fun _ => false)
  have ht := addFixedP_tCount (fun _ => false) start (fun _ => false)
  omega

theorem row2_placed_old : ∀ i ∈ erase row2, PlacedPair windowBits windowPaths windowRoot i := by
  intro i hi
  obtain ⟨b, hb, hib⟩ := List.mem_flatMap.mp hi
  exact (block_placed b (WEXUnlookup.row2_geometry b hb)).1 i hib

theorem wires_new_of {p : ECDSAAdd.Program} {l : List Wire} (hs : ECDSAAdd.wires p ⊆ l.toFinset)
    (h : ∀ w ∈ l, w ∈ ECDSAAdd.wires p → w ∈ newSource) : ECDSAAdd.wires p ⊆ newSource.toFinset :=
  fun w hw => List.mem_toFinset.mpr (h w (List.mem_toFinset.mp (hs hw)) hw)

theorem row2_lit_new (p : ECDSAAdd.Program) (hp : WInstr.literal p ∈ erase row2) :
    ECDSAAdd.wires p ⊆ newSource.toFinset :=
  wires_new_of (row2_oldWithin.1 p hp) (fun w h1 hw => newSource_of_old w h1
    (fun hm => row2_placed_old _ hp w (by simp [hm]) hw))


theorem row2_look_new (c : Option Wire) (ps : List (LookupPort 32768)) (hp : WInstr.lookup c ps ∈ erase row2) :
    (∀ q ∈ c, q ∈ newSource) ∧ portTargets ps ⊆ newSource := by
  have h1 := row2_oldWithin.2 c ps hp
  have h2 := row2_placed_old _ hp
  dsimp only [PlacedPair] at h2
  refine ⟨fun q hq => newSource_of_old q (h1.1 q hq) fun hm => ?_, fun w hw => newSource_of_old w (h1.2 hw) fun hm => ?_⟩
  · have hq' : lookupRoot windowRoot c = q := by
      cases c with
      | none => simp at hq
      | some q' => simp only [Option.mem_def, Option.some.injEq] at hq; simp [lookupRoot, hq]
    have h0 := h2.1
    rw [List.cons_append] at h0
    have hn := (List.nodup_cons.mp h0).1
    exact hn (by rw [hq']; exact List.mem_append_right _ hm)
  · exact List.disjoint_left.mp h2.2.2.2 (by simp [hm]) hw

theorem addFixedP_support (start : Nat) : ChallengeMigration.straightWires (addFixedP start) ⊆ newSource := by
  rw [addFixedP,support_cast]
  apply programP_support bank15 bank15_ok row2 row2_geo15 newSource
  · exact newSource_of_bounds [windowRoot] (by decide +kernel) (List.mem_singleton_self _)
  · exact newSource_of_bounds _ (by simp only [bank15, windowBits]; decide +kernel)
  · exact newSource_of_bounds _ (by simp only [bank15, pathBank]; decide +kernel)
  · intro i
    exact newSource_of_bounds [low i] (by
      have hi := i.isLt
      intro w hw
      simp only [List.mem_singleton] at hw
      subst hw
      simp only [low, fixedPort, oldWork, retired]
      omega) (List.mem_singleton_self _)
  · exact newSource_of_bounds _ (by simp only [bank15, WEXUnlookup.high]; decide +kernel)
  · exact row2_lit_new
  · exact row2_look_new

def rowSourceP (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  sourceCodeP bank15 (readConstant coeffs Q) row2

theorem rowSourceP_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) :
    CoherentlyImplementsOn (rowSourceP coeffs Q) (Finsupp.lmapDomain ℂ ℂ (rowPointState coeffs Q)) LiveReady := by
  have h := program_coherentP (readConstant coeffs Q) bank15 bank15_ok row2 row2_geo15 liveReady
    (rowPointState coeffs Q)
    (fun s hs => (row2_safe_run coeffs Q hQ hn _ s hs).1)
    (fun s hs => row2_clean pathBank pathBank_pool pathBank_flip pathBank_head coeffs Q hQ hn _ s hs)
    (fun s hs m => row2_run_any _ coeffs Q hQ hn s hs m) 0 Fin.elim0
  obtain ⟨cs,aligned,mass⟩ := h
  refine ⟨cs,?_,mass⟩
  rw [programP_run] at aligned
  exact aligned.imp (fun b c hb s hs => hb s ⟨hs.1.2.2, hs.1⟩)

def fastMiddleSource (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  (fastSignSource.seq (rowSourceP coeffs Q)).seq fastSignSource

theorem fastMiddle_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) :
    CoherentlyImplementsOn (fastMiddleSource coeffs Q) (Finsupp.lmapDomain ℂ ℂ (middleState coeffs Q)) LiveReady := by
  have first := composeCoherent fastSign_coherent (rowSourceP_coherent coeffs Q hQ hn)
    (fun s hs => live_write _ s hs)
  exact composeCoherent (f := fun s => rowPointState coeffs Q (signPointState s)) (g := signPointState)
    first fastSign_coherent (fun s hs => live_write _ _ (live_write _ s hs))

def fastBodySource (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  (prefixSource.seq (fastMiddleSource coeffs Q)).seq suffixSource

theorem fastBodySource_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) :
    CoherentlyImplementsOn (fastBodySource coeffs Q) (Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)) Ready := by
  have h := composeCoherent WEXUnlookup.prefix_coherent (fastMiddle_coherent coeffs Q hQ hn)
    (fun s hs => ⟨windowPrepare_live _ (rootFlip_live s hs.1),prefix_hot s hs.2⟩)
  exact composeCoherent (f := fun s => middleState coeffs Q (prefixState s)) (g := suffixState)
    h WEX.suffix_coherent (fun _ _ => True.intro)

def fastBodyProgram (start : Nat) : Straight 32768 start (start+1758490) :=
  castFinish (by omega)
    (((((prefixProgram start).append (nFastProgram start)).append (addFixedP (start+256))).append
      (nFastProgram (start+256+1757978))).append (suffixProgram (start+256+1757978+256)))

attribute [local irreducible] fastBodyProgram addFixedP

theorem fastBodyProgram_run (start : Nat) (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (history : Fin start → Bool) :
    ((fastBodyProgram start).instantiate (readConstant coeffs Q) history).run = (fastBodySource coeffs Q).run := by
  have hr : ((fastBodyProgram start).instantiate (readConstant coeffs Q) history).run =
      ((prefixSource.seq ((fastSignSource.seq (sourceCodeP bank15 (readConstant coeffs Q) row2)).seq
        fastSignSource)).seq suffixSource).run := by
    rw [fastBodyProgram,castFinish_instantiate]
    exact five_run (readConstant coeffs Q) _ _ _ _ _ prefixSource fastSignSource
      (sourceCodeP bank15 (readConstant coeffs Q) row2) fastSignSource suffixSource
      (prefixProgram_run _ _) (nFastProgram_run _ _) (addFixedP_run _ _)
      (nFastProgram_run _ _) (suffixProgram_run _ _) history
  have he : fastBodySource coeffs Q =
      ((prefixSource.seq ((fastSignSource.seq (sourceCodeP bank15 (readConstant coeffs Q) row2)).seq
        fastSignSource)).seq suffixSource) := by
    delta fastBodySource fastMiddleSource rowSourceP
    rfl
  exact hr.trans (congrArg AdaptiveCircuit.run he.symm)

theorem fastBodyProgram_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((fastBodyProgram start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)) Ready := by
  obtain ⟨cs,aligned,mass⟩ := fastBodySource_coherent coeffs Q hQ hn
  refine ⟨cs,?_,mass⟩
  rw [fastBodyProgram_run]
  exact aligned

theorem fastBodyProgram_credit (start : Nat) : ProgramCredit (fastBodyProgram start)
    (2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) + ccx row2) := by
  let a := ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)
  have hl : ProgramCredit (nFastProgram start) a := WEX.nFastProgram_credit start
  have hr : ProgramCredit (nFastProgram (start+256+1757978)) a := WEX.nFastProgram_credit _
  rw [fastBodyProgram]
  apply credit_cast
  exact five_credit a (ccx row2) (prefix_credit start) hl (addFixedP_credit (start+256)) hr
    (suffix_credit (start+256+1757978+256))

theorem fastBodyProgram_tCount (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((fastBodyProgram start).instantiate read history).tCount =
      7*(2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) + ccx row2) := by
  have hc := fastBodyProgram_credit start
  have h := exact_t (fastBodyProgram start) hc.1 read history
  rw [hc.2] at h
  exact h

theorem fastBodyProgram_wellFormed (start : Nat) : (fastBodyProgram start).WellFormed := by
  rw [fastBodyProgram,castFinish_wellFormed]
  apply straight_append_wellFormed
  · apply straight_append_wellFormed
    · apply straight_append_wellFormed
      · exact straight_append_wellFormed _ _ (prefixProgram_wellFormed start) (nFastProgram_wellFormed start)
      · exact addFixedP_wellFormed _
    · exact nFastProgram_wellFormed _
  · exact suffixProgram_wellFormed _

theorem nFast_new (start : Nat) : ChallengeMigration.straightWires (nFastProgram start) ⊆ newSource := by
  apply literalFixed_support (n := 32768) (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram) 256
    ((literal_meas (n := 32768) _).trans fastWindowSign_normalized_counts.2) newSource (start := start)
  rw [ECDSAAdd.Baselines.normalize_wires]
  have hs := WEX.finiteSignMeasured_support (negateYLayout streamLayout) 870 838 streamLayout.core.generic ECDSAAdd.p
  have cover : 870 :: 838 :: (negateYLayout streamLayout).wires streamLayout.core.generic ⊆ newSource := by
    apply newSource_of_bounds; decide +kernel
  have sub : ECDSAAdd.wires fastWindowSignProgram ⊆ ECDSAAdd.wires
      (WEX.finiteSignMeasured (negateYLayout streamLayout) 870 838 streamLayout.core.generic ECDSAAdd.p) := by
    simp only [fastWindowSignProgram, WEX.finiteSignMeasured, ECDSAAdd.wires_append]
    exact Finset.union_subset_union (Finset.union_subset_union (fun _ h => h) WEX.TrimmedSign.reflection_wires)
      (fun _ h => h)
  exact sub.trans (hs.trans (fun w hw => List.mem_toFinset.mpr (cover (List.mem_toFinset.mp hw))))

theorem fastBodyProgram_support (start : Nat) :
    ChallengeMigration.straightWires (fastBodyProgram start) ⊆ newSource := by
  have hp : ChallengeMigration.straightWires (prefixProgram start) ⊆ newSource := by
    rw [prefixProgram,straightWires_append,literalProgram_support,literalProgram_support]
    apply newSource_of_bounds
    decide +kernel
  have hs (j : Nat) : ChallengeMigration.straightWires (suffixProgram j) ⊆ newSource := by
    rw [suffixProgram,straightWires_append,literalProgram_support,literalProgram_support]
    apply newSource_of_bounds
    decide +kernel
  rw [fastBodyProgram,support_cast]
  simp only [straightWires_append,List.append_subset]
  exact ⟨⟨⟨⟨hp,nFast_new _⟩,addFixedP_support _⟩,nFast_new _⟩,hs _⟩

attribute [local irreducible] WEX.literalSlotSum WEX.portTotal WEX.traversals in
theorem fastBodyProgram_slots_upper (start : Nat) : (fastBodyProgram start).gateSlots ≤ 2000000000 := by
  rw [fastBodyProgram,castFinish_gateSlots]
  simp only [Straight.gateSlots_append,nFastProgram_slots,addFixedP_slots,
    prefixProgram,suffixProgram,literalProgram_slots]
  have len : (signedAddressCircuit 836 870 windowBits).length = 30 := by decide +kernel
  simp only [len,List.length_cons,List.length_nil]
  have hc := WEX.codeSlots_bound windowBits (normalizeW (erase row2))
  rw [literalSlotSum_normalize,portTotal_normalize,traversals_normalize] at hc
  have hl := WEX.clearReferenceRow_literal_slots_bound
  have hp := WEX.clearReferenceRow_portTotal
  have hm := WEXUnlookup.row2_measures
  have hl2 := hm.2.2.1
  rw [← hm.2.2.2.1] at hp
  rw [hm.2.1] at hc
  have sign := literal_slot_bound (n := 32768) (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)
  rw [ECDSAAdd.Baselines.normalize_slots] at sign
  have bound := fastWindowSign_slots
  norm_num [windowBits] at hc
  simp only [windowBits]
  omega

def compactProgram (start : Nat) : Straight 32768 start (start+1758490) :=
  relabelStraight pi (fastBodyProgram start)

end
end ShorECDLP.Entrant.PathShare.W15

/-! ### The width-14 body on the pool bank -/

namespace ShorECDLP.Entrant.PathShare.W14
open Quantum Challenge AndGadget WEXCredit Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
open ShorECDLP.Entrant.Schedule33.Flexible ShorECDLP.Entrant.PathShare
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

theorem lay14 : ∀ b ∈ row2, BlockLay bank14 b := fun b hb => geo_lay bank14 bank14_ok b (row2_geo14 b hb)

theorem old14_lay : ∀ b ∈ row2, BlockLay old14 b := by
  intro b hb
  have hg := WEXUnlookupWidth14.row2_geometry b hb
  cases b with
  | plain code =>
    exact pair_layouts_of_placed _ _ _ _ (by simp [old14,WEXUnlookupWidth14.bits,WEX.widthBits,windowPaths])
      (pair_placed_normalize _ _ _ _ hg.1)
  | masked site =>
    have hp : ∀ i ∈ site.prefix, PlacedPair WEXUnlookupWidth14.bits windowPaths windowRoot i := fun i hi =>
      placed_implies_pair _ _ _ _ (hg.placed i (List.mem_append_left _ hi))
    exact ⟨pair_layouts_of_placed _ _ _ _ (by simp [old14,WEXUnlookupWidth14.bits,WEX.widthBits,windowPaths])
      (pair_placed_normalize _ _ _ _ hp), WEXUnlookupWidth14.site_high_layout site hg.original⟩

theorem recordsP_old14 (code : Code 32768) : recordsP old14 code = WEXUnlookupWidth14.records code := by
  induction code with
  | nil => rfl
  | cons b code ih =>
    simp only [recordsP, WEXUnlookupWidth14.records, ih]
    cases b <;> rfl

theorem row2_recordsP : recordsP bank14 row2 = 1659034 := by
  rw [recordsP_eq bank14 old14 rfl rfl row2 lay14 old14_lay, recordsP_old14]
  exact WEXUnlookupWidth14.row2_records

theorem codeTP14 (code : Code 32768) : codeTP bank14 code = WEXUnlookupWidth14.ccx code := by
  induction code with
  | nil => rfl
  | cons b code ih =>
    have hl : 2 ^ bank14.bits.length - 1 = 16383 := by simp [bank14, WEXUnlookupWidth14.bits, WEX.widthBits]
    have hn : (tableAddressTree bank14.high 0 1).internalNodes = 127 := WEXUnlookupWidth14.high_nodes
    simp only [codeTP, WEXUnlookupWidth14.ccx, ih]
    cases b <;> simp only [blockTP, WEXUnlookupWidth14.blockCCX, hl, hn]

theorem program_slots_old14 (code : Code 32768) (hl : ∀ b ∈ code, BlockLay old14 b) (start : Nat) :
    (WEXUnlookupWidth14.program code start).gateSlots = codeSP old14 code := by
  induction code generalizing start with
  | nil => rfl
  | cons b code ih =>
    have hb : (WEXUnlookupWidth14.blockProgram b start).gateSlots = (blockProgP old14 b start).gateSlots := by
      cases b <;> rfl
    rw [WEXUnlookupWidth14.program, castFinish_gateSlots, Straight.gateSlots_append,
      ih (fun d hd => hl d (by simp [hd])), hb, blockProgP_slots old14 b (hl b (by simp))]
    rfl

attribute [local irreducible] programP blockProgP clearP WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  WEX.literalToffolis WEX.normalizeW WEXUnlookupWidth14.ccx Nat.add Nat.mul

def addFixedP (start : Nat) : Straight 32768 start (start+1659034) :=
  castFinish (congrArg (fun m => start+m) row2_recordsP) (programP bank14 row2 start)

theorem addFixedP_run (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((addFixedP start).instantiate read history).run = (sourceCodeP bank14 read row2).run := by
  rw [addFixedP,castFinish_instantiate,programP_run]

theorem addFixedP_tCount (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((addFixedP start).instantiate read history).tCount = 7*WEXUnlookupWidth14.ccx row2 := by
  rw [addFixedP,castFinish_instantiate,programP_tCount read bank14 row2 lay14,codeTP14]

theorem addFixedP_slots_upper (start : Nat) : (addFixedP start).gateSlots ≤ 1000000000 := by
  rw [addFixedP,castFinish_gateSlots,programP_slots bank14 row2 lay14,codeSP_congr bank14 old14 rfl rfl,
    ← program_slots_old14 row2 old14_lay start]
  exact WEXUnlookupWidth14.row2_slots_upper start

theorem addFixedP_wellFormed (start : Nat) : (addFixedP start).WellFormed := by
  rw [addFixedP,castFinish_wellFormed]
  exact programP_wellFormed bank14 bank14_ok row2 row2_geo14 row2_physical start

theorem addFixedP_residue (start : Nat) : residue (addFixedP start) = 0 := by
  rw [addFixedP,residue_cast]
  exact programP_residue bank14 row2 start

theorem addFixedP_credit (start : Nat) : ProgramCredit (addFixedP start) (WEXUnlookupWidth14.ccx row2) := by
  have hz := addFixedP_residue start
  refine ⟨hz,?_⟩
  have he := exact_t (addFixedP start) hz (fun _ => false) (fun _ => false)
  have ht := addFixedP_tCount (fun _ => false) start (fun _ => false)
  omega

theorem addFixedP_support (start : Nat) : ChallengeMigration.straightWires (addFixedP start) ⊆ newSource := by
  rw [addFixedP,support_cast]
  apply programP_support bank14 bank14_ok row2 row2_geo14 newSource
  · exact newSource_of_bounds [windowRoot] (by decide +kernel) (List.mem_singleton_self _)
  · exact newSource_of_bounds _ (by simp only [bank14, WEXUnlookupWidth14.bits, WEX.widthBits]; decide +kernel)
  · exact newSource_of_bounds _ (by simp only [bank14, pathBank]; decide +kernel)
  · intro i
    exact newSource_of_bounds [low i] (by
      have hi := i.isLt
      intro w hw
      simp only [List.mem_singleton] at hw
      subst hw
      simp only [low, fixedPort, oldWork, retired]
      omega) (List.mem_singleton_self _)
  · exact newSource_of_bounds _ (by simp only [bank14, WEXUnlookupWidth14.high]; decide +kernel)
  · exact W15.row2_lit_new
  · exact W15.row2_look_new

def rowSourceP (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  sourceCodeP bank14 (readConstant coeffs Q) row2

theorem rowSourceP_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (halias : WEX.WidthAliased 14 coeffs) :
    CoherentlyImplementsOn (rowSourceP coeffs Q) (Finsupp.lmapDomain ℂ ℂ (rowPointState coeffs Q)) LiveReady := by
  have h := program_coherentP (readConstant coeffs Q) bank14 bank14_ok row2 row2_geo14 liveReady
    (WEXUnlookupWidth14.rowState coeffs Q)
    (fun s hs => (row2_safe_run coeffs Q hQ hn _ s hs).1)
    (fun s hs => row2_clean pathBank pathBank_pool pathBank_flip pathBank_head coeffs Q hQ hn _ s hs)
    (fun s hs m => by
      simpa only [WEXUnlookupWidth14.rowState] using
        row2_run_any (tableAddressValue WEXUnlookupWidth14.bits s) coeffs Q hQ hn s hs m) 0 Fin.elim0
  have he : WEXUnlookupWidth14.rowState coeffs Q = rowPointState coeffs Q := by
    funext s
    unfold WEXUnlookupWidth14.rowState rowPointState
    rw [show tableAddressValue WEXUnlookupWidth14.bits s = tableAddressValue (WEX.widthBits 14) s from rfl,
      WEX.width_table 14 (by omega) coeffs Q halias s]
  rw [he] at h
  obtain ⟨cs,aligned,mass⟩ := h
  refine ⟨cs,?_,mass⟩
  rw [programP_run] at aligned
  exact aligned.imp (fun b c hb s hs => hb s ⟨hs.1.2.2, hs.1⟩)

def fastMiddleSource (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  (fastSignSource.seq (rowSourceP coeffs Q)).seq fastSignSource

theorem fastMiddle_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (halias : WEX.WidthAliased 14 coeffs) :
    CoherentlyImplementsOn (fastMiddleSource coeffs Q) (Finsupp.lmapDomain ℂ ℂ (middleState coeffs Q)) LiveReady := by
  have first := composeCoherent fastSign_coherent (rowSourceP_coherent coeffs Q hQ hn halias)
    (fun s hs => live_write _ s hs)
  exact composeCoherent (f := fun s => rowPointState coeffs Q (signPointState s)) (g := signPointState)
    first fastSign_coherent (fun s hs => live_write _ _ (live_write _ s hs))

def fastBodySource (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  (prefixSource.seq (fastMiddleSource coeffs Q)).seq suffixSource

theorem fastBodySource_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (halias : WEX.WidthAliased 14 coeffs) :
    CoherentlyImplementsOn (fastBodySource coeffs Q) (Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)) Ready := by
  have h := composeCoherent WEXUnlookup.prefix_coherent (fastMiddle_coherent coeffs Q hQ hn halias)
    (fun s hs => ⟨windowPrepare_live _ (rootFlip_live s hs.1),prefix_hot s hs.2⟩)
  exact composeCoherent (f := fun s => middleState coeffs Q (prefixState s)) (g := suffixState)
    h WEX.suffix_coherent (fun _ _ => True.intro)

def fastBodyProgram (start : Nat) : Straight 32768 start (start+1659546) :=
  castFinish (by omega)
    (((((prefixProgram start).append (nFastProgram start)).append (addFixedP (start+256))).append
      (nFastProgram (start+256+1659034))).append (suffixProgram (start+256+1659034+256)))

attribute [local irreducible] fastBodyProgram addFixedP

theorem fastBodyProgram_run (start : Nat) (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (history : Fin start → Bool) :
    ((fastBodyProgram start).instantiate (readConstant coeffs Q) history).run = (fastBodySource coeffs Q).run := by
  have hr : ((fastBodyProgram start).instantiate (readConstant coeffs Q) history).run =
      ((prefixSource.seq ((fastSignSource.seq (sourceCodeP bank14 (readConstant coeffs Q) row2)).seq
        fastSignSource)).seq suffixSource).run := by
    rw [fastBodyProgram,castFinish_instantiate]
    exact five_run (readConstant coeffs Q) _ _ _ _ _ prefixSource fastSignSource
      (sourceCodeP bank14 (readConstant coeffs Q) row2) fastSignSource suffixSource
      (prefixProgram_run _ _) (nFastProgram_run _ _) (addFixedP_run _ _)
      (nFastProgram_run _ _) (suffixProgram_run _ _) history
  have he : fastBodySource coeffs Q =
      ((prefixSource.seq ((fastSignSource.seq (sourceCodeP bank14 (readConstant coeffs Q) row2)).seq
        fastSignSource)).seq suffixSource) := by
    delta fastBodySource fastMiddleSource rowSourceP
    rfl
  exact hr.trans (congrArg AdaptiveCircuit.run he.symm)

theorem fastBodyProgram_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (halias : WEX.WidthAliased 14 coeffs) (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((fastBodyProgram start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)) Ready := by
  obtain ⟨cs,aligned,mass⟩ := fastBodySource_coherent coeffs Q hQ hn halias
  refine ⟨cs,?_,mass⟩
  rw [fastBodyProgram_run]
  exact aligned

theorem fastBodyProgram_credit (start : Nat) : ProgramCredit (fastBodyProgram start)
    (2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) +
      WEXUnlookupWidth14.ccx row2) := by
  let a := ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)
  have hl : ProgramCredit (nFastProgram start) a := WEX.nFastProgram_credit start
  have hr : ProgramCredit (nFastProgram (start+256+1659034)) a := WEX.nFastProgram_credit _
  rw [fastBodyProgram]
  apply credit_cast
  exact five_credit a (WEXUnlookupWidth14.ccx row2) (prefix_credit start) hl (addFixedP_credit (start+256)) hr
    (suffix_credit (start+256+1659034+256))

theorem fastBodyProgram_tCount (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((fastBodyProgram start).instantiate read history).tCount =
      7*(2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) +
        WEXUnlookupWidth14.ccx row2) := by
  have hc := fastBodyProgram_credit start
  have h := exact_t (fastBodyProgram start) hc.1 read history
  rw [hc.2] at h
  exact h

theorem fastBodyProgram_wellFormed (start : Nat) : (fastBodyProgram start).WellFormed := by
  rw [fastBodyProgram,castFinish_wellFormed]
  apply straight_append_wellFormed
  · apply straight_append_wellFormed
    · apply straight_append_wellFormed
      · exact straight_append_wellFormed _ _ (prefixProgram_wellFormed start) (nFastProgram_wellFormed start)
      · exact addFixedP_wellFormed _
    · exact nFastProgram_wellFormed _
  · exact suffixProgram_wellFormed _

theorem fastBodyProgram_support (start : Nat) :
    ChallengeMigration.straightWires (fastBodyProgram start) ⊆ newSource := by
  have hp : ChallengeMigration.straightWires (prefixProgram start) ⊆ newSource := by
    rw [prefixProgram,straightWires_append,literalProgram_support,literalProgram_support]
    apply newSource_of_bounds
    decide +kernel
  have hs (j : Nat) : ChallengeMigration.straightWires (suffixProgram j) ⊆ newSource := by
    rw [suffixProgram,straightWires_append,literalProgram_support,literalProgram_support]
    apply newSource_of_bounds
    decide +kernel
  rw [fastBodyProgram,support_cast]
  simp only [straightWires_append,List.append_subset]
  exact ⟨⟨⟨⟨hp,W15.nFast_new _⟩,addFixedP_support _⟩,W15.nFast_new _⟩,hs _⟩

theorem fastBodyProgram_slots_upper (start : Nat) : (fastBodyProgram start).gateSlots ≤ 1100000000 := by
  have hr := addFixedP_slots_upper (start+256)
  rw [fastBodyProgram,castFinish_gateSlots]
  simp only [Straight.gateSlots_append,nFastProgram_slots,
    prefixProgram,suffixProgram,literalProgram_slots]
  have len : (signedAddressCircuit 836 870 windowBits).length = 30 := by decide +kernel
  simp only [len,List.length_cons,List.length_nil]
  have sign := literal_slot_bound (n := 32768) (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)
  rw [ECDSAAdd.Baselines.normalize_slots] at sign
  have bound := fastWindowSign_slots
  omega

def compactProgram (start : Nat) : Straight 32768 start (start+1659546) :=
  relabelStraight pi (fastBodyProgram start)

end
end ShorECDLP.Entrant.PathShare.W14

/-! ### The body with the pool path bank, and its narrow programs -/

namespace ShorECDLP.Entrant.PathShare
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
open ShorECDLP.Entrant.Schedule33.Flexible
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

attribute [local irreducible] W15.fastBodyProgram W14.fastBodyProgram

def body2 : Single.WindowBody where
  records := 1758490
  tBound := 16536856
  slotBound := 2000000000
  support := List.range 1619
  reset := resetWires
  ready := ready2
  active := ready2_active
  ready_write := ready2_write
  ready_address := ready2_address
  ready_first := ready2_first
  program := W15.compactProgram
  update := state2
  correct := fun coeffs Q _ _ s hs P hP => state2_correct coeffs Q s hs P hP
  coherent := fun coeffs Q hQ hn start history =>
    relabel2_coherent _ coeffs Q history (W15.fastBodyProgram_coherent coeffs Q hQ hn start history)
  wellFormed := fun start => (relabelStraight_wellFormed pi (W15.fastBodyProgram start)).mpr
    (W15.fastBodyProgram_wellFormed start)
  slots := fun start => (relabelStraight_slots pi (W15.fastBodyProgram start)).trans_le
    (W15.fastBodyProgram_slots_upper start)
  tCount := by
    intro coeffs Q start history
    rw [W15.compactProgram,relabelStraight_instantiate,AdaptiveCircuit.relabel_tCount,W15.fastBodyProgram_tCount]
    have h := Width15Fused.fastCount_upper
    omega
  wires := fun start => relabel2_support _ (W15.fastBodyProgram_support start)
  reset_support := fun _ hw => base_support2 (List.mem_cons_of_mem 837 hw)
  skeleton_support := base_support2

def narrow15 : ModNarrow body2 15 where
  records := 1758490
  tBound := 16536856
  credit := 2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) + ccx row2
  program := W15.compactProgram
  coherent := fun coeffs Q hQ hn _ start history => body2.coherent coeffs Q hQ hn start history
  wellFormed := body2.wellFormed
  slots := body2.slots
  wires := body2.wires
  tCount := by
    intro start read history
    rw [W15.compactProgram,relabelStraight_instantiate,AdaptiveCircuit.relabel_tCount,W15.fastBodyProgram_tCount]
    have h := Width15Fused.fastCount_upper
    omega
  zero := by
    intro start
    rw [W15.compactProgram,WEXUnlookup.residue_relabel]
    exact (W15.fastBodyProgram_credit start).1
  count_eq := by
    intro start
    rw [W15.compactProgram,AndGadget.added_relabel]
    exact (W15.fastBodyProgram_credit start).2

def narrow14 : ModNarrow body2 14 where
  records := 1659546
  tBound := 15844248
  credit := 2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) +
    WEXUnlookupWidth14.ccx row2
  program := W14.compactProgram
  coherent := by
    intro coeffs Q hQ hn halias start history
    have ha : WEX.WidthAliased 14 coeffs := by simpa only [WEX.WidthAliased, ModAliased, reducedAddress] using halias
    exact relabel2_coherent _ coeffs Q history (W14.fastBodyProgram_coherent coeffs Q hQ hn ha start history)
  wellFormed := fun start => (relabelStraight_wellFormed pi (W14.fastBodyProgram start)).mpr
    (W14.fastBodyProgram_wellFormed start)
  slots := fun start => (relabelStraight_slots pi (W14.fastBodyProgram start)).trans_le
    ((W14.fastBodyProgram_slots_upper start).trans (by show (1100000000 : Nat) ≤ 2000000000; decide))
  wires := fun start => relabel2_support _ (W14.fastBodyProgram_support start)
  tCount := by
    intro start read history
    rw [W14.compactProgram,relabelStraight_instantiate,AdaptiveCircuit.relabel_tCount,W14.fastBodyProgram_tCount]
    have h := WEXUnlookupWidth14.Fused.fastCount_upper
    omega
  zero := by
    intro start
    rw [W14.compactProgram,WEXUnlookup.residue_relabel]
    exact (W14.fastBodyProgram_credit start).1
  count_eq := by
    intro start
    rw [W14.compactProgram,AndGadget.added_relabel]
    exact (W14.fastBodyProgram_credit start).2

theorem alias13_14 (coeffs : Fin 32768 → PointCoeff) (h : ModAliased 13 coeffs) : ModAliased 14 coeffs := by
  intro a
  have e : reducedAddress 13 (reducedAddress 14 a) = reducedAddress 13 a := by
    apply Fin.ext
    simp only [reducedAddress]
    omega
  rw [h a, h (reducedAddress 14 a), e]

/-- No 14-bit physical windows are scheduled; the width-14 program serves them as well. -/
def narrow13 : ModNarrow body2 13 where
  records := narrow14.records
  tBound := narrow14.tBound
  credit := narrow14.credit
  program := narrow14.program
  coherent := fun coeffs Q hQ hn halias start history =>
    narrow14.coherent coeffs Q hQ hn (alias13_14 coeffs halias) start history
  wellFormed := narrow14.wellFormed
  slots := narrow14.slots
  wires := narrow14.wires
  tCount := narrow14.tCount
  zero := narrow14.zero
  count_eq := narrow14.count_eq

theorem body2_ledger : body2.support.length = 1619 ∧ body2.reset.length = 854 := by
  constructor
  · simp [body2]
  · simp [body2, resetWires]

end
end ShorECDLP.Entrant.PathShare
