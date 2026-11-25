import ShorECDLP.Submission.Entrant.First20Signed
import ShorECDLP.Submission.Entrant.CornerWire

set_option Elab.async false

/-! ### Consolidated from `Schedule26.lean` -/
section
/-! Certified 26-body-window `(258, 204)` sine-windowed Shor ECDLP schedule (`Windowed26`):
- First window: signed 20-bit 5-pass SelectSwap loader (`First20Signed`, `193,625` Toffolis,
  `524,288` `G`-only rows — all frozen during specialization), locally compiled onto scratch wire `0`
  and catalyst wire `1` inside `List.range 1613`.
- Left body: `14` signed 17-bit windows (`14 × 17 = 238`, total left precision `20 + 238 = 258`),
  locally compiled via `LocalWide16.compiledProgram` (`≤ 4 × 2,303,094` T-gates/window, `0` global
  ancilla overhead, catalyst on `compact17_7 15645 = 1`), all `G`-only rows frozen during specialization.
- Right body: `12` signed 17-bit windows (`12 × 17 = 204`, `786,432` retained `Q`-rows + 1 sentinel
  `= 786,433 ≤ 983,040`), locally compiled identically via `LocalWide16.compiledProgram`.
- Top-10 centered sine window prepended to the left head (`First20Signed`) and right head (`right17 0`),
  `2 × 28 = 56` T-model gates (`k ≤ 11`, untouched by `trim 18`), compiled against catalyst wire `1`.
- `K = 3` neighbour readout (`Readout3`, `-1, 0, +1`, `1,634` records, `0` T-gates).
- Exact `trim 18` affine loss: `cost18 ≤ 425 * unit18 ≤ 51 / 10000`, `46,311` Fourier phase gates
  dropped (`7,088` kept), recovery probability `≥ 99 / 100`.
- Certified resource bounds: `1,613` qubits, `240,303,421` T-model gates (`Q×T = 387,609,418,073`),
  `≤ 105,000,000` measurements. -/


namespace ShorECDLP.Entrant.Mixed
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section

theorem branchCoeff_amplitude' (dir : PhaseDir) (ws : List Wire)
    (hws : ws.Nodup) (prior bs : List Bool) (s : BasisState) :
    fourierBranchCoeff dir ws prior bs s = fourierBitAmplitude dir (ws.map s) prior bs := by
  induction ws generalizing prior bs s with
  | nil => cases bs <;> rfl
  | cons w ws ih =>
    cases bs with
    | nil => rfl
    | cons b bs =>
      simp only [fourierBranchCoeff, List.map_cons, fourierBitAmplitude]
      rw [ih (List.nodup_cons.mp hws).2]
      have hm : ws.map (s[w ↦ false]) = ws.map s := by
        apply List.map_congr_left
        intro v hv
        have hvw : v ≠ w := by intro he; subst v; exact (List.nodup_cons.mp hws).1 hv
        simp [upd, hvw]
      rw [hm]

theorem lmap_ket' (f : BasisState → BasisState) (s : BasisState) :
    Finsupp.lmapDomain ℂ ℂ f (ket s) = ket (f s) := by
  simp [ket, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

end
end ShorECDLP.Entrant.Mixed

namespace ShorECDLP.Entrant.Width16Schedule
open Quantum Challenge Secp256k1 Single Single.Distribution
open Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

theorem odd_scalar_ne_zero (P : Point) (hr : order • P = 0) (hp : P ≠ 0)
    (exponent a : Nat) (ha : 2*a+1 < order) : oddScalar exponent a • P ≠ 0 := by
  letI : Fact (Nat.Prime order) := ⟨order_prime⟩
  have ho : addOrderOf P = order := addOrderOf_eq_prime hr hp
  have hs : 0 < 2*a+1 := by omega
  have horder : 2 < order := by norm_num [order]
  have hh : 0 < halfOrder ∧ halfOrder < order := by dsimp [Single.halfOrder]; omega
  have hodd : ¬ order ∣ 2*a+1 := fun h => (Nat.le_of_dvd hs h).not_gt ha
  have hhalf : ¬ order ∣ halfOrder := fun h => (Nat.le_of_dvd hh.1 h).not_gt hh.2
  have htwo : ¬ order ∣ 2 := by
    intro h
    have hl : 2 < order := by norm_num [order]
    exact (Nat.le_of_dvd (by decide +kernel : 0 < 2) h).not_gt hl
  intro hz
  have he : ((2*a+1)*2^exponent*halfOrder) • P = 0 := by simpa only [oddScalar] using hz
  have hd := addOrderOf_dvd_iff_nsmul_eq_zero.mpr he
  rw [ho] at hd
  rcases order_prime.dvd_mul.mp hd with hd | hd
  · rcases order_prime.dvd_mul.mp hd with hd | hd
    · exact hodd hd
    · exact htwo (order_prime.dvd_of_dvd_pow hd)
  · exact hhalf hd


def increment (P : Point) (width exponent v : Nat) : Point :=
  ((2*(v:Int)-(2:Int)^width+1):Int) • ((halfOrder*2^exponent) • P)

theorem increment_offset (P : Point) (hr : order • P = 0)
    (width exponent v : Nat) (hw : width = 16 ∨ width = 17) :
    increment P width exponent v + offsetScalar width exponent • P = (v*2^exponent) • P := by
  have hh : halfOrder ≤ 2^(width-1)+order := by
    have hl : halfOrder ≤ order := by
      have horder : 0 < order := by norm_num [order]
      dsimp [Single.halfOrder]
      omega
    exact hl.trans (Nat.le_add_left _ _)
  have he : (2^(width-1)+order-halfOrder) • P + halfOrder • P = 2^(width-1) • P := by
    rw [← add_nsmul, Nat.sub_add_cancel hh, add_nsmul, hr, add_zero]
  have hoff : offsetScalar width exponent • P =
      2^(width-1) • (2^exponent • P) - (halfOrder*2^exponent) • P := by
    unfold offsetScalar
    rw [mul_smul, smul_comm (2^(width-1)+order-halfOrder) (2^exponent),
      eq_sub_iff_add_eq.mpr he, nsmul_sub]
    simp only [mul_smul]
    rw [smul_comm (2^exponent) (2^(width-1)), smul_comm (2^exponent) halfOrder]
  let H := (halfOrder*2^exponent) • P
  have hd : H+H = 2^exponent • P := by
    change (halfOrder*2^exponent) • P + (halfOrder*2^exponent) • P = _
    rw [mul_smul, smul_comm halfOrder (2^exponent), ← nsmul_add]
    exact congrArg (fun R : Point => 2^exponent • R)
      (signedWindowHalfPoint_double P order (by decide +kernel) hr)
  have hp : (2:Int)^width = 2*(2^(width-1):Nat) := by rcases hw with rfl | rfl <;> norm_num
  have hcalc : ((2*(v:Int)-(2:Int)^width+1) • H) +
      (2^(width-1) • (H+H)-H) = v • (H+H) := by rw [hp]; module
  change ((2*(v:Int)-(2:Int)^width+1) • H) + _ = _
  rw [hoff]
  simp only [hd] at hcalc
  exact hcalc.trans (mul_smul v (2^exponent) P).symm

end
end ShorECDLP.Entrant.Width16Schedule

namespace ShorECDLP.Entrant.Width16Schedule.Specialization
open ShorECDLP.Challenge ShorECDLP.Quantum ShorECDLP.Secp256k1

def specializeGate {n m : Nat} (classify : ConstantBit n → Bool ⊕ ConstantBit m)
    (zero : ConstantBit m) : TemplateGate n → TemplateGate m
  | .literal g => .literal g
  | .whenBit r v g =>
      match classify r with
      | .inl b => if b = v then .literal g else .whenBit zero true g
      | .inr r' => .whenBit r' v g

def specialize {n m s e : Nat} (classify : ConstantBit n → Bool ⊕ ConstantBit m)
    (zero : ConstantBit m) : Straight n s e → Straight m s e
  | .done => .done
  | .gate g p => .gate (specializeGate classify zero g) (specialize classify zero p)
  | .recordGate i v g p => .recordGate i v g (specialize classify zero p)
  | .measure w p => .measure w (specialize classify zero p)

theorem specializeGate_instantiate {n m : Nat}
    (classify : ConstantBit n → Bool ⊕ ConstantBit m) (zero : ConstantBit m)
    (old : ConstantBit n → Bool) (fresh : ConstantBit m → Bool)
    (hz : fresh zero = false)
    (agree : ∀ r, old r = (classify r).elim id fresh) (g : TemplateGate n) :
    (specializeGate classify zero g).instantiate fresh = g.instantiate old := by
  cases g with
  | literal g => rfl
  | whenBit r v g =>
    have hr := agree r
    cases hc : classify r with
    | inl b =>
      simp only [hc, Sum.elim_inl, id_eq] at hr
      by_cases h : b = v <;> simp [specializeGate, hc, TemplateGate.instantiate, hr, hz, h]
    | inr r' =>
      simp only [hc, Sum.elim_inr] at hr
      simp [specializeGate, hc, TemplateGate.instantiate, hr]

theorem specialize_instantiate {n m s e : Nat}
    (classify : ConstantBit n → Bool ⊕ ConstantBit m) (zero : ConstantBit m)
    (old : ConstantBit n → Bool) (fresh : ConstantBit m → Bool)
    (hz : fresh zero = false)
    (agree : ∀ r, old r = (classify r).elim id fresh)
    (p : Straight n s e) (history : Fin s → Bool) :
    (specialize classify zero p).instantiate fresh history = p.instantiate old history := by
  induction p with
  | done => rfl
  | gate g p ih =>
    simp only [specialize, Straight.instantiate,
      specializeGate_instantiate classify zero old fresh hz agree, ih]
  | recordGate i v g p ih => simp only [specialize, Straight.instantiate, ih]
  | measure w p ih => simp only [specialize, Straight.instantiate, ih]

theorem specializeGate_wellFormed {n m : Nat}
    (classify : ConstantBit n → Bool ⊕ ConstantBit m) (zero : ConstantBit m)
    (g : TemplateGate n) :
    (specializeGate classify zero g).WellFormed = g.WellFormed := by
  cases g with
  | literal g => rfl
  | whenBit r v g =>
    cases hc : classify r with
    | inl b => simp only [specializeGate, hc]; split <;> rfl
    | inr r' => simp only [specializeGate, hc, TemplateGate.WellFormed]

theorem specialize_wellFormed {n m s e : Nat}
    (classify : ConstantBit n → Bool ⊕ ConstantBit m) (zero : ConstantBit m)
    (p : Straight n s e) :
    (specialize classify zero p).WellFormed = p.WellFormed := by
  induction p with
  | done => rfl
  | gate g p ih => simp only [specialize, Straight.WellFormed, specializeGate_wellFormed, ih]
  | recordGate i v g p ih => simp only [specialize, Straight.WellFormed, ih]
  | measure w p ih => exact ih

theorem specialize_slots {n m s e : Nat}
    (classify : ConstantBit n → Bool ⊕ ConstantBit m) (zero : ConstantBit m)
    (p : Straight n s e) : (specialize classify zero p).gateSlots = p.gateSlots := by
  induction p with
  | done => rfl
  | gate g p ih => simp only [specialize, Straight.gateSlots, ih]
  | recordGate i v g p ih => simp only [specialize, Straight.gateSlots, ih]
  | measure w p ih => exact ih

theorem generator_only_constantPoint (c : PointCoeff) (hb : c.b.val = 0) (Q R : Point) :
    constantPoint Q c = constantPoint R c := by
  simp [constantPoint, hb]

theorem generator_only_readConstant {n : Nat} (coeffs : Fin n → PointCoeff)
    (r : ConstantBit n) (hb : (coeffs r.point).b.val = 0) (Q R : Point) :
    readConstant coeffs Q r = readConstant coeffs R r := by
  unfold readConstant
  rw [generator_only_constantPoint (coeffs r.point) hb Q R]

def specializeEntry (e : StraightEntry) (coeffs : List PointCoeff)
    (classify : ConstantBit e.coefficients.length → Bool ⊕ ConstantBit coeffs.length)
    (zero : ConstantBit coeffs.length) : StraightEntry where
  coefficients := coeffs
  finalCursor := e.finalCursor
  program := specialize classify zero e.program

theorem specializeEntry_instantiate (e : StraightEntry) (coeffs : List PointCoeff)
    (classify : ConstantBit e.coefficients.length → Bool ⊕ ConstantBit coeffs.length)
    (zero : ConstantBit coeffs.length) (Q : Point)
    (hz : readConstant coeffs.get Q zero = false)
    (agree : ∀ r, readConstant e.coefficients.get Q r =
      (classify r).elim id (readConstant coeffs.get Q)) :
    (specializeEntry e coeffs classify zero).instantiate Q = e.instantiate Q :=
  specialize_instantiate classify zero _ _ hz agree e.program Fin.elim0

theorem specialize_certificate (limits : Limits) (layout : DecodeLayout)
    (e : StraightEntry) (bounds : Bounds) (coeffs : List PointCoeff)
    (classify : ConstantBit e.coefficients.length → Bool ⊕ ConstantBit coeffs.length)
    (zero : ConstantBit coeffs.length)
    (hz : ∀ Q, readConstant coeffs.get Q zero = false)
    (agree : ∀ Q r, readConstant e.coefficients.get Q r =
      (classify r).elim id (readConstant coeffs.get Q))
    (h : Certificate { limits with coefficientRows := e.coefficients.length } layout e bounds)
    (ht : coeffs.length ≤ limits.coefficientRows) :
    Certificate limits layout (specializeEntry e coeffs classify zero) bounds := by
  have he (Q : Point) := specializeEntry_instantiate e coeffs classify zero Q (hz Q) (agree Q)
  refine ⟨?_, h.recordBudget, ht, h.candidateBudget, ?_, ?_, ?_⟩
  · simpa only [specializeEntry, specialize_slots] using h.gateBudget
  · exact (specialize_wellFormed classify zero e.program).mpr h.wellFormed
  · intro Q
    rw [he Q]
    exact h.resources Q
  · intro Q d hn hd
    rw [he Q]
    exact h.success Q d hn hd

-- Entry-level statements keep the very large program abstract during elaboration.
theorem specializeEntry_properties (e : StraightEntry) (coeffs : List PointCoeff)
    (classify : ConstantBit e.coefficients.length → Bool ⊕ ConstantBit coeffs.length)
    (zero : ConstantBit coeffs.length) :
    (specializeEntry e coeffs classify zero).program.gateSlots = e.program.gateSlots ∧
    (specializeEntry e coeffs classify zero).program.WellFormed = e.program.WellFormed ∧
    (specializeEntry e coeffs classify zero).finalCursor = e.finalCursor ∧
    (specializeEntry e coeffs classify zero).coefficients.length = coeffs.length :=
  ⟨specialize_slots classify zero e.program, specialize_wellFormed classify zero e.program, rfl, rfl⟩

theorem specialize_certificate_same_limits (limits : Limits) (layout : DecodeLayout)
    (e : StraightEntry) (bounds : Bounds) (coeffs : List PointCoeff)
    (classify : ConstantBit e.coefficients.length → Bool ⊕ ConstantBit coeffs.length)
    (zero : ConstantBit coeffs.length)
    (hz : ∀ Q, readConstant coeffs.get Q zero = false)
    (agree : ∀ Q r, readConstant e.coefficients.get Q r =
      (classify r).elim id (readConstant coeffs.get Q))
    (h : Certificate limits layout e bounds)
    (ht : coeffs.length ≤ limits.coefficientRows) :
    Certificate limits layout (specializeEntry e coeffs classify zero) bounds := by
  apply specialize_certificate limits layout e bounds coeffs classify zero hz agree
  · exact ⟨h.gateBudget, h.recordBudget, le_rfl, h.candidateBudget,
      h.wellFormed, h.resources, h.success⟩
  · exact ht

end ShorECDLP.Entrant.Width16Schedule.Specialization


namespace ShorECDLP.Entrant.Width16Schedule
open Quantum Challenge Secp256k1 Single Single.Distribution Specialization
open Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
attribute [local irreducible] List.ofFn Straight.instantiate StraightEntry.instantiate
  Straight.gateSlots Straight.WellFormed AdaptiveCircuit.run ShorECDLP.Challenge.resources
local instance bodyInst : Single.WindowBody := PathShare.bodyCF
local instance : Single.ProducerResources bodyInst :=
  Single.ProducerResources.ofBody PathShare.bodyCF
    (by change resetWires.Nodup; exact resetWires_nodup)
    (by change (0 : Wire) ∈ resetWires; decide)
    (by change (1 : Wire) ∈ resetWires; decide)

theorem tableLength {n : Nat} (f : Fin n → PointCoeff) (l : List PointCoeff)
    (h : l=List.ofFn f) : l.length=n := by
  subst l
  exact List.length_ofFn

theorem table_get {n : Nat} (f : Fin n → PointCoeff) (l : List PointCoeff)
    (h : l=List.ofFn f) (hl : l.length=n) (i : Fin l.length) : l.get i=f (Fin.cast hl i) := by
  subst l
  simp only [List.get_eq_getElem,List.getElem_ofFn]
  rfl


def canonicalProgram {n : Nat} (f : Fin n → PointCoeff) (e : StraightEntry)
    (he : e.coefficients=List.ofFn f) : Straight n 0 e.finalCursor :=
  reindexStraight (Fin.cast (tableLength f e.coefficients he)) e.program

def canonicalEntry {n : Nat} (f : Fin n → PointCoeff) (e : StraightEntry)
    (he : e.coefficients=List.ofFn f) : StraightEntry := Single.fixedEntry f (canonicalProgram f e he)

theorem canonical_read {n : Nat} (f : Fin n → PointCoeff) (e : StraightEntry)
    (he : e.coefficients=List.ofFn f) (Q : Point) :
    readConstant f Q ∘ reindexBit (Fin.cast (tableLength f e.coefficients he)) =
      readConstant e.coefficients.get Q := by
  funext r
  simp only [Function.comp_def,reindexBit,readConstant]
  rw [table_get f e.coefficients he (tableLength f e.coefficients he) r.point]

theorem canonical_instantiate {n : Nat} (f : Fin n → PointCoeff) (e : StraightEntry)
    (he : e.coefficients=List.ofFn f) (Q : Point) :
    (canonicalEntry f e he).instantiate Q=e.instantiate Q := by
  rw [canonicalEntry,Single.fixedEntry_instantiate,canonicalProgram,reindexStraight_instantiate,
    canonical_read f e he Q]
  unfold StraightEntry.instantiate
  rfl

theorem canonical_certificate {n : Nat} (f : Fin n → PointCoeff) (e : StraightEntry)
    (he : e.coefficients=List.ofFn f) (limits : Limits) (layout : DecodeLayout) (bounds : Bounds)
    (h : Certificate limits layout e bounds) : Certificate limits layout (canonicalEntry f e he) bounds := by
  refine ⟨?_,h.recordBudget,?_,h.candidateBudget,?_,?_,?_⟩
  · simpa only [canonicalEntry,Single.fixedEntry_slots,canonicalProgram,reindexStraight_gateSlots] using h.gateBudget
  · rw [canonicalEntry,Single.fixedEntry_rows]
    have ht := h.tableBudget
    rw [tableLength f e.coefficients he] at ht
    exact ht
  · rw [canonicalEntry,Single.fixedEntry_wellFormed,canonicalProgram,reindexStraight_wellFormed]
    exact h.wellFormed
  · intro Q
    rw [canonical_instantiate]
    exact h.resources Q
  · intro Q d hn hd
    rw [canonical_instantiate]
    exact h.success Q d hn hd

theorem fixed_specialize_certificate {n m e : Nat} (f : Fin n → PointCoeff) (fresh : Fin m → PointCoeff)
    (classifier : ConstantBit n → Bool ⊕ ConstantBit m) (zero : ConstantBit m)
    (hz : ∀ Q,readConstant fresh Q zero=false)
    (agree : ∀ Q r,readConstant f Q r=(classifier r).elim id (readConstant fresh Q))
    (p : Straight n 0 e) (limits : Limits) (layout : DecodeLayout) (bounds : Bounds)
    (h : Certificate { limits with coefficientRows:=n } layout (Single.fixedEntry f p) bounds)
    (ht : m ≤ limits.coefficientRows) :
    Certificate limits layout (Single.fixedEntry fresh (specialize classifier zero p)) bounds := by
  have hi (Q : Point) :
      (Single.fixedEntry fresh (specialize classifier zero p)).instantiate Q=(Single.fixedEntry f p).instantiate Q := by
    rw [Single.fixedEntry_instantiate,Single.fixedEntry_instantiate]
    exact specialize_instantiate classifier zero _ _ (hz Q) (agree Q) p Fin.elim0
  refine ⟨?_,h.recordBudget,?_,h.candidateBudget,?_,?_,?_⟩
  · rw [Single.fixedEntry_slots,specialize_slots]
    simpa only [Single.fixedEntry_slots] using h.gateBudget
  · rw [Single.fixedEntry_rows]
    exact ht
  · rw [Single.fixedEntry_wellFormed,specialize_wellFormed]
    exact (Single.fixedEntry_wellFormed f p).mp h.wellFormed
  · intro Q
    rw [hi Q]
    exact h.resources Q
  · intro Q d hn hd
    rw [hi Q]
    exact h.success Q d hn hd


def reindexWindow {n m : Nat} (rows : Fin n → Fin m) (w : Window n) : Window m :=
  ⟨w.wires,w.count,fun start => reindexStraight rows (w.program start)⟩

/-- Lift an already proved physical model, preserving its full bank, cursor,
    ideal map and validity predicate. No point evaluation is used in construction. -/
def reindexModel {n m : Nat} (old : Fin n → PointCoeff) (fresh : Fin m → PointCoeff)
    (rows : Fin n → Fin m) (hcoeff : ∀ a, old a = fresh (rows a)) (Q : Point)
    (model : WindowModel (readConstant old Q)) : WindowModel (readConstant fresh Q) where
  physical := reindexWindow rows model.physical
  point := model.point
  bias := model.bias
  ideal := model.ideal
  valid := model.valid
  nodup := model.nodup
  coherent := by
    intro start history
    change CoherentlyImplementsOn
      ((reindexStraight rows (model.physical.program start)).instantiate (readConstant fresh Q) history)
      model.ideal model.valid
    rw [reindexStraight_instantiate]
    rw [readConstant_reindex rows old fresh Q (fun a => (hcoeff a).symm)]
    exact model.coherent start history

theorem reindexModel_step {n m : Nat} (old : Fin n → PointCoeff) (fresh : Fin m → PointCoeff)
    (rows : Fin n → Fin m) (hcoeff : ∀ a, old a = fresh (rows a)) (Q : Point)
    (model : WindowModel (readConstant old Q)) (prior bits : List Bool) :
    (reindexModel old fresh rows hcoeff Q model).step prior bits = model.step prior bits := rfl

theorem reindexModel_pointRule {n m : Nat} (old : Fin n → PointCoeff) (fresh : Fin m → PointCoeff)
    (rows : Fin n → Fin m) (hcoeff : ∀ a, old a = fresh (rows a)) (Q : Point)
    (model : WindowModel (readConstant old Q)) (root : BasisState)
    (h : PointRule root model) : PointRule root (reindexModel old fresh rows hcoeff Q model) := h


theorem four_coefficients (q y : Wire) (e : StraightEntry) :
    (ConditionalCatalyst.fourEntry q y e).coefficients = e.coefficients := rfl


end
end ShorECDLP.Entrant.Width16Schedule

namespace ShorECDLP.Entrant.Width16Actual
open Quantum Challenge Secp256k1 AndGadget WEXCredit ConditionalCatalyst Single Single.Distribution Width16Schedule
open Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedSectionVars false
attribute [local irreducible] fourierOutcomes

theorem clear_relabel (e : Wire ≃ Wire) (ws : List Wire) (s : BasisState) :
    fourierClear (ws.map e) (relabelBasis e s) = relabelBasis e (fourierClear ws s) := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, fourierClear, ← relabelBasis_upd, ih]

theorem coefficient_relabel (e : Wire ≃ Wire) (dir : PhaseDir) (ws : List Wire)
    (prior bits : List Bool) (s : BasisState) :
    fourierBranchCoeff dir (ws.map e) prior bits (relabelBasis e s) =
      fourierBranchCoeff dir ws prior bits s := by
  induction ws generalizing prior bits s with
  | nil => cases bits <;> rfl
  | cons w ws ih =>
    cases bits with
    | nil => rfl
    | cons b bs =>
      simp only [List.map_cons, fourierBranchCoeff, relabelBasis_at, ← relabelBasis_upd, ih]

theorem fourier_relabel (e : Wire ≃ Wire) (dir : PhaseDir) (ws : List Wire)
    (prior bits : List Bool) (ψ : State) :
    fourierBranch dir (ws.map e) prior bits (relabelState e ψ) =
      relabelState e (fourierBranch dir ws prior bits ψ) := by
  induction ψ using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single s c =>
    have hs : Finsupp.single s c = c • ket s := by ext u; simp [ket]
    rw [hs]
    simp only [map_smul, relabelState_ket, fourierBranch_ket, coefficient_relabel,
      clear_relabel]

def relabelModel {n : Nat} {read : ConstantBit n → Bool} (e : Wire ≃ Wire)
    (m : WindowModel read) : WindowModel read where
  physical := ⟨m.physical.wires.map e,m.physical.count,
    fun start => relabelStraight e (m.physical.program start)⟩
  point := m.point
  bias := m.bias
  ideal := (relabelState e).comp (m.ideal.comp (relabelState e.symm))
  valid := fun s => m.valid (relabelBasis e.symm s)
  nodup := m.nodup.map e.injective
  coherent := by
    intro start history
    rw [relabelStraight_instantiate]
    exact (m.coherent start history).relabel e

theorem hadamards_relabel (e : Wire ≃ Wire) (ws : List Wire) (ψ : State) :
    Quantum.run ((ws.map e).map Gate.H) (relabelState e ψ) =
      relabelState e (Quantum.run (ws.map Gate.H) ψ) := by
  have he : (ws.map e).map Gate.H = (ws.map Gate.H).map (Gate.relabel e) := by
    simp only [List.map_map, Function.comp_def, Gate.relabel]
  rw [he]
  exact Quantum.run_relabel e _ ψ

theorem relabelModel_step {n : Nat} {read : ConstantBit n → Bool}
    (e : Wire ≃ Wire) (m : WindowModel read) (prior bits : List Bool) (ψ : State) :
    (relabelModel e m).step prior bits (relabelState e ψ) =
      relabelState e (m.step prior bits ψ) := by
  simp only [WindowModel.step, relabelModel, LinearMap.comp_apply, ← List.map_reverse,
    hadamards_relabel, relabelState_symm, fourier_relabel]

theorem root_relabel (e : Wire ≃ Wire) (he : e 836 = 836) :
    relabelBasis e initialRoot = initialRoot := by
  have hz : relabelBasis e zeroBasisState = zeroBasisState := rfl
  simp only [initialRoot, relabelBasis_upd, hz, he]

theorem relabelModel_pointRule {n : Nat} {read : ConstantBit n → Bool}
    (e : Wire ≃ Wire) (m : WindowModel read)
    (pointFrame : ∀ P s, relabelBasis e (pointWrite P s) = pointWrite P (relabelBasis e s))
    (he : e 836 = 836) (h : PointRule initialRoot m) :
    PointRule initialRoot (relabelModel e m) := by
  intro prior bits P
  have hk : ket (pointWrite P initialRoot) = relabelState e (ket (pointWrite P initialRoot)) := by
    rw [relabelState_ket, pointFrame, root_relabel e he]
  rw [hk, relabelModel_step, h]
  simp only [map_smul, map_list_sum, relabelState_ket, pointFrame, root_relabel e he,
    List.map_map, Function.comp_def, relabelModel, List.length_map]

theorem supported_relabel (e : Wire ≃ Wire) (V : BasisState → Prop) (ψ : State)
    (hψ : SupportedOn V ψ) :
    SupportedOn (fun s => V (relabelBasis e.symm s)) (relabelState e ψ) := by
  refine Support.linear V (fun s => V (relabelBasis e.symm s)) (relabelState e) ?_ ψ hψ
  intro s hs
  rw [relabelState_ket]
  exact supportedOn_ket _ _ (by simpa only [relabelBasis_symm] using hs)

theorem relabelModel_prepared {n : Nat} {read : ConstantBit n → Bool}
    (e : Wire ≃ Wire) (m : WindowModel read)
    (pointFrame : ∀ P s, relabelBasis e.symm (pointWrite P s) = pointWrite P (relabelBasis e.symm s))
    (he : e 836 = 836)
    (hp : ∀ ψ, SupportedOn (pointFamily initialRoot) ψ →
      SupportedOn m.valid (Quantum.run (m.physical.wires.reverse.map Gate.H) ψ))
    (ψ : State) (hψ : SupportedOn (pointFamily initialRoot) ψ) :
    SupportedOn (relabelModel e m).valid
      (Quantum.run ((relabelModel e m).physical.wires.reverse.map Gate.H) ψ) := by
  have hes : e.symm 836 = 836 := (Equiv.symm_apply_eq e).mpr he.symm
  have hs : SupportedOn (pointFamily initialRoot) (relabelState e.symm ψ) := by
    refine Support.linear (pointFamily initialRoot) (pointFamily initialRoot) (relabelState e.symm) ?_ ψ hψ
    intro s hs
    obtain ⟨P,rfl⟩ := hs
    rw [relabelState_ket, pointFrame, root_relabel e.symm hes]
    exact supportedOn_ket _ _ ⟨P,rfl⟩
  have hc := supported_relabel e m.valid _ (hp _ hs)
  have hh := hadamards_relabel e m.physical.wires.reverse (relabelState e.symm ψ)
  rw [relabelState_symm_right] at hh
  simpa only [relabelModel, ← List.map_reverse, hh] using hc


theorem signed_magnitude (P : Point) (half v : Nat) (_hh : 0<half) (hv : v<2*half) :
    (if v<half then -((2*((half-1-v)%half)+1) • P)
      else (2*((v-half)%half)+1) • P) =
      (2*(v:Int)-2*(half:Int)+1) • P := by
  rw [← signedTableOdd_value half v]
  unfold signedTableOdd signedTableAddress
  split_ifs with h
  · rw [Nat.mod_eq_of_lt (by omega)]
    simp only [neg_smul,natCast_zsmul]
  · rw [Nat.mod_eq_of_lt (by omega)]
    simp only [natCast_zsmul]

def interpretModel {n} {read : ConstantBit n→Bool} (m : WindowModel read)
    (point : Nat→Point) (bias : Point) : WindowModel read := {m with point:=point,bias:=bias}

theorem interpret_pointRule {n} {read : ConstantBit n→Bool} (m : WindowModel read)
    (point : Nat→Point) (bias : Point) (root : BasisState)
    (hm : PointRule root m) (hp : ∀ v, v<2^m.physical.wires.length → m.point v=point v) :
    PointRule root (interpretModel m point bias) := by
  intro prior output P
  change m.step prior output (ket (pointWrite P root)) = _
  rw [hm prior output P]
  apply congrArg (fun ψ : State => (((((Real.sqrt 2)⁻¹:ℝ):ℂ))^m.physical.wires.length) • ψ)
  apply congrArg List.sum
  apply List.map_congr_left
  intro input hi
  rw [hp _ (by simpa only [(fourierOutcomes_mem _ _).mp hi] using boolWordToNat_lt_pow_two input)]
  rfl

theorem inverse_pointFrame (P : Point) (s : BasisState) :
    relabelBasis TightSupport.compact17_7.symm (pointWrite P s) =
      pointWrite P (relabelBasis TightSupport.compact17_7.symm s) := by
  have h := congrArg (relabelBasis TightSupport.compact17_7.symm)
    (TightSupport.compact17_7_pointWrite P (relabelBasis TightSupport.compact17_7.symm s))
  have hr : relabelBasis TightSupport.compact17_7 (relabelBasis TightSupport.compact17_7.symm s)=s := by
    simpa only [Equiv.symm_symm] using relabelBasis_symm TightSupport.compact17_7.symm s
  simpa only [relabelBasis_symm,hr] using h.symm

theorem reset_range : resetWires ⊆ List.range 1613 := by
  intro w hw
  simp only [resetWires, List.mem_append, List.mem_range, List.mem_singleton,
    List.mem_range'_1] at hw ⊢
  dsimp only [Wire] at *
  omega

theorem within_reindex {n m s e} (p : Straight n s e) (f : Fin n→Fin m)
    (ws : List Wire) (hp : Within ws p) : Within ws (reindexStraight f p) := by
  induction p with
  | done => trivial
  | gate g p ih => cases g <;> exact ⟨hp.1,ih hp.2⟩
  | recordGate i v g p ih => exact ⟨hp.1,ih hp.2⟩
  | measure w p ih => exact ⟨hp.1,ih hp.2⟩

theorem added_le_weight {n s e} (p : Straight n s e) : 4*added p ≤ weight4 p := by
  induction p with
  | done => rfl
  | gate g p ih =>
    cases g with
    | literal g => cases g <;> simp only [added,weight4,weightedLiteral] <;> omega
    | whenBit r b g => simp only [added,weight4]; omega
  | recordGate i b g p ih => simp only [added,weight4]; omega
  | measure w p ih => exact ih

theorem primitive_t_bound (g : Gate) : tCost g ≤ 7 := by cases g <;> simp only [tCost] <;> norm_num

theorem straight_t_bound {n s e} (p : Straight n s e) (read : ConstantBit n→Bool) (history : Fin s→Bool) :
    (p.instantiate read history).tCount ≤ 7*p.gateSlots := by
  induction p with
  | done => simp [Straight.instantiate,AdaptiveCircuit.tCount,Straight.gateSlots]
  | gate g p ih =>
    cases g with
    | literal g =>
      have hg := primitive_t_bound g
      simpa only [Straight.instantiate,TemplateGate.instantiate,AdaptiveCircuit.tCount,
        ShorECDLP.tCount,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,
        Straight.gateSlots,Nat.mul_add,Nat.mul_one] using Nat.add_le_add hg (ih history)
    | whenBit r v g =>
      have hg := primitive_t_bound g
      simp only [Straight.instantiate,TemplateGate.instantiate,AdaptiveCircuit.tCount,
        Straight.gateSlots]
      split
      · simpa only [ShorECDLP.tCount,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,
          Nat.mul_add,Nat.mul_one] using Nat.add_le_add hg (ih history)
      · simpa only [ShorECDLP.tCount,List.map_nil,List.sum_nil,Nat.zero_add] using
          (ih history).trans (by omega)
  | recordGate i v g p ih =>
    have hg := primitive_t_bound g
    simp only [Straight.instantiate,AdaptiveCircuit.tCount,Straight.gateSlots]
    split
    · simpa only [ShorECDLP.tCount,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,
        Nat.mul_add,Nat.mul_one] using Nat.add_le_add hg (ih history)
    · simpa only [ShorECDLP.tCount,List.map_nil,List.sum_nil,Nat.zero_add] using
        (ih history).trans (by omega)
  | measure w p ih =>
    simp only [Straight.instantiate,AdaptiveCircuit.tCount,Straight.gateSlots]
    exact max_le (ih _) (ih _)

theorem tmodel_of {lim : Limits} {lay : DecodeLayout} {e : StraightEntry} {q t m : Nat}
    (h : Certificate lim lay e ⟨q,t,m⟩) (Q : Point) : (resources (e.instantiate Q)).tModel ≤ t :=
  (h.resources Q).2.1

end
end ShorECDLP.Entrant.Width16Actual

/-! ### Part 1: Cutoff-18 affine phase trimming (`Trim18`) -/

namespace ShorECDLP.Entrant.Trim18
open Quantum Challenge AndGadget ApproximatePhase34 WeightedPhase28 ComplementLoss
open Paper2607_13816 Paper2607_13816.ChallengeMigration Single Single.Distribution
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
attribute [local irreducible] List.ofFn

def charge18 : Gate → ℝ
  | .P _ k _ => if 18 < k then (6283186 / 1000000 : ℝ) / 2 ^ (k + 1) else 0
  | _ => 0

def cost18 {n s e} : Straight n s e → ℝ
  | .done => 0
  | .gate (.literal g) p => charge18 g + cost18 p
  | .gate (.whenBit _ _ g) p => charge18 g + cost18 p
  | .recordGate _ _ g p => charge18 g + cost18 p
  | .measure _ p => cost18 p

theorem charge18_nonneg (g : Gate) : 0 ≤ charge18 g := by
  cases g <;> simp only [charge18] <;> positivity

theorem cost18_nonneg {n s e} (p : Straight n s e) : 0 ≤ cost18 p := by
  induction p with
  | done => rfl
  | gate g p ih => cases g <;> exact add_nonneg (charge18_nonneg _) ih
  | recordGate i v g p ih => exact add_nonneg (charge18_nonneg _) ih
  | measure w p ih => exact ih

theorem charge18_false (g : Gate) (h : largePhase 18 g = false) : charge18 g = 0 := by
  cases g <;> simp_all [largePhase, charge18]

theorem dropped_affine18 {n s e} (read : ConstantBit n → Bool)
    (p : Straight n s e) (history : Fin s → Bool) (psi : State)
    (accept : (Fin e → Bool) → Bool) (hp : p.WellFormed)
    (g : Gate) (hg : largePhase 18 g = true) :
    expectation read p history psi accept ≤
      (1 + 10 * charge18 g) * expectation read p history (applyGate g psi) accept +
        (charge18 g / 10 + (charge18 g) ^ 2) * normSq psi := by
  cases g <;> simp only [largePhase, Bool.false_eq_true, decide_eq_true_eq] at hg
  case P dir k t =>
    have hd : 0 < (6283186 / 1000000 : ℝ) / 2 ^ (k + 1) := by positivity
    have ha : (phaseAngle dir k / 2) ^ 2 ≤ ((6283186 / 1000000 : ℝ) / 2 ^ (k + 1)) ^ 2 := by
      have hpi := Real.pi_lt_d6
      have hb : 2 * Real.pi / (2 : ℝ) ^ k / 2 ≤ (6283186 / 1000000 : ℝ) / (2 : ℝ) ^ (k + 1) := by
        rw [pow_succ, div_div]
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith
      have hz : 0 ≤ 2 * Real.pi / (2 : ℝ) ^ k / 2 := by positivity
      cases dir <;> simp only [phaseAngle, neg_div, neg_sq] <;> nlinarith
    simpa only [charge18, hg, if_true] using phase_affine read p history psi accept hp dir k t _ hd ha

theorem compose_bound18 (c d E F G M : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hsmall : c + d ≤ 51 / 10000) (hE : 0 ≤ E) (hM : 0 ≤ M)
    (hF : F ≤ (1 + 10 * d) * E + (d / 10 + d ^ 2) * M)
    (hG : G ≤ (1 + (106 / 10) * c) * F + (112 / 1000) * c * M) :
    G ≤ (1 + (106 / 10) * (c + d)) * E + (112 / 1000) * (c + d) * M := by
  have hcoef : (1 + (106 / 10) * c) * (1 + 10 * d) ≤ 1 + (106 / 10) * (c + d) := by
    have hcd : c * d ≤ (51 / 10000) * d := mul_le_mul_of_nonneg_right (by linarith) hd
    nlinarith
  have herr : (1 + (106 / 10) * c) * (d / 10 + d ^ 2) + (112 / 1000) * c ≤ (112 / 1000) * (c + d) := by
    have hcd : c * d ≤ (51 / 10000) * d := mul_le_mul_of_nonneg_right (by linarith) hd
    have hdd : d * d ≤ (51 / 10000) * d := mul_le_mul_of_nonneg_right (by linarith) hd
    have hcdd : c * (d * d) ≤ (51 / 10000) * (d * d) :=
      mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hd hd)
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hF (show 0 ≤ 1 + (106 / 10) * c by positivity)
  have h1 := mul_le_mul_of_nonneg_right hcoef hE
  have h2 := mul_le_mul_of_nonneg_right herr hM
  nlinarith

theorem trim18_expectation {n s e} (read : ConstantBit n → Bool)
    (p : Straight n s e) (history : Fin s → Bool) (psi : State)
    (accept : (Fin e → Bool) → Bool) (hp : p.WellFormed)
    (hb : cost18 p ≤ 51 / 10000) :
    expectation read (trim 18 p) history psi accept ≤
      (1 + (106 / 10) * cost18 p) * expectation read p history psi accept +
        (112 / 1000) * cost18 p * normSq psi := by
  induction p generalizing psi with
  | done => simp [trim, cost18, expectation]
  | measure w p ih =>
    have h0 := ih (Fin.lastCases false history) (xResetKraus w false psi) accept hp hb
    have h1 := ih (Fin.lastCases true history) (xResetKraus w true psi) accept hp hb
    have hm := normSq_xResetKraus_false_add_true w psi
    simp only [trim, cost18, expectation]
    apply (add_le_add h0 h1).trans_eq
    rw [← hm]; ring
  | recordGate i v g p ih =>
    by_cases hg : largePhase 18 g = true
    · have hc := charge18_nonneg g
      have ht := cost18_nonneg p
      have hb' : cost18 p ≤ 51 / 10000 := by
        simpa only [cost18] using (show charge18 g + cost18 p ≤ 51 / 10000 from hb) |> fun h => by linarith
      have hi := ih history psi accept hp.2 hb'
      have hs := dropped_affine18 read p history psi accept hp.2 g hg
      have hE := expectation_nonneg read p history (applyGate g psi) accept
      have hM := mass_nonneg psi
      have hidle := idle_affine (charge18 g) (expectation read p history psi accept) (normSq psi)
        hc (expectation_nonneg read p history psi accept) hM
      simp only [trim, hg, if_true, cost18, expectation]
      by_cases hr : history i = v
      · simp only [hr, if_true, run_singleton]
        simpa only [add_comm] using compose_bound18 (cost18 p) (charge18 g) _ _ _ _ ht hc
          (show cost18 p + charge18 g ≤ 51 / 10000 by simpa only [cost18, add_comm] using hb) hE hM hs hi
      · simp only [hr, if_false, run_nil, LinearMap.id_coe, id_eq]
        simpa only [add_comm] using compose_bound18 (cost18 p) (charge18 g) _ _ _ _ ht hc
          (show cost18 p + charge18 g ≤ 51 / 10000 by simpa only [cost18, add_comm] using hb)
          (expectation_nonneg read p history psi accept) hM hidle hi
    · have hgf : largePhase 18 g = false := Bool.eq_false_iff.mpr hg
      have hz := charge18_false g hgf
      have hb' : cost18 p ≤ 51 / 10000 := by simpa only [cost18, hz, zero_add] using hb
      have hi := ih history (Quantum.run (if history i = v then [g] else []) psi) accept hp.2 hb'
      have hn : normSq (Quantum.run (if history i = v then [g] else []) psi) = normSq psi := by
        apply normSq_run
        split_ifs
        · simpa [CircuitWellFormed] using hp.1
        · simp [CircuitWellFormed]
      rw [hn] at hi
      simpa only [trim, hgf, Bool.false_eq_true, if_false, cost18, hz, zero_add, expectation] using hi
  | gate g p ih =>
    cases g with
    | literal g =>
      by_cases hg : largePhase 18 g = true
      · have hc := charge18_nonneg g
        have ht := cost18_nonneg p
        have hb' : cost18 p ≤ 51 / 10000 := by
          simpa only [cost18] using (show charge18 g + cost18 p ≤ 51 / 10000 from hb) |> fun h => by linarith
        have hi := ih history psi accept hp.2 hb'
        have hs := dropped_affine18 read p history psi accept hp.2 g hg
        have hE := expectation_nonneg read p history (applyGate g psi) accept
        have hM := mass_nonneg psi
        simp only [trim, hg, if_true, cost18, expectation, TemplateGate.instantiate, run_singleton]
        simpa only [add_comm] using compose_bound18 (cost18 p) (charge18 g) _ _ _ _ ht hc
          (show cost18 p + charge18 g ≤ 51 / 10000 by simpa only [cost18, add_comm] using hb) hE hM hs hi
      · have hgf : largePhase 18 g = false := Bool.eq_false_iff.mpr hg
        have hz := charge18_false g hgf
        have hb' : cost18 p ≤ 51 / 10000 := by simpa only [cost18, hz, zero_add] using hb
        have hi := ih history (Quantum.run [g] psi) accept hp.2 hb'
        have hn : normSq (Quantum.run [g] psi) = normSq psi := by
          apply normSq_run; simpa [CircuitWellFormed] using hp.1
        rw [hn] at hi
        simpa only [trim, hgf, Bool.false_eq_true, if_false, cost18, hz, zero_add, expectation,
          TemplateGate.instantiate] using hi
    | whenBit r v g =>
      by_cases hg : largePhase 18 g = true
      · have hc := charge18_nonneg g
        have ht := cost18_nonneg p
        have hb' : cost18 p ≤ 51 / 10000 := by
          simpa only [cost18] using (show charge18 g + cost18 p ≤ 51 / 10000 from hb) |> fun h => by linarith
        have hi := ih history psi accept hp.2 hb'
        have hs := dropped_affine18 read p history psi accept hp.2 g hg
        have hE := expectation_nonneg read p history (applyGate g psi) accept
        have hM := mass_nonneg psi
        have hidle := idle_affine (charge18 g) (expectation read p history psi accept) (normSq psi)
          hc (expectation_nonneg read p history psi accept) hM
        simp only [trim, hg, if_true, cost18, expectation, TemplateGate.instantiate]
        by_cases hr : read r = v
        · simp only [hr, if_true, run_singleton]
          simpa only [add_comm] using compose_bound18 (cost18 p) (charge18 g) _ _ _ _ ht hc
            (show cost18 p + charge18 g ≤ 51 / 10000 by simpa only [cost18, add_comm] using hb) hE hM hs hi
        · simp only [hr, if_false, run_nil, LinearMap.id_coe, id_eq]
          simpa only [add_comm] using compose_bound18 (cost18 p) (charge18 g) _ _ _ _ ht hc
            (show cost18 p + charge18 g ≤ 51 / 10000 by simpa only [cost18, add_comm] using hb)
            (expectation_nonneg read p history psi accept) hM hidle hi
      · have hgf : largePhase 18 g = false := Bool.eq_false_iff.mpr hg
        have hz := charge18_false g hgf
        have hb' : cost18 p ≤ 51 / 10000 := by simpa only [cost18, hz, zero_add] using hb
        have hi := ih history (Quantum.run ((TemplateGate.whenBit r v g).instantiate read) psi) accept hp.2 hb'
        have hn : normSq (Quantum.run ((TemplateGate.whenBit r v g).instantiate read) psi) = normSq psi :=
          normSq_template read (.whenBit r v g) hp.1 psi
        rw [hn] at hi
        simpa only [trim, hgf, Bool.false_eq_true, if_false, cost18, hz, zero_add, expectation,
          TemplateGate.instantiate] using hi

def potential18 (k : Nat) : ℝ := (6283186 / 1000000 : ℝ) / (2 : ℝ) ^ (max 19 k)
def unit18 : ℝ := (6283186 / 1000000 : ℝ) / 2 ^ 19

theorem cost18_zero_of_residue {n s e} (p : Straight n s e) (h : residue p = 0) : cost18 p = 0 := by
  induction p with
  | done => rfl
  | measure w p ih => exact ih h
  | recordGate i v g p ih =>
    have ht : residue p = 0 := by simp only [residue] at h; omega
    have hg : charge18 g = 0 := by cases g <;> simp_all [residue, tCost, charge18]
    simp [cost18, hg, ih ht]
  | gate g p ih =>
    have ht : residue p = 0 := by cases g <;> simp only [residue] at h <;> omega
    cases g with
    | literal g =>
      have hg : charge18 g = 0 := by cases g <;> simp_all [residue, primitivePhaseCost, charge18]
      simp [cost18, hg, ih ht]
    | whenBit r v g =>
      have hg : charge18 g = 0 := by cases g <;> simp_all [residue, tCost, charge18]
      simp [cost18, hg, ih ht]

theorem cost18_literal_zero {n s} (c : Circuit) (h : ∀ g ∈ c, largePhase 18 g = false) :
    cost18 (literalProgram (n := n) (s := s) c) = 0 := by
  induction c with
  | nil => rfl
  | cons g gs ih =>
    change charge18 g + cost18 (literalProgram gs) = 0
    rw [charge18_false g (h g List.mem_cons_self),
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx)), zero_add]

theorem cost18_append {n s m e} (p : Straight n s m) (q : Straight n m e) :
    cost18 (p.append q) = cost18 p + cost18 q := by
  induction p with
  | done => simp [Straight.append, cost18]
  | gate g p ih => cases g <;> simp [Straight.append, cost18, ih, add_assoc]
  | recordGate => simp_all [Straight.append, cost18, add_assoc]
  | measure => simp_all [Straight.append, cost18]

theorem cost18_cast {n s e f} (p : Straight n s e) (h : e = f) : cost18 (castFinish h p) = cost18 p := by
  subst f; rfl

theorem cost18_prepare {n s e} (ws : List Wire) (p : Straight n s e) :
    cost18 (prepareOuterBank ws p) = cost18 p := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simpa [prepareOuterBank, cost18, charge18] using ih

theorem cost18_reindex {n m s e} (p : Straight n s e) (f : Fin n → Fin m) :
    cost18 (reindexStraight f p) = cost18 p := by
  induction p with
  | done => rfl
  | gate g p ih => cases g <;> simp_all [reindexStraight, reindexGate, cost18]
  | recordGate => simp_all [reindexStraight, cost18]
  | measure => simp_all [reindexStraight, cost18]

theorem charge18_balance (dir : PhaseDir) (w : Wire) (k : Nat) :
    charge18 (.P dir k w) + potential18 (k + 1) = potential18 k := by
  by_cases hk : 18 < k
  · have h1 : max 19 k = k := max_eq_right (by omega)
    have h2 : max 19 (k + 1) = k + 1 := max_eq_right (by omega)
    simp only [charge18, hk, if_true, potential18, h1, h2, pow_succ]
    have hp : (2 : ℝ) ^ k ≠ 0 := by positivity
    field_simp; ring
  · have h1 : max 19 k = 19 := max_eq_left (by omega)
    have h2 : max 19 (k + 1) = 19 := max_eq_left (by omega)
    simp [charge18, hk, potential18, h1, h2]

theorem cost18_feedback_balance {n s e} (dir : PhaseDir) (w : Wire) (indices : List (Fin s))
    (k : Nat) (p : Straight n s e) :
    cost18 (feedbackProgram dir w indices k p) + potential18 (k + indices.length) =
      potential18 k + cost18 p := by
  induction indices generalizing k with
  | nil => simp [feedbackProgram, add_comm]
  | cons i is ih =>
    have hi := ih (k + 1)
    have hc := charge18_balance dir w k
    have he : k + (i :: is).length = (k + 1) + is.length := by simp; omega
    simp only [feedbackProgram, cost18, he]
    linarith

def account18 : Nat → Nat → ℝ
  | 0, _ => 0
  | n + 1, p => unit18 - potential18 (p + 2) + account18 n (p + 1)

theorem account18_append (a b p : Nat) :
    account18 (a + b) p = account18 a p + account18 b (p + a) := by
  induction a generalizing p with
  | zero => simp [account18]
  | succ a ih =>
    rw [Nat.succ_add]
    simp only [account18, ih]
    have he : p + (a + 1) = (p + 1) + a := by omega
    rw [he]; ring

theorem cost18_fourier_exact (n : Nat) (dir : PhaseDir) (ws : List Wire)
    (start : Nat) (prior : List (Fin start)) :
    cost18 (fourierProgram n dir ws start prior) = account18 ws.length prior.length := by
  induction ws generalizing start with
  | nil => simp [fourierProgram, cost18, account18]
  | cons w ws ih =>
    simp only [fourierProgram, cost18_cast]
    have hi := ih (start + 1) (Fin.last start :: prior.map Fin.castSucc)
    have hf := cost18_feedback_balance dir w prior 2 (.measure w
      (fourierProgram n dir ws (start + 1) (Fin.last start :: prior.map Fin.castSucc)))
    have he : potential18 2 = unit18 := by norm_num [potential18, unit18]
    simp only [cost18, hi, he, List.length_cons, List.length_map] at hf hi
    rw [List.length_cons, account18]
    have hn : 2 + prior.length = prior.length + 2 := by omega
    rw [hn] at hf
    linarith

theorem potential18_half (k : Nat) (hk : 19 ≤ k) :
    2 * potential18 (k + 1) = potential18 k := by
  have h1 : max 19 k = k := max_eq_right hk
  have h2 : max 19 (k + 1) = k + 1 := max_eq_right (by omega)
  simp only [potential18, h1, h2, pow_succ]; ring

theorem account18_geometric (n p : Nat) (hp : 17 ≤ p) :
    account18 n p + 2 * potential18 (p + 2) = (n : ℝ) * unit18 + 2 * potential18 (p + n + 2) := by
  induction n generalizing p with
  | zero => simp [account18]
  | succ n ih =>
    have hi := ih (p + 1) (by omega)
    have hh := potential18_half (p + 2) (by omega)
    have he : p + 2 + 1 = p + 1 + 2 := by omega
    rw [he] at hh
    have he2 : p + (n + 1) + 2 = (p + 1) + n + 2 := by omega
    simp only [account18, Nat.cast_add, Nat.cast_one, he2]
    linarith

theorem joint_error18 : account18 258 0 + account18 204 0 ≤ 51 / 10000 := by
  have hz : account18 17 0 = 0 := by norm_num [account18, potential18, unit18]
  rw [show 258 = 17 + 241 from rfl, show 204 = 17 + 187 from rfl,
    account18_append, account18_append, hz]
  norm_num only [zero_add]
  have h1 := account18_geometric 241 17 (by decide)
  have h2 := account18_geometric 187 17 (by decide)
  have hp1 : potential18 (17 + 241 + 2) ≤ unit18 / 4 := by
    unfold potential18 unit18
    rw [show max 19 (17 + 241 + 2) = 260 by decide]
    have h21 : (2 : ℝ) ^ 21 ≤ (2 : ℝ) ^ 260 := pow_le_pow_right₀ (by norm_num) (by decide)
    rw [show (6283186 / 1000000 : ℝ) / 2 ^ 19 / 4 = (6283186 / 1000000 : ℝ) / (2 : ℝ) ^ 21 by norm_num]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) h21
  have hp2 : potential18 (17 + 187 + 2) ≤ unit18 / 4 := by
    unfold potential18 unit18
    rw [show max 19 (17 + 187 + 2) = 206 by decide]
    have h21 : (2 : ℝ) ^ 21 ≤ (2 : ℝ) ^ 206 := pow_le_pow_right₀ (by norm_num) (by decide)
    rw [show (6283186 / 1000000 : ℝ) / 2 ^ 19 / 4 = (6283186 / 1000000 : ℝ) / (2 : ℝ) ^ 21 by norm_num]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) h21
  have hp19 : potential18 (17 + 2) = unit18 := by norm_num [potential18, unit18]
  rw [hp19] at h1 h2
  norm_num only [Nat.cast_ofNat] at h1 h2
  have hu : (425 : ℝ) * unit18 ≤ 51 / 10000 := by norm_num [unit18]
  linarith

theorem cost18_axis_exact [body : Single.WindowBody] [ledger : Single.ProducerResources body]
    {n} (ws : List (Window n))
    (hz : ∀ w ∈ ws, ∀ start, cost18 (w.program start) = 0)
    (start : Nat) (prior : List (Fin start)) :
    cost18 (axis ws start prior) =
      account18 ((ws.map (fun w => w.wires.length)).sum) prior.length := by
  induction ws generalizing start with
  | nil => simp [axis, cost18, account18]
  | cons w ws ih =>
    simp only [axis, cost18_cast, cost18_append, cost18_prepare]
    rw [hz w (by simp) start, zero_add]
    have hf := cost18_fourier_exact n .inverse w.wires (start + w.count) (bankPrior w.count prior)
    have hi := ih (fun v hv s => hz v (List.mem_cons_of_mem w hv) s)
      (start + w.count + w.wires.length) (nextPrior w.count w.wires.length prior)
    rw [hf, hi]
    simp only [bankPrior, nextPrior, List.length_append, List.length_reverse, List.length_ofFn,
      List.length_map, List.map_cons, List.sum_cons, account18_append]
    rw [Nat.add_comm w.wires.length prior.length]

def droppedSlots18 : Nat → Nat → Nat
  | 0, _ => 0
  | width + 1, prior => (prior - 17) + droppedSlots18 width (prior + 1)

def metadataDropped18 : List Nat → Nat → Nat
  | [], _ => 0
  | width :: ws, prior => droppedSlots18 width prior + metadataDropped18 ws (prior + width)

theorem removed18_append {n s m e} (p : Straight n s m) (q : Straight n m e) :
    removed 18 (p.append q) = removed 18 p + removed 18 q := by
  induction p with
  | done => simp [Straight.append, removed]
  | gate g p ih => cases g <;> simp [Straight.append, removed, ih, Nat.add_assoc]
  | recordGate i v g p ih => simp_all [Straight.append, removed, Nat.add_assoc]
  | measure w p ih => simp_all [Straight.append, removed]

theorem removed18_cast {n s e f} (p : Straight n s e) (h : e = f) :
    removed 18 (castFinish h p) = removed 18 p := by subst f; rfl

theorem removed18_reindex {n m s e} (p : Straight n s e) (f : Fin n → Fin m) :
    removed 18 (reindexStraight f p) = removed 18 p := by
  induction p with
  | done => rfl
  | gate g p ih =>
    cases g with
    | literal g => cases g <;> simp_all [reindexStraight, reindexGate, removed, ih]
    | whenBit r v g => simp_all [reindexStraight, reindexGate, removed, ih]
  | recordGate => simp_all [reindexStraight, removed]
  | measure => simp_all [reindexStraight, removed]

theorem removed18_feedback {n s e} (dir : PhaseDir) (w : Wire) (indices : List (Fin s))
    (k : Nat) (p : Straight n s e) :
    removed 18 (feedbackProgram dir w indices k p) =
      (indices.length - min indices.length (19 - k)) + removed 18 p := by
  induction indices generalizing k with
  | nil => simp [feedbackProgram]
  | cons i is ih =>
    simp only [feedbackProgram, removed, largePhase, ih, List.length_cons]
    by_cases hk : 18 < k
    · simp only [hk, decide_true, Bool.toNat_true]; omega
    · simp only [hk, decide_false, Bool.toNat_false]; omega

theorem removed18_prepare {n s e} (ws : List Wire) (p : Straight n s e) :
    removed 18 (prepareOuterBank ws p) = removed 18 p := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simpa [prepareOuterBank, removed, largePhase] using ih

theorem removed_fourier18 (n : Nat) (dir : PhaseDir) (ws : List Wire)
    (start : Nat) (prior : List (Fin start)) :
    removed 18 (fourierProgram n dir ws start prior) = droppedSlots18 ws.length prior.length := by
  induction ws generalizing start with
  | nil => rfl
  | cons w ws ih =>
    simp [fourierProgram, removed18_cast, removed18_feedback, removed, ih, droppedSlots18]; omega

theorem removed18_framed {n s m k e f} (p : Straight n s m) (q : Straight n m k)
    (r : Straight n k e) (h : e = f) :
    removed 18 (Single.framed p q r h) = removed 18 p + removed 18 q + removed 18 r := by
  simp [Single.framed, removed, removed18_cast, removed18_append, largePhase, Nat.add_assoc]

theorem removed_axis18 [body : Single.WindowBody] [ledger : Single.ProducerResources body] {n}
    (ws : List (Single.Window n)) (widths : List Nat)
    (hw : List.Forall₂ (fun w c => w.wires.length = c) ws widths)
    (start : Nat) (prior : List (Fin start)) :
    metadataDropped18 widths prior.length ≤ removed 18 (Single.axis ws start prior) := by
  induction ws generalizing widths start with
  | nil => cases hw; simp [metadataDropped18, Single.axis, removed]
  | cons w ws ih =>
    cases hw with
    | cons head tail =>
      rename_i c widths
      simp only [Single.axis, removed18_cast, removed18_append, removed18_prepare, removed_fourier18,
        bankPrior_length]
      have ht := ih widths tail (start + w.count + w.wires.length) (Single.nextPrior w.count w.wires.length prior)
      rw [Single.nextPrior_length] at ht
      simp only [metadataDropped18]
      rw [head] at *
      omega

theorem dropped_weight18 (g : Gate) (hg : largePhase 18 g = true) :
    ConditionalCatalyst.weightedGate g = 1 ∧ ConditionalCatalyst.weightedLiteral g = 1 := by
  cases g <;> simp only [largePhase, Bool.false_eq_true, decide_eq_true_eq] at hg
  case P dir k t =>
    have hk : k ≠ 2 := by omega
    simp [ConditionalCatalyst.weightedGate, ConditionalCatalyst.weightedLiteral,
      ConditionalCatalyst.phaseTwoGate_P, hk, tCost]

theorem weight4_trim18 {n s e} (p : Straight n s e) :
    ConditionalCatalyst.weight4 (trim 18 p) + removed 18 p = ConditionalCatalyst.weight4 p := by
  induction p with
  | done => rfl
  | gate g p ih =>
    cases g with
    | literal g =>
      by_cases hg : largePhase 18 g = true
      · have hw := (dropped_weight18 g hg).2
        simp only [trim, hg, if_true, removed, Bool.toNat_true, ConditionalCatalyst.weight4, hw]; omega
      · have hgf : largePhase 18 g = false := Bool.eq_false_iff.mpr hg
        simp only [trim, hgf, Bool.false_eq_true, if_false, removed, Bool.toNat_false, zero_add,
          ConditionalCatalyst.weight4]; omega
    | whenBit r v g =>
      by_cases hg : largePhase 18 g = true
      · have hw := (dropped_weight18 g hg).1
        simp only [trim, hg, if_true, removed, Bool.toNat_true, ConditionalCatalyst.weight4, hw]; omega
      · have hgf : largePhase 18 g = false := Bool.eq_false_iff.mpr hg
        simp only [trim, hgf, Bool.false_eq_true, if_false, removed, Bool.toNat_false, zero_add,
          ConditionalCatalyst.weight4]; omega
  | recordGate i v g p ih =>
    by_cases hg : largePhase 18 g = true
    · have hw := (dropped_weight18 g hg).1
      simp only [trim, hg, if_true, removed, Bool.toNat_true, ConditionalCatalyst.weight4, hw]; omega
    · have hgf : largePhase 18 g = false := Bool.eq_false_iff.mpr hg
      simp only [trim, hgf, Bool.false_eq_true, if_false, removed, Bool.toNat_false, zero_add,
        ConditionalCatalyst.weight4]; omega
  | measure w p ih => exact ih

theorem trim18_t {n s e} (p : Straight n s e) (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    ((trim 18 p).instantiate read history).tCount ≤ (p.instantiate read history).tCount := by
  induction p with
  | done => rfl
  | gate g p ih =>
    cases g <;> simp only [trim] <;> split_ifs <;>
      simp only [Straight.instantiate, AdaptiveCircuit.tCount] <;> (have h := ih history; omega)
  | recordGate i v g p ih =>
    simp only [trim]; split_ifs <;>
      simp only [Straight.instantiate, AdaptiveCircuit.tCount] <;> (have h := ih history; omega)
  | measure w p ih =>
    simp only [trim, Straight.instantiate, AdaptiveCircuit.tCount]
    exact max_le_max (ih _) (ih _)

theorem trim18_added {n s e} (p : Straight n s e) : added (trim 18 p) = added p := by
  induction p with
  | done => rfl
  | gate g p ih =>
    cases g with
    | literal g => cases g <;> simp [trim, largePhase, added, ih] <;> split_ifs <;> simp_all [added]
    | whenBit r v g => simp only [trim]; split_ifs <;> simpa only [added] using ih
  | recordGate i v g p ih => simp only [trim]; split_ifs <;> simpa only [added] using ih
  | measure w p ih => exact ih

theorem trim18_slots {n s e} (p : Straight n s e) : (trim 18 p).gateSlots ≤ p.gateSlots := by
  induction p with
  | done => exact le_rfl
  | gate g p ih =>
    cases g with
    | literal g => simp only [trim]; split_ifs <;> simp only [Straight.gateSlots] <;> omega
    | whenBit r v g => simp only [trim]; split_ifs <;> simp only [Straight.gateSlots] <;> omega
  | recordGate i v g p ih => simp only [trim]; split_ifs <;> simp only [Straight.gateSlots] <;> omega
  | measure w p ih => exact ih

theorem trim18_wellFormed {n s e} (p : Straight n s e) (hp : p.WellFormed) :
    (trim 18 p).WellFormed := by
  induction p with
  | done => trivial
  | gate g p ih =>
    cases g with
    | literal g => simp only [trim]; split_ifs; exact ih hp.2; exact ⟨hp.1, ih hp.2⟩
    | whenBit r v g => simp only [trim]; split_ifs; exact ih hp.2; exact ⟨hp.1, ih hp.2⟩
  | recordGate i v g p ih => simp only [trim]; split_ifs; exact ih hp.2; exact ⟨hp.1, ih hp.2⟩
  | measure w p ih => exact ih hp

theorem trim18_within {n s e} (p : Straight n s e) (ws : List Wire) (hp : Within ws p) :
    Within ws (trim 18 p) := by
  induction p with
  | done => trivial
  | gate g p ih =>
    cases g with
    | literal g => simp only [trim]; split_ifs; exact ih hp.2; exact ⟨hp.1, ih hp.2⟩
    | whenBit r v g => simp only [trim]; split_ifs; exact ih hp.2; exact ⟨hp.1, ih hp.2⟩
  | recordGate i v g p ih => simp only [trim]; split_ifs; exact ih hp.2; exact ⟨hp.1, ih hp.2⟩
  | measure w p ih => exact ⟨hp.1, ih hp.2⟩

end
end ShorECDLP.Entrant.Trim18

/-! ### Part 2: Arbitrary-bias windowed bridge and `prependCircuit` combinators -/

namespace ShorECDLP.Entrant.Schedule26Bridge
open Classical Quantum Secp256k1 Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
open Single Single.Distribution SineCircuit
open scoped Classical
noncomputable section
variable [body : Single.WindowBody] [ledger : Single.ProducerResources body]
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
attribute [local irreducible] fourierOutcomes

/-- Bijective basis permutation translating `pointWrite P root ↦ pointWrite (P + S) root`. -/
def shiftBasis (S : Point) (root : BasisState) (s : BasisState) : BasisState :=
  @dite _ (∃ P : Point, s = pointWrite P root) (Classical.propDecidable _)
    (fun h => pointWrite (Classical.choose h + S) root) (fun _ => s)

theorem shiftBasis_pointWrite (S : Point) (root : BasisState) (P : Point) :
    shiftBasis S root (pointWrite P root) = pointWrite (P + S) root := by
  have hex : ∃ Q : Point, pointWrite P root = pointWrite Q root := ⟨P, rfl⟩
  simp only [shiftBasis, dif_pos hex]
  have hP : Classical.choose hex = P :=
    (pointWrite_injective root (Classical.choose_spec hex)).symm
  rw [hP]

theorem shiftBasis_left_inv (S : Point) (root : BasisState) (s : BasisState) :
    shiftBasis (-S) root (shiftBasis S root s) = s := by
  by_cases h : ∃ P : Point, s = pointWrite P root
  · obtain ⟨P, rfl⟩ := h
    rw [shiftBasis_pointWrite, shiftBasis_pointWrite, add_neg_cancel_right]
  · unfold shiftBasis
    rw [dif_neg h, dif_neg h]

theorem shiftBasis_injective (S : Point) (root : BasisState) :
    Function.Injective (shiftBasis S root) := by
  intro a b hab
  have h := congrArg (shiftBasis (-S) root) hab
  rwa [shiftBasis_left_inv, shiftBasis_left_inv] at h

theorem lmapDomain_inj_normSq {f : BasisState → BasisState} (hf : Function.Injective f) (ψ : State) :
    normSq (Finsupp.lmapDomain ℂ ℂ f ψ) = normSq ψ := by
  unfold normSq Quantum.inner
  rw [Finsupp.lmapDomain_apply]
  congr 1
  rw [Finsupp.sum_mapDomain_index_inj hf]
  apply Finsupp.sum_congr
  intro s _
  rw [Finsupp.mapDomain_apply hf]

private theorem windowed_axis_expand26 {n : Nat} {read : ConstantBit n → Bool}
    (root : BasisState) (f : WindowModel read) (fBits : List Bool) (rest : List (WindowModel read × List Bool))
    (hrest : ∀ w ∈ rest, PointRule root w.1) (A : Point)
    (hstep : f.step List.nil fBits (ket (pointWrite A root)) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ f.physical.wires.length) •
        ((fourierOutcomes f.physical.wires.length).map (fun input =>
          (sineWeight 10 (boolWordToNat input / 2 ^ (f.physical.wires.length - 10)) *
            fourierBitAmplitude .inverse input.reverse List.nil fBits) •
            ket (pointWrite (A + f.point (boolWordToNat input)) root))).sum) :
    let path := logicalPath modelDigit ((f, fBits) :: rest)
    modelBranch ((f, fBits) :: rest) List.nil (ket (pointWrite A root)) =
      ((inputWords (pathWidths path)).map (fun inputs =>
        (sineWeight 10 (boolWordToNat (inputs.headD []) / 2 ^ (f.physical.wires.length - 10)) *
          inputWeight path List.nil inputs) •
          ket (pointWrite (pathEnd path inputs A) root))).sum := by
  dsimp only
  simp only [modelBranch, LinearMap.comp_apply, hstep, map_smul, stateLinear_list_sum,
    List.map_map, Function.comp_def]
  simp_rw [modelBranch_point modelDigit root rest (fun w hw prior P => hrest w hw prior w.2 P),
    pointKernel_inputs]
  simp only [logicalPath, pathWidths, List.map_cons, modelDigit, inputWords, List.map_flatMap,
    List.map_map, Function.comp_def, flat_sum, List.smul_sum, smul_smul, inputWeight, pathEnd]
  congr 1
  apply List.map_congr_left; intro input _
  apply congrArg List.sum; apply List.map_congr_left; intro inputs _
  congr 1; simp only [List.headD_cons]; ring

/-- Two sine-windowed axes with arbitrary total bias `S` produce `shiftBasis (-S)` applied to
`windowedPointState`, so Born mass is completely invariant to any constant point-register bias! -/
theorem windowed_two_modelBranches_anyBias {n : Nat} {read : ConstantBit n → Bool}
    (Q : Point) (root : BasisState) (ψ : State)
    (fL : WindowModel read) (restL : List (WindowModel read))
    (fR : WindowModel read) (restR : List (WindowModel read))
    (hfL : WindowedFirstRule root ψ fL)
    (hfR : WindowedPointRule root fR)
    (hrest : ∀ w ∈ restL ++ restR, PointRule root w)
    (hwL : ModelWeights G (fL :: restL)) (hwR : ModelWeights Q (fR :: restR))
    (lbp : List (WindowModel read × List Bool)) (hlbp : lbp ∈ outputPaths (fL :: restL))
    (rbp : List (WindowModel read × List Bool)) (hrbp : rbp ∈ outputPaths (fR :: restR)) :
    let S := -(((fL :: restL).map WindowModel.bias).sum + ((fR :: restR).map WindowModel.bias).sum)
    modelBranch rbp List.nil (modelBranch lbp List.nil ψ) =
      Finsupp.lmapDomain ℂ ℂ (shiftBasis S root)
        (windowedPointState Q root (precision (fL :: restL)) (precision (fR :: restR))
          (lbp.map Prod.snd).flatten (rbp.map Prod.snd).flatten) := by
  dsimp only
  set S := -(((fL :: restL).map WindowModel.bias).sum + ((fR :: restR).map WindowModel.bias).sum)
  obtain ⟨bL, hbL, hmL⟩ := List.mem_flatMap.mp hlbp
  obtain ⟨ltail, hltail, rfl⟩ := List.mem_map.mp hmL
  obtain ⟨bR, hbR, hmR⟩ := List.mem_flatMap.mp hrbp
  obtain ⟨rtail, hrtail, rfl⟩ := List.mem_map.mp hmR
  have hruleL : ∀ w ∈ ltail, PointRule root w.1 := fun w hw => by
    apply hrest w.1 (List.mem_append_left _ _)
    rw [← outputPath_models restL ltail hltail]; exact List.mem_map.mpr ⟨w, hw, rfl⟩
  have hruleR : ∀ w ∈ rtail, PointRule root w.1 := fun w hw => by
    apply hrest w.1 (List.mem_append_right _ _)
    rw [← outputPath_models restR rtail hrtail]; exact List.mem_map.mpr ⟨w, hw, rfl⟩
  let pathL := logicalPath modelDigit ((fL, bL) :: ltail)
  let pathR := logicalPath modelDigit ((fR, bR) :: rtail)
  have hL_exp : modelBranch ((fL, bL) :: ltail) List.nil ψ =
      ((inputWords (pathWidths pathL)).map (fun inputsL =>
        (sineWeight 10 (boolWordToNat (inputsL.headD []) / 2 ^ (fL.physical.wires.length - 10)) *
          inputWeight pathL List.nil inputsL) •
          ket (pointWrite (pathEnd pathL inputsL 0) root))).sum := by
    simp only [modelBranch, LinearMap.comp_apply, hfL.2, map_smul, stateLinear_list_sum,
      List.map_map, Function.comp_def]
    simp_rw [modelBranch_point modelDigit root ltail (fun w hw prior P => hruleL w hw prior w.2 P),
      pointKernel_inputs]
    simp only [pathL, logicalPath, pathWidths, List.map_cons, modelDigit, inputWords, List.map_flatMap,
      List.map_map, Function.comp_def, flat_sum, List.smul_sum, smul_smul, inputWeight, pathEnd, zero_add]
    congr 1
    apply List.map_congr_left; intro input _
    apply congrArg List.sum; apply List.map_congr_left; intro inputs _
    congr 1; simp only [List.headD_cons]; ring
  rw [hL_exp, stateLinear_list_sum, List.map_map]
  have hR_exp (A : Point) : modelBranch ((fR, bR) :: rtail) List.nil (ket (pointWrite A root)) =
      ((inputWords (pathWidths pathR)).map (fun inputsR =>
        (sineWeight 10 (boolWordToNat (inputsR.headD []) / 2 ^ (fR.physical.wires.length - 10)) *
          inputWeight pathR List.nil inputsR) •
          ket (pointWrite (pathEnd pathR inputsR A) root))).sum :=
    windowed_axis_expand26 root fR bR rtail hruleR A (hfR.2 List.nil bR A)
  simp only [Function.comp_def, map_smul, hR_exp, List.smul_sum, List.map_map, smul_smul]
  have hlenL := outputPath_lengths (fL :: restL) ((fL, bL) :: ltail) hlbp
  have hlenR := outputPath_lengths (fR :: restR) ((fR, bR) :: rtail) hrbp
  have hdescL := outputPath_weights G (fL :: restL) hwL ((fL, bL) :: ltail) hlbp
  have hdescR := outputPath_weights Q (fR :: restR) hwR ((fR, bR) :: rtail) hrbp
  have hS : S = -(biasSum DigitWindow.bias pathL + biasSum DigitWindow.bias pathR) := by
    have h1 := outputPath_bias (fL :: restL) ((fL, bL) :: ltail) hlbp
    have h2 := outputPath_bias (fR :: restR) ((fR, bR) :: rtail) hrbp
    dsimp only [pathL, pathR, S]
    rw [h1, h2]
  have hwl : (pathWidths pathL).sum = precision (fL :: restL) := by
    rw [outputPath_widths (fL :: restL) _ hlbp]; rfl
  have hwr : (pathWidths pathR).sum = precision (fR :: restR) := by
    rw [outputPath_widths (fR :: restR) _ hrbp]; rfl
  let nL := (pathWidths pathL).sum
  let nR := (pathWidths pathR).sum
  let c : ℂ := ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ (nL + nR)
  let F (a b : List Bool) : State :=
    (c * (c * (sineWeight 10 (boolWordToNat a / 2 ^ (nL - 10)) *
              dyadicFourierKernel .inverse nL (boolWordToNat a) (fourierWordLSB (pathL.map Prod.snd).flatten)) *
             (sineWeight 10 (boolWordToNat b / 2 ^ (nR - 10)) *
              dyadicFourierKernel .inverse nR (boolWordToNat b) (fourierWordLSB (pathR.map Prod.snd).flatten)))) •
      ket (pointWrite (boolWordToNat a • G + boolWordToNat b • Q + S) root)
  have hhead_divL : ∀ inputsL ∈ inputWords (pathWidths pathL),
      boolWordToNat (inputsL.headD []) / 2 ^ (fL.physical.wires.length - 10) =
        boolWordToNat (scalarWord inputsL) / 2 ^ (nL - 10) := by
    intro inputsL hinL
    have hm := (inputWords_mem _ _).mp hinL
    cases inputsL with
    | nil => simp [pathL, logicalPath, pathWidths] at hm
    | cons x xs =>
      simp only [pathL, logicalPath, pathWidths, modelDigit, List.map_cons, List.cons.injEq] at hm
      have hxs : xs.flatten.length = (pathWidths (logicalPath modelDigit ltail)).sum := by
        rw [List.length_flatten, hm.2]; rfl
      have hnL : nL = x.length + xs.flatten.length := by
        dsimp only [nL, pathL, logicalPath, pathWidths, modelDigit]
        simp only [List.map_cons, List.sum_cons, ← hm.1]
        rw [hxs]; rfl
      rw [hnL, ← hm.1, List.headD_cons]
      exact (scalarWord_head_div x xs (by rw [hm.1]; exact hfL.1)).symm
  have hhead_divR : ∀ inputsR ∈ inputWords (pathWidths pathR),
      boolWordToNat (inputsR.headD []) / 2 ^ (fR.physical.wires.length - 10) =
        boolWordToNat (scalarWord inputsR) / 2 ^ (nR - 10) := by
    intro inputsR hinR
    have hm := (inputWords_mem _ _).mp hinR
    cases inputsR with
    | nil => simp [pathR, logicalPath, pathWidths] at hm
    | cons x xs =>
      simp only [pathR, logicalPath, pathWidths, modelDigit, List.map_cons, List.cons.injEq] at hm
      have hxs : xs.flatten.length = (pathWidths (logicalPath modelDigit rtail)).sum := by
        rw [List.length_flatten, hm.2]; rfl
      have hnR : nR = x.length + xs.flatten.length := by
        dsimp only [nR, pathR, logicalPath, pathWidths, modelDigit]
        simp only [List.map_cons, List.sum_cons, ← hm.1]
        rw [hxs]; rfl
      rw [hnR, ← hm.1, List.headD_cons]
      exact (scalarWord_head_div x xs (by rw [hm.1]; exact hfR.1)).symm
  have hmatch : ((inputWords (pathWidths pathL)).map (fun inputsL =>
        ((inputWords (pathWidths pathR)).map (fun inputsR =>
          ((sineWeight 10 (boolWordToNat (inputsL.headD []) / 2 ^ (fL.physical.wires.length - 10)) *
              inputWeight pathL List.nil inputsL) *
           (sineWeight 10 (boolWordToNat (inputsR.headD []) / 2 ^ (fR.physical.wires.length - 10)) *
              inputWeight pathR List.nil inputsR)) •
            ket (pointWrite (pathEnd pathR inputsR (pathEnd pathL inputsL 0)) root))).sum)).sum =
      ((inputWords (pathWidths pathL)).map (fun inputsL =>
        ((inputWords (pathWidths pathR)).map (fun inputsR =>
          F (scalarWord inputsL) (scalarWord inputsR))).sum)).sum := by
    apply congrArg List.sum; apply List.map_congr_left; intro inputsL hinL
    apply congrArg List.sum; apply List.map_congr_left; intro inputsR hinR
    have hl := pathEnd_reconstruct G DigitWindow.bias pathL hdescL inputsL ((inputWords_mem _ _).mp hinL) 0
    have hr := pathEnd_reconstruct Q DigitWindow.bias pathR hdescR inputsR ((inputWords_mem _ _).mp hinR)
      (pathEnd pathL inputsL 0)
    have hrec : pathEnd pathR inputsR (pathEnd pathL inputsL 0) =
        boolWordToNat (scalarWord inputsL) • G + boolWordToNat (scalarWord inputsR) • Q + S := by
      rw [eq_sub_iff_add_eq.mpr hr, eq_sub_iff_add_eq.mpr hl, hS]; abel
    rw [hrec, hhead_divL inputsL hinL, hhead_divR inputsR hinR,
      inputWeight_kernel pathL inputsL hlenL ((inputWords_mem _ _).mp hinL),
      inputWeight_kernel pathR inputsR hlenR ((inputWords_mem _ _).mp hinR)]
    unfold F c
    congr 1
    change _ = (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ (nL + nR)) * _
    rw [show 2 * (pathWidths pathL).sum = nL + nL by dsimp [nL]; omega,
      show 2 * (pathWidths pathR).sum = nR + nR by dsimp [nR]; omega]
    simp only [pow_add]; ring
  rw [hmatch]
  have hinner (a : List Bool) :
      ((inputWords (pathWidths pathR)).map (fun inputs => F a (scalarWord inputs))).sum =
        ((fourierOutcomes nR).map (F a)).sum :=
    scalarWords_sum _ (F a)
  simp_rw [hinner]
  rw [scalarWords_sum (pathWidths pathL) (fun a => ((fourierOutcomes nR).map (F a)).sum)]
  have hsl : (pathL.map Prod.snd).flatten = (((fL, bL) :: ltail).map Prod.snd).flatten := by
    simp [pathL, logicalPath, List.map_map, Function.comp_def]
  have hsr : (pathR.map Prod.snd).flatten = (((fR, bR) :: rtail).map Prod.snd).flatten := by
    simp [pathR, logicalPath, List.map_map, Function.comp_def]
  unfold windowedPointState
  simp only [map_smul, stateLinear_list_sum, List.map_map, Function.comp_def, List.smul_sum, smul_smul]
  rw [← hwl, ← hwr, ← hsl, ← hsr]
  apply congrArg List.sum; apply List.map_congr_left; intro a _
  apply congrArg List.sum; apply List.map_congr_left; intro b _
  have hket : Finsupp.lmapDomain ℂ ℂ (shiftBasis S root)
      (ket (pointWrite (boolWordToNat a • G + boolWordToNat b • Q) root)) =
      ket (pointWrite (boolWordToNat a • G + boolWordToNat b • Q + S) root) := by
    simp only [ket, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, shiftBasis_pointWrite]
  rw [hket]

theorem windowed_idealTwoAxes_event_mass_anyBias {n : Nat} {read : ConstantBit n → Bool}
    (Q : Point) (root : BasisState) (ψ : State)
    (fL : WindowModel read) (restL : List (WindowModel read))
    (fR : WindowModel read) (restR : List (WindowModel read))
    (hfL : WindowedFirstRule root ψ fL)
    (hfR : WindowedPointRule root fR)
    (hrest : ∀ w ∈ restL ++ restR, PointRule root w)
    (hwL : ModelWeights G (fL :: restL)) (hwR : ModelWeights Q (fR :: restR))
    (J : Instrument) (hJ : ∀ φ, J.bornMass φ = normSq φ) (accept : Nat → Nat → Bool) :
    (idealTwoAxes (fL :: restL) (fR :: restR) (fun lhs rhs =>
      if accept (fourierWordLSB lhs.reverse) (fourierWordLSB rhs.reverse) then J else List.nil)).bornMass ψ =
      windowedEventMass Q root (precision (fL :: restL)) (precision (fR :: restR)) accept := by
  unfold idealTwoAxes
  rw [idealAxis_paths_mass]
  have h1 : ((outputPaths (fL :: restL)).map (fun lbp =>
      (idealAxis (fR :: restR) List.nil (fun rhs =>
        if accept (fourierWordLSB ((lbp.map Prod.snd).flatten.reverse ++ List.nil).reverse)
            (fourierWordLSB rhs.reverse) then J else List.nil)).bornMass (modelBranch lbp List.nil ψ))).sum =
      ((outputPaths (fL :: restL)).map (fun lbp =>
        ((outputPaths (fR :: restR)).map (fun rbp =>
          if accept (fourierWordLSB (lbp.map Prod.snd).flatten) (fourierWordLSB (rbp.map Prod.snd).flatten) then
            normSq (windowedPointState Q root (precision (fL :: restL)) (precision (fR :: restR))
              (lbp.map Prod.snd).flatten (rbp.map Prod.snd).flatten) else 0)).sum)).sum := by
    apply congrArg List.sum; apply List.map_congr_left; intro lbp hlbp
    rw [idealAxis_paths_mass]
    apply congrArg List.sum; apply List.map_congr_left; intro rbp hrbp
    rw [windowed_two_modelBranches_anyBias Q root ψ fL restL fR restR hfL hfR hrest hwL hwR lbp hlbp rbp hrbp]
    simp only [List.append_nil, List.reverse_reverse]
    split_ifs
    · rw [hJ, lmapDomain_inj_normSq (shiftBasis_injective _ _)]
    · simp [Instrument.bornMass]
  rw [h1]
  have hsum_out : ∀ (ws : List (WindowModel read)) (g : List Bool → ℝ),
      ((outputPaths ws).map (fun p => g (p.map Prod.snd).flatten)).sum =
        ((fourierOutcomes (precision ws)).map g).sum := by
    intro ws g
    rw [outputPaths_zip, List.map_map]
    have hflat := inputWords_flatten (ws.map (fun x => x.physical.wires.length))
    change _ = ((fourierOutcomes (ws.map (fun x => x.physical.wires.length)).sum).map g).sum
    rw [← hflat, List.map_map]
    apply congrArg List.sum; apply List.map_congr_left; intro ins hins
    have hl : ins.length = ws.length := by
      have := (inputWords_mem _ _).mp hins
      simpa using congrArg List.length this
    simp only [Function.comp_def]
    rw [List.map_snd_zip (by omega : ins.length ≤ ws.length)]
  have hinner (x : List Bool) :
      ((outputPaths (fR :: restR)).map (fun rbp =>
        if accept (fourierWordLSB x) (fourierWordLSB (rbp.map Prod.snd).flatten) then
          normSq (windowedPointState Q root (precision (fL :: restL)) (precision (fR :: restR))
            x (rbp.map Prod.snd).flatten) else 0)).sum =
      ((fourierOutcomes (precision (fR :: restR))).map (fun y =>
        if accept (fourierWordLSB x) (fourierWordLSB y) then
          normSq (windowedPointState Q root (precision (fL :: restL)) (precision (fR :: restR)) x y) else 0)).sum :=
    hsum_out (fR :: restR) (fun y =>
      if accept (fourierWordLSB x) (fourierWordLSB y) then
        normSq (windowedPointState Q root (precision (fL :: restL)) (precision (fR :: restR)) x y) else 0)
  simp_rw [hinner]
  exact hsum_out (fL :: restL) (fun x =>
    ((fourierOutcomes (precision (fR :: restR))).map (fun y =>
      if accept (fourierWordLSB x) (fourierWordLSB y) then
        normSq (windowedPointState Q root (precision (fL :: restL)) (precision (fR :: restR)) x y) else 0)).sum)

theorem windowed_physicalTwoAxes_event_mass_anyBias {n : Nat} {read : ConstantBit n → Bool}
    (Q : Point) (root : BasisState) (ψ : State)
    (fL : WindowModel read) (restL : List (WindowModel read))
    (fR : WindowModel read) (restR : List (WindowModel read))
    (hfL : WindowedFirstRule root ψ fL)
    (hfR : WindowedPointRule root fR)
    (hrest : ∀ w ∈ restL ++ restR, PointRule root w)
    (hwL : ModelWeights G (fL :: restL)) (hwR : ModelWeights Q (fR :: restR))
    (hready : Ready ((fL :: restL) ++ (fR :: restR)) ψ)
    (start : Nat) (history : Fin start → Bool)
    (J : Instrument) (hJ : ∀ φ, J.bornMass φ = normSq φ) (accept : Nat → Nat → Bool) :
    (selectedTwoAxes (fL :: restL) (fR :: restR) start history (fun lhs rhs =>
      if accept (fourierWordLSB lhs.reverse) (fourierWordLSB rhs.reverse) then J else List.nil)).bornMass ψ =
      windowedEventMass Q root (precision (fL :: restL)) (precision (fR :: restR)) accept := by
  rw [selectedTwoAxes_mass (fL :: restL) (fR :: restR) start history _ ψ hready]
  exact windowed_idealTwoAxes_event_mass_anyBias Q root ψ fL restL fR restR hfL hfR hrest hwL hwR J hJ accept

/-! ### `prependCircuit` and predicate-preservation lemmas -/

def prependCircuit {n s e : Nat} (c : Circuit) (p : Straight n s e) : Straight n s e :=
  (literalProgram c).append p

theorem prependCircuit_wellFormed {n s e : Nat} (c : Circuit) (p : Straight n s e)
    (hc : CircuitWellFormed c) (hp : p.WellFormed) : (prependCircuit c p).WellFormed :=
  straight_append_wellFormed _ _ (literalProgram_wellFormed c hc) hp

theorem literalProgram_slots {n s : Nat} (c : Circuit) :
    (literalProgram (n := n) (s := s) c).gateSlots = c.length := by
  induction c with
  | nil => rfl
  | cons g gs ih =>
    change 1 + (literalProgram (n := n) (s := s) gs).gateSlots = gs.length + 1
    rw [ih]; omega

theorem prependCircuit_slots {n s e : Nat} (c : Circuit) (p : Straight n s e) :
    (prependCircuit c p).gateSlots = c.length + p.gateSlots := by
  unfold prependCircuit
  rw [Straight.gateSlots_append, literalProgram_slots]

theorem literalProgram_straightWires {n s : Nat} (c : Circuit) :
    straightWires (literalProgram (n := n) (s := s) c) ⊆ circuitWires c := by
  induction c with
  | nil => intro w hw; simp [literalProgram, gateProgram, straightWires] at hw
  | cons g gs ih =>
    intro w hw
    change w ∈ straightWires (.gate (.literal g) (literalProgram gs)) at hw
    simp only [straightWires, templateGateWires, List.mem_append] at hw
    simp only [circuitWires, List.flatMap_cons, List.mem_append]
    rcases hw with hw | hw
    · exact Or.inl hw
    · exact Or.inr (ih hw)

theorem prependCircuit_support {n s e : Nat} (c : Circuit) (p : Straight n s e) (ws : List Wire)
    (hc : circuitWires c ⊆ ws) (hp : ∀ read history, (p.instantiate read history).wires ⊆ ws)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    ((prependCircuit c p).instantiate read history).wires ⊆ ws := by
  unfold prependCircuit
  apply outer_append_support _ _ read history ws
  · exact (straight_instantiate_support _ read history).trans ((literalProgram_straightWires c).trans hc)
  · intro h; exact hp read h

theorem prependCircuit_weight4 {n s e : Nat} (c : Circuit) (p : Straight n s e) :
    ConditionalCatalyst.weight4 (prependCircuit c p) =
      ConditionalCatalyst.weight4 (literalProgram (n := n) (s := s) c) +
        ConditionalCatalyst.weight4 p :=
  ConditionalCatalyst.weight4_append _ _

theorem prependCircuit_added {n s e : Nat} (c : Circuit) (p : Straight n s e) :
    AndGadget.added (prependCircuit c p) =
      AndGadget.added (literalProgram (n := n) (s := s) c) + AndGadget.added p :=
  AndGadget.added_append _ _

theorem prependCircuit_cost18 {n s e : Nat} (c : Circuit) (p : Straight n s e) :
    Trim18.cost18 (prependCircuit c p) =
      Trim18.cost18 (literalProgram (n := n) (s := s) c) + Trim18.cost18 p :=
  Trim18.cost18_append _ _

theorem branchCoherent_on_supported {U : State →ₗ[ℂ] State} {V : BasisState → Prop}
    {b : InstrumentBranch} {α : ℂ} (hb : BranchCoherentOn U V b α)
    (ψ : State) (hψ : SupportedOn V ψ) : b.kraus ψ = α • U ψ := by
  induction ψ using Finsupp.induction with
  | zero => simp
  | single_add s c f hsf hc ih =>
    have hs : V s := hψ s (by
      simp [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.notMem_support_iff.mp hsf, hc])
    have hf : SupportedOn V f := fun t ht => hψ t (by
      have hts : t ≠ s := fun h => hsf (h ▸ Finsupp.mem_support_iff.mpr ht)
      rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hts, zero_add]
      exact ht)
    have hket : Finsupp.single s c = c • ket s := by ext u; simp [ket]
    rw [map_add, map_add, smul_add, ih hf, hket, map_smul, map_smul, hb s hs, smul_comm]

theorem prependCircuit_coherent {n s e : Nat} (c : Circuit) (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool)
    (U : State →ₗ[ℂ] State) (V W : BasisState → Prop)
    (hp : CoherentlyImplementsOn (p.instantiate read history) U V)
    (hVW : ∀ x, W x → SupportedOn V (Quantum.run c (ket x))) :
    CoherentlyImplementsOn ((prependCircuit c p).instantiate read history) (U.comp (Quantum.run c)) W := by
  unfold prependCircuit CoherentlyImplementsOn
  have hlit : ((literalProgram (n := n) (s := s) c).instantiate read history).run =
      [{ history := List.nil, kraus := Quantum.run c }] := by
    rw [ChallengeMigration.literalProgram_run]
    change ([{ history := List.nil, kraus := LinearMap.id.comp (Quantum.run c) }] : Instrument) = _
    simp
  rw [Single.append_run_history, hlit]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_map, Function.comp_def]
  have hhist : Single.historyAfter s history List.nil = history := by
    funext i; simp [Single.historyAfter, List.ofFn_getElem]
  rw [hhist]
  obtain ⟨coeffs, hfa, hsum⟩ := hp
  refine ⟨coeffs, ?_, hsum⟩
  rw [List.forall₂_map_left_iff]
  refine hfa.imp (fun b α hb => ?_)
  intro x hx
  change b.kraus (Quantum.run c (ket x)) = α • U (Quantum.run c (ket x))
  exact branchCoherent_on_supported hb (Quantum.run c (ket x)) (hVW x hx)

theorem gate_preserves_pred (g : Gate) (V : BasisState → Prop)
    (hV : ∀ s w b, w ∈ gateWires g → V s → V (s[w ↦ b]))
    (s : BasisState) (hs : V s) : SupportedOn V (applyGate g (ket s)) := by
  cases g with
  | X t =>
    rw [applyGate_X_ket]
    exact supportedOn_ket _ _ (hV s t (!s t) (by simp [gateWires]) hs)
  | H t =>
    rw [applyGate_H_ket]
    apply Support.add
    · exact Support.smul _ (supportedOn_ket _ _ (hV s t false (by simp [gateWires]) hs))
    · exact Support.smul _ (supportedOn_ket _ _ (hV s t true (by simp [gateWires]) hs))
  | P dir k t =>
    rw [applyGate_P_ket]
    exact Support.smul _ (supportedOn_ket _ _ hs)
  | CX c t =>
    rw [applyGate_CX_ket]
    exact supportedOn_ket _ _ (hV s t (s t ^^ s c) (by simp [gateWires]) hs)
  | CCX c1 c2 t =>
    rw [applyGate_CCX_ket]
    exact supportedOn_ket _ _ (hV s t (s t ^^ (s c1 && s c2)) (by simp [gateWires]) hs)

theorem circuit_preserves_pred (c : Circuit) (V : BasisState → Prop)
    (hV : ∀ s w b, w ∈ circuitWires c → V s → V (s[w ↦ b]))
    (s : BasisState) (hs : V s) : SupportedOn V (Quantum.run c (ket s)) := by
  induction c generalizing s with
  | nil => simpa [Quantum.run] using supportedOn_ket _ _ hs
  | cons g gs ih =>
    rw [Quantum.run_cons]
    apply Support.linear V V (Quantum.run gs)
    · intro t ht
      exact ih (fun u w b hw hu => hV u w b (by simp [circuitWires] at hw ⊢; exact Or.inr hw) hu) t ht
    · exact gate_preserves_pred g V (fun u w b hw hu => hV u w b (by simp [circuitWires, hw]) hu) s hs

theorem relabelBasis_phaseWordState (e : Wire ≃ Wire) (ws : List Wire) (bs : List Bool) (s : BasisState) :
    relabelBasis e (phaseWordState ws bs s) = phaseWordState (ws.map e) bs (relabelBasis e s) := by
  induction ws generalizing bs s with
  | nil => cases bs <;> rfl
  | cons w ws ih =>
    cases bs with
    | nil => rfl
    | cons b bs =>
      simp only [phaseWordState, List.map_cons, ih, relabelBasis_upd]

end
end ShorECDLP.Entrant.Schedule26Bridge

/-! ### Part 2b: Local-catalyst axis combinators (`CatAxis`) -/

namespace ShorECDLP.Entrant.CatAxis
open Quantum Challenge Secp256k1 AndGadget ConditionalCatalyst ApproximatePhase34
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open Single Single.Distribution LocalFour Trim18
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
attribute [local irreducible] fourierOutcomes

local instance catAxisBody : Single.WindowBody := PathShare.bodyCF
local instance catAxisRes : Single.ProducerResources catAxisBody :=
  Single.ProducerResources.ofBody PathShare.bodyCF
    (by change resetWires.Nodup; exact resetWires_nodup)
    (by change (0 : Wire) ∈ resetWires; decide)
    (by change (1 : Wire) ∈ resetWires; decide)

/-! #### `CatCoherent` combinators -/

theorem relabelState_prep (e : Wire ≃ Wire) (y : Wire) (ψ : State) :
    relabelState e (Prep y ψ) = Prep (e y) (relabelState e ψ) := by
  have hm : (Catalyst.prepare y).map (Gate.relabel e) = Catalyst.prepare (e y) := rfl
  rw [Prep, Prep, ← hm]
  exact (Quantum.run_relabel e (Catalyst.prepare y) ψ).symm

theorem catCoherent_relabel (e : Wire ≃ Wire) (y : Wire) (C : AdaptiveCircuit)
    (U : State →ₗ[ℂ] State) (V : BasisState → Prop)
    (h : CatCoherent y C U V) :
    CatCoherent (e y) (C.relabel e)
      ((relabelState e).comp (U.comp (relabelState e.symm)))
      (fun s => V (relabelBasis e.symm s)) := by
  obtain ⟨cs, hal, hmass⟩ := h
  refine ⟨cs, ?_, hmass⟩
  rw [AdaptiveCircuit.run_relabel, List.forall₂_map_left_iff]
  refine hal.imp (fun b c hb s hs => ?_)
  change relabelState e (b.kraus (relabelState e.symm (Prep (e y) (ket s)))) = _
  have hp1 : relabelState e.symm (Prep (e y) (ket s)) = Prep y (ket (relabelBasis e.symm s)) := by
    rw [relabelState_prep, Equiv.symm_apply_apply, relabelState_ket]
  rw [hp1, hb (relabelBasis e.symm s) hs, map_smul, relabelState_prep]
  simp only [LinearMap.comp_apply, relabelState_ket]

theorem catBranch_on_supported {y : Wire} {U : State →ₗ[ℂ] State} {V : BasisState → Prop}
    {b : InstrumentBranch} {c : ℂ}
    (hb : ∀ s, V s → b.kraus (Prep y (ket s)) = c • Prep y (U (ket s)))
    (ψ : State) (hψ : SupportedOn V ψ) :
    b.kraus (Prep y ψ) = c • Prep y (U ψ) := by
  induction ψ using Finsupp.induction with
  | zero => simp
  | single_add s a f hsf ha ih =>
    have hs : V s := hψ s (by
      simp [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.notMem_support_iff.mp hsf, ha])
    have hf : SupportedOn V f := fun t ht => hψ t (by
      have hts : t ≠ s := fun h => hsf (h ▸ Finsupp.mem_support_iff.mpr ht)
      rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hts, zero_add]
      exact ht)
    have hket : Finsupp.single s a = a • ket s := by ext u; simp [ket]
    rw [map_add, map_add, map_add, map_add, smul_add, ih hf, hket,
      map_smul, map_smul, map_smul, map_smul, hb s hs, smul_comm]

private theorem literals_append {n s e : Nat} (c₁ c₂ : Circuit) (p : Straight n s e) :
    AndGadget.literals c₁ (AndGadget.literals c₂ p) = AndGadget.literals (c₁ ++ c₂) p := by
  induction c₁ with
  | nil => rfl
  | cons g gs ih =>
    simp only [AndGadget.literals, List.cons_append, List.foldr_cons]
    exact congrArg (Straight.gate (.literal g)) ih

private theorem literals_append_straight {n s m e : Nat} (c : Circuit) (p : Straight n s m)
    (q : Straight n m e) :
    (AndGadget.literals c p).append q = AndGadget.literals c (p.append q) := by
  induction c with
  | nil => rfl
  | cons g gs ih =>
    simp only [AndGadget.literals, List.foldr_cons, Straight.append]
    exact congrArg (Straight.gate (.literal g)) ih

theorem compile_literalProgram_eq {n s : Nat} (y : Wire) (c : Circuit) :
    ConditionalCatalyst.compile y (literalProgram (n := n) (s := s) c) =
      AndGadget.literals (compileCircuit y c) .done := by
  induction c with
  | nil => rfl
  | cons g gs ih =>
    change AndGadget.literals (ConditionalCatalyst.replacement y g)
        (ConditionalCatalyst.compile y (literalProgram gs)) =
      AndGadget.literals (ConditionalCatalyst.replacement y g ++ compileCircuit y gs) .done
    rw [ih, literals_append]

theorem prependCompiledCircuit_catCoherent {n s e : Nat} (y : Wire) (c : Circuit)
    (p : Straight n s e) (read : ConstantBit n → Bool) (history : Fin s → Bool)
    (U : State →ₗ[ℂ] State) (V W : BasisState → Prop)
    (hy : y ∉ circuitWires c)
    (hWY : ∀ x, W x → x y = false)
    (hVW : ∀ x, W x → SupportedOn V (Quantum.run c (ket x)))
    (hp : CatCoherent y (p.instantiate read history) U V) :
    CatCoherent y (((ConditionalCatalyst.compile y (literalProgram c)).append p).instantiate read history)
      (U.comp (Quantum.run c)) W := by
  obtain ⟨cs, hal, hmass⟩ := hp
  refine ⟨cs, ?_, hmass⟩
  rw [compile_literalProgram_eq, literals_append_straight]
  change List.Forall₂ _ ((AndGadget.literals (compileCircuit y c) p).instantiate read history).run cs
  rw [LocalFour.literals_instantiate_run, List.forall₂_map_left_iff]
  refine hal.imp (fun b k hb x hx => ?_)
  change b.kraus (Quantum.run (compileCircuit y c) (Prep y (ket x))) = _
  rw [compileCircuit_prep y c hy (ket x) (supportedOn_ket _ _ (hWY x hx))]
  rw [catBranch_on_supported hb _ (hVW x hx)]
  simp only [LinearMap.comp_apply]

/-! #### Compiled semiclassical Fourier block on `Prep y` -/

theorem compile_castFinish {n s e f : Nat} (y : Wire) (h : e = f) (p : Straight n s e) :
    ConditionalCatalyst.compile y (castFinish h p) = castFinish h (ConditionalCatalyst.compile y p) := by
  subst f; rfl

theorem compile_feedbackProgram_run {n s e : Nat} (y : Wire) (dir : PhaseDir) (w : Wire)
    (indices : List (Fin s)) (k : Nat) (next : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    ((ConditionalCatalyst.compile y (feedbackProgram dir w indices k next)).instantiate read history).run =
      ((ConditionalCatalyst.compile y next).instantiate read history).run.map
        (fun b => ⟨b.history,
          b.kraus.comp (Quantum.run (compileCircuit y (fourierHistoryRotations dir w (indices.map history) k)))⟩) := by
  induction indices generalizing k with
  | nil =>
    simp only [feedbackProgram, List.map_nil, fourierHistoryRotations, compileCircuit, Quantum.run_nil]
    symm
    apply List.map_id'
  | cons i is ih =>
    simp only [feedbackProgram, ConditionalCatalyst.compile, LocalFour.recordLiterals_instantiate_run,
      ih, List.map_map, Function.comp_def, List.map_cons, fourierHistoryRotations, fourierFeedForward]
    apply List.map_congr_left
    intro b _
    cases hi : history i
    · simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append]
      exact congrArg (InstrumentBranch.mk b.history) (LinearMap.comp_id _)
    · simp only [↓reduceIte, List.cons_append, List.nil_append, compileCircuit]
      exact congrArg (InstrumentBranch.mk b.history) (LinearMap.ext fun ψ => by
        simp only [LinearMap.comp_apply, Quantum.run_append])

def compileFourierBranch (y : Wire) (dir : PhaseDir) : List Wire → List Bool → List Bool → State →ₗ[ℂ] State
  | [], _, [] => LinearMap.id
  | w :: ws, prior, b :: bs =>
      (compileFourierBranch y dir ws (b :: prior) bs).comp
        ((xResetKraus w b).comp (Quantum.run (compileCircuit y (fourierHistoryRotations dir w prior 2))))
  | _, _, _ => 0

theorem compile_fourierProgram_run (y : Wire) (n : Nat) (dir : PhaseDir) (ws : List Wire)
    (start : Nat) (prior : List (Fin start)) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((ConditionalCatalyst.compile y (fourierProgram n dir ws start prior)).instantiate read history).run =
      (fourierOutcomes ws.length).map (fun bs => ⟨bs, compileFourierBranch y dir ws (prior.map history) bs⟩) := by
  induction ws generalizing start with
  | nil =>
    simp [fourierProgram, ConditionalCatalyst.compile, Straight.instantiate, AdaptiveCircuit.run,
      fourierOutcomes, compileFourierBranch]
  | cons w ws ih =>
    simp only [fourierProgram, compile_castFinish, castFinish_instantiate, compile_feedbackProgram_run,
      ConditionalCatalyst.compile, Straight.instantiate, AdaptiveCircuit.run, ih]
    simp only [List.length_cons, fourierOutcomes, List.map_append, List.map_map, Function.comp_def,
      List.map_cons, Fin.lastCases_last, Fin.lastCases_castSucc]
    congr 1

theorem fourierHistoryRotations_wires (dir : PhaseDir) (w : Wire) (prior : List Bool) (k : Nat) :
    circuitWires (fourierHistoryRotations dir w prior k) ⊆ [w] := by
  induction prior generalizing k with
  | nil => intro u hu; simp [fourierHistoryRotations, circuitWires] at hu
  | cons b bs ih =>
    intro u hu
    simp only [fourierHistoryRotations, fourierFeedForward, circuitWires, List.flatMap_append,
      List.mem_append] at hu
    rcases hu with hu | hu
    · cases b <;> simp [gateWires] at hu; exact List.mem_singleton.mpr hu
    · exact ih (k + 1) hu

theorem compileFourierBranch_prep (y : Wire) (dir : PhaseDir) (ws : List Wire)
    (hy : y ∉ ws) (prior bits : List Bool) (ψ : State) (hψ : SupportedOn (fun s => s y = false) ψ) :
    compileFourierBranch y dir ws prior bits (Prep y ψ) = Prep y (fourierBranch dir ws prior bits ψ) ∧
      SupportedOn (fun s => s y = false) (fourierBranch dir ws prior bits ψ) := by
  induction ws generalizing prior bits ψ with
  | nil =>
    cases bits with
    | nil => exact ⟨rfl, hψ⟩
    | cons _ _ => exact ⟨by simp [compileFourierBranch, fourierBranch], by simp [fourierBranch, SupportedOn]⟩
  | cons w ws ih =>
    have hyw : y ≠ w := fun h => hy (h ▸ List.mem_cons_self)
    have hyws : y ∉ ws := fun h => hy (List.mem_cons_of_mem _ h)
    cases bits with
    | nil => exact ⟨by simp [compileFourierBranch, fourierBranch], by simp [fourierBranch, SupportedOn]⟩
    | cons b bs =>
      have hnw : y ∉ circuitWires (fourierHistoryRotations dir w prior 2) := fun hm =>
        hyw (List.mem_singleton.mp (fourierHistoryRotations_wires dir w prior 2 hm))
      have hrot_sup : SupportedOn (fun s => s y = false)
          (Quantum.run (fourierHistoryRotations dir w prior 2) ψ) :=
        LocalFour.circuit_frame y _ hnw ψ hψ
      have hres_sup : SupportedOn (fun s => s y = false)
          (xResetKraus w b (Quantum.run (fourierHistoryRotations dir w prior 2) ψ)) :=
        ConditionalCatalyst.reset_frame y w hyw b _ hrot_sup
      simp only [compileFourierBranch, fourierBranch, LinearMap.comp_apply]
      rw [compileCircuit_prep y _ hnw ψ hψ, Catalyst.prepare_reset y w hyw]
      exact ih hyws (b :: prior) bs _ hres_sup

/-! #### `CatWindow`, `axisCat`, `selectedAxisCat`, and `selectedTwoAxesCat` -/

structure CatWindow {n : Nat} (y : Wire) (read : ConstantBit n → Bool) where
  model : WindowModel read
  catPhys : Single.Window n
  wires_eq : catPhys.wires = model.physical.wires
  noY : y ∉ model.physical.wires
  catCoherent : ∀ start history,
    CatCoherent y ((catPhys.program start).instantiate read history) model.ideal model.valid
  idealY : ∀ ψ, SupportedOn model.valid ψ → SupportedOn (fun s => s y = false) (model.ideal ψ)

def axisCat {n : Nat} (y : Wire) :
    (ws : List (Single.Window n)) → (start : Nat) → List (Fin start) →
      Straight n start (start + Single.axisCount ws)
  | [], _, _ => .done
  | w :: ws, start, prior =>
    let fourier : Straight n (start + w.count) (start + w.count + w.wires.length) :=
      castFinish (by simp)
        (ConditionalCatalyst.compile y
          (fourierProgram n .inverse w.wires (start + w.count) (bankPrior w.count prior)))
    castFinish (by simp only [Single.axisCount]; omega)
      ((prepareOuterBank w.wires.reverse (w.program start)).append (fourier.append
        (axisCat y ws (start + w.count + w.wires.length) (nextPrior w.count w.wires.length prior))))

def taggedAxisCat {n : Nat} {y : Wire} {read : ConstantBit n → Bool} :
    List (CatWindow y read) → (start : Nat) → (Fin start → Bool) → List (Fin start) →
      List (List Bool × InstrumentBranch)
  | [], _, history, prior => [(prior.map history, ⟨[], LinearMap.id⟩)]
  | w :: ws, start, history, prior =>
      (((prepareOuterBank w.catPhys.wires.reverse (w.catPhys.program start)).instantiate read history).run).flatMap
        (fun a => (fourierOutcomes w.catPhys.wires.length).flatMap (fun bits =>
          let h₁ := Single.historyAfter (start + w.catPhys.count) history a.history
          let h₂ := Single.historyAfter (start + w.catPhys.count + w.catPhys.wires.length) h₁ bits
          (taggedAxisCat ws _ h₂ (nextPrior w.catPhys.count w.catPhys.wires.length prior)).map
            (fun b => (b.1, (a.seq ⟨bits, compileFourierBranch y .inverse w.catPhys.wires (prior.map history) bits⟩).seq b.2))))

def selectedAxisCat {n : Nat} {y : Wire} {read : ConstantBit n → Bool}
    (ws : List (CatWindow y read)) (start : Nat) (history : Fin start → Bool)
    (prior : List (Fin start)) (terminal : List Bool → Instrument) : Instrument :=
  (taggedAxisCat ws start history prior).flatMap (fun a => (terminal a.1).map a.2.seq)

theorem axisCat_run_tagged {n : Nat} {y : Wire} {read : ConstantBit n → Bool}
    (ws : List (CatWindow y read)) (start : Nat) (history : Fin start → Bool)
    (prior : List (Fin start)) :
    ((axisCat y (ws.map CatWindow.catPhys) start prior).instantiate read history).run =
      (taggedAxisCat ws start history prior).map Prod.snd := by
  induction ws generalizing start with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, axisCat, castFinish_instantiate]
    rw [append_run_history]
    simp only [taggedAxisCat, List.map_flatMap, List.map_map, Function.comp_def]
    apply List.flatMap_congr
    intro a ha
    rw [append_run_history]
    simp only [castFinish_instantiate]
    rw [compile_fourierProgram_run, bankPrior_map]
    simp only [List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def]
    apply List.flatMap_congr
    intro bits hb
    rw [ih]
    simp only [List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro x _
    rcases a with ⟨ah, ak⟩; rcases x with ⟨xt, xh, xk⟩
    simp [InstrumentBranch.seq, List.append_assoc, LinearMap.comp_assoc]

theorem taggedAxisCat_transcript {n : Nat} {y : Wire} {read : ConstantBit n → Bool}
    (ws : List (CatWindow y read)) (start : Nat) (history : Fin start → Bool)
    (prior : List (Fin start)) (tagged : List Bool × InstrumentBranch)
    (ht : tagged ∈ taggedAxisCat ws start history prior) :
    ∃ bits, Transcript (ws.map (fun w => (w.catPhys.count, w.catPhys.wires.length)))
        tagged.2.history bits ∧ tagged.1 = bits.reverse ++ prior.map history := by
  induction ws generalizing start tagged with
  | nil =>
    simp only [taggedAxisCat, List.mem_singleton] at ht
    subst tagged
    exact ⟨[], Transcript.nil, rfl⟩
  | cons w ws ih =>
    obtain ⟨a, ha, ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨bits, hb, ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨b, hbt, rfl⟩ := List.mem_map.mp ht
    obtain ⟨out, htrans, htag⟩ := ih _ _ _ b hbt
    have hla : a.history.length = w.catPhys.count := by
      have h := straight_history_length _ read history a ha
      omega
    have hlb := (fourierOutcomes_mem _ _).mp hb
    refine ⟨bits ++ out, ?_, ?_⟩
    · simpa only [List.map_cons, InstrumentBranch.seq, List.append_assoc] using
        Transcript.cons w.catPhys.count w.catPhys.wires.length _ a.history bits b.2.history out hla hlb htrans
    · rw [htag, nextPrior_map _ _ _ _ _ _ hla hlb]
      simp only [List.reverse_append, List.append_assoc]

theorem taggedAxisCat_readWord {n : Nat} {y : Wire} {read : ConstantBit n → Bool}
    (ws : List (CatWindow y read)) (start : Nat) (history : Fin start → Bool)
    (tagged : List Bool × InstrumentBranch)
    (ht : tagged ∈ taggedAxisCat ws start history List.nil) (after : List Bool) :
    ShorECDLP.Challenge.readWord (List.ofFn history ++ tagged.2.history ++ after)
      (Single.axisPositions (ws.map CatWindow.catPhys) start) =
        some (fourierWordLSB tagged.1.reverse) := by
  obtain ⟨bits, htrans, htag⟩ := taggedAxisCat_transcript ws start history List.nil tagged ht
  rw [htag]
  simpa only [List.map_nil, List.append_nil, List.reverse_reverse, List.length_ofFn,
    Single.axisPositions, List.map_map, Function.comp_def] using htrans.readWord (List.ofFn history) after

theorem taggedAxisCat_history_length {n : Nat} {y : Wire} {read : ConstantBit n → Bool}
    (ws : List (CatWindow y read)) (start : Nat) (history : Fin start → Bool)
    (prior : List (Fin start)) (tagged : List Bool × InstrumentBranch)
    (ht : tagged ∈ taggedAxisCat ws start history prior) :
    tagged.2.history.length = Single.axisCount (ws.map CatWindow.catPhys) := by
  have hb : tagged.2 ∈ ((axisCat y (ws.map CatWindow.catPhys) start prior).instantiate read history).run := by
    rw [axisCat_run_tagged]
    exact List.mem_map.mpr ⟨tagged, ht, rfl⟩
  have h := straight_history_length _ read history tagged.2 hb
  omega

theorem selectedAxisCat_cons_mass {n : Nat} {y : Wire} {read : ConstantBit n → Bool}
    (w : CatWindow y read) (ws : List (CatWindow y read)) (start : Nat)
    (history : Fin start → Bool) (prior : List (Fin start))
    (terminal : List Bool → Instrument) (ψ : State) :
    (selectedAxisCat (w :: ws) start history prior terminal).bornMass ψ =
      (((w.catPhys.program start).instantiate read history).run.map (fun a =>
        ((fourierOutcomes w.catPhys.wires.length).map (fun bits =>
          let h₁ := Single.historyAfter (start + w.catPhys.count) history a.history
          let h₂ := Single.historyAfter (start + w.catPhys.count + w.catPhys.wires.length) h₁ bits
          (selectedAxisCat ws _ h₂ (nextPrior w.catPhys.count w.catPhys.wires.length prior) terminal).bornMass
            (compileFourierBranch y .inverse w.catPhys.wires (prior.map history) bits
              (a.kraus (Quantum.run (w.catPhys.wires.reverse.map Gate.H) ψ))))).sum)).sum := by
  have hcons : selectedAxisCat (w :: ws) start history prior terminal =
      (((prepareOuterBank w.catPhys.wires.reverse (w.catPhys.program start)).instantiate read history).run).flatMap
        (fun a => (fourierOutcomes w.catPhys.wires.length).flatMap (fun bits =>
          let h₁ := Single.historyAfter (start + w.catPhys.count) history a.history
          let h₂ := Single.historyAfter (start + w.catPhys.count + w.catPhys.wires.length) h₁ bits
          (selectedAxisCat ws _ h₂ (nextPrior w.catPhys.count w.catPhys.wires.length prior) terminal).map
            (a.seq ⟨bits, compileFourierBranch y .inverse w.catPhys.wires (prior.map history) bits⟩).seq)) := by
    simp only [selectedAxisCat, taggedAxisCat, List.flatMap_assoc, List.flatMap_map,
      List.map_flatMap, List.map_map, Function.comp_def]
    apply List.flatMap_congr; intro a _
    apply List.flatMap_congr; intro bits _
    apply List.flatMap_congr; intro b _
    apply List.map_congr_left; intro c _
    rcases a with ⟨ah, ak⟩; rcases b with ⟨tag, bh, bk⟩; rcases c with ⟨ch, ck⟩
    simp [InstrumentBranch.seq, LinearMap.comp_assoc, List.append_assoc]
  rw [hcons, prepare_run]
  simp only [flat_mass, prefixed_mass, List.flatMap_map,
    InstrumentBranch.seq, LinearMap.comp_apply, List.nil_append]

private theorem sum_forall2_normSq_mul {α : Type} (xs : List α) (cs : List ℂ) (f : α → ℝ) (R : ℝ)
    {P : α → ℂ → Prop}
    (hal : List.Forall₂ P xs cs)
    (hf : ∀ a ∈ xs, ∀ c, P a c → f a = Complex.normSq c * R)
    (hmass : (cs.map Complex.normSq).sum = 1) :
    (xs.map f).sum = R := by
  have h : (xs.map f).sum = (cs.map Complex.normSq).sum * R := by
    clear hmass
    induction hal with
    | nil => simp
    | cons hd tl ih =>
      simp only [List.map_cons, List.sum_cons, hf _ List.mem_cons_self _ hd,
        ih (fun a ha c hp => hf a (List.mem_cons_of_mem _ ha) c hp), add_mul]
  rw [h, hmass, one_mul]

private theorem forall2_mem_left {α β : Type} {P : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ P xs ys) {a : α} (ha : a ∈ xs) : ∃ b, P a b := by
  induction h with
  | nil => cases ha
  | cons hd tl ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨_, hd⟩
    · exact ih ha

private theorem state_normSq_smul (c : ℂ) (ψ : State) :
    normSq (c • ψ) = Complex.normSq c * normSq ψ := by
  unfold normSq
  rw [inner_smul_smul, ← Complex.normSq_eq_conj_mul_self]
  simp

private theorem bornMass_smul (I : Instrument) (c : ℂ) (ψ : State) :
    I.bornMass (c • ψ) = Complex.normSq c * I.bornMass ψ := by
  induction I with
  | nil => simp [Instrument.bornMass]
  | cons b bs ih =>
    change normSq (b.kraus (c • ψ)) + Instrument.bornMass bs (c • ψ) =
      Complex.normSq c * (normSq (b.kraus ψ) + Instrument.bornMass bs ψ)
    rw [map_smul, state_normSq_smul, ih]; ring

private theorem sum_map_mul_left_real {α : Type} (xs : List α) (r : ℝ) (f : α → ℝ) :
    (xs.map (fun x => r * f x)).sum = r * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih, mul_add]

theorem selectedAxisCat_mass {n : Nat} {y : Wire} {read : ConstantBit n → Bool}
    (ws : List (CatWindow y read)) (start : Nat) (history : Fin start → Bool)
    (prior : List (Fin start))
    (physTerm idealTerm : List Bool → Instrument)
    (hterm : ∀ tag φ, SupportedOn (fun s => s y = false) φ →
      (physTerm tag).bornMass (Prep y φ) = (idealTerm tag).bornMass φ)
    (ψ : State) (hψ : Ready (ws.map CatWindow.model) ψ)
    (hψY : SupportedOn (fun s => s y = false) ψ) :
    (selectedAxisCat ws start history prior physTerm).bornMass (Prep y ψ) =
      (idealAxis (ws.map CatWindow.model) (prior.map history) idealTerm).bornMass ψ := by
  induction ws generalizing start ψ with
  | nil =>
    simp only [selectedAxisCat, taggedAxisCat, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.map_nil, idealAxis]
    rw [prefixed_mass ⟨[], LinearMap.id⟩ _ (Prep y ψ)]
    exact hterm (prior.map history) ψ hψY
  | cons w ws ih =>
    rw [selectedAxisCat_cons_mass]
    simp only [List.map_cons, idealAxis_cons_mass]
    have hH_nw : y ∉ circuitWires (w.catPhys.wires.reverse.map Gate.H) := by
      intro hm
      simp only [circuitWires, List.mem_flatMap, List.mem_map] at hm
      obtain ⟨g, ⟨v, hv, rfl⟩, hwg⟩ := hm
      simp only [gateWires, List.mem_singleton] at hwg
      have hv' : y ∈ w.catPhys.wires.reverse := hwg ▸ hv
      rw [List.mem_reverse, w.wires_eq] at hv'
      exact w.noY hv'
    have hH_prep : Quantum.run (w.catPhys.wires.reverse.map Gate.H) (Prep y ψ) =
        Prep y (Quantum.run (w.model.physical.wires.reverse.map Gate.H) ψ) := by
      rw [prep_circuit y _ hH_nw ψ, w.wires_eq]
    obtain ⟨cs, hal, hmass⟩ := w.catCoherent start history
    apply sum_forall2_normSq_mul _ cs _ _ hal _ hmass
    intro a ha_mem c ha
    have ha_len : a.history.length = w.catPhys.count := by
      have h := straight_history_length _ read history a ha_mem
      omega
    have ha_state : a.kraus (Quantum.run (w.catPhys.wires.reverse.map Gate.H) (Prep y ψ)) =
        c • Prep y (w.model.ideal (Quantum.run (w.model.physical.wires.reverse.map Gate.H) ψ)) := by
      rw [hH_prep]
      exact catBranch_on_supported ha _ hψ.1
    have hidealY : SupportedOn (fun s => s y = false)
        (w.model.ideal (Quantum.run (w.model.physical.wires.reverse.map Gate.H) ψ)) :=
      w.idealY _ hψ.1
    rw [w.wires_eq]
    have hinner : ∀ bits ∈ fourierOutcomes w.model.physical.wires.length,
        (selectedAxisCat ws (start + w.catPhys.count + w.model.physical.wires.length)
          (Single.historyAfter (start + w.catPhys.count + w.model.physical.wires.length)
            (Single.historyAfter (start + w.catPhys.count) history a.history) bits)
          (nextPrior w.catPhys.count w.model.physical.wires.length prior) physTerm).bornMass
          (compileFourierBranch y .inverse w.model.physical.wires (prior.map history) bits
            (a.kraus (Quantum.run (w.model.physical.wires.reverse.map Gate.H) (Prep y ψ)))) =
        Complex.normSq c *
          (idealAxis (ws.map CatWindow.model) (bits.reverse ++ prior.map history) idealTerm).bornMass
            (w.model.step (prior.map history) bits ψ) := by
      intro bits hb
      have ha_state' : a.kraus (Quantum.run (w.model.physical.wires.reverse.map Gate.H) (Prep y ψ)) =
          c • Prep y (w.model.ideal (Quantum.run (w.model.physical.wires.reverse.map Gate.H) ψ)) := by
        simpa only [w.wires_eq] using ha_state
      rw [ha_state', map_smul]
      have hfb := compileFourierBranch_prep y .inverse w.model.physical.wires w.noY (prior.map history) bits _ hidealY
      rw [hfb.1, bornMass_smul]
      have hstep_eq : fourierBranch .inverse w.model.physical.wires (prior.map history) bits
          (w.model.ideal (Quantum.run (w.model.physical.wires.reverse.map Gate.H) ψ)) =
          w.model.step (prior.map history) bits ψ := rfl
      rw [hstep_eq] at hfb ⊢
      have hih := ih (start + w.catPhys.count + w.model.physical.wires.length)
        (Single.historyAfter (start + w.catPhys.count + w.model.physical.wires.length)
          (Single.historyAfter (start + w.catPhys.count) history a.history) bits)
        (nextPrior w.catPhys.count w.model.physical.wires.length prior)
        (w.model.step (prior.map history) bits ψ) (hψ.2 (prior.map history) bits) hfb.2
      rw [hih, nextPrior_map _ _ _ _ _ _ ha_len ((fourierOutcomes_mem _ _).mp hb)]
    have hsum_eq :
        ((fourierOutcomes w.model.physical.wires.length).map (fun bits =>
          (selectedAxisCat ws (start + w.catPhys.count + w.model.physical.wires.length)
            (Single.historyAfter (start + w.catPhys.count + w.model.physical.wires.length)
              (Single.historyAfter (start + w.catPhys.count) history a.history) bits)
            (nextPrior w.catPhys.count w.model.physical.wires.length prior) physTerm).bornMass
            (compileFourierBranch y .inverse w.model.physical.wires (prior.map history) bits
              (a.kraus (Quantum.run (w.model.physical.wires.reverse.map Gate.H) (Prep y ψ)))))).sum =
        ((fourierOutcomes w.model.physical.wires.length).map (fun bits =>
          Complex.normSq c *
            (idealAxis (ws.map CatWindow.model) (bits.reverse ++ prior.map history) idealTerm).bornMass
              (w.model.step (prior.map history) bits ψ))).sum := by
      apply congrArg List.sum
      exact List.map_congr_left hinner
    rw [hsum_eq, sum_map_mul_left_real]

private theorem unprep_prep (y : Wire) (ψ : State) :
    Quantum.run [.P .inverse 2 y, .H y] (Prep y ψ) = ψ := by
  have hp : applyGate (.P .inverse 2 y) (applyGate (.P .forward 2 y) (applyGate (.H y) ψ)) =
      applyGate (.H y) ψ := by
    induction (applyGate (.H y) ψ) using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single s c =>
      have hket : Finsupp.single s c = c • ket s := by ext u; simp [ket]
      rw [hket, map_smul, map_smul, applyGate_P_ket, map_smul, applyGate_P_ket, smul_smul]
      cases hs : s y
      · simp
      · have hprod : phaseCoeff .inverse 2 * phaseCoeff .forward 2 = 1 := by
          simpa [PhaseDir.adjoint] using phaseCoeff_adjoint_mul .forward 2
        simp only [↓reduceIte]
        rw [smul_smul, mul_assoc, mul_comm (phaseCoeff .forward 2), hprod, mul_one]
  change applyGate (.H y) (applyGate (.P .inverse 2 y) (applyGate (.P .forward 2 y) (applyGate (.H y) ψ))) = ψ
  rw [hp]
  exact SineCircuit.applyGate_H_twice_state y ψ

def unprepInstrument (y : Wire) (I : Instrument) : Instrument :=
  I.map (fun b => ⟨b.history, b.kraus.comp (Quantum.run [.P .inverse 2 y, .H y])⟩)

theorem unprepInstrument_mass (y : Wire) (I : Instrument) (ψ : State) :
    (unprepInstrument y I).bornMass (Prep y ψ) = I.bornMass ψ := by
  simp only [unprepInstrument, Instrument.bornMass, List.map_map, Function.comp_def,
    LinearMap.comp_apply, unprep_prep]

theorem taggedAxisCat_ready_tail {n : Nat} {y : Wire} {read : ConstantBit n → Bool}
    (left right : List (CatWindow y read)) (start : Nat) (history : Fin start → Bool)
    (prior : List (Fin start)) (tagged : List Bool × InstrumentBranch)
    (ht : tagged ∈ taggedAxisCat left start history prior) (ψ : State)
    (hψ : Ready (left.map CatWindow.model ++ right.map CatWindow.model) ψ)
    (hψY : SupportedOn (fun s => s y = false) ψ) :
    ∃ φ : State, tagged.2.kraus (Prep y ψ) = Prep y φ ∧
      Ready (right.map CatWindow.model) φ ∧ SupportedOn (fun s => s y = false) φ := by
  induction left generalizing start tagged ψ with
  | nil =>
    simp only [taggedAxisCat, List.mem_singleton] at ht
    subst tagged
    exact ⟨ψ, rfl, hψ, hψY⟩
  | cons w ws ih =>
    obtain ⟨a, ha, ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨bits, hb, ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨b, hbt, rfl⟩ := List.mem_map.mp ht
    rw [prepare_run] at ha
    obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.mp ha
    obtain ⟨cs, hal, _⟩ := w.catCoherent start history
    obtain ⟨c, hc⟩ := forall2_mem_left hal ha₀
    have hH_nw : y ∉ circuitWires (w.catPhys.wires.reverse.map Gate.H) := by
      intro hm
      simp only [circuitWires, List.mem_flatMap, List.mem_map] at hm
      obtain ⟨g, ⟨v, hv, rfl⟩, hwg⟩ := hm
      simp only [gateWires, List.mem_singleton] at hwg
      have hv' : y ∈ w.catPhys.wires.reverse := hwg ▸ hv
      rw [List.mem_reverse, w.wires_eq] at hv'
      exact w.noY hv'
    have hstep_prep : compileFourierBranch y .inverse w.catPhys.wires (prior.map history) bits
        (a₀.kraus (Quantum.run (w.catPhys.wires.reverse.map Gate.H) (Prep y ψ))) =
        Prep y (c • w.model.step (prior.map history) bits ψ) := by
      rw [prep_circuit y _ hH_nw ψ, w.wires_eq, catBranch_on_supported hc _ hψ.1, map_smul]
      have hfb := compileFourierBranch_prep y .inverse w.model.physical.wires w.noY
        (prior.map history) bits _ (w.idealY _ hψ.1)
      rw [hfb.1, ← map_smul]
      rfl
    have hfbY : SupportedOn (fun s => s y = false) (c • w.model.step (prior.map history) bits ψ) :=
      support_smul c (compileFourierBranch_prep y .inverse w.model.physical.wires w.noY
        (prior.map history) bits _ (w.idealY _ hψ.1)).2
    have hready : Ready (ws.map CatWindow.model ++ right.map CatWindow.model)
        (c • w.model.step (prior.map history) bits ψ) :=
      Ready.smul _ _ (hψ.2 (prior.map history) bits) c
    obtain ⟨φ, hφ_eq, hφ_ready, hφ_Y⟩ := ih _ _ _ b hbt _ hready hfbY
    refine ⟨φ, ?_, hφ_ready, hφ_Y⟩
    change b.2.kraus (compileFourierBranch y .inverse w.catPhys.wires (prior.map history) bits
      (a₀.kraus (Quantum.run (w.catPhys.wires.reverse.map Gate.H) (Prep y ψ)))) = _
    rw [hstep_prep, hφ_eq]

/-! #### Two-axis catalyst bridge -/

def taggedTwoAxesCat {n : Nat} {y : Wire} {read : ConstantBit n → Bool}
    (left right : List (CatWindow y read)) (start : Nat) (history : Fin start → Bool) :
    List ((List Bool × List Bool) × InstrumentBranch) :=
  (taggedAxisCat left start history List.nil).flatMap (fun l =>
    (taggedAxisCat right (start + Single.axisCount (left.map CatWindow.catPhys))
      (Single.historyAfter _ history l.2.history) List.nil).map (fun r => ((l.1, r.1), l.2.seq r.2)))

def selectedTwoAxesCat {n : Nat} {y : Wire} {read : ConstantBit n → Bool}
    (left right : List (CatWindow y read)) (start : Nat) (history : Fin start → Bool)
    (terminal : List Bool → List Bool → Instrument) : Instrument :=
  (taggedTwoAxesCat left right start history).flatMap (fun a => (terminal a.1.1 a.1.2).map a.2.seq)

def physicalAxesCat {n : Nat} {y : Wire} {read : ConstantBit n → Bool}
    (left right : List (CatWindow y read)) (start : Nat) (history : Fin start → Bool) : Instrument :=
  (((axisCat y (left.map CatWindow.catPhys) start List.nil).append
    (axisCat y (right.map CatWindow.catPhys) (start + Single.axisCount (left.map CatWindow.catPhys))
      List.nil)).instantiate read history).run

theorem twoAxesCat_run_tagged {n : Nat} {y : Wire} {read : ConstantBit n → Bool}
    (left right : List (CatWindow y read)) (start : Nat) (history : Fin start → Bool) :
    physicalAxesCat left right start history =
      (taggedTwoAxesCat left right start history).map Prod.snd := by
  unfold physicalAxesCat
  rw [append_run_history, axisCat_run_tagged]
  simp only [taggedTwoAxesCat, List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def]
  apply List.flatMap_congr; intro a _
  rw [axisCat_run_tagged]
  simp only [List.map_map, Function.comp_def]

theorem selectedTwoAxesCat_constant {n : Nat} {y : Wire} {read : ConstantBit n → Bool}
    (left right : List (CatWindow y read)) (start : Nat) (history : Fin start → Bool)
    (J : Instrument) : selectedTwoAxesCat left right start history (fun _ _ => J) =
      (physicalAxesCat left right start history).seq J := by
  rw [twoAxesCat_run_tagged]
  simp only [selectedTwoAxesCat, Instrument.seq, List.flatMap_map]

theorem taggedTwoAxesCat_readWords {n : Nat} {y : Wire} {read : ConstantBit n → Bool}
    (left right : List (CatWindow y read)) (start : Nat) (history : Fin start → Bool)
    (tagged : (List Bool × List Bool) × InstrumentBranch)
    (ht : tagged ∈ taggedTwoAxesCat left right start history) (after : List Bool) :
    ShorECDLP.Challenge.readWord (List.ofFn history ++ tagged.2.history ++ after)
      (Single.axisPositions (left.map CatWindow.catPhys) start) =
        some (fourierWordLSB tagged.1.1.reverse) ∧
    ShorECDLP.Challenge.readWord (List.ofFn history ++ tagged.2.history ++ after)
      (Single.axisPositions (right.map CatWindow.catPhys)
        (start + Single.axisCount (left.map CatWindow.catPhys))) =
        some (fourierWordLSB tagged.1.2.reverse) := by
  obtain ⟨l, hl, ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ht
  have hleft := taggedAxisCat_readWord left start history l hl (r.2.history ++ after)
  have hright := taggedAxisCat_readWord right _ _ r hr after
  have hlen := taggedAxisCat_history_length left start history List.nil l hl
  rw [historyAfter_list history l.2.history (by omega)] at hright
  exact ⟨by simpa only [InstrumentBranch.seq, List.append_assoc] using hleft,
    by simpa only [InstrumentBranch.seq, List.append_assoc] using hright⟩

theorem selectedTwoAxesCat_fixed_filter {n : Nat} {y : Wire} {read : ConstantBit n → Bool}
    (left right : List (CatWindow y read)) (J : Instrument) (accept : Nat → Nat → Bool) :
    selectedTwoAxesCat left right 0 Fin.elim0 (fun lhs rhs =>
      if accept (fourierWordLSB lhs.reverse) (fourierWordLSB rhs.reverse) then J else List.nil) =
      ((physicalAxesCat left right 0 Fin.elim0).seq J).filter (fun b =>
        pairAccept (Single.axisPositions (left.map CatWindow.catPhys) 0)
          (Single.axisPositions (right.map CatWindow.catPhys)
            (Single.axisCount (left.map CatWindow.catPhys))) accept b.history) := by
  rw [← selectedTwoAxesCat_constant left right 0 Fin.elim0 J]
  rw [selectedTwoAxesCat, selectedTwoAxesCat, List.filter_flatMap]
  apply List.flatMap_congr; intro a ha
  have hp (b : InstrumentBranch) :
      pairAccept (Single.axisPositions (left.map CatWindow.catPhys) 0)
        (Single.axisPositions (right.map CatWindow.catPhys) (Single.axisCount (left.map CatWindow.catPhys)))
        accept (a.2.seq b).history =
          accept (fourierWordLSB a.1.1.reverse) (fourierWordLSB a.1.2.reverse) := by
    have h := taggedTwoAxesCat_readWords left right 0 Fin.elim0 a ha b.history
    simp only [List.ofFn_zero, List.nil_append, Nat.zero_add] at h
    simp only [pairAccept, InstrumentBranch.seq, h.1, h.2, Option.bind_some,
      Option.map_some, Option.getD_some]
  rw [List.filter_map]
  simp only [Function.comp_def, hp]
  split <;> simp_all

theorem selectedTwoAxesCat_expand {n : Nat} {y : Wire} {read : ConstantBit n → Bool}
    (left right : List (CatWindow y read)) (start : Nat) (history : Fin start → Bool)
    (terminal : List Bool → List Bool → Instrument) :
    selectedTwoAxesCat left right start history terminal =
      (taggedAxisCat left start history List.nil).flatMap (fun l =>
        (selectedAxisCat right (start + Single.axisCount (left.map CatWindow.catPhys))
          (Single.historyAfter _ history l.2.history) List.nil (terminal l.1)).map l.2.seq) := by
  simp only [selectedTwoAxesCat, taggedTwoAxesCat, selectedAxisCat, List.flatMap_assoc,
    List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def]
  apply List.flatMap_congr; intro l _
  apply List.flatMap_congr; intro r _
  apply List.map_congr_left; intro b _
  rcases l with ⟨lt, lh, lk⟩; rcases r with ⟨rt, rh, rk⟩; rcases b with ⟨bh, bk⟩
  simp [InstrumentBranch.seq, LinearMap.comp_assoc, List.append_assoc]

theorem selectedTwoAxesCat_mass {n : Nat} {y : Wire} {read : ConstantBit n → Bool}
    (left right : List (CatWindow y read)) (start : Nat) (history : Fin start → Bool)
    (physTerm idealTerm : List Bool → List Bool → Instrument)
    (hterm : ∀ lhs rhs φ, SupportedOn (fun s => s y = false) φ →
      (physTerm lhs rhs).bornMass (Prep y φ) = (idealTerm lhs rhs).bornMass φ)
    (ψ : State) (hψ : Ready (left.map CatWindow.model ++ right.map CatWindow.model) ψ)
    (hψY : SupportedOn (fun s => s y = false) ψ) :
    (selectedTwoAxesCat left right start history physTerm).bornMass (Prep y ψ) =
      (idealTwoAxes (left.map CatWindow.model) (right.map CatWindow.model) idealTerm).bornMass ψ := by
  rw [selectedTwoAxesCat_expand, flat_mass]
  simp only [prefixed_mass]
  let liftL : List Bool → Instrument := fun lhs =>
    unprepInstrument y (idealAxis (right.map CatWindow.model) List.nil (idealTerm lhs))
  have hL_eq : ((taggedAxisCat left start history List.nil).map (fun l =>
      (selectedAxisCat right (start + Single.axisCount (left.map CatWindow.catPhys))
        (Single.historyAfter _ history l.2.history) List.nil (physTerm l.1)).bornMass (l.2.kraus (Prep y ψ)))).sum =
      (selectedAxisCat left start history List.nil liftL).bornMass (Prep y ψ) := by
    rw [show (selectedAxisCat left start history List.nil liftL).bornMass (Prep y ψ) =
        ((taggedAxisCat left start history List.nil).map (fun l =>
          (liftL l.1).bornMass (l.2.kraus (Prep y ψ)))).sum by
      simp only [selectedAxisCat, flat_mass, prefixed_mass]]
    apply congrArg List.sum
    apply List.map_congr_left
    intro l hl
    obtain ⟨φ, hφ_eq, hφ_ready, hφ_Y⟩ := taggedAxisCat_ready_tail left right start history List.nil l hl ψ hψ hψY
    rw [hφ_eq, unprepInstrument_mass]
    simpa only [List.map_nil] using
      selectedAxisCat_mass right _ _ List.nil (physTerm l.1) (idealTerm l.1) (hterm l.1) φ hφ_ready hφ_Y
  rw [hL_eq]
  have hres := selectedAxisCat_mass left start history List.nil liftL
    (fun lhs => idealAxis (right.map CatWindow.model) List.nil (idealTerm lhs))
    (fun tag φ _ => unprepInstrument_mass y _ φ)
    ψ (Ready.append_left _ _ ψ hψ) hψY
  simpa only [List.map_nil, idealTwoAxes] using hres

/-! #### Static properties of `axisCat`, `trim 18`, `cost18`, and `tCount` -/

theorem cost18_zero_of_removed18 {n s e : Nat} (p : Straight n s e) (h : removed 18 p = 0) :
    cost18 p = 0 := by
  induction p with
  | done => rfl
  | measure w p ih => exact ih h
  | recordGate i v g p ih =>
    simp only [removed] at h
    have hg : largePhase 18 g = false := by cases h1 : largePhase 18 g <;> simp [h1] at h ⊢
    have hp : removed 18 p = 0 := by simp [hg] at h; exact h
    simp only [cost18, charge18_false g hg, ih hp, add_zero]
  | gate g p ih =>
    cases g with
    | literal g =>
      simp only [removed] at h
      have hg : largePhase 18 g = false := by cases h1 : largePhase 18 g <;> simp [h1] at h ⊢
      have hp : removed 18 p = 0 := by simp [hg] at h; exact h
      simp only [cost18, charge18_false g hg, ih hp, add_zero]
    | whenBit r v g =>
      simp only [removed] at h
      have hg : largePhase 18 g = false := by cases h1 : largePhase 18 g <;> simp [h1] at h ⊢
      have hp : removed 18 p = 0 := by simp [hg] at h; exact h
      simp only [cost18, charge18_false g hg, ih hp, add_zero]

theorem cost18_literals {n s e : Nat} (gs : Circuit) (p : Straight n s e)
    (h : ∀ g ∈ gs, largePhase 18 g = false) :
    cost18 (AndGadget.literals gs p) = cost18 p := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    change charge18 g + cost18 (AndGadget.literals gs p) = cost18 p
    rw [charge18_false g (h g List.mem_cons_self),
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx)), zero_add]

theorem cost18_whenLiterals {n s e : Nat} (r : ConstantBit n) (v : Bool) (gs : Circuit)
    (p : Straight n s e) (h : ∀ g ∈ gs, largePhase 18 g = false) :
    cost18 (ConditionalCatalyst.whenLiterals r v gs p) = cost18 p := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    change charge18 g + cost18 (ConditionalCatalyst.whenLiterals r v gs p) = cost18 p
    rw [charge18_false g (h g List.mem_cons_self),
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx)), zero_add]

theorem cost18_recordLiterals {n s e : Nat} (i : Fin s) (v : Bool) (gs : Circuit)
    (p : Straight n s e) (h : ∀ g ∈ gs, largePhase 18 g = false) :
    cost18 (ConditionalCatalyst.recordLiterals i v gs p) = cost18 p := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    change charge18 g + cost18 (ConditionalCatalyst.recordLiterals i v gs p) = cost18 p
    rw [charge18_false g (h g List.mem_cons_self),
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx)), zero_add]

private theorem replacement_largePhase18_false (y : Wire) (g : Gate) (hg : largePhase 18 g = false) :
    ∀ x ∈ ConditionalCatalyst.replacement y g, largePhase 18 x = false := by
  intro x hx
  unfold ConditionalCatalyst.replacement at hx
  split at hx
  · simp [Catalyst.kick, controlledZ, largePhase] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> rfl
  · simp [ConditionalCatalyst.inverseKick, Catalyst.kick, controlledZ, Circuit.adjoint, Gate.adjoint, largePhase] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> rfl
  · simp only [List.mem_singleton] at hx; subst hx; exact hg

private theorem replacement_of_largePhase18_true (y : Wire) (g : Gate) (hg : largePhase 18 g = true) :
    ConditionalCatalyst.replacement y g = [g] := by
  cases g with
  | P d k t =>
    simp only [largePhase, decide_eq_true_eq] at hg
    have hk : k ≠ 2 := by omega
    unfold ConditionalCatalyst.replacement
    split <;> simp_all
  | _ => simp [largePhase] at hg

theorem cost18_compile {n s e : Nat} (y : Wire) (p : Straight n s e) :
    cost18 (ConditionalCatalyst.compile y p) = cost18 p := by
  induction p with
  | done => rfl
  | measure w p ih => exact ih
  | recordGate i v g p ih =>
    by_cases hg : largePhase 18 g = true
    · simp only [ConditionalCatalyst.compile, replacement_of_largePhase18_true y g hg,
        ConditionalCatalyst.recordLiterals, cost18, ih]
    · have hgf : largePhase 18 g = false := Bool.eq_false_iff.mpr hg
      simp only [ConditionalCatalyst.compile, cost18, charge18_false g hgf, zero_add]
      rw [cost18_recordLiterals i v _ _ (replacement_largePhase18_false y g hgf), ih]
  | gate g p ih =>
    cases g with
    | literal g =>
      by_cases hg : largePhase 18 g = true
      · simp only [ConditionalCatalyst.compile, replacement_of_largePhase18_true y g hg,
          AndGadget.literals, List.foldr_cons, List.foldr_nil, cost18, ih]
      · have hgf : largePhase 18 g = false := Bool.eq_false_iff.mpr hg
        simp only [ConditionalCatalyst.compile, cost18, charge18_false g hgf, zero_add]
        rw [cost18_literals _ _ (replacement_largePhase18_false y g hgf), ih]
    | whenBit r v g =>
      by_cases hg : largePhase 18 g = true
      · simp only [ConditionalCatalyst.compile, replacement_of_largePhase18_true y g hg,
          ConditionalCatalyst.whenLiterals, cost18, ih]
      · have hgf : largePhase 18 g = false := Bool.eq_false_iff.mpr hg
        simp only [ConditionalCatalyst.compile, cost18, charge18_false g hgf, zero_add]
        rw [cost18_whenLiterals r v _ _ (replacement_largePhase18_false y g hgf), ih]

theorem trim18_append {n s m e : Nat} (p : Straight n s m) (q : Straight n m e) :
    trim 18 (p.append q) = (trim 18 p).append (trim 18 q) := by
  induction p with
  | done => rfl
  | gate g p ih =>
    cases g with
    | literal g => simp only [Straight.append, trim]; split_ifs <;> simp [Straight.append, ih]
    | whenBit r v g => simp only [Straight.append, trim]; split_ifs <;> simp [Straight.append, ih]
  | recordGate i v g p ih => simp only [Straight.append, trim]; split_ifs <;> simp [Straight.append, ih]
  | measure w p ih => simp only [Straight.append, trim, ih]

theorem trim18_castFinish {n s e f : Nat} (h : e = f) (p : Straight n s e) :
    trim 18 (castFinish h p) = castFinish h (trim 18 p) := by
  subst f; rfl

theorem trim18_prepareOuterBank {n s e : Nat} (ws : List Wire) (p : Straight n s e) :
    trim 18 (prepareOuterBank ws p) = prepareOuterBank ws (trim 18 p) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change trim 18 (.gate (.literal (.H w)) (prepareOuterBank ws p)) =
      .gate (.literal (.H w)) (prepareOuterBank ws (trim 18 p))
    simp [trim, largePhase, ih]

theorem trim18_literals_false {n s e : Nat} (gs : Circuit) (p : Straight n s e)
    (h : ∀ g ∈ gs, largePhase 18 g = false) :
    trim 18 (AndGadget.literals gs p) = AndGadget.literals gs (trim 18 p) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    change trim 18 (.gate (.literal g) (AndGadget.literals gs p)) =
      .gate (.literal g) (AndGadget.literals gs (trim 18 p))
    simp only [trim, h g List.mem_cons_self, Bool.false_eq_true, ↓reduceIte,
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem trim18_whenLiterals_false {n s e : Nat} (r : ConstantBit n) (v : Bool) (gs : Circuit)
    (p : Straight n s e) (h : ∀ g ∈ gs, largePhase 18 g = false) :
    trim 18 (ConditionalCatalyst.whenLiterals r v gs p) =
      ConditionalCatalyst.whenLiterals r v gs (trim 18 p) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [ConditionalCatalyst.whenLiterals, trim, h g List.mem_cons_self, Bool.false_eq_true, ↓reduceIte,
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem trim18_recordLiterals_false {n s e : Nat} (i : Fin s) (v : Bool) (gs : Circuit)
    (p : Straight n s e) (h : ∀ g ∈ gs, largePhase 18 g = false) :
    trim 18 (ConditionalCatalyst.recordLiterals i v gs p) =
      ConditionalCatalyst.recordLiterals i v gs (trim 18 p) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [ConditionalCatalyst.recordLiterals, trim, h g List.mem_cons_self, Bool.false_eq_true, ↓reduceIte,
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem trim18_compile {n s e : Nat} (y : Wire) (p : Straight n s e) :
    trim 18 (ConditionalCatalyst.compile y p) = ConditionalCatalyst.compile y (trim 18 p) := by
  induction p with
  | done => rfl
  | measure w p ih => simp only [ConditionalCatalyst.compile, trim, ih]
  | recordGate i v g p ih =>
    by_cases hg : largePhase 18 g = true
    · simp only [ConditionalCatalyst.compile, replacement_of_largePhase18_true y g hg,
        ConditionalCatalyst.recordLiterals, trim, hg, ↓reduceIte, ih]
    · have hgf : largePhase 18 g = false := Bool.eq_false_iff.mpr hg
      simp only [ConditionalCatalyst.compile, trim, hgf, Bool.false_eq_true, ↓reduceIte]
      rw [trim18_recordLiterals_false i v _ _ (replacement_largePhase18_false y g hgf), ih]
  | gate g p ih =>
    cases g with
    | literal g =>
      by_cases hg : largePhase 18 g = true
      · simp only [ConditionalCatalyst.compile, replacement_of_largePhase18_true y g hg,
          AndGadget.literals, List.foldr_cons, List.foldr_nil, trim, hg, ↓reduceIte, ih]
      · have hgf : largePhase 18 g = false := Bool.eq_false_iff.mpr hg
        simp only [ConditionalCatalyst.compile, trim, hgf, Bool.false_eq_true, ↓reduceIte]
        rw [trim18_literals_false _ _ (replacement_largePhase18_false y g hgf), ih]
    | whenBit r v g =>
      by_cases hg : largePhase 18 g = true
      · simp only [ConditionalCatalyst.compile, replacement_of_largePhase18_true y g hg,
          ConditionalCatalyst.whenLiterals, trim, hg, ↓reduceIte, ih]
      · have hgf : largePhase 18 g = false := Bool.eq_false_iff.mpr hg
        simp only [ConditionalCatalyst.compile, trim, hgf, Bool.false_eq_true, ↓reduceIte]
        rw [trim18_whenLiterals_false r v _ _ (replacement_largePhase18_false y g hgf), ih]

theorem weight7_trim18 {n s e : Nat} (p : Straight n s e) :
    ConditionalCatalyst.weight7 (trim 18 p) + removed 18 p = ConditionalCatalyst.weight7 p := by
  induction p with
  | done => rfl
  | measure w p ih => exact ih
  | recordGate i v g p ih =>
    by_cases hg : largePhase 18 g = true
    · have hw := (Trim18.dropped_weight18 g hg).1
      simp only [trim, hg, if_true, removed, Bool.toNat_true, ConditionalCatalyst.weight7, hw]; omega
    · have hgf : largePhase 18 g = false := Bool.eq_false_iff.mpr hg
      simp only [trim, hgf, Bool.false_eq_true, if_false, removed, Bool.toNat_false, zero_add,
        ConditionalCatalyst.weight7]; omega
  | gate g p ih =>
    cases g with
    | literal g =>
      by_cases hg : largePhase 18 g = true
      · have hw := (Trim18.dropped_weight18 g hg).1
        simp only [trim, hg, if_true, removed, Bool.toNat_true, ConditionalCatalyst.weight7, hw]; omega
      · have hgf : largePhase 18 g = false := Bool.eq_false_iff.mpr hg
        simp only [trim, hgf, Bool.false_eq_true, if_false, removed, Bool.toNat_false, zero_add,
          ConditionalCatalyst.weight7]; omega
    | whenBit r v g =>
      by_cases hg : largePhase 18 g = true
      · have hw := (Trim18.dropped_weight18 g hg).1
        simp only [trim, hg, if_true, removed, Bool.toNat_true, ConditionalCatalyst.weight7, hw]; omega
      · have hgf : largePhase 18 g = false := Bool.eq_false_iff.mpr hg
        simp only [trim, hgf, Bool.false_eq_true, if_false, removed, Bool.toNat_false, zero_add,
          ConditionalCatalyst.weight7]; omega

theorem weight7_feedbackProgram {n s e : Nat} (dir : PhaseDir) (w : Wire)
    (indices : List (Fin s)) (k : Nat) (next : Straight n s e) :
    ConditionalCatalyst.weight7 (feedbackProgram dir w indices k next) =
      ConditionalCatalyst.weight4 (feedbackProgram dir w indices k next) +
        (ConditionalCatalyst.weight7 next - ConditionalCatalyst.weight4 next) := by
  induction indices generalizing k with
  | nil =>
    have hle : ConditionalCatalyst.weight4 next ≤ ConditionalCatalyst.weight7 next := by
      clear dir w k
      induction next with
      | done => rfl
      | measure _ _ ih => exact ih
      | recordGate _ _ _ _ ih => simp only [ConditionalCatalyst.weight4, ConditionalCatalyst.weight7]; omega
      | gate g _ ih =>
        cases g with
        | literal g => cases g <;> simp only [ConditionalCatalyst.weight4, ConditionalCatalyst.weight7,
            ConditionalCatalyst.weightedLiteral, ConditionalCatalyst.weightedGate,
            ConditionalCatalyst.phaseTwoGate, tCost] <;> omega
        | whenBit => simp only [ConditionalCatalyst.weight4, ConditionalCatalyst.weight7]; omega
    simp only [feedbackProgram]; omega
  | cons i is ih =>
    simp only [feedbackProgram, ConditionalCatalyst.weight7, ConditionalCatalyst.weight4, ih]; omega

theorem weight7_fourierProgram (n : Nat) (dir : PhaseDir) (ws : List Wire)
    (start : Nat) (prior : List (Fin start)) :
    ConditionalCatalyst.weight7 (fourierProgram n dir ws start prior) =
      fourierWeight ws.length prior.length := by
  have heq : ConditionalCatalyst.weight7 (fourierProgram n dir ws start prior) =
      ConditionalCatalyst.weight4 (fourierProgram n dir ws start prior) := by
    induction ws generalizing start with
    | nil => rfl
    | cons w ws ih =>
      simp only [fourierProgram]
      have hc7 : ∀ {a b} (h : a = b) (p : Straight n start a),
          ConditionalCatalyst.weight7 (castFinish h p) = ConditionalCatalyst.weight7 p := by
        intro a b h p; subst b; rfl
      rw [hc7, weight4_cast, weight7_feedbackProgram]
      simp only [ConditionalCatalyst.weight7, ConditionalCatalyst.weight4, ih, Nat.sub_self, Nat.add_zero]
  rw [heq, weight4_fourier]

theorem tCount_trim18_compile_fourier (y : Wire) (n : Nat) (dir : PhaseDir) (ws : List Wire)
    (start : Nat) (prior : List (Fin start)) (read : ConstantBit n → Bool) (h : Fin start → Bool) :
    ((trim 18 (ConditionalCatalyst.compile y (fourierProgram n dir ws start prior))).instantiate read h).tCount ≤
      fourierWeight ws.length prior.length - droppedSlots18 ws.length prior.length := by
  rw [trim18_compile]
  have ht := ConditionalCatalyst.compile_t y (trim 18 (fourierProgram n dir ws start prior)) read h
  have hw := weight7_trim18 (fourierProgram n dir ws start prior)
  rw [weight7_fourierProgram, removed_fourier18] at hw
  omega

theorem append_tCount_le {n s m e : Nat} (p : Straight n s m) (q : Straight n m e)
    (read : ConstantBit n → Bool) (h : Fin s → Bool) (B : Nat)
    (hq : ∀ h' : Fin m → Bool, (q.instantiate read h').tCount ≤ B) :
    ((p.append q).instantiate read h).tCount ≤ (p.instantiate read h).tCount + B := by
  induction p with
  | done => simpa [Straight.append, Straight.instantiate, AdaptiveCircuit.tCount] using hq h
  | gate g p ih =>
    cases g with
    | literal g =>
      simp only [Straight.append, Straight.instantiate, TemplateGate.instantiate, AdaptiveCircuit.tCount]
      have := ih q h hq; omega
    | whenBit r v g =>
      simp only [Straight.append, Straight.instantiate, TemplateGate.instantiate, AdaptiveCircuit.tCount]
      split_ifs <;> (have := ih q h hq; omega)
  | recordGate i v g p ih =>
    simp only [Straight.append, Straight.instantiate, AdaptiveCircuit.tCount]
    split_ifs <;> (have := ih q h hq; omega)
  | measure w p ih =>
    simp only [Straight.append, Straight.instantiate, AdaptiveCircuit.tCount]
    have h0 := ih q (Fin.lastCases false h) hq
    have h1 := ih q (Fin.lastCases true h) hq
    exact max_le (h0.trans (Nat.add_le_add_right (le_max_left _ _) B))
      (h1.trans (Nat.add_le_add_right (le_max_right _ _) B))

theorem prepareOuterBank_tCount {n s e : Nat} (ws : List Wire) (p : Straight n s e)
    (read : ConstantBit n → Bool) (h : Fin s → Bool) :
    ((prepareOuterBank ws p).instantiate read h).tCount = (p.instantiate read h).tCount := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change ((Straight.gate (.literal (.H w)) (prepareOuterBank ws p)).instantiate read h).tCount = _
    simp only [Straight.instantiate, TemplateGate.instantiate, AdaptiveCircuit.tCount,
      ShorECDLP.tCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, tCost, Nat.zero_add, ih]

def metadataTrimmedWeight : List (Nat × Nat) → Nat → Nat
  | [], _ => 0
  | (cost, width) :: rest, prior =>
      cost + (fourierWeight width prior - droppedSlots18 width prior) +
        metadataTrimmedWeight rest (prior + width)

theorem axisCat_tCount_trim18 {n : Nat} (y : Wire) (ws : List (Single.Window n))
    (spec : List (Nat × Nat))
    (hrel : List.Forall₂ (fun w k => w.wires.length = k.2 ∧
        ∀ start read h, ((w.program start).instantiate read h).tCount ≤ k.1) ws spec)
    (start : Nat) (prior : List (Fin start)) (read : ConstantBit n → Bool) (h : Fin start → Bool) :
    ((trim 18 (axisCat y ws start prior)).instantiate read h).tCount ≤
      metadataTrimmedWeight spec prior.length := by
  induction ws generalizing spec start with
  | nil =>
    cases hrel
    simp [axisCat, trim, Straight.instantiate, AdaptiveCircuit.tCount, metadataTrimmedWeight]
  | cons w ws ih =>
    cases hrel with
    | cons hhd htl =>
      rename_i k rest
      simp only [axisCat, trim18_castFinish, castFinish_instantiate, trim18_append,
        trim18_prepareOuterBank, metadataTrimmedWeight]
      have htail : ∀ h' : Fin (start + w.count + w.wires.length) → Bool,
          ((trim 18 (axisCat y ws (start + w.count + w.wires.length)
              (nextPrior w.count w.wires.length prior))).instantiate read h').tCount ≤
            metadataTrimmedWeight rest (prior.length + k.2) := by
        intro h'
        have := ih rest htl (start + w.count + w.wires.length) (nextPrior w.count w.wires.length prior) h'
        rw [nextPrior_length] at this
        exact this.trans (le_of_eq (congrArg (fun m => metadataTrimmedWeight rest (prior.length + m)) hhd.1))
      have hmid : ∀ h' : Fin (start + w.count) → Bool,
          (((castFinish (by simp) (trim 18 (ConditionalCatalyst.compile y
              (fourierProgram n .inverse w.wires (start + w.count) (bankPrior w.count prior))))).append
            (trim 18 (axisCat y ws (start + w.count + w.wires.length)
              (nextPrior w.count w.wires.length prior)))).instantiate read h').tCount ≤
            (fourierWeight k.2 prior.length - droppedSlots18 k.2 prior.length) +
              metadataTrimmedWeight rest (prior.length + k.2) := by
        intro h'
        have h1 := append_tCount_le
          (castFinish (by simp) (trim 18 (ConditionalCatalyst.compile y
            (fourierProgram n .inverse w.wires (start + w.count) (bankPrior w.count prior)))))
          _ read h' _ htail
        rw [castFinish_instantiate] at h1
        have hf := tCount_trim18_compile_fourier y n .inverse w.wires (start + w.count) (bankPrior w.count prior) read h'
        rw [bankPrior_length] at hf
        have hf' : ((trim 18 (ConditionalCatalyst.compile y
            (fourierProgram n .inverse w.wires (start + w.count) (bankPrior w.count prior)))).instantiate read h').tCount ≤
            fourierWeight k.2 prior.length - droppedSlots18 k.2 prior.length :=
          hf.trans (le_of_eq (congrArg (fun m => fourierWeight m prior.length - droppedSlots18 m prior.length) hhd.1))
        omega
      have h1 := append_tCount_le (prepareOuterBank w.wires.reverse (trim 18 (w.program start))) _ read h _ hmid
      rw [prepareOuterBank_tCount] at h1
      have hw := (trim18_t (w.program start) read h).trans (hhd.2 start read h)
      omega

private theorem fourierProgram_within (n : Nat) (dir : PhaseDir) (ws : List Wire)
    (start : Nat) (prior : List (Fin start)) :
    Within ws (fourierProgram n dir ws start prior) :=
  within_of_instantiate _ ws (fun read h =>
    fourierProgram_support n dir ws start prior read h ws (List.Subset.refl ws))

private theorem within_mono {n s e : Nat} {ws₁ ws₂ : List Wire} {p : Straight n s e}
    (hsub : ws₁ ⊆ ws₂) (hp : Within ws₁ p) : Within ws₂ p :=
  within_of_instantiate p ws₂ (fun read h => (hp.instantiate read h).trans hsub)

theorem axisCat_wellFormed {n : Nat} (y : Wire) (ws : List (Single.Window n))
    (hnoY : ∀ w ∈ ws, y ∉ w.wires)
    (hwf : ∀ w ∈ ws, ∀ start, (w.program start).WellFormed)
    (start : Nat) (prior : List (Fin start)) :
    (axisCat y ws start prior).WellFormed := by
  induction ws generalizing start with
  | nil => trivial
  | cons w ws ih =>
    simp only [axisCat, castFinish_wellFormed]
    apply straight_append_wellFormed
    · exact prepareOuterBank_wellFormed _ _ (hwf w List.mem_cons_self start)
    · apply straight_append_wellFormed
      · rw [castFinish_wellFormed]
        apply ConditionalCatalyst.compile_wellFormed y _ _ (fourierProgram_wellFormed n .inverse w.wires _ _)
        apply LocalFour.fresh_of_not_mem_straightWires
        intro hm
        have hsub : ChallengeMigration.straightWires
            (fourierProgram n .inverse w.wires (start + w.count) (bankPrior w.count prior)) ⊆ w.wires :=
          LocalFour.straightWires_of_within _ _ (fourierProgram_within n .inverse w.wires _ _)
        exact hnoY w List.mem_cons_self (hsub hm)
      · exact ih (fun v hv => hnoY v (List.mem_cons_of_mem _ hv))
          (fun v hv => hwf v (List.mem_cons_of_mem _ hv)) _ _

theorem axisCat_support {n : Nat} (y : Wire) (ws : List (Single.Window n)) (sup : List Wire)
    (hy : y ∈ sup)
    (hbank : ∀ w ∈ ws, w.wires ⊆ sup)
    (hprog : ∀ w ∈ ws, ∀ start read h, ((w.program start).instantiate read h).wires ⊆ sup)
    (start : Nat) (prior : List (Fin start)) (read : ConstantBit n → Bool) (h : Fin start → Bool) :
    ((axisCat y ws start prior).instantiate read h).wires ⊆ sup := by
  induction ws generalizing start with
  | nil => intro u hu; simp [axisCat, Straight.instantiate, AdaptiveCircuit.wires] at hu
  | cons w ws ih =>
    simp only [axisCat, castFinish_instantiate]
    apply outer_append_support _ _ read h sup
    · apply prepareOuterBank_support
      · exact fun u hu => hbank w List.mem_cons_self (List.mem_reverse.mp hu)
      · exact hprog w List.mem_cons_self start read h
    · intro h₁
      apply outer_append_support _ _ read h₁ sup
      · rw [castFinish_instantiate]
        have hw : Within sup (fourierProgram n .inverse w.wires (start + w.count) (bankPrior w.count prior)) :=
          within_mono (hbank w List.mem_cons_self) (fourierProgram_within n .inverse w.wires _ _)
        have hc := ConditionalCatalyst.compile_within y _ sup hw
        have hsup := hc.instantiate read h₁
        intro u hu
        have hm := hsup hu
        simp only [List.mem_cons] at hm
        rcases hm with rfl | hm
        · exact hy
        · exact hm
      · intro h₂
        exact ih (fun v hv => hbank v (List.mem_cons_of_mem _ hv))
          (fun v hv => hprog v (List.mem_cons_of_mem _ hv)) _ _ h₂

theorem axisCat_slots {n : Nat} (y : Wire) (ws : List (Single.Window n)) (B : Nat)
    (hb : ∀ w ∈ ws, ∀ start, (w.program start).gateSlots ≤ B)
    (start : Nat) (prior : List (Fin start)) :
    (axisCat y ws start prior).gateSlots ≤
      4 * metadataSlots B (ws.map (fun w => (w.count, w.wires.length))) prior.length := by
  induction ws generalizing start with
  | nil => simp [axisCat, Straight.gateSlots, metadataSlots]
  | cons w ws ih =>
    simp only [axisCat, castFinish_gateSlots, Straight.gateSlots_append, prepareOuterBank_slots,
      List.length_reverse, List.map_cons, metadataSlots]
    have hprog := hb w List.mem_cons_self start
    have hf1 := ConditionalCatalyst.compile_slots y
      (fourierProgram n .inverse w.wires (start + w.count) (bankPrior w.count prior))
    have hf2 := ConditionalCatalyst.phaseTwos_le_slots
      (fourierProgram n .inverse w.wires (start + w.count) (bankPrior w.count prior))
    have hf3 := fourierProgram_slots n .inverse w.wires (start + w.count) (bankPrior w.count prior)
    rw [bankPrior_length] at hf3
    have htail := ih (fun v hv => hb v (List.mem_cons_of_mem _ hv))
      (start + w.count + w.wires.length) (nextPrior w.count w.wires.length prior)
    rw [nextPrior_length] at htail
    omega

theorem axisCat_cost18_exact {n : Nat} (y : Wire) (ws : List (Single.Window n))
    (hz : ∀ w ∈ ws, ∀ start, cost18 (w.program start) = 0)
    (start : Nat) (prior : List (Fin start)) :
    cost18 (axisCat y ws start prior) =
      account18 ((ws.map (fun w => w.wires.length)).sum) prior.length := by
  induction ws generalizing start with
  | nil => simp [axisCat, cost18, account18]
  | cons w ws ih =>
    simp only [axisCat, cost18_cast, cost18_append, cost18_prepare, cost18_compile]
    rw [hz w List.mem_cons_self start, zero_add]
    have hf := cost18_fourier_exact n .inverse w.wires (start + w.count) (bankPrior w.count prior)
    have hi := ih (fun v hv s => hz v (List.mem_cons_of_mem w hv) s)
      (start + w.count + w.wires.length) (nextPrior w.count w.wires.length prior)
    rw [hf, hi]
    simp only [bankPrior, nextPrior, List.length_append, List.length_reverse, List.length_ofFn,
      List.length_map, List.map_cons, List.sum_cons, account18_append]
    rw [Nat.add_comm w.wires.length prior.length]

end
end ShorECDLP.Entrant.CatAxis

/-! ### Part 3: Schedule26 geometry, coefficients, specialization, and physical program -/

namespace ShorECDLP.Entrant.Schedule26
open Quantum Challenge Secp256k1 AndGadget WEXCredit ConditionalCatalyst ApproximatePhase34
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open Single Single.Distribution Width16Schedule.Specialization
open SineCircuit SineBounds Trim18 Schedule26Bridge
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
attribute [local irreducible] List.ofFn fourierOutcomes Single.fixedEntry

local instance bodyInst26 : Single.WindowBody := PathShare.bodyCF
local instance resourceInst26 : Single.ProducerResources bodyInst26 :=
  Single.ProducerResources.ofBody PathShare.bodyCF
    (by change resetWires.Nodup; exact resetWires_nodup)
    (by change (0 : Wire) ∈ resetWires; decide)
    (by change (1 : Wire) ∈ resetWires; decide)

inductive Digit26 where
  | left17 (index : Fin 14)
  | right17 (index : Fin 12)

def Digit26.exponent : Digit26 → Nat
  | .left17 j => 221 - 17 * j.val
  | .right17 j => 187 - 17 * j.val

def Digit26.base (Q : Point) : Digit26 → Point
  | .left17 _ => G
  | .right17 _ => Q

def leftDigits26 : List Digit26 := List.ofFn (fun j : Fin 14 => .left17 j)
def rightDigits26 : List Digit26 := List.ofFn (fun j : Fin 12 => .right17 j)

def initialCoefficients26 (a : Nat) : PointCoeff :=
  coefficients (oddScalar 238 a) 0

def signedCoefficients26 (w : Digit26) (a : Nat) : PointCoeff :=
  match w with
  | .left17 _ => coefficients (oddScalar w.exponent a) 0
  | .right17 _ => coefficients 0 (oddScalar w.exponent a)

/-- `2,228,224 = 524,288 + 14 * 65,536 + 12 * 65,536` raw rows.
The first `1,441,792` rows (`First20Signed` + all `14` left body windows) have `b = 0` and freeze during specialization. -/
def coefficientAt26 (i : Fin 2228224) : PointCoeff :=
  if i.val < 524288 then initialCoefficients26 i.val
  else if i.val < 1441792 then
    coefficients (oddScalar (221 - 17 * ((i.val - 524288) / 65536)) ((i.val - 524288) % 65536)) 0
  else
    coefficients 0 (oddScalar (187 - 17 * ((i.val - 1441792) / 65536)) ((i.val - 1441792) % 65536))

def firstRow26 (a : Fin 524288) : Fin 2228224 := ⟨a.val, by omega⟩

def row26 : Digit26 → Fin 65536 → Fin 2228224
  | .left17 j, a => ⟨524288 + j.val * 65536 + a.val, by omega⟩
  | .right17 j, a => ⟨1441792 + j.val * 65536 + a.val, by omega⟩

theorem coefficientAt26_first (a : Fin 524288) :
    coefficientAt26 (firstRow26 a) = initialCoefficients26 a.val := by
  simp [coefficientAt26, firstRow26, a.isLt]

theorem coefficientAt26_row (w : Digit26) (a : Fin 65536) :
    coefficientAt26 (row26 w a) = signedCoefficients26 w a.val := by
  cases w with
  | left17 j =>
    have h0 : ¬ (row26 (.left17 j) a).val < 524288 := by simp only [row26]; omega
    have h1 : (row26 (.left17 j) a).val < 1441792 := by simp only [row26]; omega
    have hj : ((row26 (.left17 j) a).val - 524288) / 65536 = j.val := by simp only [row26]; omega
    have ha : ((row26 (.left17 j) a).val - 524288) % 65536 = a.val := by simp only [row26]; omega
    simp [coefficientAt26, h0, h1, hj, ha, signedCoefficients26, Digit26.exponent]
  | right17 j =>
    have h0 : ¬ (row26 (.right17 j) a).val < 524288 := by simp only [row26]; omega
    have h1 : ¬ (row26 (.right17 j) a).val < 1441792 := by simp only [row26]; omega
    have hj : ((row26 (.right17 j) a).val - 1441792) / 65536 = j.val := by simp only [row26]; omega
    have ha : ((row26 (.right17 j) a).val - 1441792) % 65536 = a.val := by simp only [row26]; omega
    simp [coefficientAt26, h0, h1, hj, ha, signedCoefficients26, Digit26.exponent]

def initialPositivePoint26 (a : Nat) : Point :=
  oddScalar 238 a • G

def initialPoint26 (_Q : Point) (v : Nat) : Point :=
  Width16Schedule.increment G 20 238 v

def positivePoint26 (Q : Point) (w : Digit26) (a : Nat) : Point :=
  oddScalar w.exponent a • w.base Q

theorem initialCoefficients26_point (Q : Point) (hQ : order • Q = 0) (a : Nat) :
    constantPoint Q (initialCoefficients26 a) = initialPositivePoint26 a := by
  unfold initialCoefficients26 initialPositivePoint26
  simpa using coefficients_point (oddScalar 238 a) 0 Q hQ

theorem initialPositivePoint26_ne_zero (a : Nat) (ha : a < 524288) :
    initialPositivePoint26 a ≠ 0 := by
  have hl : 1048575 < order := by norm_num [order]
  exact Width16Schedule.odd_scalar_ne_zero G generator_nsmul_eq_zero G_ne_zero 238 a (by omega)

theorem increment_offset_20 (P : Point) (hr : order • P = 0) (exponent v : Nat) :
    Width16Schedule.increment P 20 exponent v + offsetScalar 20 exponent • P = (v * 2 ^ exponent) • P := by
  have hh : halfOrder ≤ 2 ^ 19 + order := by
    have hl : halfOrder ≤ order := by
      have horder : 0 < order := by norm_num [order]
      dsimp [Single.halfOrder]; omega
    exact hl.trans (Nat.le_add_left _ _)
  have he : (2 ^ 19 + order - halfOrder) • P + halfOrder • P = 2 ^ 19 • P := by
    rw [← add_nsmul, Nat.sub_add_cancel hh, add_nsmul, hr, add_zero]
  have hoff : offsetScalar 20 exponent • P =
      2 ^ 19 • (2 ^ exponent • P) - (halfOrder * 2 ^ exponent) • P := by
    unfold offsetScalar
    change ((2 ^ 19 + order - halfOrder) * 2 ^ exponent) • P = _
    rw [mul_smul, smul_comm (2 ^ 19 + order - halfOrder) (2 ^ exponent),
      eq_sub_iff_add_eq.mpr he, nsmul_sub]
    simp only [mul_smul]
    rw [smul_comm (2 ^ exponent) (2 ^ 19), smul_comm (2 ^ exponent) halfOrder]
  let H := (halfOrder * 2 ^ exponent) • P
  have hd : H + H = 2 ^ exponent • P := by
    change (halfOrder * 2 ^ exponent) • P + (halfOrder * 2 ^ exponent) • P = _
    rw [mul_smul, smul_comm halfOrder (2 ^ exponent), ← nsmul_add]
    exact congrArg (fun R : Point => 2 ^ exponent • R)
      (signedWindowHalfPoint_double P order (by decide +kernel) hr)
  have hp : (2 : Int) ^ 20 = 2 * (2 ^ 19 : Nat) := by norm_num
  have hcalc : ((2 * (v : Int) - (2 : Int) ^ 20 + 1) • H) +
      (2 ^ 19 • (H + H) - H) = v • (H + H) := by rw [hp]; module
  change ((2 * (v : Int) - (2 : Int) ^ 20 + 1) • H) + _ = _
  rw [hoff]
  simp only [hd] at hcalc
  exact hcalc.trans (mul_smul v (2 ^ exponent) P).symm

theorem signedCoefficients26_point (Q : Point) (hQ : order • Q = 0) (w : Digit26) (a : Nat) :
    constantPoint Q (signedCoefficients26 w a) = positivePoint26 Q w a := by
  cases w <;> simp [signedCoefficients26, coefficients_point _ _ Q hQ, positivePoint26, Digit26.base]

theorem positivePoint26_ne_zero (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : Digit26) (a : Nat) (ha : a < 65536) : positivePoint26 Q w a ≠ 0 := by
  have hp : w.base Q ≠ 0 := by cases w <;> [exact G_ne_zero; exact hn]
  have hr : order • w.base Q = 0 := by cases w <;> [exact generator_nsmul_eq_zero; exact hQ]
  have hl : 131071 < order := by norm_num [order]
  exact Width16Schedule.odd_scalar_ne_zero (w.base Q) hr hp w.exponent a (by omega)

/-- Specialization table retaining only the `12 × 65,536 = 786,432` `Q`-rows plus one zero sentinel (`786,433 ≤ 983,040`). -/
@[irreducible] def retainedAt26 (i : Fin 786433) : PointCoeff :=
  if h : i.val < 786432 then coefficientAt26 ⟨1441792 + i.val, by omega⟩
  else coefficients 0 0

def sentinel26 : ConstantBit 786433 := ⟨⟨786432, by decide +kernel⟩, .x, 0⟩

def classify26 (r : ConstantBit 2228224) : Bool ⊕ ConstantBit 786433 :=
  if h : r.point.val < 1441792 then .inl (readConstant coefficientAt26 (0 : Point) r)
  else .inr ⟨⟨r.point.val - 1441792, by have := r.point.isLt; omega⟩, r.field, r.bit⟩

theorem fixed26_b_zero (i : Fin 2228224) (hhi : i.val < 1441792) :
    (coefficientAt26 i).b.val = 0 := by
  unfold coefficientAt26
  split_ifs <;> simp [initialCoefficients26, coefficients]

theorem sentinel26_false (Q : Point) : readConstant retainedAt26 Q sentinel26 = false := by
  simp [sentinel26, retainedAt26, readConstant, coefficients, constantPoint, fieldValue, pointCoordinates]

theorem retained26_agree (Q : Point) (r : ConstantBit 2228224) :
    readConstant coefficientAt26 Q r = (classify26 r).elim id (readConstant retainedAt26 Q) := by
  unfold classify26
  split
  next h =>
    simp only [Sum.elim_inl, id_eq]
    exact generator_only_readConstant coefficientAt26 r (fixed26_b_zero _ h) Q 0
  next h =>
    simp only [Sum.elim_inr, readConstant]
    have hh : r.point.val - 1441792 < 786432 := by have := r.point.isLt; omega
    have he : 1441792 + (r.point.val - 1441792) = r.point.val := by omega
    simp only [retainedAt26, hh, ↓reduceDIte, he]

def rawLimits26 : Limits := { officialLimits with coefficientRows := 2228224 }

def specializeProgram26 {s e : Nat} (p : Straight 2228224 s e) : Straight 786433 s e :=
  specialize classify26 sentinel26 p

def specializeEntry26 (e : StraightEntry)
    (he : e.coefficients = List.ofFn coefficientAt26) : StraightEntry :=
  Single.fixedEntry retainedAt26
    (specializeProgram26 (Width16Schedule.canonicalProgram coefficientAt26 e he))

theorem specializeEntry26_certificate (e : StraightEntry)
    (he : e.coefficients = List.ofFn coefficientAt26)
    (layout : DecodeLayout) (bounds : Bounds) (h : Certificate rawLimits26 layout e bounds) :
    Certificate officialLimits layout (specializeEntry26 e he) bounds := by
  have hc := Width16Schedule.canonical_certificate coefficientAt26 e he rawLimits26 layout bounds h
  exact Width16Schedule.fixed_specialize_certificate coefficientAt26 retainedAt26 classify26 sentinel26
    sentinel26_false retained26_agree (Width16Schedule.canonicalProgram coefficientAt26 e he)
    officialLimits layout bounds hc (by change 786433 ≤ 983040; omega)

/-! ### Physical windows and program -/

attribute [local irreducible] First20Signed.program CornerWire.Wide16.program
  WideBank8.Signed16.program WideBank8.Row16.program Single.axis resetProgram
  WideBank8.Fast16.fcodeTP WideSigned.Body.signCredit

structure CreditBox26 where
  val : Nat

def mkCreditBox26 (c : Nat) : CreditBox26 := ⟨c⟩
theorem mkCreditBox26_val (c : Nat) : (mkCreditBox26 c).val = c := rfl

def wideCredit26Box : CreditBox26 :=
  mkCreditBox26 (2 * WideSigned.Body.signCredit + (WideBank8.Fast16.fcodeTP WideBank8.Row16.code - 15098 - 23997 - 502))

theorem wideCredit26_bound : wideCredit26Box.val ≤ 2303094 := by
  rw [wideCredit26Box, mkCreditBox26_val]
  exact CornerWire.Wide16.credit_bound

def top10Left : List Wire := First20Signed.bits.drop 10
def bank17 : List Wire := (WideSigned.Body.logicalBank .w16).map TightSupport.compact17_7
def top10Right : List Wire := bank17.drop 7

theorem top10Left_length : top10Left.length = 10 := by decide
theorem top10Left_nodup : top10Left.Nodup := by decide
theorem top10Left_sub_bits : top10Left ⊆ First20Signed.bits := List.drop_subset 10 First20Signed.bits
theorem top10Left_sub_range : top10Left ⊆ List.range 1613 :=
  top10Left_sub_bits.trans First20Signed.bits_subset_range

theorem bank17_length : bank17.length = 17 := by decide
theorem bank17_nodup : bank17.Nodup := by decide
theorem bank17_sub_range : bank17 ⊆ List.range 1613 := by decide
theorem top10Right_length : top10Right.length = 10 := by decide
theorem top10Right_nodup : top10Right.Nodup := by decide
theorem top10Right_sub_bank : top10Right ⊆ bank17 := List.drop_subset 7 bank17
theorem top10Right_sub_range : top10Right ⊆ List.range 1613 :=
  top10Right_sub_bank.trans bank17_sub_range

def first20RawWin : Window 2228224 := First20Signed.windowGeneric firstRow26

def first20Win : Window 2228224 :=
  ⟨First20Signed.bits.reverse, 193640,
    fun start => prependCircuit (sineFromPlus top10Left) (first20RawWin.program start)⟩

def bodyWin (d : Digit26) : Window 2228224 :=
  ⟨bank17.reverse, 1703388,
    fun start => reindexStraight (row26 d)
      (relabelStraight TightSupport.compact17_7 (CornerWire.Wide16.program start))⟩

def rightHeadDigit : Digit26 := .right17 ⟨0, by decide⟩
def rightTailDigits26 : List Digit26 := List.ofFn (fun j : Fin 11 => .right17 ⟨j.val + 1, by omega⟩)

theorem rightDigits26_cons : rightDigits26 = rightHeadDigit :: rightTailDigits26 := by
  simp [rightDigits26, rightHeadDigit, rightTailDigits26, List.ofFn_succ]

def rightHeadWin : Window 2228224 :=
  ⟨bank17.reverse, 1703388,
    fun start => prependCircuit (sineFromPlus top10Right) ((bodyWin rightHeadDigit).program start)⟩

def leftWins26 : List (Window 2228224) := first20Win :: leftDigits26.map bodyWin
def rightWins26 : List (Window 2228224) := rightHeadWin :: rightTailDigits26.map bodyWin

/-! ### Window models, rules, readiness, and strong ideal success (`≥ 9911 / 10000`) -/

def SignedWeights26 (Q P : Point) : List Digit26 → Prop
  | List.nil => True
  | w :: ws => w.base Q = P ∧ w.exponent = (ws.map (fun _ => (17 : Nat))).sum ∧ SignedWeights26 Q P ws

theorem left_signed_weights26 (Q : Point) : SignedWeights26 Q G leftDigits26 := by
  norm_num [leftDigits26, List.ofFn_succ, SignedWeights26, Digit26.exponent, Digit26.base]

theorem right_signed_weights26 (Q : Point) : SignedWeights26 Q Q rightDigits26 := by
  norm_num [rightDigits26, List.ofFn_succ, SignedWeights26, Digit26.exponent, Digit26.base]

theorem modelWeights26 {n : Nat} {read : ConstantBit n → Bool}
    (Q P : Point) (hr : order • P = 0) (f : Digit26 → WindowModel read)
    (hwidth : ∀ w, (f w).physical.wires.length = 17)
    (hpoint : ∀ w v, (f w).point v = Width16Schedule.increment (w.base Q) 17 w.exponent v)
    (hbias : ∀ w, (f w).bias = offsetScalar 17 w.exponent • w.base Q)
    (ws : List Digit26) (hw : SignedWeights26 Q P ws) : ModelWeights P (ws.map f) := by
  induction ws with
  | nil => trivial
  | cons w ws ih =>
    constructor
    · intro v
      have hwidths : ((ws.map f).map (fun x => x.physical.wires.length)).sum =
          (ws.map (fun _ => (17 : Nat))).sum := by simp only [List.map_map, Function.comp_def, hwidth]
      rw [hwidths, ← hw.2.1, hpoint, hbias, hw.1]
      exact Width16Schedule.increment_offset P hr 17 w.exponent v (Or.inr rfl)
    · exact ih hw.2.2

theorem first20_signed_eq (Q : Point) (hQ : order • Q = 0) (v : Nat) (hv : v < 1048576) :
    First20Signed.signedPoint (fun a => coefficientAt26 (firstRow26 a)) Q v = initialPoint26 Q v := by
  unfold First20Signed.signedPoint First20Signed.tablePoint
  have hpos (a : Nat) :
      constantPoint Q (coefficientAt26 (firstRow26 ⟨a % 524288, Nat.mod_lt _ (by decide +kernel)⟩)) =
        (2 * (a % 524288) + 1) • ((halfOrder * 2 ^ 238) • G) := by
    rw [coefficientAt26_first, initialCoefficients26_point Q hQ]
    unfold initialPositivePoint26 Single.oddScalar
    rw [Nat.mul_assoc, Nat.mul_comm (2 ^ 238) halfOrder, mul_smul]
  have hs := Width16Actual.signed_magnitude ((halfOrder * 2 ^ 238) • G) 524288 v (by decide) (by omega)
  have hinc : Width16Schedule.increment G 20 238 v =
      (2 * (v : Int) - 2 * (524288 : Nat) + 1) • ((halfOrder * 2 ^ 238) • G) := by
    unfold Width16Schedule.increment
    rw [show (2 : Int) ^ 20 = 2 * (524288 : Nat) by norm_num]
  rw [initialPoint26, hinc, ← hs]
  simp only [hpos, show 524288 - 1 = 524287 from rfl]

theorem first20Win_law : WindowLaw coefficientAt26 first20RawWin
    (First20Signed.update initialPoint26) First20Signed.Input := by
  apply First20Signed.window_law_generic
  · intro Q hQ _ a
    rw [coefficientAt26_first, initialCoefficients26_point Q hQ]
    exact initialPositivePoint26_ne_zero a.val a.isLt
  · intro Q hQ _ v hv
    exact first20_signed_eq Q hQ v hv

theorem first20_input_upd (s : BasisState) (w : Wire) (b : Bool)
    (hw : w ∈ First20Signed.bits) (hs : First20Signed.Input s) :
    First20Signed.Input (s[w ↦ b]) := by
  have hne : w ≠ 836 := by
    have := First20Signed.mem_bits.mp hw; (try dsimp only [Wire] at *); omega
  refine ⟨by simp [upd, hne.symm, hs.1], fun v hv hnb => ?_⟩
  have hvw : v ≠ w := fun h => hnb (h ▸ hw)
  simp [upd, hvw, hs.2 v hv hnb]

def first20Model (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    WindowModel (readConstant coefficientAt26 Q) where
  physical := first20Win
  point := initialPoint26 Q
  bias := offsetScalar 20 238 • G
  ideal := (Finsupp.lmapDomain ℂ ℂ (First20Signed.update initialPoint26 Q)).comp
    (Quantum.run (sineFromPlus top10Left))
  valid := First20Signed.Input
  nodup := List.nodup_reverse.mpr First20Signed.bits_nodup
  coherent := by
    intro start history
    exact prependCircuit_coherent (sineFromPlus top10Left) (first20RawWin.program start) _ history _
      First20Signed.Input First20Signed.Input (first20Win_law Q hQ hn start history)
      (fun s hs => circuit_preserves_pred (sineFromPlus top10Left) First20Signed.Input
        (fun t w b hw ht => first20_input_upd t w b
          (top10Left_sub_bits (sineFromPlus_wires top10Left top10Left_length hw)) ht) s hs)

theorem initialRoot_first20 : First20Signed.Input initialRoot := by
  refine ⟨by simp [initialRoot, upd], fun v hv _ => by simp [initialRoot, upd, hv, zeroBasisState]⟩

theorem initialRoot_clean20 : Clean First20Signed.bits initialRoot := by
  intro v hv
  have h := First20Signed.mem_bits.mp hv
  simp [initialRoot, upd, show v ≠ 836 by dsimp only [Wire] at *; omega, zeroBasisState]

theorem first20Model_rule (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    WindowedFirstRule initialRoot (ket initialRoot) (first20Model Q hQ hn) := by
  refine ⟨by change First20Signed.bits.reverse.length ≥ 10; simp [First20Signed.bits_length], ?_⟩
  intro prior output
  change fourierBranch .inverse First20Signed.bits.reverse prior output
      (Finsupp.lmapDomain ℂ ℂ (First20Signed.update initialPoint26 Q)
        (Quantum.run (sineFromPlus top10Left)
          (Quantum.run (First20Signed.bits.reverse.reverse.map Gate.H) (ket initialRoot)))) = _
  rw [List.reverse_reverse]
  have hdrop : First20Signed.bits.drop (First20Signed.bits.length - 10) = top10Left := by
    simp [top10Left, First20Signed.bits_length]
  have hsb := sineFromPlus_bank First20Signed.bits (by simp [First20Signed.bits_length])
    First20Signed.bits_nodup initialRoot initialRoot_clean20
  rw [hdrop] at hsb
  rw [hsb, map_smul, map_smul, stateLinear_list_sum, stateLinear_list_sum, List.map_map, List.map_map]
  simp only [Function.comp_def, map_smul, List.length_reverse]
  congr 1; apply congrArg List.sum; apply List.map_congr_left
  intro input hi
  have hlen : input.length = First20Signed.bits.length := (fourierOutcomes_mem _ _).mp hi
  have hupd : First20Signed.update initialPoint26 Q (phaseWordState First20Signed.bits input initialRoot) =
      pointWrite (initialPoint26 Q (boolWordToNat input)) (phaseWordState First20Signed.bits input initialRoot) := by
    unfold First20Signed.update
    rw [WEX.tableAddress_word, phaseWordState_word First20Signed.bits First20Signed.bits_nodup input hlen]
  have hket : Finsupp.lmapDomain ℂ ℂ (First20Signed.update initialPoint26 Q)
      (ket (phaseWordState First20Signed.bits input initialRoot)) =
      ket (pointWrite (initialPoint26 Q (boolWordToNat input))
        (phaseWordState First20Signed.bits input initialRoot)) := by
    simp only [ket, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, hupd]
  rw [hket, fourierBranch_ket,
    Mixed.branchCoeff_amplitude' .inverse First20Signed.bits.reverse (List.nodup_reverse.mpr First20Signed.bits_nodup)]
  have hmap : First20Signed.bits.reverse.map
      (pointWrite (initialPoint26 Q (boolWordToNat input))
        (phaseWordState First20Signed.bits input initialRoot)) = input.reverse := by
    rw [List.map_reverse]
    congr 1
    have hf : First20Signed.bits.map
        (pointWrite (initialPoint26 Q (boolWordToNat input))
          (phaseWordState First20Signed.bits input initialRoot)) =
        First20Signed.bits.map (phaseWordState First20Signed.bits input initialRoot) := by
      apply List.map_congr_left; intro v hv
      exact pointWrite_frame _ _ _ (First20Signed.bits_not_point v hv)
    rw [hf]
    exact phaseWordState_word First20Signed.bits First20Signed.bits_nodup input hlen initialRoot
  have hclr : fourierClear First20Signed.bits.reverse
      (pointWrite (initialPoint26 Q (boolWordToNat input))
        (phaseWordState First20Signed.bits input initialRoot)) =
      pointWrite (initialPoint26 Q (boolWordToNat input)) initialRoot :=
    clear_assigned_point First20Signed.bits input initialRoot initialRoot_clean20
      (fun v hv hp => First20Signed.bits_not_point v hv hp) (initialPoint26 Q (boolWordToNat input))
  rw [hmap, hclr, smul_smul]; rfl

theorem first20Model_prepared (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    SupportedOn (first20Model Q hQ hn).valid
      (Quantum.run ((first20Model Q hQ hn).physical.wires.reverse.map Gate.H) (ket initialRoot)) := by
  change SupportedOn First20Signed.Input
    (Quantum.run (First20Signed.bits.reverse.reverse.map Gate.H) (ket initialRoot))
  rw [List.reverse_reverse]
  exact circuit_preserves_pred (First20Signed.bits.map Gate.H) First20Signed.Input
    (fun s w b hw hs => first20_input_upd s w b
      (by
        simp only [circuitWires, List.mem_flatMap, List.mem_map] at hw
        obtain ⟨g, ⟨v, hv, rfl⟩, hwg⟩ := hw
        simp only [gateWires, List.mem_singleton] at hwg
        exact hwg ▸ hv) hs)
    initialRoot initialRoot_first20

def wideCoeffs26 (d : Digit26) : Fin 65536 → PointCoeff := fun a => signedCoefficients26 d a.val

theorem wide26_nonzero (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (d : Digit26)
    (a : Fin 65536) : constantPoint Q (wideCoeffs26 d a) ≠ 0 := by
  rw [wideCoeffs26, signedCoefficients26_point Q hQ]
  exact positivePoint26_ne_zero Q hQ hn d a.val a.isLt

theorem wide26_point (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (d : Digit26)
    (v : Nat) (hv : v < 131072) :
    (CornerWire.Wide16.model (wideCoeffs26 d) Q hQ (wide26_nonzero Q hQ hn d)).point v =
      Width16Schedule.increment (d.base Q) 17 d.exponent v := by
  change (if v < 65536 then -constantPoint Q (wideCoeffs26 d (WideSigned.Geometry.rows .w16 (65535 - v)))
    else constantPoint Q (wideCoeffs26 d (WideSigned.Geometry.rows .w16 (v - 65536)))) = _
  simp only [wideCoeffs26, WideSigned.Geometry.rows, WideSigned.Geometry.Width.bits,
    signedCoefficients26_point Q hQ]
  have hpos (a : Nat) : positivePoint26 Q d a = (2 * a + 1) • ((halfOrder * 2 ^ d.exponent) • d.base Q) := by
    unfold positivePoint26 Single.oddScalar
    rw [Nat.mul_assoc, Nat.mul_comm (2 ^ d.exponent) halfOrder, mul_smul]
  simp only [hpos]
  have hs := Width16Actual.signed_magnitude ((halfOrder * 2 ^ d.exponent) • d.base Q) 65536 v (by decide) (by omega)
  simpa only [Width16Schedule.increment, show (2 : Int) ^ 17 = 2 * (65536 : Nat) by norm_num] using hs

def bodyRawModel (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (d : Digit26) :=
  Width16Actual.interpretModel
    (CornerWire.Wide16.model (wideCoeffs26 d) Q hQ (wide26_nonzero Q hQ hn d))
    (Width16Schedule.increment (d.base Q) 17 d.exponent)
    (offsetScalar 17 d.exponent • d.base Q)

def bodyPackedModel (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (d : Digit26) :=
  Width16Actual.relabelModel TightSupport.compact17_7 (bodyRawModel Q hQ hn d)

def bodyModel (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (d : Digit26) :
    WindowModel (readConstant coefficientAt26 Q) :=
  Width16Schedule.reindexModel (wideCoeffs26 d) coefficientAt26 (row26 d)
    (fun a => (coefficientAt26_row d a).symm) Q (bodyPackedModel Q hQ hn d)

theorem bodyModel_physical (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (d : Digit26) :
    (bodyModel Q hQ hn d).physical = bodyWin d := by
  simp [bodyModel, Width16Schedule.reindexModel, Width16Schedule.reindexWindow, bodyPackedModel,
    Width16Actual.relabelModel, bodyRawModel, Width16Actual.interpretModel,
    CornerWire.Wide16.model, CornerWire.Wide16.window, bodyWin, bank17, List.map_reverse]

theorem bodyRawModel_rule (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (d : Digit26) :
    PointRule initialRoot (bodyRawModel Q hQ hn d) := by
  apply Width16Actual.interpret_pointRule
  · exact CornerWire.Wide16.pointRule (wideCoeffs26 d) Q hQ (wide26_nonzero Q hQ hn d)
      initialRoot initialRoot_input.1 (by
        intro v hv
        have hb := WideSigned.Body.bank_bounds .w16 v hv
        simp only [initialRoot, upd, zeroBasisState]
        split_ifs <;> dsimp only [Wire] at * <;> omega)
  · intro v hv; exact wide26_point Q hQ hn d v hv

theorem bodyModel_rule (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (d : Digit26) :
    PointRule initialRoot (bodyModel Q hQ hn d) := by
  change PointRule initialRoot (bodyPackedModel Q hQ hn d)
  exact Width16Actual.relabelModel_pointRule _ _ TightSupport.compact17_7_pointWrite
    TightSupport.compact17_7_active (bodyRawModel_rule Q hQ hn d)

theorem bodyRawModel_prepared (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (d : Digit26)
    (ψ : State) (hψ : SupportedOn (pointFamily initialRoot) ψ) :
    SupportedOn (bodyRawModel Q hQ hn d).valid
      (Quantum.run ((bodyRawModel Q hQ hn d).physical.wires.reverse.map Gate.H) ψ) := by
  have hfamily : SupportedOn (pointFamily (pointWrite 0 initialRoot)) ψ := by
    intro s hs
    obtain ⟨P, hP⟩ := hψ s hs
    exact ⟨P, by rw [pointWrite_overwrite]; exact hP⟩
  exact CornerWire.Wide16.prepared (wideCoeffs26 d) Q hQ (wide26_nonzero Q hQ hn d)
    (pointWrite 0 initialRoot) (WEX.windowReady_first initialRoot initialRoot_input 0)
    (by
      intro v hv
      rw [pointWrite_frame _ _ _ (WideSigned.Body.bank_not_point .w16 v hv)]
      have hb := WideSigned.Body.bank_bounds .w16 v hv
      simp only [initialRoot, upd, zeroBasisState]
      split_ifs <;> dsimp only [Wire] at * <;> omega)
    ψ hfamily

theorem bodyModel_prepared (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (d : Digit26)
    (ψ : State) (hψ : SupportedOn (pointFamily initialRoot) ψ) :
    SupportedOn (bodyModel Q hQ hn d).valid
      (Quantum.run ((bodyModel Q hQ hn d).physical.wires.reverse.map Gate.H) ψ) :=
  Width16Actual.relabelModel_prepared _ _ Width16Actual.inverse_pointFrame
    TightSupport.compact17_7_active (bodyRawModel_prepared Q hQ hn d) ψ hψ

theorem bodyModel_valid_upd (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (d : Digit26)
    (s : BasisState) (w : Wire) (b : Bool) (hw : w ∈ bank17)
    (hs : (bodyModel Q hQ hn d).valid s) : (bodyModel Q hQ hn d).valid (s[w ↦ b]) := by
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
  change WEX.windowReady (relabelBasis TightSupport.compact17_7.symm (s[TightSupport.compact17_7 u ↦ b]))
  rw [relabelBasis_upd, Equiv.symm_apply_apply]
  exact WideSigned.Body.ready_address .w16 _ hs u hu b

def rightHeadModel (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    WindowModel (readConstant coefficientAt26 Q) where
  physical := rightHeadWin
  point := (bodyModel Q hQ hn rightHeadDigit).point
  bias := (bodyModel Q hQ hn rightHeadDigit).bias
  ideal := (bodyModel Q hQ hn rightHeadDigit).ideal.comp (Quantum.run (sineFromPlus top10Right))
  valid := (bodyModel Q hQ hn rightHeadDigit).valid
  nodup := List.nodup_reverse.mpr bank17_nodup
  coherent := by
    intro start history
    have hcoh := (bodyModel Q hQ hn rightHeadDigit).coherent start history
    rw [bodyModel_physical Q hQ hn rightHeadDigit] at hcoh
    exact prependCircuit_coherent (sineFromPlus top10Right) ((bodyWin rightHeadDigit).program start)
      _ history _ _ _ hcoh
      (fun s hs => circuit_preserves_pred (sineFromPlus top10Right) (bodyModel Q hQ hn rightHeadDigit).valid
        (fun t w b hw ht => bodyModel_valid_upd Q hQ hn rightHeadDigit t w b
          (top10Right_sub_bank (sineFromPlus_wires top10Right top10Right_length hw)) ht) s hs)

theorem rightHeadModel_rule (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    WindowedPointRule initialRoot (rightHeadModel Q hQ hn) := by
  refine ⟨by change bank17.reverse.length ≥ 10; simp [bank17_length], ?_⟩
  intro prior output P
  have hclean_raw : Clean (WideSigned.Body.logicalBank .w16) initialRoot := by
    intro v hv
    have hb := WideSigned.Body.bank_bounds .w16 v hv
    simp only [initialRoot, upd, zeroBasisState]
    split_ifs <;> dsimp only [Wire] at * <;> omega
  have hclean17 : Clean bank17 (pointWrite P initialRoot) := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
    have hpt : TightSupport.compact17_7 u ∉ pointLogicalWires := by
      have : ∀ x ∈ bank17, x ∉ pointLogicalWires := by decide
      exact this _ (List.mem_map.mpr ⟨u, hu, rfl⟩)
    rw [pointWrite_frame _ _ _ hpt]
    have hb : TightSupport.compact17_7 u ≠ 836 := by
      have : (836 : Wire) ∉ bank17 := by decide
      intro h; exact this (h ▸ List.mem_map.mpr ⟨u, hu, rfl⟩)
    simp [initialRoot, upd, hb, zeroBasisState]
  change fourierBranch .inverse bank17.reverse prior output
      ((bodyPackedModel Q hQ hn rightHeadDigit).ideal
        (Quantum.run (sineFromPlus top10Right)
          (Quantum.run (bank17.reverse.reverse.map Gate.H) (ket (pointWrite P initialRoot))))) = _
  rw [List.reverse_reverse]
  have hdrop : bank17.drop (bank17.length - 10) = top10Right := by
    simp [top10Right, bank17_length]
  have hsb := sineFromPlus_bank bank17 (by simp [bank17_length]) bank17_nodup
    (pointWrite P initialRoot) hclean17
  rw [hdrop] at hsb
  rw [hsb, map_smul, map_smul, stateLinear_list_sum, stateLinear_list_sum, List.map_map, List.map_map]
  simp only [Function.comp_def, map_smul, List.length_reverse]
  congr 1; apply congrArg List.sum; apply List.map_congr_left
  intro input hi
  have hlen : input.length = (WideSigned.Body.logicalBank .w16).length := by
    have := (fourierOutcomes_mem _ _).mp hi
    simpa [bank17] using this
  have he_symm_836 : TightSupport.compact17_7.symm 836 = 836 :=
    (Equiv.symm_apply_eq _).mpr TightSupport.compact17_7_active.symm
  have hback : relabelBasis TightSupport.compact17_7.symm (phaseWordState bank17 input (pointWrite P initialRoot)) =
      phaseWordState (WideSigned.Body.logicalBank .w16) input (pointWrite P initialRoot) := by
    rw [relabelBasis_phaseWordState, Width16Actual.inverse_pointFrame,
      Width16Actual.root_relabel _ he_symm_836]
    have hmap : bank17.map TightSupport.compact17_7.symm = WideSigned.Body.logicalBank .w16 := by
      simp [bank17, List.map_map, Function.comp_def]
    rw [hmap]
  have hstate :
      WideSigned.Body.state .w16 (wideCoeffs26 rightHeadDigit) Q
        (phaseWordState (WideSigned.Body.logicalBank .w16) input (pointWrite P initialRoot)) =
      pointWrite (P + Width16Schedule.increment (rightHeadDigit.base Q) 17 rightHeadDigit.exponent (boolWordToNat input))
        (phaseWordState (WideSigned.Body.logicalBank .w16) input (pointWrite P initialRoot)) := by
    have hcoords : pointStateCoordinates (phaseWordState (WideSigned.Body.logicalBank .w16) input (pointWrite P initialRoot)) =
        fig14PointEncoding P := by
      rw [phaseWordState_pointWrite _ (WideSigned.Body.bank_not_point .w16), pointWrite_coordinates]
    have ha : (phaseWordState (WideSigned.Body.logicalBank .w16) input (pointWrite P initialRoot)) 836 = true := by
      rw [phaseWordState_frame _ _ _ 836 (by decide), pointWrite_frame _ _ _ (by decide)]
      exact initialRoot_input.1
    have hr : WideSigned.Body.raw .w16 (phaseWordState (WideSigned.Body.logicalBank .w16) input (pointWrite P initialRoot)) =
        boolWordToNat input := by
      rw [WideSigned.Body.raw, WEX.tableAddress_word,
        phaseWordState_word _ (WideSigned.Body.bank_nodup .w16) input hlen]
    rw [WideSigned.Body.state_correct .w16 (wideCoeffs26 rightHeadDigit) Q _ P hcoords,
      WideSigned.Body.selected_prefix .w16 (wideCoeffs26 rightHeadDigit) Q hQ (wide26_nonzero Q hQ hn rightHeadDigit) _ ha,
      hr]
    have hlt : boolWordToNat input < 131072 := by
      have := boolWordToNat_lt input
      have hlen17 : input.length = 17 := by simpa [bank17_length] using (fourierOutcomes_mem _ _).mp hi
      simpa [hlen17] using this
    exact congrArg (fun R => pointWrite (P + R) _) (wide26_point Q hQ hn rightHeadDigit (boolWordToNat input) hlt)
  have hideal :
      (bodyPackedModel Q hQ hn rightHeadDigit).ideal (ket (phaseWordState bank17 input (pointWrite P initialRoot))) =
        ket (pointWrite (P + (rightHeadModel Q hQ hn).point (boolWordToNat input))
          (phaseWordState bank17 input (pointWrite P initialRoot))) := by
    change relabelState TightSupport.compact17_7
      (Finsupp.lmapDomain ℂ ℂ (WideSigned.Body.state .w16 (wideCoeffs26 rightHeadDigit) Q)
        (relabelState TightSupport.compact17_7.symm (ket (phaseWordState bank17 input (pointWrite P initialRoot))))) = _
    rw [relabelState_ket, hback, Mixed.lmap_ket', hstate, relabelState_ket,
      TightSupport.compact17_7_pointWrite, relabelBasis_phaseWordState,
      TightSupport.compact17_7_pointWrite, Width16Actual.root_relabel _ TightSupport.compact17_7_active]
    rfl
  rw [hideal, fourierBranch_ket,
    Mixed.branchCoeff_amplitude' .inverse bank17.reverse (List.nodup_reverse.mpr bank17_nodup)]
  have hpt_disj : ∀ v ∈ bank17, v ∉ pointLogicalWires := by decide
  have hmap : bank17.reverse.map
      (pointWrite (P + (rightHeadModel Q hQ hn).point (boolWordToNat input))
        (phaseWordState bank17 input (pointWrite P initialRoot))) = input.reverse := by
    rw [List.map_reverse]; congr 1
    have hf : bank17.map
        (pointWrite (P + (rightHeadModel Q hQ hn).point (boolWordToNat input))
          (phaseWordState bank17 input (pointWrite P initialRoot))) =
        bank17.map (phaseWordState bank17 input (pointWrite P initialRoot)) := by
      apply List.map_congr_left; intro v hv; exact pointWrite_frame _ _ _ (hpt_disj v hv)
    rw [hf]
    exact phaseWordState_word bank17 bank17_nodup input (by simpa using (fourierOutcomes_mem _ _).mp hi) _
  have hclr : fourierClear bank17.reverse
      (pointWrite (P + (rightHeadModel Q hQ hn).point (boolWordToNat input))
        (phaseWordState bank17 input (pointWrite P initialRoot))) =
      pointWrite (P + (rightHeadModel Q hQ hn).point (boolWordToNat input)) initialRoot := by
    rw [clear_assigned_point bank17 input (pointWrite P initialRoot) hclean17 hpt_disj
      (P + (rightHeadModel Q hQ hn).point (boolWordToNat input)), pointWrite_overwrite]
  rw [hmap, hclr, smul_smul]; rfl

def leftModels26 (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    List (WindowModel (readConstant coefficientAt26 Q)) :=
  first20Model Q hQ hn :: leftDigits26.map (bodyModel Q hQ hn)

def rightModels26 (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    List (WindowModel (readConstant coefficientAt26 Q)) :=
  rightHeadModel Q hQ hn :: rightTailDigits26.map (bodyModel Q hQ hn)

theorem leftModels26_physical (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    (leftModels26 Q hQ hn).map WindowModel.physical = leftWins26 := by
  simp only [leftModels26, leftWins26, List.map_cons, List.map_map, Function.comp_def,
    bodyModel_physical]; rfl

theorem rightModels26_physical (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    (rightModels26 Q hQ hn).map WindowModel.physical = rightWins26 := by
  simp only [rightModels26, rightWins26, List.map_cons, List.map_map, Function.comp_def,
    bodyModel_physical]; rfl

theorem leftModels26_weights (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    ModelWeights G (leftModels26 Q hQ hn) := by
  constructor
  · intro v
    have hw : ((leftDigits26.map (bodyModel Q hQ hn)).map (fun x => x.physical.wires.length)).sum = 238 := by
      simp only [List.map_map, Function.comp_def, bodyModel_physical, bodyWin, List.length_reverse, bank17_length]
      simp [leftDigits26, List.ofFn_succ]
    rw [hw]
    exact increment_offset_20 G generator_nsmul_eq_zero 238 v
  · exact modelWeights26 Q G generator_nsmul_eq_zero (bodyModel Q hQ hn)
      (fun w => by rw [bodyModel_physical]; simp [bodyWin, bank17_length])
      (fun _ _ => rfl)
      (fun _ => by simp [bodyModel, Width16Schedule.reindexModel, bodyPackedModel, Width16Actual.relabelModel,
        bodyRawModel, Width16Actual.interpretModel])
      leftDigits26 (left_signed_weights26 Q)

theorem rightModels26_weights (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    ModelWeights Q (rightModels26 Q hQ hn) := by
  have hall := modelWeights26 Q Q hQ (bodyModel Q hQ hn)
    (fun w => by rw [bodyModel_physical]; simp [bodyWin, bank17_length])
    (fun _ _ => rfl)
    (fun _ => by simp [bodyModel, Width16Schedule.reindexModel, bodyPackedModel, Width16Actual.relabelModel,
      bodyRawModel, Width16Actual.interpretModel])
    rightDigits26 (right_signed_weights26 Q)
  rw [rightDigits26_cons, List.map_cons] at hall
  exact ⟨hall.1, hall.2⟩

theorem ready_bodyList (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (ws : List Digit26)
    (ψ : State) (hψ : SupportedOn (pointFamily initialRoot) ψ) :
    Ready (ws.map (bodyModel Q hQ hn)) ψ := by
  induction ws generalizing ψ with
  | nil => trivial
  | cons w ws ih =>
    refine ⟨bodyModel_prepared Q hQ hn w ψ hψ, fun prior bits => ih _ ?_⟩
    refine Support.linear (pointFamily initialRoot) (pointFamily initialRoot)
      ((bodyModel Q hQ hn w).step prior bits) ?_ ψ hψ
    intro s hs
    obtain ⟨P, rfl⟩ := hs
    rw [bodyModel_rule Q hQ hn w prior bits P]
    apply Support.smul; apply Support.list_sum; intro input _
    exact Support.smul _ (supportedOn_ket _ _ ⟨_, rfl⟩)

theorem ready_all26 (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    Ready (leftModels26 Q hQ hn ++ rightModels26 Q hQ hn) (ket initialRoot) := by
  refine ⟨first20Model_prepared Q hQ hn, fun prior bits => ?_⟩
  have h1 : SupportedOn (pointFamily initialRoot) ((first20Model Q hQ hn).step prior bits (ket initialRoot)) := by
    rw [(first20Model_rule Q hQ hn).2 prior bits]
    apply Support.smul; apply Support.list_sum; intro input _
    exact Support.smul _ (supportedOn_ket _ _ ⟨_, rfl⟩)
  have htail (ψ : State) (hψ : SupportedOn (pointFamily initialRoot) ψ) :
      Ready (rightModels26 Q hQ hn) ψ := by
    refine ⟨by simpa only [rightHeadModel, rightHeadWin, bodyModel_physical, bodyWin] using
        bodyModel_prepared Q hQ hn rightHeadDigit ψ hψ, fun prior' bits' => ?_⟩
    apply ready_bodyList Q hQ hn rightTailDigits26
    refine Support.linear (pointFamily initialRoot) (pointFamily initialRoot)
      ((rightHeadModel Q hQ hn).step prior' bits') ?_ ψ hψ
    intro s hs
    obtain ⟨P, rfl⟩ := hs
    rw [(rightHeadModel_rule Q hQ hn).2 prior' bits' P]
    apply Support.smul; apply Support.list_sum; intro input _
    exact Support.smul _ (supportedOn_ket _ _ ⟨_, rfl⟩)
  have happ : ∀ (ws : List Digit26) (ψ : State), SupportedOn (pointFamily initialRoot) ψ →
      Ready (ws.map (bodyModel Q hQ hn) ++ rightModels26 Q hQ hn) ψ := by
    intro ws
    induction ws with
    | nil => exact htail
    | cons w ws ih =>
      intro ψ hψ
      refine ⟨bodyModel_prepared Q hQ hn w ψ hψ, fun p b => ih _ ?_⟩
      refine Support.linear (pointFamily initialRoot) (pointFamily initialRoot)
        ((bodyModel Q hQ hn w).step p b) ?_ ψ hψ
      intro s hs; obtain ⟨P, rfl⟩ := hs
      rw [bodyModel_rule Q hQ hn w p b P]
      apply Support.smul; apply Support.list_sum; intro input _
      exact Support.smul _ (supportedOn_ket _ _ ⟨_, rfl⟩)
  exact happ leftDigits26 _ h1

/-! ### Part 3b: Local-catalyst compiled windows, program, layout, and `≥ 9911/10000` ideal success -/

attribute [local irreducible] LocalWide16.compiledProgram LocalWide16.compiledProgramFn
  LocalFour.compileLower CatAxis.axisCat ConditionalCatalyst.compile
  AndGadget.added AndGadget.residue

-- Kernel-opaque `Nat` counts via `Classical.choose`: the kernel's `is_def_eq_offset` / `whnf`
-- stops immediately at `Classical.choose` instead of unfolding `compileLower` or `compiledProgramFn`.
private theorem cFirst20_exists :
    ∃ n : Nat, n = AndGadget.Lowered.finish (LocalFour.compileLower 0 1 (first20RawWin.program 0) 0 Fin.elim0) :=
  ⟨_, rfl⟩

def cFirst20 : Nat := Classical.choose cFirst20_exists

theorem cFirst20_eq :
    cFirst20 = AndGadget.Lowered.finish (LocalFour.compileLower 0 1 (first20RawWin.program 0) 0 Fin.elim0) :=
  Classical.choose_spec cFirst20_exists

private theorem cBody16_exists :
    ∃ n : Nat, n = LocalFour.CatProg.finish (LocalWide16.compiledProgramFn 0) :=
  ⟨_, rfl⟩

def cBody16 : Nat := Classical.choose cBody16_exists

theorem cBody16_eq :
    cBody16 = LocalFour.CatProg.finish (LocalWide16.compiledProgramFn 0) :=
  Classical.choose_spec cBody16_exists

theorem cBody16_le : cBody16 ≤ 4010000 := by
  rw [cBody16_eq]
  exact LocalWide16.compiledRec16_bound

private theorem compileLower_finish_zero {n e : Nat} (q y : Wire) (p : Straight n 0 e) (start : Nat) :
    (LocalFour.compileLower q y p start Fin.elim0).finish =
      start + (LocalFour.compileLower q y p 0 Fin.elim0).finish := by
  have h1 := LocalFour.compileLower_finish q y p start Fin.elim0
  have h0 := LocalFour.compileLower_finish q y p 0 Fin.elim0
  omega

private theorem compileLower_finish_le {n e : Nat} (q y : Wire) (p : Straight n 0 e)
    (E A B : Nat) (he : e ≤ E) (ha : AndGadget.added p ≤ A) (hB : E + A ≤ B) :
    (LocalFour.compileLower q y p 0 Fin.elim0).finish ≤ B := by
  have h0 := LocalFour.compileLower_finish q y p 0 Fin.elim0
  omega

theorem first20Cat_finish_eq (start : Nat) :
    (LocalFour.compileLower 0 1 (first20RawWin.program 0) start Fin.elim0).finish = start + cFirst20 := by
  rw [cFirst20_eq]
  exact compileLower_finish_zero 0 1 (first20RawWin.program 0) start

theorem first20Cat_count_le : cFirst20 ≤ 387265 := by
  rw [cFirst20_eq]
  exact compileLower_finish_le 0 1 (first20RawWin.program 0) 193640 193625 387265
    (by change 0 + 193640 ≤ 193640; omega)
    (by unfold first20RawWin First20Signed.windowGeneric; rw [added_reindex]; exact First20Signed.program_added 0)
    (by omega)

def first20CatWin : Window 2228224 :=
  ⟨First20Signed.bits.reverse, cFirst20,
    fun start => (ConditionalCatalyst.compile 1 (literalProgram (sineFromPlus top10Left))).append
      (castFinish (first20Cat_finish_eq start)
        (LocalFour.compileLower 0 1 (first20RawWin.program 0) start Fin.elim0).program)⟩

def bodyCatWin (d : Digit26) : Window 2228224 :=
  ⟨bank17.reverse, cBody16,
    fun start => castFinish (congrArg (start + ·) cBody16_eq.symm)
      (reindexStraight (row26 d)
        (relabelStraight TightSupport.compact17_7 (LocalWide16.compiledProgram start)))⟩

def rightHeadCatWin : Window 2228224 :=
  ⟨bank17.reverse, cBody16,
    fun start => (ConditionalCatalyst.compile 1 (literalProgram (sineFromPlus top10Right))).append
      ((bodyCatWin rightHeadDigit).program start)⟩

def leftWins26Cat : List (Window 2228224) := first20CatWin :: leftDigits26.map bodyCatWin
def rightWins26Cat : List (Window 2228224) := rightHeadCatWin :: rightTailDigits26.map bodyCatWin

def leftMeta26Cat : List (Nat × Nat) := (cFirst20, 20) :: List.replicate 14 (cBody16, 17)
def rightMeta26Cat : List (Nat × Nat) := List.replicate 12 (cBody16, 17)

theorem leftWins26Cat_meta : leftWins26Cat.map (fun w => (w.count, w.wires.length)) = leftMeta26Cat := by
  simp only [leftWins26Cat, leftMeta26Cat, List.map_cons, List.map_map, Function.comp_def,
    first20CatWin, bodyCatWin, List.length_reverse, First20Signed.bits_length, bank17_length]
  simp [leftDigits26, List.ofFn_succ, List.replicate]

theorem rightWins26Cat_meta : rightWins26Cat.map (fun w => (w.count, w.wires.length)) = rightMeta26Cat := by
  simp only [rightWins26Cat, rightMeta26Cat, List.map_cons, List.map_map, Function.comp_def,
    rightHeadCatWin, bodyCatWin, List.length_reverse, bank17_length]
  simp [rightTailDigits26, List.ofFn_succ, List.replicate]

theorem leftWins26Cat_count_eq :
    axisCount leftWins26Cat = cFirst20 + 20 + 14 * (cBody16 + 17) := by
  rw [← recordCount_eq_axisCount, leftWins26Cat_meta]
  simp only [leftMeta26Cat, List.replicate, recordCount]
  omega

theorem rightWins26Cat_count_eq :
    axisCount rightWins26Cat = 12 * (cBody16 + 17) := by
  rw [← recordCount_eq_axisCount, rightWins26Cat_meta]
  simp only [rightMeta26Cat, List.replicate, recordCount]
  omega

def leftPositions26Cat : List Nat := positions leftMeta26Cat 0
def rightPositions26Cat : List Nat := positions rightMeta26Cat (axisCount leftWins26Cat)

theorem leftPositions26Cat_length : leftPositions26Cat.length = 258 := by
  simp only [leftPositions26Cat, positions_length, leftMeta26Cat, List.replicate,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rfl

theorem rightPositions26Cat_length : rightPositions26Cat.length = 204 := by
  simp only [rightPositions26Cat, positions_length, rightMeta26Cat, List.replicate,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rfl

def trialPositions26Cat : TrialPositions params258 where
  left := ⟨leftPositions26Cat.toArray, by
    simpa only [List.size_toArray, params258] using leftPositions26Cat_length⟩
  right := ⟨rightPositions26Cat.toArray, by
    simpa only [List.size_toArray, params258] using rightPositions26Cat_length⟩

theorem leftPositions26Cat_bound (i : Nat) (hi : i ∈ trialPositions26Cat.left.toList) :
    i < axisCount leftWins26Cat := by
  have hi' : i ∈ leftPositions26Cat := by simpa [trialPositions26Cat] using hi
  have hb := positions_bounds leftMeta26Cat 0 i hi'
  have hr : recordCount leftMeta26Cat = axisCount leftWins26Cat := by
    rw [← leftWins26Cat_meta, recordCount_eq_axisCount]
  omega

theorem rightPositions26Cat_bound (i : Nat) (hi : i ∈ trialPositions26Cat.right.toList) :
    i < axisCount leftWins26Cat + axisCount rightWins26Cat := by
  have hi' : i ∈ rightPositions26Cat := by simpa [trialPositions26Cat] using hi
  have hb := positions_bounds rightMeta26Cat (axisCount leftWins26Cat) i hi'
  have hr : recordCount rightMeta26Cat = axisCount rightWins26Cat := by
    rw [← rightWins26Cat_meta, recordCount_eq_axisCount]
  omega

def cursor26Cat : Nat := axisCount leftWins26Cat + axisCount rightWins26Cat + resetWires.length

def finePositions26Cat : List (Fin cursor26Cat) :=
  trialPositions26Cat.right.toList.attach.map fun i =>
    ⟨i.val, (rightPositions26Cat_bound i.val i.property).trans_le (by unfold cursor26Cat; omega)⟩

theorem finePositions26Cat_length : finePositions26Cat.length = 204 := by
  simp [finePositions26Cat, params258]

def fineBits26Cat : Vector (Fin cursor26Cat) 204 :=
  Vector.ofFn fun i => finePositions26Cat[i.val]'(by rw [finePositions26Cat_length]; exact i.isLt)

theorem fineBits26Cat_vals : fineBits26Cat.map Fin.val = trialPositions26Cat.right := by
  apply Vector.ext; intro i hi
  simp [fineBits26Cat, finePositions26Cat]; rfl

def readout26Cat : Straight 2228224 cursor26Cat (cursor26Cat + 1634) :=
  castFinish (by omega) (Readout3.suffix3 2228224 cursor26Cat 204 fineBits26Cat)

def program26Cat : Straight 2228224 0 cursor26Cat :=
  AndGadget.literals (Catalyst.prepare 1)
    (Single.framed
      (CatAxis.axisCat 1 leftWins26Cat 0 List.nil)
      (CatAxis.axisCat 1 rightWins26Cat (0 + axisCount leftWins26Cat) List.nil)
      (resetProgram 2228224 (0 + axisCount leftWins26Cat + axisCount rightWins26Cat) resetWires)
      (by unfold cursor26Cat; omega))

def fullProgram26Cat : Straight 2228224 0 (cursor26Cat + 1634) :=
  program26Cat.append readout26Cat

def rawEntry26Cat : StraightEntry := Single.fixedEntry coefficientAt26 fullProgram26Cat

def positionsFor26Cat (ps : Vector Nat 204) : TrialPositions params258 :=
  { left := trialPositions26Cat.left, right := ps }

def rawLayout26Cat : DecodeLayout :=
  ⟨.wrappedShift, params258, (Readout3.rightWords3 fineBits26Cat).map positionsFor26Cat, by
    simp only [List.length_map, Readout3.rightWords3_length]; decide⟩

/-! ### Catalyst window models and strong ideal success (`≥ 9911 / 10000`) -/

private theorem wire01_not_first20Bits :
    (0 : Wire) ∉ First20Signed.bits ∧ (1 : Wire) ∉ First20Signed.bits := by
  constructor <;> intro hm <;>
    (have := First20Signed.bits_subset_drop01 hm; simp only [List.mem_range'_1] at this; omega)

private theorem wire1_not_bank17 : (1 : Wire) ∉ bank17 := by decide

private theorem first20_input_clean01 (s : BasisState) (hs : First20Signed.Input s) :
    s 0 = false ∧ s 1 = false :=
  ⟨hs.2 0 (by decide) wire01_not_first20Bits.1, hs.2 1 (by decide) wire01_not_first20Bits.2⟩

private theorem wire15645_mem_windowScratch : (15645 : Wire) ∈ WEX.windowScratch :=
  List.mem_append_left _ (List.mem_append_left _
    (Site1Wire.dialogPool_sub_work
      (Site1Wire.pool_band_in_dialogPool (w := 15645) (by dsimp only [Wire, ECDSAAdd.Wire]; omega))))

private theorem bodyModel_valid_y1 (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (d : Digit26)
    (s : BasisState) (hs : (bodyModel Q hQ hn d).valid s) : s 1 = false := by
  have h15645 : (relabelBasis TightSupport.compact17_7.symm s) 15645 = false :=
    hs.2 15645 wire15645_mem_windowScratch
  have hsym : TightSupport.compact17_7.symm 1 = 15645 :=
    (Equiv.symm_apply_eq _).mpr LocalWide16.compact17_7_15645.symm
  simpa only [relabelBasis, hsym] using h15645

private theorem bodyModel_ideal_y1 (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (d : Digit26)
    (ψ : State) (hψ : SupportedOn (bodyModel Q hQ hn d).valid ψ) :
    SupportedOn (fun s => s 1 = false) ((bodyModel Q hQ hn d).ideal ψ) := by
  refine Support.linear _ _ (bodyModel Q hQ hn d).ideal (fun s hs => ?_) ψ hψ
  change SupportedOn (fun t => t 1 = false)
    (relabelState TightSupport.compact17_7
      (Finsupp.lmapDomain ℂ ℂ (WideSigned.Body.state .w16 (wideCoeffs26 d) Q)
        (relabelState TightSupport.compact17_7.symm (ket s))))
  rw [relabelState_ket, Mixed.lmap_ket', relabelState_ket]
  apply supportedOn_ket
  have h15645 : (WideSigned.Body.state .w16 (wideCoeffs26 d) Q (relabelBasis TightSupport.compact17_7.symm s)) 15645 = false := by
    obtain ⟨P, hP⟩ := hs.1.2
    rw [WideSigned.Body.state_correct .w16 (wideCoeffs26 d) Q _ P hP,
      pointWrite_frame _ _ _ (WEX.windowScratch_point_disjoint 15645 wire15645_mem_windowScratch)]
    exact hs.2 15645 wire15645_mem_windowScratch
  have hsym : TightSupport.compact17_7.symm 1 = 15645 :=
    (Equiv.symm_apply_eq _).mpr LocalWide16.compact17_7_15645.symm
  simpa only [relabelBasis, hsym] using h15645

def first20CatModel (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    CatAxis.CatWindow 1 (readConstant coefficientAt26 Q) where
  model := first20Model Q hQ hn
  catPhys := first20CatWin
  wires_eq := rfl
  noY := fun hm => wire01_not_first20Bits.2 (List.mem_reverse.mp hm)
  catCoherent := by
    intro start history
    apply CatAxis.prependCompiledCircuit_catCoherent 1 (sineFromPlus top10Left)
      (castFinish (first20Cat_finish_eq start)
        (LocalFour.compileLower 0 1 (first20RawWin.program 0) start Fin.elim0).program)
      (readConstant coefficientAt26 Q) history
      (Finsupp.lmapDomain ℂ ℂ (First20Signed.update initialPoint26 Q))
      First20Signed.Input First20Signed.Input
    · intro hm
      exact wire01_not_first20Bits.2 (top10Left_sub_bits (sineFromPlus_wires top10Left top10Left_length hm))
    · intro s hs; exact (first20_input_clean01 s hs).2
    · intro s hs
      exact circuit_preserves_pred (sineFromPlus top10Left) First20Signed.Input
        (fun t w b hw ht => first20_input_upd t w b
          (top10Left_sub_bits (sineFromPlus_wires top10Left top10Left_length hw)) ht) s hs
    · rw [castFinish_instantiate]
      have hsub := First20Signed.window_support_drop01 firstRow26 0
      have hf0 : Fresh 0 (first20RawWin.program 0) :=
        LocalFour.fresh_of_not_mem_straightWires _ _ (fun hm => by
          have := hsub hm; simp only [List.mem_range'_1] at this; omega)
      have hf1 : Fresh 1 (first20RawWin.program 0) :=
        LocalFour.fresh_of_not_mem_straightWires _ _ (fun hm => by
          have := hsub hm; simp only [List.mem_range'_1] at this; omega)
      exact LocalFour.compileLower_catCoherent 0 1 (first20RawWin.program 0) start Fin.elim0
        (readConstant coefficientAt26 Q) Fin.elim0 history (fun i => Fin.elim0 i)
        (First20Signed.window_wellFormed firstRow26 0) hf0 hf1 (by decide)
        _ First20Signed.Input first20_input_clean01 (first20Win_law Q hQ hn 0 Fin.elim0)
  idealY := by
    intro ψ hψ
    refine Support.linear _ _ (first20Model Q hQ hn).ideal (fun s hs => ?_) ψ hψ
    change SupportedOn (fun t => t 1 = false)
      (Finsupp.lmapDomain ℂ ℂ (First20Signed.update initialPoint26 Q)
        (Quantum.run (sineFromPlus top10Left) (ket s)))
    have hsine : SupportedOn First20Signed.Input (Quantum.run (sineFromPlus top10Left) (ket s)) :=
      circuit_preserves_pred (sineFromPlus top10Left) First20Signed.Input
        (fun t w b hw ht => first20_input_upd t w b
          (top10Left_sub_bits (sineFromPlus_wires top10Left top10Left_length hw)) ht) s hs
    refine Support.linear First20Signed.Input (fun t => t 1 = false)
      (Finsupp.lmapDomain ℂ ℂ (First20Signed.update initialPoint26 Q)) (fun t ht => ?_) _ hsine
    rw [Mixed.lmap_ket']
    apply supportedOn_ket
    unfold First20Signed.update
    rw [pointWrite_frame _ _ _ (by decide)]
    exact (first20_input_clean01 t ht).2

def bodyCatModel (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (d : Digit26) :
    CatAxis.CatWindow 1 (readConstant coefficientAt26 Q) where
  model := bodyModel Q hQ hn d
  catPhys := bodyCatWin d
  wires_eq := by rw [bodyModel_physical]; rfl
  noY := by rw [bodyModel_physical]; exact fun hm => wire1_not_bank17 (List.mem_reverse.mp hm)
  catCoherent := by
    intro start history
    change LocalFour.CatCoherent 1
      ((castFinish (congrArg (start + ·) cBody16_eq.symm)
        (reindexStraight (row26 d)
          (relabelStraight TightSupport.compact17_7 (LocalWide16.compiledProgram start)))).instantiate
            (readConstant coefficientAt26 Q) history)
      (bodyModel Q hQ hn d).ideal (bodyModel Q hQ hn d).valid
    rw [castFinish_instantiate, reindexStraight_instantiate,
      readConstant_reindex (row26 d) (wideCoeffs26 d) coefficientAt26 Q (fun a => coefficientAt26_row d a),
      relabelStraight_instantiate]
    have hrel := CatAxis.catCoherent_relabel TightSupport.compact17_7 15645
      ((LocalWide16.compiledProgram start).instantiate (readConstant (wideCoeffs26 d) Q) history)
      _ _ (LocalWide16.compiled_coherent (wideCoeffs26 d) Q hQ (wide26_nonzero Q hQ hn d) start history)
    rw [LocalWide16.compact17_7_15645] at hrel
    exact hrel
  idealY := bodyModel_ideal_y1 Q hQ hn d

def rightHeadCatModel (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    CatAxis.CatWindow 1 (readConstant coefficientAt26 Q) where
  model := rightHeadModel Q hQ hn
  catPhys := rightHeadCatWin
  wires_eq := rfl
  noY := fun hm => wire1_not_bank17 (List.mem_reverse.mp hm)
  catCoherent := by
    intro start history
    apply CatAxis.prependCompiledCircuit_catCoherent 1 (sineFromPlus top10Right)
      ((bodyCatWin rightHeadDigit).program start)
      (readConstant coefficientAt26 Q) history
      (bodyModel Q hQ hn rightHeadDigit).ideal
      (bodyModel Q hQ hn rightHeadDigit).valid
      (bodyModel Q hQ hn rightHeadDigit).valid
    · intro hm
      exact wire1_not_bank17 (top10Right_sub_bank (sineFromPlus_wires top10Right top10Right_length hm))
    · exact bodyModel_valid_y1 Q hQ hn rightHeadDigit
    · intro s hs
      exact circuit_preserves_pred (sineFromPlus top10Right) (bodyModel Q hQ hn rightHeadDigit).valid
        (fun t w b hw ht => bodyModel_valid_upd Q hQ hn rightHeadDigit t w b
          (top10Right_sub_bank (sineFromPlus_wires top10Right top10Right_length hw)) ht) s hs
    · exact (bodyCatModel Q hQ hn rightHeadDigit).catCoherent start history
  idealY := by
    intro ψ hψ
    apply bodyModel_ideal_y1 Q hQ hn rightHeadDigit
    refine Support.linear _ _ (Quantum.run (sineFromPlus top10Right)) (fun s hs => ?_) ψ hψ
    exact circuit_preserves_pred (sineFromPlus top10Right) (bodyModel Q hQ hn rightHeadDigit).valid
      (fun t w b hw ht => bodyModel_valid_upd Q hQ hn rightHeadDigit t w b
        (top10Right_sub_bank (sineFromPlus_wires top10Right top10Right_length hw)) ht) s hs

def leftCatModels26 (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    List (CatAxis.CatWindow 1 (readConstant coefficientAt26 Q)) :=
  first20CatModel Q hQ hn :: leftDigits26.map (bodyCatModel Q hQ hn)

def rightCatModels26 (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    List (CatAxis.CatWindow 1 (readConstant coefficientAt26 Q)) :=
  rightHeadCatModel Q hQ hn :: rightTailDigits26.map (bodyCatModel Q hQ hn)

theorem leftCatModels26_model (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    (leftCatModels26 Q hQ hn).map CatAxis.CatWindow.model = leftModels26 Q hQ hn := by
  simp [leftCatModels26, leftModels26, first20CatModel, bodyCatModel, List.map_map, Function.comp_def]

theorem rightCatModels26_model (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    (rightCatModels26 Q hQ hn).map CatAxis.CatWindow.model = rightModels26 Q hQ hn := by
  simp [rightCatModels26, rightModels26, rightHeadCatModel, bodyCatModel, List.map_map, Function.comp_def]

theorem leftCatModels26_catPhys (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    (leftCatModels26 Q hQ hn).map CatAxis.CatWindow.catPhys = leftWins26Cat := by
  simp [leftCatModels26, leftWins26Cat, first20CatModel, bodyCatModel, List.map_map, Function.comp_def]

theorem rightCatModels26_catPhys (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    (rightCatModels26 Q hQ hn).map CatAxis.CatWindow.catPhys = rightWins26Cat := by
  simp [rightCatModels26, rightWins26Cat, rightHeadCatModel, bodyCatModel, List.map_map, Function.comp_def]

def fineEvent26Cat (accept : Nat → Nat → Bool) (history : List Bool) : Bool :=
  pairAccept trialPositions26Cat.left.toList trialPositions26Cat.right.toList accept history

theorem program26Cat_run_data (read : ConstantBit 2228224 → Bool) :
    (program26Cat.instantiate read Fin.elim0).run =
      ((((CatAxis.axisCat 1 leftWins26Cat 0 List.nil).append
          (CatAxis.axisCat 1 rightWins26Cat (0 + axisCount leftWins26Cat) List.nil)).instantiate read Fin.elim0).run.seq
        terminalInstrument).map
        (fun b => ({ history := List.nil, kraus := Quantum.run (Catalyst.prepare 1 ++ [.X 836]) } : InstrumentBranch).seq b) := by
  unfold program26Cat
  rw [LocalFour.literals_instantiate_run]
  have hh : 0 + axisCount leftWins26Cat + axisCount rightWins26Cat + resetWires.length = cursor26Cat := by
    unfold cursor26Cat; omega
  have hfr : ((Single.framed
      (CatAxis.axisCat 1 leftWins26Cat 0 List.nil)
      (CatAxis.axisCat 1 rightWins26Cat (0 + axisCount leftWins26Cat) List.nil)
      (resetProgram 2228224 (0 + axisCount leftWins26Cat + axisCount rightWins26Cat) resetWires) hh).instantiate read Fin.elim0).run =
      ((((CatAxis.axisCat 1 leftWins26Cat 0 List.nil).append
          (CatAxis.axisCat 1 rightWins26Cat (0 + axisCount leftWins26Cat) List.nil)).instantiate read Fin.elim0).run.seq
        terminalInstrument).map
        (fun b => ({ history := List.nil, kraus := Quantum.run [.X 836] } : InstrumentBranch).seq b) := by
    simpa only [terminalInstrument, bodyInst26, PathShare.bodyCF] using
      framed_reset_run (CatAxis.axisCat 1 leftWins26Cat 0 List.nil)
        (CatAxis.axisCat 1 rightWins26Cat (0 + axisCount leftWins26Cat) List.nil)
        (resetProgram 2228224 (0 + axisCount leftWins26Cat + axisCount rightWins26Cat) resetWires)
        hh read Fin.elim0 (measureResetWithCorrection resetWires (fun _ => List.nil))
        (fun h => resetProgram_run _ _ _ read h)
  rw [hfr, List.map_map]
  apply List.map_congr_left
  intro b _
  exact congrArg (InstrumentBranch.mk b.history) (LinearMap.ext fun ψ => by
    change b.kraus (Quantum.run [.X 836] (Quantum.run (Catalyst.prepare 1) ψ)) =
      b.kraus (Quantum.run (Catalyst.prepare 1 ++ [.X 836]) ψ)
    rw [Quantum.run_append])

theorem program26Cat_event_mass (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (accept : Nat → Nat → Bool) :
    Instrument.bornMass ((program26Cat.instantiate (readConstant coefficientAt26 Q) Fin.elim0).run.filter
      (fun b => fineEvent26Cat accept b.history)) (ket zeroBasisState) =
      windowedEventMass Q initialRoot 258 204 accept := by
  rw [program26Cat_run_data, prefix_filter_mass]
  have hs : Quantum.run (Catalyst.prepare 1 ++ [.X 836]) (ket zeroBasisState) =
      LocalFour.Prep 1 (ket initialRoot) := by
    rw [Quantum.run_append, LocalFour.prep_circuit 1 ([.X 836] : Circuit) (by decide)]
    have hx : Quantum.run [.X 836] (ket zeroBasisState) = ket initialRoot := by
      simp [Quantum.run, applyGate_ket, onKet, initialRoot, zeroBasisState]
    rw [hx]
  rw [hs]
  have hY0 : SupportedOn (fun s => s 1 = false) (ket initialRoot) :=
    supportedOn_ket _ _ (by simp [initialRoot, upd, zeroBasisState])
  have hterm : ∀ (lhs rhs : List Bool) (φ : State), SupportedOn (fun s => s 1 = false) φ →
      (if accept (fourierWordLSB lhs.reverse) (fourierWordLSB rhs.reverse) then terminalInstrument else List.nil).bornMass
        (LocalFour.Prep 1 φ) =
      (if accept (fourierWordLSB lhs.reverse) (fourierWordLSB rhs.reverse) then terminalInstrument else List.nil).bornMass φ := by
    intro lhs rhs φ _
    split_ifs
    · rw [terminalInstrument_mass, terminalInstrument_mass, LocalFour.normSq_prep]
    · simp [Instrument.bornMass]
  have hm := CatAxis.selectedTwoAxesCat_mass (leftCatModels26 Q hQ hn) (rightCatModels26 Q hQ hn) 0 Fin.elim0
    (fun lhs rhs => if accept (fourierWordLSB lhs.reverse) (fourierWordLSB rhs.reverse) then terminalInstrument else List.nil)
    (fun lhs rhs => if accept (fourierWordLSB lhs.reverse) (fourierWordLSB rhs.reverse) then terminalInstrument else List.nil)
    hterm (ket initialRoot)
    (by rw [leftCatModels26_model, rightCatModels26_model]; exact ready_all26 Q hQ hn) hY0
  rw [CatAxis.selectedTwoAxesCat_fixed_filter, leftCatModels26_model, rightCatModels26_model] at hm
  dsimp only [leftModels26, rightModels26] at hm
  rw [windowed_idealTwoAxes_event_mass_anyBias Q initialRoot (ket initialRoot)
    (first20Model Q hQ hn) (leftDigits26.map (bodyModel Q hQ hn))
    (rightHeadModel Q hQ hn) (rightTailDigits26.map (bodyModel Q hQ hn))
    (first20Model_rule Q hQ hn) (rightHeadModel_rule Q hQ hn)
    (by
      intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hw; exact bodyModel_rule Q hQ hn d
      · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hw; exact bodyModel_rule Q hQ hn d)
    (leftModels26_weights Q hQ hn) (rightModels26_weights Q hQ hn)
    terminalInstrument terminalInstrument_mass accept] at hm
  change Instrument.bornMass _ _ =
      windowedEventMass Q initialRoot (precision (leftModels26 Q hQ hn)) (precision (rightModels26 Q hQ hn)) accept at hm
  have hpl : precision (leftModels26 Q hQ hn) = 258 := by
    unfold precision
    have hmap : (leftModels26 Q hQ hn).map (fun w => w.physical.wires.length) =
        ((leftModels26 Q hQ hn).map WindowModel.physical).map (fun w => w.wires.length) := by
      rw [List.map_map]; rfl
    rw [hmap, leftModels26_physical]
    simp [leftWins26, leftDigits26, List.ofFn_succ, first20Win, bodyWin,
      First20Signed.bits_length, bank17_length]
  have hpr : precision (rightModels26 Q hQ hn) = 204 := by
    unfold precision
    have hmap : (rightModels26 Q hQ hn).map (fun w => w.physical.wires.length) =
        ((rightModels26 Q hQ hn).map WindowModel.physical).map (fun w => w.wires.length) := by
      rw [List.map_map]; rfl
    rw [hmap, rightModels26_physical]
    simp [rightWins26, rightTailDigits26, List.ofFn_succ, rightHeadWin, bodyWin, bank17_length]
  unfold CatAxis.physicalAxesCat at hm
  rw [leftCatModels26_catPhys, rightCatModels26_catPhys, hpl, hpr] at hm
  have hposL : Single.axisPositions leftWins26Cat 0 = leftPositions26Cat := by
    rw [Single.axisPositions, leftWins26Cat_meta]; rfl
  have hposR : Single.axisPositions rightWins26Cat (axisCount leftWins26Cat) = rightPositions26Cat := by
    rw [Single.axisPositions, rightWins26Cat_meta]; rfl
  rw [hposL, hposR] at hm
  simpa only [fineEvent26Cat, trialPositions26Cat, Vector.toList_mk, List.toList_toArray] using hm

theorem program26Cat_clean (read : ConstantBit 2228224 → Bool) (b : InstrumentBranch)
    (hb : b ∈ (program26Cat.instantiate read Fin.elim0).run) (ψ : State) :
    SupportedOn RoundedReadout.CleanReadout (b.kraus ψ) := by
  rw [program26Cat_run_data] at hb
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
  obtain ⟨a, _, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
  simp only [terminalInstrument, AdaptiveCircuit.run] at hc
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
  have h := resetRegister_clean bodyInst26.reset resourceInst26.reset_nodup e he
    (Quantum.run [.X 836] (a.kraus (Quantum.run (Catalyst.prepare 1 ++ [.X 836]) ψ)))
  intro s hs
  exact ⟨h s hs 0 resourceInst26.reset_zero, h s hs 1 resourceInst26.reset_one⟩

theorem verified_of_reads26Cat (ps : Vector Nat 204) (hps : ps ∈ Readout3.rightWords3 fineBits26Cat)
    (Q : Point) (d : Nat) (hd : Q = d • G) (hist : List Bool) (a b : Nat)
    (hl : readWord hist trialPositions26Cat.left.toList = some a)
    (hr : readWord hist ps.toList = some b)
    (hm : (d : ZMod order) ∈ fixedCandidates params258 a b) :
    (verifiedCandidate rawLayout26Cat Q hist).isSome := by
  classical
  apply List.find?_isSome.mpr
  refine ⟨(d : ZMod order), ?_, ?_⟩
  · unfold candidates
    apply List.mem_flatMap.mpr
    refine ⟨positionsFor26Cat ps, List.mem_map.mpr ⟨ps, hps, rfl⟩, ?_⟩
    simpa only [decodeTrial, trialCandidates, positionsFor26Cat, rawLayout26Cat, hl, hr,
      fixedCandidates_take, Finset.mem_toList] using hm
  · simp only [decide_eq_true_eq, ZMod.val_natCast]
    rw [hd]
    exact nsmul_eq_nsmul_iff_modEq.mpr (by rw [generator_order]; exact Nat.mod_mod _ _)

theorem readout26Cat_wellFormed : readout26Cat.WellFormed := by
  unfold readout26Cat
  rw [castFinish_wellFormed]
  exact Readout3.suffix3_wellFormed _ _ _ _

theorem suffix26Cat_accept (Q : Point) (d : Nat) (hd : Q = d • G)
    (read : ConstantBit 2228224 → Bool) (history : Fin cursor26Cat → Bool)
    (ψ : State) (hψ : SupportedOn RoundedReadout.CleanReadout ψ)
    (hf : fineEvent26Cat (pairRecovered258 d) (List.ofFn history) = true)
    (b : InstrumentBranch) (hb : b ∈ (readout26Cat.instantiate read history).run)
    (hn : b.kraus ψ ≠ 0) :
    (verifiedCandidate rawLayout26Cat Q (List.ofFn history ++ b.history)).isSome := by
  have hr := NeighborReadout.input_read fineBits26Cat history
  rw [fineBits26Cat_vals] at hr
  obtain ⟨a, ha, hp⟩ := Rounded.pairAccept_value _ _ _ _ _ hr hf
  obtain ⟨i, hi⟩ := of_decide_eq_true hp
  obtain ⟨ps, hps, hread⟩ := Readout3.suffix3_reads 2228224 cursor26Cat fineBits26Cat
    read history ψ hψ b (by simpa only [readout26Cat, castFinish_instantiate] using hb) hn
    ((i.val : ℤ) - 1) (by have h := i.isLt; omega)
  apply verified_of_reads26Cat ps hps Q d hd _ a _ _ hread hi
  rw [NeighborReadout.readWord_append_left]
  · exact ha
  · intro j hj
    have h := leftPositions26Cat_bound j hj
    have hh : axisCount leftWins26Cat ≤ cursor26Cat := by unfold cursor26Cat; omega
    simpa only [List.length_ofFn] using h.trans_le hh

theorem strong_success26Cat (Q : Point) (d : Nat) (hn : Q ≠ 0) (hd : Q = d • G) :
    (9911 / 10000 : ℝ) ≤ Instrument.bornMass
      ((rawEntry26Cat.instantiate Q).run.filter (fun b => (verifiedCandidate rawLayout26Cat Q b.history).isSome))
      (ket zeroBasisState) := by
  have hQ : order • Q = 0 := by rw [hd, smul_comm order d, generator_nsmul_eq_zero, nsmul_zero]
  rw [rawEntry26Cat, Single.fixedEntry_instantiate]
  have hneighbor : (9911 / 10000 : ℝ) ≤ Instrument.bornMass
      ((program26Cat.instantiate (readConstant coefficientAt26 Q) Fin.elim0).run.filter
        (fun b => fineEvent26Cat (pairRecovered258 d) b.history)) (ket zeroBasisState) := by
    rw [program26Cat_event_mass Q hQ hn, windowedEventMass_distribution Q d hd initialRoot 258 204]
    exact sine_pair_success Q d hn hd
  apply hneighbor.trans
  unfold fullProgram26Cat
  rw [Single.append_run_history]
  apply Rounded.appended_mass_lower
  · intro a _
    exact AdaptiveCircuit.run_preservesBornMass _
      (readout26Cat.instantiate_wellFormed _ _ readout26Cat_wellFormed) _
  · intro a ha hf b hb hne
    have hlen : a.history.length = cursor26Cat := by
      have h := straight_history_length program26Cat (readConstant coefficientAt26 Q) Fin.elim0 a ha
      simpa only [Nat.zero_add, Nat.sub_zero] using h
    have hh : List.ofFn (Single.historyAfter cursor26Cat Fin.elim0 a.history) = a.history := by
      simpa only [List.ofFn_zero, List.nil_append] using Single.historyAfter_list Fin.elim0 a.history
        (by simpa only [Nat.zero_add] using hlen)
    have h := suffix26Cat_accept Q d hd (readConstant coefficientAt26 Q)
      (Single.historyAfter cursor26Cat Fin.elim0 a.history) (a.kraus (ket zeroBasisState))
      (program26Cat_clean _ a ha _) (by simpa only [hh] using hf) b hb hne
    simpa only [hh, InstrumentBranch.seq] using h

/-! ### Part 4: Static budgets (`wellFormed`, `slots`, `support`, `tCount`, `cost18`, `measurements`) -/

def IsWin26Cat (w : Window 2228224) : Prop :=
  w = first20CatWin ∨ w = rightHeadCatWin ∨ ∃ d, w = bodyCatWin d

theorem bodyCatWin_wellFormed (d : Digit26) (start : Nat) : ((bodyCatWin d).program start).WellFormed := by
  change (castFinish _ (reindexStraight _ (relabelStraight _ (LocalWide16.compiledProgram start)))).WellFormed
  rw [castFinish_wellFormed]
  exact (reindexStraight_wellFormed _ _).mpr ((relabelStraight_wellFormed _ _).mpr (LocalWide16.compiled_wellFormed start))

theorem bodyCatWin_support (d : Digit26) (start : Nat) :
    straightWires ((bodyCatWin d).program start) ⊆ List.range 1613 := by
  change straightWires (castFinish _ (reindexStraight _ (relabelStraight _ (LocalWide16.compiledProgram start)))) ⊆ _
  rw [straightWires_castFinish, straightWires_reindex]
  exact LocalWide16.compiled_packed_support start

theorem bodyCatWin_slots (d : Digit26) (start : Nat) : ((bodyCatWin d).program start).gateSlots ≤ 80000000000 := by
  change (castFinish _ (reindexStraight _ (relabelStraight _ (LocalWide16.compiledProgram start)))).gateSlots ≤ _
  rw [castFinish_gateSlots, reindexStraight_gateSlots, relabelStraight_slots]
  exact LocalWide16.compiled_slots start

theorem bodyCatWin_tCount (d : Digit26) (start : Nat) (read : ConstantBit 2228224 → Bool) (h : Fin start → Bool) :
    (((bodyCatWin d).program start).instantiate read h).tCount ≤ 4 * 2303094 := by
  change ((castFinish _ (reindexStraight _ (relabelStraight _ (LocalWide16.compiledProgram start)))).instantiate read h).tCount ≤ _
  rw [castFinish_instantiate, reindexStraight_instantiate, relabelStraight_instantiate, AdaptiveCircuit.relabel_tCount]
  exact LocalWide16.compiled_tCount start _ h

theorem bodyCatWin_cost18 (d : Digit26) (start : Nat) : cost18 ((bodyCatWin d).program start) = 0 := by
  apply CatAxis.cost18_zero_of_removed18
  change removed 18 (castFinish _ (reindexStraight _ (relabelStraight _ (LocalWide16.compiledProgram start)))) = 0
  rw [LocalFour.removed_castFinish, removed18_reindex]
  have hrel : ∀ {n s e} (f : Wire ≃ Wire) (p : Straight n s e), removed 18 (relabelStraight f p) = removed 18 p := by
    intro n s e f p
    induction p with
    | done => rfl
    | measure w p ih => exact ih
    | recordGate i v g p ih => cases g <;> simp [relabelStraight, Gate.relabel, removed, largePhase, ih]
    | gate g p ih =>
      cases g with
      | literal g => cases g <;> simp [relabelStraight, relabelTemplateGate, Gate.relabel, removed, largePhase, ih]
      | whenBit r v g => cases g <;> simp [relabelStraight, relabelTemplateGate, Gate.relabel, removed, largePhase, ih]
  rw [hrel]
  exact LocalWide16.compiled_removed18 start

theorem first20CatWin_wellFormed (start : Nat) : (first20CatWin.program start).WellFormed := by
  apply straight_append_wellFormed
  · apply ConditionalCatalyst.compile_wellFormed 1 _ _
      (literalProgram_wellFormed _ (sineFromPlus_wellFormed top10Left top10Left_length top10Left_nodup))
    apply LocalFour.fresh_of_not_mem_straightWires
    intro hm
    exact wire01_not_first20Bits.2 (top10Left_sub_bits (sineFromPlus_wires top10Left top10Left_length
      (literalProgram_straightWires _ hm)))
  · rw [castFinish_wellFormed]
    have hsub := First20Signed.window_support_drop01 firstRow26 0
    have hf0 : Fresh 0 (first20RawWin.program 0) :=
      LocalFour.fresh_of_not_mem_straightWires _ _ (fun hm => by
        have := hsub hm; simp only [List.mem_range'_1] at this; omega)
    have hf1 : Fresh 1 (first20RawWin.program 0) :=
      LocalFour.fresh_of_not_mem_straightWires _ _ (fun hm => by
        have := hsub hm; simp only [List.mem_range'_1] at this; omega)
    exact LocalFour.compileLower_wellFormed 0 1 (first20RawWin.program 0) start Fin.elim0 hf0 hf1 (by decide)
      (First20Signed.window_wellFormed firstRow26 0)

theorem first20CatWin_slots (start : Nat) : (first20CatWin.program start).gateSlots ≤ 60000000000 := by
  change ((ConditionalCatalyst.compile 1 (literalProgram (sineFromPlus top10Left))).append _).gateSlots ≤ _
  rw [Straight.gateSlots_append, castFinish_gateSlots]
  have hs1 := ConditionalCatalyst.compile_slots 1 (literalProgram (n := 2228224) (s := start) (sineFromPlus top10Left))
  have hs2 := ConditionalCatalyst.phaseTwos_le_slots (literalProgram (n := 2228224) (s := start) (sineFromPlus top10Left))
  have hs3 : (literalProgram (n := 2228224) (s := start) (sineFromPlus top10Left)).gateSlots = 52 := by
    rw [ChallengeMigration.literalProgram_slots, sineFromPlus_length top10Left top10Left_length]
  have hl1 := LocalFour.compileLower_slots 0 1 (first20RawWin.program 0) start Fin.elim0
  have hl2 : (first20RawWin.program 0).gateSlots ≤ 13100000000 := First20Signed.window_slots firstRow26 0
  have hl3 : AndGadget.added (first20RawWin.program 0) ≤ 193625 := by
    unfold first20RawWin First20Signed.windowGeneric; rw [added_reindex]; exact First20Signed.program_added 0
  omega

theorem sineFromPlus_weight7_eq_weight4 {n s : Nat} (ws : List Wire) :
    ConditionalCatalyst.weight7 (literalProgram (n := n) (s := s) (sineFromPlus ws)) =
      ConditionalCatalyst.weight4 (literalProgram (n := n) (s := s) (sineFromPlus ws)) := by
  have hno : ∀ c ts k, ∀ x ∈ SineCircuit.cPhaseLoop c ts k, ∀ a b t, x ≠ .CCX a b t := by
    intro c ts
    induction ts with
    | nil => intro _ _ hx; cases hx
    | cons u us ih =>
      intro k x hx a b t
      simp only [SineCircuit.cPhaseLoop, SineCircuit.cPhaseBlock, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with (rfl | rfl | rfl | rfl) | hx
      · intro h; cases h
      · intro h; cases h
      · intro h; cases h
      · intro h; cases h
      · exact ih (k - 1) x hx a b t
  have hno2 : ∀ ts k, ∀ x ∈ SineCircuit.centerLoop ts k, ∀ a b t, x ≠ .CCX a b t := by
    intro ts
    induction ts with
    | nil => intro _ _ hx; cases hx
    | cons u us ih =>
      intro k x hx a b t
      simp only [SineCircuit.centerLoop, List.mem_cons] at hx
      rcases hx with rfl | hx
      · intro h; cases h
      · exact ih (k - 1) x hx a b t
  have hnoCCX : ∀ g ∈ sineFromPlus ws, ∀ a b t, g ≠ .CCX a b t := by
    intro g hg a b t
    simp only [SineCircuit.sineFromPlus, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with ((((rfl | rfl | rfl | rfl | rfl) | hx) | rfl) | hx)
    · intro h; cases h
    · intro h; cases h
    · intro h; cases h
    · intro h; cases h
    · intro h; cases h
    · exact hno _ _ 11 g hx a b t
    · intro h; cases h
    · exact hno2 _ 11 g hx a b t
  have hgen : ∀ (cs : Circuit), (∀ g ∈ cs, ∀ a b t, g ≠ .CCX a b t) →
      ConditionalCatalyst.weight7 (literalProgram (n := n) (s := s) cs) =
        ConditionalCatalyst.weight4 (literalProgram (n := n) (s := s) cs) := by
    intro cs hcs
    induction cs with
    | nil => rfl
    | cons g gs ih =>
      have hgw : ConditionalCatalyst.weightedGate g = ConditionalCatalyst.weightedLiteral g := by
        cases g with
        | CCX a b t => exact absurd rfl (hcs _ List.mem_cons_self a b t)
        | _ => rfl
      change ConditionalCatalyst.weightedGate g + ConditionalCatalyst.weight7 (literalProgram gs) =
        ConditionalCatalyst.weightedLiteral g + ConditionalCatalyst.weight4 (literalProgram gs)
      rw [hgw, ih (fun x hx => hcs x (List.mem_cons_of_mem _ hx))]
  exact hgen _ hnoCCX

theorem first20CatWin_tCount (start : Nat) (read : ConstantBit 2228224 → Bool) (h : Fin start → Bool) :
    ((first20CatWin.program start).instantiate read h).tCount ≤ 4 * 193625 + 28 := by
  change (((ConditionalCatalyst.compile 1 (literalProgram (sineFromPlus top10Left))).append
    (castFinish (first20Cat_finish_eq start)
      (LocalFour.compileLower 0 1 (first20RawWin.program 0) start Fin.elim0).program)).instantiate read h).tCount ≤ _
  have h1 := CatAxis.append_tCount_le
    (ConditionalCatalyst.compile 1 (literalProgram (n := 2228224) (s := start) (sineFromPlus top10Left)))
    (castFinish (first20Cat_finish_eq start)
      (LocalFour.compileLower 0 1 (first20RawWin.program 0) start Fin.elim0).program)
    read h (4 * 193625) (fun h' => by
      rw [castFinish_instantiate]
      have hlo := LocalFour.compileLower_tCount 0 1 (first20RawWin.program 0) start Fin.elim0 read h'
      have hz : residue (first20RawWin.program 0) = 0 := First20Signed.window_residue firstRow26 0
      have ha : added (first20RawWin.program 0) ≤ 193625 := by
        unfold first20RawWin First20Signed.windowGeneric; rw [added_reindex]; exact First20Signed.program_added 0
      rw [weight4_zero _ hz] at hlo
      omega)
  have hsine_t : ((ConditionalCatalyst.compile 1 (literalProgram (n := 2228224) (s := start)
      (sineFromPlus top10Left))).instantiate read h).tCount ≤ 28 := by
    have ht := ConditionalCatalyst.compile_t 1
      (literalProgram (n := 2228224) (s := start) (sineFromPlus top10Left)) read h
    rw [sineFromPlus_weight7_eq_weight4, sineFromPlus_weight4 top10Left top10Left_length] at ht
    exact ht
  omega

theorem rightHeadCatWin_wellFormed (start : Nat) : (rightHeadCatWin.program start).WellFormed := by
  apply straight_append_wellFormed
  · apply ConditionalCatalyst.compile_wellFormed 1 _ _
      (literalProgram_wellFormed _ (sineFromPlus_wellFormed top10Right top10Right_length top10Right_nodup))
    apply LocalFour.fresh_of_not_mem_straightWires
    intro hm
    exact wire1_not_bank17 (top10Right_sub_bank (sineFromPlus_wires top10Right top10Right_length
      (literalProgram_straightWires _ hm)))
  · exact bodyCatWin_wellFormed rightHeadDigit start

theorem rightHeadCatWin_slots (start : Nat) : (rightHeadCatWin.program start).gateSlots ≤ 80000000400 := by
  change ((ConditionalCatalyst.compile 1 (literalProgram (sineFromPlus top10Right))).append
    ((bodyCatWin rightHeadDigit).program start)).gateSlots ≤ _
  rw [Straight.gateSlots_append]
  have hs : (ConditionalCatalyst.compile 1 (literalProgram (n := 2228224) (s := start) (sineFromPlus top10Right))).gateSlots ≤ 400 := by
    have hs1 := ConditionalCatalyst.compile_slots 1 (literalProgram (n := 2228224) (s := start) (sineFromPlus top10Right))
    have hs2 := ConditionalCatalyst.phaseTwos_le_slots (literalProgram (n := 2228224) (s := start) (sineFromPlus top10Right))
    have hs3 : (literalProgram (n := 2228224) (s := start) (sineFromPlus top10Right)).gateSlots = 52 := by
      rw [ChallengeMigration.literalProgram_slots, sineFromPlus_length top10Right top10Right_length]
    omega
  exact (Nat.add_le_add hs (bodyCatWin_slots rightHeadDigit start)).trans (by decide)

theorem rightHeadCatWin_tCount (start : Nat) (read : ConstantBit 2228224 → Bool) (h : Fin start → Bool) :
    ((rightHeadCatWin.program start).instantiate read h).tCount ≤ 4 * 2303094 + 28 := by
  change (((ConditionalCatalyst.compile 1 (literalProgram (sineFromPlus top10Right))).append
    ((bodyCatWin rightHeadDigit).program start)).instantiate read h).tCount ≤ _
  have h1 := CatAxis.append_tCount_le
    (ConditionalCatalyst.compile 1 (literalProgram (n := 2228224) (s := start) (sineFromPlus top10Right)))
    ((bodyCatWin rightHeadDigit).program start) read h (4 * 2303094)
    (fun h' => bodyCatWin_tCount rightHeadDigit start read h')
  have hsine_t : ((ConditionalCatalyst.compile 1 (literalProgram (n := 2228224) (s := start)
      (sineFromPlus top10Right))).instantiate read h).tCount ≤ 28 := by
    have ht := ConditionalCatalyst.compile_t 1
      (literalProgram (n := 2228224) (s := start) (sineFromPlus top10Right)) read h
    rw [sineFromPlus_weight7_eq_weight4, sineFromPlus_weight4 top10Right top10Right_length] at ht
    exact ht
  exact h1.trans (Nat.add_le_add_right hsine_t _ |>.trans (by decide))

theorem win26Cat_wellFormed (w : Window 2228224) (hw : IsWin26Cat w) (start : Nat) :
    (w.program start).WellFormed := by
  rcases hw with rfl | rfl | ⟨d, rfl⟩
  · exact first20CatWin_wellFormed start
  · exact rightHeadCatWin_wellFormed start
  · exact bodyCatWin_wellFormed d start

theorem win26Cat_bank_support (w : Window 2228224) (hw : IsWin26Cat w) : w.wires ⊆ List.range 1613 := by
  rcases hw with rfl | rfl | ⟨d, rfl⟩
  · intro v hv; exact First20Signed.bits_subset_range (List.mem_reverse.mp hv)
  · intro v hv; exact bank17_sub_range (List.mem_reverse.mp hv)
  · intro v hv; exact bank17_sub_range (List.mem_reverse.mp hv)

theorem win26Cat_noY (w : Window 2228224) (hw : IsWin26Cat w) : (1 : Wire) ∉ w.wires := by
  rcases hw with rfl | rfl | ⟨d, rfl⟩
  · exact fun hm => wire01_not_first20Bits.2 (List.mem_reverse.mp hm)
  · exact fun hm => wire1_not_bank17 (List.mem_reverse.mp hm)
  · exact fun hm => wire1_not_bank17 (List.mem_reverse.mp hm)

theorem win26Cat_support (w : Window 2228224) (hw : IsWin26Cat w) (start : Nat)
    (read : ConstantBit 2228224 → Bool) (history : Fin start → Bool) :
    ((w.program start).instantiate read history).wires ⊆ List.range 1613 := by
  rcases hw with rfl | rfl | ⟨d, rfl⟩
  · apply outer_append_support _ _ read history (List.range 1613)
    · have hw1 : Within (List.range 1613)
          (literalProgram (n := 2228224) (s := start) (sineFromPlus top10Left)) :=
        LocalFour.within_of_straightWires _ _
          ((literalProgram_straightWires _).trans
            ((sineFromPlus_wires top10Left top10Left_length).trans top10Left_sub_range))
      have hsup := (ConditionalCatalyst.compile_within 1 _ _ hw1).instantiate read history
      intro u hu
      rcases List.mem_cons.mp (hsup hu) with rfl | hm
      · exact List.mem_range.mpr (by decide)
      · exact hm
    · intro h'
      rw [castFinish_instantiate]
      refine (straight_instantiate_support _ read h').trans ?_
      exact LocalFour.compileLower_straightWires 0 1 (first20RawWin.program 0) (List.range 1613)
        (First20Signed.window_support firstRow26 0)
        (List.mem_range.mpr (by decide)) (List.mem_range.mpr (by decide)) start Fin.elim0
  · apply outer_append_support _ _ read history (List.range 1613)
    · have hw1 : Within (List.range 1613)
          (literalProgram (n := 2228224) (s := start) (sineFromPlus top10Right)) :=
        LocalFour.within_of_straightWires _ _
          ((literalProgram_straightWires _).trans
            ((sineFromPlus_wires top10Right top10Right_length).trans top10Right_sub_range))
      have hsup := (ConditionalCatalyst.compile_within 1 _ _ hw1).instantiate read history
      intro u hu
      rcases List.mem_cons.mp (hsup hu) with rfl | hm
      · exact List.mem_range.mpr (by decide)
      · exact hm
    · intro h'
      exact (straight_instantiate_support _ read h').trans (bodyCatWin_support rightHeadDigit start)
  · exact (straight_instantiate_support _ read history).trans (bodyCatWin_support d start)

theorem win26Cat_cost18 (w : Window 2228224) (hw : IsWin26Cat w) (start : Nat) :
    cost18 (w.program start) = 0 := by
  rcases hw with rfl | rfl | ⟨d, rfl⟩
  · change cost18 ((ConditionalCatalyst.compile 1 (literalProgram (sineFromPlus top10Left))).append _) = 0
    rw [cost18_append, CatAxis.cost18_compile,
      cost18_literal_zero _ (sineFromPlus_largePhase_false top10Left 18 (by decide)), zero_add, cost18_cast]
    apply CatAxis.cost18_zero_of_removed18
    rw [LocalFour.compileLower_removed18]
    exact LocalFour.removed18_zero_of_residue _ (First20Signed.window_residue firstRow26 0)
  · change cost18 ((ConditionalCatalyst.compile 1 (literalProgram (sineFromPlus top10Right))).append _) = 0
    rw [cost18_append, CatAxis.cost18_compile,
      cost18_literal_zero _ (sineFromPlus_largePhase_false top10Right 18 (by decide)), zero_add]
    exact bodyCatWin_cost18 rightHeadDigit start
  · exact bodyCatWin_cost18 d start

theorem full26Cat_wellFormed : fullProgram26Cat.WellFormed := by
  apply straight_append_wellFormed _ _ _ readout26Cat_wellFormed
  unfold program26Cat
  apply Catalyst.literals_wellFormed _ _ (LocalFour.prepare_wellFormed 1)
  apply framed_wellFormed
  · exact CatAxis.axisCat_wellFormed 1 leftWins26Cat
      (fun w hw => by
        rcases List.mem_cons.mp hw with rfl | hw
        · exact win26Cat_noY _ (Or.inl rfl)
        · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hw
          exact win26Cat_noY _ (Or.inr (Or.inr ⟨d, rfl⟩)))
      (fun w hw start => by
        rcases List.mem_cons.mp hw with rfl | hw
        · exact win26Cat_wellFormed _ (Or.inl rfl) start
        · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hw
          exact win26Cat_wellFormed _ (Or.inr (Or.inr ⟨d, rfl⟩)) start) _ _
  · exact CatAxis.axisCat_wellFormed 1 rightWins26Cat
      (fun w hw => by
        rcases List.mem_cons.mp hw with rfl | hw
        · exact win26Cat_noY _ (Or.inr (Or.inl rfl))
        · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hw
          exact win26Cat_noY _ (Or.inr (Or.inr ⟨d, rfl⟩)))
      (fun w hw start => by
        rcases List.mem_cons.mp hw with rfl | hw
        · exact win26Cat_wellFormed _ (Or.inr (Or.inl rfl)) start
        · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hw
          exact win26Cat_wellFormed _ (Or.inr (Or.inr ⟨d, rfl⟩)) start) _ _
  · exact resetProgram_wellFormed _ _ _

theorem full26Cat_slots : fullProgram26Cat.gateSlots ≤ 10000000000000 := by
  have hL := CatAxis.axisCat_slots 1 leftWins26Cat 80000000400
    (fun w hw start => by
      rcases List.mem_cons.mp hw with rfl | hw
      · exact (first20CatWin_slots start).trans (by decide)
      · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hw
        exact (bodyCatWin_slots d start).trans (by decide))
    0 List.nil
  have hR := CatAxis.axisCat_slots 1 rightWins26Cat 80000000400
    (fun w hw start => by
      rcases List.mem_cons.mp hw with rfl | hw
      · exact rightHeadCatWin_slots start
      · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hw
        exact (bodyCatWin_slots d start).trans (by decide))
    (0 + axisCount leftWins26Cat) List.nil
  rw [leftWins26Cat_meta, List.length_nil] at hL
  rw [rightWins26Cat_meta, List.length_nil] at hR
  have hLnum : metadataSlots 80000000400 leftMeta26Cat 0 ≤ 1300000000000 := by
    simp only [leftMeta26Cat, List.replicate, metadataSlots, fourierSlots]
    omega
  have hRnum : metadataSlots 80000000400 rightMeta26Cat 0 ≤ 1000000000000 := by
    simp only [rightMeta26Cat, List.replicate, metadataSlots, fourierSlots]
    omega
  have hro : readout26Cat.gateSlots = 5719 := by
    unfold readout26Cat
    rw [castFinish_gateSlots, Readout3.suffix3_slots]
  unfold fullProgram26Cat program26Cat
  rw [Straight.gateSlots_append, AndGadget.literals_slots, framed_slots, resetProgram_gateSlots, hro]
  have hres : resetWires.length ≤ 2000 := by decide +kernel
  have hprep : (Catalyst.prepare 1).length = 2 := rfl
  omega

theorem full26Cat_support (read : ConstantBit 2228224 → Bool) (history : Fin 0 → Bool) :
    (fullProgram26Cat.instantiate read history).wires ⊆ List.range 1613 := by
  apply outer_append_support _ _ read history (List.range 1613)
  · unfold program26Cat
    have hcur : 0 + axisCount leftWins26Cat + axisCount rightWins26Cat + resetWires.length = cursor26Cat := by
      unfold cursor26Cat; omega
    have hlit : Within (List.range 1613)
        (AndGadget.literals (Catalyst.prepare 1)
          (Single.framed
            (CatAxis.axisCat 1 leftWins26Cat 0 List.nil)
            (CatAxis.axisCat 1 rightWins26Cat (0 + axisCount leftWins26Cat) List.nil)
            (resetProgram 2228224 (0 + axisCount leftWins26Cat + axisCount rightWins26Cat) resetWires)
            hcur)) := by
      apply Catalyst.literals_within
      · intro u hu
        simp only [Catalyst.prepare, circuitWires, gateWires, List.flatMap_cons, List.flatMap_nil,
          List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl <;> exact List.mem_range.mpr (by decide)
      · apply within_of_instantiate
        intro r h0
        refine framed_support _ _ _ _ r h0 (List.range 1613) (by decide) ?_ ?_ ?_
        · exact CatAxis.axisCat_support 1 leftWins26Cat (List.range 1613)
            (List.mem_range.mpr (by decide))
            (fun w hw => by
              rcases List.mem_cons.mp hw with rfl | hw
              · exact win26Cat_bank_support _ (Or.inl rfl)
              · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hw
                exact win26Cat_bank_support _ (Or.inr (Or.inr ⟨d, rfl⟩)))
            (fun w hw start r' h' => by
              rcases List.mem_cons.mp hw with rfl | hw
              · exact win26Cat_support _ (Or.inl rfl) start r' h'
              · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hw
                exact win26Cat_support _ (Or.inr (Or.inr ⟨d, rfl⟩)) start r' h')
            0 List.nil r h0
        · intro h1
          exact CatAxis.axisCat_support 1 rightWins26Cat (List.range 1613)
            (List.mem_range.mpr (by decide))
            (fun w hw => by
              rcases List.mem_cons.mp hw with rfl | hw
              · exact win26Cat_bank_support _ (Or.inr (Or.inl rfl))
              · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hw
                exact win26Cat_bank_support _ (Or.inr (Or.inr ⟨d, rfl⟩)))
            (fun w hw start r' h' => by
              rcases List.mem_cons.mp hw with rfl | hw
              · exact win26Cat_support _ (Or.inr (Or.inl rfl)) start r' h'
              · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hw
                exact win26Cat_support _ (Or.inr (Or.inr ⟨d, rfl⟩)) start r' h')
            (0 + axisCount leftWins26Cat) List.nil r h1
        · intro h2
          exact resetProgram_support _ _ _ _ r h2 Width16Actual.reset_range
    exact hlit.instantiate read history
  · intro h
    unfold readout26Cat
    rw [castFinish_instantiate]
    exact (Readout3.suffix3_support _ _ _ _ read h).trans (by decide)

theorem source26Cat_within : Within (List.range 1613) rawEntry26Cat.program := by
  unfold rawEntry26Cat Single.fixedEntry
  dsimp only
  exact Width16Actual.within_reindex fullProgram26Cat _ (List.range 1613)
    (within_of_instantiate fullProgram26Cat (List.range 1613) full26Cat_support)

def leftTCountMeta26Cat : List (Nat × Nat) :=
  (4 * 193625 + 28, 20) :: List.replicate 14 (4 * 2303094, 17)

def rightTCountMeta26Cat : List (Nat × Nat) :=
  (4 * 2303094 + 28, 17) :: List.replicate 11 (4 * 2303094, 17)

theorem exact_trimmed_tCount26Cat :
    CatAxis.metadataTrimmedWeight leftTCountMeta26Cat 0 +
      CatAxis.metadataTrimmedWeight rightTCountMeta26Cat 0 = 240303420 := by
  decide +kernel

theorem left26Cat_tCount_relation :
    List.Forall₂ (fun w k => w.wires.length = k.2 ∧
        ∀ start read h, ((w.program start).instantiate read h).tCount ≤ k.1)
      leftWins26Cat leftTCountMeta26Cat := by
  refine .cons ⟨by simp [first20CatWin, First20Signed.bits_length], first20CatWin_tCount⟩ ?_
  have hmap : List.replicate 14 (4 * 2303094, 17) = leftDigits26.map (fun _ => (4 * 2303094, 17)) := by
    simp [leftDigits26, List.ofFn_succ, List.replicate]
  rw [hmap]
  induction leftDigits26 with
  | nil => exact .nil
  | cons d ds ih =>
    exact .cons ⟨by simp [bodyCatWin, bank17_length], bodyCatWin_tCount d⟩ ih

theorem right26Cat_tCount_relation :
    List.Forall₂ (fun w k => w.wires.length = k.2 ∧
        ∀ start read h, ((w.program start).instantiate read h).tCount ≤ k.1)
      rightWins26Cat rightTCountMeta26Cat := by
  refine .cons ⟨by simp [rightHeadCatWin, bank17_length], rightHeadCatWin_tCount⟩ ?_
  have hmap : List.replicate 11 (4 * 2303094, 17) = rightTailDigits26.map (fun _ => (4 * 2303094, 17)) := by
    simp [rightTailDigits26, List.ofFn_succ, List.replicate]
  rw [hmap]
  induction rightTailDigits26 with
  | nil => exact .nil
  | cons d ds ih =>
    exact .cons ⟨by simp [bodyCatWin, bank17_length], bodyCatWin_tCount d⟩ ih

theorem full26Cat_trim18_tCount (read : ConstantBit 2228224 → Bool) (h : Fin 0 → Bool) :
    ((trim 18 fullProgram26Cat).instantiate read h).tCount ≤ 240303421 := by
  unfold fullProgram26Cat program26Cat
  have hprep_nf : ∀ g ∈ Catalyst.prepare 1, largePhase 18 g = false := by decide
  rw [CatAxis.trim18_append, CatAxis.trim18_literals_false _ _ hprep_nf]
  have hcur : 0 + axisCount leftWins26Cat + axisCount rightWins26Cat + resetWires.length = cursor26Cat := by
    unfold cursor26Cat; omega
  have hro_t : ∀ h' : Fin cursor26Cat → Bool, ((trim 18 readout26Cat).instantiate read h').tCount ≤ 0 := by
    intro h'
    have h1 := trim18_t readout26Cat read h'
    have h2 : (readout26Cat.instantiate read h').tCount = 0 := by
      unfold readout26Cat; rw [castFinish_instantiate]; exact Readout3.suffix3_t _ _ _ _ read h'
    omega
  have h1 := CatAxis.append_tCount_le
    (AndGadget.literals (Catalyst.prepare 1)
      (trim 18 (Single.framed
        (CatAxis.axisCat 1 leftWins26Cat 0 List.nil)
        (CatAxis.axisCat 1 rightWins26Cat (0 + axisCount leftWins26Cat) List.nil)
        (resetProgram 2228224 (0 + axisCount leftWins26Cat + axisCount rightWins26Cat) resetWires)
        hcur)))
    (trim 18 readout26Cat) read h 0 hro_t
  rw [Catalyst.literals_t] at h1
  have hprep_t : ShorECDLP.tCount (Catalyst.prepare 1) = 1 := by decide
  rw [hprep_t] at h1
  have hframed_t : ((trim 18 (Single.framed
      (CatAxis.axisCat 1 leftWins26Cat 0 List.nil)
      (CatAxis.axisCat 1 rightWins26Cat (0 + axisCount leftWins26Cat) List.nil)
      (resetProgram 2228224 (0 + axisCount leftWins26Cat + axisCount rightWins26Cat) resetWires)
      hcur)).instantiate read h).tCount ≤ 240303420 := by
    unfold Single.framed
    simp only [trim, largePhase, Bool.false_eq_true, ↓reduceIte, Straight.instantiate,
      TemplateGate.instantiate, AdaptiveCircuit.tCount, ShorECDLP.tCount, tCost,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.zero_add,
      CatAxis.trim18_castFinish, castFinish_instantiate, CatAxis.trim18_append]
    have hres_t : ∀ h' : Fin (0 + axisCount leftWins26Cat + axisCount rightWins26Cat) → Bool,
        ((Straight.gate (.literal (.X 836))
          (trim 18 (resetProgram 2228224 (0 + axisCount leftWins26Cat + axisCount rightWins26Cat) resetWires))).instantiate read h').tCount ≤ 0 := by
      intro h'
      simp only [Straight.instantiate, TemplateGate.instantiate, AdaptiveCircuit.tCount,
        ShorECDLP.tCount, tCost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.zero_add]
      have hrt : ∀ (n start : Nat) (ws : List Wire) (r : ConstantBit n → Bool) (hist : Fin start → Bool),
          ((resetProgram n start ws).instantiate r hist).tCount = 0 := by
        intro n start ws r
        induction ws generalizing start with
        | nil => intro hist; simp [resetProgram, Straight.instantiate, AdaptiveCircuit.tCount]
        | cons w ws ih =>
          intro hist
          simp only [resetProgram, castFinish_instantiate, Straight.instantiate, AdaptiveCircuit.tCount,
            ShorECDLP.tCount, tCost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
            Nat.zero_add, ih, max_self]
      have hle := trim18_t (resetProgram 2228224 (0 + axisCount leftWins26Cat + axisCount rightWins26Cat) resetWires) read h'
      rw [hrt] at hle
      exact hle
    have hR_t : ∀ h' : Fin (0 + axisCount leftWins26Cat) → Bool,
        (((trim 18 (CatAxis.axisCat 1 rightWins26Cat (0 + axisCount leftWins26Cat) List.nil)).append
          (Straight.gate (.literal (.X 836))
            (trim 18 (resetProgram 2228224 (0 + axisCount leftWins26Cat + axisCount rightWins26Cat) resetWires)))).instantiate read h').tCount ≤
          CatAxis.metadataTrimmedWeight rightTCountMeta26Cat 0 := by
      intro h'
      have ha := CatAxis.append_tCount_le
        (trim 18 (CatAxis.axisCat 1 rightWins26Cat (0 + axisCount leftWins26Cat) List.nil))
        _ read h' 0 hres_t
      have hax := CatAxis.axisCat_tCount_trim18 1 rightWins26Cat rightTCountMeta26Cat
        right26Cat_tCount_relation (0 + axisCount leftWins26Cat) List.nil read h'
      rw [List.length_nil] at hax
      omega
    have hL := CatAxis.append_tCount_le
      (trim 18 (CatAxis.axisCat 1 leftWins26Cat 0 List.nil))
      _ read h _ hR_t
    have hLax := CatAxis.axisCat_tCount_trim18 1 leftWins26Cat leftTCountMeta26Cat
      left26Cat_tCount_relation 0 List.nil read h
    rw [List.length_nil] at hLax
    have hex := exact_trimmed_tCount26Cat
    omega
  omega

theorem source26Cat_cost18 : cost18 rawEntry26Cat.program ≤ 51 / 10000 := by
  have hL := CatAxis.axisCat_cost18_exact 1 leftWins26Cat
    (fun w hw start => by
      rcases List.mem_cons.mp hw with rfl | hw
      · exact win26Cat_cost18 _ (Or.inl rfl) start
      · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hw
        exact win26Cat_cost18 _ (Or.inr (Or.inr ⟨d, rfl⟩)) start) 0 List.nil
  have hR := CatAxis.axisCat_cost18_exact 1 rightWins26Cat
    (fun w hw start => by
      rcases List.mem_cons.mp hw with rfl | hw
      · exact win26Cat_cost18 _ (Or.inr (Or.inl rfl)) start
      · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hw
        exact win26Cat_cost18 _ (Or.inr (Or.inr ⟨d, rfl⟩)) start) (0 + axisCount leftWins26Cat) List.nil
  have hlw : (leftWins26Cat.map (fun w => w.wires.length)).sum = 258 := by
    have h := congrArg (fun l => (l.map Prod.snd).sum) leftWins26Cat_meta
    simp only [List.map_map, Function.comp_def] at h
    rw [h]; simp only [leftMeta26Cat, List.replicate, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; rfl
  have hrw : (rightWins26Cat.map (fun w => w.wires.length)).sum = 204 := by
    have h := congrArg (fun l => (l.map Prod.snd).sum) rightWins26Cat_meta
    simp only [List.map_map, Function.comp_def] at h
    rw [h]; simp only [rightMeta26Cat, List.replicate, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; rfl
  rw [hlw, List.length_nil] at hL
  rw [hrw, List.length_nil] at hR
  have hreset : cost18 (resetProgram 2228224 (0 + axisCount leftWins26Cat + axisCount rightWins26Cat) resetWires) = 0 := by
    apply cost18_zero_of_residue
    have hz : ∀ (n start : Nat) (ws : List Wire), residue (resetProgram n start ws) = 0 := by
      intro n start ws; induction ws generalizing start with
      | nil => simp [resetProgram, residue]
      | cons w ws ih => simpa [resetProgram, residue_cast, residue] using ih (start + 1)
    exact hz _ _ _
  have hro : cost18 readout26Cat = 0 := by
    apply cost18_zero_of_residue
    simp only [readout26Cat, residue_cast, Readout3.residue_suffix3]
  unfold rawEntry26Cat Single.fixedEntry
  dsimp only
  rw [cost18_reindex]
  simp only [fullProgram26Cat, cost18_append, program26Cat]
  rw [CatAxis.cost18_literals _ _ (by decide)]
  simp only [Single.framed, cost18_cast, cost18_append, cost18, charge18, zero_add, add_zero, hreset, hro, hL, hR]
  exact joint_error18

theorem source26Cat_cursor_le : rawEntry26Cat.finalCursor ≤ 105000000 := by
  have hfc : rawEntry26Cat.finalCursor = cursor26Cat + 1634 := by
    unfold rawEntry26Cat; rw [Single.fixedEntry_cursor]
  have h1 := first20Cat_count_le
  have h2 := cBody16_le
  have hL := leftWins26Cat_count_eq
  have hR := rightWins26Cat_count_eq
  have hres : resetWires.length ≤ 2000 := by decide +kernel
  unfold cursor26Cat at hfc
  omega

/-! ### Part 5: Raw certificate, `trim 18`, specialization, and final `1,613 × 240,303,421` certificate -/

section Cert26
attribute [local irreducible] rawEntry26Cat fullProgram26Cat program26Cat readout26Cat

def rawBounds26Cat : Bounds := ⟨1613, 70000000000000, 105000000⟩

theorem raw_certificate26Cat : Certificate rawLimits26 rawLayout26Cat rawEntry26Cat rawBounds26Cat where
  gateBudget := by
    rw [rawEntry26Cat, Single.fixedEntry_slots]
    exact full26Cat_slots.trans (by unfold rawLimits26 officialLimits; dsimp only; omega)
  recordBudget := source26Cat_cursor_le.trans (by unfold rawLimits26 officialLimits; dsimp only; omega)
  tableBudget := by rw [rawEntry26Cat, Single.fixedEntry_rows]; unfold rawLimits26; exact le_rfl
  candidateBudget := by
    change rawLayout26Cat.trials.length * (2 * (order / 2 ^ 204 + 2)) ≤ 56 * (2 ^ 49 + 2)
    have hl : rawLayout26Cat.trials.length = 3 := by
      simp only [rawLayout26Cat, List.length_map, Readout3.rightWords3_length]
    rw [hl]
    exact decoder_budget258
  wellFormed := by rw [rawEntry26Cat, Single.fixedEntry_wellFormed]; exact full26Cat_wellFormed
  resources := by
    intro Q
    have hs := source26Cat_within.instantiate (readConstant rawEntry26Cat.coefficients.get Q) Fin.elim0
    have hq : (rawEntry26Cat.instantiate Q).qubitCount ≤ 1613 := by
      have ht : (rawEntry26Cat.instantiate Q).wires.dedup.toFinset ⊆ (List.range 1613).toFinset := by
        intro v hv
        exact List.mem_toFinset.mpr (hs (by simpa only [List.mem_toFinset, List.mem_dedup] using hv))
      have hc := (Finset.card_le_card ht).trans (List.toFinset_card_le _)
      rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
      simpa only [AdaptiveCircuit.qubitCount, List.length_range] using hc
    refine ⟨hq, ?_, ?_⟩
    · have ht := Width16Actual.straight_t_bound rawEntry26Cat.program
        (readConstant rawEntry26Cat.coefficients.get Q) Fin.elim0
      have hb : rawEntry26Cat.program.gateSlots ≤ 10000000000000 := by
        rw [rawEntry26Cat, Single.fixedEntry_slots]; exact full26Cat_slots
      exact ht.trans (by change _ ≤ 70000000000000; omega)
    · have hm := source26Cat_cursor_le
      change (rawEntry26Cat.program.instantiate _ _).measurementCount ≤ 105000000
      rw [Straight.measurementCount]; omega
  success := by
    intro Q d hn hd
    exact (by norm_num : (99 / 100 : ℝ) ≤ 9911 / 10000).trans (strong_success26Cat Q d hn hd)

def entryTrim18 (e : StraightEntry) : StraightEntry where
  coefficients := e.coefficients
  finalCursor := e.finalCursor
  program := trim 18 e.program

theorem trim18_certificate_generic (limits : Limits) (layout : DecodeLayout) (entry : StraightEntry)
    (bounds : Bounds) (ws : List Wire) (cert : Certificate limits layout entry bounds)
    (hs : Within ws entry.program) (hcost : cost18 entry.program ≤ 51 / 10000)
    (hstrong : ∀ (Q : Point) (d : Nat), Q ≠ 0 → Q = d • G →
      (9911 / 10000 : ℝ) ≤ Instrument.bornMass ((entry.instantiate Q).run.filter
        (fun b => (verifiedCandidate layout Q b.history).isSome)) (ket zeroBasisState)) :
    Certificate limits layout (entryTrim18 entry) ⟨ws.length, bounds.tModel, entry.finalCursor⟩ where
  gateBudget := (trim18_slots entry.program).trans cert.gateBudget
  recordBudget := cert.recordBudget
  tableBudget := cert.tableBudget
  candidateBudget := cert.candidateBudget
  wellFormed := trim18_wellFormed entry.program cert.wellFormed
  resources := by
    intro Q
    have hsup := (trim18_within entry.program ws hs).instantiate
      (readConstant entry.coefficients.get Q) Fin.elim0
    have hc : (((entryTrim18 entry).instantiate Q).wires.dedup.toFinset).card ≤ ws.length := by
      apply (Finset.card_le_card ?_).trans (List.toFinset_card_le ws)
      intro w hw
      exact List.mem_toFinset.mpr (hsup (by simpa only [List.mem_toFinset, List.mem_dedup] using hw))
    have hqc : ((entryTrim18 entry).instantiate Q).qubitCount ≤ ws.length := by
      rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
      exact hc
    refine ⟨hqc, (trim18_t entry.program _ _).trans (cert.resources Q).2.1, ?_⟩
    have he := (entryTrim18 entry).program.measurementCount
      (readConstant entry.coefficients.get Q) Fin.elim0
    simpa only [Nat.add_zero] using he.le
  success := by
    intro Q d hn hd
    have hcn := cost18_nonneg entry.program
    let acc : (Fin entry.finalCursor → Bool) → Bool :=
      fun h => (verifiedCandidate layout Q (List.ofFn h)).isSome
    have h := trim18_expectation (readConstant entry.coefficients.get Q) entry.program
      Fin.elim0 (ket zeroBasisState) (fun h => !acc h) cert.wellFormed hcost
    have hA := ComplementLoss.expectation_compl (readConstant entry.coefficients.get Q)
      entry.program Fin.elim0 (ket zeroBasisState) acc cert.wellFormed
    have hB := ComplementLoss.expectation_compl (readConstant entry.coefficients.get Q)
      (trim 18 entry.program) Fin.elim0 (ket zeroBasisState) acc
      (trim18_wellFormed entry.program cert.wellFormed)
    dsimp only [acc] at hA hB h
    rw [expectation_verified, normSq_ket] at hA hB
    rw [normSq_ket] at h
    have hS := hstrong Q d hn hd
    change 9911 / 10000 ≤ Instrument.bornMass
      ((entry.program.instantiate (readConstant entry.coefficients.get Q) Fin.elim0).run.filter
        (fun b => (verifiedCandidate layout Q b.history).isSome)) (ket zeroBasisState) at hS
    have hf : expectation (readConstant entry.coefficients.get Q) entry.program Fin.elim0
        (ket zeroBasisState) (fun h => !(verifiedCandidate layout Q (List.ofFn h)).isSome) ≤
        1 - 9911 / 10000 := by linarith
    have hm := mul_le_mul_of_nonneg_left hf
      (show 0 ≤ 1 + (106 / 10) * cost18 entry.program by positivity)
    change 99 / 100 ≤ Instrument.bornMass
      (((trim 18 entry.program).instantiate (readConstant entry.coefficients.get Q) Fin.elim0).run.filter
        (fun b => (verifiedCandidate layout Q b.history).isSome)) (ket zeroBasisState)
    nlinarith

theorem trimmed26Cat_coefficients :
    (entryTrim18 rawEntry26Cat).coefficients = List.ofFn coefficientAt26 := by
  unfold entryTrim18 rawEntry26Cat Single.fixedEntry; rfl

theorem trim18_reindex {n m s e : Nat} (f : Fin n → Fin m) (p : Straight n s e) :
    trim 18 (reindexStraight f p) = reindexStraight f (trim 18 p) := by
  induction p with
  | done => rfl
  | measure w p ih => simp only [reindexStraight, trim, ih]
  | recordGate i v g p ih => simp only [reindexStraight, trim]; split_ifs <;> simp [reindexStraight, ih]
  | gate g p ih =>
    cases g with
    | literal g =>
      cases h : largePhase 18 g <;> simp [reindexStraight, reindexGate, trim, h, ih]
    | whenBit r v g =>
      cases h : largePhase 18 g <;> simp [reindexStraight, reindexGate, trim, h, ih]

private theorem trim18_fixedEntry_tCount {n e : Nat} (coeffs : Fin n → PointCoeff)
    (p : Straight n 0 e) (Q : Point) (B : Nat)
    (hp : ∀ read, ((trim 18 p).instantiate read Fin.elim0).tCount ≤ B) :
    ((entryTrim18 (Single.fixedEntry coeffs p)).instantiate Q).tCount ≤ B := by
  change ((trim 18 (Single.fixedEntry coeffs p).program).instantiate _ Fin.elim0).tCount ≤ B
  unfold Single.fixedEntry
  dsimp only
  rw [trim18_reindex, reindexStraight_instantiate]
  exact hp _

theorem trimmed26Cat_tCount (Q : Point) :
    ((entryTrim18 rawEntry26Cat).instantiate Q).tCount ≤ 240303421 := by
  rw [rawEntry26Cat]
  exact trim18_fixedEntry_tCount coefficientAt26 fullProgram26Cat Q 240303421
    (fun r => full26Cat_trim18_tCount r Fin.elim0)

theorem trim18_certificate26Cat :
    Certificate rawLimits26 rawLayout26Cat (entryTrim18 rawEntry26Cat) ⟨1613, 240303421, 105000000⟩ := by
  have hbase := trim18_certificate_generic rawLimits26 rawLayout26Cat rawEntry26Cat rawBounds26Cat
    (List.range 1613) raw_certificate26Cat source26Cat_within source26Cat_cost18 strong_success26Cat
  refine ⟨hbase.gateBudget, hbase.recordBudget, hbase.tableBudget, hbase.candidateBudget,
    hbase.wellFormed, ?_, hbase.success⟩
  intro Q
  have hq : ((entryTrim18 rawEntry26Cat).instantiate Q).qubitCount ≤ 1613 := by
    simpa only [List.length_range] using (hbase.resources Q).1
  have hm : ((entryTrim18 rawEntry26Cat).instantiate Q).measurementCount ≤ 105000000 :=
    (hbase.resources Q).2.2.trans source26Cat_cursor_le
  exact ⟨hq, trimmed26Cat_tCount Q, hm⟩

end Cert26

end
end ShorECDLP.Entrant.Schedule26

namespace ShorECDLP.Entrant.Schedule26Actual
open Quantum Challenge Secp256k1 AndGadget WEXCredit ConditionalCatalyst ApproximatePhase34
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open Schedule26 Trim18
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
attribute [local irreducible] List.ofFn Single.axis Single.fixedEntry
  LocalWide16.compiledProgram LocalWide16.compiledProgramFn
  LocalFour.compileLower CatAxis.axisCat
  Schedule26.rawEntry26Cat Schedule26.fullProgram26Cat Schedule26.program26Cat Schedule26.readout26Cat
  Schedule26.entryTrim18 Schedule26.rawLayout26Cat Schedule26.specializeEntry26
  ConditionalCatalyst.compile

def entry : StraightEntry :=
  specializeEntry26 (entryTrim18 rawEntry26Cat) trimmed26Cat_coefficients

def layout : DecodeLayout := rawLayout26Cat

def bounds : Bounds := ⟨1613, 240303421, 105000000⟩

theorem certificate : Certificate officialLimits layout entry bounds :=
  specializeEntry26_certificate (entryTrim18 rawEntry26Cat) trimmed26Cat_coefficients
    rawLayout26Cat bounds trim18_certificate26Cat

end
end ShorECDLP.Entrant.Schedule26Actual
end

/-! ### Consolidated from `Main.lean` -/
section
-- Entrant/Main.lean
section
namespace ShorECDLP.Entrant
open Challenge
noncomputable section
def bounds : Bounds := ⟨1613, 240303421, 105000000⟩
def entry : StraightEntry := Schedule26Actual.entry
def layout : DecodeLayout := Schedule26Actual.layout
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem certificate : Certificate officialLimits layout entry bounds := Schedule26Actual.certificate
end
end ShorECDLP.Entrant
end
end
