import ShorECDLP.Submission.Entrant.First20Signed
import ShorECDLP.Submission.Entrant.CornerWire

set_option Elab.async false

/-! ### Consolidated from `Schedule26.lean` -/
section
/-! Certified 25-body-window `(256, 206)` sine-windowed Shor ECDLP schedule (`Schedule25`, Wave 8B):
- First window: signed 20-bit 5-pass SelectSwap loader (`First20Signed`, `193,625` Toffolis,
  `524,288` `G`-only rows — all frozen during specialization), locally compiled onto scratch wire `0`
  and catalyst wire `1` inside `List.range 1610`, with internal `X 836` bracketing.
- Left body: `14` signed 17-bit windows (`14 × 17 = 238`, total left precision `20 + 238 = 258`),
  locally compiled via `Generic16.compiledProgram` (`≤ 4 × 2,238,256` T-gates/window, `0` global
  ancilla overhead, catalyst on `compact1610 14833 = 1`), all `G`-only rows frozen during specialization.
- Right body: `12` signed 17-bit windows (`12 × 17 = 204`, `786,432` retained `Q`-rows + 1 sentinel
  `= 786,433 ≤ 983,040`), locally compiled identically via `Generic16.compiledProgram`.
- Approximate catalyst bridge: exact on `First20` + first `13` left body windows (`OddSupport` invariant),
  exception mass `≤ 52 · 2⁻²⁴⁰` across the remaining `13` windows (`MaxBound` convexity),
  yielding pre-trim recovery `≥ 99109 / 100000`.
- Top-10 centered sine window prepended to the left head (`First20Signed`) and right head (`right17 0`),
  `2 × 28 = 56` T-model gates (`k ≤ 11`, untouched by `trim 18`), compiled against catalyst wire `1`.
- `K = 3` neighbour readout (`Readout3`, `-1, 0, +1`, `1,634` records, `0` T-gates).
- Exact `trim 18` affine loss: `cost18 ≤ 425 * unit18 ≤ 51 / 10000`, `46,311` Fourier phase gates
  dropped (`7,088` kept), recovery probability `≥ 99 / 100`.
- Certified resource bounds: `1,610` qubits, `233,560,269` T-model gates (`Q×T = 376,032,033,090`),
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

theorem increment_offset_ge1 (P : Point) (hr : order • P = 0)
    (width exponent v : Nat) (hw : 1 ≤ width) :
    increment P width exponent v + offsetScalar width exponent • P = (v * 2 ^ exponent) • P := by
  have hh : halfOrder ≤ 2 ^ (width - 1) + order := by
    have hl : halfOrder ≤ order := by
      have horder : 0 < order := by norm_num [order]
      dsimp [Single.halfOrder]
      omega
    exact hl.trans (Nat.le_add_left _ _)
  have he : (2 ^ (width - 1) + order - halfOrder) • P + halfOrder • P = 2 ^ (width - 1) • P := by
    rw [← add_nsmul, Nat.sub_add_cancel hh, add_nsmul, hr, add_zero]
  have hoff : offsetScalar width exponent • P =
      2 ^ (width - 1) • (2 ^ exponent • P) - (halfOrder * 2 ^ exponent) • P := by
    unfold offsetScalar
    rw [mul_smul, smul_comm (2 ^ (width - 1) + order - halfOrder) (2 ^ exponent),
      eq_sub_iff_add_eq.mpr he, nsmul_sub]
    simp only [mul_smul]
    rw [smul_comm (2 ^ exponent) (2 ^ (width - 1)), smul_comm (2 ^ exponent) halfOrder]
  let H := (halfOrder * 2 ^ exponent) • P
  have hd : H + H = 2 ^ exponent • P := by
    change (halfOrder * 2 ^ exponent) • P + (halfOrder * 2 ^ exponent) • P = _
    rw [mul_smul, smul_comm halfOrder (2 ^ exponent), ← nsmul_add]
    exact congrArg (fun R : Point => 2 ^ exponent • R)
      (signedWindowHalfPoint_double P order (by decide +kernel) hr)
  have hp_nat : 2 ^ width = 2 * 2 ^ (width - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hw]
  have hp : (2 : Int) ^ width = 2 * (2 ^ (width - 1) : Nat) := by
    exact_mod_cast hp_nat
  have hcalc : ((2 * (v : Int) - (2 : Int) ^ width + 1) • H) +
      (2 ^ (width - 1) • (H + H) - H) = v • (H + H) := by rw [hp]; module
  change ((2 * (v : Int) - (2 : Int) ^ width + 1) • H) + _ = _
  rw [hoff]
  simp only [hd] at hcalc
  exact hcalc.trans (mul_smul v (2 ^ exponent) P).symm

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

theorem reset_range : resetWires ⊆ List.range 1610 := by
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

theorem joint_error18_256_206 : account18 256 0 + account18 206 0 ≤ 51 / 10000 := by
  have hz : account18 17 0 = 0 := by norm_num [account18, potential18, unit18]
  rw [show 256 = 17 + 239 from rfl, show 206 = 17 + 189 from rfl,
    account18_append, account18_append, hz]
  norm_num only [zero_add]
  have h1 := account18_geometric 239 17 (by decide)
  have h2 := account18_geometric 189 17 (by decide)
  have hp1 : potential18 (17 + 239 + 2) ≤ unit18 / 4 := by
    unfold potential18 unit18
    rw [show max 19 (17 + 239 + 2) = 258 by decide]
    have h21 : (2 : ℝ) ^ 21 ≤ (2 : ℝ) ^ 258 := pow_le_pow_right₀ (by norm_num) (by decide)
    rw [show (6283186 / 1000000 : ℝ) / 2 ^ 19 / 4 = (6283186 / 1000000 : ℝ) / (2 : ℝ) ^ 21 by norm_num]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) h21
  have hp2 : potential18 (17 + 189 + 2) ≤ unit18 / 4 := by
    unfold potential18 unit18
    rw [show max 19 (17 + 189 + 2) = 208 by decide]
    have h21 : (2 : ℝ) ^ 21 ≤ (2 : ℝ) ^ 208 := pow_le_pow_right₀ (by norm_num) (by decide)
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

/-! ### Part 2c: Approximate local-catalyst axis bridge (`ApproxCat`) -/

namespace ShorECDLP.Entrant.ApproxCat
open Quantum Challenge Secp256k1 AndGadget ConditionalCatalyst ApproximatePhase34
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open Single Single.Distribution LocalFour Trim18 CatAxis
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
attribute [local irreducible] fourierOutcomes
local instance approxCatBody : Single.WindowBody := PathShare.bodyCF
local instance approxCatResources : Single.ProducerResources approxCatBody :=
  Single.ProducerResources.ofBody PathShare.bodyCF
    (by change resetWires.Nodup; exact resetWires_nodup)
    (by change (0 : Wire) ∈ resetWires; decide)
    (by change (1 : Wire) ∈ resetWires; decide)

/-! #### Pointwise state restriction and instrument perturbation bounds -/

def restrictState (P : BasisState → Prop) (χ : State) : State := by
  classical
  exact Finsupp.onFinset χ.support (fun s => if P s then χ s else 0) (fun s hs => by
    by_cases h : s ∈ χ.support
    · exact h
    · exfalso; apply hs; simp [Finsupp.notMem_support_iff.mp h])

theorem restrictState_apply (P : BasisState → Prop) [DecidablePred P] (χ : State) (s : BasisState) :
    restrictState P χ s = if P s then χ s else 0 := by
  unfold restrictState
  rw [Finsupp.onFinset_apply]
  split_ifs <;> rfl

theorem restrictState_add_compl (P : BasisState → Prop) (χ : State) :
    restrictState P χ + restrictState (fun s => ¬ P s) χ = χ := by
  classical
  ext s
  simp only [Finsupp.add_apply, restrictState_apply]
  by_cases h : P s <;> simp [h]

theorem restrictState_supportedOn (P : BasisState → Prop) (χ : State) :
    SupportedOn P (restrictState P χ) := by
  classical
  intro s hs
  rw [restrictState_apply] at hs
  by_contra hnp
  simp [hnp] at hs

theorem restrictState_preserves (P Q : BasisState → Prop) (χ : State) (hχ : SupportedOn Q χ) :
    SupportedOn Q (restrictState P χ) := by
  classical
  intro s hs
  rw [restrictState_apply] at hs
  by_cases hp : P s
  · simp [hp] at hs; exact hχ s hs
  · simp [hp] at hs

theorem restrictState_zero_of_supportedOn (P : BasisState → Prop) (χ : State) (hχ : SupportedOn P χ) :
    restrictState (fun s => ¬ P s) χ = 0 := by
  classical
  ext s
  simp only [restrictState_apply, Finsupp.zero_apply]
  by_cases hp : P s
  · simp [hp]
  · simp only [hp, not_false_eq_true, ↓reduceIte]
    by_contra hne
    exact hp (hχ s hne)

theorem restrictState_map_add (P : BasisState → Prop) (a b : State) :
    restrictState P (a + b) = restrictState P a + restrictState P b := by
  classical
  ext s
  simp only [Finsupp.add_apply, restrictState_apply]
  split_ifs <;> simp

theorem restrictState_map_smul (P : BasisState → Prop) (c : ℂ) (a : State) :
    restrictState P (c • a) = c • restrictState P a := by
  classical
  ext s
  simp only [Finsupp.smul_apply, smul_eq_mul, restrictState_apply]
  split_ifs <;> simp

def restrictLin (P : BasisState → Prop) : State →ₗ[ℂ] State where
  toFun := restrictState P
  map_add' := restrictState_map_add P
  map_smul' := restrictState_map_smul P

theorem restrictState_ket (P : BasisState → Prop) [DecidablePred P] (s : BasisState) :
    restrictState P (ket s) = if P s then ket s else 0 := by
  ext t
  rw [restrictState_apply]
  by_cases hst : t = s
  · subst hst; split_ifs <;> simp [ket]
  · split_ifs <;> simp [ket, hst]

theorem normSq_smul (c : ℂ) (ψ : State) :
    normSq (c • ψ) = Complex.normSq c * normSq ψ := by
  unfold normSq
  rw [inner_smul_smul, ← Complex.normSq_eq_conj_mul_self]
  simp

theorem normSq_neg (ψ : State) : normSq (-ψ) = normSq ψ := by
  have h : -ψ = (-1 : ℂ) • ψ := by simp
  rw [h, normSq_smul]
  simp

theorem instrument_mass_neg (I : Instrument) (ψ : State) :
    I.bornMass (-ψ) = I.bornMass ψ := by
  induction I with
  | nil => rfl
  | cons b bs ih =>
    change normSq (b.kraus (-ψ)) + Instrument.bornMass bs (-ψ) = normSq (b.kraus ψ) + Instrument.bornMass bs ψ
    rw [map_neg, normSq_neg, ih]

theorem instrument_mass_upper (I : Instrument) (a b : State) (eps : ℝ) (heps : 0 < eps) :
    I.bornMass (a + b) ≤ (1 + eps) * I.bornMass a + (1 + 1 / eps) * I.bornMass b := by
  induction I with
  | nil => simp [Instrument.bornMass]
  | cons br bs ih =>
    change normSq (br.kraus (a + b)) + Instrument.bornMass bs (a + b) ≤
      (1 + eps) * (normSq (br.kraus a) + Instrument.bornMass bs a) +
      (1 + 1 / eps) * (normSq (br.kraus b) + Instrument.bornMass bs b)
    have h1 := ComplementLoss.mass_upper (br.kraus a) (br.kraus b) eps
    rw [← map_add] at h1
    have h2 : normSq (br.kraus (a + b)) ≤
        (1 + eps) * normSq (br.kraus a) + (1 + 1 / eps) * normSq (br.kraus b) := by
      have hdiv : (eps * normSq (br.kraus (a + b))) / eps ≤
          ((eps + eps ^ 2) * normSq (br.kraus a) + (1 + eps) * normSq (br.kraus b)) / eps :=
        div_le_div_of_nonneg_right h1 heps.le
      have he0 : eps ≠ 0 := heps.ne'
      have hl : (eps * normSq (br.kraus (a + b))) / eps = normSq (br.kraus (a + b)) := by field_simp
      have hr : ((eps + eps ^ 2) * normSq (br.kraus a) + (1 + eps) * normSq (br.kraus b)) / eps =
          (1 + eps) * normSq (br.kraus a) + (1 + 1 / eps) * normSq (br.kraus b) := by field_simp; ring
      linarith
    linarith

theorem instrument_bornMass_nonneg (I : Instrument) (ψ : State) : 0 ≤ I.bornMass ψ := by
  induction I with
  | nil => simp [Instrument.bornMass]
  | cons b bs ih =>
    change 0 ≤ normSq (b.kraus ψ) + Instrument.bornMass bs ψ
    exact add_nonneg (ApproximatePhase34.mass_nonneg _) ih

def SubUnital (I : Instrument) : Prop := ∀ φ, I.bornMass φ ≤ normSq φ

theorem subUnital_nil : SubUnital List.nil := fun φ => by
  simpa [Instrument.bornMass] using ApproximatePhase34.mass_nonneg φ

theorem subUnital_ite (c : Bool) (I : Instrument) (hI : SubUnital I) :
    SubUnital (if c then I else List.nil) := by
  cases c <;> [exact subUnital_nil; exact hI]

theorem normSq_list_sum_fourierBranch (dir : PhaseDir) (ws : List Wire) (prior : List Bool) (φ : State) :
    ((fourierOutcomes ws.length).map (fun bits => normSq (fourierBranch dir ws prior bits φ))).sum =
      normSq φ := by
  let idxs : List (Fin prior.length) := List.ofFn id
  let hist : Fin prior.length → Bool := fun i => prior[i.val]'i.isLt
  have hmap : idxs.map hist = prior := by
    apply List.ext_getElem (by simp [idxs])
    intro i hi _
    simp [idxs, hist]
  have hpres := AdaptiveCircuit.run_preservesBornMass _
    ((fourierProgram 1 dir ws prior.length idxs).instantiate_wellFormed (fun _ => false) hist
      (fourierProgram_wellFormed 1 dir ws prior.length idxs)) φ
  rw [fourierProgram_run, hmap, semiclassicalFourier_run] at hpres
  simpa only [Instrument.bornMass, List.map_map, Function.comp_def] using hpres

theorem normSq_list_sum_compileFourierBranch (y : Wire) (dir : PhaseDir) (ws : List Wire)
    (hy : y ∉ ws) (prior : List Bool) (φ : State) :
    ((fourierOutcomes ws.length).map (fun bits => normSq (compileFourierBranch y dir ws prior bits φ))).sum =
      normSq φ := by
  let idxs : List (Fin prior.length) := List.ofFn id
  let hist : Fin prior.length → Bool := fun i => prior[i.val]'i.isLt
  have hmap : idxs.map hist = prior := by
    apply List.ext_getElem (by simp [idxs])
    intro i hi _
    simp [idxs, hist]
  have hfresh : Fresh y (fourierProgram 1 dir ws prior.length idxs) := by
    apply LocalFour.fresh_of_not_mem_straightWires
    intro hm
    have hsub : ChallengeMigration.straightWires (fourierProgram 1 dir ws prior.length idxs) ⊆ ws :=
      LocalFour.straightWires_of_within _ _ (within_of_instantiate _ ws (fun r h =>
        fourierProgram_support 1 dir ws prior.length idxs r h ws (List.Subset.refl ws)))
    exact hy (hsub hm)
  have hwf := ConditionalCatalyst.compile_wellFormed y _ hfresh
    (fourierProgram_wellFormed 1 dir ws prior.length idxs)
  have hpres := AdaptiveCircuit.run_preservesBornMass _
    ((ConditionalCatalyst.compile y (fourierProgram 1 dir ws prior.length idxs)).instantiate_wellFormed (fun _ => false) hist hwf) φ
  rw [compile_fourierProgram_run, hmap] at hpres
  simpa only [Instrument.bornMass, List.map_map, Function.comp_def] using hpres

theorem one_add_pow_le (δ : ℝ) (n : Nat) (hδ : 0 ≤ δ) (hsmall : (2 * (n : ℝ)) * δ ≤ 1) :
    (1 + δ) ^ n ≤ 1 + (2 * (n : ℝ)) * δ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : (2 * (n : ℝ)) * δ ≤ 1 := by push_cast at hsmall ⊢; linarith
    have hi := ih h1
    rw [pow_succ]
    push_cast at hsmall ⊢
    nlinarith

theorem normSq_add_ket (s : BasisState) (c : ℂ) (φ : State) (hφs : φ s = 0) :
    normSq (c • ket s + φ) = Complex.normSq c + normSq φ := by
  classical
  let S := (c • ket s).support ∪ φ.support
  have h1 : (c • ket s + φ).support ⊆ S := Finsupp.support_add
  have heq : ∑ u ∈ S, Complex.normSq ((c • ket s + φ) u) =
      ∑ u ∈ S, (Complex.normSq ((c • ket s) u) + Complex.normSq (φ u)) := by
    apply Finset.sum_congr rfl; intro u _
    rw [Finsupp.add_apply]
    by_cases hus : u = s
    · subst hus; simp [hφs]
    · simp [ket, hus]
  rw [ApproximatePhase34.mass_on (c • ket s + φ) S h1, heq, Finset.sum_add_distrib,
    ← ApproximatePhase34.mass_on (c • ket s) S Finset.subset_union_left,
    ← ApproximatePhase34.mass_on φ S Finset.subset_union_right, normSq_smul, normSq_ket, mul_one]

theorem lmapDomain_eval_zero_of_not_mem {f : BasisState → BasisState} (φ : State) (y : BasisState)
    (h : ∀ s ∈ φ.support, f s ≠ y) : (Finsupp.lmapDomain ℂ ℂ f φ) y = 0 := by
  induction φ using Finsupp.induction with
  | zero => simp
  | single_add t c g htg hc ih =>
    have ht : t ∈ (Finsupp.single t c + g).support := by
      rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_same,
        Finsupp.notMem_support_iff.mp htg, add_zero]; exact hc
    have hg : ∀ s ∈ g.support, f s ≠ y := fun s hs => h s (by
      have hst : s ≠ t := fun e => htg (e ▸ hs)
      rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_of_ne hst, zero_add]
      exact Finsupp.mem_support_iff.mp hs)
    rw [map_add, Finsupp.add_apply, ih hg, add_zero]
    rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.single_eq_of_ne (Ne.symm (h t ht))]

theorem lmapDomain_apply_injOn {f : BasisState → BasisState} (φ : State) (s : BasisState)
    (hf : Set.InjOn f (insert s (φ.support : Set BasisState))) :
    (Finsupp.lmapDomain ℂ ℂ f φ) (f s) = φ s := by
  induction φ using Finsupp.induction with
  | zero => simp
  | single_add t c g htg hc ih =>
    have ht_mem : t ∈ (Finsupp.single t c + g).support := by
      rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_same,
        Finsupp.notMem_support_iff.mp htg, add_zero]; exact hc
    have hg_sub : (g.support : Set BasisState) ⊆ ((Finsupp.single t c + g).support : Set BasisState) := by
      intro u hu
      have hut : u ≠ t := fun e => htg (e ▸ hu)
      change u ∈ (Finsupp.single t c + g).support
      rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_of_ne hut, zero_add]
      exact Finsupp.mem_support_iff.mp hu
    have hih := ih (hf.mono (Set.insert_subset_insert hg_sub))
    rw [map_add, Finsupp.add_apply, Finsupp.add_apply, hih,
      Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    by_cases hts : t = s
    · subst hts; simp
    · have hfts : f t ≠ f s := fun e => hts (hf (Set.mem_insert_of_mem _ ht_mem) (Set.mem_insert _ _) e)
      rw [Finsupp.single_eq_of_ne (Ne.symm hfts), Finsupp.single_eq_of_ne (Ne.symm hts)]

theorem normSq_lmapDomain_injOn {f : BasisState → BasisState} (φ : State)
    (hf : Set.InjOn f (φ.support : Set BasisState)) :
    normSq (Finsupp.lmapDomain ℂ ℂ f φ) = normSq φ := by
  induction φ using Finsupp.induction with
  | zero => simp
  | single_add t c g htg hc ih =>
    have ht_mem : t ∈ (Finsupp.single t c + g).support := by
      rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_same,
        Finsupp.notMem_support_iff.mp htg, add_zero]; exact hc
    have hg_sub : (g.support : Set BasisState) ⊆ ((Finsupp.single t c + g).support : Set BasisState) := by
      intro u hu
      have hut : u ≠ t := fun e => htg (e ▸ hu)
      change u ∈ (Finsupp.single t c + g).support
      rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_of_ne hut, zero_add]
      exact Finsupp.mem_support_iff.mp hu
    have hket : Finsupp.single t c = c • ket t := by ext u; simp [ket]
    have hlket : Finsupp.lmapDomain ℂ ℂ f (Finsupp.single t c) = c • ket (f t) := by
      rw [hket, map_smul, Mixed.lmap_ket']
    have hg0 : g t = 0 := Finsupp.notMem_support_iff.mp htg
    have hlg0 : (Finsupp.lmapDomain ℂ ℂ f g) (f t) = 0 :=
      lmapDomain_eval_zero_of_not_mem g (f t) (fun u hu he =>
        htg ((hf (hg_sub hu) ht_mem he) ▸ hu))
    rw [map_add, hlket, normSq_add_ket (f t) c _ hlg0, ih (hf.mono hg_sub), hket, normSq_add_ket t c g hg0]

/-! #### `ApproxCatWindow`, `taggedAxisApprox`, `selectedAxisDep`, and `axisBad` -/

structure ApproxCatWindow {n : Nat} (y : Wire) (read : ConstantBit n → Bool) where
  model : WindowModel read
  catPhys : Single.Window n
  pre : Circuit
  core : (start : Nat) → Straight n start (start + catPhys.count)
  prog_eq : ∀ start, catPhys.program start =
    (ConditionalCatalyst.compile y (literalProgram pre)).append (core start)
  pre_noY : y ∉ circuitWires pre
  pre_wf : CircuitWellFormed pre
  core_ideal : State →ₗ[ℂ] State
  ideal_eq : model.ideal = core_ideal.comp (Quantum.run pre)
  wires_eq : catPhys.wires = model.physical.wires
  noY : y ∉ model.physical.wires
  goodPred : BasisState → Prop
  catCoherent : ∀ start history,
    CatCoherent y ((core start).instantiate read history) core_ideal goodPred
  core_idealY : ∀ ψ, SupportedOn (fun s => s y = false) ψ →
    SupportedOn (fun s => s y = false) (core_ideal ψ)
  core_wf : ∀ start, (core start).WellFormed

theorem ApproxCatWindow.phys_wf {n : Nat} {y : Wire} {read : ConstantBit n → Bool}
    (w : ApproxCatWindow y read) (start : Nat) : (w.catPhys.program start).WellFormed := by
  rw [w.prog_eq start]
  apply straight_append_wellFormed
  · apply ConditionalCatalyst.compile_wellFormed y _ _ (literalProgram_wellFormed w.pre w.pre_wf)
    apply LocalFour.fresh_of_not_mem_straightWires
    intro hm
    exact w.pre_noY (Schedule26Bridge.literalProgram_straightWires w.pre hm)
  · exact w.core_wf start

def taggedAxisApprox {n : Nat} {y : Wire} {read : ConstantBit n → Bool} :
    List (ApproxCatWindow y read) → (start : Nat) → (Fin start → Bool) → List (Fin start) →
      List (List Bool × InstrumentBranch)
  | [], _, history, prior => [(prior.map history, ⟨[], LinearMap.id⟩)]
  | w :: ws, start, history, prior =>
      (((prepareOuterBank w.catPhys.wires.reverse (w.catPhys.program start)).instantiate read history).run).flatMap
        (fun a => (fourierOutcomes w.catPhys.wires.length).flatMap (fun bits =>
          let h₁ := Single.historyAfter (start + w.catPhys.count) history a.history
          let h₂ := Single.historyAfter (start + w.catPhys.count + w.catPhys.wires.length) h₁ bits
          (taggedAxisApprox ws _ h₂ (nextPrior w.catPhys.count w.catPhys.wires.length prior)).map
            (fun b => (b.1, (a.seq ⟨bits, compileFourierBranch y .inverse w.catPhys.wires (prior.map history) bits⟩).seq b.2))))

def selectedAxisDep {n : Nat} {y : Wire} {read : ConstantBit n → Bool}
    (ws : List (ApproxCatWindow y read)) (start : Nat) (history : Fin start → Bool)
    (prior : List (Fin start)) (physTerm : List Bool → List Bool → Instrument) : Instrument :=
  (taggedAxisApprox ws start history prior).flatMap (fun a => (physTerm a.2.history a.1).map a.2.seq)

def taggedTwoAxesApprox {n : Nat} {y : Wire} {read : ConstantBit n → Bool}
    (left right : List (ApproxCatWindow y read)) (start : Nat) (history : Fin start → Bool) :
    List ((List Bool × List Bool) × InstrumentBranch) :=
  (taggedAxisApprox left start history List.nil).flatMap (fun l =>
    (taggedAxisApprox right (start + Single.axisCount (left.map ApproxCatWindow.catPhys))
      (Single.historyAfter _ history l.2.history) List.nil).map (fun r => ((l.1, r.1), l.2.seq r.2)))

def selectedTwoAxesApprox {n : Nat} {y : Wire} {read : ConstantBit n → Bool}
    (left right : List (ApproxCatWindow y read)) (start : Nat) (history : Fin start → Bool)
    (terminal : List Bool → List Bool → Instrument) : Instrument :=
  (taggedTwoAxesApprox left right start history).flatMap (fun a => (terminal a.1.1 a.1.2).map a.2.seq)

def physicalAxesApprox {n : Nat} {y : Wire} {read : ConstantBit n → Bool}
    (left right : List (ApproxCatWindow y read)) (start : Nat) (history : Fin start → Bool) : Instrument :=
  (((axisCat y (left.map ApproxCatWindow.catPhys) start List.nil).append
    (axisCat y (right.map ApproxCatWindow.catPhys) (start + Single.axisCount (left.map ApproxCatWindow.catPhys))
      List.nil)).instantiate read history).run

theorem axisCat_run_taggedApprox {n : Nat} {y : Wire} {read : ConstantBit n → Bool}
    (ws : List (ApproxCatWindow y read)) (start : Nat) (history : Fin start → Bool)
    (prior : List (Fin start)) :
    ((axisCat y (ws.map ApproxCatWindow.catPhys) start prior).instantiate read history).run =
      (taggedAxisApprox ws start history prior).map Prod.snd := by
  induction ws generalizing start with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, axisCat, castFinish_instantiate]
    rw [append_run_history]
    simp only [taggedAxisApprox, List.map_flatMap, List.map_map, Function.comp_def]
    apply List.flatMap_congr; intro a _
    rw [append_run_history]
    simp only [castFinish_instantiate]
    rw [compile_fourierProgram_run, bankPrior_map]
    simp only [List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def]
    apply List.flatMap_congr; intro bits _
    rw [ih]
    simp only [List.map_map, Function.comp_def]
    apply List.map_congr_left; intro x _
    rcases a with ⟨ah, ak⟩; rcases x with ⟨xt, xh, xk⟩
    simp [InstrumentBranch.seq, List.append_assoc, LinearMap.comp_assoc]

theorem taggedAxisApprox_transcript {n : Nat} {y : Wire} {read : ConstantBit n → Bool}
    (ws : List (ApproxCatWindow y read)) (start : Nat) (history : Fin start → Bool)
    (prior : List (Fin start)) (tagged : List Bool × InstrumentBranch)
    (ht : tagged ∈ taggedAxisApprox ws start history prior) :
    ∃ bits, Transcript (ws.map (fun w => (w.catPhys.count, w.catPhys.wires.length)))
        tagged.2.history bits ∧ tagged.1 = bits.reverse ++ prior.map history := by
  induction ws generalizing start tagged with
  | nil =>
    simp only [taggedAxisApprox, List.mem_singleton] at ht
    subst tagged
    exact ⟨[], Transcript.nil, rfl⟩
  | cons w ws ih =>
    obtain ⟨a, ha, ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨bits, hb, ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨b, hbt, rfl⟩ := List.mem_map.mp ht
    obtain ⟨out, htrans, htag⟩ := ih _ _ _ b hbt
    have hla : a.history.length = w.catPhys.count := by
      have h := straight_history_length _ read history a ha; omega
    have hlb := (fourierOutcomes_mem _ _).mp hb
    refine ⟨bits ++ out, ?_, ?_⟩
    · simpa only [List.map_cons, InstrumentBranch.seq, List.append_assoc] using
        Transcript.cons w.catPhys.count w.catPhys.wires.length _ a.history bits b.2.history out hla hlb htrans
    · rw [htag, nextPrior_map _ _ _ _ _ _ hla hlb]
      simp only [List.reverse_append, List.append_assoc]

theorem taggedAxisApprox_readWord {n : Nat} {y : Wire} {read : ConstantBit n → Bool}
    (ws : List (ApproxCatWindow y read)) (start : Nat) (history : Fin start → Bool)
    (tagged : List Bool × InstrumentBranch)
    (ht : tagged ∈ taggedAxisApprox ws start history List.nil) (after : List Bool) :
    ShorECDLP.Challenge.readWord (List.ofFn history ++ tagged.2.history ++ after)
      (Single.axisPositions (ws.map ApproxCatWindow.catPhys) start) =
        some (fourierWordLSB tagged.1.reverse) := by
  obtain ⟨bits, htrans, htag⟩ := taggedAxisApprox_transcript ws start history List.nil tagged ht
  rw [htag]
  simpa only [List.map_nil, List.append_nil, List.reverse_reverse, List.length_ofFn,
    Single.axisPositions, List.map_map, Function.comp_def] using htrans.readWord (List.ofFn history) after

theorem taggedAxisApprox_history_length {n : Nat} {y : Wire} {read : ConstantBit n → Bool}
    (ws : List (ApproxCatWindow y read)) (start : Nat) (history : Fin start → Bool)
    (prior : List (Fin start)) (tagged : List Bool × InstrumentBranch)
    (ht : tagged ∈ taggedAxisApprox ws start history prior) :
    tagged.2.history.length = Single.axisCount (ws.map ApproxCatWindow.catPhys) := by
  have hb : tagged.2 ∈ ((axisCat y (ws.map ApproxCatWindow.catPhys) start prior).instantiate read history).run := by
    rw [axisCat_run_taggedApprox]
    exact List.mem_map.mpr ⟨tagged, ht, rfl⟩
  have h := straight_history_length _ read history tagged.2 hb
  omega

theorem twoAxesApprox_run_tagged {n : Nat} {y : Wire} {read : ConstantBit n → Bool}
    (left right : List (ApproxCatWindow y read)) (start : Nat) (history : Fin start → Bool) :
    physicalAxesApprox left right start history =
      (taggedTwoAxesApprox left right start history).map Prod.snd := by
  unfold physicalAxesApprox
  rw [append_run_history, axisCat_run_taggedApprox]
  simp only [taggedTwoAxesApprox, List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def]
  apply List.flatMap_congr; intro a _
  rw [axisCat_run_taggedApprox]
  simp only [List.map_map, Function.comp_def]

theorem selectedTwoAxesApprox_fixed_filter {n : Nat} {y : Wire} {read : ConstantBit n → Bool}
    (left right : List (ApproxCatWindow y read)) (J : Instrument) (accept : Nat → Nat → Bool) :
    selectedTwoAxesApprox left right 0 Fin.elim0 (fun lhs rhs =>
      if accept (fourierWordLSB lhs.reverse) (fourierWordLSB rhs.reverse) then J else List.nil) =
      ((physicalAxesApprox left right 0 Fin.elim0).seq J).filter (fun b =>
        pairAccept (Single.axisPositions (left.map ApproxCatWindow.catPhys) 0)
          (Single.axisPositions (right.map ApproxCatWindow.catPhys)
            (Single.axisCount (left.map ApproxCatWindow.catPhys))) accept b.history) := by
  have hconst : selectedTwoAxesApprox left right 0 Fin.elim0 (fun _ _ => J) =
      (physicalAxesApprox left right 0 Fin.elim0).seq J := by
    rw [twoAxesApprox_run_tagged]
    simp only [selectedTwoAxesApprox, Instrument.seq, List.flatMap_map]
  rw [← hconst, selectedTwoAxesApprox, selectedTwoAxesApprox, List.filter_flatMap]
  apply List.flatMap_congr; intro a ha
  obtain ⟨l, hl, ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
  have hp (b : InstrumentBranch) :
      pairAccept (Single.axisPositions (left.map ApproxCatWindow.catPhys) 0)
        (Single.axisPositions (right.map ApproxCatWindow.catPhys)
          (Single.axisCount (left.map ApproxCatWindow.catPhys)))
        accept ((l.2.seq r.2).seq b).history =
          accept (fourierWordLSB l.1.reverse) (fourierWordLSB r.1.reverse) := by
    have hleft := taggedAxisApprox_readWord left 0 Fin.elim0 l hl (r.2.history ++ b.history)
    have hright := taggedAxisApprox_readWord right _ _ r hr b.history
    have hlen := taggedAxisApprox_history_length left 0 Fin.elim0 List.nil l hl
    rw [historyAfter_list Fin.elim0 l.2.history (by omega)] at hright
    simp only [List.ofFn_zero, List.nil_append, Nat.zero_add, InstrumentBranch.seq, List.append_assoc] at hleft hright ⊢
    simp only [pairAccept, hleft, hright, Option.bind_some, Option.map_some, Option.getD_some]
  rw [List.filter_map]
  simp only [Function.comp_def, hp]
  split <;> simp_all

theorem selectedTwoAxesApprox_expand {n : Nat} {y : Wire} {read : ConstantBit n → Bool}
    (left right : List (ApproxCatWindow y read)) (start : Nat) (history : Fin start → Bool)
    (terminal : List Bool → List Bool → Instrument) :
    selectedTwoAxesApprox left right start history terminal =
      selectedAxisDep left start history List.nil (fun lHist lhs =>
        selectedAxisDep right (start + Single.axisCount (left.map ApproxCatWindow.catPhys))
          (Single.historyAfter _ history lHist) List.nil (fun _ rhs => terminal lhs rhs)) := by
  simp only [selectedTwoAxesApprox, taggedTwoAxesApprox, selectedAxisDep, List.flatMap_assoc,
    List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def]
  apply List.flatMap_congr; intro l _
  apply List.flatMap_congr; intro r _
  apply List.map_congr_left; intro b _
  rcases l with ⟨lt, lh, lk⟩; rcases r with ⟨rt, rh, rk⟩; rcases b with ⟨bh, bk⟩
  simp [InstrumentBranch.seq, LinearMap.comp_assoc, List.append_assoc]

theorem selectedAxisDep_cons_mass {n : Nat} {y : Wire} {read : ConstantBit n → Bool}
    (w : ApproxCatWindow y read) (ws : List (ApproxCatWindow y read)) (start : Nat)
    (history : Fin start → Bool) (prior : List (Fin start))
    (physTerm : List Bool → List Bool → Instrument) (ψ : State) :
    (selectedAxisDep (w :: ws) start history prior physTerm).bornMass ψ =
      (((w.core start).instantiate read history).run.map (fun a =>
        ((fourierOutcomes w.catPhys.wires.length).map (fun bits =>
          let h₁ := Single.historyAfter (start + w.catPhys.count) history a.history
          let h₂ := Single.historyAfter (start + w.catPhys.count + w.catPhys.wires.length) h₁ bits
          (selectedAxisDep ws _ h₂ (nextPrior w.catPhys.count w.catPhys.wires.length prior)
            (fun hRest tag => physTerm (a.history ++ bits ++ hRest) tag)).bornMass
            (compileFourierBranch y .inverse w.catPhys.wires (prior.map history) bits
              (a.kraus (Quantum.run (compileCircuit y w.pre)
                (Quantum.run (w.catPhys.wires.reverse.map Gate.H) ψ)))))).sum)).sum := by
  have hcons : selectedAxisDep (w :: ws) start history prior physTerm =
      (((prepareOuterBank w.catPhys.wires.reverse (w.catPhys.program start)).instantiate read history).run).flatMap
        (fun a => (fourierOutcomes w.catPhys.wires.length).flatMap (fun bits =>
          let h₁ := Single.historyAfter (start + w.catPhys.count) history a.history
          let h₂ := Single.historyAfter (start + w.catPhys.count + w.catPhys.wires.length) h₁ bits
          (selectedAxisDep ws _ h₂ (nextPrior w.catPhys.count w.catPhys.wires.length prior)
            (fun hRest tag => physTerm (a.history ++ bits ++ hRest) tag)).map
            (a.seq ⟨bits, compileFourierBranch y .inverse w.catPhys.wires (prior.map history) bits⟩).seq)) := by
    simp only [selectedAxisDep, taggedAxisApprox, List.flatMap_assoc, List.flatMap_map,
      List.map_flatMap, List.map_map, Function.comp_def]
    apply List.flatMap_congr; intro a _
    apply List.flatMap_congr; intro bits _
    apply List.flatMap_congr; intro b _
    apply List.map_congr_left; intro c _
    rcases a with ⟨ah, ak⟩; rcases b with ⟨tag, bh, bk⟩; rcases c with ⟨ch, ck⟩
    simp [InstrumentBranch.seq, LinearMap.comp_assoc, List.append_assoc]
  have hprog_run : ((w.catPhys.program start).instantiate read history).run =
      ((w.core start).instantiate read history).run.map
        (fun a => ({ history := List.nil, kraus := Quantum.run (compileCircuit y w.pre) } : InstrumentBranch).seq a) := by
    rw [w.prog_eq start, Single.append_run_history, CatAxis.compile_literalProgram_eq]
    have hlit_eq : ∀ (gs : Circuit), AndGadget.literals gs (.done : Straight n start start) = literalProgram gs := by
      intro gs; induction gs with
      | nil => rfl
      | cons g gs ih =>
        change Straight.gate (.literal g) (AndGadget.literals gs (.done : Straight n start start)) =
          Straight.gate (.literal g) (literalProgram gs)
        rw [ih]
    have hlit : ((AndGadget.literals (compileCircuit y w.pre) (.done : Straight n start start)).instantiate read history).run =
        [{ history := List.nil, kraus := Quantum.run (compileCircuit y w.pre) }] := by
      rw [hlit_eq, ChallengeMigration.literalProgram_run]
      change ([{ history := List.nil, kraus := LinearMap.id.comp (Quantum.run (compileCircuit y w.pre)) }] : Instrument) = _
      simp
    rw [hlit]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have hhist0 : Single.historyAfter start history List.nil = history := by
      funext i; simp [Single.historyAfter, List.ofFn_getElem]
    rw [hhist0]
  rw [hcons, prepare_run, hprog_run]
  simp only [flat_mass, prefixed_mass, List.flatMap_map, List.map_map, Function.comp_def,
    InstrumentBranch.seq, LinearMap.comp_apply, List.nil_append]

theorem list_sum_map_le {α : Type} (xs : List α) (f g : α → ℝ) (h : ∀ x ∈ xs, f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h x List.mem_cons_self) (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))

theorem selectedAxisDep_subUnital {n : Nat} {y : Wire} {read : ConstantBit n → Bool}
    (ws : List (ApproxCatWindow y read)) (start : Nat) (history : Fin start → Bool)
    (prior : List (Fin start)) (physTerm : List Bool → List Bool → Instrument)
    (hterm : ∀ h tag, SubUnital (physTerm h tag)) :
    SubUnital (selectedAxisDep ws start history prior physTerm) := by
  induction ws generalizing start physTerm with
  | nil =>
    intro φ
    simp only [selectedAxisDep, taggedAxisApprox, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [prefixed_mass ⟨[], LinearMap.id⟩ _ φ]
    exact hterm _ _ φ
  | cons w ws ih =>
    intro φ
    rw [selectedAxisDep_cons_mass]
    have h1 : ∀ a ∈ ((w.core start).instantiate read history).run,
        ((fourierOutcomes w.catPhys.wires.length).map (fun bits =>
          let h₁ := Single.historyAfter (start + w.catPhys.count) history a.history
          let h₂ := Single.historyAfter (start + w.catPhys.count + w.catPhys.wires.length) h₁ bits
          (selectedAxisDep ws _ h₂ (nextPrior w.catPhys.count w.catPhys.wires.length prior)
            (fun hRest tag => physTerm (a.history ++ bits ++ hRest) tag)).bornMass
            (compileFourierBranch y .inverse w.catPhys.wires (prior.map history) bits
              (a.kraus (Quantum.run (compileCircuit y w.pre)
                (Quantum.run (w.catPhys.wires.reverse.map Gate.H) φ)))))).sum ≤
          normSq (a.kraus (Quantum.run (compileCircuit y w.pre)
            (Quantum.run (w.catPhys.wires.reverse.map Gate.H) φ))) := by
      intro a _
      have hle : ((fourierOutcomes w.catPhys.wires.length).map (fun bits =>
          let h₁ := Single.historyAfter (start + w.catPhys.count) history a.history
          let h₂ := Single.historyAfter (start + w.catPhys.count + w.catPhys.wires.length) h₁ bits
          (selectedAxisDep ws _ h₂ (nextPrior w.catPhys.count w.catPhys.wires.length prior)
            (fun hRest tag => physTerm (a.history ++ bits ++ hRest) tag)).bornMass
            (compileFourierBranch y .inverse w.catPhys.wires (prior.map history) bits
              (a.kraus (Quantum.run (compileCircuit y w.pre)
                (Quantum.run (w.catPhys.wires.reverse.map Gate.H) φ)))))).sum ≤
          ((fourierOutcomes w.catPhys.wires.length).map (fun bits =>
            normSq (compileFourierBranch y .inverse w.catPhys.wires (prior.map history) bits
              (a.kraus (Quantum.run (compileCircuit y w.pre)
                (Quantum.run (w.catPhys.wires.reverse.map Gate.H) φ)))))).sum := by
        apply list_sum_map_le; intro bits _
        exact ih _ _ _ (fun hRest tag => physTerm (a.history ++ bits ++ hRest) tag)
          (fun hRest tag => hterm _ tag) _
      refine hle.trans_eq ?_
      exact normSq_list_sum_compileFourierBranch y .inverse w.catPhys.wires
        (w.wires_eq ▸ w.noY) (prior.map history) _
    have h2 : (((w.core start).instantiate read history).run.map (fun a =>
          ((fourierOutcomes w.catPhys.wires.length).map (fun bits =>
            let h₁ := Single.historyAfter (start + w.catPhys.count) history a.history
            let h₂ := Single.historyAfter (start + w.catPhys.count + w.catPhys.wires.length) h₁ bits
            (selectedAxisDep ws _ h₂ (nextPrior w.catPhys.count w.catPhys.wires.length prior)
              (fun hRest tag => physTerm (a.history ++ bits ++ hRest) tag)).bornMass
              (compileFourierBranch y .inverse w.catPhys.wires (prior.map history) bits
                (a.kraus (Quantum.run (compileCircuit y w.pre)
                  (Quantum.run (w.catPhys.wires.reverse.map Gate.H) φ)))))).sum)).sum ≤
        (((w.core start).instantiate read history).run.map (fun a =>
          normSq (a.kraus (Quantum.run (compileCircuit y w.pre)
            (Quantum.run (w.catPhys.wires.reverse.map Gate.H) φ))))).sum :=
      list_sum_map_le _ _ _ h1
    refine h2.trans_eq ?_
    change (((w.core start).instantiate read history).run).bornMass _ = normSq φ
    rw [AdaptiveCircuit.run_preservesBornMass _ ((w.core start).instantiate_wellFormed read history (w.core_wf start))]
    have hpre_wf : CircuitWellFormed (compileCircuit y w.pre) := by
      have hgen : ∀ (gs : Circuit), (AndGadget.literals gs (.done : Straight n start start)).WellFormed →
          CircuitWellFormed gs := by
        intro gs; induction gs with
        | nil => intro _ g hg; cases hg
        | cons g gs ihg =>
          intro hwf x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hwf.1
          · exact ihg hwf.2 x hx
      apply hgen
      rw [← CatAxis.compile_literalProgram_eq]
      apply ConditionalCatalyst.compile_wellFormed y _ _ (literalProgram_wellFormed w.pre w.pre_wf)
      apply LocalFour.fresh_of_not_mem_straightWires
      intro hm
      exact w.pre_noY (Schedule26Bridge.literalProgram_straightWires w.pre hm)
    rw [Quantum.run_preservesNormSq _ hpre_wf]
    exact Quantum.run_preservesNormSq _ (fun g hg => by
      obtain ⟨u, _, rfl⟩ := List.mem_map.mp hg; trivial) φ

def axisBad {n : Nat} {y : Wire} {read : ConstantBit n → Bool} :
    List (ApproxCatWindow y read) → List Bool → (List Bool → State → ℝ) → State → ℝ
  | [], prior, baseBad, ψ => baseBad prior ψ
  | w :: ws, prior, baseBad, ψ =>
      let χ := Quantum.run w.pre (Quantum.run (w.model.physical.wires.reverse.map Gate.H) ψ)
      normSq (restrictState (fun s => ¬ w.goodPred s) χ) +
        ((fourierOutcomes w.model.physical.wires.length).map (fun bits =>
          axisBad ws (bits.reverse ++ prior) baseBad (w.model.step prior bits ψ))).sum

private theorem list_sum_map_add {α : Type} (xs : List α) (f g : α → ℝ) :
    (xs.map (fun x => f x + g x)).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring

private theorem list_sum_map_mul_left {α : Type} (xs : List α) (r : ℝ) (f : α → ℝ) :
    (xs.map (fun x => r * f x)).sum = r * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih, mul_add]

private theorem list_sum_forall2_normSq_mul {α : Type} (xs : List α) (cs : List ℂ) (f : α → ℝ) (R : ℝ)
    {P : α → ℂ → Prop} (hal : List.Forall₂ P xs cs)
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

private theorem list_sum_forall2_normSq_le {α : Type} (xs : List α) (cs : List ℂ) (f : α → ℝ) (R : ℝ)
    {P : α → ℂ → Prop} (hal : List.Forall₂ P xs cs)
    (hf : ∀ a ∈ xs, ∀ c, P a c → Complex.normSq c * R ≤ f a)
    (hmass : (cs.map Complex.normSq).sum = 1) :
    R ≤ (xs.map f).sum := by
  have h : (cs.map Complex.normSq).sum * R ≤ (xs.map f).sum := by
    clear hmass
    induction hal with
    | nil => simp
    | cons hd tl ih =>
      simp only [List.map_cons, List.sum_cons, add_mul]
      exact add_le_add (hf _ List.mem_cons_self _ hd)
        (ih (fun a ha c hp => hf a (List.mem_cons_of_mem _ ha) c hp))
  rwa [hmass, one_mul] at h

private theorem bornMass_smul_real (I : Instrument) (c : ℂ) (ψ : State) :
    I.bornMass (c • ψ) = Complex.normSq c * I.bornMass ψ := by
  induction I with
  | nil => simp [Instrument.bornMass]
  | cons b bs ih =>
    change normSq (b.kraus (c • ψ)) + Instrument.bornMass bs (c • ψ) =
      Complex.normSq c * (normSq (b.kraus ψ) + Instrument.bornMass bs ψ)
    rw [map_smul, normSq_smul, ih]; ring

/-- Main approximate-catalyst axis theorem: bounds ideal mass from above by `(A₀ * α^L) * physMass + B * axisBad`,
    evaluated ONLY along the pure ideal trajectory. -/
theorem selectedAxisDep_mass_lower {n : Nat} {y : Wire} {read : ConstantBit n → Bool}
    (ws : List (ApproxCatWindow y read)) (start : Nat) (history : Fin start → Bool)
    (prior : List (Fin start))
    (physTerm : List Bool → List Bool → Instrument) (idealTerm : List Bool → Instrument)
    (baseBad : List Bool → State → ℝ)
    (Inv : State → Prop) (eps A₀ B : ℝ) (heps : 0 < eps) (hA₀ : 0 ≤ A₀)
    (hB_step : A₀ * ((1 + eps) ^ 2) ^ ws.length * (2 + eps) * (1 + 1 / eps) ≤ B)
    (hstep_inv : ∀ w ∈ ws, ∀ pr bits φ, Inv φ → Inv (w.model.step pr bits φ))
    (hbad_iso : ∀ w ∈ ws, ∀ φ, Inv φ →
      let χ := Quantum.run w.pre (Quantum.run (w.model.physical.wires.reverse.map Gate.H) φ)
      normSq (w.core_ideal (restrictState (fun s => ¬ w.goodPred s) χ)) ≤
        normSq (restrictState (fun s => ¬ w.goodPred s) χ))
    (hphys_sub : ∀ h tag, SubUnital (physTerm h tag))
    (hterm : ∀ h tag φ, Inv φ → SupportedOn (fun s => s y = false) φ →
      (idealTerm tag).bornMass φ ≤ A₀ * (physTerm h tag).bornMass (Prep y φ) + B * baseBad tag φ)
    (ψ : State) (hψ_inv : Inv ψ) (hψY : SupportedOn (fun s => s y = false) ψ) :
    (idealAxis (ws.map ApproxCatWindow.model) (prior.map history) idealTerm).bornMass ψ ≤
      (A₀ * ((1 + eps) ^ 2) ^ ws.length) *
        (selectedAxisDep ws start history prior physTerm).bornMass (Prep y ψ) +
      B * axisBad ws (prior.map history) baseBad ψ := by
  induction ws generalizing start physTerm ψ with
  | nil =>
    simp only [List.map_nil, idealAxis, List.length_nil, pow_zero, mul_one,
      selectedAxisDep, taggedAxisApprox, List.flatMap_cons, List.flatMap_nil, List.append_nil, axisBad]
    rw [prefixed_mass ⟨[], LinearMap.id⟩ _ (Prep y ψ)]
    exact hterm List.nil (prior.map history) ψ hψ_inv hψY
  | cons w ws ih =>
    set α₁ : ℝ := 1 + eps
    set β₁ : ℝ := 1 + 1 / eps
    set α : ℝ := α₁ ^ 2
    have hα₁_pos : 0 < α₁ := by dsimp [α₁]; linarith
    have hα₁_ge : 1 ≤ α₁ := by dsimp [α₁]; linarith
    have hα_ge : 1 ≤ α := by dsimp [α]; nlinarith
    have hβ₁_nonneg : 0 ≤ β₁ := by dsimp [β₁]; positivity
    have hpow_ge : α ^ ws.length ≤ α ^ (w :: ws).length := by
      simp only [List.length_cons, pow_succ]
      exact le_mul_of_one_le_right (pow_nonneg (by linarith) _) hα_ge
    have hB_tail : A₀ * α ^ ws.length * (2 + eps) * β₁ ≤ B := by
      refine le_trans ?_ hB_step
      have h1 : A₀ * α ^ ws.length ≤ A₀ * α ^ (w :: ws).length := mul_le_mul_of_nonneg_left hpow_ge hA₀
      have h2 : 0 ≤ (2 + eps) * β₁ := by positivity
      calc A₀ * α ^ ws.length * (2 + eps) * β₁
          = (A₀ * α ^ ws.length) * ((2 + eps) * β₁) := by ring
        _ ≤ (A₀ * α ^ (w :: ws).length) * ((2 + eps) * β₁) := mul_le_mul_of_nonneg_right h1 h2
        _ = A₀ * α ^ (w :: ws).length * (2 + eps) * β₁ := by ring
    have hH_nw : y ∉ circuitWires (w.model.physical.wires.reverse.map Gate.H) := by
      intro hm
      simp only [circuitWires, List.mem_flatMap, List.mem_map] at hm
      obtain ⟨g, ⟨v, hv, rfl⟩, hwg⟩ := hm
      simp only [gateWires, List.mem_singleton] at hwg
      exact w.noY (List.mem_reverse.mp (hwg ▸ hv))
    let χ : State := Quantum.run w.pre (Quantum.run (w.model.physical.wires.reverse.map Gate.H) ψ)
    let χ_good : State := restrictState w.goodPred χ
    let χ_bad : State := restrictState (fun s => ¬ w.goodPred s) χ
    have hχ_split : χ = χ_good + χ_bad := (restrictState_add_compl w.goodPred χ).symm
    have hχY : SupportedOn (fun s => s y = false) χ :=
      LocalFour.circuit_frame y w.pre w.pre_noY _ (LocalFour.circuit_frame y _ hH_nw ψ hψY)
    have hgoodY : SupportedOn (fun s => s y = false) χ_good :=
      restrictState_preserves w.goodPred _ χ hχY
    have hbadY : SupportedOn (fun s => s y = false) χ_bad :=
      restrictState_preserves (fun s => ¬ w.goodPred s) _ χ hχY
    have hgood_sup : SupportedOn w.goodPred χ_good := restrictState_supportedOn w.goodPred χ
    have hpreH_prep : Quantum.run (compileCircuit y w.pre)
        (Quantum.run (w.catPhys.wires.reverse.map Gate.H) (Prep y ψ)) = Prep y χ := by
      rw [w.wires_eq, prep_circuit y _ hH_nw ψ,
        compileCircuit_prep y w.pre w.pre_noY _ (LocalFour.circuit_frame y _ hH_nw ψ hψY)]
    -- Step 1: apply IH to each ideal step `φ_full bits = w.model.step (prior.map history) bits ψ`
    --         for EVERY branch `a` of `w.core start` with scalar `c`.
    obtain ⟨cs, hal, hmass⟩ := w.catCoherent start history
    let tailPhys (a : InstrumentBranch) (bits : List Bool) : Instrument :=
      let h₁ := Single.historyAfter (start + w.catPhys.count) history a.history
      let h₂ := Single.historyAfter (start + w.catPhys.count + w.catPhys.wires.length) h₁ bits
      selectedAxisDep ws _ h₂ (nextPrior w.catPhys.count w.catPhys.wires.length prior)
        (fun hRest tag => physTerm (a.history ++ bits ++ hRest) tag)
    let stepPhys : Instrument :=
      (((w.core start).instantiate read history).run).flatMap (fun a =>
        (fourierOutcomes w.catPhys.wires.length).flatMap (fun bits =>
          (tailPhys a bits).map
            (a.seq ⟨bits, compileFourierBranch y .inverse w.catPhys.wires (prior.map history) bits⟩).seq))
    have hstepPhys_mass (φ : State) :
        stepPhys.bornMass φ =
          (((w.core start).instantiate read history).run.map (fun a =>
            ((fourierOutcomes w.catPhys.wires.length).map (fun bits =>
              (tailPhys a bits).bornMass
                (compileFourierBranch y .inverse w.catPhys.wires (prior.map history) bits
                  (a.kraus φ)))).sum)).sum := by
      simp only [stepPhys, flat_mass, prefixed_mass, List.flatMap_map, List.map_map,
        Function.comp_def, InstrumentBranch.seq, LinearMap.comp_apply]
    have hstepPhys_eq : (selectedAxisDep (w :: ws) start history prior physTerm).bornMass (Prep y ψ) =
        stepPhys.bornMass (Prep y χ) := by
      rw [selectedAxisDep_cons_mass, hstepPhys_mass, hpreH_prep]
    have hstepPhys_sub : SubUnital stepPhys := by
      intro φ
      rw [hstepPhys_mass]
      have h1 : ∀ a ∈ ((w.core start).instantiate read history).run,
          ((fourierOutcomes w.catPhys.wires.length).map (fun bits =>
            (tailPhys a bits).bornMass
              (compileFourierBranch y .inverse w.catPhys.wires (prior.map history) bits
                (a.kraus φ)))).sum ≤ normSq (a.kraus φ) := by
        intro a _
        have hle : ((fourierOutcomes w.catPhys.wires.length).map (fun bits =>
            (tailPhys a bits).bornMass
              (compileFourierBranch y .inverse w.catPhys.wires (prior.map history) bits
                (a.kraus φ)))).sum ≤
            ((fourierOutcomes w.catPhys.wires.length).map (fun bits =>
              normSq (compileFourierBranch y .inverse w.catPhys.wires (prior.map history) bits
                (a.kraus φ)))).sum :=
          list_sum_map_le _ _ _ (fun bits _ =>
            selectedAxisDep_subUnital ws _ _ _ _ (fun _ tag => hphys_sub _ tag) _)
        exact hle.trans_eq (normSq_list_sum_compileFourierBranch y .inverse w.catPhys.wires
          (w.wires_eq ▸ w.noY) (prior.map history) _)
      exact (list_sum_map_le _ _ _ h1).trans_eq
        (AdaptiveCircuit.run_preservesBornMass _ ((w.core start).instantiate_wellFormed read history (w.core_wf start)) φ)
    -- Step 2: bound `idealAxis` in terms of `stepPhys.bornMass (Prep y χ_good)` + `normSq χ_bad`
    have hstep_full :
        (idealAxis ((w :: ws).map ApproxCatWindow.model) (prior.map history) idealTerm).bornMass ψ ≤
          (A₀ * α ^ ws.length * α₁) * stepPhys.bornMass (Prep y χ_good) +
          (A₀ * α ^ ws.length * β₁) * normSq χ_bad +
          B * ((fourierOutcomes w.model.physical.wires.length).map (fun bits =>
            axisBad ws (bits.reverse ++ prior.map history) baseBad (w.model.step (prior.map history) bits ψ))).sum := by
      -- For each branch `a` with scalar `c`:
      have hper_a : ∀ a ∈ ((w.core start).instantiate read history).run, ∀ c : ℂ,
          (∀ s, w.goodPred s → a.kraus (Prep y (ket s)) = c • Prep y (w.core_ideal (ket s))) →
          Complex.normSq c *
            ((idealAxis ((w :: ws).map ApproxCatWindow.model) (prior.map history) idealTerm).bornMass ψ -
              (A₀ * α ^ ws.length * β₁) * normSq χ_bad -
              B * ((fourierOutcomes w.model.physical.wires.length).map (fun bits =>
                axisBad ws (bits.reverse ++ prior.map history) baseBad (w.model.step (prior.map history) bits ψ))).sum) ≤
          (A₀ * α ^ ws.length * α₁) *
            ((fourierOutcomes w.catPhys.wires.length).map (fun bits =>
              (tailPhys a bits).bornMass
                (compileFourierBranch y .inverse w.catPhys.wires (prior.map history) bits
                  (a.kraus (Prep y χ_good))))).sum := by
        intro a ha_mem c ha
        have ha_len : a.history.length = w.catPhys.count := by
          have h := straight_history_length _ read history a ha_mem; omega
        have ha_good : a.kraus (Prep y χ_good) = c • Prep y (w.core_ideal χ_good) :=
          catBranch_on_supported ha χ_good hgood_sup
        have hper_bits : ∀ bits ∈ fourierOutcomes w.model.physical.wires.length,
            Complex.normSq c *
              (idealAxis (ws.map ApproxCatWindow.model) (bits.reverse ++ prior.map history) idealTerm).bornMass
                (w.model.step (prior.map history) bits ψ) ≤
            (A₀ * α ^ ws.length * α₁) *
              (tailPhys a bits).bornMass
                (compileFourierBranch y .inverse w.catPhys.wires (prior.map history) bits
                  (a.kraus (Prep y χ_good))) +
            Complex.normSq c *
              ((A₀ * α ^ ws.length * β₁) *
                normSq (fourierBranch .inverse w.model.physical.wires (prior.map history) bits (w.core_ideal χ_bad)) +
               B * axisBad ws (bits.reverse ++ prior.map history) baseBad (w.model.step (prior.map history) bits ψ)) := by
          intro bits hb
          let φ_full := w.model.step (prior.map history) bits ψ
          let φ_good := fourierBranch .inverse w.model.physical.wires (prior.map history) bits (w.core_ideal χ_good)
          let φ_bad := fourierBranch .inverse w.model.physical.wires (prior.map history) bits (w.core_ideal χ_bad)
          have hφ_eq : φ_full = φ_good + φ_bad := by
            change fourierBranch .inverse w.model.physical.wires (prior.map history) bits
                (w.model.ideal (Quantum.run (w.model.physical.wires.reverse.map Gate.H) ψ)) = _
            rw [w.ideal_eq]; change fourierBranch _ _ _ _ (w.core_ideal χ) = _
            rw [hχ_split, map_add, map_add]
          have hφY : SupportedOn (fun s => s y = false) φ_full := by
            have h1 := compileFourierBranch_prep y .inverse w.model.physical.wires w.noY
              (prior.map history) bits (w.core_ideal χ) (w.core_idealY χ hχY)
            change SupportedOn _ (fourierBranch _ _ _ _ (w.model.ideal _))
            rw [w.ideal_eq]; exact h1.2
          have hih := ih (start + w.catPhys.count + w.catPhys.wires.length)
            (Single.historyAfter (start + w.catPhys.count + w.catPhys.wires.length)
              (Single.historyAfter (start + w.catPhys.count) history a.history) bits)
            (nextPrior w.catPhys.count w.catPhys.wires.length prior)
            (fun hRest tag => physTerm (a.history ++ bits ++ hRest) tag)
            hB_tail
            (fun v hv => hstep_inv v (List.mem_cons_of_mem _ hv))
            (fun v hv => hbad_iso v (List.mem_cons_of_mem _ hv))
            (fun _ tag => hphys_sub _ tag)
            (fun _ tag => hterm _ tag)
            φ_full (hstep_inv w List.mem_cons_self _ bits ψ hψ_inv) hφY
          have hnp : (nextPrior w.catPhys.count w.catPhys.wires.length prior).map
              (Single.historyAfter (start + w.catPhys.count + w.catPhys.wires.length)
                (Single.historyAfter (start + w.catPhys.count) history a.history) bits) =
              bits.reverse ++ prior.map history :=
            nextPrior_map _ _ _ _ _ _ ha_len (w.wires_eq ▸ (fourierOutcomes_mem _ _).mp hb)
          rw [hnp] at hih
          have hsplit_phys : (tailPhys a bits).bornMass (Prep y φ_full) ≤
              α₁ * (tailPhys a bits).bornMass (Prep y φ_good) + β₁ * normSq φ_bad := by
            rw [hφ_eq, map_add]
            have hu := instrument_mass_upper (tailPhys a bits) (Prep y φ_good) (Prep y φ_bad) eps heps
            have hsub : (tailPhys a bits).bornMass (Prep y φ_bad) ≤ normSq (Prep y φ_bad) :=
              selectedAxisDep_subUnital ws _ _ _ _ (fun _ tag => hphys_sub _ tag) (Prep y φ_bad)
            rw [LocalFour.normSq_prep] at hsub
            have hm := mul_le_mul_of_nonneg_left hsub hβ₁_nonneg
            linarith
          have hcfb : compileFourierBranch y .inverse w.catPhys.wires (prior.map history) bits
              (a.kraus (Prep y χ_good)) = c • Prep y φ_good := by
            rw [ha_good, map_smul, w.wires_eq]
            have hfb := compileFourierBranch_prep y .inverse w.model.physical.wires w.noY
              (prior.map history) bits (w.core_ideal χ_good) (w.core_idealY χ_good hgoodY)
            rw [hfb.1]
          rw [hcfb, bornMass_smul_real]
          have hA_nn : 0 ≤ A₀ * α ^ ws.length := mul_nonneg hA₀ (pow_nonneg (by linarith) _)
          have hnc_nn : 0 ≤ Complex.normSq c := Complex.normSq_nonneg c
          have hcomb : (idealAxis (ws.map ApproxCatWindow.model) (bits.reverse ++ prior.map history) idealTerm).bornMass φ_full ≤
              (A₀ * α ^ ws.length * α₁) * (tailPhys a bits).bornMass (Prep y φ_good) +
              (A₀ * α ^ ws.length * β₁) * normSq φ_bad +
              B * axisBad ws (bits.reverse ++ prior.map history) baseBad φ_full := by
            have hm := mul_le_mul_of_nonneg_left hsplit_phys hA_nn
            linarith
          have hm2 := mul_le_mul_of_nonneg_left hcomb hnc_nn
          linarith
        have hsum_bits := list_sum_map_le _ _ _ hper_bits
        simp only [List.map_cons, idealAxis_cons_mass]
        rw [list_sum_map_mul_left, list_sum_map_add, list_sum_map_mul_left,
          list_sum_map_mul_left, list_sum_map_add, list_sum_map_mul_left,
          list_sum_map_mul_left] at hsum_bits
        have hfb_bad : ((fourierOutcomes w.model.physical.wires.length).map (fun bits =>
            normSq (fourierBranch .inverse w.model.physical.wires (prior.map history) bits (w.core_ideal χ_bad)))).sum ≤
            normSq χ_bad := by
          rw [normSq_list_sum_fourierBranch]
          exact hbad_iso w List.mem_cons_self ψ hψ_inv
        have hA_nn : 0 ≤ A₀ * α ^ ws.length * β₁ := by positivity
        have hnc_nn : 0 ≤ Complex.normSq c := Complex.normSq_nonneg c
        have hmb : Complex.normSq c * (A₀ * α ^ ws.length * β₁ *
            ((fourierOutcomes w.model.physical.wires.length).map (fun bits =>
              normSq (fourierBranch .inverse w.model.physical.wires (prior.map history) bits (w.core_ideal χ_bad)))).sum) ≤
            Complex.normSq c * (A₀ * α ^ ws.length * β₁ * normSq χ_bad) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfb_bad hA_nn) hnc_nn
        rw [congrArg (fun l => fourierOutcomes l.length) w.wires_eq, mul_sub, mul_sub]
        linarith
      have htot := list_sum_forall2_normSq_le _ cs _ _ hal hper_a hmass
      rw [list_sum_map_mul_left] at htot
      rw [hstepPhys_mass]
      linarith
    -- Step 3: relate `stepPhys.bornMass (Prep y χ_good)` to `stepPhys.bornMass (Prep y χ)`
    have hgood_to_full : stepPhys.bornMass (Prep y χ_good) ≤
        α₁ * stepPhys.bornMass (Prep y χ) + β₁ * normSq χ_bad := by
      have hgs : χ_good = χ + (-χ_bad) := by rw [hχ_split]; abel
      rw [hgs, map_add, map_neg]
      have hu := instrument_mass_upper stepPhys (Prep y χ) (-(Prep y χ_bad)) eps heps
      rw [instrument_mass_neg] at hu
      have hsub := hstepPhys_sub (Prep y χ_bad)
      rw [LocalFour.normSq_prep] at hsub
      have hm := mul_le_mul_of_nonneg_left hsub hβ₁_nonneg
      linarith
    have hA_nn : 0 ≤ A₀ * α ^ ws.length * α₁ := mul_nonneg (mul_nonneg hA₀ (pow_nonneg (by linarith) _)) hα₁_pos.le
    have hm_g := mul_le_mul_of_nonneg_left hgood_to_full hA_nn
    have hB_err : A₀ * α ^ ws.length * α₁ * β₁ + A₀ * α ^ ws.length * β₁ ≤ B := by
      have heq : A₀ * α ^ ws.length * α₁ * β₁ + A₀ * α ^ ws.length * β₁ =
          A₀ * α ^ ws.length * (2 + eps) * β₁ := by dsimp [α₁]; ring
      rw [heq]; exact hB_tail
    have hnb_nn : 0 ≤ normSq χ_bad := ApproximatePhase34.mass_nonneg _
    have hm_bad := mul_le_mul_of_nonneg_right hB_err hnb_nn
    have hpow_succ : A₀ * α ^ ws.length * α₁ * α₁ = A₀ * α ^ (w :: ws).length := by
      simp only [List.length_cons, pow_succ, α]; ring
    rw [hstepPhys_eq]
    change _ ≤ (A₀ * α ^ (w :: ws).length) * stepPhys.bornMass (Prep y χ) +
      B * (normSq χ_bad + ((fourierOutcomes w.model.physical.wires.length).map (fun bits =>
        axisBad ws (bits.reverse ++ prior.map history) baseBad (w.model.step (prior.map history) bits ψ))).sum)
    have hm_g' : A₀ * α ^ ws.length * α₁ * stepPhys.bornMass (Prep y χ_good) ≤
        (A₀ * α ^ (w :: ws).length) * stepPhys.bornMass (Prep y χ) +
        (A₀ * α ^ ws.length * α₁ * β₁) * normSq χ_bad := by
      have heq1 : A₀ * α ^ ws.length * α₁ * (α₁ * stepPhys.bornMass (Prep y χ) + β₁ * normSq χ_bad) =
          (A₀ * α ^ (w :: ws).length) * stepPhys.bornMass (Prep y χ) +
          (A₀ * α ^ ws.length * α₁ * β₁) * normSq χ_bad := by
        rw [← hpow_succ]; ring
      linarith
    have hm_bad' : (A₀ * α ^ ws.length * α₁ * β₁) * normSq χ_bad +
        (A₀ * α ^ ws.length * β₁) * normSq χ_bad ≤ B * normSq χ_bad := by linarith
    have hmul_split : B * (normSq χ_bad + ((fourierOutcomes w.model.physical.wires.length).map (fun bits =>
        axisBad ws (bits.reverse ++ prior.map history) baseBad (w.model.step (prior.map history) bits ψ))).sum) =
        B * normSq χ_bad + B * ((fourierOutcomes w.model.physical.wires.length).map (fun bits =>
        axisBad ws (bits.reverse ++ prior.map history) baseBad (w.model.step (prior.map history) bits ψ))).sum :=
      mul_add _ _ _
    linarith

/-- Exact head step (`χ_bad = 0`, zero loss, no multiplier increase): used for `first20ApproxWin`. -/
theorem selectedAxisDep_cons_exact {n : Nat} {y : Wire} {read : ConstantBit n → Bool}
    (w : ApproxCatWindow y read) (ws : List (ApproxCatWindow y read))
    (start : Nat) (history : Fin start → Bool) (prior : List (Fin start))
    (physTerm : List Bool → List Bool → Instrument) (idealTerm : List Bool → Instrument)
    (tailBad : List Bool → ℝ) (A B : ℝ)
    (ψ : State) (hψY : SupportedOn (fun s => s y = false) ψ)
    (hgood : SupportedOn w.goodPred
      (Quantum.run w.pre (Quantum.run (w.model.physical.wires.reverse.map Gate.H) ψ)))
    (htail : ∀ (a : InstrumentBranch) (bits : List Bool),
      a ∈ ((w.core start).instantiate read history).run →
      bits ∈ fourierOutcomes w.model.physical.wires.length →
      let h₁ := Single.historyAfter (start + w.catPhys.count) history a.history
      let h₂ := Single.historyAfter (start + w.catPhys.count + w.catPhys.wires.length) h₁ bits
      (idealAxis (ws.map ApproxCatWindow.model) (bits.reverse ++ prior.map history) idealTerm).bornMass
        (w.model.step (prior.map history) bits ψ) ≤
      A * (selectedAxisDep ws _ h₂ (nextPrior w.catPhys.count w.catPhys.wires.length prior)
        (fun hRest tag => physTerm (a.history ++ bits ++ hRest) tag)).bornMass
          (Prep y (w.model.step (prior.map history) bits ψ)) +
      B * tailBad bits) :
    (idealAxis ((w :: ws).map ApproxCatWindow.model) (prior.map history) idealTerm).bornMass ψ ≤
      A * (selectedAxisDep (w :: ws) start history prior physTerm).bornMass (Prep y ψ) +
      B * ((fourierOutcomes w.model.physical.wires.length).map tailBad).sum := by
  have hH_nw : y ∉ circuitWires (w.model.physical.wires.reverse.map Gate.H) := by
    intro hm
    simp only [circuitWires, List.mem_flatMap, List.mem_map] at hm
    obtain ⟨g, ⟨v, hv, rfl⟩, hwg⟩ := hm
    simp only [gateWires, List.mem_singleton] at hwg
    exact w.noY (List.mem_reverse.mp (hwg ▸ hv))
  let χ : State := Quantum.run w.pre (Quantum.run (w.model.physical.wires.reverse.map Gate.H) ψ)
  have hχY : SupportedOn (fun s => s y = false) χ :=
    LocalFour.circuit_frame y w.pre w.pre_noY _ (LocalFour.circuit_frame y _ hH_nw ψ hψY)
  have hpreH_prep : Quantum.run (compileCircuit y w.pre)
      (Quantum.run (w.catPhys.wires.reverse.map Gate.H) (Prep y ψ)) = Prep y χ := by
    rw [w.wires_eq, prep_circuit y _ hH_nw ψ,
      compileCircuit_prep y w.pre w.pre_noY _ (LocalFour.circuit_frame y _ hH_nw ψ hψY)]
  obtain ⟨cs, hal, hmass⟩ := w.catCoherent start history
  rw [selectedAxisDep_cons_mass, hpreH_prep]
  simp only [List.map_cons, idealAxis_cons_mass]
  have hper_a : ∀ a ∈ ((w.core start).instantiate read history).run, ∀ c : ℂ,
      (∀ s, w.goodPred s → a.kraus (Prep y (ket s)) = c • Prep y (w.core_ideal (ket s))) →
      Complex.normSq c *
        (((fourierOutcomes w.model.physical.wires.length).map (fun bits =>
            (idealAxis (ws.map ApproxCatWindow.model) (bits.reverse ++ prior.map history) idealTerm).bornMass
              (w.model.step (prior.map history) bits ψ))).sum -
         B * ((fourierOutcomes w.model.physical.wires.length).map tailBad).sum) ≤
      A * ((fourierOutcomes w.catPhys.wires.length).map (fun bits =>
        let h₁ := Single.historyAfter (start + w.catPhys.count) history a.history
        let h₂ := Single.historyAfter (start + w.catPhys.count + w.catPhys.wires.length) h₁ bits
        (selectedAxisDep ws _ h₂ (nextPrior w.catPhys.count w.catPhys.wires.length prior)
          (fun hRest tag => physTerm (a.history ++ bits ++ hRest) tag)).bornMass
          (compileFourierBranch y .inverse w.catPhys.wires (prior.map history) bits
            (a.kraus (Prep y χ))))).sum := by
    intro a ha_mem c ha
    have ha_χ : a.kraus (Prep y χ) = c • Prep y (w.core_ideal χ) := catBranch_on_supported ha χ hgood
    have hper_bits : ∀ bits ∈ fourierOutcomes w.model.physical.wires.length,
        Complex.normSq c *
          (idealAxis (ws.map ApproxCatWindow.model) (bits.reverse ++ prior.map history) idealTerm).bornMass
            (w.model.step (prior.map history) bits ψ) ≤
        A * (let h₁ := Single.historyAfter (start + w.catPhys.count) history a.history
             let h₂ := Single.historyAfter (start + w.catPhys.count + w.catPhys.wires.length) h₁ bits
             (selectedAxisDep ws _ h₂ (nextPrior w.catPhys.count w.catPhys.wires.length prior)
               (fun hRest tag => physTerm (a.history ++ bits ++ hRest) tag)).bornMass
               (compileFourierBranch y .inverse w.catPhys.wires (prior.map history) bits
                 (a.kraus (Prep y χ)))) +
        Complex.normSq c * (B * tailBad bits) := by
      intro bits hb
      have hfb := compileFourierBranch_prep y .inverse w.model.physical.wires w.noY
        (prior.map history) bits (w.core_ideal χ) (w.core_idealY χ hχY)
      have hcfb : compileFourierBranch y .inverse w.catPhys.wires (prior.map history) bits (a.kraus (Prep y χ)) =
          c • Prep y (w.model.step (prior.map history) bits ψ) := by
        rw [ha_χ, map_smul, w.wires_eq, hfb.1]
        change c • Prep y (fourierBranch .inverse w.model.physical.wires (prior.map history) bits (w.core_ideal χ)) =
          c • Prep y (fourierBranch .inverse w.model.physical.wires (prior.map history) bits
            (w.model.ideal (Quantum.run (w.model.physical.wires.reverse.map Gate.H) ψ)))
        rw [w.ideal_eq]; rfl
      rw [hcfb, bornMass_smul_real]
      have ht := htail a bits ha_mem hb
      have hm := mul_le_mul_of_nonneg_left ht (Complex.normSq_nonneg c)
      linarith
    have hs := list_sum_map_le _ _ _ hper_bits
    rw [list_sum_map_mul_left, list_sum_map_add, list_sum_map_mul_left,
      list_sum_map_mul_left, list_sum_map_mul_left] at hs
    rw [congrArg (fun l => fourierOutcomes l.length) w.wires_eq, mul_sub]
    linarith
  have htot := list_sum_forall2_normSq_le _ cs _ _ hal hper_a hmass
  rw [list_sum_map_mul_left] at htot
  linarith

private theorem list_sum_forall2_normSq_ge {α : Type} (xs : List α) (cs : List ℂ) (f : α → ℝ) (R : ℝ)
    {P : α → ℂ → Prop} (hal : List.Forall₂ P xs cs)
    (hf : ∀ a ∈ xs, ∀ c, P a c → f a ≤ Complex.normSq c * R)
    (hmass : (cs.map Complex.normSq).sum = 1) :
    (xs.map f).sum ≤ R := by
  have h : (xs.map f).sum ≤ (cs.map Complex.normSq).sum * R := by
    clear hmass
    induction hal with
    | nil => simp
    | cons hd tl ih =>
      simp only [List.map_cons, List.sum_cons, add_mul]
      exact add_le_add (hf _ List.mem_cons_self _ hd)
        (ih (fun a ha c hp => hf a (List.mem_cons_of_mem _ ha) c hp))
  rwa [hmass, one_mul] at h

/-- Upper-bound mirror of `selectedAxisDep_mass_lower`: bounds physical event mass by ideal event mass + `axisBad`. -/
theorem selectedAxisDep_mass_upper {n : Nat} {y : Wire} {read : ConstantBit n → Bool}
    (ws : List (ApproxCatWindow y read)) (start : Nat) (history : Fin start → Bool)
    (prior : List (Fin start))
    (physTerm : List Bool → List Bool → Instrument) (idealTerm : List Bool → Instrument)
    (baseBad : List Bool → State → ℝ)
    (Inv : State → Prop) (eps A₀ B₀ : ℝ) (heps : 0 < eps) (hA₀ : 0 ≤ A₀) (hB₀_nn : 0 ≤ B₀)
    (hB_step : (2 + eps) * (1 + 1 / eps) ≤ B₀)
    (hstep_inv : ∀ w ∈ ws, ∀ pr bits φ, Inv φ → Inv (w.model.step pr bits φ))
    (hbad_iso : ∀ w ∈ ws, ∀ φ, Inv φ →
      let χ := Quantum.run w.pre (Quantum.run (w.model.physical.wires.reverse.map Gate.H) φ)
      normSq (w.core_ideal (restrictState (fun s => ¬ w.goodPred s) χ)) ≤
        normSq (restrictState (fun s => ¬ w.goodPred s) χ))
    (hphys_sub : ∀ h tag, SubUnital (physTerm h tag))
    (hterm : ∀ h tag φ, Inv φ → SupportedOn (fun s => s y = false) φ →
      (physTerm h tag).bornMass (Prep y φ) ≤ A₀ * (idealTerm tag).bornMass φ + B₀ * baseBad tag φ)
    (ψ : State) (hψ_inv : Inv ψ) (hψY : SupportedOn (fun s => s y = false) ψ) :
    (selectedAxisDep ws start history prior physTerm).bornMass (Prep y ψ) ≤
      (A₀ * ((1 + eps) ^ 2) ^ ws.length) *
        (idealAxis (ws.map ApproxCatWindow.model) (prior.map history) idealTerm).bornMass ψ +
      (B₀ * ((1 + eps) ^ 2) ^ ws.length) * axisBad ws (prior.map history) baseBad ψ := by
  induction ws generalizing start physTerm ψ with
  | nil =>
    simp only [List.map_nil, idealAxis, List.length_nil, pow_zero, mul_one,
      selectedAxisDep, taggedAxisApprox, List.flatMap_cons, List.flatMap_nil, List.append_nil, axisBad]
    rw [prefixed_mass ⟨[], LinearMap.id⟩ _ (Prep y ψ)]
    exact hterm List.nil (prior.map history) ψ hψ_inv hψY
  | cons w ws ih =>
    set α₁ : ℝ := 1 + eps
    set β₁ : ℝ := 1 + 1 / eps
    set α : ℝ := α₁ ^ 2
    have hα₁_pos : 0 < α₁ := by dsimp [α₁]; linarith
    have hα₁_ge : 1 ≤ α₁ := by dsimp [α₁]; linarith
    have hα_ge : 1 ≤ α := by dsimp [α]; nlinarith
    have hβ₁_nonneg : 0 ≤ β₁ := by dsimp [β₁]; positivity
    have hH_nw : y ∉ circuitWires (w.model.physical.wires.reverse.map Gate.H) := by
      intro hm
      simp only [circuitWires, List.mem_flatMap, List.mem_map] at hm
      obtain ⟨g, ⟨v, hv, rfl⟩, hwg⟩ := hm
      simp only [gateWires, List.mem_singleton] at hwg
      exact w.noY (List.mem_reverse.mp (hwg ▸ hv))
    let χ : State := Quantum.run w.pre (Quantum.run (w.model.physical.wires.reverse.map Gate.H) ψ)
    let χ_good : State := restrictState w.goodPred χ
    let χ_bad : State := restrictState (fun s => ¬ w.goodPred s) χ
    have hχ_split : χ = χ_good + χ_bad := (restrictState_add_compl w.goodPred χ).symm
    have hχY : SupportedOn (fun s => s y = false) χ :=
      LocalFour.circuit_frame y w.pre w.pre_noY _ (LocalFour.circuit_frame y _ hH_nw ψ hψY)
    have hgoodY : SupportedOn (fun s => s y = false) χ_good :=
      restrictState_preserves w.goodPred _ χ hχY
    have hgood_sup : SupportedOn w.goodPred χ_good := restrictState_supportedOn w.goodPred χ
    have hpreH_prep : Quantum.run (compileCircuit y w.pre)
        (Quantum.run (w.catPhys.wires.reverse.map Gate.H) (Prep y ψ)) = Prep y χ := by
      rw [w.wires_eq, prep_circuit y _ hH_nw ψ,
        compileCircuit_prep y w.pre w.pre_noY _ (LocalFour.circuit_frame y _ hH_nw ψ hψY)]
    obtain ⟨cs, hal, hmass⟩ := w.catCoherent start history
    let tailPhys (a : InstrumentBranch) (bits : List Bool) : Instrument :=
      let h₁ := Single.historyAfter (start + w.catPhys.count) history a.history
      let h₂ := Single.historyAfter (start + w.catPhys.count + w.catPhys.wires.length) h₁ bits
      selectedAxisDep ws _ h₂ (nextPrior w.catPhys.count w.catPhys.wires.length prior)
        (fun hRest tag => physTerm (a.history ++ bits ++ hRest) tag)
    let stepPhys : Instrument :=
      (((w.core start).instantiate read history).run).flatMap (fun a =>
        (fourierOutcomes w.catPhys.wires.length).flatMap (fun bits =>
          (tailPhys a bits).map
            (a.seq ⟨bits, compileFourierBranch y .inverse w.catPhys.wires (prior.map history) bits⟩).seq))
    have hstepPhys_mass (φ : State) :
        stepPhys.bornMass φ =
          (((w.core start).instantiate read history).run.map (fun a =>
            ((fourierOutcomes w.catPhys.wires.length).map (fun bits =>
              (tailPhys a bits).bornMass
                (compileFourierBranch y .inverse w.catPhys.wires (prior.map history) bits
                  (a.kraus φ)))).sum)).sum := by
      simp only [stepPhys, flat_mass, prefixed_mass, List.flatMap_map, List.map_map,
        Function.comp_def, InstrumentBranch.seq, LinearMap.comp_apply]
    have hstepPhys_eq : (selectedAxisDep (w :: ws) start history prior physTerm).bornMass (Prep y ψ) =
        stepPhys.bornMass (Prep y χ) := by
      rw [selectedAxisDep_cons_mass, hstepPhys_mass, hpreH_prep]
    have hstepPhys_sub : SubUnital stepPhys := by
      intro φ
      rw [hstepPhys_mass]
      have h1 : ∀ a ∈ ((w.core start).instantiate read history).run,
          ((fourierOutcomes w.catPhys.wires.length).map (fun bits =>
            (tailPhys a bits).bornMass
              (compileFourierBranch y .inverse w.catPhys.wires (prior.map history) bits
                (a.kraus φ)))).sum ≤ normSq (a.kraus φ) := by
        intro a _
        have hle : ((fourierOutcomes w.catPhys.wires.length).map (fun bits =>
            (tailPhys a bits).bornMass
              (compileFourierBranch y .inverse w.catPhys.wires (prior.map history) bits
                (a.kraus φ)))).sum ≤
            ((fourierOutcomes w.catPhys.wires.length).map (fun bits =>
              normSq (compileFourierBranch y .inverse w.catPhys.wires (prior.map history) bits
                (a.kraus φ)))).sum :=
          list_sum_map_le _ _ _ (fun bits _ =>
            selectedAxisDep_subUnital ws _ _ _ _ (fun _ tag => hphys_sub _ tag) _)
        exact hle.trans_eq (normSq_list_sum_compileFourierBranch y .inverse w.catPhys.wires
          (w.wires_eq ▸ w.noY) (prior.map history) _)
      exact (list_sum_map_le _ _ _ h1).trans_eq
        (AdaptiveCircuit.run_preservesBornMass _ ((w.core start).instantiate_wellFormed read history (w.core_wf start)) φ)
    -- Step 1: bound `stepPhys.bornMass (Prep y χ)` in terms of `stepPhys.bornMass (Prep y χ_good)` + `normSq χ_bad`
    have hfull_to_good : stepPhys.bornMass (Prep y χ) ≤
        α₁ * stepPhys.bornMass (Prep y χ_good) + β₁ * normSq χ_bad := by
      rw [hχ_split, map_add]
      have hu := instrument_mass_upper stepPhys (Prep y χ_good) (Prep y χ_bad) eps heps
      have hsub := hstepPhys_sub (Prep y χ_bad)
      rw [LocalFour.normSq_prep] at hsub
      have hm := mul_le_mul_of_nonneg_left hsub hβ₁_nonneg
      linarith
    -- Step 2: bound `stepPhys.bornMass (Prep y χ_good)` using `ih`
    have hgood_bound :
        stepPhys.bornMass (Prep y χ_good) ≤
          (A₀ * α ^ ws.length * α₁) *
            (idealAxis ((w :: ws).map ApproxCatWindow.model) (prior.map history) idealTerm).bornMass ψ +
          (B₀ * α ^ ws.length * α₁) *
            ((fourierOutcomes w.model.physical.wires.length).map (fun bits =>
              axisBad ws (bits.reverse ++ prior.map history) baseBad (w.model.step (prior.map history) bits ψ))).sum +
          β₁ * normSq χ_bad := by
      have hper_a : ∀ a ∈ ((w.core start).instantiate read history).run, ∀ c : ℂ,
          (∀ s, w.goodPred s → a.kraus (Prep y (ket s)) = c • Prep y (w.core_ideal (ket s))) →
          ((fourierOutcomes w.catPhys.wires.length).map (fun bits =>
            (tailPhys a bits).bornMass
              (compileFourierBranch y .inverse w.catPhys.wires (prior.map history) bits
                (a.kraus (Prep y χ_good))))).sum ≤
          Complex.normSq c *
            ((A₀ * α ^ ws.length * α₁) *
              (idealAxis ((w :: ws).map ApproxCatWindow.model) (prior.map history) idealTerm).bornMass ψ +
            (B₀ * α ^ ws.length * α₁) *
              ((fourierOutcomes w.model.physical.wires.length).map (fun bits =>
                axisBad ws (bits.reverse ++ prior.map history) baseBad (w.model.step (prior.map history) bits ψ))).sum +
            β₁ * normSq χ_bad) := by
        intro a ha_mem c ha
        have ha_len : a.history.length = w.catPhys.count := by
          have h := straight_history_length _ read history a ha_mem; omega
        have ha_good : a.kraus (Prep y χ_good) = c • Prep y (w.core_ideal χ_good) :=
          catBranch_on_supported ha χ_good hgood_sup
        have hper_bits : ∀ bits ∈ fourierOutcomes w.model.physical.wires.length,
            (tailPhys a bits).bornMass
              (compileFourierBranch y .inverse w.catPhys.wires (prior.map history) bits
                (a.kraus (Prep y χ_good))) ≤
            Complex.normSq c *
              ((A₀ * α ^ ws.length * α₁) *
                (idealAxis (ws.map ApproxCatWindow.model) (bits.reverse ++ prior.map history) idealTerm).bornMass
                  (w.model.step (prior.map history) bits ψ) +
               (B₀ * α ^ ws.length * α₁) *
                axisBad ws (bits.reverse ++ prior.map history) baseBad (w.model.step (prior.map history) bits ψ) +
               β₁ * normSq (fourierBranch .inverse w.model.physical.wires (prior.map history) bits (w.core_ideal χ_bad))) := by
          intro bits hb
          let φ_full := w.model.step (prior.map history) bits ψ
          let φ_good := fourierBranch .inverse w.model.physical.wires (prior.map history) bits (w.core_ideal χ_good)
          let φ_bad := fourierBranch .inverse w.model.physical.wires (prior.map history) bits (w.core_ideal χ_bad)
          have hφ_eq : φ_full = φ_good + φ_bad := by
            change fourierBranch .inverse w.model.physical.wires (prior.map history) bits
                (w.model.ideal (Quantum.run (w.model.physical.wires.reverse.map Gate.H) ψ)) = _
            rw [w.ideal_eq]; change fourierBranch _ _ _ _ (w.core_ideal χ) = _
            rw [hχ_split, map_add, map_add]
          have hφY : SupportedOn (fun s => s y = false) φ_full := by
            have h1 := compileFourierBranch_prep y .inverse w.model.physical.wires w.noY
              (prior.map history) bits (w.core_ideal χ) (w.core_idealY χ hχY)
            change SupportedOn _ (fourierBranch _ _ _ _ (w.model.ideal _))
            rw [w.ideal_eq]; exact h1.2
          have hih := ih (start + w.catPhys.count + w.catPhys.wires.length)
            (Single.historyAfter (start + w.catPhys.count + w.catPhys.wires.length)
              (Single.historyAfter (start + w.catPhys.count) history a.history) bits)
            (nextPrior w.catPhys.count w.catPhys.wires.length prior)
            (fun hRest tag => physTerm (a.history ++ bits ++ hRest) tag)
            (fun v hv => hstep_inv v (List.mem_cons_of_mem _ hv))
            (fun v hv => hbad_iso v (List.mem_cons_of_mem _ hv))
            (fun _ tag => hphys_sub _ tag)
            (fun _ tag => hterm _ tag)
            φ_full (hstep_inv w List.mem_cons_self _ bits ψ hψ_inv) hφY
          have hnp : (nextPrior w.catPhys.count w.catPhys.wires.length prior).map
              (Single.historyAfter (start + w.catPhys.count + w.catPhys.wires.length)
                (Single.historyAfter (start + w.catPhys.count) history a.history) bits) =
              bits.reverse ++ prior.map history :=
            nextPrior_map _ _ _ _ _ _ ha_len (w.wires_eq ▸ (fourierOutcomes_mem _ _).mp hb)
          rw [hnp] at hih
          have hsplit_good : (tailPhys a bits).bornMass (Prep y φ_good) ≤
              α₁ * (tailPhys a bits).bornMass (Prep y φ_full) + β₁ * normSq φ_bad := by
            have hgs : φ_good = φ_full + (-φ_bad) := by rw [hφ_eq]; abel
            rw [hgs, map_add, map_neg]
            have hu := instrument_mass_upper (tailPhys a bits) (Prep y φ_full) (-(Prep y φ_bad)) eps heps
            rw [instrument_mass_neg] at hu
            have hsub : (tailPhys a bits).bornMass (Prep y φ_bad) ≤ normSq (Prep y φ_bad) :=
              selectedAxisDep_subUnital ws _ _ _ _ (fun _ tag => hphys_sub _ tag) (Prep y φ_bad)
            rw [LocalFour.normSq_prep] at hsub
            have hm := mul_le_mul_of_nonneg_left hsub hβ₁_nonneg
            linarith
          have hcfb : compileFourierBranch y .inverse w.catPhys.wires (prior.map history) bits
              (a.kraus (Prep y χ_good)) = c • Prep y φ_good := by
            rw [ha_good, map_smul, w.wires_eq]
            have hfb := compileFourierBranch_prep y .inverse w.model.physical.wires w.noY
              (prior.map history) bits (w.core_ideal χ_good) (w.core_idealY χ_good hgoodY)
            rw [hfb.1]
          rw [hcfb, bornMass_smul_real]
          have hcomb : (tailPhys a bits).bornMass (Prep y φ_good) ≤
              (A₀ * α ^ ws.length * α₁) *
                (idealAxis (ws.map ApproxCatWindow.model) (bits.reverse ++ prior.map history) idealTerm).bornMass φ_full +
              (B₀ * α ^ ws.length * α₁) *
                axisBad ws (bits.reverse ++ prior.map history) baseBad φ_full +
              β₁ * normSq φ_bad := by
            have hm := mul_le_mul_of_nonneg_left hih hα₁_pos.le
            have heq1 : α₁ * (A₀ * α ^ ws.length *
                (idealAxis (ws.map ApproxCatWindow.model) (bits.reverse ++ prior.map history) idealTerm).bornMass φ_full +
                B₀ * α ^ ws.length * axisBad ws (bits.reverse ++ prior.map history) baseBad φ_full) =
                (A₀ * α ^ ws.length * α₁) *
                  (idealAxis (ws.map ApproxCatWindow.model) (bits.reverse ++ prior.map history) idealTerm).bornMass φ_full +
                (B₀ * α ^ ws.length * α₁) *
                  axisBad ws (bits.reverse ++ prior.map history) baseBad φ_full := by ring
            linarith
          exact mul_le_mul_of_nonneg_left hcomb (Complex.normSq_nonneg c)
        have hsum_bits := list_sum_map_le _ _ _ hper_bits
        simp only [List.map_cons, idealAxis_cons_mass]
        rw [list_sum_map_mul_left, list_sum_map_add, list_sum_map_add,
          list_sum_map_mul_left, list_sum_map_mul_left, list_sum_map_mul_left] at hsum_bits
        have hfb_bad : ((fourierOutcomes w.model.physical.wires.length).map (fun bits =>
            normSq (fourierBranch .inverse w.model.physical.wires (prior.map history) bits (w.core_ideal χ_bad)))).sum ≤
            normSq χ_bad := by
          rw [normSq_list_sum_fourierBranch]
          exact hbad_iso w List.mem_cons_self ψ hψ_inv
        have hmb : Complex.normSq c * (β₁ *
            ((fourierOutcomes w.model.physical.wires.length).map (fun bits =>
              normSq (fourierBranch .inverse w.model.physical.wires (prior.map history) bits (w.core_ideal χ_bad)))).sum) ≤
            Complex.normSq c * (β₁ * normSq χ_bad) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfb_bad hβ₁_nonneg) (Complex.normSq_nonneg c)
        rw [congrArg (fun l => fourierOutcomes l.length) w.wires_eq]
        linarith
      rw [hstepPhys_mass]
      exact list_sum_forall2_normSq_ge _ cs _ _ hal hper_a hmass
    -- Step 3: combine Step 1 and Step 2
    have hpow_succ : α₁ * (A₀ * α ^ ws.length * α₁) = A₀ * α ^ (w :: ws).length := by
      simp only [List.length_cons, pow_succ, α]; ring
    have hpow_succB : α₁ * (B₀ * α ^ ws.length * α₁) = B₀ * α ^ (w :: ws).length := by
      simp only [List.length_cons, pow_succ, α]; ring
    have hpow_ge1 : (1 : ℝ) ≤ α ^ (w :: ws).length := one_le_pow₀ hα_ge
    have hbad_coef : α₁ * β₁ + β₁ ≤ B₀ * α ^ (w :: ws).length := by
      have h1 : α₁ * β₁ + β₁ = (2 + eps) * β₁ := by dsimp [α₁]; ring
      have h2 : B₀ ≤ B₀ * α ^ (w :: ws).length := le_mul_of_one_le_right hB₀_nn hpow_ge1
      linarith
    have hnb_nn : 0 ≤ normSq χ_bad := ApproximatePhase34.mass_nonneg _
    have hm_bad := mul_le_mul_of_nonneg_right hbad_coef hnb_nn
    have hm_good := mul_le_mul_of_nonneg_left hgood_bound hα₁_pos.le
    rw [hstepPhys_eq]
    change _ ≤ (A₀ * α ^ (w :: ws).length) *
        (idealAxis ((w :: ws).map ApproxCatWindow.model) (prior.map history) idealTerm).bornMass ψ +
      (B₀ * α ^ (w :: ws).length) * (normSq χ_bad + ((fourierOutcomes w.model.physical.wires.length).map (fun bits =>
        axisBad ws (bits.reverse ++ prior.map history) baseBad (w.model.step (prior.map history) bits ψ))).sum)
    have hmul_split : (B₀ * α ^ (w :: ws).length) * (normSq χ_bad + ((fourierOutcomes w.model.physical.wires.length).map (fun bits =>
        axisBad ws (bits.reverse ++ prior.map history) baseBad (w.model.step (prior.map history) bits ψ))).sum) =
        (B₀ * α ^ (w :: ws).length) * normSq χ_bad +
        (B₀ * α ^ (w :: ws).length) * ((fourierOutcomes w.model.physical.wires.length).map (fun bits =>
          axisBad ws (bits.reverse ++ prior.map history) baseBad (w.model.step (prior.map history) bits ψ))).sum :=
      mul_add _ _ _
    have heq_m : α₁ * ((A₀ * α ^ ws.length * α₁) *
        (idealAxis ((w :: ws).map ApproxCatWindow.model) (prior.map history) idealTerm).bornMass ψ +
        (B₀ * α ^ ws.length * α₁) *
          ((fourierOutcomes w.model.physical.wires.length).map (fun bits =>
            axisBad ws (bits.reverse ++ prior.map history) baseBad (w.model.step (prior.map history) bits ψ))).sum +
        β₁ * normSq χ_bad) =
        (A₀ * α ^ (w :: ws).length) *
          (idealAxis ((w :: ws).map ApproxCatWindow.model) (prior.map history) idealTerm).bornMass ψ +
        (B₀ * α ^ (w :: ws).length) *
          ((fourierOutcomes w.model.physical.wires.length).map (fun bits =>
            axisBad ws (bits.reverse ++ prior.map history) baseBad (w.model.step (prior.map history) bits ψ))).sum +
        (α₁ * β₁) * normSq χ_bad := by
      rw [← hpow_succ, ← hpow_succB]; ring
    linarith

/-- Exact head step (`χ_bad = 0`, zero loss, upper-bound direction): used for `first20ApproxWin`. -/
theorem selectedAxisDep_cons_exact_upper {n : Nat} {y : Wire} {read : ConstantBit n → Bool}
    (w : ApproxCatWindow y read) (ws : List (ApproxCatWindow y read))
    (start : Nat) (history : Fin start → Bool) (prior : List (Fin start))
    (physTerm : List Bool → List Bool → Instrument) (idealTerm : List Bool → Instrument)
    (tailBad : List Bool → ℝ) (A B : ℝ)
    (ψ : State) (hψY : SupportedOn (fun s => s y = false) ψ)
    (hgood : SupportedOn w.goodPred
      (Quantum.run w.pre (Quantum.run (w.model.physical.wires.reverse.map Gate.H) ψ)))
    (htail : ∀ (a : InstrumentBranch) (bits : List Bool),
      a ∈ ((w.core start).instantiate read history).run →
      bits ∈ fourierOutcomes w.model.physical.wires.length →
      let h₁ := Single.historyAfter (start + w.catPhys.count) history a.history
      let h₂ := Single.historyAfter (start + w.catPhys.count + w.catPhys.wires.length) h₁ bits
      (selectedAxisDep ws _ h₂ (nextPrior w.catPhys.count w.catPhys.wires.length prior)
        (fun hRest tag => physTerm (a.history ++ bits ++ hRest) tag)).bornMass
          (Prep y (w.model.step (prior.map history) bits ψ)) ≤
      A * (idealAxis (ws.map ApproxCatWindow.model) (bits.reverse ++ prior.map history) idealTerm).bornMass
        (w.model.step (prior.map history) bits ψ) +
      B * tailBad bits) :
    (selectedAxisDep (w :: ws) start history prior physTerm).bornMass (Prep y ψ) ≤
      A * (idealAxis ((w :: ws).map ApproxCatWindow.model) (prior.map history) idealTerm).bornMass ψ +
      B * ((fourierOutcomes w.model.physical.wires.length).map tailBad).sum := by
  have hH_nw : y ∉ circuitWires (w.model.physical.wires.reverse.map Gate.H) := by
    intro hm
    simp only [circuitWires, List.mem_flatMap, List.mem_map] at hm
    obtain ⟨g, ⟨v, hv, rfl⟩, hwg⟩ := hm
    simp only [gateWires, List.mem_singleton] at hwg
    exact w.noY (List.mem_reverse.mp (hwg ▸ hv))
  let χ : State := Quantum.run w.pre (Quantum.run (w.model.physical.wires.reverse.map Gate.H) ψ)
  have hχY : SupportedOn (fun s => s y = false) χ :=
    LocalFour.circuit_frame y w.pre w.pre_noY _ (LocalFour.circuit_frame y _ hH_nw ψ hψY)
  have hpreH_prep : Quantum.run (compileCircuit y w.pre)
      (Quantum.run (w.catPhys.wires.reverse.map Gate.H) (Prep y ψ)) = Prep y χ := by
    rw [w.wires_eq, prep_circuit y _ hH_nw ψ,
      compileCircuit_prep y w.pre w.pre_noY _ (LocalFour.circuit_frame y _ hH_nw ψ hψY)]
  obtain ⟨cs, hal, hmass⟩ := w.catCoherent start history
  rw [selectedAxisDep_cons_mass, hpreH_prep]
  simp only [List.map_cons, idealAxis_cons_mass]
  have hper_a : ∀ a ∈ ((w.core start).instantiate read history).run, ∀ c : ℂ,
      (∀ s, w.goodPred s → a.kraus (Prep y (ket s)) = c • Prep y (w.core_ideal (ket s))) →
      ((fourierOutcomes w.catPhys.wires.length).map (fun bits =>
        let h₁ := Single.historyAfter (start + w.catPhys.count) history a.history
        let h₂ := Single.historyAfter (start + w.catPhys.count + w.catPhys.wires.length) h₁ bits
        (selectedAxisDep ws _ h₂ (nextPrior w.catPhys.count w.catPhys.wires.length prior)
          (fun hRest tag => physTerm (a.history ++ bits ++ hRest) tag)).bornMass
          (compileFourierBranch y .inverse w.catPhys.wires (prior.map history) bits
            (a.kraus (Prep y χ))))).sum ≤
      Complex.normSq c *
        (A * ((fourierOutcomes w.model.physical.wires.length).map (fun bits =>
            (idealAxis (ws.map ApproxCatWindow.model) (bits.reverse ++ prior.map history) idealTerm).bornMass
              (w.model.step (prior.map history) bits ψ))).sum +
         B * ((fourierOutcomes w.model.physical.wires.length).map tailBad).sum) := by
    intro a ha_mem c ha
    have ha_χ : a.kraus (Prep y χ) = c • Prep y (w.core_ideal χ) := catBranch_on_supported ha χ hgood
    have hper_bits : ∀ bits ∈ fourierOutcomes w.model.physical.wires.length,
        (let h₁ := Single.historyAfter (start + w.catPhys.count) history a.history
         let h₂ := Single.historyAfter (start + w.catPhys.count + w.catPhys.wires.length) h₁ bits
         (selectedAxisDep ws _ h₂ (nextPrior w.catPhys.count w.catPhys.wires.length prior)
           (fun hRest tag => physTerm (a.history ++ bits ++ hRest) tag)).bornMass
           (compileFourierBranch y .inverse w.catPhys.wires (prior.map history) bits
             (a.kraus (Prep y χ)))) ≤
        Complex.normSq c *
          (A * (idealAxis (ws.map ApproxCatWindow.model) (bits.reverse ++ prior.map history) idealTerm).bornMass
            (w.model.step (prior.map history) bits ψ) +
          B * tailBad bits) := by
      intro bits hb
      have hfb := compileFourierBranch_prep y .inverse w.model.physical.wires w.noY
        (prior.map history) bits (w.core_ideal χ) (w.core_idealY χ hχY)
      have hcfb : compileFourierBranch y .inverse w.catPhys.wires (prior.map history) bits (a.kraus (Prep y χ)) =
          c • Prep y (w.model.step (prior.map history) bits ψ) := by
        rw [ha_χ, map_smul, w.wires_eq, hfb.1]
        change c • Prep y (fourierBranch .inverse w.model.physical.wires (prior.map history) bits (w.core_ideal χ)) =
          c • Prep y (fourierBranch .inverse w.model.physical.wires (prior.map history) bits
            (w.model.ideal (Quantum.run (w.model.physical.wires.reverse.map Gate.H) ψ)))
        rw [w.ideal_eq]; rfl
      rw [hcfb, bornMass_smul_real]
      exact mul_le_mul_of_nonneg_left (htail a bits ha_mem hb) (Complex.normSq_nonneg c)
    have hs := list_sum_map_le _ _ _ hper_bits
    rw [list_sum_map_mul_left, list_sum_map_add, list_sum_map_mul_left, list_sum_map_mul_left] at hs
    rw [congrArg (fun l => fourierOutcomes l.length) w.wires_eq]
    exact hs
  exact list_sum_forall2_normSq_ge _ cs _ _ hal hper_a hmass

end
end ShorECDLP.Entrant.ApproxCat

/-! ### Skywalk 485-step tail cardinality bound (`|Bad485| ≤ 15e-11 · 2^256`) -/

namespace ShorECDLP.Entrant.SkywalkTail485
open ECDSAAdd ECDSAAdd.SkywalkNat
open scoped Classical
noncomputable section
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
set_option linter.unusedSimpArgs false

/-! ### 1. Exact step kinds, adjoint forward/backward recurrences, and linear invariants -/

inductive StepKind where
  | E | O0 | O1
  deriving DecidableEq

def allKinds : List StepKind := [.E, .O0, .O1]
def eo0Kinds : List StepKind := [.E, .O0]

def stepKind (z : SkywalkNat.State) : StepKind :=
  if z.u % 2 = 0 then .E
  else if z.v ≤ z.u then .O0
  else .O1

def stepF : StepKind → Nat × Nat → Nat × Nat
  | .E,  (C, D) => (2 * C, D)
  | .O0, (C, D) => (2 * C, C + D)
  | .O1, (C, D) => (2 * D, C + D)

def stepB : StepKind → Nat × Nat → Nat × Nat
  | .E,  (u, v) => (2 * u, v)
  | .O0, (u, v) => (2 * u + v, v)
  | .O1, (u, v) => (v, 2 * u + v)

def runF (p : Nat × Nat) (γ : List StepKind) : Nat × Nat :=
  γ.foldl (fun q k => stepF k q) p

def runB (p : Nat × Nat) (γ : List StepKind) : Nat × Nat :=
  γ.foldr stepB p

def runBL (p : Nat × Nat) (γ : List StepKind) : Nat × Nat :=
  γ.foldl (fun q k => stepB k q) p

theorem runF_nil (p : Nat × Nat) : runF p List.nil = p := rfl
theorem runF_cons (p : Nat × Nat) (k : StepKind) (γ : List StepKind) :
    runF p (k :: γ) = runF (stepF k p) γ := rfl
theorem runF_append (p : Nat × Nat) (γ₁ γ₂ : List StepKind) :
    runF p (γ₁ ++ γ₂) = runF (runF p γ₁) γ₂ := List.foldl_append

theorem runB_nil (p : Nat × Nat) : runB p List.nil = p := rfl
theorem runB_cons (p : Nat × Nat) (k : StepKind) (γ : List StepKind) :
    runB p (k :: γ) = stepB k (runB p γ) := rfl
theorem runB_append (p : Nat × Nat) (γ₁ γ₂ : List StepKind) :
    runB p (γ₁ ++ γ₂) = runB (runB p γ₂) γ₁ := List.foldr_append

theorem runBL_reverse (p : Nat × Nat) (γ : List StepKind) : runBL p γ.reverse = runB p γ := by
  induction γ generalizing p with
  | nil => rfl
  | cons k γ ih => simp [runBL, runB, List.foldl_append, ih]

theorem step_of_u_zero {z : SkywalkNat.State} (h : z.u = 0) : SkywalkNat.step z = z := by
  unfold SkywalkNat.step; rw [if_pos h]

theorem iter_of_u_zero {z : SkywalkNat.State} (h : z.u = 0) (k : Nat) :
    (SkywalkNat.step^[k] z).u = 0 := by
  induction k with
  | zero => exact h
  | succ k ih => rw [Function.iterate_succ_apply', step_of_u_zero ih]; exact ih

theorem stepB_step (z : SkywalkNat.State) (hu : 0 < z.u) (hvodd : z.v % 2 = 1) :
    stepB (stepKind z) ((SkywalkNat.step z).u, (SkywalkNat.step z).v) = (z.u, z.v) := by
  unfold stepKind SkywalkNat.step
  have hne : z.u ≠ 0 := by omega
  rw [if_neg hne]
  split_ifs with he hle
  · dsimp only [stepB]; apply Prod.ext <;> (dsimp; try omega)
  · dsimp only [stepB]; apply Prod.ext <;> (dsimp; try omega)
  · dsimp only [stepB]; apply Prod.ext <;> (dsimp; try omega)

theorem stepF_dot (k : StepKind) (C D u v : Nat) :
    (stepF k (C, D)).1 * u + (stepF k (C, D)).2 * v =
      C * (stepB k (u, v)).1 + D * (stepB k (u, v)).2 := by
  cases k <;> dsimp only [stepF, stepB] <;> ring

theorem runF_runB_dot (γ : List StepKind) (C D u v : Nat) :
    (runF (C, D) γ).1 * u + (runF (C, D) γ).2 * v =
      C * (runB (u, v) γ).1 + D * (runB (u, v) γ).2 := by
  induction γ generalizing C D with
  | nil => simp [runF, runB]
  | cons k γ ih =>
    rw [runF_cons, runB_cons]
    have h1 := ih (stepF k (C, D)).1 (stepF k (C, D)).2
    have h2 := stepF_dot k C D (runB (u, v) γ).1 (runB (u, v) γ).2
    simpa only [Prod.mk.eta] using h1.trans h2

theorem stepF_pos (k : StepKind) {C D : Nat} (hC : 0 < C) (hD : 0 < D) :
    0 < (stepF k (C, D)).1 ∧ 0 < (stepF k (C, D)).2 := by
  cases k <;> dsimp only [stepF] <;> omega

theorem runF_pos (γ : List StepKind) {C D : Nat} (hC : 0 < C) (hD : 0 < D) :
    0 < (runF (C, D) γ).1 ∧ 0 < (runF (C, D) γ).2 := by
  induction γ generalizing C D with
  | nil => exact ⟨hC, hD⟩
  | cons k γ ih =>
    have h1 := stepF_pos k hC hD
    exact ih h1.1 h1.2

theorem stepB_pos (k : StepKind) {u v : Nat} (hu : 0 < u) (hv : 0 < v) :
    0 < (stepB k (u, v)).1 ∧ 0 < (stepB k (u, v)).2 := by
  cases k <;> dsimp only [stepB] <;> omega

theorem runB_pos (γ : List StepKind) {u v : Nat} (hu : 0 < u) (hv : 0 < v) :
    0 < (runB (u, v) γ).1 ∧ 0 < (runB (u, v) γ).2 := by
  induction γ with
  | nil => exact ⟨hu, hv⟩
  | cons k γ ih => exact stepB_pos k ih.1 ih.2

theorem runBL_pos (γ : List StepKind) {u v : Nat} (hu : 0 < u) (hv : 0 < v) :
    0 < (runBL (u, v) γ).1 ∧ 0 < (runBL (u, v) γ).2 := by
  have h := runB_pos γ.reverse hu hv
  rwa [← runBL_reverse, List.reverse_reverse] at h

theorem stepB_prod (k : StepKind) (u v : Nat) :
    2 * (u * v) ≤ (stepB k (u, v)).1 * (stepB k (u, v)).2 := by
  cases k <;> dsimp only [stepB] <;> nlinarith

theorem runB_prod (γ : List StepKind) (u v : Nat) :
    2 ^ γ.length * (u * v) ≤ (runB (u, v) γ).1 * (runB (u, v) γ).2 := by
  induction γ with
  | nil => simp [runB]
  | cons k γ ih =>
    rw [List.length_cons, pow_succ, runB_cons]
    have h1 := stepB_prod k (runB (u, v) γ).1 (runB (u, v) γ).2
    nlinarith

theorem runBL_prod (γ : List StepKind) (u v : Nat) :
    2 ^ γ.length * (u * v) ≤ (runBL (u, v) γ).1 * (runBL (u, v) γ).2 := by
  have h := runB_prod γ.reverse u v
  rw [← runBL_reverse, List.reverse_reverse, List.length_reverse] at h
  exact h

theorem stepF_coprime_even_odd (k : StepKind) {C D : Nat}
    (hc : C.Coprime D) (hCe : C % 2 = 0) (hDo : D % 2 = 1) :
    (stepF k (C, D)).1.Coprime (stepF k (C, D)).2 ∧
      (stepF k (C, D)).1 % 2 = 0 ∧ (stepF k (C, D)).2 % 2 = 1 := by
  cases k
  · refine ⟨?_, by dsimp [stepF]; omega, hDo⟩
    dsimp only [stepF]
    exact (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hDo)).mul_left hc
  · refine ⟨?_, by dsimp [stepF]; omega, by dsimp [stepF]; omega⟩
    dsimp only [stepF]
    have h1 : C.Coprime (C + D) := by
      change C.gcd (C + D) = 1; rw [add_comm C D, Nat.gcd_add_self_right]; exact hc
    have h2 : (2 : Nat).Coprime (C + D) := Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (by omega))
    exact h2.mul_left h1
  · refine ⟨?_, by dsimp [stepF]; omega, by dsimp [stepF]; omega⟩
    dsimp only [stepF]
    have h1 : D.Coprime (C + D) := by
      change D.gcd (C + D) = 1; rw [Nat.gcd_add_self_right, Nat.gcd_comm]; exact hc
    have h2 : (2 : Nat).Coprime (C + D) := Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (by omega))
    exact h2.mul_left h1

theorem runF_coprime_even_odd (γ : List StepKind) {C D : Nat}
    (hc : C.Coprime D) (hCe : C % 2 = 0) (hDo : D % 2 = 1) :
    (runF (C, D) γ).1.Coprime (runF (C, D) γ).2 ∧
      (runF (C, D) γ).1 % 2 = 0 ∧ (runF (C, D) γ).2 % 2 = 1 := by
  induction γ generalizing C D with
  | nil => exact ⟨hc, hCe, hDo⟩
  | cons k γ ih =>
    have h1 := stepF_coprime_even_odd k hc hCe hDo
    exact ih h1.1 h1.2.1 h1.2.2

theorem stepF_det (k : StepKind) (A B C D : Nat) :
    (((stepF k (A, B)).1 : ℤ) * (stepF k (C, D)).2 - ((stepF k (A, B)).2 : ℤ) * (stepF k (C, D)).1) =
      (if k = .O1 then -2 else 2) * ((A : ℤ) * D - (B : ℤ) * C) := by
  cases k <;> simp only [stepF, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, reduceCtorEq, ↓reduceIte] <;> ring

theorem runF_det_abs (γ : List StepKind) (A B C D : Nat) :
    ∃ sgn : Bool,
      (((runF (A, B) γ).1 : ℤ) * (runF (C, D) γ).2 - ((runF (A, B) γ).2 : ℤ) * (runF (C, D) γ).1) =
        (if sgn then (1 : ℤ) else -1) * (2 : ℤ) ^ γ.length * ((A : ℤ) * D - (B : ℤ) * C) := by
  induction γ generalizing A B C D with
  | nil => exact ⟨true, by simp [runF]⟩
  | cons k γ ih =>
    rw [runF_cons, runF_cons, List.length_cons, pow_succ']
    obtain ⟨sgn, hs⟩ := ih (stepF k (A, B)).1 (stepF k (A, B)).2 (stepF k (C, D)).1 (stepF k (C, D)).2
    have hd := stepF_det k A B C D
    simp only [Prod.mk.eta] at hs
    rw [hs, hd]
    cases k <;> cases sgn
    · exact ⟨false, by simp; ring⟩
    · exact ⟨true, by simp; ring⟩
    · exact ⟨false, by simp; ring⟩
    · exact ⟨true, by simp; ring⟩
    · exact ⟨true, by simp; ring⟩
    · exact ⟨false, by simp; ring⟩

def traceKinds (z : SkywalkNat.State) : Nat → List StepKind
  | 0 => []
  | n + 1 => stepKind z :: traceKinds (SkywalkNat.step z) n

theorem traceKinds_length (z : SkywalkNat.State) (n : Nat) : (traceKinds z n).length = n := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => simp [traceKinds, ih]

theorem traceKinds_add (z : SkywalkNat.State) (a b : Nat) :
    traceKinds z (a + b) = traceKinds z a ++ traceKinds (SkywalkNat.step^[a] z) b := by
  induction a generalizing z with
  | zero => simp [traceKinds]
  | succ a ih =>
    rw [Nat.succ_add, traceKinds, traceKinds, List.cons_append, Function.iterate_succ_apply]
    exact congrArg (stepKind z :: ·) (ih (SkywalkNat.step z))

theorem runB_traceKinds (z : SkywalkNat.State) (n : Nat) (hv0 : 0 < z.v) (hvodd : z.v % 2 = 1)
    (halive : ∀ i < n, 0 < (SkywalkNat.step^[i] z).u) :
    runB ((SkywalkNat.step^[n] z).u, (SkywalkNat.step^[n] z).v) (traceKinds z n) = (z.u, z.v) := by
  induction n generalizing z with
  | zero => simp [traceKinds, runB]
  | succ n ih =>
    rw [traceKinds, runB_cons, Function.iterate_succ_apply]
    have hv1 := SkywalkNat.step_v_odd_pos z hv0 hvodd
    have hrec := ih (SkywalkNat.step z) hv1.1 hv1.2 (fun i hi => by
      simpa only [Function.iterate_succ_apply] using halive (i + 1) (by omega))
    rw [hrec]
    exact stepB_step z (halive 0 (by omega)) hvodd

theorem iter_alive_of_u_ne_zero (z : SkywalkNat.State) {n i : Nat} (hi : i ≤ n)
    (h : (SkywalkNat.step^[n] z).u ≠ 0) : 0 < (SkywalkNat.step^[i] z).u := by
  by_contra h0
  have hz : (SkywalkNat.step^[i] z).u = 0 := by omega
  have hrew : n = (n - i) + i := by omega
  rw [hrew, Function.iterate_add_apply] at h
  exact h (iter_of_u_zero hz (n - i))

/-! ### 2. Linear Diophantine solution counting (`#sol(C u + D v = N) ≤ N / (C D) + 1`) -/

theorem linear_diophantine_card (C D N : Nat) (hC : 0 < C) (hD : 0 < D) (hc : C.Coprime D) :
    ((Finset.Ioo 0 N).filter (fun v => ∃ u > 0, C * u + D * v = N)).card ≤ N / (C * D) + 1 := by
  set S := (Finset.Ioo 0 N).filter (fun v => ∃ u > 0, C * u + D * v = N)
  by_cases hne : S.Nonempty
  · let v0 := S.min' hne
    have hv0_mem : v0 ∈ S := Finset.min'_mem S hne
    obtain ⟨u0, _, heq0⟩ := (Finset.mem_filter.mp hv0_mem).2
    have hinj : Set.InjOn (fun v => (v - v0) / C) (S : Set Nat) := by
      intro v₁ hv₁ v₂ hv₂ heq
      have hv₁' : v₁ ∈ S := Finset.mem_coe.mp hv₁
      have hv₂' : v₂ ∈ S := Finset.mem_coe.mp hv₂
      have hle₁ : v0 ≤ v₁ := Finset.min'_le S v₁ hv₁'
      have hle₂ : v0 ≤ v₂ := Finset.min'_le S v₂ hv₂'
      obtain ⟨u₁, _, heq₁⟩ := (Finset.mem_filter.mp hv₁').2
      obtain ⟨u₂, _, heq₂⟩ := (Finset.mem_filter.mp hv₂').2
      have hdvd₁ : C ∣ (v₁ - v0) := by
        have hm : (v₁ - v0) * D = (u0 - u₁) * C := by
          have : D * v0 ≤ D * v₁ := Nat.mul_le_mul_left D hle₁
          have : C * u₁ ≤ C * u0 := by omega
          have : u₁ ≤ u0 := Nat.le_of_mul_le_mul_left this hC
          zify [hle₁, this] at heq0 heq₁ ⊢; linarith
        exact hc.dvd_of_dvd_mul_right ⟨u0 - u₁, by linarith⟩
      have hdvd₂ : C ∣ (v₂ - v0) := by
        have hm : (v₂ - v0) * D = (u0 - u₂) * C := by
          have : D * v0 ≤ D * v₂ := Nat.mul_le_mul_left D hle₂
          have : C * u₂ ≤ C * u0 := by omega
          have : u₂ ≤ u0 := Nat.le_of_mul_le_mul_left this hC
          zify [hle₂, this] at heq0 heq₂ ⊢; linarith
        exact hc.dvd_of_dvd_mul_right ⟨u0 - u₂, by linarith⟩
      have h1 : C * ((v₁ - v0) / C) = v₁ - v0 := Nat.mul_div_cancel' hdvd₁
      have h2 : C * ((v₂ - v0) / C) = v₂ - v0 := Nat.mul_div_cancel' hdvd₂
      dsimp only at heq
      rw [heq] at h1
      omega
    have hmap : Set.MapsTo (fun v => (v - v0) / C) (S : Set Nat) (Finset.range (N / (C * D) + 1) : Set Nat) := by
      intro v hv
      have hv' : v ∈ S := Finset.mem_coe.mp hv
      rw [Finset.mem_coe, Finset.mem_range]
      obtain ⟨u, hu, heq⟩ := (Finset.mem_filter.mp hv').2
      have hmul : (v - v0) / C * (C * D) < N := by
        have h1 : (v - v0) / C * C ≤ v - v0 := Nat.div_mul_le_self (v - v0) C
        have h2 : (v - v0) / C * (C * D) = (v - v0) / C * C * D := by ring
        rw [h2]
        have h3 : (v - v0) / C * C * D ≤ (v - v0) * D := Nat.mul_le_mul_right D h1
        have h4 : (v - v0) * D ≤ v * D := Nat.mul_le_mul_right D (Nat.sub_le v v0)
        have h5 : C * u ≥ 1 := Nat.mul_pos hC hu
        nlinarith
      exact Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le (Nat.mul_pos hC hD)).mpr hmul.le)
    have hc_le := Finset.card_le_card_of_injOn (fun v => (v - v0) / C) hmap hinj
    simpa only [Finset.card_range] using hc_le
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]; exact Nat.zero_le _

/-! ### 3. Exact manifest-positive rational potentials `Φ_F`, `Φ_B` and contractions -/

def P_F (C D : ℝ) : ℝ :=
  1000 * D ^ 6 + 22122 * C * D ^ 5 + 94633 * C ^ 2 * D ^ 4 + 169415 * C ^ 3 * D ^ 3 +
    172641 * C ^ 4 * D ^ 2 + 56248 * C ^ 5 * D + 3364 * C ^ 6

def Q_F (C D : ℝ) : ℝ := D ^ 2 + 10 * C * D + C ^ 2

def phiF (C D : ℝ) : ℝ := P_F C D / (C ^ 3 * D ^ 3 * (C + D) ^ 3 * Q_F C D)

def P_B (u v : ℝ) : ℝ :=
  1000 * v ^ 6 + 39562 * u * v ^ 5 + 228983 * u ^ 2 * v ^ 4 + 419099 * u ^ 3 * v ^ 3 +
    337106 * u ^ 4 * v ^ 2 + 99995 * u ^ 5 * v + 6562 * u ^ 6

def Q_B (u v : ℝ) : ℝ := v ^ 2 + 20 * u * v + 2 * u ^ 2

def phiB (u v : ℝ) : ℝ := P_B u v / (u ^ 2 * v ^ 2 * (u + v) ^ 5 * Q_B u v)

def rhoF : ℝ := 359 / 1250
def rhoB : ℝ := 2881 / 10000
def rhoEO0 : ℝ := 32 / 125

theorem phiF_pos {C D : ℝ} (hC : 0 < C) (hD : 0 < D) : 0 < phiF C D := by
  unfold phiF P_F Q_F; positivity

theorem phiB_pos {u v : ℝ} (hu : 0 < u) (hv : 0 < v) : 0 < phiB u v := by
  unfold phiB P_B Q_B; positivity

theorem phiF_lower {C D : ℝ} (hC : 0 < C) (hD : 0 < D) :
    1000 * (C + D) / (C ^ 3 * D ^ 3) ≤ phiF C D := by
  unfold phiF
  have hQ : 0 < Q_F C D := by unfold Q_F; positivity
  have hden : 0 < C ^ 3 * D ^ 3 * (C + D) ^ 3 * Q_F C D := by positivity
  rw [div_le_div_iff₀ (by positivity) hden]
  have hid : P_F C D * (C ^ 3 * D ^ 3) - 1000 * (C + D) * (C ^ 3 * D ^ 3 * (C + D) ^ 3 * Q_F C D) =
      (C ^ 3 * D ^ 3) * (8122 * C * D ^ 5 + 47633 * C ^ 2 * D ^ 4 + 101415 * C ^ 3 * D ^ 3 +
        125641 * C ^ 4 * D ^ 2 + 42248 * C ^ 5 * D + 2364 * C ^ 6) := by
    unfold P_F Q_F; ring
  have hnn : 0 ≤ P_F C D * (C ^ 3 * D ^ 3) - 1000 * (C + D) * (C ^ 3 * D ^ 3 * (C + D) ^ 3 * Q_F C D) := by
    rw [hid]; positivity
  linarith

theorem phiB_lower {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    1000 / (u ^ 2 * v ^ 2 * (u + v)) ≤ phiB u v := by
  unfold phiB
  have hQ : 0 < Q_B u v := by unfold Q_B; positivity
  have hden : 0 < u ^ 2 * v ^ 2 * (u + v) ^ 5 * Q_B u v := by positivity
  rw [div_le_div_iff₀ (by positivity) hden]
  have hid : P_B u v * (u ^ 2 * v ^ 2 * (u + v)) - 1000 * (u ^ 2 * v ^ 2 * (u + v) ^ 5 * Q_B u v) =
      (u ^ 2 * v ^ 2 * (u + v)) * (15562 * u * v ^ 5 + 140983 * u ^ 2 * v ^ 4 + 287099 * u ^ 3 * v ^ 3 +
        244106 * u ^ 4 * v ^ 2 + 71995 * u ^ 5 * v + 4562 * u ^ 6) := by
    unfold P_B Q_B; ring
  have hnn : 0 ≤ P_B u v * (u ^ 2 * v ^ 2 * (u + v)) - 1000 * (u ^ 2 * v ^ 2 * (u + v) ^ 5 * Q_B u v) := by
    rw [hid]; positivity
  linarith

theorem inv_prod_le_phiF {C D : ℝ} (hC : 0 < C) (hD : 0 < D) (hCD : C * D ≤ (2 : ℝ) ^ 256) :
    1 / (C * D) ≤ ((2 : ℝ) ^ 384 / 2000) * phiF C D := by
  have hfl := phiF_lower hC hD
  have hcube : (C * D) ^ 3 ≤ ((2 : ℝ) ^ 384) ^ 2 := by
    have h1 : (C * D) ^ 3 ≤ ((2 : ℝ) ^ 256) ^ 3 := pow_le_pow_left₀ (by positivity) hCD 3
    have h2 : ((2 : ℝ) ^ 256) ^ 3 = ((2 : ℝ) ^ 384) ^ 2 := by rw [← pow_mul, ← pow_mul]
    exact h1.trans_eq h2
  have hE : 0 < (2 : ℝ) ^ 384 := by positivity
  generalize (2 : ℝ) ^ 384 = E at hcube hE ⊢
  have hsq : (1 / (C * D)) ^ 2 ≤ ((E / 2000) * (1000 * (C + D) / (C ^ 3 * D ^ 3))) ^ 2 := by
    have h4 : 4 * (C * D) ≤ (C + D) ^ 2 := by nlinarith [sq_nonneg (C - D)]
    have hnum : 4 * (C * D) ^ 4 ≤ E ^ 2 * (C + D) ^ 2 := by
      have h1 := mul_le_mul hcube h4 (by positivity) (by positivity)
      linarith
    have h6 : 4 * (C * D) ^ 6 ≤ E ^ 2 * (C + D) ^ 2 * (C * D) ^ 2 := by
      have h1 := mul_le_mul_of_nonneg_right hnum (sq_nonneg (C * D))
      linarith
    have hrhs : ((E / 2000) * (1000 * (C + D) / (C ^ 3 * D ^ 3))) ^ 2 =
        E ^ 2 * (C + D) ^ 2 / (4 * (C * D) ^ 6) := by
      field_simp [hC.ne', hD.ne']; ring
    rw [hrhs, div_pow, one_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have h1 : 1 / (C * D) ≤ (E / 2000) * (1000 * (C + D) / (C ^ 3 * D ^ 3)) :=
    le_of_sq_le_sq hsq (by positivity)
  exact h1.trans (mul_le_mul_of_nonneg_left hfl (by positivity))

theorem coupling_lower {C D u v : ℝ} (hC : 0 < C) (hD : 0 < D) (hu : 0 < u) (hv : 0 < v) :
    (3125 * 10 ^ 6 / 108 : ℝ) ≤ phiF C D * phiB u v * (C * u + D * v) ^ 5 := by
  have hf := phiF_lower hC hD
  have hb := phiB_lower hu hv
  have hfb : (1000 * (C + D) / (C ^ 3 * D ^ 3)) * (1000 / (u ^ 2 * v ^ 2 * (u + v))) ≤ phiF C D * phiB u v :=
    mul_le_mul hf hb (by positivity) (phiF_pos hC hD).le
  have hmul := mul_le_mul_of_nonneg_right hfb (by positivity : 0 ≤ (C * u + D * v) ^ 5)
  refine le_trans ?_ hmul
  have hpoly (X Y : ℝ) (hX : 0 < X) (hY : 0 < Y) : 3125 * X ^ 2 * Y ^ 3 ≤ 108 * (X + Y) ^ 5 := by
    have h : 108 * (X + Y) ^ 5 - 3125 * X ^ 2 * Y ^ 3 =
        (3 * X - 2 * Y) ^ 2 * (12 * X ^ 3 + 76 * X ^ 2 * Y + 216 * X * Y ^ 2 + 27 * Y ^ 3) := by ring
    have hnn : 0 ≤ 108 * (X + Y) ^ 5 - 3125 * X ^ 2 * Y ^ 3 := by rw [h]; positivity
    linarith
  have h1 := hpoly (C * u) (D * v) (by positivity) (by positivity)
  have h2 := hpoly (D * v) (C * u) (by positivity) (by positivity)
  have hcomb : 3125 * C ^ 3 * D ^ 3 * u ^ 2 * v ^ 2 * (u + v) ≤ 108 * (C + D) * (C * u + D * v) ^ 5 := by
    have hC1 := mul_le_mul_of_nonneg_left h1 hC.le
    have hD1 := mul_le_mul_of_nonneg_left h2 hD.le
    have hsum : C * (3125 * (C * u) ^ 2 * (D * v) ^ 3) + D * (3125 * (D * v) ^ 2 * (C * u) ^ 3) =
        3125 * C ^ 3 * D ^ 3 * u ^ 2 * v ^ 2 * (u + v) := by ring
    have hrhs : C * (108 * (C * u + D * v) ^ 5) + D * (108 * (D * v + C * u) ^ 5) =
        108 * (C + D) * (C * u + D * v) ^ 5 := by ring
    linarith
  have hden : 0 < C ^ 3 * D ^ 3 * (u ^ 2 * v ^ 2 * (u + v)) := by positivity
  have hlhs : 1000 * (C + D) / (C ^ 3 * D ^ 3) * (1000 / (u ^ 2 * v ^ 2 * (u + v))) * (C * u + D * v) ^ 5 =
      10 ^ 6 * (C + D) * (C * u + D * v) ^ 5 / (C ^ 3 * D ^ 3 * (u ^ 2 * v ^ 2 * (u + v))) := by
    field_simp [hC.ne', hD.ne', hu.ne', hv.ne', (show 0 < u + v by positivity).ne']; ring
  rw [hlhs, div_le_div_iff₀ (by norm_num) hden]
  linarith

theorem phiF_contract {C D : ℝ} (hC : 0 < C) (hD : 0 < D) :
    phiF (2 * C) D + phiF (2 * C) (C + D) + phiF (2 * D) (C + D) ≤ rhoF * phiF C D := by
  unfold phiF rhoF
  have hQ0 : 0 < Q_F C D := by unfold Q_F; positivity
  have hQE : 0 < Q_F (2 * C) D := by unfold Q_F; positivity
  have hQO0 : 0 < Q_F (2 * C) (C + D) := by unfold Q_F; positivity
  have hQO1 : 0 < Q_F (2 * D) (C + D) := by unfold Q_F; positivity
  have h31 : 2 * C + (C + D) = 3 * C + D := by ring
  have h13 : 2 * D + (C + D) = C + 3 * D := by ring
  rw [h31, h13]
  set M := 1250 * 8 * C ^ 3 * D ^ 3 * (C + D) ^ 5 * (2 * C + D) ^ 3 * (3 * C + D) ^ 3 * (C + 3 * D) ^ 3 *
      Q_F C D * Q_F (2 * C) D * Q_F (2 * C) (C + D) * Q_F (2 * D) (C + D)
  have hM : 0 < M := by dsimp [M]; positivity
  suffices hsub : 0 ≤ M * (359 / 1250 * (P_F C D / (C ^ 3 * D ^ 3 * (C + D) ^ 3 * Q_F C D)) -
      (P_F (2 * C) D / ((2 * C) ^ 3 * D ^ 3 * (2 * C + D) ^ 3 * Q_F (2 * C) D) +
       P_F (2 * C) (C + D) / ((2 * C) ^ 3 * (C + D) ^ 3 * (3 * C + D) ^ 3 * Q_F (2 * C) (C + D)) +
       P_F (2 * D) (C + D) / ((2 * D) ^ 3 * (C + D) ^ 3 * (C + 3 * D) ^ 3 * Q_F (2 * D) (C + D)))) by
    have hnn := nonneg_of_mul_nonneg_right hsub hM
    linarith
  have hclear : M * (359 / 1250 * (P_F C D / (C ^ 3 * D ^ 3 * (C + D) ^ 3 * Q_F C D)) -
      (P_F (2 * C) D / ((2 * C) ^ 3 * D ^ 3 * (2 * C + D) ^ 3 * Q_F (2 * C) D) +
       P_F (2 * C) (C + D) / ((2 * C) ^ 3 * (C + D) ^ 3 * (3 * C + D) ^ 3 * Q_F (2 * C) (C + D)) +
       P_F (2 * D) (C + D) / ((2 * D) ^ 3 * (C + D) ^ 3 * (C + 3 * D) ^ 3 * Q_F (2 * D) (C + D)))) =
      (C + D) ^ 2 * (
        359 * 8 * (2 * C + D) ^ 3 * (3 * C + D) ^ 3 * (C + 3 * D) ^ 3 * Q_F (2 * C) D * Q_F (2 * C) (C + D) * Q_F (2 * D) (C + D) * P_F C D
        - 1250 * ((C + D) ^ 3 * (3 * C + D) ^ 3 * (C + 3 * D) ^ 3 * Q_F C D * Q_F (2 * C) (C + D) * Q_F (2 * D) (C + D) * P_F (2 * C) D
                + D ^ 3 * (2 * C + D) ^ 3 * (C + 3 * D) ^ 3 * Q_F C D * Q_F (2 * C) D * Q_F (2 * D) (C + D) * P_F (2 * C) (C + D)
                + C ^ 3 * (2 * C + D) ^ 3 * (3 * C + D) ^ 3 * Q_F C D * Q_F (2 * C) D * Q_F (2 * C) (C + D) * P_F (2 * D) (C + D))) := by
    dsimp only [M]
    generalize Q_F C D = q0 at hQ0 ⊢
    generalize Q_F (2 * C) D = qe at hQE ⊢
    generalize Q_F (2 * C) (C + D) = qo0 at hQO0 ⊢
    generalize Q_F (2 * D) (C + D) = qo1 at hQO1 ⊢
    field_simp
    ring
  rw [hclear]
  have hid : (C + D) ^ 2 * (
        359 * 8 * (2 * C + D) ^ 3 * (3 * C + D) ^ 3 * (C + 3 * D) ^ 3 * Q_F (2 * C) D * Q_F (2 * C) (C + D) * Q_F (2 * D) (C + D) * P_F C D
        - 1250 * ((C + D) ^ 3 * (3 * C + D) ^ 3 * (C + 3 * D) ^ 3 * Q_F C D * Q_F (2 * C) (C + D) * Q_F (2 * D) (C + D) * P_F (2 * C) D
                + D ^ 3 * (2 * C + D) ^ 3 * (C + 3 * D) ^ 3 * Q_F C D * Q_F (2 * C) D * Q_F (2 * D) (C + D) * P_F (2 * C) (C + D)
                + C ^ 3 * (2 * C + D) ^ 3 * (3 * C + D) ^ 3 * Q_F C D * Q_F (2 * C) D * Q_F (2 * C) (C + D) * P_F (2 * D) (C + D))) =
      251100000 * D ^ 23 + 7135927200 * C * D ^ 22 + 42740968896 * C ^ 2 * D ^ 21 + 13475513472 * C ^ 3 * D ^ 20 +
      157045860560 * C ^ 4 * D ^ 19 + 11180872647872 * C ^ 5 * D ^ 18 + 71111814523696 * C ^ 6 * D ^ 17 +
      161294689885176 * C ^ 7 * D ^ 16 + 94725774363808 * C ^ 8 * D ^ 15 + 237084598265936 * C ^ 9 * D ^ 14 +
      2547001311711632 * C ^ 10 * D ^ 13 + 7871039956412616 * C ^ 11 * D ^ 12 + 11522451273465248 * C ^ 12 * D ^ 11 +
      8441404560143808 * C ^ 13 * D ^ 10 + 2432762994107472 * C ^ 14 * D ^ 9 + 415461302137096 * C ^ 15 * D ^ 8 +
      1691281594971584 * C ^ 16 * D ^ 7 + 2040172166507632 * C ^ 17 * D ^ 6 + 1072036835112240 * C ^ 18 * D ^ 5 +
      293723985914040 * C ^ 19 * D ^ 4 + 42427334594000 * C ^ 20 * D ^ 3 + 2617763422752 * C ^ 21 * D ^ 2 +
      1566411264 * C ^ 22 * D + 30412800 * C ^ 23 := by
    unfold P_F Q_F; ring
  rw [hid]; positivity

theorem phiB_contract {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    phiB (2 * u) v + phiB (2 * u + v) v + phiB v (2 * u + v) ≤ rhoB * phiB u v := by
  unfold phiB rhoB
  have hQ0 : 0 < Q_B u v := by unfold Q_B; positivity
  have hQE : 0 < Q_B (2 * u) v := by unfold Q_B; positivity
  have hQO0 : 0 < Q_B (2 * u + v) v := by unfold Q_B; positivity
  have hQO1 : 0 < Q_B v (2 * u + v) := by unfold Q_B; positivity
  have h2uv1 : 2 * u + v + v = 2 * (u + v) := by ring
  have h2uv2 : v + (2 * u + v) = 2 * (u + v) := by ring
  rw [h2uv1, h2uv2]
  set M := 10000 * 32 * u ^ 2 * v ^ 2 * (u + v) ^ 7 * (2 * u + v) ^ 5 *
      Q_B u v * Q_B (2 * u) v * Q_B (2 * u + v) v * Q_B v (2 * u + v)
  have hM : 0 < M := by dsimp [M]; positivity
  suffices hsub : 0 ≤ M * (2881 / 10000 * (P_B u v / (u ^ 2 * v ^ 2 * (u + v) ^ 5 * Q_B u v)) -
      (P_B (2 * u) v / ((2 * u) ^ 2 * v ^ 2 * (2 * u + v) ^ 5 * Q_B (2 * u) v) +
       P_B (2 * u + v) v / ((2 * u + v) ^ 2 * v ^ 2 * (2 * (u + v)) ^ 5 * Q_B (2 * u + v) v) +
       P_B v (2 * u + v) / (v ^ 2 * (2 * u + v) ^ 2 * (2 * (u + v)) ^ 5 * Q_B v (2 * u + v)))) by
    have hnn := nonneg_of_mul_nonneg_right hsub hM
    linarith
  have hclear : M * (2881 / 10000 * (P_B u v / (u ^ 2 * v ^ 2 * (u + v) ^ 5 * Q_B u v)) -
      (P_B (2 * u) v / ((2 * u) ^ 2 * v ^ 2 * (2 * u + v) ^ 5 * Q_B (2 * u) v) +
       P_B (2 * u + v) v / ((2 * u + v) ^ 2 * v ^ 2 * (2 * (u + v)) ^ 5 * Q_B (2 * u + v) v) +
       P_B v (2 * u + v) / (v ^ 2 * (2 * u + v) ^ 2 * (2 * (u + v)) ^ 5 * Q_B v (2 * u + v)))) =
      (u + v) ^ 2 * (
        2881 * 32 * (2 * u + v) ^ 5 * Q_B (2 * u) v * Q_B (2 * u + v) v * Q_B v (2 * u + v) * P_B u v
        - 10000 * (8 * (u + v) ^ 5 * Q_B u v * Q_B (2 * u + v) v * Q_B v (2 * u + v) * P_B (2 * u) v
                 + u ^ 2 * (2 * u + v) ^ 3 * Q_B u v * Q_B (2 * u) v * Q_B v (2 * u + v) * P_B (2 * u + v) v
                 + u ^ 2 * (2 * u + v) ^ 3 * Q_B u v * Q_B (2 * u) v * Q_B (2 * u + v) v * P_B v (2 * u + v))) := by
    dsimp only [M]
    generalize Q_B u v = q0 at hQ0 ⊢
    generalize Q_B (2 * u) v = qe at hQE ⊢
    generalize Q_B (2 * u + v) v = qo0 at hQO0 ⊢
    generalize Q_B v (2 * u + v) = qo1 at hQO1 ⊢
    field_simp
    ring
  rw [hclear]
  have hid : (u + v) ^ 2 * (
        2881 * 32 * (2 * u + v) ^ 5 * Q_B (2 * u) v * Q_B (2 * u + v) v * Q_B v (2 * u + v) * P_B u v
        - 10000 * (8 * (u + v) ^ 5 * Q_B u v * Q_B (2 * u + v) v * Q_B v (2 * u + v) * P_B (2 * u) v
                 + u ^ 2 * (2 * u + v) ^ 3 * Q_B u v * Q_B (2 * u) v * Q_B v (2 * u + v) * P_B (2 * u + v) v
                 + u ^ 2 * (2 * u + v) ^ 3 * Q_B u v * Q_B (2 * u) v * Q_B (2 * u + v) v * P_B v (2 * u + v))) =
      6449568000 * v ^ 19 + 69777216 * u * v ^ 18 + 1606510277440 * u ^ 2 * v ^ 17 +
      7348047945760 * u ^ 3 * v ^ 16 + 275453341888 * u ^ 4 * v ^ 15 + 1552781252544 * u ^ 5 * v ^ 14 +
      322867813257088 * u ^ 6 * v ^ 13 + 1329542784952032 * u ^ 7 * v ^ 12 + 2252279628383104 * u ^ 8 * v ^ 11 +
      1601552632989696 * u ^ 9 * v ^ 10 + 94516252773888 * u ^ 10 * v ^ 9 + 94151335135232 * u ^ 11 * v ^ 8 +
      1207676159293440 * u ^ 12 * v ^ 7 + 1247603729526784 * u ^ 13 * v ^ 6 + 428015070552064 * u ^ 14 * v ^ 5 +
      24943582863360 * u ^ 15 * v ^ 4 + 782709555200 * u ^ 16 * v ^ 3 + 1438222385152 * u ^ 17 * v ^ 2 +
      107171807232 * u ^ 18 * v + 31981568 * u ^ 19 := by
    unfold P_B Q_B; ring
  rw [hid]; positivity

theorem phiF_eo0_contract {C D : ℝ} (hD : 0 < D) (hCD : D ≤ C) :
    phiF (2 * C) D + phiF (2 * C) (C + D) ≤ rhoEO0 * phiF C D := by
  have hC : 0 < C := lt_of_lt_of_le hD hCD
  unfold phiF rhoEO0
  have hQ0 : 0 < Q_F C D := by unfold Q_F; positivity
  have hQE : 0 < Q_F (2 * C) D := by unfold Q_F; positivity
  have hQO0 : 0 < Q_F (2 * C) (C + D) := by unfold Q_F; positivity
  have h31 : 2 * C + (C + D) = 3 * C + D := by ring
  rw [h31]
  set M := 125 * 8 * C ^ 3 * D ^ 3 * (C + D) ^ 3 * (2 * C + D) ^ 3 * (3 * C + D) ^ 3 *
      Q_F C D * Q_F (2 * C) D * Q_F (2 * C) (C + D)
  have hM : 0 < M := by dsimp [M]; positivity
  suffices hsub : 0 ≤ M * (32 / 125 * (P_F C D / (C ^ 3 * D ^ 3 * (C + D) ^ 3 * Q_F C D)) -
      (P_F (2 * C) D / ((2 * C) ^ 3 * D ^ 3 * (2 * C + D) ^ 3 * Q_F (2 * C) D) +
       P_F (2 * C) (C + D) / ((2 * C) ^ 3 * (C + D) ^ 3 * (3 * C + D) ^ 3 * Q_F (2 * C) (C + D)))) by
    have hnn := nonneg_of_mul_nonneg_right hsub hM
    linarith
  have hclear : M * (32 / 125 * (P_F C D / (C ^ 3 * D ^ 3 * (C + D) ^ 3 * Q_F C D)) -
      (P_F (2 * C) D / ((2 * C) ^ 3 * D ^ 3 * (2 * C + D) ^ 3 * Q_F (2 * C) D) +
       P_F (2 * C) (C + D) / ((2 * C) ^ 3 * (C + D) ^ 3 * (3 * C + D) ^ 3 * Q_F (2 * C) (C + D)))) =
      32 * 8 * (2 * C + D) ^ 3 * (3 * C + D) ^ 3 * Q_F (2 * C) D * Q_F (2 * C) (C + D) * P_F C D
      - 125 * ((C + D) ^ 3 * (3 * C + D) ^ 3 * Q_F C D * Q_F (2 * C) (C + D) * P_F (2 * C) D
             + D ^ 3 * (2 * C + D) ^ 3 * Q_F C D * Q_F (2 * C) D * P_F (2 * C) (C + D)) := by
    dsimp only [M]
    generalize Q_F C D = q0 at hQ0 ⊢
    generalize Q_F (2 * C) D = qe at hQE ⊢
    generalize Q_F (2 * C) (C + D) = qo0 at hQO0 ⊢
    field_simp
    ring
  rw [hclear]
  set t := C - D
  have ht : 0 ≤ t := sub_nonneg.mpr hCD
  have hCeq : C = t + D := by dsimp [t]; ring
  rw [hCeq]
  have hid : 32 * 8 * (2 * (t + D) + D) ^ 3 * (3 * (t + D) + D) ^ 3 *
        Q_F (2 * (t + D)) D * Q_F (2 * (t + D)) (t + D + D) * P_F (t + D) D
      - 125 * ((t + D + D) ^ 3 * (3 * (t + D) + D) ^ 3 * Q_F (t + D) D * Q_F (2 * (t + D)) (t + D + D) * P_F (2 * (t + D)) D
             + D ^ 3 * (2 * (t + D) + D) ^ 3 * Q_F (t + D) D * Q_F (2 * (t + D)) D * P_F (2 * (t + D)) (t + D + D)) =
      370813420800 * D ^ 16 + 31008708959616 * t * D ^ 15 + 277910958981312 * t ^ 2 * D ^ 14 +
      1194365542632768 * t ^ 3 * D ^ 13 + 3161811169282992 * t ^ 4 * D ^ 12 + 5718780934162728 * t ^ 5 * D ^ 11 +
      7453583570410404 * t ^ 6 * D ^ 10 + 7206305505080116 * t ^ 7 * D ^ 9 + 5243541127053392 * t ^ 8 * D ^ 8 +
      2882659283100512 * t ^ 9 * D ^ 7 + 1190836405581184 * t ^ 10 * D ^ 6 + 363938594284044 * t ^ 11 * D ^ 5 +
      79927058953116 * t ^ 12 * D ^ 4 + 11987169035544 * t ^ 13 * D ^ 3 + 1115909600400 * t ^ 14 * D ^ 2 +
      51711996672 * t ^ 15 * D + 435974400 * t ^ 16 := by
    unfold P_F Q_F; ring
  rw [hid]; positivity

/-! ### 4. Path-list enumeration and tree-sum contraction lemmas -/

def pathsOf (alphabet : List StepKind) : Nat → List (List StepKind)
  | 0 => [[]]
  | n + 1 => alphabet.flatMap (fun k => (pathsOf alphabet n).map (k :: ·))

theorem pathsOf_length (alphabet : List StepKind) (n : Nat) :
    (pathsOf alphabet n).length = alphabet.length ^ n := by
  induction n with
  | zero => simp [pathsOf]
  | succ n ih =>
    simp only [pathsOf, List.length_flatMap, List.map_map, Function.comp_def, List.length_map, ih,
      List.map_const', List.sum_replicate, smul_eq_mul, pow_succ']

theorem mem_pathsOf {alphabet : List StepKind} {n : Nat} {γ : List StepKind} :
    γ ∈ pathsOf alphabet n ↔ γ.length = n ∧ ∀ k ∈ γ, k ∈ alphabet := by
  induction n generalizing γ with
  | zero =>
    simp only [pathsOf, List.mem_singleton, List.length_eq_zero_iff]
    constructor
    · rintro rfl; exact ⟨rfl, fun _ h => by cases h⟩
    · rintro ⟨rfl, _⟩; rfl
  | succ n ih =>
    simp only [pathsOf, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨k, hk, γ', hγ', rfl⟩
      obtain ⟨hl, hm⟩ := ih.mp hγ'
      refine ⟨by simp [hl], fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hk
      · exact hm x hx
    · rintro ⟨hl, hm⟩
      cases γ with
      | nil => simp at hl
      | cons k γ' =>
        refine ⟨k, hm k List.mem_cons_self, γ', ih.mpr ⟨by simpa using hl, fun x hx => hm x (List.mem_cons_of_mem _ hx)⟩, rfl⟩

theorem mem_pathsOf_all {n : Nat} {γ : List StepKind} (hl : γ.length = n) :
    γ ∈ pathsOf allKinds n :=
  mem_pathsOf.mpr ⟨hl, fun k _ => by cases k <;> decide⟩

private theorem list_sum_flatMap_real {α β : Type} (xs : List α) (g : α → List β) (f : β → ℝ) :
    ((xs.flatMap g).map f).sum = (xs.map (fun x => ((g x).map f).sum)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

private theorem list_sum_map_le {α : Type} (xs : List α) (f g : α → ℝ)
    (h : ∀ x ∈ xs, f x ≤ g x) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    linarith [h x List.mem_cons_self, ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

private theorem list_sum_mul_left {α : Type} (xs : List α) (c : ℝ) (f : α → ℝ) :
    (xs.map (fun x => c * f x)).sum = c * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, mul_add]

theorem sum_pathsAll_phiF (n : Nat) (C D : Nat) (hC : 0 < C) (hD : 0 < D) :
    ((pathsOf allKinds n).map (fun γ => phiF (runF (C, D) γ).1 (runF (C, D) γ).2)).sum ≤
      phiF C D * rhoF ^ n := by
  induction n generalizing C D with
  | zero => simp [pathsOf, runF]
  | succ n ih =>
    rw [pathsOf, list_sum_flatMap_real]
    simp only [allKinds, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      List.map_map, Function.comp_def, runF_cons, stepF]
    have hE := ih (2 * C) D (by omega) hD
    have hO0 := ih (2 * C) (C + D) (by omega) (by omega)
    have hO1 := ih (2 * D) (C + D) (by omega) (by omega)
    have hc := phiF_contract (C := (C : ℝ)) (D := (D : ℝ)) (by exact_mod_cast hC) (by exact_mod_cast hD)
    have hmul := mul_le_mul_of_nonneg_right hc (by unfold rhoF; positivity : 0 ≤ rhoF ^ n)
    have hsum : phiF ((2 * C : Nat) : ℝ) (D : ℝ) * rhoF ^ n +
        (phiF ((2 * C : Nat) : ℝ) ((C + D : Nat) : ℝ) * rhoF ^ n +
         phiF ((2 * D : Nat) : ℝ) ((C + D : Nat) : ℝ) * rhoF ^ n) =
        (phiF (2 * (C : ℝ)) (D : ℝ) + phiF (2 * (C : ℝ)) ((C : ℝ) + (D : ℝ)) +
         phiF (2 * (D : ℝ)) ((C : ℝ) + (D : ℝ))) * rhoF ^ n := by
      push_cast; ring
    calc _ ≤ phiF ((2 * C : Nat) : ℝ) (D : ℝ) * rhoF ^ n +
              (phiF ((2 * C : Nat) : ℝ) ((C + D : Nat) : ℝ) * rhoF ^ n +
               phiF ((2 * D : Nat) : ℝ) ((C + D : Nat) : ℝ) * rhoF ^ n) :=
            add_le_add hE (add_le_add hO0 hO1)
      _ = (phiF (2 * (C : ℝ)) (D : ℝ) + phiF (2 * (C : ℝ)) ((C : ℝ) + (D : ℝ)) +
           phiF (2 * (D : ℝ)) ((C : ℝ) + (D : ℝ))) * rhoF ^ n := hsum
      _ ≤ (rhoF * phiF C D) * rhoF ^ n := hmul
      _ = phiF C D * rhoF ^ (n + 1) := by rw [pow_succ']; ring

theorem sum_pathsEO0_phiF (n : Nat) (C D : Nat) (hD : 0 < D) (hCD : D ≤ C) :
    ((pathsOf eo0Kinds n).map (fun γ => phiF (runF (C, D) γ).1 (runF (C, D) γ).2)).sum ≤
      phiF C D * rhoEO0 ^ n := by
  induction n generalizing C D with
  | zero => simp [pathsOf, runF]
  | succ n ih =>
    rw [pathsOf, list_sum_flatMap_real]
    simp only [eo0Kinds, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      List.map_map, Function.comp_def, runF_cons, stepF]
    have hE := ih (2 * C) D hD (by omega)
    have hO0 := ih (2 * C) (C + D) (by omega) (by omega)
    have hc := phiF_eo0_contract (C := (C : ℝ)) (D := (D : ℝ)) (by exact_mod_cast hD) (by exact_mod_cast hCD)
    have hmul := mul_le_mul_of_nonneg_right hc (by unfold rhoEO0; positivity : 0 ≤ rhoEO0 ^ n)
    have hsum : phiF ((2 * C : Nat) : ℝ) (D : ℝ) * rhoEO0 ^ n +
        phiF ((2 * C : Nat) : ℝ) ((C + D : Nat) : ℝ) * rhoEO0 ^ n =
        (phiF (2 * (C : ℝ)) (D : ℝ) + phiF (2 * (C : ℝ)) ((C : ℝ) + (D : ℝ))) * rhoEO0 ^ n := by
      push_cast; ring
    calc _ ≤ phiF ((2 * C : Nat) : ℝ) (D : ℝ) * rhoEO0 ^ n +
              phiF ((2 * C : Nat) : ℝ) ((C + D : Nat) : ℝ) * rhoEO0 ^ n := add_le_add hE hO0
      _ = (phiF (2 * (C : ℝ)) (D : ℝ) + phiF (2 * (C : ℝ)) ((C : ℝ) + (D : ℝ))) * rhoEO0 ^ n := hsum
      _ ≤ (rhoEO0 * phiF C D) * rhoEO0 ^ n := hmul
      _ = phiF C D * rhoEO0 ^ (n + 1) := by rw [pow_succ']; ring

theorem sum_pathsAll_phiB (n : Nat) (u v : Nat) (hu : 0 < u) (hv : 0 < v) :
    ((pathsOf allKinds n).map (fun γ => phiB (runBL (u, v) γ).1 (runBL (u, v) γ).2)).sum ≤
      phiB u v * rhoB ^ n := by
  induction n generalizing u v with
  | zero => simp [pathsOf, runBL]
  | succ n ih =>
    rw [pathsOf, list_sum_flatMap_real]
    simp only [allKinds, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      List.map_map, Function.comp_def, runBL, List.foldl_cons, stepB]
    have hE := ih (2 * u) v (by omega) hv
    have hO0 := ih (2 * u + v) v (by omega) hv
    have hO1 := ih v (2 * u + v) hv (by omega)
    have hc := phiB_contract (u := (u : ℝ)) (v := (v : ℝ)) (by exact_mod_cast hu) (by exact_mod_cast hv)
    have hmul := mul_le_mul_of_nonneg_right hc (by unfold rhoB; positivity : 0 ≤ rhoB ^ n)
    have hsum : phiB ((2 * u : Nat) : ℝ) (v : ℝ) * rhoB ^ n +
        (phiB ((2 * u + v : Nat) : ℝ) (v : ℝ) * rhoB ^ n +
         phiB (v : ℝ) ((2 * u + v : Nat) : ℝ) * rhoB ^ n) =
        (phiB (2 * (u : ℝ)) (v : ℝ) + phiB (2 * (u : ℝ) + (v : ℝ)) (v : ℝ) +
         phiB (v : ℝ) (2 * (u : ℝ) + (v : ℝ))) * rhoB ^ n := by
      push_cast; ring
    calc _ ≤ phiB ((2 * u : Nat) : ℝ) (v : ℝ) * rhoB ^ n +
              (phiB ((2 * u + v : Nat) : ℝ) (v : ℝ) * rhoB ^ n +
               phiB (v : ℝ) ((2 * u + v : Nat) : ℝ) * rhoB ^ n) :=
            add_le_add hE (add_le_add hO0 hO1)
      _ = (phiB (2 * (u : ℝ)) (v : ℝ) + phiB (2 * (u : ℝ) + (v : ℝ)) (v : ℝ) +
           phiB (v : ℝ) (2 * (u : ℝ) + (v : ℝ))) * rhoB ^ n := hsum
      _ ≤ (rhoB * phiB u v) * rhoB ^ n := hmul
      _ = phiB u v * rhoB ^ (n + 1) := by rw [pow_succ']; ring

/-! ### 5. Exact trajectory decomposition for `x ∈ (0, p)` and `k₀ = v₂(x)` -/

theorem p_pos : 0 < ECDSAAdd.p := by norm_num [ECDSAAdd.p]
theorem p_odd : ECDSAAdd.p % 2 = 1 := by norm_num [ECDSAAdd.p]
theorem p_lt_256 : ECDSAAdd.p < 2 ^ 256 := by norm_num [ECDSAAdd.p]

private theorem phi_consts :
    phiF 2 1 ≤ 1215 ∧ phiF 1 1 ≤ 5411 ∧ phiB 1 1 ≤ 1539 := by
  unfold phiF phiB P_F Q_F P_B Q_B; norm_num

attribute [local irreducible] Nat.iterate pathsOf phiF phiB P_F Q_F P_B Q_B

theorem canonical_coprime_p {x : Nat} (hx0 : 0 < x) (hxp : x < ECDSAAdd.p) : x.Coprime ECDSAAdd.p :=
  (ECDSAAdd.Secp256k1.p_prime.coprime_iff_not_dvd.mpr
    (fun hd => (Nat.not_le_of_lt hxp) (Nat.le_of_dvd hx0 hd))).symm

theorem exists_term_time {x : Nat} (hx0 : 0 < x) (hxp : x < ECDSAAdd.p)
    (hbad : (SkywalkNat.step^[485] (SkywalkNat.init x ECDSAAdd.p)).u ≠ 0) :
    ∃ L : Nat, 486 ≤ L ∧ L ≤ 512 ∧
      SkywalkNat.step^[L - 1] (SkywalkNat.init x ECDSAAdd.p) = ⟨1, 1⟩ ∧
      (SkywalkNat.step^[L] (SkywalkNat.init x ECDSAAdd.p)).u = 0 := by
  have h512 := (SkywalkNat.terminates_2n ECDSAAdd.p x 256 p_pos hx0 p_odd p_lt_256 (hxp.trans p_lt_256)
    (canonical_coprime_p hx0 hxp)).1
  let P : Nat → Prop := fun n => (SkywalkNat.step^[n] (SkywalkNat.init x ECDSAAdd.p)).u = 0
  have hex : ∃ n, P n := ⟨512, h512⟩
  let L := Nat.find hex
  have hPL : (SkywalkNat.step^[L] (SkywalkNat.init x ECDSAAdd.p)).u = 0 := Nat.find_spec hex
  have hL_le : L ≤ 512 := Nat.find_min' hex h512
  have hL_gt : 485 < L := by
    by_contra hle
    have h485 : (SkywalkNat.step^[485] (SkywalkNat.init x ECDSAAdd.p)).u = 0 := by
      have hrew : 485 = (485 - L) + L := by omega
      rw [hrew, Function.iterate_add_apply]
      exact iter_of_u_zero hPL (485 - L)
    exact hbad h485
  have hprev_ne : (SkywalkNat.step^[L - 1] (SkywalkNat.init x ECDSAAdd.p)).u ≠ 0 :=
    Nat.find_min hex (by omega)
  set z := SkywalkNat.step^[L - 1] (SkywalkNat.init x ECDSAAdd.p)
  have hvalid := SkywalkNat.iter_valid (L - 1) (SkywalkNat.init x ECDSAAdd.p) p_pos p_odd
  have hvpos : 0 < z.v := hvalid.1
  have hvodd : z.v % 2 = 1 := hvalid.2.1
  have hg : z.u.gcd z.v = 1 := hvalid.2.2.trans (canonical_coprime_p hx0 hxp)
  have hstep_z : (SkywalkNat.step z).u = 0 := by
    have hL1 : L = (L - 1) + 1 := by omega
    rw [hL1, Function.iterate_succ_apply'] at hPL
    exact hPL
  have huv : z.u = z.v := by
    unfold SkywalkNat.step at hstep_z
    rw [if_neg hprev_ne] at hstep_z
    split_ifs at hstep_z with he hle
    · dsimp at hstep_z; omega
    · dsimp at hstep_z; omega
    · dsimp at hstep_z; omega
  have hv1 : z.v = 1 := by rw [huv, Nat.gcd_self] at hg; exact hg
  have hu1 : z.u = 1 := huv.trans hv1
  exact ⟨L, by omega, hL_le, SkywalkNat.State.ext hu1 hv1, hPL⟩

private theorem finset_toFinset_sum_le_list_sum {β : Type} [DecidableEq β]
    (bs : List β) (g : β → ℝ) (hg : ∀ b, 0 ≤ g b) :
    ∑ b ∈ bs.toFinset, g b ≤ (bs.map g).sum := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    simp only [List.toFinset_cons, List.map_cons, List.sum_cons]
    by_cases hm : b ∈ bs.toFinset
    · rw [Finset.insert_eq_of_mem hm]; linarith [hg b]
    · rw [Finset.sum_insert hm]; linarith

private theorem card_le_list_sum_fiber {α β : Type} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (bs : List β) (f : α → β) (hf : ∀ a ∈ S, f a ∈ bs) :
    (S.card : ℝ) ≤ (bs.map (fun b => ((S.filter (fun a => f a = b)).card : ℝ))).sum := by
  have h1 : S.card = ∑ b ∈ bs.toFinset, (S.filter (fun a => f a = b)).card := by
    rw [← Finset.card_biUnion]
    · congr 1; ext a
      simp only [Finset.mem_biUnion, List.mem_toFinset, Finset.mem_filter]
      exact ⟨fun ha => ⟨f a, hf a ha, ha, rfl⟩, fun ⟨_, _, ha, _⟩ => ha⟩
    · intro b₁ _ b₂ _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro a ha1 ha2
      exact hne ((Finset.mem_filter.mp ha1).2.symm.trans (Finset.mem_filter.mp ha2).2)
  rw [h1, Nat.cast_sum]
  exact finset_toFinset_sum_le_list_sum bs _ (fun _ => Nat.cast_nonneg _)

theorem forward_prefix_fiber_card (S : Finset Nat) (hS_sub : ∀ x ∈ S, 0 < x ∧ x < ECDSAAdd.p)
    (t : Nat) (γ : List StepKind)
    (hγ_eq : ∀ x ∈ S, traceKinds (SkywalkNat.init x ECDSAAdd.p) t = γ ∧
      0 < (SkywalkNat.step^[t] (SkywalkNat.init x ECDSAAdd.p)).u)
    (hC : 0 < (runF (0, 1) γ).1) (hD : 0 < (runF (0, 1) γ).2)
    (hcop : (runF (0, 1) γ).1.Coprime (runF (0, 1) γ).2) :
    S.card ≤ ECDSAAdd.p / ((runF (0, 1) γ).1 * (runF (0, 1) γ).2) + 1 := by
  set C := (runF (0, 1) γ).1
  set D := (runF (0, 1) γ).2
  let f : Nat → Nat := fun x => (SkywalkNat.step^[t] (SkywalkNat.init x ECDSAAdd.p)).v
  let T := (Finset.Ioo 0 ECDSAAdd.p).filter (fun v => ∃ u > 0, C * u + D * v = ECDSAAdd.p)
  have hmem : ∀ x ∈ S, f x ∈ T := by
    intro x hx
    obtain ⟨_, _⟩ := hS_sub x hx
    obtain ⟨htr, hu_pos⟩ := hγ_eq x hx
    have hval := SkywalkNat.iter_valid t (SkywalkNat.init x ECDSAAdd.p) p_pos p_odd
    have halive : ∀ i < t, 0 < (SkywalkNat.step^[i] (SkywalkNat.init x ECDSAAdd.p)).u := fun i hi =>
      iter_alive_of_u_ne_zero _ hi.le (Nat.ne_of_gt hu_pos)
    have hB := runB_traceKinds (SkywalkNat.init x ECDSAAdd.p) t p_pos p_odd halive
    rw [htr] at hB
    have hdot := runF_runB_dot γ 0 1 (SkywalkNat.step^[t] (SkywalkNat.init x ECDSAAdd.p)).u (f x)
    rw [hB] at hdot
    simp only [SkywalkNat.init, zero_mul, one_mul, zero_add] at hdot
    have hv_lt : f x < ECDSAAdd.p := by
      have h1 : 1 ≤ C * (SkywalkNat.step^[t] (SkywalkNat.init x ECDSAAdd.p)).u := Nat.mul_pos hC hu_pos
      have h2 : f x ≤ D * f x := Nat.le_mul_of_pos_left _ hD
      change C * (SkywalkNat.step^[t] (SkywalkNat.init x ECDSAAdd.p)).u + D * f x = ECDSAAdd.p at hdot
      omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨hval.1, hv_lt⟩,
      (SkywalkNat.step^[t] (SkywalkNat.init x ECDSAAdd.p)).u, hu_pos, hdot⟩
  have hinj : Set.InjOn f (S : Set Nat) := by
    intro x₁ hx₁ x₂ hx₂ hfeq
    obtain ⟨htr₁, hu₁⟩ := hγ_eq x₁ (Finset.mem_coe.mp hx₁)
    obtain ⟨htr₂, hu₂⟩ := hγ_eq x₂ (Finset.mem_coe.mp hx₂)
    have halive₁ : ∀ i < t, 0 < (SkywalkNat.step^[i] (SkywalkNat.init x₁ ECDSAAdd.p)).u := fun i hi =>
      iter_alive_of_u_ne_zero _ hi.le (Nat.ne_of_gt hu₁)
    have halive₂ : ∀ i < t, 0 < (SkywalkNat.step^[i] (SkywalkNat.init x₂ ECDSAAdd.p)).u := fun i hi =>
      iter_alive_of_u_ne_zero _ hi.le (Nat.ne_of_gt hu₂)
    have hB₁ := runB_traceKinds (SkywalkNat.init x₁ ECDSAAdd.p) t p_pos p_odd halive₁
    have hB₂ := runB_traceKinds (SkywalkNat.init x₂ ECDSAAdd.p) t p_pos p_odd halive₂
    rw [htr₁] at hB₁; rw [htr₂] at hB₂
    have hd₁ := runF_runB_dot γ 0 1 (SkywalkNat.step^[t] (SkywalkNat.init x₁ ECDSAAdd.p)).u (f x₁)
    have hd₂ := runF_runB_dot γ 0 1 (SkywalkNat.step^[t] (SkywalkNat.init x₂ ECDSAAdd.p)).u (f x₂)
    rw [hB₁] at hd₁; rw [hB₂] at hd₂
    simp only [SkywalkNat.init, zero_mul, one_mul, zero_add] at hd₁ hd₂
    have hueq : (SkywalkNat.step^[t] (SkywalkNat.init x₁ ECDSAAdd.p)).u =
        (SkywalkNat.step^[t] (SkywalkNat.init x₂ ECDSAAdd.p)).u := by
      have : C * (SkywalkNat.step^[t] (SkywalkNat.init x₁ ECDSAAdd.p)).u =
          C * (SkywalkNat.step^[t] (SkywalkNat.init x₂ ECDSAAdd.p)).u := by
        change C * (SkywalkNat.step^[t] (SkywalkNat.init x₁ ECDSAAdd.p)).u + D * f x₁ = ECDSAAdd.p at hd₁
        change C * (SkywalkNat.step^[t] (SkywalkNat.init x₂ ECDSAAdd.p)).u + D * f x₂ = ECDSAAdd.p at hd₂
        rw [hfeq] at hd₁; omega
      exact Nat.eq_of_mul_eq_mul_left hC this
    have hpair : ((SkywalkNat.step^[t] (SkywalkNat.init x₁ ECDSAAdd.p)).u, f x₁) =
        ((SkywalkNat.step^[t] (SkywalkNat.init x₂ ECDSAAdd.p)).u, f x₂) := Prod.ext hueq hfeq
    have h0 := congrArg (fun q => (runB q γ).1) hpair
    dsimp only at h0
    have h1 : (runB ((SkywalkNat.step^[t] (SkywalkNat.init x₁ ECDSAAdd.p)).u, f x₁) γ).1 = x₁ := by
      change (runB ((SkywalkNat.step^[t] (SkywalkNat.init x₁ ECDSAAdd.p)).u, (SkywalkNat.step^[t] (SkywalkNat.init x₁ ECDSAAdd.p)).v) γ).1 = x₁
      rw [hB₁]; rfl
    have h2 : (runB ((SkywalkNat.step^[t] (SkywalkNat.init x₂ ECDSAAdd.p)).u, f x₂) γ).1 = x₂ := by
      change (runB ((SkywalkNat.step^[t] (SkywalkNat.init x₂ ECDSAAdd.p)).u, (SkywalkNat.step^[t] (SkywalkNat.init x₂ ECDSAAdd.p)).v) γ).1 = x₂
      rw [hB₂]; rfl
    rw [h1, h2] at h0; exact h0
  exact (Finset.card_le_card_of_injOn f (fun x hx => Finset.mem_coe.mpr (hmem x (Finset.mem_coe.mp hx))) hinj).trans
    (linear_diophantine_card C D ECDSAAdd.p hC hD hcop)

theorem backward_state_fiber_card (S : Finset Nat) (hS_sub : ∀ x ∈ S, 0 < x ∧ x < ECDSAAdd.p)
    (t u v : Nat) (hu : 0 < u) (hv : 0 < v) (hcop : u.Coprime v)
    (hreach : ∀ x ∈ S, SkywalkNat.step^[t] (SkywalkNat.init x ECDSAAdd.p) = ⟨u, v⟩ ∧
      0 < (runF (0, 1) (traceKinds (SkywalkNat.init x ECDSAAdd.p) t)).1) :
    S.card ≤ 2 * (ECDSAAdd.p / (u * v) + 1) := by
  letI : Fact (Nat.Prime ECDSAAdd.p) := ⟨ECDSAAdd.Secp256k1.p_prime⟩
  let T := (Finset.Ioo 0 ECDSAAdd.p).filter (fun D => ∃ C > 0, u * C + v * D = ECDSAAdd.p)
  let g : Nat → Nat × Bool := fun x =>
    let γ := traceKinds (SkywalkNat.init x ECDSAAdd.p) t
    let D := (runF (0, 1) γ).2
    let sgn := decide (((runF (1, 0) γ).1 : ℤ) * D - ((runF (1, 0) γ).2 : ℤ) * (runF (0, 1) γ).1 = (2 : ℤ) ^ t)
    (D, sgn)
  have hD_pres : ∀ (l : List StepKind) (C0 D0 : Nat), 0 < D0 → 0 < (runF (C0, D0) l).2 := by
    intro l; induction l with
    | nil => intro _ _ h0; exact h0
    | cons k l ih =>
      intro C0 D0 h0; rw [runF_cons]; apply ih
      cases k <;> dsimp [stepF] <;> omega
  have hmem : ∀ x ∈ S, g x ∈ T ×ˢ (Finset.univ : Finset Bool) := by
    intro x hx
    obtain ⟨hstate, hCpos⟩ := hreach x hx
    set γ := traceKinds (SkywalkNat.init x ECDSAAdd.p) t
    have halive : ∀ i < t, 0 < (SkywalkNat.step^[i] (SkywalkNat.init x ECDSAAdd.p)).u := fun i hi =>
      iter_alive_of_u_ne_zero _ hi.le (by rw [hstate]; exact Nat.ne_of_gt hu)
    have hB := runB_traceKinds (SkywalkNat.init x ECDSAAdd.p) t p_pos p_odd halive
    rw [hstate] at hB
    have hdot := runF_runB_dot γ 0 1 u v
    rw [hB] at hdot
    simp only [SkywalkNat.init, zero_mul, one_mul, zero_add] at hdot
    have hDpos : 0 < (runF (0, 1) γ).2 := hD_pres γ 0 1 (by omega)
    have hDlt : (runF (0, 1) γ).2 < ECDSAAdd.p := by
      have h1 : 1 ≤ (runF (0, 1) γ).1 * u := Nat.mul_pos hCpos hu
      have h2 : (runF (0, 1) γ).2 ≤ (runF (0, 1) γ).2 * v := Nat.le_mul_of_pos_right _ hv
      linarith
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨hDpos, hDlt⟩,
      (runF (0, 1) γ).1, hCpos, by linarith⟩, Finset.mem_univ _⟩
  have hinj : Set.InjOn g (S : Set Nat) := by
    intro x₁ hx₁ x₂ hx₂ hgeq
    obtain ⟨_, hx₁p⟩ := hS_sub x₁ hx₁
    obtain ⟨_, hx₂p⟩ := hS_sub x₂ hx₂
    have hcong : ∀ x ∈ S,
        let γ := traceKinds (SkywalkNat.init x ECDSAAdd.p) t
        (((runF (0, 1) γ).2 : ECDSAAdd.Fp) * (x : ECDSAAdd.Fp) =
          (if (g x).2 then (1 : ECDSAAdd.Fp) else -1) * ((2 : ECDSAAdd.Fp) ^ t * (u : ECDSAAdd.Fp))) ∧
        ((runF (0, 1) γ).2 : ECDSAAdd.Fp) ≠ 0 := by
      intro x hx
      obtain ⟨hstate, _⟩ := hreach x hx
      set γ := traceKinds (SkywalkNat.init x ECDSAAdd.p) t
      have hlen : γ.length = t := traceKinds_length _ _
      have halive : ∀ i < t, 0 < (SkywalkNat.step^[i] (SkywalkNat.init x ECDSAAdd.p)).u := fun i hi =>
        iter_alive_of_u_ne_zero _ hi.le (by rw [hstate]; exact Nat.ne_of_gt hu)
      have hB := runB_traceKinds (SkywalkNat.init x ECDSAAdd.p) t p_pos p_odd halive
      rw [hstate] at hB
      have hdotC := runF_runB_dot γ 0 1 u v
      have hdotA := runF_runB_dot γ 1 0 u v
      rw [hB] at hdotC hdotA
      simp only [SkywalkNat.init, zero_mul, one_mul, zero_add, add_zero] at hdotC hdotA
      obtain ⟨sgn, hdet⟩ := runF_det_abs γ 1 0 0 1
      rw [hlen] at hdet
      simp only [Nat.cast_one, Nat.cast_zero, mul_one, mul_zero, sub_zero] at hdet
      have hsgn_eq : (g x).2 = sgn := by
        dsimp only [g]
        cases sgn
        · simp only [Bool.false_eq_true, ↓reduceIte, neg_one_mul] at hdet
          rw [hdet, decide_eq_false_iff_not]
          have h2pos : (0 : ℤ) < (2 : ℤ) ^ t := by positivity
          omega
        · simp only [↓reduceIte, one_mul] at hdet
          rw [hdet]; simp
      have helim : ((runF (0, 1) γ).2 : ℤ) * x - ((runF (1, 0) γ).2 : ℤ) * ECDSAAdd.p =
          (if sgn then (1 : ℤ) else -1) * (2 : ℤ) ^ t * u := by
        have h1 : ((runF (1, 0) γ).1 : ℤ) * u + ((runF (1, 0) γ).2 : ℤ) * v = x := by exact_mod_cast hdotA
        have h2 : ((runF (0, 1) γ).1 : ℤ) * u + ((runF (0, 1) γ).2 : ℤ) * v = ECDSAAdd.p := by exact_mod_cast hdotC
        calc ((runF (0, 1) γ).2 : ℤ) * x - ((runF (1, 0) γ).2 : ℤ) * ECDSAAdd.p
            = ((runF (0, 1) γ).2 : ℤ) * (((runF (1, 0) γ).1 : ℤ) * u + ((runF (1, 0) γ).2 : ℤ) * v) -
              ((runF (1, 0) γ).2 : ℤ) * (((runF (0, 1) γ).1 : ℤ) * u + ((runF (0, 1) γ).2 : ℤ) * v) := by rw [h1, h2]
          _ = (((runF (1, 0) γ).1 : ℤ) * (runF (0, 1) γ).2 - ((runF (1, 0) γ).2 : ℤ) * (runF (0, 1) γ).1) * u := by ring
          _ = (if sgn then (1 : ℤ) else -1) * (2 : ℤ) ^ t * u := by rw [hdet]
      have hcast := congrArg (Int.cast (R := ECDSAAdd.Fp)) helim
      simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_pow, Int.cast_ofNat,
        ZMod.natCast_self, mul_zero, sub_zero] at hcast
      have hif : (Int.cast (if sgn then (1 : ℤ) else -1) : ECDSAAdd.Fp) = (if (g x).2 then (1 : ECDSAAdd.Fp) else -1) := by
        rw [hsgn_eq]; cases sgn <;> simp
      rw [hif, mul_assoc] at hcast
      have hD_mem := (Finset.mem_filter.mp (Finset.mem_product.mp (hmem x hx)).1).1
      obtain ⟨hDpos, hDlt⟩ := Finset.mem_Ioo.mp hD_mem
      have hDne : ((runF (0, 1) γ).2 : ECDSAAdd.Fp) ≠ 0 := by
        intro hz
        have hdvd := (ZMod.natCast_eq_zero_iff _ _).mp hz
        exact (Nat.not_le_of_lt hDlt) (Nat.le_of_dvd hDpos hdvd)
      exact ⟨hcast, hDne⟩
    obtain ⟨hc1, hne1⟩ := hcong x₁ (Finset.mem_coe.mp hx₁)
    obtain ⟨hc2, _⟩ := hcong x₂ (Finset.mem_coe.mp hx₂)
    have hD_eq : (runF (0, 1) (traceKinds (SkywalkNat.init x₁ ECDSAAdd.p) t)).2 =
        (runF (0, 1) (traceKinds (SkywalkNat.init x₂ ECDSAAdd.p) t)).2 := congrArg Prod.fst hgeq
    have hs_eq : (g x₁).2 = (g x₂).2 := congrArg Prod.snd hgeq
    rw [← hD_eq, ← hs_eq] at hc2
    have hx_fp : (x₁ : ECDSAAdd.Fp) = (x₂ : ECDSAAdd.Fp) := mul_left_cancel₀ hne1 (hc1.trans hc2.symm)
    have hv1 : (x₁ : ECDSAAdd.Fp).val = x₁ := ZMod.val_natCast_of_lt hx₁p
    have hv2 : (x₂ : ECDSAAdd.Fp).val = x₂ := ZMod.val_natCast_of_lt hx₂p
    rw [← hv1, ← hv2, hx_fp]
  have hc := Finset.card_le_card_of_injOn g (fun x hx => Finset.mem_coe.mpr (hmem x (Finset.mem_coe.mp hx))) hinj
  rw [Finset.card_product, Finset.card_univ, Fintype.card_bool, mul_comm] at hc
  exact hc.trans (Nat.mul_le_mul_left 2 (linear_diophantine_card u v ECDSAAdd.p hu hv hcop))

/-! ### 6. Leading-even-steps (`k₀ = v₂(x)`) forced `E/O0` phase -/

theorem leading_E_steps (x k0 : Nat) (hdiv : 2 ^ k0 ∣ x) (hodd : (x / 2 ^ k0) % 2 = 1)
    (hxp : x < ECDSAAdd.p) :
    SkywalkNat.step^[k0] (SkywalkNat.init x ECDSAAdd.p) = ⟨x / 2 ^ k0, ECDSAAdd.p⟩ ∧
    SkywalkNat.step^[k0 + 1] (SkywalkNat.init x ECDSAAdd.p) = ⟨(ECDSAAdd.p - x / 2 ^ k0) / 2, x / 2 ^ k0⟩ ∧
    traceKinds (SkywalkNat.init x ECDSAAdd.p) (k0 + 1) = List.replicate k0 .E ++ [.O1] ∧
    runF (0, 1) (List.replicate k0 .E ++ [.O1]) = (2, 1) := by
  have hx_pos : 0 < x := by
    by_contra h0; have hx0 : x = 0 := by omega
    rw [hx0] at hodd; simp at hodd
  have hk0_step : ∀ j ≤ k0, SkywalkNat.step^[j] (SkywalkNat.init x ECDSAAdd.p) = ⟨x / 2 ^ j, ECDSAAdd.p⟩ ∧
      traceKinds (SkywalkNat.init x ECDSAAdd.p) j = List.replicate j .E := by
    intro j hj
    induction j with
    | zero => simp [SkywalkNat.init, traceKinds]
    | succ j ih =>
      obtain ⟨hst, htr⟩ := ih (by omega)
      have h2j : 2 ^ (j + 1) ∣ x := dvd_trans (Nat.pow_dvd_pow 2 hj) hdiv
      have hdivj : (x / 2 ^ j) % 2 = 0 := by
        obtain ⟨q, rfl⟩ := h2j
        rw [pow_succ, mul_assoc, Nat.mul_div_cancel_left _ (Nat.two_pow_pos j)]
        omega
      have hne : x / 2 ^ j ≠ 0 := by
        obtain ⟨q, hq⟩ := h2j
        have hq0 : 0 < q := by
          by_contra h; have hqz : q = 0 := by omega
          rw [hqz] at hq; simp at hq; omega
        rw [hq, pow_succ, mul_assoc, Nat.mul_div_cancel_left _ (Nat.two_pow_pos j)]; omega
      have hstep : SkywalkNat.step ⟨x / 2 ^ j, ECDSAAdd.p⟩ = ⟨x / 2 ^ (j + 1), ECDSAAdd.p⟩ := by
        unfold SkywalkNat.step; rw [if_neg hne, if_pos hdivj, Nat.div_div_eq_div_mul, ← pow_succ]
      have hkd : stepKind ⟨x / 2 ^ j, ECDSAAdd.p⟩ = .E := by unfold stepKind; rw [if_pos hdivj]
      refine ⟨?_, ?_⟩
      · rw [Function.iterate_succ_apply', hst, hstep]
      · rw [traceKinds_add _ j 1, htr, hst]
        simp only [traceKinds, hkd, List.replicate_succ']
  obtain ⟨hst_k, htr_k⟩ := hk0_step k0 (le_refl k0)
  have hlt_p : x / 2 ^ k0 < ECDSAAdd.p := (Nat.div_le_self x _).trans_lt hxp
  have hne_k : x / 2 ^ k0 ≠ 0 := by omega
  have hnot_even : (x / 2 ^ k0) % 2 ≠ 0 := by omega
  have hnot_le : ¬ ECDSAAdd.p ≤ x / 2 ^ k0 := by omega
  have hstep_o1 : SkywalkNat.step ⟨x / 2 ^ k0, ECDSAAdd.p⟩ = ⟨(ECDSAAdd.p - x / 2 ^ k0) / 2, x / 2 ^ k0⟩ := by
    unfold SkywalkNat.step; rw [if_neg hne_k, if_neg hnot_even, if_neg hnot_le]
  have hkd_o1 : stepKind ⟨x / 2 ^ k0, ECDSAAdd.p⟩ = .O1 := by
    unfold stepKind; rw [if_neg hnot_even, if_neg hnot_le]
  have hrunF_rep : ∀ n, runF (0, 1) (List.replicate n .E) = (0, 1) := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, runF_cons, stepF, ih]
  refine ⟨hst_k, ?_, ?_, ?_⟩
  · rw [Function.iterate_succ_apply', hst_k, hstep_o1]
  · rw [traceKinds_add _ k0 1, htr_k, hst_k]; simp [traceKinds, hkd_o1]
  · rw [runF_append, hrunF_rep k0]; rfl

theorem forced_eo0_phase (x k0 : Nat) (hk0 : 1 ≤ k0) (hdiv : 2 ^ k0 ∣ x)
    (hodd : (x / 2 ^ k0) % 2 = 1) (hxp : x < ECDSAAdd.p) :
    let z1 := SkywalkNat.step^[k0 + 1] (SkywalkNat.init x ECDSAAdd.p)
    let γ1 := traceKinds z1 (k0 - 1)
    let z2 := SkywalkNat.step^[2 * k0] (SkywalkNat.init x ECDSAAdd.p)
    (∀ k ∈ γ1, k ∈ eo0Kinds) ∧
    (runF (2, 1) γ1).1 = 2 ^ k0 ∧ (runF (2, 1) γ1).2 < 2 ^ k0 ∧
    (z2.u : ℝ) + (z2.v : ℝ) < 2 * (ECDSAAdd.p : ℝ) / (2 : ℝ) ^ k0 := by
  obtain ⟨_, hz1_eq, _, _⟩ := leading_E_steps x k0 hdiv hodd hxp
  set v0 := x / 2 ^ k0
  have hv0_lt : 2 ^ k0 * v0 < ECDSAAdd.p := by
    have : 2 ^ k0 * v0 = x := Nat.mul_div_cancel' hdiv
    omega
  have hv0_pos : 0 < v0 := Nat.pos_of_ne_zero (fun h0 => by have : v0 % 2 = 1 := hodd; rw [h0] at this; simp at this)
  have hstep_ind : ∀ j ≤ k0 - 1,
      let zj := SkywalkNat.step^[j] (SkywalkNat.step^[k0 + 1] (SkywalkNat.init x ECDSAAdd.p))
      let γj := traceKinds (SkywalkNat.step^[k0 + 1] (SkywalkNat.init x ECDSAAdd.p)) j
      (∀ k ∈ γj, k ∈ eo0Kinds) ∧
      zj.v = v0 ∧
      (runF (2, 1) γj).1 = 2 ^ (j + 1) ∧
      (runF (2, 1) γj).2 < 2 ^ (j + 1) ∧
      2 ^ (j + 1) * zj.u + (runF (2, 1) γj).2 * v0 = ECDSAAdd.p := by
    intro j hj
    induction j with
    | zero =>
      refine ⟨fun _ h => by simp [traceKinds] at h, ?_, by simp [traceKinds, runF], by simp [traceKinds, runF], ?_⟩
      · simp [hz1_eq]
      · simp only [Function.iterate_zero_apply, hz1_eq, traceKinds, runF, List.foldl_nil, Nat.zero_add, pow_one, one_mul]
        have hpo := p_odd
        have hltp : v0 < ECDSAAdd.p := (Nat.div_le_self x _).trans_lt hxp
        have hv0_odd : v0 % 2 = 1 := hodd
        omega
    | succ j ih =>
      obtain ⟨hEO, hvj, hCj, hDj, hlin⟩ := ih (by omega)
      set zj := SkywalkNat.step^[j] (SkywalkNat.step^[k0 + 1] (SkywalkNat.init x ECDSAAdd.p))
      set γj := traceKinds (SkywalkNat.step^[k0 + 1] (SkywalkNat.init x ECDSAAdd.p)) j
      have hgt : v0 < zj.u := by
        have hpow_le : 2 ^ (j + 2) ≤ 2 ^ k0 := Nat.pow_le_pow_right (by decide) (by omega)
        have hsum_lt : (2 ^ (j + 1) + (runF (2, 1) γj).2) * v0 < ECDSAAdd.p := by
          have h1 : 2 ^ (j + 1) + (runF (2, 1) γj).2 ≤ 2 ^ (j + 2) := by
            rw [show j + 2 = (j + 1) + 1 by omega, pow_succ]; omega
          have h2 := Nat.mul_le_mul_right v0 (h1.trans hpow_le)
          linarith
        nlinarith
      have hkd_in : stepKind zj ∈ eo0Kinds := by
        unfold stepKind eo0Kinds
        split_ifs with he hle
        · simp
        · simp
        · exfalso; rw [hvj] at hle; omega
      have htr_succ : traceKinds (SkywalkNat.step^[k0 + 1] (SkywalkNat.init x ECDSAAdd.p)) (j + 1) =
          γj ++ [stepKind zj] := by
        rw [traceKinds_add _ j 1]; rfl
      have hstep_v : (SkywalkNat.step zj).v = v0 := by
        unfold SkywalkNat.step
        rw [if_neg (by omega)]
        split_ifs with he hle
        · exact hvj
        · exact hvj
        · exfalso; rw [hvj] at hle; omega
      have hB_one := stepB_step zj (by omega) (by rw [hvj]; exact hodd)
      have hdot_one := stepF_dot (stepKind zj) (runF (2, 1) γj).1 (runF (2, 1) γj).2
        (SkywalkNat.step zj).u (SkywalkNat.step zj).v
      rw [hB_one, hvj] at hdot_one
      have hF_succ : runF (2, 1) (γj ++ [stepKind zj]) = stepF (stepKind zj) (runF (2, 1) γj) := by
        rw [runF_append]; rfl
      have hC_succ : (stepF (stepKind zj) (runF (2, 1) γj)).1 = 2 ^ (j + 2) := by
        simp only [eo0Kinds, List.mem_cons, List.not_mem_nil, or_false] at hkd_in
        rcases hkd_in with hk | hk <;> rw [hk] <;> simp [stepF, hCj, pow_succ']
      have hD_succ : (stepF (stepKind zj) (runF (2, 1) γj)).2 < 2 ^ (j + 2) := by
        simp only [eo0Kinds, List.mem_cons, List.not_mem_nil, or_false] at hkd_in
        rcases hkd_in with hk | hk <;> rw [hk] <;> simp [stepF, hCj, pow_succ'] <;> omega
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro k hk; rw [htr_succ, List.mem_append, List.mem_singleton] at hk
        rcases hk with h | rfl
        · exact hEO k h
        · exact hkd_in
      · rw [Function.iterate_succ_apply']; exact hstep_v
      · rw [htr_succ, hF_succ]; exact hC_succ
      · rw [htr_succ, hF_succ]; exact hD_succ
      · rw [htr_succ, hF_succ, Function.iterate_succ_apply']
        have hdot' : 2 ^ (j + 2) * (SkywalkNat.step zj).u + (stepF (stepKind zj) (runF (2, 1) γj)).2 * v0 =
            2 ^ (j + 1) * zj.u + (runF (2, 1) γj).2 * v0 := by
          rw [Prod.mk.eta] at hdot_one
          rw [hC_succ, hstep_v, hCj] at hdot_one
          exact hdot_one
        exact hdot'.trans hlin
  obtain ⟨hEO, hv2, hC2, hD2, hlin2⟩ := hstep_ind (k0 - 1) (le_refl _)
  have h2k : (k0 - 1) + (k0 + 1) = 2 * k0 := by omega
  have hz2_eq : SkywalkNat.step^[2 * k0] (SkywalkNat.init x ECDSAAdd.p) =
      SkywalkNat.step^[k0 - 1] (SkywalkNat.step^[k0 + 1] (SkywalkNat.init x ECDSAAdd.p)) := by
    rw [← h2k, Function.iterate_add_apply]
  have hsub1 : (k0 - 1) + 1 = k0 := by omega
  rw [hsub1] at hC2 hD2 hlin2
  rw [← hz2_eq] at hv2 hlin2
  set z2 := SkywalkNat.step^[2 * k0] (SkywalkNat.init x ECDSAAdd.p)
  have hu2_mul : 2 ^ k0 * z2.u < ECDSAAdd.p := by
    have hD_pos : 0 < (runF (2, 1) (traceKinds (SkywalkNat.step^[k0 + 1] (SkywalkNat.init x ECDSAAdd.p)) (k0 - 1))).2 :=
      (runF_pos _ (by omega) (by omega)).2
    have : 1 ≤ (runF (2, 1) (traceKinds (SkywalkNat.step^[k0 + 1] (SkywalkNat.init x ECDSAAdd.p)) (k0 - 1))).2 * v0 :=
      Nat.mul_pos hD_pos hv0_pos
    linarith
  have hsum_mul : 2 ^ k0 * (z2.u + z2.v) < 2 * ECDSAAdd.p := by
    rw [hv2]; linarith
  have hsum_real : (z2.u : ℝ) + (z2.v : ℝ) < 2 * (ECDSAAdd.p : ℝ) / (2 : ℝ) ^ k0 := by
    rw [lt_div_iff₀ (by positivity)]
    have hcast : ((2 ^ k0 * (z2.u + z2.v) : Nat) : ℝ) < ((2 * ECDSAAdd.p : Nat) : ℝ) := by exact_mod_cast hsum_mul
    push_cast at hcast; linarith
  exact ⟨hEO, hC2, hD2, hsum_real⟩

/-! ### 7. Per-`k₀` 3-case bound (Case 1 + Case 2 + Case 3, geometric sum in `L ≥ 486`) -/

def Bad485 : Finset Nat :=
  (Finset.Ioo 0 ECDSAAdd.p).filter (fun x => (SkywalkNat.step^[485] (SkywalkNat.init x ECDSAAdd.p)).u ≠ 0)

def qL : ℝ := 38 / 100

theorem geom_sum_le_inv {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : Nat) :
    ∑ j ∈ Finset.range n, r ^ j ≤ 1 / (1 - r) := by
  have h1 : (1 - r) * ∑ j ∈ Finset.range n, r ^ j = 1 - r ^ n := by
    have := geom_sum_mul_neg r n
    linarith
  have h2 : 1 - r ^ n ≤ 1 := by have : 0 ≤ r ^ n := pow_nonneg hr0 n; linarith
  rw [le_div_iff₀ (by linarith)]
  linarith

theorem case3_card_bound (S : Finset Nat) (hS_sub : S ⊆ Bad485)
    (t : Nat) (ht : t ≤ 485) (T0 : ℝ) (hT0 : 0 < T0)
    (hC_pos : ∀ x ∈ S, 0 < (runF (0, 1) (traceKinds (SkywalkNat.init x ECDSAAdd.p) t)).1)
    (hPhiB : ∀ x ∈ S, ∀ L, 486 ≤ L → L ≤ 512 →
      SkywalkNat.step^[L - 1] (SkywalkNat.init x ECDSAAdd.p) = ⟨1, 1⟩ →
      T0 * qL ^ (L - 486) < phiB ((SkywalkNat.step^[t] (SkywalkNat.init x ECDSAAdd.p)).u : ℝ)
        ((SkywalkNat.step^[t] (SkywalkNat.init x ECDSAAdd.p)).v : ℝ)) :
    (S.card : ℝ) ≤ (2 : ℝ) ^ 256 *
      ((2 * phiB 1 1 * (rhoB / 2) ^ (485 - t) / (1 - (rhoB / 2) / qL) +
        (2 / (2 : ℝ) ^ 256) * phiB 1 1 * rhoB ^ (485 - t) / (1 - rhoB / qL)) / T0) := by
  let SL : Nat → Finset Nat := fun j =>
    S.filter (fun x => SkywalkNat.step^[485 + j] (SkywalkNat.init x ECDSAAdd.p) = ⟨1, 1⟩ ∧
      (SkywalkNat.step^[486 + j] (SkywalkNat.init x ECDSAAdd.p)).u = 0)
  have hcov : S ⊆ (Finset.range 27).biUnion SL := by
    intro x hx
    have hbad := Finset.mem_filter.mp (hS_sub hx)
    obtain ⟨hx0, hxp⟩ := Finset.mem_Ioo.mp hbad.1
    obtain ⟨L, hL1, hL2, hterm1, hterm0⟩ := exists_term_time hx0 hxp hbad.2
    refine Finset.mem_biUnion.mpr ⟨L - 486, Finset.mem_range.mpr (by omega),
      Finset.mem_filter.mpr ⟨hx, by rwa [show 485 + (L - 486) = L - 1 by omega],
        by rwa [show 486 + (L - 486) = L by omega]⟩⟩
  have hcard_sum : (S.card : ℝ) ≤ ∑ j ∈ Finset.range 27, ((SL j).card : ℝ) := by
    have h1 := (Finset.card_le_card hcov).trans Finset.card_biUnion_le
    exact_mod_cast h1
  have hper_j : ∀ j ∈ Finset.range 27,
      ((SL j).card : ℝ) ≤ (2 : ℝ) ^ 256 / T0 *
        (2 * phiB 1 1 * (rhoB / 2) ^ (485 - t) * ((rhoB / 2) / qL) ^ j +
         (2 / (2 : ℝ) ^ 256) * phiB 1 1 * rhoB ^ (485 - t) * (rhoB / qL) ^ j) := by
    intro j hj
    have hjlt : j < 27 := Finset.mem_range.mp hj
    set Lb := (485 - t) + j
    let fB : Nat → List StepKind := fun x =>
      (traceKinds (SkywalkNat.step^[t] (SkywalkNat.init x ECDSAAdd.p)) Lb).reverse
    have hfB_mem : ∀ x ∈ SL j, fB x ∈ pathsOf allKinds Lb := fun x _ =>
      mem_pathsOf_all (by simp [fB, traceKinds_length])
    have hfib := card_le_list_sum_fiber (SL j) (pathsOf allKinds Lb) fB hfB_mem
    have hper_γ : ∀ γ ∈ pathsOf allKinds Lb,
        (((SL j).filter (fun x => fB x = γ)).card : ℝ) ≤
          (2 * (2 : ℝ) ^ 256 / (2 : ℝ) ^ Lb + 2) / (T0 * qL ^ j) *
            phiB ((runBL (1, 1) γ).1 : ℝ) ((runBL (1, 1) γ).2 : ℝ) := by
      intro γ hγ
      have hγ_len : γ.length = Lb := (mem_pathsOf.mp hγ).1
      set F := (SL j).filter (fun x => fB x = γ)
      by_cases hFne : F.Nonempty
      · obtain ⟨x0, hx0F⟩ := hFne
        have hx0SL : x0 ∈ SL j := (Finset.mem_filter.mp hx0F).1
        have hx0S : x0 ∈ S := (Finset.mem_filter.mp hx0SL).1
        have hbad0 := Finset.mem_filter.mp (hS_sub hx0S)
        obtain ⟨hx0_0, hx0_p⟩ := Finset.mem_Ioo.mp hbad0.1
        set uv := runBL (1, 1) γ
        have huv_pos := runBL_pos γ (by omega : 0 < 1) (by omega : 0 < 1)
        have hstate_all : ∀ x ∈ F, SkywalkNat.step^[t] (SkywalkNat.init x ECDSAAdd.p) = ⟨uv.1, uv.2⟩ := by
          intro x hxF
          have hxSL := (Finset.mem_filter.mp hxF).1
          have hfx : fB x = γ := (Finset.mem_filter.mp hxF).2
          have hterm := (Finset.mem_filter.mp hxSL).2.1
          have hval := SkywalkNat.iter_valid t (SkywalkNat.init x ECDSAAdd.p) p_pos p_odd
          have halive : ∀ i < Lb, 0 < (SkywalkNat.step^[i] (SkywalkNat.step^[t] (SkywalkNat.init x ECDSAAdd.p))).u := by
            intro i hi
            rw [← Function.iterate_add_apply]
            exact iter_alive_of_u_ne_zero _ (show i + t ≤ 485 + j by omega) (by rw [hterm]; decide)
          have hB := runB_traceKinds (SkywalkNat.step^[t] (SkywalkNat.init x ECDSAAdd.p)) Lb hval.1 hval.2.1 halive
          have hadd : Lb + t = 485 + j := by omega
          rw [← Function.iterate_add_apply, hadd, hterm] at hB
          have hrev : runB (1, 1) (traceKinds (SkywalkNat.step^[t] (SkywalkNat.init x ECDSAAdd.p)) Lb) = uv := by
            dsimp only [uv]; rw [← hfx]; exact (runBL_reverse (1, 1) _).symm
          rw [hrev] at hB
          exact SkywalkNat.State.ext (congrArg Prod.fst hB).symm (congrArg Prod.snd hB).symm
        have hcop_uv : uv.1.Coprime uv.2 := by
          have hval0 := SkywalkNat.iter_valid t (SkywalkNat.init x0 ECDSAAdd.p) p_pos p_odd
          have hg0 := hval0.2.2.trans (canonical_coprime_p hx0_0 hx0_p)
          rw [hstate_all x0 hx0F] at hg0
          exact hg0
        have hcardF := backward_state_fiber_card F
          (fun x hx => Finset.mem_Ioo.mp (Finset.mem_filter.mp (hS_sub (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1)).1)
          t uv.1 uv.2 huv_pos.1 huv_pos.2 hcop_uv
          (fun x hx => ⟨hstate_all x hx, hC_pos x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1⟩)
        have hprod_lb : 2 ^ Lb ≤ uv.1 * uv.2 := by
          have := runBL_prod γ 1 1; rw [hγ_len, mul_one, mul_one] at this; exact this
        have hdiv_le : ((ECDSAAdd.p / (uv.1 * uv.2) : Nat) : ℝ) ≤ (2 : ℝ) ^ 256 / (2 : ℝ) ^ Lb := by
          have h1 : ((ECDSAAdd.p / (uv.1 * uv.2) : Nat) : ℝ) ≤ (ECDSAAdd.p : ℝ) / ((uv.1 * uv.2 : Nat) : ℝ) :=
            Nat.cast_div_le
          have h2 : (ECDSAAdd.p : ℝ) ≤ (2 : ℝ) ^ 256 := by exact_mod_cast p_lt_256.le
          have h3 : (2 : ℝ) ^ Lb ≤ ((uv.1 * uv.2 : Nat) : ℝ) := by exact_mod_cast hprod_lb
          exact h1.trans (div_le_div₀ (by positivity) h2 (by positivity) h3)
        have hcardF_real : (F.card : ℝ) ≤ 2 * (2 : ℝ) ^ 256 / (2 : ℝ) ^ Lb + 2 := by
          have hcR : (F.card : ℝ) ≤ 2 * ((ECDSAAdd.p / (uv.1 * uv.2) : Nat) : ℝ) + 2 := by
            have := Nat.cast_le (α := ℝ).mpr hcardF
            push_cast at this; linarith
          have h2div := mul_le_mul_of_nonneg_left hdiv_le (by norm_num : (0 : ℝ) ≤ 2)
          linarith [show 2 * ((2 : ℝ) ^ 256 / (2 : ℝ) ^ Lb) = 2 * (2 : ℝ) ^ 256 / (2 : ℝ) ^ Lb by ring]
        have hphi_gt : T0 * qL ^ j < phiB (uv.1 : ℝ) (uv.2 : ℝ) := by
          have h1 := hPhiB x0 hx0S (486 + j) (by omega) (by omega) (by
            simpa only [show 486 + j - 1 = 485 + j by omega] using (Finset.mem_filter.mp hx0SL).2.1)
          rw [hstate_all x0 hx0F, show 486 + j - 486 = j by omega] at h1
          exact h1
        have hqpos : 0 < T0 * qL ^ j := by unfold qL; positivity
        have h1le : 1 ≤ phiB (uv.1 : ℝ) (uv.2 : ℝ) / (T0 * qL ^ j) := (one_le_div hqpos).mpr hphi_gt.le
        have hmul := mul_le_mul hcardF_real h1le (by norm_num) (by positivity)
        calc (F.card : ℝ) = (F.card : ℝ) * 1 := (mul_one _).symm
          _ ≤ (2 * (2 : ℝ) ^ 256 / (2 : ℝ) ^ Lb + 2) * (phiB (uv.1 : ℝ) (uv.2 : ℝ) / (T0 * qL ^ j)) := hmul
          _ = (2 * (2 : ℝ) ^ 256 / (2 : ℝ) ^ Lb + 2) / (T0 * qL ^ j) * phiB (uv.1 : ℝ) (uv.2 : ℝ) := by ring
      · rw [Finset.not_nonempty_iff_eq_empty.mp hFne, Finset.card_empty, Nat.cast_zero]
        have huv_pos := runBL_pos γ (by omega : 0 < 1) (by omega : 0 < 1)
        have hphi_pos := phiB_pos (u := ((runBL (1, 1) γ).1 : ℝ)) (v := ((runBL (1, 1) γ).2 : ℝ))
          (by exact_mod_cast huv_pos.1) (by exact_mod_cast huv_pos.2)
        unfold qL; positivity
    have hsum1 := hfib.trans (list_sum_map_le _ _ _ hper_γ)
    rw [list_sum_mul_left] at hsum1
    have htree := sum_pathsAll_phiB Lb 1 1 (by omega) (by omega)
    have hcoef_nn : 0 ≤ (2 * (2 : ℝ) ^ 256 / (2 : ℝ) ^ Lb + 2) / (T0 * qL ^ j) := by unfold qL; positivity
    have hsum2 := hsum1.trans (mul_le_mul_of_nonneg_left htree hcoef_nn)
    refine hsum2.trans_eq ?_
    dsimp only [Lb]
    rw [pow_add (2 : ℝ), pow_add rhoB]
    simp only [Nat.cast_one, div_pow]
    have hT0ne : T0 ≠ 0 := hT0.ne'
    have hq_ne : qL ≠ 0 := by unfold qL; norm_num
    have h2_ne : (2 : ℝ) ≠ 0 := by norm_num
    field_simp
  have hsum_all := hcard_sum.trans (Finset.sum_le_sum hper_j)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum_all
  have hg1 := geom_sum_le_inv (r := (rhoB / 2) / qL) (by unfold rhoB qL; positivity) (by unfold rhoB qL; norm_num) 27
  have hg2 := geom_sum_le_inv (r := rhoB / qL) (by unfold rhoB qL; positivity) (by unfold rhoB qL; norm_num) 27
  have hphiB_pos : 0 ≤ phiB 1 1 := (phiB_pos (by norm_num) (by norm_num)).le
  have hterm1 := mul_le_mul_of_nonneg_left hg1 (by unfold rhoB; positivity : 0 ≤ 2 * phiB 1 1 * (rhoB / 2) ^ (485 - t))
  have hterm2 := mul_le_mul_of_nonneg_left hg2 (by unfold rhoB; positivity : 0 ≤ 2 / (2 : ℝ) ^ 256 * phiB 1 1 * rhoB ^ (485 - t))
  have hcomb := mul_le_mul_of_nonneg_left (add_le_add hterm1 hterm2) (by positivity : 0 ≤ (2 : ℝ) ^ 256 / T0)
  refine (hsum_all.trans hcomb).trans_eq ?_
  ring

def Bad485_k0 (k0 : Nat) : Finset Nat :=
  Bad485.filter (fun x => 2 ^ k0 ∣ x ∧ (x / 2 ^ k0) % 2 = 1)

theorem bad485_k0_zero_bound :
    ((Bad485_k0 0).card : ℝ) ≤ (2 : ℝ) ^ 256 * (
      ((2 : ℝ) ^ 384 / 1000) * phiF 2 1 * rhoF ^ 240 +
      ((108 / (3125 * 10 ^ 6 : ℝ)) * (2 : ℝ) ^ 1024 * phiF 2 1 * rhoF ^ 240 / (1 - qL)) / (2 : ℝ) ^ 624 +
      (2 * phiB 1 1 * (rhoB / 2) ^ 244 / (1 - (rhoB / 2) / qL) +
       (2 / (2 : ℝ) ^ 256) * phiB 1 1 * rhoB ^ 244 / (1 - rhoB / qL)) * (2 : ℝ) ^ 624) := by
  set S0 := Bad485_k0 0
  set t : Nat := 241
  set T0 : ℝ := 1 / (2 : ℝ) ^ 624
  have hT0 : 0 < T0 := by dsimp [T0]; positivity
  let c1Pred : Nat → Prop := fun x =>
    let γ := traceKinds (SkywalkNat.init x ECDSAAdd.p) t
    (runF (0, 1) γ).1 * (runF (0, 1) γ).2 ≤ ECDSAAdd.p
  let c3Pred : Nat → Prop := fun x =>
    ∀ L, 486 ≤ L → L ≤ 512 →
      SkywalkNat.step^[L - 1] (SkywalkNat.init x ECDSAAdd.p) = ⟨1, 1⟩ →
      T0 * qL ^ (L - 486) < phiB ((SkywalkNat.step^[t] (SkywalkNat.init x ECDSAAdd.p)).u : ℝ)
        ((SkywalkNat.step^[t] (SkywalkNat.init x ECDSAAdd.p)).v : ℝ)
  set S1 := S0.filter c1Pred
  set S3 := S0.filter c3Pred
  set S2 := S0.filter (fun x => ¬ c1Pred x ∧ ¬ c3Pred x)
  have hsplit : (S0.card : ℝ) ≤ (S1.card : ℝ) + (S2.card : ℝ) + (S3.card : ℝ) := by
    have hsub : S0 ⊆ S1 ∪ (S2 ∪ S3) := by
      intro x hx
      by_cases h1 : c1Pred x
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, h1⟩)
      · by_cases h3 : c3Pred x
        · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, h3⟩))
        · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, h1, h3⟩))
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hc2 := Finset.card_union_le S2 S3
    have hnat : S0.card ≤ S1.card + S2.card + S3.card := by omega
    exact_mod_cast hnat
  have hx_facts : ∀ x ∈ S0,
      0 < x ∧ x < ECDSAAdd.p ∧
      0 < (SkywalkNat.step^[t] (SkywalkNat.init x ECDSAAdd.p)).u ∧
      traceKinds (SkywalkNat.init x ECDSAAdd.p) t = .O1 :: traceKinds (SkywalkNat.step^[1] (SkywalkNat.init x ECDSAAdd.p)) 240 ∧
      0 < (runF (0, 1) (traceKinds (SkywalkNat.init x ECDSAAdd.p) t)).1 := by
    intro x hx
    have hmem := Finset.mem_filter.mp hx
    have hbad := Finset.mem_filter.mp hmem.1
    obtain ⟨hx0, hxp⟩ := Finset.mem_Ioo.mp hbad.1
    have hodd : (x / 2 ^ 0) % 2 = 1 := hmem.2.2
    obtain ⟨_, _, htr1, _⟩ := leading_E_steps x 0 (by simp) hodd hxp
    have hu_t : 0 < (SkywalkNat.step^[t] (SkywalkNat.init x ECDSAAdd.p)).u :=
      iter_alive_of_u_ne_zero _ (by decide : t ≤ 485) hbad.2
    have htr_t : traceKinds (SkywalkNat.init x ECDSAAdd.p) t =
        .O1 :: traceKinds (SkywalkNat.step^[1] (SkywalkNat.init x ECDSAAdd.p)) 240 := by
      have := traceKinds_add (SkywalkNat.init x ECDSAAdd.p) 1 240
      simpa only [show 1 + 240 = t from rfl, htr1, List.replicate_zero, List.nil_append, List.cons_append] using this
    have hCpos : 0 < (runF (0, 1) (traceKinds (SkywalkNat.init x ECDSAAdd.p) t)).1 := by
      rw [htr_t, runF_cons]
      exact (runF_pos _ (by omega : 0 < 2) (by omega : 0 < 1)).1
    exact ⟨hx0, hxp, hu_t, htr_t, hCpos⟩
  -- Case 1 bound on `S1`:
  have hS1 : (S1.card : ℝ) ≤ (2 : ℝ) ^ 256 * (((2 : ℝ) ^ 384 / 1000) * phiF 2 1 * rhoF ^ 240) := by
    let f1 : Nat → List StepKind := fun x => traceKinds (SkywalkNat.step^[1] (SkywalkNat.init x ECDSAAdd.p)) 240
    have hfib := card_le_list_sum_fiber S1 (pathsOf allKinds 240) f1
      (fun x _ => mem_pathsOf_all (traceKinds_length _ _))
    have hper : ∀ γ ∈ pathsOf allKinds 240,
        ((S1.filter (fun x => f1 x = γ)).card : ℝ) ≤
          (2 : ℝ) ^ 256 * ((2 : ℝ) ^ 384 / 1000) * phiF (runF (2, 1) γ).1 (runF (2, 1) γ).2 := by
      intro γ _
      set F := S1.filter (fun x => f1 x = γ)
      have hpos := runF_pos γ (by omega : 0 < 2) (by omega : 0 < 1)
      have hC_R : (0 : ℝ) < ((runF (2, 1) γ).1 : ℝ) := by exact_mod_cast hpos.1
      have hD_R : (0 : ℝ) < ((runF (2, 1) γ).2 : ℝ) := by exact_mod_cast hpos.2
      by_cases hne : F.Nonempty
      · obtain ⟨x0, hx0⟩ := hne
        have hx0_S1 := (Finset.mem_filter.mp hx0).1
        have hx0_S0 := (Finset.mem_filter.mp hx0_S1).1
        have hc1_0 : c1Pred x0 := (Finset.mem_filter.mp hx0_S1).2
        have hfx0 : f1 x0 = γ := (Finset.mem_filter.mp hx0).2
        dsimp only [f1] at hfx0
        have htr0 := (hx_facts x0 hx0_S0).2.2.2.1
        rw [hfx0] at htr0
        have hF_eq : runF (0, 1) (.O1 :: γ) = runF (2, 1) γ := rfl
        have hCD_le : (runF (2, 1) γ).1 * (runF (2, 1) γ).2 ≤ ECDSAAdd.p := by
          dsimp only [c1Pred] at hc1_0; rwa [htr0, hF_eq] at hc1_0
        have hcop := (runF_coprime_even_odd γ (by decide : (2 : Nat).Coprime 1) (by decide) (by decide)).1
        have hcF := forward_prefix_fiber_card F
          (fun x hx => let hf := hx_facts x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1; ⟨hf.1, hf.2.1⟩)
          t (.O1 :: γ)
          (fun x hx => by
            have hxS0 := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
            have hfx : f1 x = γ := (Finset.mem_filter.mp hx).2
            dsimp only [f1] at hfx
            have hf := hx_facts x hxS0
            exact ⟨by rw [hf.2.2.2.1, hfx], hf.2.2.1⟩)
          hpos.1 hpos.2 hcop
        rw [hF_eq] at hcF
        have hdiv : ((ECDSAAdd.p / ((runF (2, 1) γ).1 * (runF (2, 1) γ).2) + 1 : Nat) : ℝ) ≤
            2 * (2 : ℝ) ^ 256 / ((runF (2, 1) γ).1 * (runF (2, 1) γ).2 : ℝ) := by
          have h1 : ((ECDSAAdd.p / ((runF (2, 1) γ).1 * (runF (2, 1) γ).2) : Nat) : ℝ) ≤
              (ECDSAAdd.p : ℝ) / ((runF (2, 1) γ).1 * (runF (2, 1) γ).2 : ℝ) := by
            simpa only [Nat.cast_mul] using (Nat.cast_div_le (α := ℝ) (m := ECDSAAdd.p) (n := (runF (2, 1) γ).1 * (runF (2, 1) γ).2))
          have h2 : (1 : ℝ) ≤ (ECDSAAdd.p : ℝ) / ((runF (2, 1) γ).1 * (runF (2, 1) γ).2 : ℝ) :=
            (one_le_div (by positivity)).mpr (by exact_mod_cast hCD_le)
          have h3 : (ECDSAAdd.p : ℝ) / ((runF (2, 1) γ).1 * (runF (2, 1) γ).2 : ℝ) ≤
              (2 : ℝ) ^ 256 / ((runF (2, 1) γ).1 * (runF (2, 1) γ).2 : ℝ) :=
            div_le_div_of_nonneg_right (by exact_mod_cast p_lt_256.le) (by positivity)
          push_cast
          linarith [show (2 : ℝ) ^ 256 / ((runF (2, 1) γ).1 * (runF (2, 1) γ).2 : ℝ) +
              (2 : ℝ) ^ 256 / ((runF (2, 1) γ).1 * (runF (2, 1) γ).2 : ℝ) =
              2 * (2 : ℝ) ^ 256 / ((runF (2, 1) γ).1 * (runF (2, 1) γ).2 : ℝ) by ring]
        have hinv := inv_prod_le_phiF hC_R hD_R (by exact_mod_cast hCD_le.trans p_lt_256.le)
        have hcardR : (F.card : ℝ) ≤ 2 * (2 : ℝ) ^ 256 / ((runF (2, 1) γ).1 * (runF (2, 1) γ).2 : ℝ) :=
          (Nat.cast_le.mpr hcF).trans hdiv
        have hmul := mul_le_mul_of_nonneg_left hinv (by positivity : (0 : ℝ) ≤ 2 * (2 : ℝ) ^ 256)
        refine hcardR.trans ?_
        calc 2 * (2 : ℝ) ^ 256 / ((runF (2, 1) γ).1 * (runF (2, 1) γ).2 : ℝ)
            = 2 * (2 : ℝ) ^ 256 * (1 / ((runF (2, 1) γ).1 * (runF (2, 1) γ).2 : ℝ)) := by ring
          _ ≤ 2 * (2 : ℝ) ^ 256 * ((2 : ℝ) ^ 384 / 2000 * phiF (runF (2, 1) γ).1 (runF (2, 1) γ).2) := hmul
          _ = (2 : ℝ) ^ 256 * ((2 : ℝ) ^ 384 / 1000) * phiF (runF (2, 1) γ).1 (runF (2, 1) γ).2 := by
            generalize (2 : ℝ) ^ 384 = P384; ring
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero]
        have := phiF_pos hC_R hD_R
        exact mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) (div_nonneg (pow_nonneg (by norm_num) _) (by norm_num))) this.le
    have h1 := hfib.trans (list_sum_map_le _ _ _ hper)
    rw [list_sum_mul_left] at h1
    have hcoef_nn : (0 : ℝ) ≤ (2 : ℝ) ^ 256 * ((2 : ℝ) ^ 384 / 1000) :=
      mul_nonneg (pow_nonneg (by norm_num) _) (div_nonneg (pow_nonneg (by norm_num) _) (by norm_num))
    have h2 := h1.trans (mul_le_mul_of_nonneg_left (sum_pathsAll_phiF 240 2 1 (by omega) (by omega)) hcoef_nn)
    refine h2.trans_eq ?_; simp only [Nat.cast_ofNat, Nat.cast_one]; generalize (2 : ℝ) ^ 384 = P384; ring
  -- Case 2 bound on `S2`:
  have hS2 : (S2.card : ℝ) ≤ (2 : ℝ) ^ 256 *
      (((108 / (3125 * 10 ^ 6 : ℝ)) * (2 : ℝ) ^ 1024 * phiF 2 1 * rhoF ^ 240 / (1 - qL)) / (2 : ℝ) ^ 624) := by
    let SL2 : Nat → Finset Nat := fun j =>
      S2.filter (fun x => SkywalkNat.step^[485 + j] (SkywalkNat.init x ECDSAAdd.p) = ⟨1, 1⟩ ∧
        phiB ((SkywalkNat.step^[t] (SkywalkNat.init x ECDSAAdd.p)).u : ℝ)
          ((SkywalkNat.step^[t] (SkywalkNat.init x ECDSAAdd.p)).v : ℝ) ≤ T0 * qL ^ j)
    have hcov2 : S2 ⊆ (Finset.range 27).biUnion SL2 := by
      intro x hx
      have hnc3 : ¬ c3Pred x := (Finset.mem_filter.mp hx).2.2
      dsimp only [c3Pred] at hnc3
      push_neg at hnc3
      obtain ⟨L, hL1, hL2, hterm, hle⟩ := hnc3
      refine Finset.mem_biUnion.mpr ⟨L - 486, Finset.mem_range.mpr (by omega),
        Finset.mem_filter.mpr ⟨hx, by rwa [show 485 + (L - 486) = L - 1 by omega], hle⟩⟩
    have hsum2 : (S2.card : ℝ) ≤ ∑ j ∈ Finset.range 27, ((SL2 j).card : ℝ) := by
      exact_mod_cast (Finset.card_le_card hcov2).trans Finset.card_biUnion_le
    have hper_j : ∀ j ∈ Finset.range 27,
        ((SL2 j).card : ℝ) ≤
          (108 / (3125 * 10 ^ 6 : ℝ)) * (2 : ℝ) ^ 1280 * (T0 * qL ^ j) * (phiF 2 1 * rhoF ^ 240) := by
      intro j _
      let f1 : Nat → List StepKind := fun x => traceKinds (SkywalkNat.step^[1] (SkywalkNat.init x ECDSAAdd.p)) 240
      have hfib := card_le_list_sum_fiber (SL2 j) (pathsOf allKinds 240) f1
        (fun x _ => mem_pathsOf_all (traceKinds_length _ _))
      have hper_γ : ∀ γ ∈ pathsOf allKinds 240,
          (((SL2 j).filter (fun x => f1 x = γ)).card : ℝ) ≤
            (108 / (3125 * 10 ^ 6 : ℝ)) * (2 : ℝ) ^ 1280 * (T0 * qL ^ j) * phiF (runF (2, 1) γ).1 (runF (2, 1) γ).2 := by
        intro γ _
        set F := (SL2 j).filter (fun x => f1 x = γ)
        have hpos := runF_pos γ (by omega : 0 < 2) (by omega : 0 < 1)
        have hC_R : (0 : ℝ) < ((runF (2, 1) γ).1 : ℝ) := by exact_mod_cast hpos.1
        have hD_R : (0 : ℝ) < ((runF (2, 1) γ).2 : ℝ) := by exact_mod_cast hpos.2
        by_cases hne : F.Nonempty
        · obtain ⟨x0, hx0⟩ := hne
          have hx0_SL2 := (Finset.mem_filter.mp hx0).1
          have hx0_S2 := (Finset.mem_filter.mp hx0_SL2).1
          have hx0_S0 := (Finset.mem_filter.mp hx0_S2).1
          have hnc1 : ¬ c1Pred x0 := (Finset.mem_filter.mp hx0_S2).2.1
          have hphiB_le := (Finset.mem_filter.mp hx0_SL2).2.2
          have hfx0 : f1 x0 = γ := (Finset.mem_filter.mp hx0).2
          dsimp only [f1] at hfx0
          have hf0 := hx_facts x0 hx0_S0
          have htr0 : traceKinds (SkywalkNat.init x0 ECDSAAdd.p) t = .O1 :: γ := by rw [hf0.2.2.2.1, hfx0]
          have hF_eq : runF (0, 1) (.O1 :: γ) = runF (2, 1) γ := rfl
          have hCD_gt : ECDSAAdd.p < (runF (2, 1) γ).1 * (runF (2, 1) γ).2 := by
            dsimp only [c1Pred] at hnc1; rw [htr0, hF_eq] at hnc1; omega
          have hcop := (runF_coprime_even_odd γ (by decide : (2 : Nat).Coprime 1) (by decide) (by decide)).1
          have hcF := forward_prefix_fiber_card F
            (fun x hx => let hf := hx_facts x (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1).1; ⟨hf.1, hf.2.1⟩)
            t (.O1 :: γ)
            (fun x hx => by
              have hxS0 := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1).1
              have hfx : f1 x = γ := (Finset.mem_filter.mp hx).2
              dsimp only [f1] at hfx
              have hf := hx_facts x hxS0
              exact ⟨by rw [hf.2.2.2.1, hfx], hf.2.2.1⟩)
            hpos.1 hpos.2 hcop
          rw [hF_eq, Nat.div_eq_of_lt hCD_gt] at hcF
          have hval0 := SkywalkNat.iter_valid t (SkywalkNat.init x0 ECDSAAdd.p) p_pos p_odd
          have halive0 : ∀ i < t, 0 < (SkywalkNat.step^[i] (SkywalkNat.init x0 ECDSAAdd.p)).u := fun i hi =>
            iter_alive_of_u_ne_zero _ hi.le (Nat.ne_of_gt hf0.2.2.1)
          have hB0 := runB_traceKinds (SkywalkNat.init x0 ECDSAAdd.p) t p_pos p_odd halive0
          rw [htr0] at hB0
          have hdot0 := runF_runB_dot (.O1 :: γ) 0 1
            (SkywalkNat.step^[t] (SkywalkNat.init x0 ECDSAAdd.p)).u
            (SkywalkNat.step^[t] (SkywalkNat.init x0 ECDSAAdd.p)).v
          rw [hB0, hF_eq] at hdot0
          simp only [SkywalkNat.init, zero_mul, one_mul, zero_add] at hdot0
          have hcoup := coupling_lower hC_R hD_R
            (Nat.cast_pos.mpr hf0.2.2.1) (Nat.cast_pos.mpr hval0.1)
          have hlinR : ((runF (2, 1) γ).1 : ℝ) * ((SkywalkNat.step^[t] (SkywalkNat.init x0 ECDSAAdd.p)).u : ℝ) +
              ((runF (2, 1) γ).2 : ℝ) * ((SkywalkNat.step^[t] (SkywalkNat.init x0 ECDSAAdd.p)).v : ℝ) ≤ (2 : ℝ) ^ 256 := by
            have : ((runF (2, 1) γ).1 * (SkywalkNat.step^[t] (SkywalkNat.init x0 ECDSAAdd.p)).u +
                (runF (2, 1) γ).2 * (SkywalkNat.step^[t] (SkywalkNat.init x0 ECDSAAdd.p)).v : Nat) ≤ 2 ^ 256 :=
              hdot0.le.trans p_lt_256.le
            exact_mod_cast this
          have hpow5 : (((runF (2, 1) γ).1 : ℝ) * ((SkywalkNat.step^[t] (SkywalkNat.init x0 ECDSAAdd.p)).u : ℝ) +
              ((runF (2, 1) γ).2 : ℝ) * ((SkywalkNat.step^[t] (SkywalkNat.init x0 ECDSAAdd.p)).v : ℝ)) ^ 5 ≤ (2 : ℝ) ^ 1280 :=
            (pow_le_pow_left₀ (by positivity) hlinR 5).trans_eq (by rw [← pow_mul])
          have hphiF_pos := phiF_pos hC_R hD_R
          have h1 : (3125 * 10 ^ 6 / 108 : ℝ) ≤ phiF (runF (2, 1) γ).1 (runF (2, 1) γ).2 * (T0 * qL ^ j) * (2 : ℝ) ^ 1280 :=
            hcoup.trans (mul_le_mul (mul_le_mul_of_nonneg_left hphiB_le hphiF_pos.le) hpow5
              (by positivity) (by unfold qL; positivity))
          have hcard1 : (F.card : ℝ) ≤ 1 := by exact_mod_cast hcF
          have h2 : (1 : ℝ) ≤ (108 / (3125 * 10 ^ 6 : ℝ)) * (2 : ℝ) ^ 1280 * (T0 * qL ^ j) *
              phiF (runF (2, 1) γ).1 (runF (2, 1) γ).2 := by
            have hmul := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 108 / (3125 * 10 ^ 6 : ℝ))
            have hlhs : (108 / (3125 * 10 ^ 6 : ℝ)) * (3125 * 10 ^ 6 / 108 : ℝ) = 1 := by norm_num
            rw [hlhs] at hmul
            exact hmul.trans_eq (by generalize (2 : ℝ) ^ 1280 = P1280; generalize T0 = T0'; ring)
          exact hcard1.trans h2
        · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero]
          have := phiF_pos hC_R hD_R; unfold qL; positivity
      have h1 := hfib.trans (list_sum_map_le _ _ _ hper_γ)
      rw [list_sum_mul_left] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left
        (by simpa only [Nat.cast_ofNat, Nat.cast_one] using sum_pathsAll_phiF 240 2 1 (by omega) (by omega))
        (by unfold qL; positivity))
    have h1 := hsum2.trans (Finset.sum_le_sum hper_j)
    have hfact : ∑ j ∈ Finset.range 27,
        (108 / (3125 * 10 ^ 6 : ℝ)) * (2 : ℝ) ^ 1280 * (T0 * qL ^ j) * (phiF 2 1 * rhoF ^ 240) =
        ((108 / (3125 * 10 ^ 6 : ℝ)) * (2 : ℝ) ^ 1280 * T0 * (phiF 2 1 * rhoF ^ 240)) *
          ∑ j ∈ Finset.range 27, qL ^ j := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; generalize (2 : ℝ) ^ 1280 = P1280; generalize T0 = T0'; ring
    rw [hfact] at h1
    have hg := geom_sum_le_inv (r := qL) (by unfold qL; positivity) (by unfold qL; norm_num) 27
    have hphi21_pos : 0 ≤ phiF 2 1 := (phiF_pos (by norm_num) (by norm_num)).le
    have h2 := h1.trans (mul_le_mul_of_nonneg_left hg (by unfold rhoF; positivity))
    refine h2.trans_eq ?_
    dsimp only [T0]
    have hpow : (2 : ℝ) ^ 1280 = (2 : ℝ) ^ 256 * (2 : ℝ) ^ 1024 := by rw [← pow_add]
    rw [hpow]; generalize (2 : ℝ) ^ 1024 = P1024; generalize (2 : ℝ) ^ 624 = P624; ring
  -- Case 3 bound on `S3`:
  have hS3 := case3_card_bound S3 (Finset.filter_subset _ _ |>.trans (Finset.filter_subset _ _)) t (by decide) T0 hT0
    (fun x hx => (hx_facts x (Finset.mem_filter.mp hx).1).2.2.2.2)
    (fun x hx => (Finset.mem_filter.mp hx).2)
  have hS3' : (S3.card : ℝ) ≤ (2 : ℝ) ^ 256 *
      ((2 * phiB 1 1 * (rhoB / 2) ^ 244 / (1 - (rhoB / 2) / qL) +
        (2 / (2 : ℝ) ^ 256) * phiB 1 1 * rhoB ^ 244 / (1 - rhoB / qL)) * (2 : ℝ) ^ 624) := by
    refine hS3.trans_eq ?_
    have hsub : 485 - t = 244 := by decide
    rw [hsub]; dsimp only [T0]; field_simp
  have hadd := add_le_add (add_le_add hS1 hS2) hS3'
  rw [← mul_add, ← mul_add] at hadd
  exact hsplit.trans hadd

theorem bad485_k0_pos_bound (k0 m e : Nat) (hk0 : 1 ≤ k0) (_hm : 1 ≤ m) (ht : 2 * k0 + m ≤ 485) :
    ((Bad485_k0 k0).card : ℝ) ≤ (2 : ℝ) ^ 256 * (
      ((2 : ℝ) ^ 384 / 1000) * phiF 2 1 * rhoEO0 ^ (k0 - 1) * rhoF ^ m +
      ((16 * 108 / (3125 * 10 ^ 6 : ℝ)) * (2 : ℝ) ^ 1024 / (16 : ℝ) ^ k0 * phiF 1 1 * rhoF ^ m / (1 - qL)) / (2 : ℝ) ^ e +
      (2 * phiB 1 1 * (rhoB / 2) ^ (485 - (2 * k0 + m)) / (1 - (rhoB / 2) / qL) +
       (2 / (2 : ℝ) ^ 256) * phiB 1 1 * rhoB ^ (485 - (2 * k0 + m)) / (1 - rhoB / qL)) * (2 : ℝ) ^ e) := by
  set Sk := Bad485_k0 k0
  set t : Nat := 2 * k0 + m
  set T0 : ℝ := 1 / (2 : ℝ) ^ e
  have hT0 : 0 < T0 := by dsimp [T0]; positivity
  let c1Pred : Nat → Prop := fun x =>
    let γ := traceKinds (SkywalkNat.init x ECDSAAdd.p) t
    (runF (0, 1) γ).1 * (runF (0, 1) γ).2 ≤ ECDSAAdd.p
  let c3Pred : Nat → Prop := fun x =>
    ∀ L, 486 ≤ L → L ≤ 512 →
      SkywalkNat.step^[L - 1] (SkywalkNat.init x ECDSAAdd.p) = ⟨1, 1⟩ →
      T0 * qL ^ (L - 486) < phiB ((SkywalkNat.step^[t] (SkywalkNat.init x ECDSAAdd.p)).u : ℝ)
        ((SkywalkNat.step^[t] (SkywalkNat.init x ECDSAAdd.p)).v : ℝ)
  set S1 := Sk.filter c1Pred
  set S3 := Sk.filter c3Pred
  set S2 := Sk.filter (fun x => ¬ c1Pred x ∧ ¬ c3Pred x)
  have hsplit : (Sk.card : ℝ) ≤ (S1.card : ℝ) + (S2.card : ℝ) + (S3.card : ℝ) := by
    have hsub : Sk ⊆ S1 ∪ (S2 ∪ S3) := by
      intro x hx
      by_cases h1 : c1Pred x
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, h1⟩)
      · by_cases h3 : c3Pred x
        · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, h3⟩))
        · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, h1, h3⟩))
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hc2 := Finset.card_union_le S2 S3
    have hnat : Sk.card ≤ S1.card + S2.card + S3.card := by omega
    exact_mod_cast hnat
  let pref : List StepKind := List.replicate k0 .E ++ [.O1]
  let g1 : Nat → List StepKind := fun x =>
    traceKinds (SkywalkNat.step^[k0 + 1] (SkywalkNat.init x ECDSAAdd.p)) (k0 - 1)
  let g2 : Nat → List StepKind := fun x =>
    traceKinds (SkywalkNat.step^[2 * k0] (SkywalkNat.init x ECDSAAdd.p)) m
  have hrunF_pref : runF (0, 1) pref = (2, 1) := by
    have hrep : ∀ n, runF (0, 1) (List.replicate n .E) = (0, 1) := by
      intro n; induction n with
      | zero => rfl
      | succ n ih => simp [List.replicate_succ, runF_cons, stepF, ih]
    rw [runF_append, hrep]; rfl
  have hx_facts : ∀ x ∈ Sk,
      0 < x ∧ x < ECDSAAdd.p ∧
      0 < (SkywalkNat.step^[t] (SkywalkNat.init x ECDSAAdd.p)).u ∧
      traceKinds (SkywalkNat.init x ECDSAAdd.p) t = pref ++ g1 x ++ g2 x ∧
      g1 x ∈ pathsOf eo0Kinds (k0 - 1) ∧
      g2 x ∈ pathsOf allKinds m ∧
      ((SkywalkNat.step^[2 * k0] (SkywalkNat.init x ECDSAAdd.p)).u : ℝ) +
        ((SkywalkNat.step^[2 * k0] (SkywalkNat.init x ECDSAAdd.p)).v : ℝ) <
          2 * (ECDSAAdd.p : ℝ) / (2 : ℝ) ^ k0 ∧
      0 < (runF (0, 1) (traceKinds (SkywalkNat.init x ECDSAAdd.p) t)).1 := by
    intro x hx
    have hmem := Finset.mem_filter.mp hx
    have hbad := Finset.mem_filter.mp hmem.1
    obtain ⟨hx0, hxp⟩ := Finset.mem_Ioo.mp hbad.1
    obtain ⟨_, _, htr1, _⟩ := leading_E_steps x k0 hmem.2.1 hmem.2.2 hxp
    obtain ⟨hEO, _, _, hsumR⟩ := forced_eo0_phase x k0 hk0 hmem.2.1 hmem.2.2 hxp
    have hu_t : 0 < (SkywalkNat.step^[t] (SkywalkNat.init x ECDSAAdd.p)).u :=
      iter_alive_of_u_ne_zero _ ht hbad.2
    have htr_2k : traceKinds (SkywalkNat.init x ECDSAAdd.p) (2 * k0) = pref ++ g1 x := by
      have h1 := traceKinds_add (SkywalkNat.init x ECDSAAdd.p) (k0 + 1) (k0 - 1)
      rw [show (k0 + 1) + (k0 - 1) = 2 * k0 by omega, htr1] at h1
      exact h1
    have htr_t : traceKinds (SkywalkNat.init x ECDSAAdd.p) t = pref ++ g1 x ++ g2 x := by
      have h1 := traceKinds_add (SkywalkNat.init x ECDSAAdd.p) (2 * k0) m
      rw [htr_2k] at h1; exact h1
    have hCpos : 0 < (runF (0, 1) (traceKinds (SkywalkNat.init x ECDSAAdd.p) t)).1 := by
      rw [htr_t, runF_append, runF_append, hrunF_pref]
      have h1 := runF_pos (g1 x) (by omega : 0 < 2) (by omega : 0 < 1)
      exact (runF_pos (g2 x) h1.1 h1.2).1
    exact ⟨hx0, hxp, hu_t, htr_t, mem_pathsOf.mpr ⟨traceKinds_length _ _, hEO⟩,
      mem_pathsOf_all (traceKinds_length _ _), hsumR, hCpos⟩
  let pairList : List (List StepKind × List StepKind) :=
    (pathsOf eo0Kinds (k0 - 1)).flatMap (fun γ1 => (pathsOf allKinds m).map (fun γ2 => (γ1, γ2)))
  have hpair_mem : ∀ x ∈ Sk, (g1 x, g2 x) ∈ pairList := fun x hx => by
    have hf := hx_facts x hx
    exact List.mem_flatMap.mpr ⟨g1 x, hf.2.2.2.2.1, List.mem_map.mpr ⟨g2 x, hf.2.2.2.2.2.1, rfl⟩⟩
  -- Case 1 bound on `S1`:
  have hS1 : (S1.card : ℝ) ≤ (2 : ℝ) ^ 256 * (((2 : ℝ) ^ 384 / 1000) * phiF 2 1 * rhoEO0 ^ (k0 - 1) * rhoF ^ m) := by
    have hfib := card_le_list_sum_fiber S1 pairList (fun x => (g1 x, g2 x))
      (fun x hx => hpair_mem x (Finset.mem_filter.mp hx).1)
    have hper : ∀ p12 ∈ pairList,
        ((S1.filter (fun x => (g1 x, g2 x) = p12)).card : ℝ) ≤
          (2 : ℝ) ^ 256 * ((2 : ℝ) ^ 384 / 1000) *
            phiF (runF (runF (2, 1) p12.1) p12.2).1 (runF (runF (2, 1) p12.1) p12.2).2 := by
      rintro ⟨γ1, γ2⟩ _
      set F := S1.filter (fun x => (g1 x, g2 x) = (γ1, γ2))
      have hpos1 := runF_pos γ1 (by omega : 0 < 2) (by omega : 0 < 1)
      have hpos := runF_pos γ2 hpos1.1 hpos1.2
      set C := (runF (runF (2, 1) γ1) γ2).1
      set D := (runF (runF (2, 1) γ1) γ2).2
      have hC_R : (0 : ℝ) < (C : ℝ) := by exact_mod_cast hpos.1
      have hD_R : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hpos.2
      by_cases hne : F.Nonempty
      · obtain ⟨x0, hx0⟩ := hne
        have hx0_S1 := (Finset.mem_filter.mp hx0).1
        have hx0_Sk := (Finset.mem_filter.mp hx0_S1).1
        have hc1_0 : c1Pred x0 := (Finset.mem_filter.mp hx0_S1).2
        have hpair0 := (Finset.mem_filter.mp hx0).2
        have htr0 := (hx_facts x0 hx0_Sk).2.2.2.1
        rw [(Prod.mk.inj hpair0).1, (Prod.mk.inj hpair0).2] at htr0
        have hF_eq : runF (0, 1) (pref ++ γ1 ++ γ2) = runF (runF (2, 1) γ1) γ2 := by
          rw [runF_append, runF_append, hrunF_pref]
        have hCD_le : C * D ≤ ECDSAAdd.p := by
          dsimp only [c1Pred] at hc1_0; rwa [htr0, hF_eq] at hc1_0
        have hcop := (runF_coprime_even_odd (γ1 ++ γ2) (by decide : (2 : Nat).Coprime 1) (by decide) (by decide)).1
        rw [runF_append] at hcop
        have hcF := forward_prefix_fiber_card F
          (fun x hx => let hf := hx_facts x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1; ⟨hf.1, hf.2.1⟩)
          t (pref ++ γ1 ++ γ2)
          (fun x hx => by
            have hxSk := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
            have hp := (Finset.mem_filter.mp hx).2
            have hf := hx_facts x hxSk
            exact ⟨by rw [hf.2.2.2.1, (Prod.mk.inj hp).1, (Prod.mk.inj hp).2], hf.2.2.1⟩)
          (by rw [hF_eq]; exact hpos.1) (by rw [hF_eq]; exact hpos.2) (by rw [hF_eq]; exact hcop)
        rw [hF_eq] at hcF
        have hdiv : ((ECDSAAdd.p / (C * D) + 1 : Nat) : ℝ) ≤ 2 * (2 : ℝ) ^ 256 / ((C : ℝ) * D) := by
          have h1 : ((ECDSAAdd.p / (C * D) : Nat) : ℝ) ≤ (ECDSAAdd.p : ℝ) / ((C : ℝ) * D) := by
            simpa only [Nat.cast_mul] using (Nat.cast_div_le (α := ℝ) (m := ECDSAAdd.p) (n := C * D))
          have h2 : (1 : ℝ) ≤ (ECDSAAdd.p : ℝ) / ((C : ℝ) * D) :=
            (one_le_div (by positivity)).mpr (by exact_mod_cast hCD_le)
          have h3 : (ECDSAAdd.p : ℝ) / ((C : ℝ) * D) ≤ (2 : ℝ) ^ 256 / ((C : ℝ) * D) :=
            div_le_div_of_nonneg_right (by exact_mod_cast p_lt_256.le) (by positivity)
          push_cast
          linarith [show (2 : ℝ) ^ 256 / ((C : ℝ) * D) + (2 : ℝ) ^ 256 / ((C : ℝ) * D) =
            2 * (2 : ℝ) ^ 256 / ((C : ℝ) * D) by ring]
        have hinv := inv_prod_le_phiF hC_R hD_R (by exact_mod_cast hCD_le.trans p_lt_256.le)
        have hcardR : (F.card : ℝ) ≤ 2 * (2 : ℝ) ^ 256 / ((C : ℝ) * D) := (Nat.cast_le.mpr hcF).trans hdiv
        have hmul := mul_le_mul_of_nonneg_left hinv (by positivity : (0 : ℝ) ≤ 2 * (2 : ℝ) ^ 256)
        refine hcardR.trans ?_
        calc 2 * (2 : ℝ) ^ 256 / ((C : ℝ) * D) = 2 * (2 : ℝ) ^ 256 * (1 / ((C : ℝ) * D)) := by ring
          _ ≤ 2 * (2 : ℝ) ^ 256 * ((2 : ℝ) ^ 384 / 2000 * phiF C D) := hmul
          _ = (2 : ℝ) ^ 256 * ((2 : ℝ) ^ 384 / 1000) * phiF C D := by
            generalize (2 : ℝ) ^ 384 = P384; ring
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero]
        have := phiF_pos hC_R hD_R
        exact mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) (div_nonneg (pow_nonneg (by norm_num) _) (by norm_num))) this.le
    have h1 := hfib.trans (list_sum_map_le _ _ _ hper)
    rw [list_sum_mul_left] at h1
    dsimp only [pairList] at h1
    rw [list_sum_flatMap_real] at h1
    have hinner : ∀ γ1 ∈ pathsOf eo0Kinds (k0 - 1),
        (((pathsOf allKinds m).map (fun γ2 => (γ1, γ2))).map
          (fun p12 => phiF (runF (runF (2, 1) p12.1) p12.2).1 (runF (runF (2, 1) p12.1) p12.2).2)).sum ≤
        phiF (runF (2, 1) γ1).1 (runF (2, 1) γ1).2 * rhoF ^ m := by
      intro γ1 _
      simp only [List.map_map, Function.comp_def]
      have hpos1 := runF_pos γ1 (by omega : 0 < 2) (by omega : 0 < 1)
      simpa only [Prod.mk.eta] using sum_pathsAll_phiF m (runF (2, 1) γ1).1 (runF (2, 1) γ1).2 hpos1.1 hpos1.2
    have h2 := list_sum_map_le _ _ _ hinner
    have hrhs_pull : ((pathsOf eo0Kinds (k0 - 1)).map (fun γ1 => phiF (runF (2, 1) γ1).1 (runF (2, 1) γ1).2 * rhoF ^ m)).sum =
        rhoF ^ m * ((pathsOf eo0Kinds (k0 - 1)).map (fun γ1 => phiF (runF (2, 1) γ1).1 (runF (2, 1) γ1).2)).sum := by
      rw [← list_sum_mul_left]; apply congrArg List.sum; apply List.map_congr_left; intro _ _; ring
    rw [hrhs_pull] at h2
    have houter := sum_pathsEO0_phiF (k0 - 1) 2 1 (by omega) (by omega)
    have h3 := h2.trans (mul_le_mul_of_nonneg_left houter (by unfold rhoF; positivity))
    have hcoef_nn : (0 : ℝ) ≤ (2 : ℝ) ^ 256 * ((2 : ℝ) ^ 384 / 1000) :=
      mul_nonneg (pow_nonneg (by norm_num) _) (div_nonneg (pow_nonneg (by norm_num) _) (by norm_num))
    have h4 := h1.trans (mul_le_mul_of_nonneg_left h3 hcoef_nn)
    refine h4.trans_eq ?_; simp only [Nat.cast_ofNat, Nat.cast_one]; generalize (2 : ℝ) ^ 384 = P384; ring
  -- Case 2 bound on `S2`:
  have hS2 : (S2.card : ℝ) ≤ (2 : ℝ) ^ 256 *
      (((16 * 108 / (3125 * 10 ^ 6 : ℝ)) * (2 : ℝ) ^ 1024 / (16 : ℝ) ^ k0 * phiF 1 1 * rhoF ^ m / (1 - qL)) / (2 : ℝ) ^ e) := by
    let SL2 : Nat → Finset Nat := fun j =>
      S2.filter (fun x => SkywalkNat.step^[485 + j] (SkywalkNat.init x ECDSAAdd.p) = ⟨1, 1⟩ ∧
        phiB ((SkywalkNat.step^[t] (SkywalkNat.init x ECDSAAdd.p)).u : ℝ)
          ((SkywalkNat.step^[t] (SkywalkNat.init x ECDSAAdd.p)).v : ℝ) ≤ T0 * qL ^ j)
    have hcov2 : S2 ⊆ (Finset.range 27).biUnion SL2 := by
      intro x hx
      have hnc3 : ¬ c3Pred x := (Finset.mem_filter.mp hx).2.2
      dsimp only [c3Pred] at hnc3
      push_neg at hnc3
      obtain ⟨L, hL1, hL2, hterm, hle⟩ := hnc3
      refine Finset.mem_biUnion.mpr ⟨L - 486, Finset.mem_range.mpr (by omega),
        Finset.mem_filter.mpr ⟨hx, by rwa [show 485 + (L - 486) = L - 1 by omega], hle⟩⟩
    have hsum2 : (S2.card : ℝ) ≤ ∑ j ∈ Finset.range 27, ((SL2 j).card : ℝ) := by
      exact_mod_cast (Finset.card_le_card hcov2).trans Finset.card_biUnion_le
    have hper_j : ∀ j ∈ Finset.range 27,
        ((SL2 j).card : ℝ) ≤
          (16 * 108 / (3125 * 10 ^ 6 : ℝ)) * (2 : ℝ) ^ 1280 / (16 : ℝ) ^ k0 * (T0 * qL ^ j) * (phiF 1 1 * rhoF ^ m) := by
      intro j _
      have hfib := card_le_list_sum_fiber (SL2 j) pairList (fun x => (g1 x, g2 x))
        (fun x hx => hpair_mem x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1)
      have hper_p : ∀ p12 ∈ pairList,
          (((SL2 j).filter (fun x => (g1 x, g2 x) = p12)).card : ℝ) ≤
            (108 / (3125 * 10 ^ 6 : ℝ)) * (2 * (2 : ℝ) ^ 256 / (2 : ℝ) ^ k0) ^ 5 * (T0 * qL ^ j) *
              phiF (runF (1, 1) p12.2).1 (runF (1, 1) p12.2).2 := by
        rintro ⟨γ1, γ2⟩ _
        set F := (SL2 j).filter (fun x => (g1 x, g2 x) = (γ1, γ2))
        have hpos1 := runF_pos γ1 (by omega : 0 < 2) (by omega : 0 < 1)
        have hpos := runF_pos γ2 hpos1.1 hpos1.2
        have hpos' := runF_pos γ2 (by omega : 0 < 1) (by omega : 0 < 1)
        have hC'_R : (0 : ℝ) < ((runF (1, 1) γ2).1 : ℝ) := by exact_mod_cast hpos'.1
        have hD'_R : (0 : ℝ) < ((runF (1, 1) γ2).2 : ℝ) := by exact_mod_cast hpos'.2
        by_cases hne : F.Nonempty
        · obtain ⟨x0, hx0⟩ := hne
          have hx0_SL2 := (Finset.mem_filter.mp hx0).1
          have hx0_S2 := (Finset.mem_filter.mp hx0_SL2).1
          have hx0_Sk := (Finset.mem_filter.mp hx0_S2).1
          have hnc1 : ¬ c1Pred x0 := (Finset.mem_filter.mp hx0_S2).2.1
          have hphiB_le := (Finset.mem_filter.mp hx0_SL2).2.2
          have hpair0 := (Finset.mem_filter.mp hx0).2
          have hf0 := hx_facts x0 hx0_Sk
          have htr0 : traceKinds (SkywalkNat.init x0 ECDSAAdd.p) t = pref ++ γ1 ++ γ2 := by
            rw [hf0.2.2.2.1, (Prod.mk.inj hpair0).1, (Prod.mk.inj hpair0).2]
          have hF_eq : runF (0, 1) (pref ++ γ1 ++ γ2) = runF (runF (2, 1) γ1) γ2 := by
            rw [runF_append, runF_append, hrunF_pref]
          have hCD_gt : ECDSAAdd.p < (runF (runF (2, 1) γ1) γ2).1 * (runF (runF (2, 1) γ1) γ2).2 := by
            dsimp only [c1Pred] at hnc1; rw [htr0, hF_eq] at hnc1; omega
          have hcop := (runF_coprime_even_odd (γ1 ++ γ2) (by decide : (2 : Nat).Coprime 1) (by decide) (by decide)).1
          rw [runF_append] at hcop
          have hcF := forward_prefix_fiber_card F
            (fun x hx => let hf := hx_facts x (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1).1; ⟨hf.1, hf.2.1⟩)
            t (pref ++ γ1 ++ γ2)
            (fun x hx => by
              have hxSk := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1).1
              have hp := (Finset.mem_filter.mp hx).2
              have hf := hx_facts x hxSk
              exact ⟨by rw [hf.2.2.2.1, (Prod.mk.inj hp).1, (Prod.mk.inj hp).2], hf.2.2.1⟩)
            (by rw [hF_eq]; exact hpos.1) (by rw [hF_eq]; exact hpos.2) (by rw [hF_eq]; exact hcop)
          rw [hF_eq, Nat.div_eq_of_lt hCD_gt] at hcF
          have hval_2k := SkywalkNat.iter_valid (2 * k0) (SkywalkNat.init x0 ECDSAAdd.p) p_pos p_odd
          have hval_t := SkywalkNat.iter_valid t (SkywalkNat.init x0 ECDSAAdd.p) p_pos p_odd
          have halive_m : ∀ i < m, 0 < (SkywalkNat.step^[i] (SkywalkNat.step^[2 * k0] (SkywalkNat.init x0 ECDSAAdd.p))).u := by
            intro i hi; rw [← Function.iterate_add_apply]
            exact iter_alive_of_u_ne_zero _ (show i + 2 * k0 ≤ t by omega) (Nat.ne_of_gt hf0.2.2.1)
          have hBm := runB_traceKinds (SkywalkNat.step^[2 * k0] (SkywalkNat.init x0 ECDSAAdd.p)) m hval_2k.1 hval_2k.2.1 halive_m
          have hadd_m : m + 2 * k0 = t := by omega
          rw [← Function.iterate_add_apply, hadd_m] at hBm
          have hg2_eq : traceKinds (SkywalkNat.step^[2 * k0] (SkywalkNat.init x0 ECDSAAdd.p)) m = γ2 := (Prod.mk.inj hpair0).2
          rw [hg2_eq] at hBm
          have hdot' := runF_runB_dot γ2 1 1
            (SkywalkNat.step^[t] (SkywalkNat.init x0 ECDSAAdd.p)).u
            (SkywalkNat.step^[t] (SkywalkNat.init x0 ECDSAAdd.p)).v
          rw [hBm] at hdot'
          simp only [one_mul] at hdot'
          have hsumR := hf0.2.2.2.2.2.2.1
          have hlinR : ((runF (1, 1) γ2).1 : ℝ) * ((SkywalkNat.step^[t] (SkywalkNat.init x0 ECDSAAdd.p)).u : ℝ) +
              ((runF (1, 1) γ2).2 : ℝ) * ((SkywalkNat.step^[t] (SkywalkNat.init x0 ECDSAAdd.p)).v : ℝ) ≤
              2 * (2 : ℝ) ^ 256 / (2 : ℝ) ^ k0 := by
            have heqR : ((runF (1, 1) γ2).1 : ℝ) * ((SkywalkNat.step^[t] (SkywalkNat.init x0 ECDSAAdd.p)).u : ℝ) +
                ((runF (1, 1) γ2).2 : ℝ) * ((SkywalkNat.step^[t] (SkywalkNat.init x0 ECDSAAdd.p)).v : ℝ) =
                ((SkywalkNat.step^[2 * k0] (SkywalkNat.init x0 ECDSAAdd.p)).u : ℝ) +
                ((SkywalkNat.step^[2 * k0] (SkywalkNat.init x0 ECDSAAdd.p)).v : ℝ) := by exact_mod_cast hdot'
            rw [heqR]
            have hpR : 2 * (ECDSAAdd.p : ℝ) / (2 : ℝ) ^ k0 ≤ 2 * (2 : ℝ) ^ 256 / (2 : ℝ) ^ k0 := by
              have hple : (ECDSAAdd.p : ℝ) ≤ (2 : ℝ) ^ 256 := by exact_mod_cast p_lt_256.le
              exact div_le_div_of_nonneg_right (by linarith) (by positivity)
            linarith
          have hpow5 := pow_le_pow_left₀ (by positivity) hlinR 5
          have hcoup := coupling_lower hC'_R hD'_R
            (Nat.cast_pos.mpr hf0.2.2.1) (Nat.cast_pos.mpr hval_t.1)
          have hphiF_pos := phiF_pos hC'_R hD'_R
          have h1 : (3125 * 10 ^ 6 / 108 : ℝ) ≤
              phiF (runF (1, 1) γ2).1 (runF (1, 1) γ2).2 * (T0 * qL ^ j) * (2 * (2 : ℝ) ^ 256 / (2 : ℝ) ^ k0) ^ 5 :=
            hcoup.trans (mul_le_mul (mul_le_mul_of_nonneg_left hphiB_le hphiF_pos.le) hpow5
              (by positivity) (by unfold qL; positivity))
          have hcard1 : (F.card : ℝ) ≤ 1 := by exact_mod_cast hcF
          have h2 : (1 : ℝ) ≤ (108 / (3125 * 10 ^ 6 : ℝ)) * (2 * (2 : ℝ) ^ 256 / (2 : ℝ) ^ k0) ^ 5 *
              (T0 * qL ^ j) * phiF (runF (1, 1) γ2).1 (runF (1, 1) γ2).2 := by linarith
          exact hcard1.trans h2
        · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero]
          have := phiF_pos hC'_R hD'_R; unfold qL; positivity
      have h1 := hfib.trans (list_sum_map_le _ _ _ hper_p)
      rw [list_sum_mul_left] at h1
      dsimp only [pairList] at h1
      rw [list_sum_flatMap_real] at h1
      have hinner : ∀ γ1 ∈ pathsOf eo0Kinds (k0 - 1),
          (((pathsOf allKinds m).map (fun γ2 => (γ1, γ2))).map
            (fun p12 => phiF (runF (1, 1) p12.2).1 (runF (1, 1) p12.2).2)).sum ≤ phiF 1 1 * rhoF ^ m := by
        intro γ1 _
        simp only [List.map_map, Function.comp_def]
        simpa only [Nat.cast_one] using sum_pathsAll_phiF m 1 1 (by omega) (by omega)
      have h2 := list_sum_map_le _ _ _ hinner
      have hconst : ((pathsOf eo0Kinds (k0 - 1)).map (fun _ => phiF 1 1 * rhoF ^ m)).sum =
          (2 : ℝ) ^ (k0 - 1) * (phiF 1 1 * rhoF ^ m) := by
        rw [List.map_const', List.sum_replicate, nsmul_eq_mul, pathsOf_length]
        have hl : eo0Kinds.length = 2 := rfl
        rw [hl]; norm_cast
      rw [hconst] at h2
      have h3 := h1.trans (mul_le_mul_of_nonneg_left h2 (by unfold qL; positivity))
      refine h3.trans_eq ?_
      have hk0_eq : (2 : ℝ) ^ k0 = 2 * (2 : ℝ) ^ (k0 - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel hk0]
      have h16 : (16 : ℝ) ^ k0 = ((2 : ℝ) ^ k0) ^ 4 := by
        rw [show (16 : ℝ) = (2 : ℝ) ^ 4 by norm_num, ← pow_mul, mul_comm, pow_mul]
      have h1280 : ((2 : ℝ) ^ 256) ^ 5 = (2 : ℝ) ^ 1280 := by rw [← pow_mul]
      rw [div_pow, mul_pow, h1280, h16]
      have h2k_ne : (2 : ℝ) ^ k0 ≠ 0 := by positivity
      field_simp [h2k_ne]
      rw [hk0_eq]; ring
    have h1 := hsum2.trans (Finset.sum_le_sum hper_j)
    have hfact : ∑ j ∈ Finset.range 27,
        (16 * 108 / (3125 * 10 ^ 6 : ℝ)) * (2 : ℝ) ^ 1280 / (16 : ℝ) ^ k0 * (T0 * qL ^ j) * (phiF 1 1 * rhoF ^ m) =
        ((16 * 108 / (3125 * 10 ^ 6 : ℝ)) * (2 : ℝ) ^ 1280 / (16 : ℝ) ^ k0 * T0 * (phiF 1 1 * rhoF ^ m)) *
          ∑ j ∈ Finset.range 27, qL ^ j := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; generalize (2 : ℝ) ^ 1280 = P1280; ring
    rw [hfact] at h1
    have hg := geom_sum_le_inv (r := qL) (by unfold qL; positivity) (by unfold qL; norm_num) 27
    have hphi11_pos : 0 ≤ phiF 1 1 := (phiF_pos (by norm_num) (by norm_num)).le
    have h2 := h1.trans (mul_le_mul_of_nonneg_left hg (by unfold rhoF; positivity))
    refine h2.trans_eq ?_
    dsimp only [T0]
    have hpow : (2 : ℝ) ^ 1280 = (2 : ℝ) ^ 256 * (2 : ℝ) ^ 1024 := by rw [← pow_add]
    rw [hpow]; generalize (2 : ℝ) ^ 1024 = P1024; ring
  -- Case 3 bound on `S3`:
  have hS3 := case3_card_bound S3 (Finset.filter_subset _ _ |>.trans (Finset.filter_subset _ _)) t ht T0 hT0
    (fun x hx => (hx_facts x (Finset.mem_filter.mp hx).1).2.2.2.2.2.2.2)
    (fun x hx => (Finset.mem_filter.mp hx).2)
  have hS3' : (S3.card : ℝ) ≤ (2 : ℝ) ^ 256 *
      ((2 * phiB 1 1 * (rhoB / 2) ^ (485 - t) / (1 - (rhoB / 2) / qL) +
        (2 / (2 : ℝ) ^ 256) * phiB 1 1 * rhoB ^ (485 - t) / (1 - rhoB / qL)) * (2 : ℝ) ^ e) := by
    refine hS3.trans_eq ?_
    dsimp only [T0]; field_simp
  have hadd := add_le_add (add_le_add hS1 hS2) hS3'
  rw [← mul_add, ← mul_add] at hadd
  exact hsplit.trans hadd

/-! ### 8. Repeated-squaring numeric bounds and final `skywalk_bad485_card` theorem -/

private theorem pow_step {x : ℝ} {n : Nat} {a b : ℝ} {e1 e2 : Int}
    (hx : 0 ≤ x) (h1 : x ^ n ≤ a * (2 : ℝ) ^ e1) (hsq : a ^ 2 * (2 : ℝ) ^ (2 * e1 - e2) ≤ b) :
    x ^ (2 * n) ≤ b * (2 : ℝ) ^ e2 := by
  have h2 : x ^ (2 * n) = (x ^ n) ^ 2 := by rw [mul_comm, pow_mul]
  rw [h2]
  have h3 := pow_le_pow_left₀ (pow_nonneg hx n) h1 2
  have hpow2 : ((2 : ℝ) ^ e1) ^ 2 = (2 : ℝ) ^ (2 * e1) := by
    rw [← zpow_natCast ((2 : ℝ) ^ e1), ← zpow_mul]; congr 1; ring
  calc (x ^ n) ^ 2 ≤ (a * (2 : ℝ) ^ e1) ^ 2 := h3
    _ = a ^ 2 * (2 : ℝ) ^ (2 * e1) := by rw [mul_pow, hpow2]
    _ = (a ^ 2 * (2 : ℝ) ^ (2 * e1 - e2)) * (2 : ℝ) ^ e2 := by
        rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), sub_add_cancel]
    _ ≤ b * (2 : ℝ) ^ e2 := mul_le_mul_of_nonneg_right hsq (by positivity)

private theorem pow_mul2 {x : ℝ} (hx : 0 ≤ x) (n1 n2 : Nat) (a1 a2 b : ℝ) (e1 e2 e3 : Int)
    (h1 : x ^ n1 ≤ a1 * (2 : ℝ) ^ e1) (h2 : x ^ n2 ≤ a2 * (2 : ℝ) ^ e2)
    (ha1 : 0 ≤ a1) (_ha2 : 0 ≤ a2) (hab : a1 * a2 * (2 : ℝ) ^ (e1 + e2 - e3) ≤ b) :
    x ^ (n1 + n2) ≤ b * (2 : ℝ) ^ e3 := by
  rw [pow_add]
  have hmul := mul_le_mul h1 h2 (pow_nonneg hx n2) (by positivity)
  calc x ^ n1 * x ^ n2 ≤ (a1 * (2 : ℝ) ^ e1) * (a2 * (2 : ℝ) ^ e2) := hmul
    _ = (a1 * a2 * (2 : ℝ) ^ (e1 + e2 - e3)) * (2 : ℝ) ^ e3 := by
        have h2 : (2 : ℝ) ^ e1 * (2 : ℝ) ^ e2 = (2 : ℝ) ^ (e1 + e2 - e3) * (2 : ℝ) ^ e3 := by
          rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), sub_add_cancel]
        linear_combination a1 * a2 * h2
    _ ≤ b * (2 : ℝ) ^ e3 := mul_le_mul_of_nonneg_right hab (by positivity)

private theorem rhoF_pow_239_240 :
    rhoF ^ 239 ≤ (178057 / 100000 : ℝ) * (2 : ℝ) ^ (-431 : Int) ∧
    rhoF ^ 240 ≤ (102277 / 100000 : ℝ) * (2 : ℝ) ^ (-432 : Int) := by
  have h0 : 0 ≤ rhoF := by unfold rhoF; positivity
  have p1 : rhoF ^ 1 ≤ (114880 / 100000 : ℝ) * (2 : ℝ) ^ (-2 : Int) := by unfold rhoF; norm_num
  have p2 : rhoF ^ 2 ≤ (131975 / 100000 : ℝ) * (2 : ℝ) ^ (-4 : Int) := pow_step h0 p1 (by norm_num)
  have p4 : rhoF ^ 4 ≤ (174175 / 100000 : ℝ) * (2 : ℝ) ^ (-8 : Int) := pow_step h0 p2 (by norm_num)
  have p8 : rhoF ^ 8 ≤ (151685 / 100000 : ℝ) * (2 : ℝ) ^ (-15 : Int) := pow_step h0 p4 (by norm_num)
  have p16 : rhoF ^ 16 ≤ (115042 / 100000 : ℝ) * (2 : ℝ) ^ (-29 : Int) := pow_step h0 p8 (by norm_num)
  have p32 : rhoF ^ 32 ≤ (132347 / 100000 : ℝ) * (2 : ℝ) ^ (-58 : Int) := pow_step h0 p16 (by norm_num)
  have p64 : rhoF ^ 64 ≤ (175158 / 100000 : ℝ) * (2 : ℝ) ^ (-116 : Int) := pow_step h0 p32 (by norm_num)
  have p128 : rhoF ^ 128 ≤ (153402 / 100000 : ℝ) * (2 : ℝ) ^ (-231 : Int) := pow_step h0 p64 (by norm_num)
  have p192 := pow_mul2 h0 128 64 _ _ (134349 / 100000) _ _ (-346) p128 p64 (by norm_num) (by norm_num) (by norm_num)
  have p224 := pow_mul2 h0 192 32 _ _ (177807 / 100000) _ _ (-404) p192 p32 (by norm_num) (by norm_num) (by norm_num)
  have p240 := pow_mul2 h0 224 16 _ _ (102277 / 100000) _ _ (-432) p224 p16 (by norm_num) (by norm_num) (by norm_num)
  have p3 := pow_mul2 h0 2 1 _ _ (151613 / 100000) _ _ (-6) p2 p1 (by norm_num) (by norm_num) (by norm_num)
  have p7 := pow_mul2 h0 4 3 _ _ (132036 / 100000) _ _ (-13) p4 p3 (by norm_num) (by norm_num) (by norm_num)
  have p15 := pow_mul2 h0 8 7 _ _ (100140 / 100000) _ _ (-27) p8 p7 (by norm_num) (by norm_num) (by norm_num)
  have p239 := pow_mul2 h0 224 15 _ _ (178057 / 100000) _ _ (-431) p224 p15 (by norm_num) (by norm_num) (by norm_num)
  exact ⟨p239, p240⟩

private theorem rhoB_pow_244_246 :
    rhoB ^ 244 ≤ (191022 / 100000 : ℝ) * (2 : ℝ) ^ (-439 : Int) ∧
    rhoB ^ 246 ≤ (126842 / 100000 : ℝ) * (2 : ℝ) ^ (-442 : Int) := by
  have h0 : 0 ≤ rhoB := by unfold rhoB; positivity
  have p1 : rhoB ^ 1 ≤ (115240 / 100000 : ℝ) * (2 : ℝ) ^ (-2 : Int) := by unfold rhoB; norm_num
  have p2 : rhoB ^ 2 ≤ (132803 / 100000 : ℝ) * (2 : ℝ) ^ (-4 : Int) := pow_step h0 p1 (by norm_num)
  have p4 : rhoB ^ 4 ≤ (176367 / 100000 : ℝ) * (2 : ℝ) ^ (-8 : Int) := pow_step h0 p2 (by norm_num)
  have p8 : rhoB ^ 8 ≤ (155527 / 100000 : ℝ) * (2 : ℝ) ^ (-15 : Int) := pow_step h0 p4 (by norm_num)
  have p16 : rhoB ^ 16 ≤ (120944 / 100000 : ℝ) * (2 : ℝ) ^ (-29 : Int) := pow_step h0 p8 (by norm_num)
  have p32 : rhoB ^ 32 ≤ (146275 / 100000 : ℝ) * (2 : ℝ) ^ (-58 : Int) := pow_step h0 p16 (by norm_num)
  have p64 : rhoB ^ 64 ≤ (106982 / 100000 : ℝ) * (2 : ℝ) ^ (-115 : Int) := pow_step h0 p32 (by norm_num)
  have p128 : rhoB ^ 128 ≤ (114452 / 100000 : ℝ) * (2 : ℝ) ^ (-230 : Int) := pow_step h0 p64 (by norm_num)
  have p192 := pow_mul2 h0 128 64 _ _ (122444 / 100000) _ _ (-345) p128 p64 (by norm_num) (by norm_num) (by norm_num)
  have p224 := pow_mul2 h0 192 32 _ _ (179105 / 100000) _ _ (-403) p192 p32 (by norm_num) (by norm_num) (by norm_num)
  have p240 := pow_mul2 h0 224 16 _ _ (108309 / 100000) _ _ (-431) p224 p16 (by norm_num) (by norm_num) (by norm_num)
  have p244 := pow_mul2 h0 240 4 _ _ (191022 / 100000) _ _ (-439) p240 p4 (by norm_num) (by norm_num) (by norm_num)
  have p246 := pow_mul2 h0 244 2 _ _ (126842 / 100000) _ _ (-442) p244 p2 (by norm_num) (by norm_num) (by norm_num)
  exact ⟨p244, p246⟩

private theorem tail_k0_ge_36 :
    (((Finset.Ioo 0 ECDSAAdd.p).filter (fun x => 2 ^ 36 ∣ x)).card : ℝ) ≤ (2 : ℝ) ^ 256 / (2 : ℝ) ^ 36 := by
  set S := (Finset.Ioo 0 ECDSAAdd.p).filter (fun x => 2 ^ 36 ∣ x)
  have hinj : Set.InjOn (fun x => x / 2 ^ 36) (S : Set Nat) := by
    intro a ha b hb heq
    dsimp only at heq
    have ha' := Nat.mul_div_cancel' (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
    have hb' := Nat.mul_div_cancel' (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2
    rw [← ha', ← hb', heq]
  have hpow : 2 ^ 256 = 2 ^ 220 * 2 ^ 36 := by rw [← pow_add]
  have h2_36 : 0 < 2 ^ 36 := Nat.two_pow_pos 36
  generalize hM : (2 ^ 220 : Nat) = M at hpow
  have hmap : Set.MapsTo (fun x => x / 2 ^ 36) (S : Set Nat) (Finset.range M : Set Nat) := by
    intro x hx
    rw [Finset.mem_coe, Finset.mem_range]
    have hxp : x < 2 ^ 256 := (Finset.mem_Ioo.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).1).2.trans p_lt_256
    exact (Nat.div_lt_iff_lt_mul h2_36).mpr (hpow ▸ hxp)
  have hc := Finset.card_le_card_of_injOn (fun x => x / 2 ^ 36) hmap hinj
  rw [Finset.card_range, ← hM] at hc
  have hR : (S.card : ℝ) ≤ (2 : ℝ) ^ 220 := by exact_mod_cast hc
  refine hR.trans_eq ?_
  rw [show (2 : ℝ) ^ 256 = (2 : ℝ) ^ 220 * (2 : ℝ) ^ 36 by rw [← pow_add]]
  field_simp

theorem skywalk_bad485_card :
    (Bad485.card : ℝ) ≤ (15 : ℝ) / 10 ^ 11 * (2 : ℝ) ^ 256 := by
  let Stail := (Finset.Ioo 0 ECDSAAdd.p).filter (fun x => 2 ^ 36 ∣ x)
  let Smid := (Finset.range 7).biUnion (fun q => (Finset.Icc 1 5).biUnion (fun r => Bad485_k0 (5 * q + r)))
  have hcov : Bad485 ⊆ Bad485_k0 0 ∪ Smid ∪ Stail := by
    intro x hx
    have hxI := (Finset.mem_filter.mp hx).1
    obtain ⟨_, _⟩ := Finset.mem_Ioo.mp hxI
    by_cases h36 : 2 ^ 36 ∣ x
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hxI, h36⟩)
    · apply Finset.mem_union_left
      have hex : ∃ k, ¬ 2 ^ (k + 1) ∣ x := ⟨35, h36⟩
      let k0 := Nat.find hex
      have hk0_lt : k0 < 36 := by have := Nat.find_min' hex h36; omega
      have hdiv : 2 ^ k0 ∣ x := by
        cases hk : k0 with
        | zero => simp
        | succ j =>
          have hnj := Nat.find_min hex (show j < k0 by omega)
          push_neg at hnj; exact hnj
      have hodd : (x / 2 ^ k0) % 2 = 1 := by
        have hndiv : ¬ 2 ^ (k0 + 1) ∣ x := Nat.find_spec hex
        by_contra he
        apply hndiv
        obtain ⟨q, hq⟩ := hdiv
        have hq_even : q % 2 = 0 := by
          have : x / 2 ^ k0 = q := by rw [hq, Nat.mul_div_cancel_left _ (by positivity)]
          omega
        refine ⟨q / 2, ?_⟩
        rw [hq, pow_succ, mul_assoc]; congr 1; omega
      have hmem_k0 : x ∈ Bad485_k0 k0 := Finset.mem_filter.mpr ⟨hx, hdiv, hodd⟩
      by_cases hz : k0 = 0
      · rw [hz] at hmem_k0; exact Finset.mem_union_left _ hmem_k0
      · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨(k0 - 1) / 5, Finset.mem_range.mpr (by omega),
          Finset.mem_biUnion.mpr ⟨(k0 - 1) % 5 + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩⟩)
        rwa [show 5 * ((k0 - 1) / 5) + ((k0 - 1) % 5 + 1) = k0 by omega]
  have hcard_total : (Bad485.card : ℝ) ≤
      ((Bad485_k0 0).card : ℝ) +
      (∑ q ∈ Finset.range 7, ∑ r ∈ Finset.Icc 1 5, ((Bad485_k0 (5 * q + r)).card : ℝ)) +
      (Stail.card : ℝ) := by
    have h1 := (Finset.card_le_card hcov).trans (Finset.card_union_le _ _)
    have h2 := Finset.card_union_le (Bad485_k0 0) Smid
    have h3 : Smid.card ≤ ∑ q ∈ Finset.range 7, ∑ r ∈ Finset.Icc 1 5, (Bad485_k0 (5 * q + r)).card :=
      Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun q _ => Finset.card_biUnion_le))
    have hnat : Bad485.card ≤ (Bad485_k0 0).card +
        (∑ q ∈ Finset.range 7, ∑ r ∈ Finset.Icc 1 5, (Bad485_k0 (5 * q + r)).card) + Stail.card := by omega
    exact_mod_cast hnat
  obtain ⟨hrF239, hrF240⟩ := rhoF_pow_239_240
  obtain ⟨hrB244, hrB246⟩ := rhoB_pow_244_246
  obtain ⟨hphiF21, hphiF11, hphiB11⟩ := phi_consts
  -- Piece 1: `k0 = 0` (`≤ 10^(-13) * 2^256`)
  have h0_bound : ((Bad485_k0 0).card : ℝ) ≤ (1 / 10 ^ 13 : ℝ) * (2 : ℝ) ^ 256 := by
    have hb0 := bad485_k0_zero_bound
    have ht1 : (2 : ℝ) ^ 384 / 1000 * phiF 2 1 * rhoF ^ 240 ≤ (1 / 10 ^ 14 : ℝ) := by
      have h1 : (2 : ℝ) ^ 384 / 1000 * phiF 2 1 * rhoF ^ 240 ≤
          (2 : ℝ) ^ 384 / 1000 * 1215 * ((102277 / 100000 : ℝ) * (2 : ℝ) ^ (-432 : Int)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hphiF21 (div_nonneg (pow_nonneg (by norm_num) _) (by norm_num)))
          hrF240 (by unfold rhoF; positivity) (mul_nonneg (div_nonneg (pow_nonneg (by norm_num) _) (by norm_num)) (by norm_num))
      refine h1.trans ?_
      have hz : (2 : ℝ) ^ 384 * (2 : ℝ) ^ (-432 : Int) = (2 : ℝ) ^ (-48 : Int) := by
        rw [← zpow_natCast (2 : ℝ) 384, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1
      have heq : (2 : ℝ) ^ 384 / 1000 * 1215 * ((102277 / 100000 : ℝ) * (2 : ℝ) ^ (-432 : Int)) =
          (1215 * 102277 / 100000000 : ℝ) * ((2 : ℝ) ^ 384 * (2 : ℝ) ^ (-432 : Int)) := by
        generalize (2 : ℝ) ^ 384 = P384; ring
      rw [heq, hz]; norm_num
    have ht2 : (108 / (3125 * 10 ^ 6 : ℝ) * (2 : ℝ) ^ 1024 * phiF 2 1 * rhoF ^ 240 / (1 - qL)) / (2 : ℝ) ^ 624 ≤ (2 / 10 ^ 14 : ℝ) := by
      have h1 : (108 / (3125 * 10 ^ 6 : ℝ) * (2 : ℝ) ^ 1024 * phiF 2 1 * rhoF ^ 240 / (1 - qL)) / (2 : ℝ) ^ 624 ≤
          (108 / (3125 * 10 ^ 6 : ℝ) * (2 : ℝ) ^ 1024 * 1215 * ((102277 / 100000 : ℝ) * (2 : ℝ) ^ (-432 : Int)) / (1 - qL)) / (2 : ℝ) ^ 624 := by
        have hq : 0 < 1 - qL := by unfold qL; norm_num
        have hphi : 0 ≤ phiF 2 1 := (phiF_pos (by norm_num) (by norm_num)).le
        have hrF_nn : 0 ≤ rhoF ^ 240 := by unfold rhoF; positivity
        gcongr
      refine h1.trans ?_
      have hz : (2 : ℝ) ^ 1024 * (2 : ℝ) ^ (-432 : Int) / (2 : ℝ) ^ 624 = (2 : ℝ) ^ (-32 : Int) := by
        rw [← zpow_natCast (2 : ℝ) 1024, ← zpow_natCast (2 : ℝ) 624,
            ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), ← zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1
      have heq : (108 / (3125 * 10 ^ 6 : ℝ) * (2 : ℝ) ^ 1024 * 1215 * ((102277 / 100000 : ℝ) * (2 : ℝ) ^ (-432 : Int)) / (1 - qL)) / (2 : ℝ) ^ 624 =
          (108 / (3125 * 10 ^ 6 : ℝ) * 1215 * (102277 / 100000 : ℝ) / (1 - qL)) *
            ((2 : ℝ) ^ 1024 * (2 : ℝ) ^ (-432 : Int) / (2 : ℝ) ^ 624) := by
        generalize (2 : ℝ) ^ 1024 = P1024; generalize (2 : ℝ) ^ 624 = P624; ring
      rw [heq, hz]; unfold qL; norm_num
    have ht3 : (2 * phiB 1 1 * (rhoB / 2) ^ 244 / (1 - (rhoB / 2) / qL) +
        (2 / (2 : ℝ) ^ 256) * phiB 1 1 * rhoB ^ 244 / (1 - rhoB / qL)) * (2 : ℝ) ^ 624 ≤ (3 / 10 ^ 14 : ℝ) := by
      rw [div_pow rhoB 2 244]
      have h1 : (2 * phiB 1 1 * (rhoB ^ 244 / (2 : ℝ) ^ 244) / (1 - (rhoB / 2) / qL) +
          (2 / (2 : ℝ) ^ 256) * phiB 1 1 * rhoB ^ 244 / (1 - rhoB / qL)) * (2 : ℝ) ^ 624 ≤
          (2 * 1539 * ((191022 / 100000 : ℝ) * (2 : ℝ) ^ (-439 : Int) / (2 : ℝ) ^ 244) / (1 - (rhoB / 2) / qL) +
          (2 / (2 : ℝ) ^ 256) * 1539 * ((191022 / 100000 : ℝ) * (2 : ℝ) ^ (-439 : Int)) / (1 - rhoB / qL)) * (2 : ℝ) ^ 624 := by
        have hq1 : 0 < 1 - (rhoB / 2) / qL := by unfold rhoB qL; norm_num
        have hq2 : 0 < 1 - rhoB / qL := by unfold rhoB qL; norm_num
        have hphi : 0 ≤ phiB 1 1 := (phiB_pos (by norm_num) (by norm_num)).le
        have hrB_nn : 0 ≤ rhoB ^ 244 := by unfold rhoB; positivity
        gcongr
      refine h1.trans ?_
      have hz1 : (2 : ℝ) ^ (-439 : Int) / (2 : ℝ) ^ 244 * (2 : ℝ) ^ 624 = (2 : ℝ) ^ (-59 : Int) := by
        rw [← zpow_natCast (2 : ℝ) 244, ← zpow_natCast (2 : ℝ) 624,
            ← zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1
      have hz2 : (2 : ℝ) ^ (-439 : Int) / (2 : ℝ) ^ 256 * (2 : ℝ) ^ 624 = (2 : ℝ) ^ (-71 : Int) := by
        rw [← zpow_natCast (2 : ℝ) 256, ← zpow_natCast (2 : ℝ) 624,
            ← zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1
      have heq : (2 * 1539 * ((191022 / 100000 : ℝ) * (2 : ℝ) ^ (-439 : Int) / (2 : ℝ) ^ 244) / (1 - (rhoB / 2) / qL) +
          (2 / (2 : ℝ) ^ 256) * 1539 * ((191022 / 100000 : ℝ) * (2 : ℝ) ^ (-439 : Int)) / (1 - rhoB / qL)) * (2 : ℝ) ^ 624 =
          (2 * 1539 * (191022 / 100000 : ℝ) / (1 - (rhoB / 2) / qL)) * ((2 : ℝ) ^ (-439 : Int) / (2 : ℝ) ^ 244 * (2 : ℝ) ^ 624) +
          (2 * 1539 * (191022 / 100000 : ℝ) / (1 - rhoB / qL)) * ((2 : ℝ) ^ (-439 : Int) / (2 : ℝ) ^ 256 * (2 : ℝ) ^ 624) := by
        generalize (2 : ℝ) ^ 624 = P624; ring
      rw [heq, hz1, hz2]; unfold rhoB qL; norm_num
    have hsum_t : _ + _ + _ ≤ (1 / 10 ^ 13 : ℝ) :=
      (add_le_add (add_le_add ht1 ht2) ht3).trans (by norm_num)
    exact hb0.trans ((mul_le_mul_of_nonneg_left hsum_t (by positivity)).trans_eq (mul_comm _ _))
  -- Piece 2: separable `(q ∈ range 7, r ∈ Icc 1 5)` sum (`≤ 130 / 10^12 * 2^256`)
  have hmid_bound : (∑ q ∈ Finset.range 7, ∑ r ∈ Finset.Icc 1 5, ((Bad485_k0 (5 * q + r)).card : ℝ)) ≤
      (130 / 10 ^ 12 : ℝ) * (2 : ℝ) ^ 256 := by
    have hrhoF_ne : rhoF ≠ 0 := by unfold rhoF; norm_num
    have hrhoB_ne : rhoB ≠ 0 := by unfold rhoB; norm_num
    have hrhoEO0_ne : rhoEO0 ≠ 0 := by unfold rhoEO0; norm_num
    let b1 : ℝ := (2 : ℝ) ^ 384 / 1000 * phiF 2 1 * rhoF ^ 239 / rhoEO0
    let q1 : ℝ := rhoEO0 ^ 5 / rhoF ^ 6
    let r1 : ℝ := rhoEO0 / rhoF
    let b2 : ℝ := (16 * 108 / (3125 * 10 ^ 6 : ℝ)) * (2 : ℝ) ^ 1024 * phiF 1 1 * rhoF ^ 239 / (1 - qL) / (2 : ℝ) ^ 628
    let q2 : ℝ := (2 : ℝ) ^ 10 / ((16 : ℝ) ^ 5 * rhoF ^ 6)
    let r2 : ℝ := 4 / (16 * rhoF)
    let b3a : ℝ := 2 * phiB 1 1 * (rhoB / 2) ^ 246 / (1 - (rhoB / 2) / qL) * (2 : ℝ) ^ 628
    let q3a : ℝ := 1 / ((2 : ℝ) ^ 10 * (rhoB / 2) ^ 4)
    let r3a : ℝ := 1 / (4 * (rhoB / 2))
    let b3b : ℝ := (2 / (2 : ℝ) ^ 256) * phiB 1 1 * rhoB ^ 246 / (1 - rhoB / qL) * (2 : ℝ) ^ 628
    let q3b : ℝ := 1 / ((2 : ℝ) ^ 10 * rhoB ^ 4)
    let r3b : ℝ := 1 / (4 * rhoB)
    have hper_qr : ∀ q ∈ Finset.range 7, ∀ r ∈ Finset.Icc 1 5,
        ((Bad485_k0 (5 * q + r)).card : ℝ) ≤
          (2 : ℝ) ^ 256 * (b1 * q1 ^ q * r1 ^ r + b2 * q2 ^ q * r2 ^ r +
            b3a * q3a ^ q * r3a ^ r + b3b * q3b ^ q * r3b ^ r) := by
      intro q hq r hr
      have hq7 : q < 7 := Finset.mem_range.mp hq
      obtain ⟨hr1, hr5⟩ := Finset.mem_Icc.mp hr
      set k0 := 5 * q + r
      set m := 239 - 6 * q - r
      set e := 628 - 10 * q - 2 * r
      have hcall := bad485_k0_pos_bound k0 m e (by omega) (by omega) (by omega)
      refine hcall.trans_eq ?_
      apply congrArg ((2 : ℝ) ^ 256 * ·)
      have hm_add : m + (6 * q + r) = 239 := by omega
      have he_add : e + (10 * q + 2 * r) = 628 := by omega
      have hLb_add : (485 - (2 * k0 + m)) + (4 * q + r) = 246 := by omega
      have hk_sub : (k0 - 1) + 1 = 5 * q + r := by omega
      have hpow_m : rhoF ^ m = rhoF ^ 239 / (rhoF ^ 6) ^ q / rhoF ^ r := by
        have h1 : rhoF ^ 239 = rhoF ^ m * ((rhoF ^ 6) ^ q * rhoF ^ r) := by
          rw [← pow_mul, ← pow_add, ← pow_add, hm_add]
        rw [h1]; field_simp [hrhoF_ne]
      have hpow_e : (2 : ℝ) ^ e = (2 : ℝ) ^ 628 / ((2 : ℝ) ^ 10) ^ q / (4 : ℝ) ^ r := by
        have h1 : (2 : ℝ) ^ 628 = (2 : ℝ) ^ e * (((2 : ℝ) ^ 10) ^ q * (4 : ℝ) ^ r) := by
          rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add, he_add]
        rw [h1]; field_simp
      have hpow_eo : rhoEO0 ^ (k0 - 1) = (rhoEO0 ^ 5) ^ q * rhoEO0 ^ r / rhoEO0 := by
        have h1 : rhoEO0 ^ (k0 - 1) * rhoEO0 = (rhoEO0 ^ 5) ^ q * rhoEO0 ^ r := by
          rw [← pow_succ, hk_sub, ← pow_mul, ← pow_add]
        rw [← h1]; field_simp [hrhoEO0_ne]
      have hpow_16 : (16 : ℝ) ^ k0 = ((16 : ℝ) ^ 5) ^ q * (16 : ℝ) ^ r := by
        dsimp only [k0]; rw [pow_add, pow_mul]
      have hpow_Lb1 : (rhoB / 2) ^ (485 - (2 * k0 + m)) = (rhoB / 2) ^ 246 / ((rhoB / 2) ^ 4) ^ q / (rhoB / 2) ^ r := by
        have h1 : (rhoB / 2) ^ 246 = (rhoB / 2) ^ (485 - (2 * k0 + m)) * (((rhoB / 2) ^ 4) ^ q * (rhoB / 2) ^ r) := by
          rw [← pow_mul, ← pow_add, ← pow_add, hLb_add]
        rw [h1]; field_simp [hrhoB_ne]
      have hpow_Lb2 : rhoB ^ (485 - (2 * k0 + m)) = rhoB ^ 246 / (rhoB ^ 4) ^ q / rhoB ^ r := by
        have h1 : rhoB ^ 246 = rhoB ^ (485 - (2 * k0 + m)) * ((rhoB ^ 4) ^ q * rhoB ^ r) := by
          rw [← pow_mul, ← pow_add, ← pow_add, hLb_add]
        rw [h1]; field_simp [hrhoB_ne]
      dsimp only [b1, q1, r1, b2, q2, r2, b3a, q3a, r3a, b3b, q3b, r3b]
      rw [hpow_m, hpow_e, hpow_eo, hpow_16, hpow_Lb1, hpow_Lb2]
      have hq1_p : (rhoEO0 ^ 5 / rhoF ^ 6) ^ q = (rhoEO0 ^ 5) ^ q / (rhoF ^ 6) ^ q := div_pow _ _ _
      have hr1_p : (rhoEO0 / rhoF) ^ r = rhoEO0 ^ r / rhoF ^ r := div_pow _ _ _
      have hq2_p : ((2 : ℝ) ^ 10 / ((16 : ℝ) ^ 5 * rhoF ^ 6)) ^ q = ((2 : ℝ) ^ 10) ^ q / (((16 : ℝ) ^ 5) ^ q * (rhoF ^ 6) ^ q) := by
        rw [div_pow, mul_pow]
      have hr2_p : (4 / (16 * rhoF)) ^ r = (4 : ℝ) ^ r / ((16 : ℝ) ^ r * rhoF ^ r) := by rw [div_pow, mul_pow]
      have hq3a_p : (1 / ((2 : ℝ) ^ 10 * (rhoB / 2) ^ 4)) ^ q = 1 / (((2 : ℝ) ^ 10) ^ q * ((rhoB / 2) ^ 4) ^ q) := by
        rw [one_div_pow, mul_pow, one_div]
      have hr3a_p : (1 / (4 * (rhoB / 2))) ^ r = 1 / ((4 : ℝ) ^ r * (rhoB / 2) ^ r) := by
        rw [one_div_pow, mul_pow, one_div]
      have hq3b_p : (1 / ((2 : ℝ) ^ 10 * rhoB ^ 4)) ^ q = 1 / (((2 : ℝ) ^ 10) ^ q * (rhoB ^ 4) ^ q) := by
        rw [one_div_pow, mul_pow, one_div]
      have hr3b_p : (1 / (4 * rhoB)) ^ r = 1 / ((4 : ℝ) ^ r * rhoB ^ r) := by
        rw [one_div_pow, mul_pow, one_div]
      rw [hq1_p, hr1_p, hq2_p, hr2_p, hq3a_p, hr3a_p, hq3b_p, hr3b_p]
      have hqL1 : 1 - qL ≠ 0 := by unfold qL; norm_num
      have hqLa : 1 - rhoB / 2 / qL ≠ 0 := by unfold rhoB qL; norm_num
      have hqLb : 1 - rhoB / qL ≠ 0 := by unfold rhoB qL; norm_num
      field_simp [hrhoF_ne, hrhoB_ne, hrhoEO0_ne, hqL1, hqLa, hqLb]
      generalize (2 : ℝ) ^ 384 = P384; generalize (2 : ℝ) ^ 628 = P628; generalize (2 : ℝ) ^ 1024 = P1024; ring
    have hsum_qr := Finset.sum_le_sum (fun q hq => Finset.sum_le_sum (fun r hr => hper_qr q hq r hr))
    have hsep : ∀ (b A B : ℝ),
        (∑ q ∈ Finset.range 7, ∑ r ∈ Finset.Icc 1 5, b * A ^ q * B ^ r) =
        b * (∑ q ∈ Finset.range 7, A ^ q) * (∑ r ∈ Finset.Icc 1 5, B ^ r) := fun b A B => by
      have h1 : ∀ q, (∑ r ∈ Finset.Icc 1 5, b * A ^ q * B ^ r) = (b * A ^ q) * (∑ r ∈ Finset.Icc 1 5, B ^ r) :=
        fun q => by rw [Finset.mul_sum]
      simp_rw [h1, ← Finset.sum_mul, ← Finset.mul_sum]
    have hpull : (∑ q ∈ Finset.range 7, ∑ r ∈ Finset.Icc 1 5,
        (2 : ℝ) ^ 256 * (b1 * q1 ^ q * r1 ^ r + b2 * q2 ^ q * r2 ^ r +
          b3a * q3a ^ q * r3a ^ r + b3b * q3b ^ q * r3b ^ r)) =
        (2 : ℝ) ^ 256 * (
          b1 * (∑ q ∈ Finset.range 7, q1 ^ q) * (∑ r ∈ Finset.Icc 1 5, r1 ^ r) +
          b2 * (∑ q ∈ Finset.range 7, q2 ^ q) * (∑ r ∈ Finset.Icc 1 5, r2 ^ r) +
          b3a * (∑ q ∈ Finset.range 7, q3a ^ q) * (∑ r ∈ Finset.Icc 1 5, r3a ^ r) +
          b3b * (∑ q ∈ Finset.range 7, q3b ^ q) * (∑ r ∈ Finset.Icc 1 5, r3b ^ r)) := by
      simp_rw [← Finset.mul_sum, Finset.sum_add_distrib, hsep]
    rw [hpull] at hsum_qr
    have hG1q : ∑ q ∈ Finset.range 7, q1 ^ q ≤ 115 := by
      dsimp only [q1]; unfold rhoEO0 rhoF
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num
    have hG1r : ∑ r ∈ Finset.Icc 1 5, r1 ^ r ≤ 36 / 10 := by
      dsimp only [r1]; unfold rhoEO0 rhoF
      rw [show (Finset.Icc 1 5 : Finset Nat) = {1, 2, 3, 4, 5} by decide]
      simp; norm_num
    have hG2q : ∑ q ∈ Finset.range 7, q2 ^ q ≤ 64 := by
      dsimp only [q2]; unfold rhoF
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num
    have hG2r : ∑ r ∈ Finset.Icc 1 5, r2 ^ r ≤ 34 / 10 := by
      dsimp only [r2]; unfold rhoF
      rw [show (Finset.Icc 1 5 : Finset Nat) = {1, 2, 3, 4, 5} by decide]
      simp; norm_num
    have hG3aq : ∑ q ∈ Finset.range 7, q3a ^ q ≤ 243 := by
      dsimp only [q3a]; unfold rhoB
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num
    have hG3ar : ∑ r ∈ Finset.Icc 1 5, r3a ^ r ≤ 35 := by
      dsimp only [r3a]; unfold rhoB
      rw [show (Finset.Icc 1 5 : Finset Nat) = {1, 2, 3, 4, 5} by decide]
      simp; norm_num
    have hG3bq : ∑ q ∈ Finset.range 7, q3b ^ q ≤ 2 := by
      dsimp only [q3b]; unfold rhoB
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num
    have hG3br : ∑ r ∈ Finset.Icc 1 5, r3b ^ r ≤ 4 := by
      dsimp only [r3b]; unfold rhoB
      rw [show (Finset.Icc 1 5 : Finset Nat) = {1, 2, 3, 4, 5} by decide]
      simp; norm_num
    have hb1 : b1 ≤ 61 / 10 ^ 15 := by
      dsimp only [b1]
      have h1 : (2 : ℝ) ^ 384 / 1000 * phiF 2 1 * rhoF ^ 239 / rhoEO0 ≤
          (2 : ℝ) ^ 384 / 1000 * 1215 * ((178057 / 100000 : ℝ) * (2 : ℝ) ^ (-431 : Int)) / rhoEO0 := by
        have hphi : 0 ≤ phiF 2 1 := (phiF_pos (by norm_num) (by norm_num)).le
        have heo : 0 < rhoEO0 := by unfold rhoEO0; norm_num
        have hrF_nn : 0 ≤ rhoF ^ 239 := by unfold rhoF; positivity
        gcongr
      refine h1.trans ?_
      have hz : (2 : ℝ) ^ 384 * (2 : ℝ) ^ (-431 : Int) = (2 : ℝ) ^ (-47 : Int) := by
        rw [← zpow_natCast (2 : ℝ) 384, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1
      have heq : (2 : ℝ) ^ 384 / 1000 * 1215 * ((178057 / 100000 : ℝ) * (2 : ℝ) ^ (-431 : Int)) / rhoEO0 =
          (1215 * 178057 / 100000000 / rhoEO0) * ((2 : ℝ) ^ 384 * (2 : ℝ) ^ (-431 : Int)) := by
        generalize (2 : ℝ) ^ 384 = P384; ring
      rw [heq, hz]; unfold rhoEO0; norm_num
    have hb2 : b2 ≤ 255 / 10 ^ 15 := by
      dsimp only [b2]
      have h1 : (16 * 108 / (3125 * 10 ^ 6 : ℝ)) * (2 : ℝ) ^ 1024 * phiF 1 1 * rhoF ^ 239 / (1 - qL) / (2 : ℝ) ^ 628 ≤
          (16 * 108 / (3125 * 10 ^ 6 : ℝ)) * (2 : ℝ) ^ 1024 * 5411 * ((178057 / 100000 : ℝ) * (2 : ℝ) ^ (-431 : Int)) / (1 - qL) / (2 : ℝ) ^ 628 := by
        have hphi : 0 ≤ phiF 1 1 := (phiF_pos (by norm_num) (by norm_num)).le
        have hq : 0 < 1 - qL := by unfold qL; norm_num
        have hrF_nn : 0 ≤ rhoF ^ 239 := by unfold rhoF; positivity
        gcongr
      refine h1.trans ?_
      have hz : (2 : ℝ) ^ 1024 * (2 : ℝ) ^ (-431 : Int) / (2 : ℝ) ^ 628 = (2 : ℝ) ^ (-35 : Int) := by
        rw [← zpow_natCast (2 : ℝ) 1024, ← zpow_natCast (2 : ℝ) 628,
            ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), ← zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1
      have heq : (16 * 108 / (3125 * 10 ^ 6 : ℝ)) * (2 : ℝ) ^ 1024 * 5411 * ((178057 / 100000 : ℝ) * (2 : ℝ) ^ (-431 : Int)) / (1 - qL) / (2 : ℝ) ^ 628 =
          (16 * 108 / (3125 * 10 ^ 6 : ℝ) * 5411 * (178057 / 100000 : ℝ) / (1 - qL)) *
            ((2 : ℝ) ^ 1024 * (2 : ℝ) ^ (-431 : Int) / (2 : ℝ) ^ 628) := by
        generalize (2 : ℝ) ^ 1024 = P1024; generalize (2 : ℝ) ^ 628 = P628; ring
      rw [heq, hz]; unfold qL; norm_num
    have hb3a : b3a ≤ 56 / 10 ^ 16 := by
      dsimp only [b3a]
      rw [div_pow rhoB 2 246]
      have h1 : 2 * phiB 1 1 * (rhoB ^ 246 / (2 : ℝ) ^ 246) / (1 - rhoB / 2 / qL) * (2 : ℝ) ^ 628 ≤
          2 * 1539 * ((126842 / 100000 : ℝ) * (2 : ℝ) ^ (-442 : Int) / (2 : ℝ) ^ 246) / (1 - rhoB / 2 / qL) * (2 : ℝ) ^ 628 := by
        have hphi : 0 ≤ phiB 1 1 := (phiB_pos (by norm_num) (by norm_num)).le
        have hq : 0 < 1 - rhoB / 2 / qL := by unfold rhoB qL; norm_num
        have hrB_nn : 0 ≤ rhoB ^ 246 := by unfold rhoB; positivity
        gcongr
      refine h1.trans ?_
      have hz : (2 : ℝ) ^ (-442 : Int) / (2 : ℝ) ^ 246 * (2 : ℝ) ^ 628 = (2 : ℝ) ^ (-60 : Int) := by
        rw [← zpow_natCast (2 : ℝ) 246, ← zpow_natCast (2 : ℝ) 628,
            ← zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1
      have heq : 2 * 1539 * ((126842 / 100000 : ℝ) * (2 : ℝ) ^ (-442 : Int) / (2 : ℝ) ^ 246) / (1 - rhoB / 2 / qL) * (2 : ℝ) ^ 628 =
          (2 * 1539 * (126842 / 100000 : ℝ) / (1 - rhoB / 2 / qL)) * ((2 : ℝ) ^ (-442 : Int) / (2 : ℝ) ^ 246 * (2 : ℝ) ^ 628) := by
        generalize (2 : ℝ) ^ 628 = P628; ring
      rw [heq, hz]; unfold rhoB qL; norm_num
    have hb3b : b3b ≤ 1 / 10 ^ 16 := by
      dsimp only [b3b]
      have h1 : (2 / (2 : ℝ) ^ 256) * phiB 1 1 * rhoB ^ 246 / (1 - rhoB / qL) * (2 : ℝ) ^ 628 ≤
          (2 / (2 : ℝ) ^ 256) * 1539 * ((126842 / 100000 : ℝ) * (2 : ℝ) ^ (-442 : Int)) / (1 - rhoB / qL) * (2 : ℝ) ^ 628 := by
        have hphi : 0 ≤ phiB 1 1 := (phiB_pos (by norm_num) (by norm_num)).le
        have hq : 0 < 1 - rhoB / qL := by unfold rhoB qL; norm_num
        have hrB_nn : 0 ≤ rhoB ^ 246 := by unfold rhoB; positivity
        gcongr
      refine h1.trans ?_
      have hz : (2 : ℝ) ^ (-442 : Int) / (2 : ℝ) ^ 256 * (2 : ℝ) ^ 628 = (2 : ℝ) ^ (-70 : Int) := by
        rw [← zpow_natCast (2 : ℝ) 256, ← zpow_natCast (2 : ℝ) 628,
            ← zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1
      have heq : (2 / (2 : ℝ) ^ 256) * 1539 * ((126842 / 100000 : ℝ) * (2 : ℝ) ^ (-442 : Int)) / (1 - rhoB / qL) * (2 : ℝ) ^ 628 =
          (2 * 1539 * (126842 / 100000 : ℝ) / (1 - rhoB / qL)) * ((2 : ℝ) ^ (-442 : Int) / (2 : ℝ) ^ 256 * (2 : ℝ) ^ 628) := by
        generalize (2 : ℝ) ^ 628 = P628; ring
      rw [heq, hz]; unfold rhoB qL; norm_num
    have hnn_sum : ∀ (f : Nat → ℝ) (S : Finset Nat), (∀ i ∈ S, 0 ≤ f i) → 0 ≤ ∑ i ∈ S, f i :=
      fun _ _ hf => Finset.sum_nonneg hf
    have hq1_nn : 0 ≤ ∑ q ∈ Finset.range 7, q1 ^ q := hnn_sum _ _ (fun _ _ => by dsimp [q1]; unfold rhoEO0 rhoF; positivity)
    have hr1_nn : 0 ≤ ∑ r ∈ Finset.Icc 1 5, r1 ^ r := hnn_sum _ _ (fun _ _ => by dsimp [r1]; unfold rhoEO0 rhoF; positivity)
    have hq2_nn : 0 ≤ ∑ q ∈ Finset.range 7, q2 ^ q := hnn_sum _ _ (fun _ _ => by dsimp [q2]; unfold rhoF; positivity)
    have hr2_nn : 0 ≤ ∑ r ∈ Finset.Icc 1 5, r2 ^ r := hnn_sum _ _ (fun _ _ => by dsimp [r2]; unfold rhoF; positivity)
    have hq3a_nn : 0 ≤ ∑ q ∈ Finset.range 7, q3a ^ q := hnn_sum _ _ (fun _ _ => by dsimp [q3a]; unfold rhoB; positivity)
    have hr3a_nn : 0 ≤ ∑ r ∈ Finset.Icc 1 5, r3a ^ r := hnn_sum _ _ (fun _ _ => by dsimp [r3a]; unfold rhoB; positivity)
    have hq3b_nn : 0 ≤ ∑ q ∈ Finset.range 7, q3b ^ q := hnn_sum _ _ (fun _ _ => by dsimp [q3b]; unfold rhoB; positivity)
    have hr3b_nn : 0 ≤ ∑ r ∈ Finset.Icc 1 5, r3b ^ r := hnn_sum _ _ (fun _ _ => by dsimp [r3b]; unfold rhoB; positivity)
    have hterm1 : b1 * (∑ q ∈ Finset.range 7, q1 ^ q) * (∑ r ∈ Finset.Icc 1 5, r1 ^ r) ≤ (61 / 10 ^ 15) * 115 * (36 / 10) :=
      mul_le_mul (mul_le_mul hb1 hG1q hq1_nn (by norm_num)) hG1r hr1_nn (by norm_num)
    have hterm2 : b2 * (∑ q ∈ Finset.range 7, q2 ^ q) * (∑ r ∈ Finset.Icc 1 5, r2 ^ r) ≤ (255 / 10 ^ 15) * 64 * (34 / 10) :=
      mul_le_mul (mul_le_mul hb2 hG2q hq2_nn (by norm_num)) hG2r hr2_nn (by norm_num)
    have hterm3a : b3a * (∑ q ∈ Finset.range 7, q3a ^ q) * (∑ r ∈ Finset.Icc 1 5, r3a ^ r) ≤ (56 / 10 ^ 16) * 243 * 35 :=
      mul_le_mul (mul_le_mul hb3a hG3aq hq3a_nn (by norm_num)) hG3ar hr3a_nn (by norm_num)
    have hterm3b : b3b * (∑ q ∈ Finset.range 7, q3b ^ q) * (∑ r ∈ Finset.Icc 1 5, r3b ^ r) ≤ (1 / 10 ^ 16) * 2 * 4 :=
      mul_le_mul (mul_le_mul hb3b hG3bq hq3b_nn (by norm_num)) hG3br hr3b_nn (by norm_num)
    have htot_inner :
        b1 * (∑ q ∈ Finset.range 7, q1 ^ q) * (∑ r ∈ Finset.Icc 1 5, r1 ^ r) +
        b2 * (∑ q ∈ Finset.range 7, q2 ^ q) * (∑ r ∈ Finset.Icc 1 5, r2 ^ r) +
        b3a * (∑ q ∈ Finset.range 7, q3a ^ q) * (∑ r ∈ Finset.Icc 1 5, r3a ^ r) +
        b3b * (∑ q ∈ Finset.range 7, q3b ^ q) * (∑ r ∈ Finset.Icc 1 5, r3b ^ r) ≤ 130 / 10 ^ 12 :=
      (add_le_add (add_le_add (add_le_add hterm1 hterm2) hterm3a) hterm3b).trans (by norm_num)
    calc (∑ q ∈ Finset.range 7, ∑ r ∈ Finset.Icc 1 5, ((Bad485_k0 (5 * q + r)).card : ℝ))
        ≤ (2 : ℝ) ^ 256 * _ := hsum_qr
      _ ≤ (2 : ℝ) ^ 256 * (130 / 10 ^ 12) := mul_le_mul_of_nonneg_left htot_inner (by positivity)
      _ = (130 / 10 ^ 12 : ℝ) * (2 : ℝ) ^ 256 := by ring
  -- Piece 3: `k0 ≥ 36` (`≤ 15 / 10^12 * 2^256`)
  have htail : (Stail.card : ℝ) ≤ (15 / 10 ^ 12 : ℝ) * (2 : ℝ) ^ 256 := by
    have ht := tail_k0_ge_36
    have h1 : (1 : ℝ) / (2 : ℝ) ^ 36 ≤ 15 / 10 ^ 12 := by norm_num
    calc (Stail.card : ℝ) ≤ (2 : ℝ) ^ 256 / (2 : ℝ) ^ 36 := ht
      _ = (1 / (2 : ℝ) ^ 36) * (2 : ℝ) ^ 256 := by ring
      _ ≤ (15 / 10 ^ 12) * (2 : ℝ) ^ 256 := mul_le_mul_of_nonneg_right h1 (by positivity)
  have hfinal_const : (1 / 10 ^ 13 : ℝ) + (130 / 10 ^ 12) + (15 / 10 ^ 12) ≤ 15 / 10 ^ 11 := by norm_num
  have h256_pos : (0 : ℝ) ≤ (2 : ℝ) ^ 256 := by positivity
  have htot := add_le_add (add_le_add h0_bound hmid_bound) htail
  rw [← add_mul, ← add_mul] at htot
  exact hcard_total.trans (htot.trans (mul_le_mul_of_nonneg_right hfinal_const h256_pos))

end
end ShorECDLP.Entrant.SkywalkTail485


/-! ### Part 3: Schedule25 geometry, coefficients, specialization, and physical program (Wave 8B) -/

namespace ShorECDLP.Entrant.Schedule25
open Quantum Challenge Secp256k1 AndGadget WEXCredit ConditionalCatalyst ApproximatePhase34
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open Single Single.Distribution Width16Schedule.Specialization
open SineCircuit SineBounds Trim18 Schedule26Bridge ApproxCat
open scoped BigOperators
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
attribute [local irreducible] List.ofFn fourierOutcomes Single.fixedEntry

local instance bodyInst25 : Single.WindowBody := PathShare.bodyCF
local instance resourceInst25 : Single.ProducerResources bodyInst25 :=
  Single.ProducerResources.ofBody PathShare.bodyCF
    (by change resetWires.Nodup; exact resetWires_nodup)
    (by change (0 : Wire) ∈ resetWires; decide)
    (by change (1 : Wire) ∈ resetWires; decide)

inductive Digit25 where
  | left18 (index : Fin 11)
  | left19 (index : Fin 2)
  | right17 (index : Fin 10)
  | right18 (index : Fin 2)

def Digit25.k : Digit25 → Nat
  | .left18 _ => 17
  | .left19 _ => 18
  | .right17 _ => 16
  | .right18 _ => 17

def Digit25.width (d : Digit25) : Nat := d.k + 1

def Digit25.bank (d : Digit25) : List Wire := GenericW.bankW d.k

def Digit25.tof : Digit25 → Nat
  | .left18 _ => 2319661
  | .left19 _ => 2483757
  | .right17 _ => 2171700
  | .right18 _ => 2253875

def Digit25.isRight : Digit25 → Bool
  | .left18 _ | .left19 _ => false
  | .right17 _ | .right18 _ => true

def Digit25.exponent : Digit25 → Nat
  | .left18 j => 218 - 18 * j.val
  | .left19 j => 19 - 19 * j.val
  | .right17 j => 189 - 17 * j.val
  | .right18 j => 18 - 18 * j.val

def Digit25.base (Q : Point) : Digit25 → Point
  | .left18 _ => G
  | .left19 _ => G
  | .right17 _ => Q
  | .right18 _ => Q

theorem Digit25.k_lo (d : Digit25) : 16 ≤ d.k := by cases d <;> dsimp only [Digit25.k] <;> decide
theorem Digit25.k_hi (d : Digit25) : d.k ≤ 18 := by cases d <;> dsimp only [Digit25.k] <;> decide
theorem Digit25.width_ge1 (d : Digit25) : 1 ≤ d.width := by cases d <;> dsimp only [Digit25.width, Digit25.k] <;> decide

def leftDigits25 : List Digit25 :=
  List.ofFn (fun j : Fin 11 => .left18 j) ++ List.ofFn (fun j : Fin 2 => .left19 j)

def rightDigits25 : List Digit25 :=
  List.ofFn (fun j : Fin 10 => .right17 j) ++ List.ofFn (fun j : Fin 2 => .right18 j)

def rightHeadDigit : Digit25 := .right17 ⟨0, by decide⟩

def rightTailDigits25 : List Digit25 :=
  List.ofFn (fun j : Fin 9 => .right17 ⟨j.val + 1, by omega⟩) ++ List.ofFn (fun j : Fin 2 => .right18 j)

theorem rightDigits25_cons : rightDigits25 = rightHeadDigit :: rightTailDigits25 := by
  simp [rightDigits25, rightHeadDigit, rightTailDigits25, List.ofFn_succ]

def initialCoefficients25 (a : Nat) : PointCoeff :=
  coefficients (oddScalar 236 a) 0

def signedCoefficients25 (w : Digit25) (a : Nat) : PointCoeff :=
  match w with
  | .left18 _ => coefficients (oddScalar w.exponent a) 0
  | .left19 _ => coefficients (oddScalar w.exponent a) 0
  | .right17 _ => coefficients 0 (oddScalar w.exponent a)
  | .right18 _ => coefficients 0 (oddScalar w.exponent a)

/-- `3,407,872 = 524,288 + 11 * 131,072 + 2 * 262,144 + 10 * 65,536 + 2 * 131,072` raw rows.
The first `2,490,368` rows (`First20Signed` + all `13` left body windows) have `b = 0` and freeze during specialization. -/
def coefficientAt25 (i : Fin 3407872) : PointCoeff :=
  if i.val < 524288 then initialCoefficients25 i.val
  else if i.val < 1966080 then
    coefficients (oddScalar (218 - 18 * ((i.val - 524288) / 131072)) ((i.val - 524288) % 131072)) 0
  else if i.val < 2490368 then
    coefficients (oddScalar (19 - 19 * ((i.val - 1966080) / 262144)) ((i.val - 1966080) % 262144)) 0
  else if i.val < 3145728 then
    coefficients 0 (oddScalar (189 - 17 * ((i.val - 2490368) / 65536)) ((i.val - 2490368) % 65536))
  else
    coefficients 0 (oddScalar (18 - 18 * ((i.val - 3145728) / 131072)) ((i.val - 3145728) % 131072))

def firstRow25 (a : Fin 524288) : Fin 3407872 := ⟨a.val, by omega⟩

def row25 : (d : Digit25) → Fin (2 ^ d.k) → Fin 3407872
  | .left18 j, a => ⟨524288 + j.val * 131072 + a.val, by have := a.isLt; dsimp [Digit25.k] at this; omega⟩
  | .left19 j, a => ⟨1966080 + j.val * 262144 + a.val, by have := a.isLt; dsimp [Digit25.k] at this; omega⟩
  | .right17 j, a => ⟨2490368 + j.val * 65536 + a.val, by have := a.isLt; dsimp [Digit25.k] at this; omega⟩
  | .right18 j, a => ⟨3145728 + j.val * 131072 + a.val, by have := a.isLt; dsimp [Digit25.k] at this; omega⟩

theorem coefficientAt25_first (a : Fin 524288) :
    coefficientAt25 (firstRow25 a) = initialCoefficients25 a.val := by
  simp [coefficientAt25, firstRow25, a.isLt]

theorem coefficientAt25_row (w : Digit25) (a : Fin (2 ^ w.k)) :
    coefficientAt25 (row25 w a) = signedCoefficients25 w a.val := by
  cases w with
  | left18 j =>
    have haLt : a.val < 131072 := a.isLt
    have h0 : ¬ (row25 (.left18 j) a).val < 524288 := by simp only [row25]; omega
    have h1 : (row25 (.left18 j) a).val < 1966080 := by simp only [row25]; omega
    have hj : ((row25 (.left18 j) a).val - 524288) / 131072 = j.val := by simp only [row25]; omega
    have ha : ((row25 (.left18 j) a).val - 524288) % 131072 = a.val := by simp only [row25]; omega
    simp [coefficientAt25, h0, h1, hj, ha, signedCoefficients25, Digit25.exponent]
  | left19 j =>
    have haLt : a.val < 262144 := a.isLt
    have h0 : ¬ (row25 (.left19 j) a).val < 524288 := by simp only [row25]; omega
    have h1 : ¬ (row25 (.left19 j) a).val < 1966080 := by simp only [row25]; omega
    have h2 : (row25 (.left19 j) a).val < 2490368 := by simp only [row25]; omega
    have hj : ((row25 (.left19 j) a).val - 1966080) / 262144 = j.val := by simp only [row25]; omega
    have ha : ((row25 (.left19 j) a).val - 1966080) % 262144 = a.val := by simp only [row25]; omega
    simp [coefficientAt25, h0, h1, h2, hj, ha, signedCoefficients25, Digit25.exponent]
  | right17 j =>
    have haLt : a.val < 65536 := a.isLt
    have h0 : ¬ (row25 (.right17 j) a).val < 524288 := by simp only [row25]; omega
    have h1 : ¬ (row25 (.right17 j) a).val < 1966080 := by simp only [row25]; omega
    have h2 : ¬ (row25 (.right17 j) a).val < 2490368 := by simp only [row25]; omega
    have h3 : (row25 (.right17 j) a).val < 3145728 := by simp only [row25]; omega
    have hj : ((row25 (.right17 j) a).val - 2490368) / 65536 = j.val := by simp only [row25]; omega
    have ha : ((row25 (.right17 j) a).val - 2490368) % 65536 = a.val := by simp only [row25]; omega
    simp [coefficientAt25, h0, h1, h2, h3, hj, ha, signedCoefficients25, Digit25.exponent]
  | right18 j =>
    have haLt : a.val < 131072 := a.isLt
    have h0 : ¬ (row25 (.right18 j) a).val < 524288 := by simp only [row25]; omega
    have h1 : ¬ (row25 (.right18 j) a).val < 1966080 := by simp only [row25]; omega
    have h2 : ¬ (row25 (.right18 j) a).val < 2490368 := by simp only [row25]; omega
    have h3 : ¬ (row25 (.right18 j) a).val < 3145728 := by simp only [row25]; omega
    have hj : ((row25 (.right18 j) a).val - 3145728) / 131072 = j.val := by simp only [row25]; omega
    have ha : ((row25 (.right18 j) a).val - 3145728) % 131072 = a.val := by simp only [row25]; omega
    simp [coefficientAt25, h0, h1, h2, h3, hj, ha, signedCoefficients25, Digit25.exponent]

def initialPositivePoint25 (a : Nat) : Point :=
  oddScalar 236 a • G

def initialPoint25 (_Q : Point) (v : Nat) : Point :=
  Width16Schedule.increment G 20 236 v

def positivePoint25 (Q : Point) (w : Digit25) (a : Nat) : Point :=
  oddScalar w.exponent a • w.base Q

theorem initialCoefficients25_point (Q : Point) (hQ : order • Q = 0) (a : Nat) :
    constantPoint Q (initialCoefficients25 a) = initialPositivePoint25 a := by
  unfold initialCoefficients25 initialPositivePoint25
  simpa using coefficients_point (oddScalar 236 a) 0 Q hQ

theorem initialPositivePoint25_ne_zero (a : Nat) (ha : a < 524288) :
    initialPositivePoint25 a ≠ 0 := by
  have hl : 1048575 < order := by norm_num [order]
  exact Width16Schedule.odd_scalar_ne_zero G generator_nsmul_eq_zero G_ne_zero 236 a (by omega)

theorem signedCoefficients25_point (Q : Point) (hQ : order • Q = 0) (w : Digit25) (a : Nat) :
    constantPoint Q (signedCoefficients25 w a) = positivePoint25 Q w a := by
  cases w <;> simp [signedCoefficients25, coefficients_point _ _ Q hQ, positivePoint25, Digit25.base]

theorem positivePoint25_ne_zero (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : Digit25) (a : Nat) (ha : a < 2 ^ w.k) : positivePoint25 Q w a ≠ 0 := by
  have hp : w.base Q ≠ 0 := by cases w <;> [exact G_ne_zero; exact G_ne_zero; exact hn; exact hn]
  have hr : order • w.base Q = 0 := by
    cases w <;> [exact generator_nsmul_eq_zero; exact generator_nsmul_eq_zero; exact hQ; exact hQ]
  have hpow : 2 ^ w.k ≤ 262144 := by cases w <;> dsimp only [Digit25.k] <;> decide
  have hl : 524287 < order := by norm_num [order]
  exact Width16Schedule.odd_scalar_ne_zero (w.base Q) hr hp w.exponent a (by omega)

/-- Specialization table retaining only the `917,504` `Q`-rows (`10*65,536 + 2*131,072`) plus one zero sentinel (`917,505 ≤ 983,040`). -/
@[irreducible] def retainedAt25 (i : Fin 917505) : PointCoeff :=
  if h : i.val < 917504 then coefficientAt25 ⟨2490368 + i.val, by omega⟩
  else coefficients 0 0

def sentinel25 : ConstantBit 917505 := ⟨⟨917504, by decide +kernel⟩, .x, 0⟩

def classify25 (r : ConstantBit 3407872) : Bool ⊕ ConstantBit 917505 :=
  if h : r.point.val < 2490368 then .inl (readConstant coefficientAt25 (0 : Point) r)
  else .inr ⟨⟨r.point.val - 2490368, by have := r.point.isLt; omega⟩, r.field, r.bit⟩

theorem fixed25_b_zero (i : Fin 3407872) (hhi : i.val < 2490368) :
    (coefficientAt25 i).b.val = 0 := by
  unfold coefficientAt25
  split_ifs <;> simp [initialCoefficients25, coefficients]

theorem sentinel25_false (Q : Point) : readConstant retainedAt25 Q sentinel25 = false := by
  simp [sentinel25, retainedAt25, readConstant, coefficients, constantPoint, fieldValue, pointCoordinates]

theorem retained25_agree (Q : Point) (r : ConstantBit 3407872) :
    readConstant coefficientAt25 Q r = (classify25 r).elim id (readConstant retainedAt25 Q) := by
  unfold classify25
  split
  next h =>
    simp only [Sum.elim_inl, id_eq]
    exact generator_only_readConstant coefficientAt25 r (fixed25_b_zero _ h) Q 0
  next h =>
    simp only [Sum.elim_inr, readConstant]
    have hh : r.point.val - 2490368 < 917504 := by have := r.point.isLt; omega
    have he : 2490368 + (r.point.val - 2490368) = r.point.val := by omega
    simp only [retainedAt25, hh, ↓reduceDIte, he]

def rawLimits25 : Limits := { officialLimits with coefficientRows := 3407872 }

def specializeProgram25 {s e : Nat} (p : Straight 3407872 s e) : Straight 917505 s e :=
  specialize classify25 sentinel25 p

def specializeEntry25 (e : StraightEntry)
    (he : e.coefficients = List.ofFn coefficientAt25) : StraightEntry :=
  Single.fixedEntry retainedAt25
    (specializeProgram25 (Width16Schedule.canonicalProgram coefficientAt25 e he))

theorem specializeEntry25_certificate (e : StraightEntry)
    (he : e.coefficients = List.ofFn coefficientAt25)
    (layout : DecodeLayout) (bounds : Bounds) (h : Certificate rawLimits25 layout e bounds) :
    Certificate officialLimits layout (specializeEntry25 e he) bounds := by
  have hc := Width16Schedule.canonical_certificate coefficientAt25 e he rawLimits25 layout bounds h
  exact Width16Schedule.fixed_specialize_certificate coefficientAt25 retainedAt25 classify25 sentinel25
    sentinel25_false retained25_agree (Width16Schedule.canonicalProgram coefficientAt25 e he)
    officialLimits layout bounds hc (by change 917505 ≤ 983040; omega)

/-! ### Physical windows (`GenericW` + `First20Signed`), models, and program (`1,612` qubits) -/

attribute [local irreducible] First20Signed.program Single.axis resetProgram
  GenericW.compiledProgramW GenericW.compiledProgramFnW
  GenericW.compiledProgram16 GenericW.compiledProgram17 GenericW.compiledProgram18
  GenericW.compiledProgramTrunc16 GenericW.compiledProgramTrunc17
  GenericW.arithSpecFull GenericW.arithSpecTrunc96
  GenericW.fixupSpec16 GenericW.fixupSpec17 GenericW.fixupSpec18
  GenericW.compiledFixup16 GenericW.compiledFixup9 GenericW.rawFixup16 GenericW.rawFixup9
  GenericW.compact1612 Readout5.suffix5
  LocalFour.compileLower CatAxis.axisCat ConditionalCatalyst.compile
  AndGadget.added AndGadget.residue

def top10Left : List Wire := First20Signed.bits.drop 10
def top10Right : List Wire := (GenericW.bankW 16).drop 7

private theorem range1610_sub_1612 : List.range 1610 ⊆ List.range 1612 := fun _ h =>
  List.mem_range.mpr ((List.mem_range.mp h).trans (by decide))

theorem top10Left_length : top10Left.length = 10 := by decide
theorem top10Left_nodup : top10Left.Nodup := by decide
theorem top10Left_sub_bits : top10Left ⊆ First20Signed.bits := List.drop_subset 10 First20Signed.bits
theorem top10Left_sub_range : top10Left ⊆ List.range 1612 :=
  (top10Left_sub_bits.trans First20Signed.bits_subset_range).trans range1610_sub_1612

theorem bankW_sub_range {k : Nat} (hk : k ≤ 18) : GenericW.bankW k ⊆ List.range 1612 := by
  intro v hv
  have hb := GenericW.mem_bankW.mp hv
  rw [List.mem_range]; dsimp only [Wire] at *; omega

theorem bankW_not_point {k : Nat} (hk : k ≤ 18) : ∀ v ∈ GenericW.bankW k, v ∉ pointLogicalWires := by
  intro v hv hm
  have hb := GenericW.mem_bankW.mp hv
  simp only [pointLogicalWires, pointCorrectionX, pointCorrectionYInf, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_range'_1] at hm
  dsimp only [Wire] at *; omega

private theorem wire1_not_point : (1 : Wire) ∉ pointLogicalWires := by
  intro hm
  simp only [pointLogicalWires, pointCorrectionX, pointCorrectionYInf, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_range'_1] at hm
  dsimp only [Wire] at *; omega

private theorem wire836_not_point : (836 : Wire) ∉ pointLogicalWires := by
  intro hm
  simp only [pointLogicalWires, pointCorrectionX, pointCorrectionYInf, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_range'_1] at hm
  dsimp only [Wire] at *; omega

private theorem wire838_mem_point : (838 : Wire) ∈ pointLogicalWires := by
  simp only [pointLogicalWires, pointCorrectionX, pointCorrectionYInf, List.mem_append, List.mem_cons,
    or_true, true_or]

theorem top10Right_length : top10Right.length = 10 := by decide
theorem top10Right_nodup : top10Right.Nodup := by decide
theorem top10Right_sub_bank : top10Right ⊆ GenericW.bankW 16 := List.drop_subset 7 (GenericW.bankW 16)
theorem top10Right_sub_range : top10Right ⊆ List.range 1612 :=
  top10Right_sub_bank.trans (bankW_sub_range (by decide))

private theorem wire01_not_first20Bits :
    (0 : Wire) ∉ First20Signed.bits ∧ (1 : Wire) ∉ First20Signed.bits := by
  constructor <;> intro hm <;>
    (have := First20Signed.bits_subset_drop01 hm; simp only [List.mem_range'_1] at this; omega)

private theorem wire836_not_first20Bits : (836 : Wire) ∉ First20Signed.bits := by decide
private theorem wire1_not_bankW {k : Nat} : (1 : Wire) ∉ GenericW.bankW k := fun hm => by
  have hb := GenericW.mem_bankW.mp hm; dsimp only [Wire] at *; omega

def first20RawWin : Window 3407872 := First20Signed.windowGeneric firstRow25

def wideCoeffs25 (d : Digit25) : Fin (2 ^ d.k) → PointCoeff := fun a => signedCoefficients25 d a.val

theorem wide25_nonzero (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (d : Digit25)
    (a : Fin (2 ^ d.k)) : constantPoint Q (wideCoeffs25 d a) ≠ 0 := by
  rw [wideCoeffs25, signedCoefficients25_point Q hQ]
  exact positivePoint25_ne_zero Q hQ hn d a.val a.isLt

private theorem cFirst20_exists :
    ∃ n : Nat, n = AndGadget.Lowered.finish (LocalFour.compileLower 0 1 (first20RawWin.program 0) 0 Fin.elim0) :=
  ⟨_, rfl⟩
def cFirst20 : Nat := Classical.choose cFirst20_exists
theorem cFirst20_eq :
    cFirst20 = AndGadget.Lowered.finish (LocalFour.compileLower 0 1 (first20RawWin.program 0) 0 Fin.elim0) :=
  Classical.choose_spec cFirst20_exists

private theorem cBody16_exists :
    ∃ n : Nat, n = LocalFour.CatProg.finish (GenericW.compiledProgramFnW GenericW.arithSpecFull GenericW.fixupSpec16 0) := ⟨_, rfl⟩
def cBody16 : Nat := Classical.choose cBody16_exists
theorem cBody16_eq :
    cBody16 = LocalFour.CatProg.finish (GenericW.compiledProgramFnW GenericW.arithSpecFull GenericW.fixupSpec16 0) :=
  Classical.choose_spec cBody16_exists
theorem cBody16_le : cBody16 ≤ 3850000 := cBody16_eq ▸ GenericW.compiledRec16_bound

private theorem cBody17_exists :
    ∃ n : Nat, n = LocalFour.CatProg.finish (GenericW.compiledProgramFnW GenericW.arithSpecFull GenericW.fixupSpec17 0) := ⟨_, rfl⟩
def cBody17 : Nat := Classical.choose cBody17_exists
theorem cBody17_eq :
    cBody17 = LocalFour.CatProg.finish (GenericW.compiledProgramFnW GenericW.arithSpecFull GenericW.fixupSpec17 0) :=
  Classical.choose_spec cBody17_exists
theorem cBody17_le : cBody17 ≤ 4000000 := cBody17_eq ▸ GenericW.compiledRec17_bound

private theorem cBody18_exists :
    ∃ n : Nat, n = LocalFour.CatProg.finish (GenericW.compiledProgramFnW GenericW.arithSpecFull GenericW.fixupSpec18 0) := ⟨_, rfl⟩
def cBody18 : Nat := Classical.choose cBody18_exists
theorem cBody18_eq :
    cBody18 = LocalFour.CatProg.finish (GenericW.compiledProgramFnW GenericW.arithSpecFull GenericW.fixupSpec18 0) :=
  Classical.choose_spec cBody18_exists
theorem cBody18_le : cBody18 ≤ 4350000 := cBody18_eq ▸ GenericW.compiledRec18_bound

private theorem cBody16Trunc_exists :
    ∃ n : Nat, n = LocalFour.CatProg.finish (GenericW.compiledProgramFnW GenericW.arithSpecTrunc96 GenericW.fixupSpec16 0) := ⟨_, rfl⟩
def cBody16Trunc : Nat := Classical.choose cBody16Trunc_exists
theorem cBody16Trunc_eq :
    cBody16Trunc = LocalFour.CatProg.finish (GenericW.compiledProgramFnW GenericW.arithSpecTrunc96 GenericW.fixupSpec16 0) :=
  Classical.choose_spec cBody16Trunc_exists
theorem cBody16Trunc_le : cBody16Trunc ≤ 3730000 := cBody16Trunc_eq ▸ GenericW.compiledRecTrunc16_bound

private theorem cBody17Trunc_exists :
    ∃ n : Nat, n = LocalFour.CatProg.finish (GenericW.compiledProgramFnW GenericW.arithSpecTrunc96 GenericW.fixupSpec17 0) := ⟨_, rfl⟩
def cBody17Trunc : Nat := Classical.choose cBody17Trunc_exists
theorem cBody17Trunc_eq :
    cBody17Trunc = LocalFour.CatProg.finish (GenericW.compiledProgramFnW GenericW.arithSpecTrunc96 GenericW.fixupSpec17 0) :=
  Classical.choose_spec cBody17Trunc_exists
theorem cBody17Trunc_le : cBody17Trunc ≤ 3880000 := cBody17Trunc_eq ▸ GenericW.compiledRecTrunc17_bound

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

def first20Core (start : Nat) : Straight 3407872 start (start + cFirst20) :=
  ((literalProgram [.X 836]).append
    (castFinish (first20Cat_finish_eq start)
      (LocalFour.compileLower 0 1 (first20RawWin.program 0) start Fin.elim0).program)).append
    (literalProgram [.X 836])

def first20CatWin : Window 3407872 :=
  ⟨First20Signed.bits.reverse, cFirst20,
    fun start => (ConditionalCatalyst.compile 1 (literalProgram (sineFromPlus top10Left))).append
      (first20Core start)⟩

def bodyCatWin : Digit25 → Window 3407872
  | .left18 j =>
    ⟨(GenericW.bankW 17).reverse, cBody17,
      fun start => castFinish (congrArg (start + ·) cBody17_eq.symm)
        (reindexStraight (row25 (.left18 j))
          (relabelStraight GenericW.compact1612 (GenericW.compiledProgram17 start)))⟩
  | .left19 j =>
    ⟨(GenericW.bankW 18).reverse, cBody18,
      fun start => castFinish (congrArg (start + ·) cBody18_eq.symm)
        (reindexStraight (row25 (.left19 j))
          (relabelStraight GenericW.compact1612 (GenericW.compiledProgram18 start)))⟩
  | .right17 j =>
    ⟨(GenericW.bankW 16).reverse, cBody16Trunc,
      fun start => castFinish (congrArg (start + ·) cBody16Trunc_eq.symm)
        (reindexStraight (row25 (.right17 j))
          (relabelStraight GenericW.compact1612 (GenericW.compiledProgramTrunc16 start)))⟩
  | .right18 j =>
    ⟨(GenericW.bankW 17).reverse, cBody17Trunc,
      fun start => castFinish (congrArg (start + ·) cBody17Trunc_eq.symm)
        (reindexStraight (row25 (.right18 j))
          (relabelStraight GenericW.compact1612 (GenericW.compiledProgramTrunc17 start)))⟩

theorem bodyCatWin_wires (d : Digit25) : (bodyCatWin d).wires = d.bank.reverse := by
  cases d <;> rfl

def rightHeadCatWin : Window 3407872 :=
  ⟨(GenericW.bankW 16).reverse, cBody16Trunc,
    fun start => (ConditionalCatalyst.compile 1 (literalProgram (sineFromPlus top10Right))).append
      ((bodyCatWin rightHeadDigit).program start)⟩

def leftWins25Cat : List (Window 3407872) := first20CatWin :: leftDigits25.map bodyCatWin
def rightWins25Cat : List (Window 3407872) := rightHeadCatWin :: rightTailDigits25.map bodyCatWin

def leftMeta25Cat : List (Nat × Nat) :=
  (cFirst20, 20) :: List.replicate 11 (cBody17, 18) ++ List.replicate 2 (cBody18, 19)

def rightMeta25Cat : List (Nat × Nat) :=
  List.replicate 10 (cBody16Trunc, 17) ++ List.replicate 2 (cBody17Trunc, 18)

theorem leftWins25Cat_meta : leftWins25Cat.map (fun w => (w.count, w.wires.length)) = leftMeta25Cat := by
  simp only [leftWins25Cat, leftMeta25Cat, leftDigits25, List.map_cons, List.map_append,
    List.map_map, Function.comp_def, first20CatWin, List.length_reverse, First20Signed.bits_length]
  simp [List.ofFn_succ, List.replicate, bodyCatWin, GenericW.bankW_length]

theorem rightWins25Cat_meta : rightWins25Cat.map (fun w => (w.count, w.wires.length)) = rightMeta25Cat := by
  simp only [rightWins25Cat, rightMeta25Cat, rightTailDigits25, List.map_cons, List.map_append,
    List.map_map, Function.comp_def, rightHeadCatWin, List.length_reverse, GenericW.bankW_length]
  simp [List.ofFn_succ, List.replicate, bodyCatWin, GenericW.bankW_length]

theorem leftWins25Cat_count_eq :
    axisCount leftWins25Cat = cFirst20 + 20 + 11 * (cBody17 + 18) + 2 * (cBody18 + 19) := by
  rw [← recordCount_eq_axisCount, leftWins25Cat_meta]
  simp only [leftMeta25Cat, List.replicate, List.cons_append, List.nil_append, recordCount]
  omega

theorem rightWins25Cat_count_eq :
    axisCount rightWins25Cat = 10 * (cBody16Trunc + 17) + 2 * (cBody17Trunc + 18) := by
  rw [← recordCount_eq_axisCount, rightWins25Cat_meta]
  simp only [rightMeta25Cat, List.replicate, List.cons_append, List.nil_append, recordCount]
  omega

def leftPositions25Cat : List Nat := positions leftMeta25Cat 0
def rightPositions25Cat : List Nat := positions rightMeta25Cat (axisCount leftWins25Cat)

theorem leftPositions25Cat_length : leftPositions25Cat.length = 256 := by
  simp only [leftPositions25Cat, positions_length, leftMeta25Cat, List.replicate,
    List.cons_append, List.nil_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  rfl

theorem rightPositions25Cat_length : rightPositions25Cat.length = 206 := by
  simp only [rightPositions25Cat, positions_length, rightMeta25Cat, List.replicate,
    List.cons_append, List.nil_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  rfl

def trialPositions25Cat : TrialPositions params256 where
  left := ⟨leftPositions25Cat.toArray, by
    simpa only [List.size_toArray, params256] using leftPositions25Cat_length⟩
  right := ⟨rightPositions25Cat.toArray, by
    simpa only [List.size_toArray, params256] using rightPositions25Cat_length⟩

theorem leftPositions25Cat_bound (i : Nat) (hi : i ∈ trialPositions25Cat.left.toList) :
    i < axisCount leftWins25Cat := by
  have hi' : i ∈ leftPositions25Cat := by simpa [trialPositions25Cat] using hi
  have hb := positions_bounds leftMeta25Cat 0 i hi'
  have hr : recordCount leftMeta25Cat = axisCount leftWins25Cat := by
    rw [← leftWins25Cat_meta, recordCount_eq_axisCount]
  omega

theorem rightPositions25Cat_bound (i : Nat) (hi : i ∈ trialPositions25Cat.right.toList) :
    i < axisCount leftWins25Cat + axisCount rightWins25Cat := by
  have hi' : i ∈ rightPositions25Cat := by simpa [trialPositions25Cat] using hi
  have hb := positions_bounds rightMeta25Cat (axisCount leftWins25Cat) i hi'
  have hr : recordCount rightMeta25Cat = axisCount rightWins25Cat := by
    rw [← rightWins25Cat_meta, recordCount_eq_axisCount]
  omega

def cursor25Cat : Nat := axisCount leftWins25Cat + axisCount rightWins25Cat + resetWires.length
def cursor25Mid : Nat := cursor25Cat + 3586

def leftFinPositions25Cat : List (Fin cursor25Cat) :=
  trialPositions25Cat.left.toList.attach.map fun i =>
    ⟨i.val, (leftPositions25Cat_bound i.val i.property).trans_le (by unfold cursor25Cat; omega)⟩

theorem leftFinPositions25Cat_length : leftFinPositions25Cat.length = 256 := by
  simp [leftFinPositions25Cat, params256]

def leftBits25Cat : Vector (Fin cursor25Cat) 256 :=
  Vector.ofFn fun i => leftFinPositions25Cat[i.val]'(by rw [leftFinPositions25Cat_length]; exact i.isLt)

theorem leftBits25Cat_vals : leftBits25Cat.map Fin.val = trialPositions25Cat.left := by
  apply Vector.ext; intro i hi
  simp [leftBits25Cat, leftFinPositions25Cat]; rfl

def rightFinPositions25Cat : List (Fin cursor25Cat) :=
  trialPositions25Cat.right.toList.attach.map fun i =>
    ⟨i.val, (rightPositions25Cat_bound i.val i.property).trans_le (by unfold cursor25Cat; omega)⟩

theorem rightFinPositions25Cat_length : rightFinPositions25Cat.length = 206 := by
  simp [rightFinPositions25Cat, params256]

def rightBits25Cat : Vector (Fin cursor25Cat) 206 :=
  Vector.ofFn fun i => rightFinPositions25Cat[i.val]'(by rw [rightFinPositions25Cat_length]; exact i.isLt)

theorem rightBits25Cat_vals : rightBits25Cat.map Fin.val = trialPositions25Cat.right := by
  apply Vector.ext; intro i hi
  simp [rightBits25Cat, rightFinPositions25Cat]; rfl

def rightBits25Mid : Vector (Fin cursor25Mid) 206 :=
  rightBits25Cat.map fun i => ⟨i.val, i.isLt.trans_le (by unfold cursor25Mid; omega)⟩

def readoutL25 : Straight 3407872 cursor25Cat cursor25Mid :=
  castFinish (by unfold cursor25Mid; omega) (Readout5.suffix5 3407872 cursor25Cat 256 leftBits25Cat)

def readoutR25 : Straight 3407872 cursor25Mid (cursor25Mid + 2886) :=
  castFinish (by omega) (Readout5.suffix5 3407872 cursor25Mid 206 rightBits25Mid)

def readout25Cat : Straight 3407872 cursor25Cat (cursor25Cat + 6472) :=
  castFinish (by unfold cursor25Mid; omega) (readoutL25.append readoutR25)

/-- Frame-free physical program: starts directly on `ket zeroBasisState`, prepares catalyst wire `1`,
    runs left and right catalyst axes, and resets `resetWires`. -/
def program25Cat : Straight 3407872 0 cursor25Cat :=
  AndGadget.literals (Catalyst.prepare 1)
    (castFinish (show 0 + axisCount leftWins25Cat + axisCount rightWins25Cat + resetWires.length = cursor25Cat by unfold cursor25Cat; omega)
      (((CatAxis.axisCat 1 leftWins25Cat 0 List.nil).append
        (CatAxis.axisCat 1 rightWins25Cat (0 + axisCount leftWins25Cat) List.nil)).append
          (resetProgram 3407872 (0 + axisCount leftWins25Cat + axisCount rightWins25Cat) resetWires)))

def fullProgram25Cat : Straight 3407872 0 (cursor25Cat + 6472) :=
  program25Cat.append readout25Cat

def rawEntry25Cat : StraightEntry := Single.fixedEntry coefficientAt25 fullProgram25Cat

def rawLayout25Cat : DecodeLayout :=
  ⟨.wrappedShift, params256,
    offsets13.map (fun p => ⟨Readout5.wordAt5 leftBits25Cat p.1, Readout5.wordAt5 rightBits25Mid p.2⟩), by
    simp only [List.length_map, offsets13_length]; decide⟩

/-! ### Ideal window models on `root := zeroBasisState` -/

def SignedWeights25 (Q P : Point) : List Digit25 → Prop
  | List.nil => True
  | w :: ws => w.base Q = P ∧ w.exponent = (ws.map Digit25.width).sum ∧ SignedWeights25 Q P ws

theorem left_signed_weights25 (Q : Point) : SignedWeights25 Q G leftDigits25 := by
  norm_num [leftDigits25, List.ofFn_succ, List.ofFn_zero, List.cons_append, List.nil_append,
    SignedWeights25, Digit25.exponent, Digit25.base, Digit25.width, Digit25.k]

theorem right_signed_weights25 (Q : Point) : SignedWeights25 Q Q rightDigits25 := by
  norm_num [rightDigits25, List.ofFn_succ, List.ofFn_zero, List.cons_append, List.nil_append,
    SignedWeights25, Digit25.exponent, Digit25.base, Digit25.width, Digit25.k]

theorem modelWeights25 {n : Nat} {read : ConstantBit n → Bool}
    (Q P : Point) (hr : order • P = 0) (f : Digit25 → WindowModel read)
    (hwidth : ∀ w, (f w).physical.wires.length = w.width)
    (hpoint : ∀ w v, (f w).point v = Width16Schedule.increment (w.base Q) w.width w.exponent v)
    (hbias : ∀ w, (f w).bias = offsetScalar w.width w.exponent • w.base Q)
    (ws : List Digit25) (hw : SignedWeights25 Q P ws) : ModelWeights P (ws.map f) := by
  induction ws with
  | nil => trivial
  | cons w ws ih =>
    constructor
    · intro v
      have hwidths : ((ws.map f).map (fun x => x.physical.wires.length)).sum =
          (ws.map Digit25.width).sum := by simp only [List.map_map, Function.comp_def, hwidth]
      rw [hwidths, ← hw.2.1, hpoint, hbias, hw.1]
      exact Width16Schedule.increment_offset_ge1 P hr w.width w.exponent v w.width_ge1
    · exact ih hw.2.2

theorem first20_signed_eq (Q : Point) (hQ : order • Q = 0) (v : Nat) (hv : v < 1048576) :
    First20Signed.signedPoint (fun a => coefficientAt25 (firstRow25 a)) Q v = initialPoint25 Q v := by
  unfold First20Signed.signedPoint First20Signed.tablePoint
  have hpos (a : Nat) :
      constantPoint Q (coefficientAt25 (firstRow25 ⟨a % 524288, Nat.mod_lt _ (by decide +kernel)⟩)) =
        (2 * (a % 524288) + 1) • ((halfOrder * 2 ^ 236) • G) := by
    rw [coefficientAt25_first, initialCoefficients25_point Q hQ]
    unfold initialPositivePoint25 Single.oddScalar
    rw [Nat.mul_assoc, Nat.mul_comm (2 ^ 236) halfOrder, mul_smul]
  have hs := Width16Actual.signed_magnitude ((halfOrder * 2 ^ 236) • G) 524288 v (by decide) (by omega)
  have hinc : Width16Schedule.increment G 20 236 v =
      (2 * (v : Int) - 2 * (524288 : Nat) + 1) • ((halfOrder * 2 ^ 236) • G) := by
    unfold Width16Schedule.increment
    rw [show (2 : Int) ^ 20 = 2 * (524288 : Nat) by norm_num]
  rw [initialPoint25, hinc, ← hs]
  simp only [hpos, show 524288 - 1 = 524287 from rfl]

theorem first20Win_law : WindowLaw coefficientAt25 first20RawWin
    (First20Signed.update initialPoint25) First20Signed.Input := by
  apply First20Signed.window_law_generic
  · intro Q hQ _ a
    rw [coefficientAt25_first, initialCoefficients25_point Q hQ]
    exact initialPositivePoint25_ne_zero a.val a.isLt
  · intro Q hQ _ v hv
    exact first20_signed_eq Q hQ v hv

theorem signedDeltaW_eq (Q : Point) (hQ : order • Q = 0) (d : Digit25) (bs : BasisState) :
    GenericW.signedDeltaW d.k (wideCoeffs25 d) Q bs =
      Width16Schedule.increment (d.base Q) d.width d.exponent (GenericW.rawBankW d.k bs) := by
  have hsplit := GenericW.rawBankW_split d.k bs
  have hltK := GenericW.rawW_lt d.k bs
  have hltW : GenericW.rawBankW d.k bs < 2 * 2 ^ d.k := by
    cases hb : bs (GenericW.signBitW d.k) <;> simp [hb] at hsplit <;> omega
  have hpos (a : Nat) :
      constantPoint Q (wideCoeffs25 d (GenericW.rowsW d.k a)) =
        (2 * (a % 2 ^ d.k) + 1) • ((halfOrder * 2 ^ d.exponent) • d.base Q) := by
    rw [wideCoeffs25, GenericW.rowsW, signedCoefficients25_point Q hQ]
    unfold positivePoint25 Single.oddScalar
    rw [Nat.mul_assoc, Nat.mul_comm (2 ^ d.exponent) halfOrder, mul_smul]
  have hs := Width16Actual.signed_magnitude ((halfOrder * 2 ^ d.exponent) • d.base Q) (2 ^ d.k)
    (GenericW.rawBankW d.k bs) (by positivity) hltW
  have hpowZ : (2 : Int) ^ d.width = 2 * ((2 ^ d.k : Nat) : Int) := by
    have hnat : 2 ^ d.width = 2 * 2 ^ d.k := by rw [Digit25.width, pow_succ']
    exact_mod_cast hnat
  have hinc : Width16Schedule.increment (d.base Q) d.width d.exponent (GenericW.rawBankW d.k bs) =
      (2 * ((GenericW.rawBankW d.k bs : Nat) : Int) - 2 * ((2 ^ d.k : Nat) : Int) + 1) •
        ((halfOrder * 2 ^ d.exponent) • d.base Q) := by
    unfold Width16Schedule.increment; rw [hpowZ]
  rw [hinc, ← hs, GenericW.signedDeltaW]
  cases hb : bs (GenericW.signBitW d.k) with
  | false =>
    simp only [hb, Bool.toNat_false, mul_zero, add_zero] at hsplit
    have hlt : GenericW.rawBankW d.k bs < 2 ^ d.k := by omega
    have hmod : (2 ^ d.k - 1 - GenericW.rawW d.k bs) % 2 ^ d.k = 2 ^ d.k - 1 - GenericW.rawW d.k bs :=
      Nat.mod_eq_of_lt (by omega)
    simp only [Bool.false_eq_true, ↓reduceIte, hlt, hltK, hpos, hsplit, hmod]
  | true =>
    simp only [hb, Bool.toNat_true, mul_one] at hsplit
    have hge : ¬ GenericW.rawBankW d.k bs < 2 ^ d.k := by omega
    have hsub : GenericW.rawBankW d.k bs - 2 ^ d.k = GenericW.rawW d.k bs := by omega
    have hmod : GenericW.rawW d.k bs % 2 ^ d.k = GenericW.rawW d.k bs := Nat.mod_eq_of_lt hltK
    simp only [↓reduceIte, hge, hpos, hsub, hmod]

theorem signedDeltaW_phaseWord (Q : Point) (hQ : order • Q = 0) (d : Digit25)
    (input : List Bool) (hlen : input.length = d.width) (s : BasisState) :
    GenericW.signedDeltaW d.k (wideCoeffs25 d) Q (phaseWordState d.bank input s) =
      Width16Schedule.increment (d.base Q) d.width d.exponent (boolWordToNat input) := by
  rw [signedDeltaW_eq Q hQ d]
  have hr : GenericW.rawBankW d.k (phaseWordState d.bank input s) = boolWordToNat input := by
    rw [GenericW.rawBankW, WEX.tableAddress_word]
    exact congrArg boolWordToNat
      (phaseWordState_word d.bank (GenericW.bankW_nodup d.k) input (by simpa [Digit25.bank, Digit25.width, GenericW.bankW_length] using hlen) s)
  rw [hr]

def first20Model (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    WindowModel (readConstant coefficientAt25 Q) where
  physical := ⟨First20Signed.bits.reverse, 0, fun _ => .done⟩
  point := initialPoint25 Q
  bias := offsetScalar 20 236 • G
  ideal := (Finsupp.lmapDomain ℂ ℂ (First20Signed.update initialPoint25 Q)).comp
    (Quantum.run (sineFromPlus top10Left))
  valid := fun _ => False
  nodup := List.nodup_reverse.mpr First20Signed.bits_nodup
  coherent := fun _ _ => ⟨[1], .cons (fun _ h => False.elim h) .nil, by simp⟩

def bodyModel (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (d : Digit25) :
    WindowModel (readConstant coefficientAt25 Q) where
  physical := ⟨d.bank.reverse, 0, fun _ => .done⟩
  point := Width16Schedule.increment (d.base Q) d.width d.exponent
  bias := offsetScalar d.width d.exponent • d.base Q
  ideal := Finsupp.lmapDomain ℂ ℂ (GenericW.updateW d.k (wideCoeffs25 d) Q)
  valid := fun _ => False
  nodup := List.nodup_reverse.mpr (GenericW.bankW_nodup d.k)
  coherent := fun _ _ => ⟨[1], .cons (fun _ h => False.elim h) .nil, by simp⟩

def rightHeadModel (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    WindowModel (readConstant coefficientAt25 Q) where
  physical := ⟨rightHeadDigit.bank.reverse, 0, fun _ => .done⟩
  point := (bodyModel Q hQ hn rightHeadDigit).point
  bias := (bodyModel Q hQ hn rightHeadDigit).bias
  ideal := (Finsupp.lmapDomain ℂ ℂ (GenericW.updateW rightHeadDigit.k (wideCoeffs25 rightHeadDigit) Q)).comp
    (Quantum.run (sineFromPlus top10Right))
  valid := fun _ => False
  nodup := List.nodup_reverse.mpr (GenericW.bankW_nodup 16)
  coherent := fun _ _ => ⟨[1], .cons (fun _ h => False.elim h) .nil, by simp⟩

theorem zeroBasisState_clean20 : Clean First20Signed.bits zeroBasisState := fun _ _ => rfl

theorem pointWrite_zero_cleanW {k : Nat} (hk : k ≤ 18) (P : Point) :
    Clean (GenericW.bankW k) (pointWrite P zeroBasisState) := fun w hw => by
  rw [pointWrite_frame P zeroBasisState w (bankW_not_point hk w hw)]; rfl

theorem first20Model_rule (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    WindowedFirstRule zeroBasisState (ket zeroBasisState) (first20Model Q hQ hn) := by
  refine ⟨by change First20Signed.bits.reverse.length ≥ 10; simp [First20Signed.bits_length], ?_⟩
  intro prior output
  change fourierBranch .inverse First20Signed.bits.reverse prior output
      (Finsupp.lmapDomain ℂ ℂ (First20Signed.update initialPoint25 Q)
        (Quantum.run (sineFromPlus top10Left)
          (Quantum.run (First20Signed.bits.reverse.reverse.map Gate.H) (ket zeroBasisState)))) = _
  rw [List.reverse_reverse]
  have hdrop : First20Signed.bits.drop (First20Signed.bits.length - 10) = top10Left := by
    simp [top10Left, First20Signed.bits_length]
  have hsb := sineFromPlus_bank First20Signed.bits (by simp [First20Signed.bits_length])
    First20Signed.bits_nodup zeroBasisState zeroBasisState_clean20
  rw [hdrop] at hsb
  rw [hsb, map_smul, map_smul, stateLinear_list_sum, stateLinear_list_sum, List.map_map, List.map_map]
  simp only [Function.comp_def, map_smul, List.length_reverse]
  congr 1; apply congrArg List.sum; apply List.map_congr_left
  intro input hi
  have hlen : input.length = First20Signed.bits.length := (fourierOutcomes_mem _ _).mp hi
  have hupd : First20Signed.update initialPoint25 Q (phaseWordState First20Signed.bits input zeroBasisState) =
      pointWrite (initialPoint25 Q (boolWordToNat input)) (phaseWordState First20Signed.bits input zeroBasisState) := by
    unfold First20Signed.update
    rw [WEX.tableAddress_word, phaseWordState_word First20Signed.bits First20Signed.bits_nodup input hlen]
  have hket : Finsupp.lmapDomain ℂ ℂ (First20Signed.update initialPoint25 Q)
      (ket (phaseWordState First20Signed.bits input zeroBasisState)) =
      ket (pointWrite (initialPoint25 Q (boolWordToNat input))
        (phaseWordState First20Signed.bits input zeroBasisState)) := by
    simp only [ket, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, hupd]
  rw [hket, fourierBranch_ket,
    Mixed.branchCoeff_amplitude' .inverse First20Signed.bits.reverse (List.nodup_reverse.mpr First20Signed.bits_nodup)]
  have hmap : First20Signed.bits.reverse.map
      (pointWrite (initialPoint25 Q (boolWordToNat input))
        (phaseWordState First20Signed.bits input zeroBasisState)) = input.reverse := by
    rw [List.map_reverse]; congr 1
    have hf : First20Signed.bits.map
        (pointWrite (initialPoint25 Q (boolWordToNat input))
          (phaseWordState First20Signed.bits input zeroBasisState)) =
        First20Signed.bits.map (phaseWordState First20Signed.bits input zeroBasisState) := by
      apply List.map_congr_left; intro v hv
      exact pointWrite_frame _ _ _ (First20Signed.bits_not_point v hv)
    rw [hf]
    exact phaseWordState_word First20Signed.bits First20Signed.bits_nodup input hlen zeroBasisState
  have hclr : fourierClear First20Signed.bits.reverse
      (pointWrite (initialPoint25 Q (boolWordToNat input))
        (phaseWordState First20Signed.bits input zeroBasisState)) =
      pointWrite (initialPoint25 Q (boolWordToNat input)) zeroBasisState :=
    clear_assigned_point First20Signed.bits input zeroBasisState zeroBasisState_clean20
      (fun v hv hp => First20Signed.bits_not_point v hv hp) (initialPoint25 Q (boolWordToNat input))
  rw [hmap, hclr, smul_smul]; rfl

theorem bodyModel_rule (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (d : Digit25) :
    PointRule zeroBasisState (bodyModel Q hQ hn d) := by
  intro prior output P
  have hnot := bankW_not_point d.k_hi
  have hnd := GenericW.bankW_nodup d.k
  have hblen : d.bank.length = d.width := GenericW.bankW_length d.k
  change fourierBranch .inverse d.bank.reverse prior output
      (Finsupp.lmapDomain ℂ ℂ (GenericW.updateW d.k (wideCoeffs25 d) Q)
        (Quantum.run (d.bank.reverse.reverse.map Gate.H) (ket (pointWrite P zeroBasisState)))) = _
  rw [List.reverse_reverse, phaseHadamards_uniform d.bank hnd _ (pointWrite_zero_cleanW d.k_hi P)]
  simp only [phaseUniformSum, map_smul, stateLinear_list_sum, List.map_map, Function.comp_def, List.length_reverse]
  rw [show (bodyModel Q hQ hn d).physical.wires.length = d.bank.length by simp [bodyModel]]
  congr 1; apply congrArg List.sum; apply List.map_congr_left
  intro input hi
  have hlen : input.length = d.width := by simpa [hblen] using (fourierOutcomes_mem _ _).mp hi
  have hcoords : pointStateCoordinates (phaseWordState d.bank input (pointWrite P zeroBasisState)) =
      fig14PointEncoding P := by
    rw [phaseWordState_pointWrite d.bank hnot, pointWrite_coordinates]
  have hupd : GenericW.updateW d.k (wideCoeffs25 d) Q (phaseWordState d.bank input (pointWrite P zeroBasisState)) =
      pointWrite (P + (bodyModel Q hQ hn d).point (boolWordToNat input))
        (phaseWordState d.bank input (pointWrite P zeroBasisState)) := by
    rw [GenericW.updateW_eq hcoords, signedDeltaW_phaseWord Q hQ d input hlen]; rfl
  rw [Mixed.lmap_ket', hupd, fourierBranch_ket,
    Mixed.branchCoeff_amplitude' .inverse d.bank.reverse (List.nodup_reverse.mpr hnd)]
  have hmap : d.bank.reverse.map
      (pointWrite (P + (bodyModel Q hQ hn d).point (boolWordToNat input))
        (phaseWordState d.bank input (pointWrite P zeroBasisState))) = input.reverse := by
    rw [List.map_reverse]; congr 1
    have hf : d.bank.map
        (pointWrite (P + (bodyModel Q hQ hn d).point (boolWordToNat input))
          (phaseWordState d.bank input (pointWrite P zeroBasisState))) =
        d.bank.map (phaseWordState d.bank input (pointWrite P zeroBasisState)) := by
      apply List.map_congr_left; intro v hv; exact pointWrite_frame _ _ _ (hnot v hv)
    rw [hf]
    exact phaseWordState_word d.bank hnd input (by simpa [hblen] using hlen) _
  have hclr : fourierClear d.bank.reverse
      (pointWrite (P + (bodyModel Q hQ hn d).point (boolWordToNat input))
        (phaseWordState d.bank input (pointWrite P zeroBasisState))) =
      pointWrite (P + (bodyModel Q hQ hn d).point (boolWordToNat input)) zeroBasisState := by
    rw [clear_assigned_point d.bank input (pointWrite P zeroBasisState) (pointWrite_zero_cleanW d.k_hi P)
      hnot, pointWrite_overwrite]
  rw [hmap, hclr]

theorem rightHeadModel_rule (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    WindowedPointRule zeroBasisState (rightHeadModel Q hQ hn) := by
  have hnot := bankW_not_point (k := 16) (by decide)
  have hnd := GenericW.bankW_nodup 16
  refine ⟨by change (GenericW.bankW 16).reverse.length ≥ 10; simp [GenericW.bankW_length], ?_⟩
  intro prior output P
  change fourierBranch .inverse (GenericW.bankW 16).reverse prior output
      (Finsupp.lmapDomain ℂ ℂ (GenericW.updateW 16 (wideCoeffs25 rightHeadDigit) Q)
        (Quantum.run (sineFromPlus top10Right)
          (Quantum.run ((GenericW.bankW 16).reverse.reverse.map Gate.H) (ket (pointWrite P zeroBasisState))))) = _
  rw [List.reverse_reverse]
  have hdrop : (GenericW.bankW 16).drop ((GenericW.bankW 16).length - 10) = top10Right := by
    simp [top10Right, GenericW.bankW_length]
  have hsb := sineFromPlus_bank (GenericW.bankW 16) (by simp [GenericW.bankW_length]) hnd
    (pointWrite P zeroBasisState) (pointWrite_zero_cleanW (by decide) P)
  rw [hdrop] at hsb
  rw [hsb, map_smul, map_smul, stateLinear_list_sum, stateLinear_list_sum, List.map_map, List.map_map]
  simp only [Function.comp_def, map_smul, List.length_reverse]
  congr 1; apply congrArg List.sum; apply List.map_congr_left
  intro input hi
  have hlen : input.length = 17 := by simpa [GenericW.bankW_length] using (fourierOutcomes_mem _ _).mp hi
  have hcoords : pointStateCoordinates (phaseWordState (GenericW.bankW 16) input (pointWrite P zeroBasisState)) =
      fig14PointEncoding P := by
    rw [phaseWordState_pointWrite (GenericW.bankW 16) hnot, pointWrite_coordinates]
  have hupd : GenericW.updateW 16 (wideCoeffs25 rightHeadDigit) Q
        (phaseWordState (GenericW.bankW 16) input (pointWrite P zeroBasisState)) =
      pointWrite (P + (rightHeadModel Q hQ hn).point (boolWordToNat input))
        (phaseWordState (GenericW.bankW 16) input (pointWrite P zeroBasisState)) := by
    have hsd : GenericW.signedDeltaW 16 (wideCoeffs25 rightHeadDigit) Q
        (phaseWordState (GenericW.bankW 16) input (pointWrite P zeroBasisState)) =
        (rightHeadModel Q hQ hn).point (boolWordToNat input) :=
      signedDeltaW_phaseWord Q hQ rightHeadDigit input hlen (pointWrite P zeroBasisState)
    rw [GenericW.updateW_eq hcoords, hsd]
  rw [Mixed.lmap_ket', hupd, fourierBranch_ket,
    Mixed.branchCoeff_amplitude' .inverse (GenericW.bankW 16).reverse (List.nodup_reverse.mpr hnd)]
  have hmap : (GenericW.bankW 16).reverse.map
      (pointWrite (P + (rightHeadModel Q hQ hn).point (boolWordToNat input))
        (phaseWordState (GenericW.bankW 16) input (pointWrite P zeroBasisState))) = input.reverse := by
    rw [List.map_reverse]; congr 1
    have hf : (GenericW.bankW 16).map
        (pointWrite (P + (rightHeadModel Q hQ hn).point (boolWordToNat input))
          (phaseWordState (GenericW.bankW 16) input (pointWrite P zeroBasisState))) =
        (GenericW.bankW 16).map (phaseWordState (GenericW.bankW 16) input (pointWrite P zeroBasisState)) := by
      apply List.map_congr_left; intro v hv; exact pointWrite_frame _ _ _ (hnot v hv)
    rw [hf]
    exact phaseWordState_word (GenericW.bankW 16) hnd input (by simpa [GenericW.bankW_length] using hlen) _
  have hclr : fourierClear (GenericW.bankW 16).reverse
      (pointWrite (P + (rightHeadModel Q hQ hn).point (boolWordToNat input))
        (phaseWordState (GenericW.bankW 16) input (pointWrite P zeroBasisState))) =
      pointWrite (P + (rightHeadModel Q hQ hn).point (boolWordToNat input)) zeroBasisState := by
    rw [clear_assigned_point (GenericW.bankW 16) input (pointWrite P zeroBasisState) (pointWrite_zero_cleanW (by decide) P)
      hnot, pointWrite_overwrite]
  rw [hmap, hclr, smul_smul]; rfl

def leftModels25 (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    List (WindowModel (readConstant coefficientAt25 Q)) :=
  first20Model Q hQ hn :: leftDigits25.map (bodyModel Q hQ hn)

def rightModels25 (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    List (WindowModel (readConstant coefficientAt25 Q)) :=
  rightHeadModel Q hQ hn :: rightTailDigits25.map (bodyModel Q hQ hn)

theorem leftModels25_weights (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    ModelWeights G (leftModels25 Q hQ hn) := by
  constructor
  · intro v
    have hw : ((leftDigits25.map (bodyModel Q hQ hn)).map (fun x => x.physical.wires.length)).sum = 236 := by
      simp only [List.map_map, Function.comp_def, bodyModel, List.length_reverse, Digit25.bank, GenericW.bankW_length]
      simp [leftDigits25, List.ofFn_succ, Digit25.k]
    rw [hw]
    exact Width16Schedule.increment_offset_ge1 G generator_nsmul_eq_zero 20 236 v (by decide)
  · exact modelWeights25 Q G generator_nsmul_eq_zero (bodyModel Q hQ hn)
      (fun w => by simp [bodyModel, Digit25.bank, Digit25.width, GenericW.bankW_length])
      (fun _ _ => rfl) (fun _ => rfl) leftDigits25 (left_signed_weights25 Q)

theorem rightModels25_weights (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    ModelWeights Q (rightModels25 Q hQ hn) := by
  have hall := modelWeights25 Q Q hQ (bodyModel Q hQ hn)
    (fun w => by simp [bodyModel, Digit25.bank, Digit25.width, GenericW.bankW_length])
    (fun _ _ => rfl) (fun _ => rfl) rightDigits25 (right_signed_weights25 Q)
  rw [rightDigits25_cons, List.map_cons] at hall
  exact hall

/-! ### `ApproxCatWindow` instances (`first20`, `body`, `rightHead`) -/

def First20Input0 (s : BasisState) : Prop :=
  s 836 = false ∧ First20Signed.Input (s[836 ↦ true])

private theorem first20Input0_upd (s : BasisState) (w : Wire) (b : Bool)
    (hw : w ∈ First20Signed.bits) (hs : First20Input0 s) :
    First20Input0 (s[w ↦ b]) := by
  have hne : w ≠ 836 := fun e => wire836_not_first20Bits (e ▸ hw)
  refine ⟨by simp [upd, hne.symm, hs.1], ?_⟩
  have hsw : (s[w ↦ b])[836 ↦ true] = (s[836 ↦ true])[w ↦ b] := by
    funext u; by_cases hu : u = 836
    · subst hu; simp [upd, hne.symm]
    · by_cases huw : u = w <;> simp [upd, hu, huw, hne]
  rw [hsw]
  refine ⟨by simp [upd, hne.symm, hs.2.1], fun v hv hnb => ?_⟩
  have hvw : v ≠ w := fun e => hnb (e ▸ hw)
  simp only [upd, hvw, ↓reduceIte]
  exact hs.2.2 v hv hnb

private theorem zeroBasisState_first20Input0 : First20Input0 zeroBasisState :=
  ⟨rfl, by simp [upd], fun v hv _ => by simp [upd, hv, zeroBasisState]⟩

private theorem first20_input_clean01 (s : BasisState) (hs : First20Signed.Input s) :
    s 0 = false ∧ s 1 = false :=
  ⟨hs.2 0 (by decide) wire01_not_first20Bits.1, hs.2 1 (by decide) wire01_not_first20Bits.2⟩

theorem first20Core_wellFormed (start : Nat) : (first20Core start).WellFormed := by
  have hwfX : (literalProgram (n := 3407872) (s := start) [.X 836]).WellFormed :=
    literalProgram_wellFormed [.X 836] (fun g hg => by simp at hg; subst hg; trivial)
  have hwfX2 : (literalProgram (n := 3407872) (s := start + cFirst20) [.X 836]).WellFormed :=
    literalProgram_wellFormed [.X 836] (fun g hg => by simp at hg; subst hg; trivial)
  apply straight_append_wellFormed _ _ _ hwfX2
  apply straight_append_wellFormed _ _ hwfX
  rw [castFinish_wellFormed]
  have hsub := First20Signed.window_support_drop01 firstRow25 0
  have hf0 : Fresh 0 (first20RawWin.program 0) :=
    LocalFour.fresh_of_not_mem_straightWires _ _ (fun hm => by
      have := hsub hm; simp only [List.mem_range'_1] at this; omega)
  have hf1 : Fresh 1 (first20RawWin.program 0) :=
    LocalFour.fresh_of_not_mem_straightWires _ _ (fun hm => by
      have := hsub hm; simp only [List.mem_range'_1] at this; omega)
  exact LocalFour.compileLower_wellFormed 0 1 (first20RawWin.program 0) start Fin.elim0 hf0 hf1 (by decide)
    (First20Signed.window_wellFormed firstRow25 0)

private theorem boolWordToNat_injective : ∀ {a b : List Bool},
    a.length = b.length → boolWordToNat a = boolWordToNat b → a = b
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, hl, hv => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    simp only [boolWordToNat] at hv
    have hxy : x = y := by cases x <;> cases y <;> simp at hv ⊢ <;> omega
    subst hxy
    have hxs : boolWordToNat xs = boolWordToNat ys := by cases x <;> simp at hv <;> omega
    exact congrArg (x :: ·) (boolWordToNat_injective hl hxs)

private theorem list_sum_fourierOutcomes_eq_range (k : Nat) (f : Nat → ℝ) :
    ((fourierOutcomes k).map (fun b => f (boolWordToNat b))).sum =
      ∑ u ∈ Finset.range (2 ^ k), f u := by
  induction k generalizing f with
  | zero => simp [fourierOutcomes, boolWordToNat]
  | succ k ih =>
    simp only [fourierOutcomes, List.map_append, List.sum_append, List.map_map, Function.comp_def,
      boolWordToNat, Bool.toNat_false, Bool.toNat_true, zero_add]
    rw [ih (fun n => f (2 * n)), ih (fun n => f (1 + 2 * n))]
    have heven : ∑ u ∈ Finset.range (2 ^ k), f (2 * u) +
        ∑ u ∈ Finset.range (2 ^ k), f (1 + 2 * u) =
        ∑ u ∈ Finset.range (2 ^ (k + 1)), f u := by
      rw [pow_succ, mul_comm (2 ^ k) 2]
      clear ih
      induction (2 ^ k) with
      | zero => simp
      | succ m ihm =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Nat.mul_succ,
          Finset.sum_range_succ, Finset.sum_range_succ]
        rw [show 1 + 2 * m = 2 * m + 1 by omega]
        linarith
    exact heven

private theorem phaseWordState_agree : ∀ (ws : List Wire) (inp : List Bool) (s₁ s₂ : BasisState)
    (w : Wire), ws.length = inp.length → w ∈ ws →
    phaseWordState ws inp s₁ w = phaseWordState ws inp s₂ w
  | [], [], _, _, _, _, hw => by cases hw
  | u :: us, b :: bs, s₁, s₂, w, hl, hw => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    by_cases hwu : w ∈ us
    · exact phaseWordState_agree us bs (s₁[u ↦ b]) (s₂[u ↦ b]) w hl hwu
    · have hwe : w = u := by
        rcases List.mem_cons.mp hw with rfl | hm
        · rfl
        · exact absurd hm hwu
      subst hwe
      simp only [phaseWordState]
      rw [phaseWordState_frame us bs (s₁[w ↦ b]) w hwu,
          phaseWordState_frame us bs (s₂[w ↦ b]) w hwu]
      simp [upd]
  | _ :: _, [], _, _, _, hl, _ => by simp at hl
  | [], _ :: _, _, _, _, hl, _ => by simp at hl

private theorem pointWrite_agree_on_point (P : Point) (s₁ s₂ : BasisState) (w : Wire)
    (hw : w ∈ pointLogicalWires) : pointWrite P s₁ w = pointWrite P s₂ w := by
  have h1 := pointWrite_word P s₁
  have h2 := pointWrite_word P s₂
  have hmap : pointLogicalWires.map (pointWrite P s₁) = pointLogicalWires.map (pointWrite P s₂) :=
    h1.trans h2.symm
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
  have hgi := congrArg (fun l : List Bool => l[i]?) hmap
  simpa [List.getElem?_map, List.getElem?_eq_getElem hi] using hgi

private theorem surroundX836_catCoherent_aux {start fin : Nat}
    (read : ConstantBit 3407872 → Bool) (mid : Straight 3407872 start fin)
    (Q : Point) (history : Fin start → Bool)
    (hmid : LocalFour.CatCoherent 1 (mid.instantiate read history)
      (Finsupp.lmapDomain ℂ ℂ (First20Signed.update initialPoint25 Q)) First20Signed.Input) :
    LocalFour.CatCoherent 1
      ((((literalProgram (n := 3407872) (s := start) [.X 836]).append mid).append
        (literalProgram (n := 3407872) (s := fin) [.X 836])).instantiate read history)
      (Finsupp.lmapDomain ℂ ℂ (First20Signed.update initialPoint25 Q)) First20Input0 := by
  obtain ⟨cs, hal, hmass⟩ := hmid
  refine ⟨cs, ?_, hmass⟩
  have hlit_run (s : Nat) (h : Fin s → Bool) :
      ((literalProgram (n := 3407872) (s := s) [.X 836]).instantiate read h).run =
        [{ history := List.nil, kraus := Quantum.run [.X 836] }] := by
    rw [ChallengeMigration.literalProgram_run]
    change ([{ history := List.nil, kraus := LinearMap.id.comp (Quantum.run [.X 836]) }] : Instrument) = _
    simp
  rw [Single.append_run_history, Single.append_run_history, hlit_run]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_map, Function.comp_def]
  have hhist0 : Single.historyAfter start history List.nil = history := by
    funext i; simp [Single.historyAfter, List.ofFn_getElem]
  rw [hhist0]
  have hfm : ∀ (f : InstrumentBranch → InstrumentBranch) (l : List InstrumentBranch),
      l.flatMap (fun a => [f a]) = l.map f := by
    intro f l; induction l with | nil => rfl | cons x xs ih => simp [ih]
  have hrun_eq :
      ((mid.instantiate read history).run.map
        (fun b => ({ history := List.nil, kraus := Quantum.run [.X 836] } : InstrumentBranch).seq b)).flatMap
        (fun a => ((literalProgram (n := 3407872) (s := fin) [.X 836]).instantiate
          read (Single.historyAfter fin history a.history)).run.map a.seq) =
      (mid.instantiate read history).run.map
        (fun b => (({ history := List.nil, kraus := Quantum.run [.X 836] } : InstrumentBranch).seq b).seq
          { history := List.nil, kraus := Quantum.run [.X 836] }) := by
    rw [List.flatMap_map]
    simp only [hlit_run, List.map_cons, List.map_nil]
    exact hfm _ _
  rw [hrun_eq, List.forall₂_map_left_iff]
  refine hal.imp (fun b c hb s hs => ?_)
  change Quantum.run ([.X 836] : Circuit) (b.kraus (Quantum.run ([.X 836] : Circuit) (LocalFour.Prep 1 (ket s)))) = _
  rw [LocalFour.prep_circuit 1 ([.X 836] : Circuit) (by decide) (ket s)]
  have hx1 : Quantum.run ([.X 836] : Circuit) (ket s) = ket (s[836 ↦ true]) := by
    rw [Quantum.run_singleton, applyGate_X_ket, hs.1]; rfl
  rw [hx1, hb (s[836 ↦ true]) hs.2, map_smul, LocalFour.prep_circuit 1 ([.X 836] : Circuit) (by decide)]
  rw [Mixed.lmap_ket', Mixed.lmap_ket']
  have haddr : tableAddressValue First20Signed.bits (s[836 ↦ true]) = tableAddressValue First20Signed.bits s :=
    WEX.tableAddressValue_congr _ _ _ (fun w hw => by
      have hne : w ≠ 836 := fun e => wire836_not_first20Bits (e ▸ hw)
      simp [upd, hne])
  have h836_np : (836 : Wire) ∉ pointLogicalWires := wire836_not_point
  have h836_upd : First20Signed.update initialPoint25 Q (s[836 ↦ true]) 836 = true := by
    unfold First20Signed.update
    rw [pointWrite_frame _ _ 836 h836_np]
    simp [upd]
  have hx2 : Quantum.run ([.X 836] : Circuit) (ket (First20Signed.update initialPoint25 Q (s[836 ↦ true]))) =
      ket (First20Signed.update initialPoint25 Q s) := by
    rw [Quantum.run_singleton, applyGate_X_ket, h836_upd, Bool.not_true]
    apply congrArg ket; funext w
    unfold First20Signed.update; rw [haddr]
    by_cases hw : w = 836
    · subst hw; rw [upd_same, pointWrite_frame _ _ 836 h836_np, hs.1]
    · simp only [upd, hw, ↓reduceIte]
      by_cases hp : w ∈ pointLogicalWires
      · exact pointWrite_agree_on_point _ _ _ w hp
      · rw [pointWrite_frame _ _ w hp, pointWrite_frame _ _ w hp]; simp [upd, hw]
  rw [hx2]

theorem first20Core_catCoherent (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (start : Nat) (history : Fin start → Bool) :
    LocalFour.CatCoherent 1 ((first20Core start).instantiate (readConstant coefficientAt25 Q) history)
      (Finsupp.lmapDomain ℂ ℂ (First20Signed.update initialPoint25 Q)) First20Input0 := by
  have hsub := First20Signed.window_support_drop01 firstRow25 0
  have hf0 : Fresh 0 (first20RawWin.program 0) :=
    LocalFour.fresh_of_not_mem_straightWires _ _ (fun hm => by
      have := hsub hm; simp only [List.mem_range'_1] at this; omega)
  have hf1 : Fresh 1 (first20RawWin.program 0) :=
    LocalFour.fresh_of_not_mem_straightWires _ _ (fun hm => by
      have := hsub hm; simp only [List.mem_range'_1] at this; omega)
  have hlo := LocalFour.compileLower_catCoherent 0 1 (first20RawWin.program 0) start Fin.elim0
    (readConstant coefficientAt25 Q) Fin.elim0 history (fun i => Fin.elim0 i)
    (First20Signed.window_wellFormed firstRow25 0) hf0 hf1 (by decide)
    _ First20Signed.Input first20_input_clean01 (first20Win_law Q hQ hn 0 Fin.elim0)
  unfold first20Core
  exact surroundX836_catCoherent_aux (readConstant coefficientAt25 Q)
    (castFinish (first20Cat_finish_eq start) (LocalFour.compileLower 0 1 (first20RawWin.program 0) start Fin.elim0).program)
    Q history (by rw [castFinish_instantiate]; exact hlo)

theorem bodyCatWin_wellFormed (d : Digit25) (start : Nat) : ((bodyCatWin d).program start).WellFormed := by
  cases d with
  | left18 j =>
    change (castFinish _ (reindexStraight _ (relabelStraight _ (GenericW.compiledProgram17 start)))).WellFormed
    rw [castFinish_wellFormed]
    exact (reindexStraight_wellFormed _ _).mpr ((relabelStraight_wellFormed _ _).mpr (GenericW.compiled17_wellFormed start))
  | left19 j =>
    change (castFinish _ (reindexStraight _ (relabelStraight _ (GenericW.compiledProgram18 start)))).WellFormed
    rw [castFinish_wellFormed]
    exact (reindexStraight_wellFormed _ _).mpr ((relabelStraight_wellFormed _ _).mpr (GenericW.compiled18_wellFormed start))
  | right17 j =>
    change (castFinish _ (reindexStraight _ (relabelStraight _ (GenericW.compiledProgramTrunc16 start)))).WellFormed
    rw [castFinish_wellFormed]
    exact (reindexStraight_wellFormed _ _).mpr ((relabelStraight_wellFormed _ _).mpr (GenericW.compiledTrunc16_wellFormed start))
  | right18 j =>
    change (castFinish _ (reindexStraight _ (relabelStraight _ (GenericW.compiledProgramTrunc17 start)))).WellFormed
    rw [castFinish_wellFormed]
    exact (reindexStraight_wellFormed _ _).mpr ((relabelStraight_wellFormed _ _).mpr (GenericW.compiledTrunc17_wellFormed start))

def Digit25.goodPred (Q : Point) (d : Digit25) : BasisState → Prop :=
  if d.isRight then GenericW.GoodW96 d.k (wideCoeffs25 d) Q
  else GenericW.GoodW d.k (wideCoeffs25 d) Q

def first20ApproxWin (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    ApproxCatWindow 1 (readConstant coefficientAt25 Q) where
  model := first20Model Q hQ hn
  catPhys := first20CatWin
  pre := sineFromPlus top10Left
  core := first20Core
  prog_eq := fun _ => rfl
  pre_noY := fun hm => wire01_not_first20Bits.2 (top10Left_sub_bits (sineFromPlus_wires top10Left top10Left_length hm))
  pre_wf := sineFromPlus_wellFormed top10Left top10Left_length top10Left_nodup
  core_ideal := Finsupp.lmapDomain ℂ ℂ (First20Signed.update initialPoint25 Q)
  ideal_eq := rfl
  wires_eq := rfl
  noY := fun hm => wire01_not_first20Bits.2 (List.mem_reverse.mp hm)
  goodPred := First20Input0
  catCoherent := first20Core_catCoherent Q hQ hn
  core_idealY := fun ψ hψ => by
    refine Support.linear _ _ _ (fun s hs => ?_) ψ hψ
    rw [Mixed.lmap_ket']; apply supportedOn_ket
    unfold First20Signed.update; rw [pointWrite_frame _ _ 1 wire1_not_point]; exact hs
  core_wf := first20Core_wellFormed

def bodyApproxWin (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (d : Digit25) :
    ApproxCatWindow 1 (readConstant coefficientAt25 Q) where
  model := bodyModel Q hQ hn d
  catPhys := bodyCatWin d
  pre := List.nil
  core := (bodyCatWin d).program
  prog_eq := fun _ => by rw [CatAxis.compile_literalProgram_eq]; rfl
  pre_noY := by simp [circuitWires]
  pre_wf := fun g hg => by cases hg
  core_ideal := Finsupp.lmapDomain ℂ ℂ (GenericW.updateW d.k (wideCoeffs25 d) Q)
  ideal_eq := by simp [bodyModel, Quantum.run]
  wires_eq := bodyCatWin_wires d
  noY := fun hm => wire1_not_bankW (List.mem_reverse.mp hm)
  goodPred := d.goodPred Q
  catCoherent := fun start history => by
    cases d with
    | left18 j =>
      change LocalFour.CatCoherent 1
        ((castFinish (congrArg (start + ·) cBody17_eq.symm)
          (reindexStraight (row25 (.left18 j))
            (relabelStraight GenericW.compact1612 (GenericW.compiledProgram17 start)))).instantiate
              (readConstant coefficientAt25 Q) history)
        (Finsupp.lmapDomain ℂ ℂ (GenericW.updateW 17 (wideCoeffs25 (.left18 j)) Q))
        (GenericW.GoodW 17 (wideCoeffs25 (.left18 j)) Q)
      rw [castFinish_instantiate, reindexStraight_instantiate,
        readConstant_reindex (row25 (.left18 j)) (wideCoeffs25 (.left18 j)) coefficientAt25 Q
          (fun a => coefficientAt25_row (.left18 j) a)]
      exact GenericW.compiled17_packed_coherent (wideCoeffs25 (.left18 j)) Q
        (wide25_nonzero Q hQ hn (.left18 j)) start history
    | left19 j =>
      change LocalFour.CatCoherent 1
        ((castFinish (congrArg (start + ·) cBody18_eq.symm)
          (reindexStraight (row25 (.left19 j))
            (relabelStraight GenericW.compact1612 (GenericW.compiledProgram18 start)))).instantiate
              (readConstant coefficientAt25 Q) history)
        (Finsupp.lmapDomain ℂ ℂ (GenericW.updateW 18 (wideCoeffs25 (.left19 j)) Q))
        (GenericW.GoodW 18 (wideCoeffs25 (.left19 j)) Q)
      rw [castFinish_instantiate, reindexStraight_instantiate,
        readConstant_reindex (row25 (.left19 j)) (wideCoeffs25 (.left19 j)) coefficientAt25 Q
          (fun a => coefficientAt25_row (.left19 j) a)]
      exact GenericW.compiled18_packed_coherent (wideCoeffs25 (.left19 j)) Q
        (wide25_nonzero Q hQ hn (.left19 j)) start history
    | right17 j =>
      change LocalFour.CatCoherent 1
        ((castFinish (congrArg (start + ·) cBody16Trunc_eq.symm)
          (reindexStraight (row25 (.right17 j))
            (relabelStraight GenericW.compact1612 (GenericW.compiledProgramTrunc16 start)))).instantiate
              (readConstant coefficientAt25 Q) history)
        (Finsupp.lmapDomain ℂ ℂ (GenericW.updateW 16 (wideCoeffs25 (.right17 j)) Q))
        (GenericW.GoodW96 16 (wideCoeffs25 (.right17 j)) Q)
      rw [castFinish_instantiate, reindexStraight_instantiate,
        readConstant_reindex (row25 (.right17 j)) (wideCoeffs25 (.right17 j)) coefficientAt25 Q
          (fun a => coefficientAt25_row (.right17 j) a)]
      exact GenericW.compiledTrunc16_packed_coherent (wideCoeffs25 (.right17 j)) Q
        (wide25_nonzero Q hQ hn (.right17 j)) start history
    | right18 j =>
      change LocalFour.CatCoherent 1
        ((castFinish (congrArg (start + ·) cBody17Trunc_eq.symm)
          (reindexStraight (row25 (.right18 j))
            (relabelStraight GenericW.compact1612 (GenericW.compiledProgramTrunc17 start)))).instantiate
              (readConstant coefficientAt25 Q) history)
        (Finsupp.lmapDomain ℂ ℂ (GenericW.updateW 17 (wideCoeffs25 (.right18 j)) Q))
        (GenericW.GoodW96 17 (wideCoeffs25 (.right18 j)) Q)
      rw [castFinish_instantiate, reindexStraight_instantiate,
        readConstant_reindex (row25 (.right18 j)) (wideCoeffs25 (.right18 j)) coefficientAt25 Q
          (fun a => coefficientAt25_row (.right18 j) a)]
      exact GenericW.compiledTrunc17_packed_coherent (wideCoeffs25 (.right18 j)) Q
        (wide25_nonzero Q hQ hn (.right18 j)) start history
  core_idealY := fun ψ hψ => by
    refine Support.linear _ _ _ (fun s hs => ?_) ψ hψ
    rw [Mixed.lmap_ket']; apply supportedOn_ket
    unfold GenericW.updateW
    split_ifs
    · rw [pointWrite_frame _ _ 1 wire1_not_point]; exact hs
    · exact hs
  core_wf := bodyCatWin_wellFormed d

def rightHeadApproxWin (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    ApproxCatWindow 1 (readConstant coefficientAt25 Q) where
  model := rightHeadModel Q hQ hn
  catPhys := rightHeadCatWin
  pre := sineFromPlus top10Right
  core := (bodyCatWin rightHeadDigit).program
  prog_eq := fun _ => rfl
  pre_noY := fun hm => wire1_not_bankW (top10Right_sub_bank (sineFromPlus_wires top10Right top10Right_length hm))
  pre_wf := sineFromPlus_wellFormed top10Right top10Right_length top10Right_nodup
  core_ideal := Finsupp.lmapDomain ℂ ℂ (GenericW.updateW rightHeadDigit.k (wideCoeffs25 rightHeadDigit) Q)
  ideal_eq := rfl
  wires_eq := rfl
  noY := fun hm => wire1_not_bankW (List.mem_reverse.mp hm)
  goodPred := GenericW.GoodW96 rightHeadDigit.k (wideCoeffs25 rightHeadDigit) Q
  catCoherent := (bodyApproxWin Q hQ hn rightHeadDigit).catCoherent
  core_idealY := (bodyApproxWin Q hQ hn rightHeadDigit).core_idealY
  core_wf := bodyCatWin_wellFormed rightHeadDigit

def leftRestApprox25 (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    List (ApproxCatWindow 1 (readConstant coefficientAt25 Q)) :=
  leftDigits25.map (bodyApproxWin Q hQ hn)

def leftApprox25 (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    List (ApproxCatWindow 1 (readConstant coefficientAt25 Q)) :=
  first20ApproxWin Q hQ hn :: leftRestApprox25 Q hQ hn

def rightApprox25 (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    List (ApproxCatWindow 1 (readConstant coefficientAt25 Q)) :=
  rightHeadApproxWin Q hQ hn :: rightTailDigits25.map (bodyApproxWin Q hQ hn)

theorem leftApprox25_model (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    (leftApprox25 Q hQ hn).map ApproxCatWindow.model = leftModels25 Q hQ hn := by
  simp [leftApprox25, leftRestApprox25, leftModels25, first20ApproxWin, bodyApproxWin, List.map_map, Function.comp_def]

theorem rightApprox25_model (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    (rightApprox25 Q hQ hn).map ApproxCatWindow.model = rightModels25 Q hQ hn := by
  simp [rightApprox25, rightModels25, rightHeadApproxWin, bodyApproxWin, List.map_map, Function.comp_def]

theorem leftApprox25_catPhys (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    (leftApprox25 Q hQ hn).map ApproxCatWindow.catPhys = leftWins25Cat := by
  simp [leftApprox25, leftRestApprox25, leftWins25Cat, first20ApproxWin, bodyApproxWin, List.map_map, Function.comp_def]

theorem rightApprox25_catPhys (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    (rightApprox25 Q hQ hn).map ApproxCatWindow.catPhys = rightWins25Cat := by
  simp [rightApprox25, rightWins25Cat, rightHeadApproxWin, bodyApproxWin, List.map_map, Function.comp_def]

/-! ### Point-distribution propagation and exception bound (`≤ 52 / 2^236`) -/

def PointSupported (φ : State) : Prop := SupportedOn (pointFamily zeroBasisState) φ

def pointMass (φ : State) (P : Point) : ℝ := Complex.normSq (φ (pointWrite P zeroBasisState))

def BankPointFamily (bank : List Wire) : BasisState → Prop :=
  fun s => ∃ P input, input.length = bank.length ∧ s = phaseWordState bank input (pointWrite P zeroBasisState)

theorem pointSupported_y1 (φ : State) (hφ : PointSupported φ) :
    SupportedOn (fun s => s 1 = false) φ := fun s hs => by
  obtain ⟨P, rfl⟩ := hφ s hs
  rw [pointWrite_frame P zeroBasisState 1 wire1_not_point]; rfl

theorem phaseWordState_bankW_inj {k : Nat} (hk : k ≤ 18) {P₁ P₂ : Point} {in₁ in₂ : List Bool}
    (h1 : in₁.length = k + 1) (h2 : in₂.length = k + 1)
    (heq : phaseWordState (GenericW.bankW k) in₁ (pointWrite P₁ zeroBasisState) =
           phaseWordState (GenericW.bankW k) in₂ (pointWrite P₂ zeroBasisState)) :
    P₁ = P₂ ∧ in₁ = in₂ := by
  have hnd := GenericW.bankW_nodup k
  have hnot := bankW_not_point hk
  have hin : in₁ = in₂ := by
    have w1 := phaseWordState_word (GenericW.bankW k) hnd in₁ (by simpa [GenericW.bankW_length] using h1) (pointWrite P₁ zeroBasisState)
    have w2 := phaseWordState_word (GenericW.bankW k) hnd in₂ (by simpa [GenericW.bankW_length] using h2) (pointWrite P₂ zeroBasisState)
    rw [← w1, heq, w2]
  have hP : P₁ = P₂ := by
    have c1 : pointStateCoordinates (phaseWordState (GenericW.bankW k) in₁ (pointWrite P₁ zeroBasisState)) = fig14PointEncoding P₁ := by
      rw [phaseWordState_pointWrite (GenericW.bankW k) hnot, pointWrite_coordinates]
    have c2 : pointStateCoordinates (phaseWordState (GenericW.bankW k) in₂ (pointWrite P₂ zeroBasisState)) = fig14PointEncoding P₂ := by
      rw [phaseWordState_pointWrite (GenericW.bankW k) hnot, pointWrite_coordinates]
    exact fig14PointEncoding_injective (c1.symm.trans (by rw [heq, c2]))
  exact ⟨hP, hin⟩

theorem phaseWordState_bankW_goodW (Q : Point) (hQ : order • Q = 0) (d : Digit25)
    (P : Point) (input : List Bool) (hlen : input.length = d.width)
    (hgood : GenericW.GoodPoint P (Width16Schedule.increment (d.base Q) d.width d.exponent (boolWordToNat input))) :
    GenericW.GoodW d.k (wideCoeffs25 d) Q (phaseWordState d.bank input (pointWrite P zeroBasisState)) := by
  have hkhi := d.k_hi
  have hcl : GenericW.CleanOutsideXYBank (phaseWordState d.bank input (pointWrite P zeroBasisState)) := by
    intro w h1 h2 h3
    have hnb : w ∉ d.bank := fun hm => by
      have hb := GenericW.mem_bankW.mp hm
      exact h3 ⟨hb.1, by dsimp only [Wire] at *; omega⟩
    rw [phaseWordState_frame d.bank input _ w hnb]
    by_cases h8 : w = 838
    · subst h8
      cases hP : P with
      | zero => exact absurd hP hgood.1
      | some hns => exact congrArg Prod.fst (pointWrite_coordinates (.some hns) zeroBasisState)
    · rw [pointWrite_frame P zeroBasisState w (fun hm => by
        simp only [pointLogicalWires, pointCorrectionX, pointCorrectionYInf, List.mem_append,
          List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1, or_assoc] at hm
        rcases hm with hx | hy | rfl
        · exact h1 hx
        · exact h2 hy
        · exact h8 rfl)]; rfl
  have hfp : GenericW.HasFinitePoint P (phaseWordState d.bank input (pointWrite P zeroBasisState)) := by
    obtain ⟨x, y, hns, hPeq, hx, hy⟩ := GenericW.hasFinitePoint_pointWrite P hgood.1 zeroBasisState
    refine ⟨x, y, hns, hPeq, ?_, ?_⟩
    · rw [← hx]; apply ECDSAAdd.Arithmetic.regValue_congr; intro w hw
      rw [List.mem_range'_1] at hw
      exact phaseWordState_frame d.bank input _ w (fun hm => by
        have := GenericW.mem_bankW.mp hm; dsimp only [Wire] at *; omega)
    · rw [← hy]; apply ECDSAAdd.Arithmetic.regValue_congr; intro w hw
      rw [List.mem_range'_1] at hw
      exact phaseWordState_frame d.bank input _ w (fun hm => by
        have := GenericW.mem_bankW.mp hm; dsimp only [Wire] at *; omega)
  refine ⟨hcl, P, hfp, ?_⟩
  rwa [signedDeltaW_phaseWord Q hQ d input hlen]

theorem phaseWordState_bankW_goodW96 (Q : Point) (hQ : order • Q = 0) (d : Digit25)
    (P : Point) (input : List Bool) (hlen : input.length = d.width)
    (hgood : GenericW.GoodPoint96 P (Width16Schedule.increment (d.base Q) d.width d.exponent (boolWordToNat input))) :
    GenericW.GoodW96 d.k (wideCoeffs25 d) Q (phaseWordState d.bank input (pointWrite P zeroBasisState)) := by
  obtain ⟨hcl, R, hfp, _⟩ := phaseWordState_bankW_goodW Q hQ d P input hlen hgood.1
  have hPR : R = P := by
    have hc1 := GenericW.hasFinitePoint_coords hcl hfp
    have hc2 : pointStateCoordinates (phaseWordState d.bank input (pointWrite P zeroBasisState)) =
        fig14PointEncoding P := by
      rw [phaseWordState_pointWrite d.bank (bankW_not_point d.k_hi), pointWrite_coordinates]
    exact fig14PointEncoding_injective (hc1.symm.trans hc2)
  subst hPR
  refine ⟨hcl, R, hfp, ?_⟩
  rwa [signedDeltaW_phaseWord Q hQ d input hlen]

theorem updateW_injOn_bankPoint (Q : Point) (hQ : order • Q = 0) (d : Digit25) :
    Set.InjOn (GenericW.updateW d.k (wideCoeffs25 d) Q) {s | BankPointFamily d.bank s} := by
  have hnot := bankW_not_point d.k_hi
  have hblen : d.bank.length = d.width := GenericW.bankW_length d.k
  rintro s₁ ⟨P₁, in₁, h1, rfl⟩ s₂ ⟨P₂, in₂, h2, rfl⟩ heq
  have hc1 : pointStateCoordinates (phaseWordState d.bank in₁ (pointWrite P₁ zeroBasisState)) = fig14PointEncoding P₁ := by
    rw [phaseWordState_pointWrite d.bank hnot, pointWrite_coordinates]
  have hc2 : pointStateCoordinates (phaseWordState d.bank in₂ (pointWrite P₂ zeroBasisState)) = fig14PointEncoding P₂ := by
    rw [phaseWordState_pointWrite d.bank hnot, pointWrite_coordinates]
  have h1' : GenericW.updateW d.k (wideCoeffs25 d) Q (phaseWordState d.bank in₁ (pointWrite P₁ zeroBasisState)) =
      phaseWordState d.bank in₁ (pointWrite (P₁ + Width16Schedule.increment (d.base Q) d.width d.exponent (boolWordToNat in₁)) zeroBasisState) := by
    rw [GenericW.updateW_eq hc1, signedDeltaW_phaseWord Q hQ d in₁ (by simpa [hblen] using h1)]
    funext w
    by_cases hwb : w ∈ d.bank
    · rw [pointWrite_frame _ _ w (hnot w hwb)]
      exact (phaseWordState_agree d.bank in₁ _ _ w (by simpa [hblen] using h1.symm) hwb).symm
    · rw [phaseWordState_frame d.bank in₁ _ w hwb]
      by_cases hwp : w ∈ pointLogicalWires
      · exact pointWrite_agree_on_point _ _ _ w hwp
      · rw [pointWrite_frame _ _ w hwp, phaseWordState_frame d.bank in₁ _ w hwb,
          pointWrite_frame _ _ w hwp, pointWrite_frame _ _ w hwp]
  have h2' : GenericW.updateW d.k (wideCoeffs25 d) Q (phaseWordState d.bank in₂ (pointWrite P₂ zeroBasisState)) =
      phaseWordState d.bank in₂ (pointWrite (P₂ + Width16Schedule.increment (d.base Q) d.width d.exponent (boolWordToNat in₂)) zeroBasisState) := by
    rw [GenericW.updateW_eq hc2, signedDeltaW_phaseWord Q hQ d in₂ (by simpa [hblen] using h2)]
    funext w
    by_cases hwb : w ∈ d.bank
    · rw [pointWrite_frame _ _ w (hnot w hwb)]
      exact (phaseWordState_agree d.bank in₂ _ _ w (by simpa [hblen] using h2.symm) hwb).symm
    · rw [phaseWordState_frame d.bank in₂ _ w hwb]
      by_cases hwp : w ∈ pointLogicalWires
      · exact pointWrite_agree_on_point _ _ _ w hwp
      · rw [pointWrite_frame _ _ w hwp, phaseWordState_frame d.bank in₂ _ w hwb,
          pointWrite_frame _ _ w hwp, pointWrite_frame _ _ w hwp]
  rw [h1', h2'] at heq
  obtain ⟨hPsum, hin⟩ := phaseWordState_bankW_inj d.k_hi (by simpa [Digit25.bank, GenericW.bankW_length] using h1)
    (by simpa [Digit25.bank, GenericW.bankW_length] using h2) heq
  subst hin
  have hP : P₁ = P₂ := add_right_cancel hPsum
  subst hP; rfl

private theorem list_sum_eval_ket_not_mem {α : Type} (xs : List α) (f : α → ℂ)
    (g : α → BasisState) (s : BasisState) (hne : ∀ a ∈ xs, g a ≠ s) :
    ((xs.map (fun a => f a • ket (g a))).sum) s = 0 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
      ih (fun a ha => hne a (List.mem_cons_of_mem _ ha)), add_zero]
    rw [show ket (g x) s = 0 from Finsupp.single_eq_of_ne (Ne.symm (hne x List.mem_cons_self)), mul_zero]

private theorem list_sum_eval_ket_mem {α : Type} (xs : List α) (hnd : xs.Nodup) (f : α → ℂ)
    (g : α → BasisState) (hinj : ∀ a ∈ xs, ∀ b ∈ xs, g a = g b → a = b)
    (a₀ : α) (ha₀ : a₀ ∈ xs) :
    ((xs.map (fun a => f a • ket (g a))).sum) (g a₀) = f a₀ := by
  induction xs with
  | nil => cases ha₀
  | cons x xs ih =>
    have ⟨hxn, hnd'⟩ := List.nodup_cons.mp hnd
    have hinj' : ∀ a ∈ xs, ∀ b ∈ xs, g a = g b → a = b :=
      fun a ha b hb => hinj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)
    simp only [List.map_cons, List.sum_cons, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    rcases List.mem_cons.mp ha₀ with rfl | hm
    · rw [list_sum_eval_ket_not_mem xs f g (g a₀) (fun a ha hga =>
        hxn (hinj a (List.mem_cons_of_mem _ ha) a₀ List.mem_cons_self hga ▸ ha)), add_zero]
      simp [ket]
    · have hgx : g x ≠ g a₀ := fun h => hxn (hinj x List.mem_cons_self a₀ (List.mem_cons_of_mem _ hm) h ▸ hm)
      rw [show ket (g x) (g a₀) = 0 from Finsupp.single_eq_of_ne (Ne.symm hgx), mul_zero, zero_add]
      exact ih hnd' hinj' hm

private theorem fourierOutcomes_nodup (k : Nat) : (fourierOutcomes k).Nodup := by
  induction k with
  | zero => simp [fourierOutcomes]
  | succ k ih =>
    simp only [fourierOutcomes, List.nodup_append]
    refine ⟨ih.map (fun _ _ h => List.cons.inj h |>.2), ih.map (fun _ _ h => List.cons.inj h |>.2), ?_⟩
    intro x hx y hy
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hy
    simp

private theorem bankW_prep_eval_aux (k : Nat) (hk : k ≤ 18) (xs : List (List Bool)) (hnd : xs.Nodup)
    (hmem : ∀ a, a ∈ xs ↔ a.length = k + 1)
    (pre : Circuit) (wpre : Nat → ℂ)
    (hpre : ∀ P : Point, Quantum.run pre (Quantum.run ((GenericW.bankW k).map Gate.H) (ket (pointWrite P zeroBasisState))) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ (k + 1)) •
        (xs.map (fun input =>
          wpre (boolWordToNat input) • ket (phaseWordState (GenericW.bankW k) input (pointWrite P zeroBasisState)))).sum)
    (ψ : State) (hψ : PointSupported ψ) :
    let χ := Quantum.run pre (Quantum.run ((GenericW.bankW k).map Gate.H) ψ)
    SupportedOn (BankPointFamily (GenericW.bankW k)) χ ∧
    ∀ (P : Point) (input : List Bool), input.length = k + 1 →
      χ (phaseWordState (GenericW.bankW k) input (pointWrite P zeroBasisState)) =
        (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ (k + 1)) * wpre (boolWordToNat input) * ψ (pointWrite P zeroBasisState) := by
  dsimp only
  induction ψ using Finsupp.induction with
  | zero =>
    refine ⟨by simp [SupportedOn], fun P input _ => by simp⟩
  | single_add s c f hsf hc ih =>
    have hs_mem : pointFamily zeroBasisState s := hψ s (by
      simp [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.notMem_support_iff.mp hsf, hc])
    have hf : PointSupported f := fun t ht => hψ t (by
      have hts : t ≠ s := fun h => hsf (h ▸ Finsupp.mem_support_iff.mpr ht)
      rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hts, zero_add]; exact ht)
    obtain ⟨Q₀, rfl⟩ := hs_mem
    obtain ⟨ih_sup, ih_eval⟩ := ih hf
    have hket : Finsupp.single (pointWrite Q₀ zeroBasisState) c = c • ket (pointWrite Q₀ zeroBasisState) := by
      ext u; simp [ket]
    have hexp : Quantum.run pre (Quantum.run ((GenericW.bankW k).map Gate.H) (c • ket (pointWrite Q₀ zeroBasisState))) =
        (c * ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ (k + 1)) •
          (xs.map (fun input =>
            wpre (boolWordToNat input) • ket (phaseWordState (GenericW.bankW k) input (pointWrite Q₀ zeroBasisState)))).sum := by
      rw [map_smul, map_smul, hpre Q₀, smul_smul]
    have hsup1 : SupportedOn (BankPointFamily (GenericW.bankW k))
        (Quantum.run pre (Quantum.run ((GenericW.bankW k).map Gate.H) (Finsupp.single (pointWrite Q₀ zeroBasisState) c))) := by
      rw [hket, hexp]
      apply Support.smul; apply Support.list_sum; intro input hi
      apply Support.smul; apply supportedOn_ket
      exact ⟨Q₀, input, by simpa [GenericW.bankW_length] using (hmem input).mp hi, rfl⟩
    refine ⟨by rw [map_add, map_add]; exact Support.add hsup1 ih_sup, fun P input hlen => ?_⟩
    rw [map_add, map_add, Finsupp.add_apply, Finsupp.add_apply, hket, hexp, ih_eval P input hlen]
    rw [Finsupp.smul_apply, smul_eq_mul]
    have hinj : ∀ a ∈ xs, ∀ b ∈ xs,
        phaseWordState (GenericW.bankW k) a (pointWrite Q₀ zeroBasisState) =
        phaseWordState (GenericW.bankW k) b (pointWrite Q₀ zeroBasisState) → a = b :=
      fun a ha b hb heq => (phaseWordState_bankW_inj hk ((hmem a).mp ha) ((hmem b).mp hb) heq).2
    by_cases hP : P = Q₀
    · subst hP
      rw [list_sum_eval_ket_mem xs hnd (fun inp => wpre (boolWordToNat inp))
        (fun inp => phaseWordState (GenericW.bankW k) inp (pointWrite P zeroBasisState)) hinj input
        ((hmem input).mpr hlen)]
      simp only [Finsupp.smul_apply, ket, Finsupp.single_eq_same, smul_eq_mul, mul_one]
      ring
    · rw [list_sum_eval_ket_not_mem xs (fun inp => wpre (boolWordToNat inp))
        (fun inp => phaseWordState (GenericW.bankW k) inp (pointWrite Q₀ zeroBasisState)) _ (fun a ha hga =>
          hP (phaseWordState_bankW_inj hk ((hmem a).mp ha) hlen hga).1.symm)]
      have hne_s : pointWrite P zeroBasisState ≠ pointWrite Q₀ zeroBasisState :=
        fun e => hP (pointWrite_injective zeroBasisState e)
      simp only [Finsupp.smul_apply, ket, Finsupp.single_eq_of_ne hne_s, mul_zero, smul_zero, zero_add]

theorem bankW_prep_eval (k : Nat) (hk : k ≤ 18) (pre : Circuit) (wpre : Nat → ℂ)
    (hpre : ∀ P : Point, Quantum.run pre (Quantum.run ((GenericW.bankW k).map Gate.H) (ket (pointWrite P zeroBasisState))) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ (k + 1)) •
        ((fourierOutcomes (k + 1)).map (fun input =>
          wpre (boolWordToNat input) • ket (phaseWordState (GenericW.bankW k) input (pointWrite P zeroBasisState)))).sum)
    (ψ : State) (hψ : PointSupported ψ) :
    let χ := Quantum.run pre (Quantum.run ((GenericW.bankW k).map Gate.H) ψ)
    SupportedOn (BankPointFamily (GenericW.bankW k)) χ ∧
    ∀ (P : Point) (input : List Bool), input.length = k + 1 →
      χ (phaseWordState (GenericW.bankW k) input (pointWrite P zeroBasisState)) =
        (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ (k + 1)) * wpre (boolWordToNat input) * ψ (pointWrite P zeroBasisState) :=
  bankW_prep_eval_aux k hk (fourierOutcomes (k + 1)) (fourierOutcomes_nodup (k + 1)) (fourierOutcomes_mem (k + 1)) pre wpre hpre ψ hψ

theorem body_pre_expandW (k : Nat) (hk : k ≤ 18) (P : Point) :
    Quantum.run ([] : Circuit) (Quantum.run ((GenericW.bankW k).map Gate.H) (ket (pointWrite P zeroBasisState))) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ (k + 1)) •
        ((fourierOutcomes (k + 1)).map (fun input =>
          (1 : ℂ) • ket (phaseWordState (GenericW.bankW k) input (pointWrite P zeroBasisState)))).sum := by
  rw [Quantum.run_nil, phaseHadamards_uniform (GenericW.bankW k) (GenericW.bankW_nodup k) _ (pointWrite_zero_cleanW hk P)]
  simp [phaseUniformSum, GenericW.bankW_length]

theorem rightHead_pre_expand (P : Point) :
    Quantum.run (sineFromPlus top10Right) (Quantum.run ((GenericW.bankW 16).map Gate.H) (ket (pointWrite P zeroBasisState))) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 17) •
        ((fourierOutcomes 17).map (fun input =>
          sineWeight 10 (boolWordToNat input / 2 ^ 7) •
            ket (phaseWordState (GenericW.bankW 16) input (pointWrite P zeroBasisState)))).sum := by
  have hdrop : (GenericW.bankW 16).drop ((GenericW.bankW 16).length - 10) = top10Right := by
    simp [top10Right, GenericW.bankW_length]
  have hsb := sineFromPlus_bank (GenericW.bankW 16) (by simp [GenericW.bankW_length]) (GenericW.bankW_nodup 16)
    (pointWrite P zeroBasisState) (pointWrite_zero_cleanW (by decide) P)
  rw [hdrop, GenericW.bankW_length] at hsb
  exact hsb

private theorem sqrt2_inv_normSq_pow (k : Nat) :
    Complex.normSq (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ k) = (1 : ℝ) / (2 : ℝ) ^ k := by
  rw [map_pow, Complex.normSq_ofReal, ← sq, inv_pow, Real.sq_sqrt (by norm_num), inv_pow, one_div]

private theorem finset_sum_toFinset_le {α : Type} [DecidableEq α] (xs : List α) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ xs.toFinset, f x ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.toFinset_cons, List.map_cons, List.sum_cons]
    by_cases hm : x ∈ xs.toFinset
    · rw [Finset.insert_eq_of_mem hm]; linarith [hf x]
    · rw [Finset.sum_insert hm]; linarith

private theorem flatMap_sum_real {α β : Type} (xs : List α) (g : α → List β) (f : β → ℝ) :
    ((xs.flatMap g).map f).sum = (xs.map (fun x => ((g x).map f).sum)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons, ih]

def badBoundW (w : Nat) (wpre : Nat → ℂ) (delta : Nat → Point) (D : Point → ℝ) : ℝ :=
  ((1 : ℝ) / (2 : ℝ) ^ w) *
    ((fourierOutcomes w).map (fun input =>
      let v := boolWordToNat input
      let Δ := delta v
      Complex.normSq (wpre v) * (D 0 + D Δ + D (-Δ) + D (-(Δ + Δ))))).sum

def stepDistW (w : Nat) (wpre : Nat → ℂ) (delta : Nat → Point) (D : Point → ℝ) (P' : Point) : ℝ :=
  ((1 : ℝ) / (2 : ℝ) ^ w) *
    ((fourierOutcomes w).map (fun input =>
      let v := boolWordToNat input
      Complex.normSq (wpre v) * D (P' - delta v))).sum

theorem badStep_le_badBoundW (Q : Point) (hQ : order • Q = 0) (d : Digit25)
    (pre : Circuit) (wpre : Nat → ℂ)
    (hpre : ∀ P : Point, Quantum.run pre (Quantum.run (d.bank.map Gate.H) (ket (pointWrite P zeroBasisState))) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ d.width) •
        ((fourierOutcomes d.width).map (fun input =>
          wpre (boolWordToNat input) • ket (phaseWordState d.bank input (pointWrite P zeroBasisState)))).sum)
    (ψ : State) (hψ : PointSupported ψ) :
    let χ := Quantum.run pre (Quantum.run (d.bank.map Gate.H) ψ)
    normSq (restrictState (fun s => ¬ GenericW.GoodW d.k (wideCoeffs25 d) Q s) χ) ≤
      badBoundW d.width wpre (Width16Schedule.increment (d.base Q) d.width d.exponent) (pointMass ψ) := by
  classical
  dsimp only
  set χ := Quantum.run pre (Quantum.run (d.bank.map Gate.H) ψ)
  set χ_bad := restrictState (fun s => ¬ GenericW.GoodW d.k (wideCoeffs25 d) Q s) χ
  obtain ⟨hχ_sup, hχ_eval⟩ := bankW_prep_eval d.k d.k_hi pre wpre hpre ψ hψ
  let badList : List BasisState :=
    (fourierOutcomes d.width).flatMap (fun input =>
      let Δ := Width16Schedule.increment (d.base Q) d.width d.exponent (boolWordToNat input);
      ([0, Δ, -Δ, -(Δ + Δ)] : List Point).map (fun P => phaseWordState d.bank input (pointWrite P zeroBasisState)))
  have hsub : χ_bad.support ⊆ badList.toFinset := by
    intro s hs
    have hne : χ_bad s ≠ 0 := Finsupp.mem_support_iff.mp hs
    rw [restrictState_apply] at hne
    have hng : ¬ GenericW.GoodW d.k (wideCoeffs25 d) Q s := by
      by_contra hg; simp [hg] at hne
    have hχne : χ s ≠ 0 := by simpa [hng] using hne
    obtain ⟨P, input, hlen, rfl⟩ := hχ_sup s hχne
    have hlenW : input.length = d.width := by simpa [Digit25.bank, Digit25.width, GenericW.bankW_length] using hlen
    have hnb : ¬ GenericW.GoodPoint P (Width16Schedule.increment (d.base Q) d.width d.exponent (boolWordToNat input)) :=
      fun hg => hng (phaseWordState_bankW_goodW Q hQ d P input hlenW hg)
    rw [List.mem_toFinset]
    apply List.mem_flatMap.mpr
    refine ⟨input, (fourierOutcomes_mem d.width input).mpr hlenW, List.mem_map.mpr ⟨P, ?_, rfl⟩⟩
    unfold GenericW.GoodPoint at hnb
    push_neg at hnb
    by_cases h0 : P = 0; · simp [h0]
    by_cases h1 : P = Width16Schedule.increment (d.base Q) d.width d.exponent (boolWordToNat input); · simp [h1]
    by_cases h2 : P = -Width16Schedule.increment (d.base Q) d.width d.exponent (boolWordToNat input); · simp [h2]
    have h3 := hnb h0 h1 h2
    simp [h3]
  have hmass_eq : normSq χ_bad = ∑ s ∈ χ_bad.support, Complex.normSq (χ_bad s) := by
    unfold normSq Quantum.inner
    rw [Finsupp.sum, Complex.re_sum]
    apply Finset.sum_congr rfl; intro s _
    rw [mul_comm, Complex.mul_conj, Complex.ofReal_re]
  have hle1 : normSq χ_bad ≤ ∑ s ∈ badList.toFinset, Complex.normSq (χ s) := by
    rw [hmass_eq]
    calc ∑ s ∈ χ_bad.support, Complex.normSq (χ_bad s)
        ≤ ∑ s ∈ χ_bad.support, Complex.normSq (χ s) := by
          apply Finset.sum_le_sum; intro s _
          dsimp only [χ_bad]; rw [restrictState_apply]
          split_ifs
          · simp [Complex.normSq_nonneg]
          · exact le_rfl
      _ ≤ ∑ s ∈ badList.toFinset, Complex.normSq (χ s) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Complex.normSq_nonneg _)
  have hle2 : ∑ s ∈ badList.toFinset, Complex.normSq (χ s) ≤ (badList.map (fun s => Complex.normSq (χ s))).sum :=
    finset_sum_toFinset_le badList (fun s => Complex.normSq (χ s)) (fun _ => Complex.normSq_nonneg _)
  suffices hsum_eq : (badList.map (fun s => Complex.normSq (χ s))).sum =
      badBoundW d.width wpre (Width16Schedule.increment (d.base Q) d.width d.exponent) (pointMass ψ) by
    linarith
  dsimp only [badList, badBoundW]
  rw [flatMap_sum_real]
  have hmul : ∀ (xs : List (List Bool)) (r : ℝ) (f : List Bool → ℝ),
      r * (xs.map f).sum = (xs.map (fun x => r * f x)).sum := fun xs r f => by
    induction xs with
    | nil => simp
    | cons x xs ih => simp [ih, mul_add]
  rw [hmul]
  apply congrArg List.sum; apply List.map_congr_left
  intro input hi
  have hlenW : input.length = d.width := (fourierOutcomes_mem d.width input).mp hi
  simp only [List.map_map, Function.comp_def, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  dsimp only [χ]
  simp only [Digit25.bank, Digit25.width, hχ_eval _ input hlenW, map_mul, sqrt2_inv_normSq_pow, pointMass]
  ring

section
open scoped Classical
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Nat.iterate

private theorem p_eq_ecdsa : p = ECDSAAdd.p := by unfold p ECDSAAdd.p; rfl

private theorem zmod_sub_val_eq {n m : Nat} [NeZero n] [NeZero m] (h : n = m)
    (a b : ZMod n) (a' b' : ZMod m) (ha : a.val = a'.val) (hb : b.val = b'.val) :
    (a - b).val = (a' - b').val := by
  subst h
  have := ZMod.val_injective _ ha
  have := ZMod.val_injective _ hb
  subst_vars; rfl

private theorem zmod_genericX_sub_val_eq {n m : Nat} [NeZero n] [NeZero m] (h : n = m)
    (x y cx cy : ZMod n) (x' y' cx' cy' : ZMod m)
    (hx : x.val = x'.val) (hy : y.val = y'.val)
    (hcx : cx.val = cx'.val) (hcy : cy.val = cy'.val) :
    (cx - (((y - cy) * (x - cx)⁻¹) ^ 2 - x - cx)).val =
    (cx' - (((y' - cy') * (x' - cx')⁻¹) ^ 2 - x' - cx')).val := by
  subst h
  have : x = x' := ZMod.val_injective _ hx
  have : y = y' := ZMod.val_injective _ hy
  have : cx = cx' := ZMod.val_injective _ hcx
  have : cy = cy' := ZMod.val_injective _ hcy
  subst_vars; rfl

private def pointsListWithX (x : Fp) : List Point :=
  if h : ∃ y : Fp, curve.toAffine.Nonsingular x y then
    let hns := Classical.choose_spec h
    (WeierstrassCurve.Affine.Point.some hns : Point) :: -(WeierstrassCurve.Affine.Point.some hns : Point) :: List.nil
  else List.nil

private theorem pointsListWithX_length_le (x : Fp) : (pointsListWithX x).length ≤ 2 := by
  unfold pointsListWithX; split_ifs <;> simp

private theorem mem_pointsListWithX {x y : Fp} (hns : curve.toAffine.Nonsingular x y) :
    (WeierstrassCurve.Affine.Point.some hns : Point) ∈ pointsListWithX x := by
  have hex : ∃ y' : Fp, curve.toAffine.Nonsingular x y' := ⟨y, hns⟩
  unfold pointsListWithX
  rw [dif_pos hex]
  set y' := Classical.choose hex
  have hns' : curve.toAffine.Nonsingular x y' := Classical.choose_spec hex
  have heq1 : y ^ 2 = x ^ 3 + 7 := by
    have h := (curve.toAffine.equation_iff x y).mp hns.1
    simp only [curve, curveA, curveB, Nat.cast_zero, Nat.cast_ofNat, zero_mul, add_zero] at h; exact h
  have heq2 : y' ^ 2 = x ^ 3 + 7 := by
    have h := (curve.toAffine.equation_iff x y').mp hns'.1
    simp only [curve, curveA, curveB, Nat.cast_zero, Nat.cast_ofNat, zero_mul, add_zero] at h; exact h
  have hsq : y = y' ∨ y = -y' := sq_eq_sq_iff_eq_or_eq_neg.mp (heq1.trans heq2.symm)
  rcases hsq with rfl | rfl
  · exact List.mem_cons_self
  · apply List.mem_cons_of_mem
    rw [List.mem_singleton, WeierstrassCurve.Affine.Point.neg_some]
    congr 1; simp [WeierstrassCurve.Affine.negY, curve, y']

private def badListOf (B : List Nat) (Δ : Point) : List Point :=
  match Δ with
  | .zero => 0 :: List.nil
  | .some (x := cx) _ =>
    (0 :: Δ :: -Δ :: -(Δ + Δ) :: List.nil) ++
    B.flatMap (fun (b : Nat) => pointsListWithX (cx + (b : Fp))) ++
    B.flatMap (fun (b : Nat) => (pointsListWithX (cx - (b : Fp))).map (fun P' => P' - Δ))

private theorem flatMap_length_le_two {α β : Type*} (xs : List α) (f : α → List β)
    (hf : ∀ a, (f a).length ≤ 2) : (xs.flatMap f).length ≤ 2 * xs.length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have := hf a; omega

private theorem badListOf_length_le (B : List Nat) (Δ : Point) : (badListOf B Δ).length ≤ 4 + 4 * B.length := by
  cases Δ with
  | zero => simp [badListOf]; omega
  | @some cx cy hnsC =>
    let Δ' : Point := .some hnsC
    change ((0 :: Δ' :: -Δ' :: -(Δ' + Δ') :: List.nil) ++
      B.flatMap (fun (b : Nat) => pointsListWithX (cx + (b : Fp))) ++
      B.flatMap (fun (b : Nat) => (pointsListWithX (cx - (b : Fp))).map (fun P' => P' - Δ'))).length ≤ _
    simp only [List.length_append, List.length_cons, List.length_nil]
    have h1 := flatMap_length_le_two B (fun (b : Nat) => pointsListWithX (cx + (b : Fp)))
      (fun b => pointsListWithX_length_le _)
    have h2 := flatMap_length_le_two B (fun (b : Nat) => (pointsListWithX (cx - (b : Fp))).map (fun P' => P' - Δ'))
      (fun b => by simp only [List.length_map]; exact pointsListWithX_length_le _)
    omega

private theorem goodPoint_x_ne {x y cx cy : Fp}
    {hnsR : curve.toAffine.Nonsingular x y} {hnsC : curve.toAffine.Nonsingular cx cy}
    (hgp : GenericW.GoodPoint (.some hnsR) (.some hnsC)) : x ≠ cx := by
  intro hxc
  have heq1 : y ^ 2 = x ^ 3 + 7 := by
    have h := (curve.toAffine.equation_iff x y).mp hnsR.1
    simp only [curve, curveA, curveB, Nat.cast_zero, Nat.cast_ofNat, zero_mul, add_zero] at h; exact h
  have heq2 : cy ^ 2 = cx ^ 3 + 7 := by
    have h := (curve.toAffine.equation_iff cx cy).mp hnsC.1
    simp only [curve, curveA, curveB, Nat.cast_zero, Nat.cast_ofNat, zero_mul, add_zero] at h; exact h
  rw [hxc] at heq1
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (heq1.trans heq2.symm) with rfl | rfl
  · exact hgp.2.1 (by congr 1)
  · apply hgp.2.2.1
    change (WeierstrassCurve.Affine.Point.some hnsR : Point) = -(.some hnsC : Point)
    rw [WeierstrassCurve.Affine.Point.neg_some]
    congr 1; simp [WeierstrassCurve.Affine.negY, curve]

private theorem goodPoint_gx_ne {x y cx cy : Fp}
    {hnsR : curve.toAffine.Nonsingular x y} {hnsC : curve.toAffine.Nonsingular cx cy}
    (hgp : GenericW.GoodPoint (.some hnsR) (.some hnsC)) :
    ((y - cy) * (x - cx)⁻¹) ^ 2 - x - cx ≠ cx := by
  have hx_ne := goodPoint_x_ne hgp
  set gx : Fp := ((y - cy) * (x - cx)⁻¹) ^ 2 - x - cx
  have haddX : curve.toAffine.addX x cx (curve.toAffine.slope x cx y cy) = gx := by
    rw [curve.toAffine.slope_of_X_ne hx_ne]
    simp only [WeierstrassCurve.Affine.addX, curve, curveA, curveB, Nat.cast_zero,
      zero_mul, add_zero, div_eq_mul_inv, gx]; ring
  have hnsS0 := curve.toAffine.nonsingular_add hnsR hnsC (fun hxy => hx_ne hxy.1)
  have hadd0 : (WeierstrassCurve.Affine.Point.some hnsR : Point) + .some hnsC = .some hnsS0 :=
    WeierstrassCurve.Affine.Point.add_of_X_ne hx_ne
  intro hgx
  have hsum_ne : (WeierstrassCurve.Affine.Point.some hnsR : Point) + .some hnsC ≠ .some hnsC := by
    intro h
    have h0 : (WeierstrassCurve.Affine.Point.some hnsR : Point) + .some hnsC = 0 + .some hnsC := by
      rw [zero_add]; exact h
    exact hgp.1 (add_right_cancel h0)
  have hsum_ne_neg : (WeierstrassCurve.Affine.Point.some hnsR : Point) + .some hnsC ≠ -(.some hnsC : Point) := by
    intro h; apply hgp.2.2.2
    have h1 : (WeierstrassCurve.Affine.Point.some hnsR : Point) = -(.some hnsC : Point) - .some hnsC := eq_sub_of_add_eq h
    simpa [sub_eq_add_neg, neg_add] using h1
  set gy := curve.toAffine.addY x cx y (curve.toAffine.slope x cx y cy)
  have heq1 : gy ^ 2 = (curve.toAffine.addX x cx (curve.toAffine.slope x cx y cy)) ^ 3 + 7 := by
    have h := (curve.toAffine.equation_iff _ _).mp hnsS0.1
    simp only [curve, curveA, curveB, Nat.cast_zero, Nat.cast_ofNat, zero_mul, add_zero] at h; exact h
  have heq2 : cy ^ 2 = cx ^ 3 + 7 := by
    have h := (curve.toAffine.equation_iff cx cy).mp hnsC.1
    simp only [curve, curveA, curveB, Nat.cast_zero, Nat.cast_ofNat, zero_mul, add_zero] at h; exact h
  rw [haddX, hgx] at heq1
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (heq1.trans heq2.symm) with hy1 | hy2
  · apply hsum_ne; rw [hadd0]
    simp only [WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨haddX.trans hgx, hy1⟩
  · apply hsum_ne_neg; rw [hadd0]
    change (WeierstrassCurve.Affine.Point.some hnsS0 : Point) = -(.some hnsC : Point)
    rw [WeierstrassCurve.Affine.Point.neg_some]
    simp only [WeierstrassCurve.Affine.Point.some.injEq, WeierstrassCurve.Affine.negY, curve]
    exact ⟨haddX.trans hgx, by simp [hy2]⟩

private theorem goodPoint96_not_both {x y cx cy : Fp}
    {hnsR : curve.toAffine.Nonsingular x y} {hnsC : curve.toAffine.Nonsingular cx cy}
    (hgp : GenericW.GoodPoint (.some hnsR) (.some hnsC))
    (hnb : ¬ GenericW.GoodPoint96 (.some hnsR) (.some hnsC)) :
    ¬ (LocalKernel.SkywalkFast485 (x - cx).val ∧
      LocalKernel.SkywalkFast485 (cx - (((y - cy) * (x - cx)⁻¹) ^ 2 - x - cx)).val) := by
  have hx_ne := goodPoint_x_ne hgp
  have hgx_ne := goodPoint_gx_ne hgp
  haveI : NeZero p := ⟨p_prime.ne_zero⟩
  haveI : NeZero ECDSAAdd.p := ⟨ECDSAAdd.Secp256k1.p_prime.ne_zero⟩
  rintro ⟨hf1, hf2⟩
  apply hnb
  refine ⟨hgp, fun x' y' cx' cy' hnsR' hnsC' hR' hC' => ?_⟩
  have hx_val : x.val = x'.val ∧ y.val = y'.val := by cases hR'; exact ⟨rfl, rfl⟩
  have hcx_val : cx.val = cx'.val ∧ cy.val = cy'.val := by cases hC'; exact ⟨rfl, rfl⟩
  have hv1 : (x - cx).val = (x' - cx').val :=
    zmod_sub_val_eq p_eq_ecdsa x cx x' cx' hx_val.1 hcx_val.1
  have hv2 : (cx - (((y - cy) * (x - cx)⁻¹) ^ 2 - x - cx)).val =
      (cx' - ECDSAAdd.Secp256k1.genericX x' y' cx' cy').val := by
    unfold ECDSAAdd.Secp256k1.genericX ECDSAAdd.Secp256k1.genericSlope
      ECDSAAdd.Secp256k1.genericNumerator ECDSAAdd.Secp256k1.genericDenominator
    dsimp only
    exact zmod_genericX_sub_val_eq p_eq_ecdsa x y cx cy x' y' cx' cy' hx_val.1 hx_val.2 hcx_val.1 hcx_val.2
  have hne1' : x' - cx' ≠ 0 := by
    intro h0
    have h1 : (x - cx).val = 0 := hv1.trans (by rw [h0]; rfl)
    exact sub_ne_zero.mpr hx_ne ((ZMod.val_eq_zero _).mp h1)
  have hne2' : cx' - ECDSAAdd.Secp256k1.genericX x' y' cx' cy' ≠ 0 := by
    intro h0
    have h2 : (cx - (((y - cy) * (x - cx)⁻¹) ^ 2 - x - cx)).val = 0 := hv2.trans (by rw [h0]; rfl)
    exact sub_ne_zero.mpr hgx_ne.symm ((ZMod.val_eq_zero _).mp h2)
  unfold GenericW.arithSpecTrunc96
  exact ⟨⟨hne1', hv1 ▸ hf1⟩, ⟨hne2', hv2 ▸ hf2⟩⟩

private theorem not_goodPoint96_mem_badListOf {B : List Nat}
    (hB : ∀ b, 0 < b → b < ECDSAAdd.p → ¬ LocalKernel.SkywalkFast485 b → b ∈ B)
    {R Δ : Point} (hnb : ¬ GenericW.GoodPoint96 R Δ) :
    R ∈ badListOf B Δ := by
  cases Δ with
  | zero =>
    have hR0 : R = 0 := by
      by_contra hne
      apply hnb
      refine ⟨⟨hne, hne, by simpa using hne, by simpa using hne⟩, ?_⟩
      intro _ _ _ _ _ _ _ hC; cases hC
    change R ∈ ((0 :: List.nil) : List Point)
    simp [hR0]
  | @some cx cy hnsC =>
    let Δ' : Point := .some hnsC
    change R ∈ ((0 :: Δ' :: -Δ' :: -(Δ' + Δ') :: List.nil) : List Point) ++
      B.flatMap (fun (b : Nat) => pointsListWithX (cx + (b : Fp))) ++
      B.flatMap (fun (b : Nat) => (pointsListWithX (cx - (b : Fp))).map (fun P' => P' - Δ'))
    by_cases hgp : GenericW.GoodPoint R Δ'
    · cases hR : R with
      | zero => exact absurd hR hgp.1
      | @some x y hnsR =>
        let R' : Point := .some hnsR
        have hgp' : GenericW.GoodPoint R' Δ' := by dsimp only [R']; rwa [← hR]
        have hnb' : ¬ GenericW.GoodPoint96 R' Δ' := by dsimp only [R']; rwa [← hR]
        have hx_ne := goodPoint_x_ne hgp'
        have hgx_ne := goodPoint_gx_ne hgp'
        have hnot_both := goodPoint96_not_both hgp' hnb'
        set gx : Fp := ((y - cy) * (x - cx)⁻¹) ^ 2 - x - cx
        have hne1 : x - cx ≠ 0 := sub_ne_zero.mpr hx_ne
        have hne2 : cx - gx ≠ 0 := sub_ne_zero.mpr hgx_ne.symm
        by_cases hf1 : LocalKernel.SkywalkFast485 (x - cx).val
        · have hnf2 : ¬ LocalKernel.SkywalkFast485 (cx - gx).val := fun hf2 => hnot_both ⟨hf1, hf2⟩
          set b : Nat := (cx - gx).val
          have hb_pos : 0 < b := by
            haveI : NeZero p := ⟨p_prime.ne_zero⟩
            exact Nat.pos_of_ne_zero (fun h0 => hne2 ((ZMod.val_eq_zero _).mp h0))
          have hb_lt : b < ECDSAAdd.p := by
            haveI : NeZero p := ⟨p_prime.ne_zero⟩
            exact p_eq_ecdsa ▸ ZMod.val_lt _
          have hb_mem : b ∈ B := hB b hb_pos hb_lt hnf2
          have hcx_sub : cx - (b : Fp) = gx := by dsimp only [b]; rw [ZMod.natCast_zmod_val]; ring
          have haddX : curve.toAffine.addX x cx (curve.toAffine.slope x cx y cy) = gx := by
            rw [curve.toAffine.slope_of_X_ne hx_ne]
            simp only [WeierstrassCurve.Affine.addX, curve, curveA, curveB, Nat.cast_zero,
              zero_mul, add_zero, div_eq_mul_inv, gx]; ring
          have hnsS0 := curve.toAffine.nonsingular_add hnsR hnsC (fun hxy => hx_ne hxy.1)
          have hadd0 : R' + Δ' = .some hnsS0 := WeierstrassCurve.Affine.Point.add_of_X_ne hx_ne
          have hP'_mem : R' + Δ' ∈ pointsListWithX (cx - (b : Fp)) := by
            rw [hcx_sub, ← haddX, hadd0]; exact mem_pointsListWithX hnsS0
          exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨b, hb_mem,
            List.mem_map.mpr ⟨R' + Δ', hP'_mem, add_sub_cancel_right R' Δ'⟩⟩)
        · set b : Nat := (x - cx).val
          have hb_pos : 0 < b := by
            haveI : NeZero p := ⟨p_prime.ne_zero⟩
            exact Nat.pos_of_ne_zero (fun h0 => hne1 ((ZMod.val_eq_zero _).mp h0))
          have hb_lt : b < ECDSAAdd.p := by
            haveI : NeZero p := ⟨p_prime.ne_zero⟩
            exact p_eq_ecdsa ▸ ZMod.val_lt _
          have hb_mem : b ∈ B := hB b hb_pos hb_lt hf1
          have hcx_add : cx + (b : Fp) = x := by dsimp only [b]; rw [ZMod.natCast_zmod_val]; ring
          have hR_mem : R' ∈ pointsListWithX (cx + (b : Fp)) := by
            rw [hcx_add]; exact mem_pointsListWithX hnsR
          exact List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨b, hb_mem, hR_mem⟩))
    · apply List.mem_append_left; apply List.mem_append_left
      unfold GenericW.GoodPoint at hgp
      push_neg at hgp
      by_cases h0 : R = 0
      · subst h0; simp
      by_cases h1 : R = Δ'
      · subst h1; simp
      by_cases h2 : R = -Δ'
      · subst h2; simp
      have h3 := hgp h0 h1 h2
      subst h3; simp

private def badList96 (Δ : Point) : List Point := badListOf SkywalkTail485.Bad485.toList Δ

private theorem badList96_length_le (Δ : Point) : (badList96 Δ).length ≤ 4 + 4 * SkywalkTail485.Bad485.card := by
  simpa [badList96, Finset.length_toList] using badListOf_length_le SkywalkTail485.Bad485.toList Δ

private theorem not_goodPoint96_mem_badList96 {R Δ : Point} (hnb : ¬ GenericW.GoodPoint96 R Δ) :
    R ∈ badList96 Δ :=
  not_goodPoint96_mem_badListOf
    (fun _ hpos hlt hnf => Finset.mem_toList.mpr (by
      unfold SkywalkTail485.Bad485
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨hpos, hlt⟩, hnf⟩)) hnb

end

private def badBoundW96 (w : Nat) (wpre : Nat → ℂ) (delta : Nat → Point) (D : Point → ℝ) : ℝ :=
  ((1 : ℝ) / (2 : ℝ) ^ w) *
    ((fourierOutcomes w).map (fun input =>
      let v := boolWordToNat input
      Complex.normSq (wpre v) * ((badList96 (delta v)).map D).sum)).sum

private theorem badStep96_le_badBoundW96 (Q : Point) (hQ : order • Q = 0) (d : Digit25)
    (pre : Circuit) (wpre : Nat → ℂ)
    (hpre : ∀ P : Point, Quantum.run pre (Quantum.run (d.bank.map Gate.H) (ket (pointWrite P zeroBasisState))) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ d.width) •
        ((fourierOutcomes d.width).map (fun input =>
          wpre (boolWordToNat input) • ket (phaseWordState d.bank input (pointWrite P zeroBasisState)))).sum)
    (ψ : State) (hψ : PointSupported ψ) :
    let χ := Quantum.run pre (Quantum.run (d.bank.map Gate.H) ψ)
    normSq (restrictState (fun s => ¬ GenericW.GoodW96 d.k (wideCoeffs25 d) Q s) χ) ≤
      badBoundW96 d.width wpre (Width16Schedule.increment (d.base Q) d.width d.exponent) (pointMass ψ) := by
  classical
  dsimp only
  set χ := Quantum.run pre (Quantum.run (d.bank.map Gate.H) ψ)
  set χ_bad := restrictState (fun s => ¬ GenericW.GoodW96 d.k (wideCoeffs25 d) Q s) χ
  obtain ⟨hχ_sup, hχ_eval⟩ := bankW_prep_eval d.k d.k_hi pre wpre hpre ψ hψ
  let badList : List BasisState :=
    (fourierOutcomes d.width).flatMap (fun input =>
      let Δ := Width16Schedule.increment (d.base Q) d.width d.exponent (boolWordToNat input);
      (badList96 Δ).map (fun P => phaseWordState d.bank input (pointWrite P zeroBasisState)))
  have hsub : χ_bad.support ⊆ badList.toFinset := by
    intro s hs
    have hne : χ_bad s ≠ 0 := Finsupp.mem_support_iff.mp hs
    rw [restrictState_apply] at hne
    have hng : ¬ GenericW.GoodW96 d.k (wideCoeffs25 d) Q s := by
      by_contra hg; simp [hg] at hne
    have hχne : χ s ≠ 0 := by simpa [hng] using hne
    obtain ⟨P, input, hlen, rfl⟩ := hχ_sup s hχne
    have hlenW : input.length = d.width := by simpa [Digit25.bank, Digit25.width, GenericW.bankW_length] using hlen
    have hnb : ¬ GenericW.GoodPoint96 P (Width16Schedule.increment (d.base Q) d.width d.exponent (boolWordToNat input)) :=
      fun hg => hng (phaseWordState_bankW_goodW96 Q hQ d P input hlenW hg)
    rw [List.mem_toFinset]
    apply List.mem_flatMap.mpr
    refine ⟨input, (fourierOutcomes_mem d.width input).mpr hlenW,
      List.mem_map.mpr ⟨P, not_goodPoint96_mem_badList96 hnb, rfl⟩⟩
  have hmass_eq : normSq χ_bad = ∑ s ∈ χ_bad.support, Complex.normSq (χ_bad s) := by
    unfold normSq Quantum.inner
    rw [Finsupp.sum, Complex.re_sum]
    apply Finset.sum_congr rfl; intro s _
    rw [mul_comm, Complex.mul_conj, Complex.ofReal_re]
  have hle1 : normSq χ_bad ≤ ∑ s ∈ badList.toFinset, Complex.normSq (χ s) := by
    rw [hmass_eq]
    calc ∑ s ∈ χ_bad.support, Complex.normSq (χ_bad s)
        ≤ ∑ s ∈ χ_bad.support, Complex.normSq (χ s) := by
          apply Finset.sum_le_sum; intro s _
          dsimp only [χ_bad]; rw [restrictState_apply]
          split_ifs
          · simp [Complex.normSq_nonneg]
          · exact le_rfl
      _ ≤ ∑ s ∈ badList.toFinset, Complex.normSq (χ s) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Complex.normSq_nonneg _)
  have hle2 : ∑ s ∈ badList.toFinset, Complex.normSq (χ s) ≤ (badList.map (fun s => Complex.normSq (χ s))).sum :=
    finset_sum_toFinset_le badList (fun s => Complex.normSq (χ s)) (fun _ => Complex.normSq_nonneg _)
  suffices hsum_eq : (badList.map (fun s => Complex.normSq (χ s))).sum =
      badBoundW96 d.width wpre (Width16Schedule.increment (d.base Q) d.width d.exponent) (pointMass ψ) by
    linarith
  dsimp only [badList, badBoundW96]
  rw [flatMap_sum_real]
  have hmul : ∀ (xs : List (List Bool)) (r : ℝ) (f : List Bool → ℝ),
      r * (xs.map f).sum = (xs.map (fun x => r * f x)).sum := fun xs r f => by
    induction xs with
    | nil => simp
    | cons x xs ih => simp [ih, mul_add]
  rw [hmul]
  apply congrArg List.sum; apply List.map_congr_left
  intro input hi
  have hlenW : input.length = d.width := (fourierOutcomes_mem d.width input).mp hi
  rw [List.map_map]
  have hmulP : ∀ (ps : List Point) (r : ℝ) (f : Point → ℝ),
      (ps.map (fun P => r * f P)).sum = r * (ps.map f).sum := fun ps r f => by
    induction ps with
    | nil => simp
    | cons _ _ ih => simp [ih, mul_add]
  have hcongr : ∀ P ∈ badList96 (Width16Schedule.increment (d.base Q) d.width d.exponent (boolWordToNat input)),
      Complex.normSq (χ (phaseWordState d.bank input (pointWrite P zeroBasisState))) =
        ((1 : ℝ) / (2 : ℝ) ^ d.width * Complex.normSq (wpre (boolWordToNat input))) * pointMass ψ P := by
    intro P _
    dsimp only [χ]
    simp only [Digit25.bank, Digit25.width, hχ_eval P input hlenW, map_mul, sqrt2_inv_normSq_pow, pointMass]
  change ((badList96 _).map (fun P => Complex.normSq (χ (phaseWordState d.bank input (pointWrite P zeroBasisState))))).sum = _
  rw [List.map_congr_left hcongr, hmulP]; ring

theorem projPoint_fourierBranch_comm (ws : List Wire) (hdisj : ∀ w ∈ ws, w ∉ pointLogicalWires)
    (dir : PhaseDir) (prior bits : List Bool) (P' : Point) (φ : State) :
    fourierBranch dir ws prior bits (restrictState (fun s => pointStateCoordinates s = fig14PointEncoding P') φ) =
      restrictState (fun s => pointStateCoordinates s = fig14PointEncoding P') (fourierBranch dir ws prior bits φ) := by
  classical
  have hclr (s : BasisState) : pointStateCoordinates (fourierClear ws s) = pointStateCoordinates s := by
    have hfr : ∀ w ∈ pointLogicalWires, fourierClear ws s w = s w := by
      intro w hw
      clear prior bits dir P' φ
      induction ws generalizing s with
      | nil => rfl
      | cons u us ih =>
        have hwu : w ≠ u := fun e => hdisj u List.mem_cons_self (e ▸ hw)
        rw [fourierClear, ih (fun v hv => hdisj v (List.mem_cons_of_mem _ hv))]
        simp [upd, hwu]
    simp only [pointStateCoordinates, wireValues]
    have hx : (List.range' 263 256).map (fourierClear ws s) = (List.range' 263 256).map s :=
      List.map_congr_left (fun w hw => hfr w (by simp only [pointLogicalWires, pointCorrectionX, List.mem_append, hw, true_or]))
    have hy : (List.range' 580 256).map (fourierClear ws s) = (List.range' 580 256).map s :=
      List.map_congr_left (fun w hw => hfr w (by simp only [pointLogicalWires, pointCorrectionYInf, List.mem_append, List.mem_cons, hw, true_or, or_true]))
    have h8 : fourierClear ws s 838 = s 838 := hfr 838 wire838_mem_point
    rw [hx, hy, h8]
  induction φ using Finsupp.induction_linear with
  | zero =>
    have hz : restrictState (fun s => pointStateCoordinates s = fig14PointEncoding P') (0 : State) = 0 := by
      ext s; simp [restrictState_apply]
    simp [hz]
  | add a b ha hb => rw [restrictState_map_add, map_add, map_add, restrictState_map_add, ha, hb]
  | single s c =>
    have hk : Finsupp.single s c = c • ket s := by ext u; simp [ket]
    rw [hk, restrictState_map_smul, map_smul, map_smul, restrictState_map_smul,
      restrictState_ket, fourierBranch_ket, restrictState_map_smul, restrictState_ket, hclr s]
    by_cases hc : pointStateCoordinates s = fig14PointEncoding P'
    · simp [hc, fourierBranch_ket]
    · simp [hc]

theorem pointMass_eq_normSq_projPoint (φ : State) (hφ : PointSupported φ) (P' : Point) :
    pointMass φ P' = normSq (restrictState (fun s => pointStateCoordinates s = fig14PointEncoding P') φ) := by
  classical
  have heq : restrictState (fun s => pointStateCoordinates s = fig14PointEncoding P') φ =
      φ (pointWrite P' zeroBasisState) • ket (pointWrite P' zeroBasisState) := by
    ext s
    rw [restrictState_apply, Finsupp.smul_apply, smul_eq_mul]
    by_cases hs : s = pointWrite P' zeroBasisState
    · subst hs; simp [pointWrite_coordinates, ket]
    · simp only [ket, Finsupp.single_eq_of_ne hs, mul_zero]
      split_ifs with hco
      · by_contra hne
        obtain ⟨Q₀, rfl⟩ := hφ s hne
        rw [pointWrite_coordinates] at hco
        exact hs (congrArg (fun R => pointWrite R zeroBasisState) (fig14PointEncoding_injective hco))
      · rfl
  rw [heq, normSq_smul, normSq_ket, mul_one]; rfl

theorem step_pointMass_sumW (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (d : Digit25)
    (pre : Circuit) (wpre : Nat → ℂ) (m : WindowModel (readConstant coefficientAt25 Q))
    (hm_wires : m.physical.wires = d.bank.reverse)
    (hm_ideal : m.ideal = (Finsupp.lmapDomain ℂ ℂ (GenericW.updateW d.k (wideCoeffs25 d) Q)).comp (Quantum.run pre))
    (hpre : ∀ P : Point, Quantum.run pre (Quantum.run (d.bank.map Gate.H) (ket (pointWrite P zeroBasisState))) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ d.width) •
        ((fourierOutcomes d.width).map (fun input =>
          wpre (boolWordToNat input) • ket (phaseWordState d.bank input (pointWrite P zeroBasisState)))).sum)
    (hm_pt : ∀ prior bits φ, PointSupported φ → PointSupported (m.step prior bits φ))
    (prior : List Bool) (ψ : State) (hψ : PointSupported ψ) (P' : Point) :
    ((fourierOutcomes d.width).map (fun bits => pointMass (m.step prior bits ψ) P')).sum =
      stepDistW d.width wpre (Width16Schedule.increment (d.base Q) d.width d.exponent) (pointMass ψ) P' := by
  classical
  have hnot := bankW_not_point d.k_hi
  have hblen : d.bank.length = d.width := GenericW.bankW_length d.k
  let φ_after := m.ideal (Quantum.run (m.physical.wires.reverse.map Gate.H) ψ)
  have h1 : ((fourierOutcomes d.width).map (fun bits => pointMass (m.step prior bits ψ) P')).sum =
      normSq (restrictState (fun s => pointStateCoordinates s = fig14PointEncoding P') φ_after) := by
    have hper : ∀ bits ∈ fourierOutcomes d.width,
        pointMass (m.step prior bits ψ) P' =
          normSq (fourierBranch .inverse d.bank.reverse prior bits
            (restrictState (fun s => pointStateCoordinates s = fig14PointEncoding P') φ_after)) := by
      intro bits _
      rw [pointMass_eq_normSq_projPoint _ (hm_pt prior bits ψ hψ) P']
      change normSq (restrictState _ (fourierBranch .inverse m.physical.wires prior bits φ_after)) = _
      rw [hm_wires, projPoint_fourierBranch_comm d.bank.reverse (fun w hw => hnot w (List.mem_reverse.mp hw))]
    rw [List.map_congr_left hper]
    simpa [hblen] using
      normSq_list_sum_fourierBranch .inverse d.bank.reverse prior
        (restrictState (fun s => pointStateCoordinates s = fig14PointEncoding P') φ_after)
  rw [h1]
  let χ := Quantum.run pre (Quantum.run (d.bank.map Gate.H) ψ)
  obtain ⟨hχ_sup, hχ_eval⟩ := bankW_prep_eval d.k d.k_hi pre wpre hpre ψ hψ
  have hφ_eq : φ_after = Finsupp.lmapDomain ℂ ℂ (GenericW.updateW d.k (wideCoeffs25 d) Q) χ := by
    dsimp only [φ_after, χ]; rw [hm_ideal, hm_wires, List.reverse_reverse]; rfl
  have hproj_eq : restrictState (fun s => pointStateCoordinates s = fig14PointEncoding P') φ_after =
      Finsupp.lmapDomain ℂ ℂ (GenericW.updateW d.k (wideCoeffs25 d) Q)
        (restrictState (fun s => pointStateCoordinates (GenericW.updateW d.k (wideCoeffs25 d) Q s) = fig14PointEncoding P') χ) := by
    rw [hφ_eq]
    induction χ using Finsupp.induction_linear with
    | zero =>
      have hz1 : restrictState (fun s => pointStateCoordinates s = fig14PointEncoding P') (0 : State) = 0 := by
        ext s; simp [restrictState_apply]
      have hz2 : restrictState (fun s => pointStateCoordinates (GenericW.updateW d.k (wideCoeffs25 d) Q s) = fig14PointEncoding P') (0 : State) = 0 := by
        ext s; simp [restrictState_apply]
      simp [hz1, hz2]
    | add a b ha hb => rw [map_add, restrictState_map_add, restrictState_map_add, map_add, ha, hb]
    | single s c =>
      have hk : Finsupp.single s c = c • ket s := by ext u; simp [ket]
      rw [hk, map_smul, restrictState_map_smul, restrictState_map_smul, map_smul,
        Mixed.lmap_ket', restrictState_ket, restrictState_ket]
      split_ifs <;> simp [ket, Finsupp.mapDomain_single]
  have hres_sup : SupportedOn (BankPointFamily d.bank)
      (restrictState (fun s => pointStateCoordinates (GenericW.updateW d.k (wideCoeffs25 d) Q s) = fig14PointEncoding P') χ) :=
    restrictState_preserves _ _ _ hχ_sup
  rw [hproj_eq, normSq_lmapDomain_injOn _ ((updateW_injOn_bankPoint Q hQ d).mono (fun s hs => hres_sup s (Finsupp.mem_support_iff.mp hs)))]
  have hres_expand :
      restrictState (fun s => pointStateCoordinates (GenericW.updateW d.k (wideCoeffs25 d) Q s) = fig14PointEncoding P') χ =
      ((fourierOutcomes d.width).map (fun input =>
        let P₀ := P' - Width16Schedule.increment (d.base Q) d.width d.exponent (boolWordToNat input);
        χ (phaseWordState d.bank input (pointWrite P₀ zeroBasisState)) •
          ket (phaseWordState d.bank input (pointWrite P₀ zeroBasisState)))).sum := by
    have hinj : ∀ a ∈ fourierOutcomes d.width, ∀ b ∈ fourierOutcomes d.width,
        phaseWordState d.bank a (pointWrite (P' - Width16Schedule.increment (d.base Q) d.width d.exponent (boolWordToNat a)) zeroBasisState) =
        phaseWordState d.bank b (pointWrite (P' - Width16Schedule.increment (d.base Q) d.width d.exponent (boolWordToNat b)) zeroBasisState) →
        a = b := fun a ha b hb heq =>
      (phaseWordState_bankW_inj d.k_hi ((fourierOutcomes_mem d.width a).mp ha) ((fourierOutcomes_mem d.width b).mp hb) heq).2
    ext s
    rw [restrictState_apply]
    by_cases hcond : pointStateCoordinates (GenericW.updateW d.k (wideCoeffs25 d) Q s) = fig14PointEncoding P' ∧ χ s ≠ 0
    · obtain ⟨hco, hχne⟩ := hcond
      rw [if_pos hco]
      obtain ⟨P, input, hlen, rfl⟩ := hχ_sup s hχne
      have hlenW : input.length = d.width := by rw [← hblen]; exact hlen
      have hc0 : pointStateCoordinates (phaseWordState d.bank input (pointWrite P zeroBasisState)) = fig14PointEncoding P := by
        rw [phaseWordState_pointWrite d.bank hnot, pointWrite_coordinates]
      have hupd_co : pointStateCoordinates (GenericW.updateW d.k (wideCoeffs25 d) Q
            (phaseWordState d.bank input (pointWrite P zeroBasisState))) =
          fig14PointEncoding (P + Width16Schedule.increment (d.base Q) d.width d.exponent (boolWordToNat input)) := by
        rw [GenericW.updateW_eq hc0, signedDeltaW_phaseWord Q hQ d input hlenW, pointWrite_coordinates]
      have hP_eq : P = P' - Width16Schedule.increment (d.base Q) d.width d.exponent (boolWordToNat input) := by
        have hsum : P + Width16Schedule.increment (d.base Q) d.width d.exponent (boolWordToNat input) = P' :=
          fig14PointEncoding_injective (hupd_co.symm.trans hco)
        exact eq_sub_of_add_eq hsum
      subst hP_eq
      symm
      exact list_sum_eval_ket_mem (fourierOutcomes d.width) (fourierOutcomes_nodup d.width)
        (fun inp => χ (phaseWordState d.bank inp (pointWrite (P' - Width16Schedule.increment (d.base Q) d.width d.exponent (boolWordToNat inp)) zeroBasisState)))
        (fun inp => phaseWordState d.bank inp (pointWrite (P' - Width16Schedule.increment (d.base Q) d.width d.exponent (boolWordToNat inp)) zeroBasisState))
        hinj input ((fourierOutcomes_mem d.width input).mpr hlenW)
    · push_neg at hcond
      have hlhs0 : (if pointStateCoordinates (GenericW.updateW d.k (wideCoeffs25 d) Q s) = fig14PointEncoding P' then χ s else 0) = 0 := by
        by_cases hco : pointStateCoordinates (GenericW.updateW d.k (wideCoeffs25 d) Q s) = fig14PointEncoding P'
        · rw [if_pos hco, hcond hco]
        · rw [if_neg hco]
      rw [hlhs0]
      symm
      by_cases hex : ∃ inp ∈ fourierOutcomes d.width,
          phaseWordState d.bank inp (pointWrite (P' - Width16Schedule.increment (d.base Q) d.width d.exponent (boolWordToNat inp)) zeroBasisState) = s
      · obtain ⟨inp, hi, rfl⟩ := hex
        have hlenW : inp.length = d.width := (fourierOutcomes_mem d.width inp).mp hi
        have hc0 : pointStateCoordinates (phaseWordState d.bank inp (pointWrite (P' - Width16Schedule.increment (d.base Q) d.width d.exponent (boolWordToNat inp)) zeroBasisState)) =
            fig14PointEncoding (P' - Width16Schedule.increment (d.base Q) d.width d.exponent (boolWordToNat inp)) := by
          rw [phaseWordState_pointWrite d.bank hnot, pointWrite_coordinates]
        have hco : pointStateCoordinates (GenericW.updateW d.k (wideCoeffs25 d) Q
            (phaseWordState d.bank inp (pointWrite (P' - Width16Schedule.increment (d.base Q) d.width d.exponent (boolWordToNat inp)) zeroBasisState))) =
            fig14PointEncoding P' := by
          rw [GenericW.updateW_eq hc0, signedDeltaW_phaseWord Q hQ d inp hlenW, pointWrite_coordinates, sub_add_cancel]
        rw [list_sum_eval_ket_mem (fourierOutcomes d.width) (fourierOutcomes_nodup d.width)
          (fun x => χ (phaseWordState d.bank x (pointWrite (P' - Width16Schedule.increment (d.base Q) d.width d.exponent (boolWordToNat x)) zeroBasisState)))
          (fun x => phaseWordState d.bank x (pointWrite (P' - Width16Schedule.increment (d.base Q) d.width d.exponent (boolWordToNat x)) zeroBasisState))
          hinj inp hi, hcond hco]
      · push_neg at hex
        exact list_sum_eval_ket_not_mem (fourierOutcomes d.width) _ _ s hex
  rw [hres_expand]
  have hnorm_sum : ∀ (xs : List (List Bool)), xs.Nodup → (∀ x ∈ xs, x.length = d.width) →
      normSq ((xs.map (fun input =>
        let P₀ := P' - Width16Schedule.increment (d.base Q) d.width d.exponent (boolWordToNat input);
        χ (phaseWordState d.bank input (pointWrite P₀ zeroBasisState)) •
          ket (phaseWordState d.bank input (pointWrite P₀ zeroBasisState)))).sum) =
      (xs.map (fun input =>
        let P₀ := P' - Width16Schedule.increment (d.base Q) d.width d.exponent (boolWordToNat input);
        Complex.normSq (χ (phaseWordState d.bank input (pointWrite P₀ zeroBasisState))))).sum := by
    intro xs hnd hxsl
    induction xs with
    | nil => simp [normSq, Quantum.inner]
    | cons x xs ih =>
      have ⟨hxn, hnd'⟩ := List.nodup_cons.mp hnd
      have hxl : x.length = d.width := hxsl x List.mem_cons_self
      have hxsl' : ∀ y ∈ xs, y.length = d.width := fun y hy => hxsl y (List.mem_cons_of_mem _ hy)
      simp only [List.map_cons, List.sum_cons]
      have hzero : ((xs.map (fun input =>
          let P₀ := P' - Width16Schedule.increment (d.base Q) d.width d.exponent (boolWordToNat input);
          χ (phaseWordState d.bank input (pointWrite P₀ zeroBasisState)) •
            ket (phaseWordState d.bank input (pointWrite P₀ zeroBasisState)))).sum)
          (phaseWordState d.bank x (pointWrite (P' - Width16Schedule.increment (d.base Q) d.width d.exponent (boolWordToNat x)) zeroBasisState)) = 0 :=
        list_sum_eval_ket_not_mem xs _ _ _ (fun a ha hga =>
          hxn ((phaseWordState_bankW_inj d.k_hi (hxsl' a ha) hxl hga).2 ▸ ha))
      rw [normSq_add_ket _ _ _ hzero, ih hnd' hxsl']
  rw [hnorm_sum (fourierOutcomes d.width) (fourierOutcomes_nodup d.width) (fun x hx => (fourierOutcomes_mem d.width x).mp hx)]
  dsimp only [stepDistW]
  have hmul : ∀ (xs : List (List Bool)) (r : ℝ) (f : List Bool → ℝ),
      r * (xs.map f).sum = (xs.map (fun x => r * f x)).sum := fun xs r f => by
    induction xs with
    | nil => simp
    | cons x xs ih => simp [ih, mul_add]
  rw [hmul]
  apply congrArg List.sum; apply List.map_congr_left
  intro input hi
  have hlenW : input.length = d.width := (fourierOutcomes_mem d.width input).mp hi
  simp only [χ, Digit25.bank, Digit25.width]
  rw [hχ_eval _ input hlenW, map_mul, map_mul, sqrt2_inv_normSq_pow]
  dsimp only [pointMass]; ring

theorem zsmul_halfPow_eq_zero (e : Nat) (m : ℤ) (hm : |m| < (order : ℤ))
    (hz : m • ((halfOrder * 2 ^ e) • G) = 0) : m = 0 := by
  letI : Fact (Nat.Prime order) := ⟨order_prime⟩
  have ho : addOrderOf G = order := addOrderOf_eq_prime generator_nsmul_eq_zero G_ne_zero
  have hz' : (m * ((halfOrder * 2 ^ e : Nat) : ℤ)) • G = 0 := by
    simpa only [mul_zsmul, natCast_zsmul] using hz
  have hdvd : (order : ℤ) ∣ m * ((halfOrder * 2 ^ e : Nat) : ℤ) := by
    have := addOrderOf_dvd_iff_zsmul_eq_zero.mpr hz'
    rwa [ho] at this
  have hprimeZ : Prime (order : ℤ) := Nat.prime_iff_prime_int.mp order_prime
  rcases hprimeZ.dvd_or_dvd hdvd with hdm | hdh
  · by_contra hm0
    have hle : (order : ℤ) ≤ |m| := by
      have h1 : (order : ℤ) ∣ |m| := by
        rcases le_or_gt 0 m with h | h
        · rwa [abs_of_nonneg h]
        · rw [abs_of_neg h]; exact dvd_neg.mpr hdm
      exact Int.le_of_dvd (abs_pos.mpr hm0) h1
    omega
  · exfalso
    have hnat : order ∣ halfOrder * 2 ^ e := Int.natCast_dvd_natCast.mp hdh
    have horder : 2 < order := by norm_num [order]
    have hh : 0 < halfOrder ∧ halfOrder < order := by dsimp [Single.halfOrder]; omega
    rcases order_prime.dvd_mul.mp hnat with h1 | h2
    · exact (Nat.le_of_dvd hh.1 h1).not_gt hh.2
    · exact (Nat.le_of_dvd (by decide : 0 < 2) (order_prime.dvd_of_dvd_pow h2)).not_gt horder

def OddSupport (acc exp : Nat) (D : Point → ℝ) : Prop :=
  (∀ P, 0 ≤ D P) ∧
  (∀ P, D P ≤ 2 / (2 : ℝ) ^ acc) ∧
  (∀ P, D P ≠ 0 → ∃ m : ℤ, Odd m ∧ |m| < (2 : ℤ) ^ acc ∧
    -(2 : ℤ) ^ acc + (2 : ℤ) ^ (acc - 9) < m ∧
    P = m • ((halfOrder * 2 ^ exp) • G))

def MaxBound (M : ℝ) (D : Point → ℝ) : Prop :=
  (∀ P, 0 ≤ D P) ∧ (∀ P, D P ≤ M)

private theorem halfPow_shift (e w : Nat) :
    ((halfOrder * 2 ^ (e + w)) • G) = ((2 : ℤ) ^ w) • ((halfOrder * 2 ^ e) • G) := by
  have h : halfOrder * 2 ^ (e + w) = 2 ^ w * (halfOrder * 2 ^ e) := by rw [pow_add]; ring
  rw [h, mul_smul, show ((2 : ℤ) ^ w) = ((2 ^ w : Nat) : ℤ) by norm_cast, natCast_zsmul]

theorem oddSupport_badBound_zero (acc e w : Nat) (hw : 2 ≤ w) (hsum : acc + w ≤ 240)
    (D : Point → ℝ) (hD : OddSupport acc (e + w) D) :
    badBoundW w (fun _ => 1) (Width16Schedule.increment G w e) D = 0 := by
  unfold badBoundW
  have hzero : ∀ input ∈ fourierOutcomes w,
      let v := boolWordToNat input
      let Δ := Width16Schedule.increment G w e v
      Complex.normSq (1 : ℂ) * (D 0 + D Δ + D (-Δ) + D (-(Δ + Δ))) = 0 := by
    intro input hi
    set v := boolWordToNat input
    have hvlt : v < 2 ^ w := by
      have hlen : input.length = w := (fourierOutcomes_mem w input).mp hi
      simpa [hlen] using boolWordToNat_lt_pow_two input
    set H := (halfOrder * 2 ^ e) • G
    set r : ℤ := 2 * (v : ℤ) - (2 : ℤ) ^ w + 1
    have hpow2 : (2 : ℤ) ^ w = 2 * (2 : ℤ) ^ (w - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel (by omega)]
    have hpow4 : (2 : ℤ) ^ w = 4 * (2 : ℤ) ^ (w - 2) := by
      have : w = (w - 2) + 2 := by omega
      conv_lhs => rw [this]
      rw [pow_add]; ring
    have hr_odd : Odd r := ⟨(v : ℤ) - (2 : ℤ) ^ (w - 1), by dsimp [r]; rw [hpow2]; ring⟩
    have hr_abs : |r| < (2 : ℤ) ^ w := by
      have hvltZ : (v : ℤ) < (2 : ℤ) ^ w := by exact_mod_cast hvlt
      dsimp [r]; rw [abs_lt]; constructor <;> omega
    have hΔ : Width16Schedule.increment G w e v = r • H := rfl
    have hpow_lt : (2 : ℤ) ^ acc * (2 : ℤ) ^ w + 2 * (2 : ℤ) ^ w < (order : ℤ) := by
      rw [← pow_add]
      have h1 : (2 : ℤ) ^ (acc + w) ≤ (2 : ℤ) ^ 240 := pow_le_pow_right₀ (by decide) hsum
      have h2 : (2 : ℤ) ^ w ≤ (2 : ℤ) ^ 240 := pow_le_pow_right₀ (by decide) (by omega)
      have hord : (2 : ℤ) ^ 243 < (order : ℤ) := by norm_num [order]
      have h3 : (2 : ℤ) ^ 240 + 2 * (2 : ℤ) ^ 240 < (2 : ℤ) ^ 243 := by norm_num
      linarith
    have hD_eq_zero (c : ℤ) (hc_abs : |c| < 2 * (2 : ℤ) ^ w) (hbad : ∀ m : ℤ, Odd m → m * (2 : ℤ) ^ w ≠ c) :
        D (c • H) = 0 := by
      by_contra hne
      obtain ⟨m, hm_odd, hm_abs, _, hPm⟩ := hD.2.2 (c • H) hne
      rw [halfPow_shift e w, ← mul_zsmul] at hPm
      have hsub : (m * (2 : ℤ) ^ w - c) • H = 0 := by rw [sub_zsmul, ← hPm, add_neg_cancel]
      have habs : |m * (2 : ℤ) ^ w - c| < (order : ℤ) := by
        have htri := abs_sub (m * (2 : ℤ) ^ w) c
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < (2 : ℤ) ^ w)] at htri
        have hm1 : |m| * (2 : ℤ) ^ w ≤ (2 : ℤ) ^ acc * (2 : ℤ) ^ w :=
          mul_le_mul_of_nonneg_right hm_abs.le (by positivity)
        linarith
      have h0 := zsmul_halfPow_eq_zero e (m * (2 : ℤ) ^ w - c) habs hsub
      exact hbad m hm_odd (sub_eq_zero.mp h0)
    have h0 : D 0 = 0 := by
      have hpw_pos : (0 : ℤ) < (2 : ℤ) ^ w := by positivity
      simpa using hD_eq_zero 0 (by rw [abs_zero]; linarith) (fun m ⟨j, hj⟩ he => by
        have hm0 : m = 0 := (mul_eq_zero.mp he).resolve_right (ne_of_gt hpw_pos)
        omega)
    have h1 : D (r • H) = 0 :=
      hD_eq_zero r (by linarith) (fun m _ he => by
        obtain ⟨j, hj⟩ := hr_odd
        have h2 : 2 * (m * (2 : ℤ) ^ (w - 1)) = r := by rw [← he, hpow2]; ring
        omega)
    have h2 : D (-(r • H)) = 0 := by
      rw [← neg_zsmul]
      exact hD_eq_zero (-r) (by rw [abs_neg]; linarith) (fun m _ he => by
        obtain ⟨j, hj⟩ := hr_odd
        have h2 : 2 * (m * (2 : ℤ) ^ (w - 1)) = -r := by rw [← he, hpow2]; ring
        omega)
    have h3 : D (-(r • H + r • H)) = 0 := by
      have hrew : -(r • H + r • H) = (-2 * r) • H := by
        rw [← add_zsmul, ← neg_zsmul]; congr 1; ring
      rw [hrew]
      exact hD_eq_zero (-2 * r) (by rw [abs_mul]; norm_num; linarith)
        (fun m _ he => by
          obtain ⟨j, hj⟩ := hr_odd
          have h4 : 2 * (m * (2 : ℤ) ^ (w - 2)) = -r := by
            have : 2 * (2 * (m * (2 : ℤ) ^ (w - 2))) = -2 * r := by rw [← he, hpow4]; ring
            linarith
          omega)
    dsimp only; rw [hΔ, h0, h1, h2, h3]; ring
  rw [List.map_congr_left hzero]
  have hsum0 : ((fourierOutcomes w).map (fun _ => (0 : ℝ))).sum = 0 := by
    induction (fourierOutcomes w) with
    | nil => rfl
    | cons _ _ ih => simp [ih]
  rw [hsum0, mul_zero]

theorem oddSupport_stepDist (acc e w : Nat) (hacc : 9 ≤ acc) (hw : 2 ≤ w) (hsum : acc + w ≤ 240)
    (D : Point → ℝ) (hD : OddSupport acc (e + w) D) :
    OddSupport (acc + w) e (stepDistW w (fun _ => 1) (Width16Schedule.increment G w e) D) := by
  set H := (halfOrder * 2 ^ e) • G
  have hpow2 : (2 : ℤ) ^ w = 2 * (2 : ℤ) ^ (w - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega)]
  have hnn : ∀ P', 0 ≤ stepDistW w (fun _ => 1) (Width16Schedule.increment G w e) D P' := fun P' => by
    unfold stepDistW
    apply mul_nonneg (by positivity)
    apply List.sum_nonneg; intro x hx
    obtain ⟨inp, _, rfl⟩ := List.mem_map.mp hx
    exact mul_nonneg (Complex.normSq_nonneg _) (hD.1 _)
  have huniq : ∀ (P' : Point) (in₁ in₂ : List Bool),
      in₁ ∈ fourierOutcomes w → in₂ ∈ fourierOutcomes w →
      D (P' - Width16Schedule.increment G w e (boolWordToNat in₁)) ≠ 0 →
      D (P' - Width16Schedule.increment G w e (boolWordToNat in₂)) ≠ 0 →
      in₁ = in₂ := by
    intro P' in₁ in₂ h1 h2 hne1 hne2
    have hl1 : in₁.length = w := (fourierOutcomes_mem w in₁).mp h1
    have hl2 : in₂.length = w := (fourierOutcomes_mem w in₂).mp h2
    have hv1 : boolWordToNat in₁ < 2 ^ w := by simpa [hl1] using boolWordToNat_lt_pow_two in₁
    have hv2 : boolWordToNat in₂ < 2 ^ w := by simpa [hl2] using boolWordToNat_lt_pow_two in₂
    have hv1Z : (boolWordToNat in₁ : ℤ) < (2 : ℤ) ^ w := by exact_mod_cast hv1
    have hv2Z : (boolWordToNat in₂ : ℤ) < (2 : ℤ) ^ w := by exact_mod_cast hv2
    obtain ⟨m₁, hm1_odd, hm1_abs, _, hP1⟩ := hD.2.2 _ hne1
    obtain ⟨m₂, hm2_odd, hm2_abs, _, hP2⟩ := hD.2.2 _ hne2
    rw [halfPow_shift e w, ← mul_zsmul] at hP1 hP2
    set r₁ : ℤ := 2 * (boolWordToNat in₁ : ℤ) - (2 : ℤ) ^ w + 1
    set r₂ : ℤ := 2 * (boolWordToNat in₂ : ℤ) - (2 : ℤ) ^ w + 1
    have hP1' : P' = (m₁ * (2 : ℤ) ^ w + r₁) • H := by
      rw [add_zsmul, ← hP1]; exact (sub_add_cancel P' (r₁ • H)).symm
    have hP2' : P' = (m₂ * (2 : ℤ) ^ w + r₂) • H := by
      rw [add_zsmul, ← hP2]; exact (sub_add_cancel P' (r₂ • H)).symm
    have hdiff : ((m₁ - m₂) * (2 : ℤ) ^ w + (r₁ - r₂)) • H = 0 := by
      have : (m₁ - m₂) * (2 : ℤ) ^ w + (r₁ - r₂) = (m₁ * (2 : ℤ) ^ w + r₁) - (m₂ * (2 : ℤ) ^ w + r₂) := by ring
      rw [this, sub_zsmul, ← hP1', ← hP2', add_neg_cancel]
    have habs : |(m₁ - m₂) * (2 : ℤ) ^ w + (r₁ - r₂)| < (order : ℤ) := by
      have hm12 : |m₁ - m₂| < 2 * (2 : ℤ) ^ acc := by
        have := abs_sub m₁ m₂; linarith
      have hr12 : |r₁ - r₂| < 2 * (2 : ℤ) ^ w := by
        dsimp [r₁, r₂]; rw [abs_lt]; constructor <;> omega
      have htri := abs_add_le ((m₁ - m₂) * (2 : ℤ) ^ w) (r₁ - r₂)
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < (2 : ℤ) ^ w)] at htri
      have hbound : 2 * (2 : ℤ) ^ acc * (2 : ℤ) ^ w + 2 * (2 : ℤ) ^ w ≤ (order : ℤ) := by
        have hpa : (2 : ℤ) ^ acc * (2 : ℤ) ^ w = (2 : ℤ) ^ (acc + w) := (pow_add _ _ _).symm
        have hp1 : (2 : ℤ) ^ (acc + w) ≤ (2 : ℤ) ^ 240 := pow_le_pow_right₀ (by decide) hsum
        have hp2 : (2 : ℤ) ^ w ≤ (2 : ℤ) ^ 240 := pow_le_pow_right₀ (by decide) (by omega)
        have hord : (2 : ℤ) ^ 243 < (order : ℤ) := by norm_num [order]
        have h3 : 2 * (2 : ℤ) ^ 240 + 2 * (2 : ℤ) ^ 240 < (2 : ℤ) ^ 243 := by norm_num
        nlinarith
      have hmul : |m₁ - m₂| * (2 : ℤ) ^ w < 2 * (2 : ℤ) ^ acc * (2 : ℤ) ^ w :=
        mul_lt_mul_of_pos_right hm12 (by positivity)
      linarith
    have h0 := zsmul_halfPow_eq_zero e _ habs hdiff
    obtain ⟨j₁, hj1⟩ := hm1_odd
    obtain ⟨j₂, hj2⟩ := hm2_odd
    have hdiv_eq : (2 : ℤ) ^ w * (j₁ - j₂) + ((boolWordToNat in₁ : ℤ) - (boolWordToNat in₂ : ℤ)) = 0 := by
      have hsub : (m₁ - m₂) * (2 : ℤ) ^ w + (r₁ - r₂) =
          2 * ((2 : ℤ) ^ w * (j₁ - j₂) + ((boolWordToNat in₁ : ℤ) - (boolWordToNat in₂ : ℤ))) := by
        dsimp [r₁, r₂]; rw [hj1, hj2]; ring
      linarith
    have hj_eq : j₁ - j₂ = 0 := by
      by_contra hjne
      have h1 : (1 : ℤ) ≤ |j₁ - j₂| := by rw [le_abs]; omega
      have h2 : (2 : ℤ) ^ w ≤ |(2 : ℤ) ^ w * (j₁ - j₂)| := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < (2 : ℤ) ^ w)]
        nlinarith [pow_pos (by decide : (0 : ℤ) < 2) w]
      have h3 : (2 : ℤ) ^ w * (j₁ - j₂) = -((boolWordToNat in₁ : ℤ) - (boolWordToNat in₂ : ℤ)) := by linarith
      rw [h3, abs_neg] at h2
      have h4 : |(boolWordToNat in₁ : ℤ) - (boolWordToNat in₂ : ℤ)| < (2 : ℤ) ^ w := by
        rw [abs_lt]; constructor <;> omega
      linarith
    have hv_eq : boolWordToNat in₁ = boolWordToNat in₂ := by
      rw [hj_eq, mul_zero, zero_add] at hdiv_eq; omega
    exact boolWordToNat_injective (hl1.trans hl2.symm) hv_eq
  refine ⟨hnn, fun P' => ?_, fun P' hne => ?_⟩
  · have hsum_le (xs : List (List Bool)) (hnd : xs.Nodup) (hsub : ∀ x ∈ xs, x ∈ fourierOutcomes w) :
        (xs.map (fun inp => Complex.normSq (1 : ℂ) *
          D (P' - Width16Schedule.increment G w e (boolWordToNat inp)))).sum ≤
          2 / (2 : ℝ) ^ acc := by
      induction xs with
      | nil => simp; positivity
      | cons x xs ih =>
        have ⟨hxn, hnd'⟩ := List.nodup_cons.mp hnd
        simp only [List.map_cons, List.sum_cons]
        by_cases hdx : D (P' - Width16Schedule.increment G w e (boolWordToNat x)) = 0
        · rw [hdx, mul_zero, zero_add]
          exact ih hnd' (fun y hy => hsub y (List.mem_cons_of_mem _ hy))
        · have hrest0 : ∀ y ∈ xs, Complex.normSq (1 : ℂ) *
              D (P' - Width16Schedule.increment G w e (boolWordToNat y)) = 0 := by
            intro y hy
            have hdy : D (P' - Width16Schedule.increment G w e (boolWordToNat y)) = 0 := by
              by_contra hney
              exact hxn (huniq P' y x (hsub y (List.mem_cons_of_mem _ hy)) (hsub x List.mem_cons_self) hney hdx ▸ hy)
            rw [hdy, mul_zero]
          have hsum0 : (xs.map (fun inp => Complex.normSq (1 : ℂ) *
              D (P' - Width16Schedule.increment G w e (boolWordToNat inp)))).sum = 0 := by
            rw [List.map_congr_left hrest0]
            clear hrest0 ih hnd' hsub; induction xs with
            | nil => rfl
            | cons _ _ ih' => simp [ih']
          rw [hsum0, add_zero, map_one, one_mul]
          exact hD.2.1 _
    unfold stepDistW
    have h1 := hsum_le (fourierOutcomes w) (fourierOutcomes_nodup w) (fun _ h => h)
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (1 : ℝ) / (2 : ℝ) ^ w)
    refine h2.trans_eq ?_
    rw [pow_add]; ring
  · have hex : ∃ inp ∈ fourierOutcomes w,
        D (P' - Width16Schedule.increment G w e (boolWordToNat inp)) ≠ 0 := by
      by_contra hall
      push_neg at hall
      apply hne; unfold stepDistW
      have hz : ∀ inp ∈ fourierOutcomes w,
          Complex.normSq (1 : ℂ) * D (P' - Width16Schedule.increment G w e (boolWordToNat inp)) = 0 :=
        fun inp hi => by rw [hall inp hi, mul_zero]
      rw [List.map_congr_left hz]
      have hs0 : ((fourierOutcomes w).map (fun _ => (0 : ℝ))).sum = 0 := by
        induction (fourierOutcomes w) with
        | nil => rfl
        | cons _ _ ih => simp [ih]
      rw [hs0, mul_zero]
    obtain ⟨inp, hi, hdi⟩ := hex
    have hl : inp.length = w := (fourierOutcomes_mem w inp).mp hi
    have hv : boolWordToNat inp < 2 ^ w := by simpa [hl] using boolWordToNat_lt_pow_two inp
    have hvZ : (boolWordToNat inp : ℤ) < (2 : ℤ) ^ w := by exact_mod_cast hv
    obtain ⟨m, hm_odd, hm_abs, hm_lo, hPm⟩ := hD.2.2 _ hdi
    rw [halfPow_shift e w, ← mul_zsmul] at hPm
    set r : ℤ := 2 * (boolWordToNat inp : ℤ) - (2 : ℤ) ^ w + 1
    refine ⟨m * (2 : ℤ) ^ w + r, ?_, ?_, ?_, ?_⟩
    · refine ⟨m * (2 : ℤ) ^ (w - 1) + (boolWordToNat inp : ℤ) - (2 : ℤ) ^ (w - 1), ?_⟩
      dsimp [r]; rw [hpow2]; ring
    · rw [pow_add]
      have hr_abs : |r| < (2 : ℤ) ^ w := by dsimp [r]; rw [abs_lt]; constructor <;> omega
      have htri := abs_add_le (m * (2 : ℤ) ^ w) r
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < (2 : ℤ) ^ w)] at htri
      have hm1 : |m| ≤ (2 : ℤ) ^ acc - 1 := by omega
      have hmul : |m| * (2 : ℤ) ^ w ≤ ((2 : ℤ) ^ acc - 1) * (2 : ℤ) ^ w :=
        mul_le_mul_of_nonneg_right hm1 (by positivity)
      linarith
    · have hm_lo' : -(2 : ℤ) ^ acc + (2 : ℤ) ^ (acc - 9) + 1 ≤ m := by omega
      have hr_lo : -(2 : ℤ) ^ w + 1 ≤ r := by dsimp [r]; omega
      have hpow_sub : (2 : ℤ) ^ (acc - 9) * (2 : ℤ) ^ w = (2 : ℤ) ^ (acc + w - 9) := by
        rw [← pow_add, show acc - 9 + w = acc + w - 9 by omega]
      have hmul_lo : (-(2 : ℤ) ^ acc + (2 : ℤ) ^ (acc - 9) + 1) * (2 : ℤ) ^ w ≤ m * (2 : ℤ) ^ w :=
        mul_le_mul_of_nonneg_right hm_lo' (by positivity)
      rw [pow_add]
      linarith
    · rw [add_zsmul, ← hPm]
      exact (sub_add_cancel P' (r • H)).symm

private theorem oddSupport_stepDist_last_aux (w : Nat) (hw : w = 19) (D : Point → ℝ) (hD : OddSupport 237 w D) :
    MaxBound (2 / (2 : ℝ) ^ (237 + w))
      (stepDistW w (fun _ => 1) (Width16Schedule.increment G w 0) D) := by
  set H := (halfOrder * 2 ^ 0) • G
  have h2h : (2 * halfOrder) • G = G := by
    have h : 2 * halfOrder = order + 1 := by norm_num [Single.halfOrder, order]
    rw [h, add_nsmul, one_nsmul, generator_nsmul_eq_zero, zero_add]
  have hnn : ∀ P', 0 ≤ stepDistW w (fun _ => 1) (Width16Schedule.increment G w 0) D P' := fun P' => by
    unfold stepDistW
    apply mul_nonneg (by positivity)
    apply List.sum_nonneg; intro x hx
    obtain ⟨inp, _, rfl⟩ := List.mem_map.mp hx
    exact mul_nonneg (Complex.normSq_nonneg _) (hD.1 _)
  have huniq : ∀ (P' : Point) (in₁ in₂ : List Bool),
      in₁ ∈ fourierOutcomes w → in₂ ∈ fourierOutcomes w →
      D (P' - Width16Schedule.increment G w 0 (boolWordToNat in₁)) ≠ 0 →
      D (P' - Width16Schedule.increment G w 0 (boolWordToNat in₂)) ≠ 0 →
      in₁ = in₂ := by
    intro P' in₁ in₂ h1 h2 hne1 hne2
    have hl1 : in₁.length = w := (fourierOutcomes_mem w in₁).mp h1
    have hl2 : in₂.length = w := (fourierOutcomes_mem w in₂).mp h2
    have hv1 : boolWordToNat in₁ < 2 ^ w := by simpa [hl1] using boolWordToNat_lt_pow_two in₁
    have hv2 : boolWordToNat in₂ < 2 ^ w := by simpa [hl2] using boolWordToNat_lt_pow_two in₂
    have hv1Z : (boolWordToNat in₁ : ℤ) < (2 : ℤ) ^ w := by exact_mod_cast hv1
    have hv2Z : (boolWordToNat in₂ : ℤ) < (2 : ℤ) ^ w := by exact_mod_cast hv2
    obtain ⟨m₁, ⟨j₁, hj1⟩, hm1_abs, hm1_lo, hP1⟩ := hD.2.2 _ hne1
    obtain ⟨m₂, ⟨j₂, hj2⟩, hm2_abs, hm2_lo, hP2⟩ := hD.2.2 _ hne2
    have hsh : ((halfOrder * 2 ^ w) • G) = ((2 : ℤ) ^ w) • H := by
      simpa only [Nat.zero_add] using halfPow_shift 0 w
    rw [hsh, ← mul_zsmul] at hP1 hP2
    set r₁ : ℤ := 2 * (boolWordToNat in₁ : ℤ) - (2 : ℤ) ^ w + 1
    set r₂ : ℤ := 2 * (boolWordToNat in₂ : ℤ) - (2 : ℤ) ^ w + 1
    have hP1' : P' = (m₁ * (2 : ℤ) ^ w + r₁) • H := by
      rw [add_zsmul, ← hP1]; exact (sub_add_cancel P' (r₁ • H)).symm
    have hP2' : P' = (m₂ * (2 : ℤ) ^ w + r₂) • H := by
      rw [add_zsmul, ← hP2]; exact (sub_add_cancel P' (r₂ • H)).symm
    set t : ℤ := (2 : ℤ) ^ w * (j₁ - j₂) + ((boolWordToNat in₁ : ℤ) - (boolWordToNat in₂ : ℤ))
    have h2t_eq : (m₁ - m₂) * (2 : ℤ) ^ w + (r₁ - r₂) = 2 * t := by
      dsimp [r₁, r₂, t]; rw [hj1, hj2]; ring
    have hdiff : (2 * t) • H = 0 := by
      have : 2 * t = (m₁ * (2 : ℤ) ^ w + r₁) - (m₂ * (2 : ℤ) ^ w + r₂) := by linarith
      rw [this, sub_zsmul, ← hP1', ← hP2', add_neg_cancel]
    have htG : t • G = 0 := by
      have hrew : (2 * t) • H = t • G := by
        have h1 : (2 : ℤ) • H = G := by
          dsimp only [H]
          rw [pow_zero, mul_one, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, natCast_zsmul, ← mul_nsmul, Nat.mul_comm, h2h]
        rw [show (2 * t : ℤ) = t * 2 by ring, mul_zsmul, h1]
      exact hrew.symm.trans hdiff
    have hj_bound : |j₁ - j₂| ≤ (2 : ℤ) ^ 237 - (2 : ℤ) ^ 227 - 1 := by
      have hm1_hi : m₁ ≤ (2 : ℤ) ^ 237 - 1 := Int.le_sub_one_of_lt (abs_lt.mp hm1_abs).2
      have hm2_hi : m₂ ≤ (2 : ℤ) ^ 237 - 1 := Int.le_sub_one_of_lt (abs_lt.mp hm2_abs).2
      have hpow228 : (2 : ℤ) ^ 228 = 2 * (2 : ℤ) ^ 227 := by ring
      rw [show (237 : Nat) - 9 = 228 from rfl] at hm1_lo hm2_lo
      rw [abs_le]; constructor <;> linarith
    have htabs : |t| < (order : ℤ) := by
      have hv_bound : |(boolWordToNat in₁ : ℤ) - (boolWordToNat in₂ : ℤ)| ≤ (2 : ℤ) ^ w - 1 := by
        have h1lo : (0 : ℤ) ≤ (boolWordToNat in₁ : ℤ) := Int.natCast_nonneg _
        have h2lo : (0 : ℤ) ≤ (boolWordToNat in₂ : ℤ) := Int.natCast_nonneg _
        have h1hi : (boolWordToNat in₁ : ℤ) ≤ (2 : ℤ) ^ w - 1 := Int.le_sub_one_of_lt hv1Z
        have h2hi : (boolWordToNat in₂ : ℤ) ≤ (2 : ℤ) ^ w - 1 := Int.le_sub_one_of_lt hv2Z
        rw [abs_le]; constructor <;> linarith
      have htri := abs_add_le ((2 : ℤ) ^ w * (j₁ - j₂)) ((boolWordToNat in₁ : ℤ) - (boolWordToNat in₂ : ℤ))
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < (2 : ℤ) ^ w)] at htri
      have hmul : (2 : ℤ) ^ w * |j₁ - j₂| ≤ (2 : ℤ) ^ w * ((2 : ℤ) ^ 237 - (2 : ℤ) ^ 227 - 1) :=
        mul_le_mul_of_nonneg_left hj_bound (by positivity)
      have hord : (2 : ℤ) ^ w * ((2 : ℤ) ^ 237 - (2 : ℤ) ^ 227 - 1) + ((2 : ℤ) ^ w - 1) < (order : ℤ) := by
        rw [hw]; norm_num [order]
      linarith
    have ht0 : t = 0 := by
      letI : Fact (Nat.Prime order) := ⟨order_prime⟩
      have ho : addOrderOf G = order := addOrderOf_eq_prime generator_nsmul_eq_zero G_ne_zero
      have hdvd : (order : ℤ) ∣ t := by
        have := addOrderOf_dvd_iff_zsmul_eq_zero.mpr htG
        rwa [ho] at this
      by_contra hne
      have hle : (order : ℤ) ≤ |t| := by
        have h1 : (order : ℤ) ∣ |t| := by
          rcases le_or_gt 0 t with h | h
          · rwa [abs_of_nonneg h]
          · rw [abs_of_neg h]; exact dvd_neg.mpr hdvd
        exact Int.le_of_dvd (abs_pos.mpr hne) h1
      linarith
    have hj_eq : j₁ - j₂ = 0 := by
      by_contra hjne
      have h1 : (1 : ℤ) ≤ |j₁ - j₂| := Int.one_le_abs hjne
      have h2 : (2 : ℤ) ^ w ≤ |(2 : ℤ) ^ w * (j₁ - j₂)| := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < (2 : ℤ) ^ w)]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℤ) ≤ (2 : ℤ) ^ w)
      have h3 : (2 : ℤ) ^ w * (j₁ - j₂) = -((boolWordToNat in₁ : ℤ) - (boolWordToNat in₂ : ℤ)) := by
        dsimp [t] at ht0; linarith
      rw [h3, abs_neg] at h2
      have h4 : |(boolWordToNat in₁ : ℤ) - (boolWordToNat in₂ : ℤ)| < (2 : ℤ) ^ w := by
        have h1lo : (0 : ℤ) ≤ (boolWordToNat in₁ : ℤ) := Int.natCast_nonneg _
        have h2lo : (0 : ℤ) ≤ (boolWordToNat in₂ : ℤ) := Int.natCast_nonneg _
        rw [abs_lt]; constructor <;> linarith
      linarith
    have hv_eq : boolWordToNat in₁ = boolWordToNat in₂ := by
      dsimp [t] at ht0; rw [hj_eq, mul_zero, zero_add] at ht0
      exact Int.ofNat.inj (sub_eq_zero.mp ht0)
    exact boolWordToNat_injective (hl1.trans hl2.symm) hv_eq
  refine ⟨hnn, fun P' => ?_⟩
  have hsum_le (xs : List (List Bool)) (hnd : xs.Nodup) (hsub : ∀ x ∈ xs, x ∈ fourierOutcomes w) :
      (xs.map (fun inp => Complex.normSq (1 : ℂ) *
        D (P' - Width16Schedule.increment G w 0 (boolWordToNat inp)))).sum ≤
        2 / (2 : ℝ) ^ 237 := by
    induction xs with
    | nil => simp; positivity
    | cons x xs ih =>
      have ⟨hxn, hnd'⟩ := List.nodup_cons.mp hnd
      simp only [List.map_cons, List.sum_cons]
      by_cases hdx : D (P' - Width16Schedule.increment G w 0 (boolWordToNat x)) = 0
      · rw [hdx, mul_zero, zero_add]
        exact ih hnd' (fun y hy => hsub y (List.mem_cons_of_mem _ hy))
      · have hrest0 : ∀ y ∈ xs, Complex.normSq (1 : ℂ) *
            D (P' - Width16Schedule.increment G w 0 (boolWordToNat y)) = 0 := by
          intro y hy
          have hdy : D (P' - Width16Schedule.increment G w 0 (boolWordToNat y)) = 0 := by
            by_contra hney
            exact hxn (huniq P' y x (hsub y (List.mem_cons_of_mem _ hy)) (hsub x List.mem_cons_self) hney hdx ▸ hy)
          rw [hdy, mul_zero]
        have hsum0 : (xs.map (fun inp => Complex.normSq (1 : ℂ) *
            D (P' - Width16Schedule.increment G w 0 (boolWordToNat inp)))).sum = 0 := by
          rw [List.map_congr_left hrest0]
          clear hrest0 ih hnd' hsub hnd hxn; induction xs with
          | nil => rfl
          | cons _ _ ih' => simp only [List.map_cons, List.sum_cons, ih', zero_add]
        rw [hsum0, add_zero, map_one, one_mul]
        exact hD.2.1 _
  unfold stepDistW
  have h1 := hsum_le (fourierOutcomes w) (fourierOutcomes_nodup w) (fun _ h => h)
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (1 : ℝ) / (2 : ℝ) ^ w)
  refine h2.trans_eq ?_
  rw [pow_add]; ring

private theorem oddSupport_stepDist_last (D : Point → ℝ) (hD : OddSupport 237 19 D) :
    MaxBound (2 / (2 : ℝ) ^ 256)
      (stepDistW 19 (fun _ => 1) (Width16Schedule.increment G 19 0) D) :=
  oddSupport_stepDist_last_aux 19 rfl D hD

private theorem fourierOutcomes_length_eq (k : Nat) : (fourierOutcomes k).length = 2 ^ k := by
  induction k with
  | zero => simp [fourierOutcomes]
  | succ k ih => simp [fourierOutcomes, ih, pow_succ]; omega

private theorem sum_fourierOutcomes_one (w : Nat) :
    ((fourierOutcomes w).map (fun _ => Complex.normSq (1 : ℂ))).sum = (2 : ℝ) ^ w := by
  have hmap : (fourierOutcomes w).map (fun _ => Complex.normSq (1 : ℂ)) =
      List.replicate (fourierOutcomes w).length (1 : ℝ) := by
    simp [List.map_const']
  rw [hmap, List.sum_replicate, nsmul_eq_mul, mul_one, fourierOutcomes_length_eq]
  norm_cast

private theorem sum_fourierOutcomes17_sine :
    ((fourierOutcomes 17).map (fun input =>
      Complex.normSq (sineWeight 10 (boolWordToNat input / 2 ^ 7)))).sum = (2 : ℝ) ^ 17 := by
  rw [show (17 : Nat) = 7 + 10 from rfl, fourierOutcomes_add 7 10, flatMap_sum_real]
  have hinner : ∀ a ∈ fourierOutcomes 7,
      ((fourierOutcomes 10).map (fun b =>
        Complex.normSq (sineWeight 10 (boolWordToNat (a ++ b) / 2 ^ 7)))).sum = 1024 := by
    intro a ha
    have hal : a.length = 7 := (fourierOutcomes_mem 7 a).mp ha
    have hcongr : ∀ b ∈ fourierOutcomes 10,
        Complex.normSq (sineWeight 10 (boolWordToNat (a ++ b) / 2 ^ 7)) =
          Complex.normSq (sineWeight 10 (boolWordToNat b)) := by
      intro b _
      rw [boolWordToNat_append, hal, Nat.add_mul_div_left _ _ (by decide : 0 < 2 ^ 7),
        Nat.div_eq_of_lt (by simpa [hal] using boolWordToNat_lt_pow_two a), Nat.zero_add]
    rw [List.map_congr_left hcongr]
    have hfin : ((fourierOutcomes 10).map (fun b => Complex.normSq (sineWeight 10 (boolWordToNat b)))).sum =
        ∑ u ∈ Finset.range 1024, Complex.normSq (sineWeight 10 u) :=
      list_sum_fourierOutcomes_eq_range 10 (fun u => Complex.normSq (sineWeight 10 u))
    rw [hfin, SineBounds.sineWeight_sum_normSq]
  simp only [List.map_map, Function.comp_def]
  rw [List.map_congr_left hinner]
  have hrep : (fourierOutcomes 7).map (fun _ => (1024 : ℝ)) =
      List.replicate (fourierOutcomes 7).length (1024 : ℝ) := by simp [List.map_const']
  rw [hrep, List.sum_replicate, nsmul_eq_mul, fourierOutcomes_length_eq]
  norm_num

theorem maxBound_stepDistW (w : Nat) (wpre : Nat → ℂ) (delta : Nat → Point) (M : ℝ) (hM : 0 ≤ M)
    (hw : ((fourierOutcomes w).map (fun inp => Complex.normSq (wpre (boolWordToNat inp)))).sum = (2 : ℝ) ^ w)
    (D : Point → ℝ) (hD : MaxBound M D) :
    MaxBound M (stepDistW w wpre delta D) := by
  refine ⟨fun P' => ?_, fun P' => ?_⟩
  · unfold stepDistW
    apply mul_nonneg (by positivity)
    apply List.sum_nonneg; intro x hx
    obtain ⟨inp, _, rfl⟩ := List.mem_map.mp hx
    exact mul_nonneg (Complex.normSq_nonneg _) (hD.1 _)
  · unfold stepDistW
    have h1 : ((fourierOutcomes w).map (fun inp =>
        Complex.normSq (wpre (boolWordToNat inp)) * D (P' - delta (boolWordToNat inp)))).sum ≤
        ((fourierOutcomes w).map (fun inp => Complex.normSq (wpre (boolWordToNat inp)) * M)).sum := by
      apply list_sum_map_le; intro inp _
      exact mul_le_mul_of_nonneg_left (hD.2 _) (Complex.normSq_nonneg _)
    have hmr : ∀ (xs : List (List Bool)) (f : List Bool → ℝ) (r : ℝ),
        (xs.map (fun x => f x * r)).sum = (xs.map f).sum * r := fun xs f r => by
      induction xs with
      | nil => simp
      | cons x xs ih => simp [ih, add_mul]
    rw [hmr, hw] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (1 : ℝ) / (2 : ℝ) ^ w)
    refine h2.trans_eq ?_; field_simp

theorem maxBound_badBoundW (w : Nat) (wpre : Nat → ℂ) (delta : Nat → Point) (M : ℝ) (hM : 0 ≤ M)
    (hw : ((fourierOutcomes w).map (fun inp => Complex.normSq (wpre (boolWordToNat inp)))).sum = (2 : ℝ) ^ w)
    (D : Point → ℝ) (hD : MaxBound M D) :
    badBoundW w wpre delta D ≤ 4 * M := by
  unfold badBoundW
  have h1 : ((fourierOutcomes w).map (fun inp =>
      let v := boolWordToNat inp
      let Δ := delta v
      Complex.normSq (wpre v) * (D 0 + D Δ + D (-Δ) + D (-(Δ + Δ))))).sum ≤
      ((fourierOutcomes w).map (fun inp => Complex.normSq (wpre (boolWordToNat inp)) * (4 * M))).sum := by
    apply list_sum_map_le; intro inp _
    apply mul_le_mul_of_nonneg_left _ (Complex.normSq_nonneg _)
    linarith [hD.2 0, hD.2 (delta (boolWordToNat inp)), hD.2 (-delta (boolWordToNat inp)),
      hD.2 (-(delta (boolWordToNat inp) + delta (boolWordToNat inp)))]
  have hmr : ∀ (xs : List (List Bool)) (f : List Bool → ℝ) (r : ℝ),
      (xs.map (fun x => f x * r)).sum = (xs.map f).sum * r := fun xs f r => by
    induction xs with
    | nil => simp
    | cons x xs ih => simp [ih, add_mul]
  rw [hmr, hw] at h1
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (1 : ℝ) / (2 : ℝ) ^ w)
  refine h2.trans_eq ?_; field_simp

private theorem maxBound_badBoundW96 (w : Nat) (wpre : Nat → ℂ) (delta : Nat → Point) (M : ℝ) (hM : 0 ≤ M)
    (hw : ((fourierOutcomes w).map (fun inp => Complex.normSq (wpre (boolWordToNat inp)))).sum = (2 : ℝ) ^ w)
    (D : Point → ℝ) (hD : MaxBound M D) :
    badBoundW96 w wpre delta D ≤ (4 + 4 * (SkywalkTail485.Bad485.card : ℝ)) * M := by
  unfold badBoundW96
  have hconst : ∀ (ps : List Point) (r : ℝ), (ps.map (fun _ => r)).sum = (ps.length : ℝ) * r := fun ps r => by
    induction ps with
    | nil => simp
    | cons _ ps ih => simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one, ih]; ring
  have h1 : ((fourierOutcomes w).map (fun inp =>
      let v := boolWordToNat inp
      Complex.normSq (wpre v) * ((badList96 (delta v)).map D).sum)).sum ≤
      ((fourierOutcomes w).map (fun inp =>
        Complex.normSq (wpre (boolWordToNat inp)) * ((4 + 4 * (SkywalkTail485.Bad485.card : ℝ)) * M))).sum := by
    apply list_sum_map_le; intro inp _
    apply mul_le_mul_of_nonneg_left _ (Complex.normSq_nonneg _)
    have hsum : ((badList96 (delta (boolWordToNat inp))).map D).sum ≤
        ((badList96 (delta (boolWordToNat inp))).length : ℝ) * M :=
      (list_sum_map_le _ D (fun _ => M) (fun P _ => hD.2 P)).trans_eq (hconst _ M)
    have hcard : ((badList96 (delta (boolWordToNat inp))).length : ℝ) ≤ 4 + 4 * (SkywalkTail485.Bad485.card : ℝ) := by
      exact_mod_cast badList96_length_le (delta (boolWordToNat inp))
    exact hsum.trans (mul_le_mul_of_nonneg_right hcard hM)
  have hmr : ∀ (xs : List (List Bool)) (f : List Bool → ℝ) (r : ℝ),
      (xs.map (fun x => f x * r)).sum = (xs.map f).sum * r := fun xs f r => by
    induction xs with
    | nil => simp
    | cons x xs ih => simp [ih, add_mul]
  rw [hmr, hw] at h1
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (1 : ℝ) / (2 : ℝ) ^ w)
  refine h2.trans_eq ?_; field_simp

/-! ### Initial `First20` distribution (`OddSupport 20 236`) and full `52 / 2^236` exception bound -/

theorem first20Model_step_pointSupported (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (prior bits : List Bool) :
    PointSupported ((first20Model Q hQ hn).step prior bits (ket zeroBasisState)) := by
  rw [(first20Model_rule Q hQ hn).2 prior bits]
  apply Support.smul; apply Support.list_sum; intro input _
  exact Support.smul _ (supportedOn_ket _ _ ⟨_, rfl⟩)

theorem bodyModel_step_pointSupported (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (d : Digit25)
    (prior bits : List Bool) (φ : State) (hφ : PointSupported φ) :
    PointSupported ((bodyModel Q hQ hn d).step prior bits φ) := by
  refine Support.linear (pointFamily zeroBasisState) (pointFamily zeroBasisState)
    ((bodyModel Q hQ hn d).step prior bits) ?_ φ hφ
  intro s hs; obtain ⟨P, rfl⟩ := hs
  rw [bodyModel_rule Q hQ hn d prior bits P]
  apply Support.smul; apply Support.list_sum; intro input _
  exact Support.smul _ (supportedOn_ket _ _ ⟨_, rfl⟩)

theorem rightHeadModel_step_pointSupported (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (prior bits : List Bool) (φ : State) (hφ : PointSupported φ) :
    PointSupported ((rightHeadModel Q hQ hn).step prior bits φ) := by
  refine Support.linear (pointFamily zeroBasisState) (pointFamily zeroBasisState)
    ((rightHeadModel Q hQ hn).step prior bits) ?_ φ hφ
  intro s hs; obtain ⟨P, rfl⟩ := hs
  rw [(rightHeadModel_rule Q hQ hn).2 prior bits P]
  apply Support.smul; apply Support.list_sum; intro input _
  exact Support.smul _ (supportedOn_ket _ _ ⟨_, rfl⟩)

theorem first20_pointMass_sum_oddSupport (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) :
    OddSupport 20 236 (fun P' =>
      ((fourierOutcomes 20).map (fun bits =>
        pointMass ((first20Model Q hQ hn).step List.nil bits (ket zeroBasisState)) P')).sum) := by
  classical
  let φ₀ := (first20Model Q hQ hn).ideal (Quantum.run (First20Signed.bits.reverse.reverse.map Gate.H) (ket zeroBasisState))
  have hdrop : First20Signed.bits.drop (First20Signed.bits.length - 10) = top10Left := by
    simp [top10Left, First20Signed.bits_length]
  have hφ₀_exp : φ₀ = (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 20) •
      ((fourierOutcomes 20).map (fun input =>
        sineWeight 10 (boolWordToNat input / 2 ^ 10) •
          ket (pointWrite (initialPoint25 Q (boolWordToNat input))
            (phaseWordState First20Signed.bits input zeroBasisState)))).sum := by
    change Finsupp.lmapDomain ℂ ℂ (First20Signed.update initialPoint25 Q)
      (Quantum.run (sineFromPlus top10Left)
        (Quantum.run (First20Signed.bits.reverse.reverse.map Gate.H) (ket zeroBasisState))) = _
    rw [List.reverse_reverse]
    have hsb := sineFromPlus_bank First20Signed.bits (by simp [First20Signed.bits_length])
      First20Signed.bits_nodup zeroBasisState zeroBasisState_clean20
    rw [hdrop, First20Signed.bits_length, show (20 : Nat) - 10 = 10 from rfl] at hsb
    rw [hsb, map_smul, stateLinear_list_sum, List.map_map]
    apply congrArg (fun x => (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 20) • x)
    apply congrArg List.sum; apply List.map_congr_left
    intro input hi
    have hlen : input.length = First20Signed.bits.length := by
      simpa [First20Signed.bits_length] using (fourierOutcomes_mem 20 input).mp hi
    simp only [Function.comp_def, map_smul, Mixed.lmap_ket']
    have hupd : First20Signed.update initialPoint25 Q (phaseWordState First20Signed.bits input zeroBasisState) =
        pointWrite (initialPoint25 Q (boolWordToNat input)) (phaseWordState First20Signed.bits input zeroBasisState) := by
      unfold First20Signed.update
      rw [WEX.tableAddress_word, phaseWordState_word First20Signed.bits First20Signed.bits_nodup input hlen]
    rw [hupd]
  have hinit_inj : ∀ (a b : List Bool), a ∈ fourierOutcomes 20 → b ∈ fourierOutcomes 20 →
      initialPoint25 Q (boolWordToNat a) = initialPoint25 Q (boolWordToNat b) → a = b := by
    intro a b ha hb heq
    have hla : a.length = 20 := (fourierOutcomes_mem 20 a).mp ha
    have hlb : b.length = 20 := (fourierOutcomes_mem 20 b).mp hb
    have hva : boolWordToNat a < 2 ^ 20 := by simpa [hla] using boolWordToNat_lt_pow_two a
    have hvb : boolWordToNat b < 2 ^ 20 := by simpa [hlb] using boolWordToNat_lt_pow_two b
    have hsub : (2 * ((boolWordToNat a : ℤ) - (boolWordToNat b : ℤ))) • ((halfOrder * 2 ^ 236) • G) = 0 := by
      have hc : (2 * (boolWordToNat a : ℤ) - (2 : ℤ) ^ 20 + 1) - (2 * (boolWordToNat b : ℤ) - (2 : ℤ) ^ 20 + 1) =
          2 * ((boolWordToNat a : ℤ) - (boolWordToNat b : ℤ)) := by ring
      rw [← hc, sub_zsmul]
      exact sub_eq_zero.mpr heq
    have habs : |2 * ((boolWordToNat a : ℤ) - (boolWordToNat b : ℤ))| < (order : ℤ) := by
      have hord : (2 : ℤ) ^ 22 < (order : ℤ) := by norm_num [order]
      rw [abs_lt]; constructor <;> omega
    have h0 := zsmul_halfPow_eq_zero 236 _ habs hsub
    exact boolWordToNat_injective (hla.trans hlb.symm) (by omega)
  have hsum_eq (P' : Point) :
      ((fourierOutcomes 20).map (fun bits =>
        pointMass ((first20Model Q hQ hn).step List.nil bits (ket zeroBasisState)) P')).sum =
      normSq (restrictState (fun s => pointStateCoordinates s = fig14PointEncoding P') φ₀) := by
    have hper : ∀ bits ∈ fourierOutcomes 20,
        pointMass ((first20Model Q hQ hn).step List.nil bits (ket zeroBasisState)) P' =
          normSq (fourierBranch .inverse First20Signed.bits.reverse List.nil bits
            (restrictState (fun s => pointStateCoordinates s = fig14PointEncoding P') φ₀)) := by
      intro bits _
      rw [pointMass_eq_normSq_projPoint _ (first20Model_step_pointSupported Q hQ hn List.nil bits) P']
      change normSq (restrictState _ (fourierBranch .inverse First20Signed.bits.reverse List.nil bits φ₀)) = _
      rw [projPoint_fourierBranch_comm First20Signed.bits.reverse
        (fun w hw => First20Signed.bits_not_point w (List.mem_reverse.mp hw))]
    rw [List.map_congr_left hper]
    simpa [First20Signed.bits_length] using
      normSq_list_sum_fourierBranch .inverse First20Signed.bits.reverse List.nil
        (restrictState (fun s => pointStateCoordinates s = fig14PointEncoding P') φ₀)
  have hproj (P' : Point) :
      restrictState (fun s => pointStateCoordinates s = fig14PointEncoding P') φ₀ =
        if h : ∃ inp ∈ fourierOutcomes 20, initialPoint25 Q (boolWordToNat inp) = P' then
          (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 20 * sineWeight 10 (boolWordToNat (Classical.choose h) / 2 ^ 10)) •
            ket (pointWrite P' (phaseWordState First20Signed.bits (Classical.choose h) zeroBasisState))
        else 0 := by
    rw [hφ₀_exp, restrictState_map_smul]
    have hmap_res : ∀ xs : List (List Bool),
        restrictState (fun s => pointStateCoordinates s = fig14PointEncoding P')
          ((xs.map (fun input =>
            sineWeight 10 (boolWordToNat input / 2 ^ 10) •
              ket (pointWrite (initialPoint25 Q (boolWordToNat input))
                (phaseWordState First20Signed.bits input zeroBasisState)))).sum) =
        (xs.map (fun input =>
          if initialPoint25 Q (boolWordToNat input) = P' then
            sineWeight 10 (boolWordToNat input / 2 ^ 10) •
              ket (pointWrite P' (phaseWordState First20Signed.bits input zeroBasisState))
          else 0)).sum := by
      intro xs; induction xs with
      | nil => ext s; simp [restrictState_apply]
      | cons x xs ih =>
        simp only [List.map_cons, List.sum_cons, restrictState_map_add, ih, restrictState_map_smul,
          restrictState_ket, pointWrite_coordinates]
        by_cases he : initialPoint25 Q (boolWordToNat x) = P'
        · simp [he]
        · have hne : fig14PointEncoding (initialPoint25 Q (boolWordToNat x)) ≠ fig14PointEncoding P' :=
            fun h => he (fig14PointEncoding_injective h)
          simp [he, hne]
    rw [hmap_res]
    by_cases hex : ∃ inp ∈ fourierOutcomes 20, initialPoint25 Q (boolWordToNat inp) = P'
    · rw [dif_pos hex]
      set inp₀ := Classical.choose hex
      have hinp₀_mem : inp₀ ∈ fourierOutcomes 20 := (Classical.choose_spec hex).1
      have hinp₀_eq : initialPoint25 Q (boolWordToNat inp₀) = P' := (Classical.choose_spec hex).2
      have hsingle : ∀ (xs : List (List Bool)), xs.Nodup → (∀ x ∈ xs, x ∈ fourierOutcomes 20) →
          inp₀ ∈ xs →
          (xs.map (fun input =>
            if initialPoint25 Q (boolWordToNat input) = P' then
              sineWeight 10 (boolWordToNat input / 2 ^ 10) •
                ket (pointWrite P' (phaseWordState First20Signed.bits input zeroBasisState))
            else 0)).sum =
          sineWeight 10 (boolWordToNat inp₀ / 2 ^ 10) •
            ket (pointWrite P' (phaseWordState First20Signed.bits inp₀ zeroBasisState)) := by
        intro xs hnd hsub hmem
        induction xs with
        | nil => cases hmem
        | cons x xs ih =>
          have ⟨hxn, hnd'⟩ := List.nodup_cons.mp hnd
          simp only [List.map_cons, List.sum_cons]
          rcases List.mem_cons.mp hmem with rfl | hm
          · have hrest : ∀ y ∈ xs,
                (if initialPoint25 Q (boolWordToNat y) = P' then
                  sineWeight 10 (boolWordToNat y / 2 ^ 10) •
                    ket (pointWrite P' (phaseWordState First20Signed.bits y zeroBasisState))
                else 0) = 0 := by
              intro y hy
              rw [if_neg]
              intro he
              exact hxn (hinit_inj y inp₀ (hsub y (List.mem_cons_of_mem _ hy)) (hsub inp₀ List.mem_cons_self)
                (he.trans hinp₀_eq.symm) ▸ hy)
            rw [if_pos hinp₀_eq, List.map_congr_left hrest]
            have hz : (xs.map (fun _ => (0 : State))).sum = 0 := by
              clear hrest ih hnd' hsub; induction xs with | nil => rfl | cons _ _ ih' => simp [ih']
            rw [hz, add_zero]
          · have hne : initialPoint25 Q (boolWordToNat x) ≠ P' := by
              intro he
              exact hxn (hinit_inj x inp₀ (hsub x List.mem_cons_self) hinp₀_mem (he.trans hinp₀_eq.symm) ▸ hm)
            rw [if_neg hne, zero_add]
            exact ih hnd' (fun y hy => hsub y (List.mem_cons_of_mem _ hy)) hm
      rw [hsingle (fourierOutcomes 20) (fourierOutcomes_nodup 20) (fun _ h => h) hinp₀_mem, smul_smul]
    · rw [dif_neg hex]
      have hzero : ∀ input ∈ fourierOutcomes 20,
          (if initialPoint25 Q (boolWordToNat input) = P' then
            sineWeight 10 (boolWordToNat input / 2 ^ 10) •
              ket (pointWrite P' (phaseWordState First20Signed.bits input zeroBasisState))
          else 0) = 0 := by
        intro input hi; rw [if_neg]; intro he; exact hex ⟨input, hi, he⟩
      rw [List.map_congr_left hzero]
      have hz : ((fourierOutcomes 20).map (fun _ => (0 : State))).sum = 0 := by
        induction (fourierOutcomes 20) with | nil => rfl | cons _ _ ih' => simp [ih']
      rw [hz, smul_zero]
  refine ⟨fun P' => by dsimp only; rw [hsum_eq]; exact ApproximatePhase34.mass_nonneg _, fun P' => ?_, fun P' hne => ?_⟩
  · dsimp only; rw [hsum_eq, hproj P']
    split_ifs with hex
    · rw [normSq_smul, normSq_ket, mul_one, map_mul, sqrt2_inv_normSq_pow,
        SineCircuit.sineWeight_normSq]
      have hsin : Real.sin (Real.pi * (boolWordToNat (Classical.choose hex) / 2 ^ 10 : Nat) / 2 ^ 10) ^ 2 ≤ 1 :=
        Real.sin_sq_le_one _
      calc (1 : ℝ) / (2 : ℝ) ^ 20 * (2 * Real.sin (Real.pi * (boolWordToNat (Classical.choose hex) / 2 ^ 10 : Nat) / 2 ^ 10) ^ 2)
          ≤ (1 : ℝ) / (2 : ℝ) ^ 20 * 2 := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = 2 / (2 : ℝ) ^ 20 := by ring
    · simp only [normSq, Quantum.inner, Finsupp.sum_zero_index, Complex.zero_re]; positivity
  · dsimp only at hne; rw [hsum_eq, hproj P'] at hne
    by_cases hex : ∃ inp ∈ fourierOutcomes 20, initialPoint25 Q (boolWordToNat inp) = P'
    · rw [dif_pos hex] at hne
      set inp₀ := Classical.choose hex
      have hi : inp₀ ∈ fourierOutcomes 20 := (Classical.choose_spec hex).1
      have hPeq : initialPoint25 Q (boolWordToNat inp₀) = P' := (Classical.choose_spec hex).2
      have hl : inp₀.length = 20 := (fourierOutcomes_mem 20 inp₀).mp hi
      have hv : boolWordToNat inp₀ < 2 ^ 20 := by simpa [hl] using boolWordToNat_lt_pow_two inp₀
      have hv_ge : 2 ^ 10 ≤ boolWordToNat inp₀ := by
        by_contra hlt
        push_neg at hlt
        have hdiv0 : boolWordToNat inp₀ / 2 ^ 10 = 0 := Nat.div_eq_of_lt hlt
        have hsw0 : sineWeight 10 (boolWordToNat inp₀ / 2 ^ 10) = 0 := by
          rw [hdiv0, SineCircuit.sineWeight_eq_sin]; simp
        rw [hsw0, mul_zero, zero_smul] at hne
        simp [normSq, Quantum.inner] at hne
      set m : ℤ := 2 * (boolWordToNat inp₀ : ℤ) - (2 : ℤ) ^ 20 + 1
      refine ⟨m, ⟨(boolWordToNat inp₀ : ℤ) - 2 ^ 19, by dsimp [m]; ring⟩, ?_, ?_, ?_⟩
      · dsimp [m]; rw [abs_lt]; constructor <;> omega
      · dsimp [m]; omega
      · exact hPeq.symm
    · rw [dif_neg hex] at hne
      simp [normSq, Quantum.inner] at hne

/-! ### List-sum propagation of `axisBad` over Phase 1 (`left18 0..10` + `left19 0`) and Phase 2 (`left19 1` + `right 0..11`) -/

private theorem list_map_map_congr {α β γ : Type} (xs : List α) (g : α → β) (f : β → γ)
    (h : α → γ) (heq : ∀ x, f (g x) = h x) :
    (xs.map g).map f = xs.map h := by
  induction xs with | nil => rfl | cons x xs ih => simp [heq, ih]

private theorem badBoundW_linear_sum (w : Nat) (wpre : Nat → ℂ) (delta : Nat → Point)
    (S : List (List Bool × State)) (D : Point → ℝ)
    (hD : ∀ P, (S.map (fun x => pointMass x.2 P)).sum ≤ D P) :
    (S.map (fun x => badBoundW w wpre delta (pointMass x.2))).sum ≤ badBoundW w wpre delta D := by
  have hsum_comm : ∀ (xs : List (List Bool × State)) (ys : List (List Bool)) (f : (List Bool × State) → List Bool → ℝ),
      (xs.map (fun x => (ys.map (fun y => f x y)).sum)).sum =
      (ys.map (fun y => (xs.map (fun x => f x y)).sum)).sum := by
    intro xs ys f
    induction xs with
    | nil =>
      simp only [List.map_nil, List.sum_nil]
      symm; induction ys with | nil => rfl | cons _ _ ihy => simp [ihy]
    | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      clear ih
      induction ys with
      | nil => simp
      | cons y ys ihy => simp only [List.map_cons, List.sum_cons]; linarith
  have hmul : ∀ (xs : List (List Bool × State)) (r : ℝ) (f : (List Bool × State) → ℝ),
      (xs.map (fun x => r * f x)).sum = r * (xs.map f).sum := fun xs r f => by
    induction xs with | nil => simp | cons _ _ ih => simp [ih, mul_add]
  unfold badBoundW
  rw [hmul, hsum_comm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply list_sum_map_le; intro inp _
  rw [hmul]
  apply mul_le_mul_of_nonneg_left _ (Complex.normSq_nonneg _)
  have hadd4 : ∀ (xs : List (List Bool × State)) (a b c d : (List Bool × State) → ℝ),
      (xs.map (fun x => a x + b x + c x + d x)).sum =
      (xs.map a).sum + (xs.map b).sum + (xs.map c).sum + (xs.map d).sum := by
    intro xs a b c d; induction xs with | nil => simp | cons _ _ ih => simp [ih]; ring
  rw [hadd4]
  linarith [hD 0, hD (delta (boolWordToNat inp)), hD (-delta (boolWordToNat inp)),
    hD (-(delta (boolWordToNat inp) + delta (boolWordToNat inp)))]

private theorem badBoundW96_linear_sum (w : Nat) (wpre : Nat → ℂ) (delta : Nat → Point)
    (S : List (List Bool × State)) (D : Point → ℝ)
    (hD : ∀ P, (S.map (fun x => pointMass x.2 P)).sum ≤ D P) :
    (S.map (fun x => badBoundW96 w wpre delta (pointMass x.2))).sum ≤ badBoundW96 w wpre delta D := by
  have hsum_comm : ∀ {β : Type} (xs : List (List Bool × State)) (ys : List β) (f : (List Bool × State) → β → ℝ),
      (xs.map (fun x => (ys.map (fun y => f x y)).sum)).sum =
      (ys.map (fun y => (xs.map (fun x => f x y)).sum)).sum := by
    intro β xs ys f
    induction xs with
    | nil =>
      simp only [List.map_nil, List.sum_nil]
      symm; induction ys with | nil => rfl | cons _ _ ihy => simp [ihy]
    | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      clear ih
      induction ys with
      | nil => simp
      | cons y ys ihy => simp only [List.map_cons, List.sum_cons]; linarith
  have hmul : ∀ (xs : List (List Bool × State)) (r : ℝ) (f : (List Bool × State) → ℝ),
      (xs.map (fun x => r * f x)).sum = r * (xs.map f).sum := fun xs r f => by
    induction xs with | nil => simp | cons _ _ ih => simp [ih, mul_add]
  unfold badBoundW96
  rw [hmul, hsum_comm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply list_sum_map_le; intro inp _
  rw [hmul, hsum_comm]
  apply mul_le_mul_of_nonneg_left _ (Complex.normSq_nonneg _)
  exact list_sum_map_le _ _ _ (fun P _ => hD P)

private theorem stepDistW_linear_sum (w : Nat) (wpre : Nat → ℂ) (delta : Nat → Point)
    (S : List (List Bool × State)) (D : Point → ℝ)
    (hD : ∀ P, (S.map (fun x => pointMass x.2 P)).sum ≤ D P) (P' : Point) :
    (S.map (fun x => stepDistW w wpre delta (pointMass x.2) P')).sum ≤ stepDistW w wpre delta D P' := by
  have hsum_comm : ∀ (xs : List (List Bool × State)) (ys : List (List Bool)) (f : (List Bool × State) → List Bool → ℝ),
      (xs.map (fun x => (ys.map (fun y => f x y)).sum)).sum =
      (ys.map (fun y => (xs.map (fun x => f x y)).sum)).sum := by
    intro xs ys f
    induction xs with
    | nil =>
      simp only [List.map_nil, List.sum_nil]
      symm; induction ys with | nil => rfl | cons _ _ ihy => simp [ihy]
    | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      clear ih
      induction ys with
      | nil => simp
      | cons y ys ihy => simp only [List.map_cons, List.sum_cons]; linarith
  have hmul : ∀ (xs : List (List Bool × State)) (r : ℝ) (f : (List Bool × State) → ℝ),
      (xs.map (fun x => r * f x)).sum = r * (xs.map f).sum := fun xs r f => by
    induction xs with | nil => simp | cons _ _ ih => simp [ih, mul_add]
  unfold stepDistW
  rw [hmul, hsum_comm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply list_sum_map_le; intro inp _
  rw [hmul]
  apply mul_le_mul_of_nonneg_left (hD _) (Complex.normSq_nonneg _)

theorem bodyTail_axisBad_maxBound96 (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (ds : List Digit25) (hright : ∀ d ∈ ds, d.isRight = true)
    (baseBad : List Bool → State → ℝ) (M Btail : ℝ) (hM : 0 ≤ M)
    (hbase : ∀ (S : List (List Bool × State)) (D : Point → ℝ),
      (∀ x ∈ S, PointSupported x.2) → MaxBound M D →
      (∀ P, (S.map (fun x => pointMass x.2 P)).sum ≤ D P) →
      (S.map (fun x => baseBad x.1 x.2)).sum ≤ Btail)
    (S : List (List Bool × State)) (D : Point → ℝ)
    (hS : ∀ x ∈ S, PointSupported x.2) (hD : MaxBound M D)
    (hdom : ∀ P, (S.map (fun x => pointMass x.2 P)).sum ≤ D P) :
    (S.map (fun x => axisBad (ds.map (bodyApproxWin Q hQ hn)) x.1 baseBad x.2)).sum ≤
      (ds.length : ℝ) * ((4 + 4 * (SkywalkTail485.Bad485.card : ℝ)) * M) + Btail := by
  induction ds generalizing S D with
  | nil =>
    simp only [List.map_nil, axisBad, List.length_nil, Nat.cast_zero, zero_mul, zero_add]
    exact hbase S D hS hD hdom
  | cons d ds ih =>
    have hd_r : d.isRight = true := hright d List.mem_cons_self
    have hds_r : ∀ d' ∈ ds, d'.isRight = true := fun d' hd' => hright d' (List.mem_cons_of_mem _ hd')
    simp only [List.map_cons, axisBad, List.length_cons, Nat.cast_add, Nat.cast_one]
    have hadd : (S.map (fun x =>
        normSq (restrictState (fun s => ¬ (bodyApproxWin Q hQ hn d).goodPred s)
          (Quantum.run (bodyApproxWin Q hQ hn d).pre
            (Quantum.run ((bodyApproxWin Q hQ hn d).model.physical.wires.reverse.map Gate.H) x.2))) +
        ((fourierOutcomes (bodyApproxWin Q hQ hn d).model.physical.wires.length).map (fun bits =>
          axisBad (ds.map (bodyApproxWin Q hQ hn)) (bits.reverse ++ x.1) baseBad
            ((bodyApproxWin Q hQ hn d).model.step x.1 bits x.2))).sum)).sum =
      (S.map (fun x =>
        normSq (restrictState (fun s => ¬ (bodyApproxWin Q hQ hn d).goodPred s)
          (Quantum.run (bodyApproxWin Q hQ hn d).pre
            (Quantum.run ((bodyApproxWin Q hQ hn d).model.physical.wires.reverse.map Gate.H) x.2))))).sum +
      (S.map (fun x =>
        ((fourierOutcomes (bodyApproxWin Q hQ hn d).model.physical.wires.length).map (fun bits =>
          axisBad (ds.map (bodyApproxWin Q hQ hn)) (bits.reverse ++ x.1) baseBad
            ((bodyApproxWin Q hQ hn d).model.step x.1 bits x.2))).sum)).sum := by
      clear ih hbase hdom hS
      induction S with | nil => simp | cons _ _ ihs => simp [ihs]; ring
    rw [hadd]
    have hbad1 : (S.map (fun x =>
        normSq (restrictState (fun s => ¬ (bodyApproxWin Q hQ hn d).goodPred s)
          (Quantum.run (bodyApproxWin Q hQ hn d).pre
            (Quantum.run ((bodyApproxWin Q hQ hn d).model.physical.wires.reverse.map Gate.H) x.2))))).sum ≤
        (4 + 4 * (SkywalkTail485.Bad485.card : ℝ)) * M := by
      have h1 : (S.map (fun x =>
          normSq (restrictState (fun s => ¬ (bodyApproxWin Q hQ hn d).goodPred s)
            (Quantum.run (bodyApproxWin Q hQ hn d).pre
              (Quantum.run ((bodyApproxWin Q hQ hn d).model.physical.wires.reverse.map Gate.H) x.2))))).sum ≤
          (S.map (fun x => badBoundW96 d.width (fun _ => 1) (Width16Schedule.increment (d.base Q) d.width d.exponent) (pointMass x.2))).sum := by
        apply list_sum_map_le; intro x hx
        have hgp_eq : (bodyApproxWin Q hQ hn d).goodPred = GenericW.GoodW96 d.k (wideCoeffs25 d) Q := by
          simp [bodyApproxWin, Digit25.goodPred, hd_r]
        rw [hgp_eq]
        change normSq (restrictState (fun s => ¬ GenericW.GoodW96 d.k (wideCoeffs25 d) Q s)
          (Quantum.run List.nil (Quantum.run (d.bank.reverse.reverse.map Gate.H) x.2))) ≤ _
        rw [List.reverse_reverse]
        exact badStep96_le_badBoundW96 Q hQ d List.nil (fun _ => 1) (body_pre_expandW d.k d.k_hi) x.2 (hS x hx)
      exact (h1.trans (badBoundW96_linear_sum d.width _ _ S D hdom)).trans
        (maxBound_badBoundW96 d.width _ _ M hM (sum_fourierOutcomes_one d.width) D hD)
    let S' : List (List Bool × State) := S.flatMap (fun x =>
      (fourierOutcomes d.width).map (fun bits => (bits.reverse ++ x.1, (bodyModel Q hQ hn d).step x.1 bits x.2)))
    have hS'_pt : ∀ y ∈ S', PointSupported y.2 := by
      intro y hy
      obtain ⟨x, hx, hy⟩ := List.mem_flatMap.mp hy
      obtain ⟨bits, _, rfl⟩ := List.mem_map.mp hy
      exact bodyModel_step_pointSupported Q hQ hn d x.1 bits x.2 (hS x hx)
    let D' := stepDistW d.width (fun _ => 1) (Width16Schedule.increment (d.base Q) d.width d.exponent) D
    have hD' : MaxBound M D' := maxBound_stepDistW d.width _ _ M hM (sum_fourierOutcomes_one d.width) D hD
    have hdom' : ∀ P', (S'.map (fun y => pointMass y.2 P')).sum ≤ D' P' := by
      intro P'
      dsimp only [S']
      rw [flatMap_sum_real]
      have hper : ∀ x ∈ S,
          (((fourierOutcomes d.width).map (fun bits => (bits.reverse ++ x.1, (bodyModel Q hQ hn d).step x.1 bits x.2))).map
            (fun y => pointMass y.2 P')).sum =
          stepDistW d.width (fun _ => 1) (Width16Schedule.increment (d.base Q) d.width d.exponent) (pointMass x.2) P' := by
        intro x hx
        rw [list_map_map_congr (fourierOutcomes d.width)
          (fun bits => (bits.reverse ++ x.1, (bodyModel Q hQ hn d).step x.1 bits x.2))
          (fun y => pointMass y.2 P')
          (fun bits => pointMass ((bodyModel Q hQ hn d).step x.1 bits x.2) P')
          (fun _ => rfl)]
        exact step_pointMass_sumW Q hQ hn d List.nil (fun _ => 1) (bodyModel Q hQ hn d) rfl
          (by simp [bodyModel, Quantum.run]) (body_pre_expandW d.k d.k_hi)
          (bodyModel_step_pointSupported Q hQ hn d) x.1 x.2 (hS x hx) P'
      rw [List.map_congr_left hper]
      exact stepDistW_linear_sum d.width _ _ S D hdom P'
    have htail_eq : (S.map (fun x =>
        ((fourierOutcomes (bodyApproxWin Q hQ hn d).model.physical.wires.length).map (fun bits =>
          axisBad (ds.map (bodyApproxWin Q hQ hn)) (bits.reverse ++ x.1) baseBad
            ((bodyApproxWin Q hQ hn d).model.step x.1 bits x.2))).sum)).sum =
        (S'.map (fun y => axisBad (ds.map (bodyApproxWin Q hQ hn)) y.1 baseBad y.2)).sum := by
      dsimp only [S']
      rw [flatMap_sum_real]
      apply congrArg List.sum; apply List.map_congr_left; intro x _
      have hwl : (bodyApproxWin Q hQ hn d).model.physical.wires.length = d.width := by
        simp only [bodyApproxWin, bodyModel, List.length_reverse, Digit25.bank, Digit25.width, GenericW.bankW_length]
      rw [hwl]
      apply congrArg List.sum; symm
      exact list_map_map_congr _ _ _ _ (fun _ => rfl)
    rw [htail_eq]
    have h2 := ih hds_r S' D' hS'_pt hD' hdom'
    linarith

theorem rightApprox25_axisBad_maxBound (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (M : ℝ) (hM : 0 ≤ M)
    (S : List (List Bool × State)) (D : Point → ℝ)
    (hS : ∀ x ∈ S, PointSupported x.2) (hD : MaxBound M D)
    (hdom : ∀ P, (S.map (fun x => pointMass x.2 P)).sum ≤ D P) :
    (S.map (fun x => axisBad (rightApprox25 Q hQ hn) List.nil (fun _ _ => 0) x.2)).sum ≤
      12 * ((4 + 4 * (SkywalkTail485.Bad485.card : ℝ)) * M) := by
  unfold rightApprox25
  simp only [axisBad]
  have hadd : (S.map (fun x =>
      normSq (restrictState (fun s => ¬ (rightHeadApproxWin Q hQ hn).goodPred s)
        (Quantum.run (rightHeadApproxWin Q hQ hn).pre
          (Quantum.run ((rightHeadApproxWin Q hQ hn).model.physical.wires.reverse.map Gate.H) x.2))) +
      ((fourierOutcomes (rightHeadApproxWin Q hQ hn).model.physical.wires.length).map (fun bits =>
        axisBad (rightTailDigits25.map (bodyApproxWin Q hQ hn)) (bits.reverse ++ List.nil) (fun _ _ => 0)
          ((rightHeadApproxWin Q hQ hn).model.step List.nil bits x.2))).sum)).sum =
    (S.map (fun x =>
      normSq (restrictState (fun s => ¬ (rightHeadApproxWin Q hQ hn).goodPred s)
        (Quantum.run (rightHeadApproxWin Q hQ hn).pre
          (Quantum.run ((rightHeadApproxWin Q hQ hn).model.physical.wires.reverse.map Gate.H) x.2))))).sum +
    (S.map (fun x =>
      ((fourierOutcomes (rightHeadApproxWin Q hQ hn).model.physical.wires.length).map (fun bits =>
        axisBad (rightTailDigits25.map (bodyApproxWin Q hQ hn)) (bits.reverse ++ List.nil) (fun _ _ => 0)
          ((rightHeadApproxWin Q hQ hn).model.step List.nil bits x.2))).sum)).sum := by
    clear hdom hS
    induction S with | nil => simp | cons _ _ ihs => simp [ihs]; ring
  rw [hadd]
  have hbad1 : (S.map (fun x =>
      normSq (restrictState (fun s => ¬ (rightHeadApproxWin Q hQ hn).goodPred s)
        (Quantum.run (rightHeadApproxWin Q hQ hn).pre
          (Quantum.run ((rightHeadApproxWin Q hQ hn).model.physical.wires.reverse.map Gate.H) x.2))))).sum ≤
      (4 + 4 * (SkywalkTail485.Bad485.card : ℝ)) * M := by
    have h1 : (S.map (fun x =>
        normSq (restrictState (fun s => ¬ (rightHeadApproxWin Q hQ hn).goodPred s)
          (Quantum.run (rightHeadApproxWin Q hQ hn).pre
            (Quantum.run ((rightHeadApproxWin Q hQ hn).model.physical.wires.reverse.map Gate.H) x.2))))).sum ≤
        (S.map (fun x => badBoundW96 17 (fun v => sineWeight 10 (v / 2 ^ 7))
          (Width16Schedule.increment (rightHeadDigit.base Q) 17 rightHeadDigit.exponent) (pointMass x.2))).sum := by
      apply list_sum_map_le; intro x hx
      change normSq (restrictState (fun s => ¬ GenericW.GoodW96 16 (wideCoeffs25 rightHeadDigit) Q s)
        (Quantum.run (sineFromPlus top10Right) (Quantum.run ((GenericW.bankW 16).reverse.reverse.map Gate.H) x.2))) ≤ _
      rw [List.reverse_reverse]
      exact badStep96_le_badBoundW96 Q hQ rightHeadDigit (sineFromPlus top10Right)
        (fun v => sineWeight 10 (v / 2 ^ 7)) rightHead_pre_expand x.2 (hS x hx)
    exact (h1.trans (badBoundW96_linear_sum 17 _ _ S D hdom)).trans
      (maxBound_badBoundW96 17 _ _ M hM sum_fourierOutcomes17_sine D hD)
  let S' : List (List Bool × State) := S.flatMap (fun x =>
    (fourierOutcomes 17).map (fun bits => (bits.reverse ++ List.nil, (rightHeadModel Q hQ hn).step List.nil bits x.2)))
  have hS'_pt : ∀ y ∈ S', PointSupported y.2 := by
    intro y hy
    obtain ⟨x, hx, hy⟩ := List.mem_flatMap.mp hy
    obtain ⟨bits, _, rfl⟩ := List.mem_map.mp hy
    exact rightHeadModel_step_pointSupported Q hQ hn List.nil bits x.2 (hS x hx)
  let D' := stepDistW 17 (fun v => sineWeight 10 (v / 2 ^ 7))
    (Width16Schedule.increment (rightHeadDigit.base Q) 17 rightHeadDigit.exponent) D
  have hD' : MaxBound M D' := maxBound_stepDistW 17 _ _ M hM sum_fourierOutcomes17_sine D hD
  have hdom' : ∀ P', (S'.map (fun y => pointMass y.2 P')).sum ≤ D' P' := by
    intro P'
    dsimp only [S']
    rw [flatMap_sum_real]
    have hper : ∀ x ∈ S,
        (((fourierOutcomes 17).map (fun bits => (bits.reverse ++ List.nil, (rightHeadModel Q hQ hn).step List.nil bits x.2))).map
          (fun y => pointMass y.2 P')).sum =
        stepDistW 17 (fun v => sineWeight 10 (v / 2 ^ 7))
          (Width16Schedule.increment (rightHeadDigit.base Q) 17 rightHeadDigit.exponent) (pointMass x.2) P' := by
      intro x hx
      rw [list_map_map_congr (fourierOutcomes 17)
        (fun bits => (bits.reverse ++ List.nil, (rightHeadModel Q hQ hn).step List.nil bits x.2))
        (fun y => pointMass y.2 P')
        (fun bits => pointMass ((rightHeadModel Q hQ hn).step List.nil bits x.2) P')
        (fun _ => rfl)]
      exact step_pointMass_sumW Q hQ hn rightHeadDigit (sineFromPlus top10Right)
        (fun v => sineWeight 10 (v / 2 ^ 7)) (rightHeadModel Q hQ hn) rfl rfl
        rightHead_pre_expand (rightHeadModel_step_pointSupported Q hQ hn) List.nil x.2 (hS x hx) P'
    rw [List.map_congr_left hper]
    exact stepDistW_linear_sum 17 _ _ S D hdom P'
  have htail_eq : (S.map (fun x =>
      ((fourierOutcomes (rightHeadApproxWin Q hQ hn).model.physical.wires.length).map (fun bits =>
        axisBad (rightTailDigits25.map (bodyApproxWin Q hQ hn)) (bits.reverse ++ List.nil) (fun _ _ => 0)
          ((rightHeadApproxWin Q hQ hn).model.step List.nil bits x.2))).sum)).sum =
      (S'.map (fun y => axisBad (rightTailDigits25.map (bodyApproxWin Q hQ hn)) y.1 (fun _ _ => 0) y.2)).sum := by
    dsimp only [S']
    rw [flatMap_sum_real]
    apply congrArg List.sum; apply List.map_congr_left; intro x _
    have hwl : (rightHeadApproxWin Q hQ hn).model.physical.wires.length = 17 := by
      simp only [rightHeadApproxWin, rightHeadModel, rightHeadDigit, List.length_reverse, Digit25.bank, Digit25.k, GenericW.bankW_length]
    rw [hwl]
    apply congrArg List.sum; symm
    exact list_map_map_congr _ _ _ _ (fun _ => rfl)
  rw [htail_eq]
  have hright_tail : ∀ d ∈ rightTailDigits25, d.isRight = true := by
    intro d hd
    simp only [rightTailDigits25, List.mem_append, List.mem_ofFn] at hd
    rcases hd with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
  have h2 := bodyTail_axisBad_maxBound96 Q hQ hn rightTailDigits25 hright_tail (fun _ _ => 0) M 0 hM
    (fun S₀ _ _ _ _ => by
      induction S₀ with | nil => simp | cons _ _ ih => simp [ih])
    S' D' hS'_pt hD' hdom'
  have hlen11 : rightTailDigits25.length = 11 := by simp [rightTailDigits25]
  rw [hlen11] at h2
  norm_num only [Nat.cast_ofNat] at h2
  linarith

theorem leftPhase1_step (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (d : Digit25) (hbaseG : d.base Q = G) (hleft : d.isRight = false)
    (acc : Nat) (hacc : 9 ≤ acc) (hsum : acc + d.width ≤ 240)
    (rest : List (ApproxCatWindow 1 (readConstant coefficientAt25 Q)))
    (baseBad : List Bool → State → ℝ) (B : ℝ)
    (S : List (List Bool × State)) (D : Point → ℝ)
    (hS : ∀ x ∈ S, PointSupported x.2) (hD : OddSupport acc (d.exponent + d.width) D)
    (hdom : ∀ P, (S.map (fun x => pointMass x.2 P)).sum ≤ D P)
    (hnext : ∀ (S' : List (List Bool × State)) (D' : Point → ℝ),
      (∀ x ∈ S', PointSupported x.2) → OddSupport (acc + d.width) d.exponent D' →
      (∀ P, (S'.map (fun x => pointMass x.2 P)).sum ≤ D' P) →
      (S'.map (fun x => axisBad rest x.1 baseBad x.2)).sum ≤ B) :
    (S.map (fun x => axisBad (bodyApproxWin Q hQ hn d :: rest) x.1 baseBad x.2)).sum ≤ B := by
  have hw2 : 2 ≤ d.width := by cases d <;> dsimp only [Digit25.width, Digit25.k] <;> decide
  simp only [axisBad]
  have hadd : (S.map (fun x =>
      normSq (restrictState (fun s => ¬ (bodyApproxWin Q hQ hn d).goodPred s)
        (Quantum.run (bodyApproxWin Q hQ hn d).pre
          (Quantum.run ((bodyApproxWin Q hQ hn d).model.physical.wires.reverse.map Gate.H) x.2))) +
      ((fourierOutcomes (bodyApproxWin Q hQ hn d).model.physical.wires.length).map (fun bits =>
        axisBad rest (bits.reverse ++ x.1) baseBad
          ((bodyApproxWin Q hQ hn d).model.step x.1 bits x.2))).sum)).sum =
    (S.map (fun x =>
      normSq (restrictState (fun s => ¬ (bodyApproxWin Q hQ hn d).goodPred s)
        (Quantum.run (bodyApproxWin Q hQ hn d).pre
          (Quantum.run ((bodyApproxWin Q hQ hn d).model.physical.wires.reverse.map Gate.H) x.2))))).sum +
    (S.map (fun x =>
      ((fourierOutcomes (bodyApproxWin Q hQ hn d).model.physical.wires.length).map (fun bits =>
        axisBad rest (bits.reverse ++ x.1) baseBad
          ((bodyApproxWin Q hQ hn d).model.step x.1 bits x.2))).sum)).sum := by
    clear hnext hdom hS
    induction S with | nil => simp | cons _ _ ihs => simp [ihs]; ring
  rw [hadd]
  have hbad0 : (S.map (fun x =>
      normSq (restrictState (fun s => ¬ (bodyApproxWin Q hQ hn d).goodPred s)
        (Quantum.run (bodyApproxWin Q hQ hn d).pre
          (Quantum.run ((bodyApproxWin Q hQ hn d).model.physical.wires.reverse.map Gate.H) x.2))))).sum ≤ 0 := by
    have h1 : (S.map (fun x =>
        normSq (restrictState (fun s => ¬ (bodyApproxWin Q hQ hn d).goodPred s)
          (Quantum.run (bodyApproxWin Q hQ hn d).pre
            (Quantum.run ((bodyApproxWin Q hQ hn d).model.physical.wires.reverse.map Gate.H) x.2))))).sum ≤
        (S.map (fun x => badBoundW d.width (fun _ => 1) (Width16Schedule.increment G d.width d.exponent) (pointMass x.2))).sum := by
      apply list_sum_map_le; intro x hx
      have hgp_eq : (bodyApproxWin Q hQ hn d).goodPred = GenericW.GoodW d.k (wideCoeffs25 d) Q := by
        simp [bodyApproxWin, Digit25.goodPred, hleft]
      rw [hgp_eq]
      change normSq (restrictState (fun s => ¬ GenericW.GoodW d.k (wideCoeffs25 d) Q s)
        (Quantum.run List.nil (Quantum.run (d.bank.reverse.reverse.map Gate.H) x.2))) ≤ _
      rw [List.reverse_reverse, ← hbaseG]
      exact badStep_le_badBoundW Q hQ d List.nil (fun _ => 1) (body_pre_expandW d.k d.k_hi) x.2 (hS x hx)
    exact (h1.trans (badBoundW_linear_sum d.width _ _ S D hdom)).trans_eq
      (oddSupport_badBound_zero acc d.exponent d.width hw2 hsum D hD)
  let S' : List (List Bool × State) := S.flatMap (fun x =>
    (fourierOutcomes d.width).map (fun bits => (bits.reverse ++ x.1, (bodyModel Q hQ hn d).step x.1 bits x.2)))
  have hS'_pt : ∀ y ∈ S', PointSupported y.2 := by
    intro y hy
    obtain ⟨x, hx, hy⟩ := List.mem_flatMap.mp hy
    obtain ⟨bits, _, rfl⟩ := List.mem_map.mp hy
    exact bodyModel_step_pointSupported Q hQ hn d x.1 bits x.2 (hS x hx)
  let D' := stepDistW d.width (fun _ => 1) (Width16Schedule.increment G d.width d.exponent) D
  have hD' : OddSupport (acc + d.width) d.exponent D' :=
    oddSupport_stepDist acc d.exponent d.width hacc hw2 hsum D hD
  have hdom' : ∀ P', (S'.map (fun y => pointMass y.2 P')).sum ≤ D' P' := by
    intro P'
    dsimp only [S']
    rw [flatMap_sum_real]
    have hper : ∀ x ∈ S,
        (((fourierOutcomes d.width).map (fun bits => (bits.reverse ++ x.1, (bodyModel Q hQ hn d).step x.1 bits x.2))).map
          (fun y => pointMass y.2 P')).sum =
        stepDistW d.width (fun _ => 1) (Width16Schedule.increment G d.width d.exponent) (pointMass x.2) P' := by
      intro x hx
      rw [list_map_map_congr (fourierOutcomes d.width)
        (fun bits => (bits.reverse ++ x.1, (bodyModel Q hQ hn d).step x.1 bits x.2))
        (fun y => pointMass y.2 P')
        (fun bits => pointMass ((bodyModel Q hQ hn d).step x.1 bits x.2) P')
        (fun _ => rfl), ← hbaseG]
      exact step_pointMass_sumW Q hQ hn d List.nil (fun _ => 1) (bodyModel Q hQ hn d) rfl
        (by simp [bodyModel, Quantum.run]) (body_pre_expandW d.k d.k_hi)
        (bodyModel_step_pointSupported Q hQ hn d) x.1 x.2 (hS x hx) P'
    rw [List.map_congr_left hper]
    exact stepDistW_linear_sum d.width _ _ S D hdom P'
  have htail_eq : (S.map (fun x =>
      ((fourierOutcomes (bodyApproxWin Q hQ hn d).model.physical.wires.length).map (fun bits =>
        axisBad rest (bits.reverse ++ x.1) baseBad
          ((bodyApproxWin Q hQ hn d).model.step x.1 bits x.2))).sum)).sum =
      (S'.map (fun y => axisBad rest y.1 baseBad y.2)).sum := by
    dsimp only [S']
    rw [flatMap_sum_real]
    apply congrArg List.sum; apply List.map_congr_left; intro x _
    have hwl : (bodyApproxWin Q hQ hn d).model.physical.wires.length = d.width := by
      simp only [bodyApproxWin, bodyModel, List.length_reverse, Digit25.bank, Digit25.width, GenericW.bankW_length]
    rw [hwl]
    apply congrArg List.sum; symm
    exact list_map_map_congr _ _ _ _ (fun _ => rfl)
  rw [htail_eq]
  have h2 := hnext S' D' hS'_pt hD' hdom'
  linarith

theorem totalBad25_bound (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (cR : ℝ) (hcR : 0 ≤ cR) :
    ((fourierOutcomes 20).map (fun bits =>
      axisBad (leftRestApprox25 Q hQ hn) bits.reverse
        (fun _ φ => cR * axisBad (rightApprox25 Q hQ hn) List.nil (fun _ _ => 0) φ)
        ((first20Model Q hQ hn).step List.nil bits (ket zeroBasisState)))).sum ≤
      (4 : ℝ) / (2 : ℝ) ^ 236 + cR * ((145 : ℝ) / 10 ^ 10) := by
  let baseR : List Bool → State → ℝ :=
    fun _ φ => cR * axisBad (rightApprox25 Q hQ hn) List.nil (fun _ _ => 0) φ
  let S₀ : List (List Bool × State) := (fourierOutcomes 20).map (fun bits =>
    (bits.reverse, (first20Model Q hQ hn).step List.nil bits (ket zeroBasisState)))
  have hS₀_pt : ∀ x ∈ S₀, PointSupported x.2 := by
    intro x hx; obtain ⟨bits, _, rfl⟩ := List.mem_map.mp hx
    exact first20Model_step_pointSupported Q hQ hn List.nil bits
  let D₀ : Point → ℝ := fun P' =>
    ((fourierOutcomes 20).map (fun bits =>
      pointMass ((first20Model Q hQ hn).step List.nil bits (ket zeroBasisState)) P')).sum
  have hD₀ : OddSupport 20 236 D₀ := first20_pointMass_sum_oddSupport Q hQ hn
  have hdom₀ : ∀ P, (S₀.map (fun x => pointMass x.2 P)).sum ≤ D₀ P := fun P => by
    dsimp only [S₀, D₀]
    rw [list_map_map_congr (fourierOutcomes 20)
      (fun bits => (bits.reverse, (first20Model Q hQ hn).step List.nil bits (ket zeroBasisState)))
      (fun x => pointMass x.2 P)
      (fun bits => pointMass ((first20Model Q hQ hn).step List.nil bits (ket zeroBasisState)) P)
      (fun _ => rfl)]
  rw [← list_map_map_congr (fourierOutcomes 20)
    (fun bits => (bits.reverse, (first20Model Q hQ hn).step List.nil bits (ket zeroBasisState)))
    (fun x => axisBad (leftRestApprox25 Q hQ hn) x.1 baseR x.2)
    (fun bits => axisBad (leftRestApprox25 Q hQ hn) bits.reverse baseR ((first20Model Q hQ hn).step List.nil bits (ket zeroBasisState)))
    (fun _ => rfl)]
  change (S₀.map (fun x => axisBad (leftRestApprox25 Q hQ hn) x.1 baseR x.2)).sum ≤
    (4 : ℝ) / (2 : ℝ) ^ 236 + cR * ((145 : ℝ) / 10 ^ 10)
  let tail2 : List (ApproxCatWindow 1 (readConstant coefficientAt25 Q)) :=
    [bodyApproxWin Q hQ hn (.left19 ⟨0, by decide⟩), bodyApproxWin Q hQ hn (.left19 ⟨1, by decide⟩)]
  have hleft_eq : leftRestApprox25 Q hQ hn =
      (List.ofFn (fun j : Fin 11 => Digit25.left18 j)).map (bodyApproxWin Q hQ hn) ++ tail2 := by
    simp [leftRestApprox25, leftDigits25, tail2, List.ofFn_succ]
  -- Phase 2: starting before `left19 1`, `OddSupport 237 19 D` gives `4 / 2^236` on `left19 1`
  -- and tight `MaxBound (2 / 2^256)` after `left19 1` for the 12 truncated Right windows.
  have hphase2 : ∀ (S : List (List Bool × State)) (D : Point → ℝ),
      (∀ x ∈ S, PointSupported x.2) → OddSupport 237 19 D →
      (∀ P, (S.map (fun x => pointMass x.2 P)).sum ≤ D P) →
      (S.map (fun x => axisBad ([bodyApproxWin Q hQ hn (.left19 ⟨1, by decide⟩)]) x.1 baseR x.2)).sum ≤
        (4 : ℝ) / (2 : ℝ) ^ 236 + cR * ((145 : ℝ) / 10 ^ 10) := by
    intro S D hS hD hdom
    let dLast : Digit25 := .left19 ⟨1, by decide⟩
    simp only [axisBad]
    have hadd : (S.map (fun x =>
        normSq (restrictState (fun s => ¬ (bodyApproxWin Q hQ hn dLast).goodPred s)
          (Quantum.run (bodyApproxWin Q hQ hn dLast).pre
            (Quantum.run ((bodyApproxWin Q hQ hn dLast).model.physical.wires.reverse.map Gate.H) x.2))) +
        ((fourierOutcomes (bodyApproxWin Q hQ hn dLast).model.physical.wires.length).map (fun bits =>
          baseR (bits.reverse ++ x.1)
            ((bodyApproxWin Q hQ hn dLast).model.step x.1 bits x.2))).sum)).sum =
      (S.map (fun x =>
        normSq (restrictState (fun s => ¬ (bodyApproxWin Q hQ hn dLast).goodPred s)
          (Quantum.run (bodyApproxWin Q hQ hn dLast).pre
            (Quantum.run ((bodyApproxWin Q hQ hn dLast).model.physical.wires.reverse.map Gate.H) x.2))))).sum +
      (S.map (fun x =>
        ((fourierOutcomes (bodyApproxWin Q hQ hn dLast).model.physical.wires.length).map (fun bits =>
          baseR (bits.reverse ++ x.1)
            ((bodyApproxWin Q hQ hn dLast).model.step x.1 bits x.2))).sum)).sum := by
      clear hdom hS
      induction S with | nil => simp | cons _ _ ihs => simp [ihs]; ring
    rw [hadd]
    have hM : MaxBound ((1 : ℝ) / (2 : ℝ) ^ 236) D := by
      refine ⟨hD.1, fun P => (hD.2.1 P).trans_eq ?_⟩
      norm_num [pow_succ]
    have hbad1 : (S.map (fun x =>
        normSq (restrictState (fun s => ¬ (bodyApproxWin Q hQ hn dLast).goodPred s)
          (Quantum.run (bodyApproxWin Q hQ hn dLast).pre
            (Quantum.run ((bodyApproxWin Q hQ hn dLast).model.physical.wires.reverse.map Gate.H) x.2))))).sum ≤
        (4 : ℝ) / (2 : ℝ) ^ 236 := by
      have h1 : (S.map (fun x =>
          normSq (restrictState (fun s => ¬ (bodyApproxWin Q hQ hn dLast).goodPred s)
            (Quantum.run (bodyApproxWin Q hQ hn dLast).pre
              (Quantum.run ((bodyApproxWin Q hQ hn dLast).model.physical.wires.reverse.map Gate.H) x.2))))).sum ≤
          (S.map (fun x => badBoundW 19 (fun _ => 1) (Width16Schedule.increment G 19 0) (pointMass x.2))).sum := by
        apply list_sum_map_le; intro x hx
        change normSq (restrictState (fun s => ¬ GenericW.GoodW 18 (wideCoeffs25 dLast) Q s)
          (Quantum.run List.nil (Quantum.run ((GenericW.bankW 18).reverse.reverse.map Gate.H) x.2))) ≤ _
        rw [List.reverse_reverse]
        exact badStep_le_badBoundW Q hQ dLast List.nil (fun _ => 1) (body_pre_expandW 18 (by decide)) x.2 (hS x hx)
      have h2 := (h1.trans (badBoundW_linear_sum 19 _ _ S D hdom)).trans
        (maxBound_badBoundW 19 _ _ _ (by positivity) (sum_fourierOutcomes_one 19) D hM)
      exact h2.trans_eq (by ring)
    let S' : List (List Bool × State) := S.flatMap (fun x =>
      (fourierOutcomes 19).map (fun bits => (bits.reverse ++ x.1, (bodyModel Q hQ hn dLast).step x.1 bits x.2)))
    have hS'_pt : ∀ y ∈ S', PointSupported y.2 := by
      intro y hy
      obtain ⟨x, hx, hy⟩ := List.mem_flatMap.mp hy
      obtain ⟨bits, _, rfl⟩ := List.mem_map.mp hy
      exact bodyModel_step_pointSupported Q hQ hn dLast x.1 bits x.2 (hS x hx)
    let D' := stepDistW 19 (fun _ => 1) (Width16Schedule.increment G 19 0) D
    have hD' : MaxBound (2 / (2 : ℝ) ^ 256) D' := oddSupport_stepDist_last D hD
    have hdom' : ∀ P', (S'.map (fun y => pointMass y.2 P')).sum ≤ D' P' := by
      intro P'
      dsimp only [S']
      rw [flatMap_sum_real]
      have hper : ∀ x ∈ S,
          (((fourierOutcomes 19).map (fun bits => (bits.reverse ++ x.1, (bodyModel Q hQ hn dLast).step x.1 bits x.2))).map
            (fun y => pointMass y.2 P')).sum =
          stepDistW 19 (fun _ => 1) (Width16Schedule.increment G 19 0) (pointMass x.2) P' := by
        intro x hx
        rw [list_map_map_congr (fourierOutcomes 19)
          (fun bits => (bits.reverse ++ x.1, (bodyModel Q hQ hn dLast).step x.1 bits x.2))
          (fun y => pointMass y.2 P')
          (fun bits => pointMass ((bodyModel Q hQ hn dLast).step x.1 bits x.2) P')
          (fun _ => rfl)]
        exact step_pointMass_sumW Q hQ hn dLast List.nil (fun _ => 1) (bodyModel Q hQ hn dLast) rfl
          (by simp [bodyModel, Quantum.run]) (body_pre_expandW 18 (by decide))
          (bodyModel_step_pointSupported Q hQ hn dLast) x.1 x.2 (hS x hx) P'
      rw [List.map_congr_left hper]
      exact stepDistW_linear_sum 19 _ _ S D hdom P'
    have htail_eq : (S.map (fun x =>
        ((fourierOutcomes (bodyApproxWin Q hQ hn dLast).model.physical.wires.length).map (fun bits =>
          baseR (bits.reverse ++ x.1)
            ((bodyApproxWin Q hQ hn dLast).model.step x.1 bits x.2))).sum)).sum =
        cR * (S'.map (fun y => axisBad (rightApprox25 Q hQ hn) List.nil (fun _ _ => 0) y.2)).sum := by
      have hmul : ∀ (xs : List (List Bool × State)) (r : ℝ) (f : (List Bool × State) → ℝ),
          (xs.map (fun x => r * f x)).sum = r * (xs.map f).sum := fun xs r f => by
        induction xs with | nil => simp | cons _ _ ih => simp [ih, mul_add]
      rw [← hmul]
      dsimp only [S', baseR]
      rw [flatMap_sum_real]
      apply congrArg List.sum; apply List.map_congr_left; intro x _
      have hwl : (bodyApproxWin Q hQ hn dLast).model.physical.wires.length = 19 := by
        simp only [bodyApproxWin, bodyModel, dLast, List.length_reverse, Digit25.bank, Digit25.k, GenericW.bankW_length]
      rw [hwl]
      apply congrArg List.sum; symm
      exact list_map_map_congr _ _ _ _ (fun _ => rfl)
    rw [htail_eq]
    have hR := rightApprox25_axisBad_maxBound Q hQ hn (2 / (2 : ℝ) ^ 256) (by positivity) S' D' hS'_pt hD' hdom'
    have hR_num : 12 * ((4 + 4 * (SkywalkTail485.Bad485.card : ℝ)) * (2 / (2 : ℝ) ^ 256)) ≤ (145 : ℝ) / 10 ^ 10 := by
      have hcard := SkywalkTail485.skywalk_bad485_card
      have h1 : 12 * ((4 + 4 * (SkywalkTail485.Bad485.card : ℝ)) * (2 / (2 : ℝ) ^ 256)) ≤
          12 * ((4 + 4 * ((15 : ℝ) / 10 ^ 11 * (2 : ℝ) ^ 256)) * (2 / (2 : ℝ) ^ 256)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith
      have h2 : 12 * ((4 + 4 * ((15 : ℝ) / 10 ^ 11 * (2 : ℝ) ^ 256)) * (2 / (2 : ℝ) ^ 256)) =
          96 / (2 : ℝ) ^ 256 + 144 / 10 ^ 10 := by
        have hp : (2 : ℝ) ^ 256 ≠ 0 := by positivity
        field_simp [hp]; ring
      have h3 : (96 : ℝ) / (2 : ℝ) ^ 256 + 144 / 10 ^ 10 ≤ 145 / 10 ^ 10 := by norm_num
      linarith
    have htail_le : cR * (S'.map (fun y => axisBad (rightApprox25 Q hQ hn) List.nil (fun _ _ => 0) y.2)).sum ≤
        cR * ((145 : ℝ) / 10 ^ 10) :=
      mul_le_mul_of_nonneg_left (hR.trans hR_num) hcR
    linarith
  -- Phase 1b: `left19 0` advances `OddSupport 218 38` to `OddSupport 237 19`
  have hphase1b : ∀ (S : List (List Bool × State)) (D : Point → ℝ),
      (∀ x ∈ S, PointSupported x.2) → OddSupport 218 38 D →
      (∀ P, (S.map (fun x => pointMass x.2 P)).sum ≤ D P) →
      (S.map (fun x => axisBad tail2 x.1 baseR x.2)).sum ≤
        (4 : ℝ) / (2 : ℝ) ^ 236 + cR * ((145 : ℝ) / 10 ^ 10) := by
    intro S D hS hD hdom
    exact leftPhase1_step Q hQ hn (.left19 ⟨0, by decide⟩) rfl rfl 218 (by decide) (by decide)
      ([bodyApproxWin Q hQ hn (.left19 ⟨1, by decide⟩)]) baseR _ S D hS hD hdom hphase2
  -- Phase 1a: induction over `m = 11 - j` steps of `left18`
  have hphase1a : ∀ (m : Nat) (hm : m ≤ 11) (S : List (List Bool × State)) (D : Point → ℝ),
      (∀ x ∈ S, PointSupported x.2) → OddSupport (20 + 18 * (11 - m)) (236 - 18 * (11 - m)) D →
      (∀ P, (S.map (fun x => pointMass x.2 P)).sum ≤ D P) →
      (S.map (fun x => axisBad
        ((List.ofFn (fun j : Fin m => Digit25.left18 ⟨(11 - m) + j.val, by omega⟩)).map (bodyApproxWin Q hQ hn) ++ tail2)
        x.1 baseR x.2)).sum ≤ (4 : ℝ) / (2 : ℝ) ^ 236 + cR * ((145 : ℝ) / 10 ^ 10) := by
    intro m
    induction m with
    | zero =>
      intro _ S D hS hD hdom
      simpa using hphase1b S D hS hD hdom
    | succ m ih =>
      intro hm S D hS hD hdom
      have hlist : (List.ofFn (fun j : Fin (m + 1) => Digit25.left18 ⟨(11 - (m + 1)) + j.val, by omega⟩)).map
          (bodyApproxWin Q hQ hn) ++ tail2 =
        bodyApproxWin Q hQ hn (.left18 ⟨11 - (m + 1), by omega⟩) ::
          ((List.ofFn (fun j : Fin m => Digit25.left18 ⟨(11 - m) + j.val, by omega⟩)).map
            (bodyApproxWin Q hQ hn) ++ tail2) := by
        rw [List.ofFn_succ, List.map_cons, List.cons_append]
        apply congrArg (List.cons _)
        apply congrArg (fun l => l ++ tail2)
        apply congrArg (List.map _)
        apply congrArg List.ofFn; funext j
        apply congrArg Digit25.left18; apply Fin.ext; simp only [Fin.val_succ]; omega
      rw [hlist]
      have hexp_eq : 236 - 18 * (11 - (m + 1)) = (Digit25.left18 ⟨11 - (m + 1), by omega⟩).exponent + (Digit25.left18 ⟨11 - (m + 1), by omega⟩).width := by
        simp only [Digit25.exponent, Digit25.width, Digit25.k]; omega
      rw [hexp_eq] at hD
      refine leftPhase1_step Q hQ hn (.left18 ⟨11 - (m + 1), by omega⟩) rfl rfl (20 + 18 * (11 - (m + 1))) (by omega)
        (by simp only [Digit25.width, Digit25.k]; omega) _ baseR _ S D hS hD hdom ?_
      intro S' D' hS' hD' hdom'
      have hacc_eq : 20 + 18 * (11 - (m + 1)) + (Digit25.left18 ⟨11 - (m + 1), by omega⟩).width = 20 + 18 * (11 - m) := by
        simp only [Digit25.width, Digit25.k]; omega
      have hexp_next : (Digit25.left18 ⟨11 - (m + 1), by omega⟩).exponent = 236 - 18 * (11 - m) := by
        simp only [Digit25.exponent]; omega
      rw [hacc_eq, hexp_next] at hD'
      exact ih (by omega) S' D' hS' hD' hdom'
  rw [hleft_eq]
  have h11 := hphase1a 11 (le_refl 11) S₀ D₀ hS₀_pt hD₀ hdom₀
  simpa using h11

/-! ### Physical program execution, lower bound (`≥ 99239 / 100000`), and dual `Readout5` readout -/

def resetTerminal25 : Instrument :=
  (measureResetWithCorrection resetWires (fun _ => List.nil)).run

theorem resetTerminal25_mass (ψ : State) : resetTerminal25.bornMass ψ = normSq ψ := by
  have hr := resetProgram_run 3407872 0 resetWires (fun _ => false) Fin.elim0
  rw [resetTerminal25, ← hr]
  exact AdaptiveCircuit.run_preservesBornMass _
    ((resetProgram 3407872 0 resetWires).instantiate_wellFormed _ _ (resetProgram_wellFormed _ _ _)) ψ

def fineEvent25Cat (accept : Nat → Nat → Bool) (history : List Bool) : Bool :=
  pairAccept trialPositions25Cat.left.toList trialPositions25Cat.right.toList accept history

private theorem program_prep_append_reset_run {n mid fin : Nat} (hfin : mid + resetWires.length = fin)
    (body : Straight n 0 mid) (read : ConstantBit n → Bool) :
    ((AndGadget.literals (Catalyst.prepare 1)
        (castFinish hfin (body.append (resetProgram n mid resetWires)))).instantiate read Fin.elim0).run =
      ((body.instantiate read Fin.elim0).run.seq resetTerminal25).map
        (fun b => ({ history := List.nil, kraus := Quantum.run (Catalyst.prepare 1) } : InstrumentBranch).seq b) := by
  rw [LocalFour.literals_instantiate_run, castFinish_instantiate, Single.append_run_history]
  have hres : ∀ h : Fin mid → Bool,
      ((resetProgram n mid resetWires).instantiate read h).run = resetTerminal25 := fun h =>
    resetProgram_run n mid resetWires read h
  simp only [hres, Instrument.seq]
  apply List.map_congr_left; intro b _; rfl

theorem program25Cat_run_data (read : ConstantBit 3407872 → Bool) :
    (program25Cat.instantiate read Fin.elim0).run =
      ((((CatAxis.axisCat 1 leftWins25Cat 0 List.nil).append
          (CatAxis.axisCat 1 rightWins25Cat (0 + axisCount leftWins25Cat) List.nil)).instantiate read Fin.elim0).run.seq
        resetTerminal25).map
        (fun b => ({ history := List.nil, kraus := Quantum.run (Catalyst.prepare 1) } : InstrumentBranch).seq b) :=
  program_prep_append_reset_run _ _ read

private theorem approx_bad_iso (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : ApproxCatWindow 1 (readConstant coefficientAt25 Q))
    (hw : w ∈ leftRestApprox25 Q hQ hn ∨ w ∈ rightApprox25 Q hQ hn)
    (φ : State) (hφ : PointSupported φ) :
    let χ := Quantum.run w.pre (Quantum.run (w.model.physical.wires.reverse.map Gate.H) φ)
    normSq (w.core_ideal (restrictState (fun s => ¬ w.goodPred s) χ)) ≤
      normSq (restrictState (fun s => ¬ w.goodPred s) χ) := by
  dsimp only
  have hfor (d : Digit25) (GoodP : BasisState → Prop) (pre : Circuit) (wpre : Nat → ℂ)
      (hpre : ∀ P : Point, Quantum.run pre (Quantum.run (d.bank.map Gate.H) (ket (pointWrite P zeroBasisState))) =
        (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ d.width) •
          ((fourierOutcomes d.width).map (fun input =>
            wpre (boolWordToNat input) • ket (phaseWordState d.bank input (pointWrite P zeroBasisState)))).sum) :
      normSq (Finsupp.lmapDomain ℂ ℂ (GenericW.updateW d.k (wideCoeffs25 d) Q)
        (restrictState (fun s => ¬ GoodP s)
          (Quantum.run pre (Quantum.run (d.bank.map Gate.H) φ)))) ≤
      normSq (restrictState (fun s => ¬ GoodP s)
        (Quantum.run pre (Quantum.run (d.bank.map Gate.H) φ))) := by
    obtain ⟨hχ_sup, _⟩ := bankW_prep_eval d.k d.k_hi pre wpre hpre φ hφ
    have hbad_sup : SupportedOn (BankPointFamily d.bank)
        (restrictState (fun s => ¬ GoodP s)
          (Quantum.run pre (Quantum.run (d.bank.map Gate.H) φ))) :=
      restrictState_preserves _ _ _ hχ_sup
    exact le_of_eq (normSq_lmapDomain_injOn _ ((updateW_injOn_bankPoint Q hQ d).mono
      (fun s hs => hbad_sup s (Finsupp.mem_support_iff.mp hs))))
  rcases hw with hwL | hwR
  · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hwL
    change normSq (Finsupp.lmapDomain ℂ ℂ (GenericW.updateW d.k (wideCoeffs25 d) Q)
      (restrictState (fun s => ¬ d.goodPred Q s)
        (Quantum.run List.nil (Quantum.run (d.bank.reverse.reverse.map Gate.H) φ)))) ≤
      normSq (restrictState (fun s => ¬ d.goodPred Q s)
        (Quantum.run List.nil (Quantum.run (d.bank.reverse.reverse.map Gate.H) φ)))
    rw [List.reverse_reverse]
    exact hfor d (d.goodPred Q) List.nil (fun _ => 1) (body_pre_expandW d.k d.k_hi)
  · rcases List.mem_cons.mp hwR with rfl | hwR
    · change normSq (Finsupp.lmapDomain ℂ ℂ (GenericW.updateW 16 (wideCoeffs25 rightHeadDigit) Q)
        (restrictState (fun s => ¬ GenericW.GoodW96 16 (wideCoeffs25 rightHeadDigit) Q s)
          (Quantum.run (sineFromPlus top10Right) (Quantum.run ((GenericW.bankW 16).reverse.reverse.map Gate.H) φ)))) ≤
        normSq (restrictState (fun s => ¬ GenericW.GoodW96 16 (wideCoeffs25 rightHeadDigit) Q s)
          (Quantum.run (sineFromPlus top10Right) (Quantum.run ((GenericW.bankW 16).reverse.reverse.map Gate.H) φ)))
      rw [List.reverse_reverse]
      exact hfor rightHeadDigit (GenericW.GoodW96 16 (wideCoeffs25 rightHeadDigit) Q)
        (sineFromPlus top10Right) (fun v => sineWeight 10 (v / 2 ^ 7)) rightHead_pre_expand
    · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hwR
      change normSq (Finsupp.lmapDomain ℂ ℂ (GenericW.updateW d.k (wideCoeffs25 d) Q)
        (restrictState (fun s => ¬ d.goodPred Q s)
          (Quantum.run List.nil (Quantum.run (d.bank.reverse.reverse.map Gate.H) φ)))) ≤
        normSq (restrictState (fun s => ¬ d.goodPred Q s)
          (Quantum.run List.nil (Quantum.run (d.bank.reverse.reverse.map Gate.H) φ)))
      rw [List.reverse_reverse]
      exact hfor d (d.goodPred Q) List.nil (fun _ => 1) (body_pre_expandW d.k d.k_hi)

theorem program25Cat_event_mass_upper (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0) (accept : Nat → Nat → Bool) :
    Instrument.bornMass ((program25Cat.instantiate (readConstant coefficientAt25 Q) Fin.elim0).run.filter
      (fun b => fineEvent25Cat accept b.history)) (ket zeroBasisState) ≤
      ((1 + (1 / 3000 : ℝ)) ^ 2) ^ 12 * ((1 + (1 / 10 ^ 8 : ℝ)) ^ 2) ^ 13 *
        windowedEventMass Q zeroBasisState 256 206 accept +
      (((1 + (1 / 10 ^ 8 : ℝ)) ^ 2) ^ 13 * (2 + 1 / 10 ^ 8) * (1 + 1 / (1 / 10 ^ 8))) *
        ((4 : ℝ) / (2 : ℝ) ^ 236) +
      (((1 + (1 / 3000 : ℝ)) ^ 2) ^ 12 * ((1 + (1 / 10 ^ 8 : ℝ)) ^ 2) ^ 13 * (2 + 1 / 3000) * (1 + 1 / (1 / 3000))) *
        ((145 : ℝ) / 10 ^ 10) := by
  set epsR : ℝ := 1 / 3000
  set αR : ℝ := (1 + epsR) ^ 2
  set B0R : ℝ := (2 + epsR) * (1 + 1 / epsR)
  set epsL : ℝ := 1 / 10 ^ 8
  set αL : ℝ := (1 + epsL) ^ 2
  set B0L : ℝ := (2 + epsL) * (1 + 1 / epsL)
  have hepsR : 0 < epsR := by dsimp [epsR]; positivity
  have hepsL : 0 < epsL := by dsimp [epsL]; positivity
  have hB0R_nn : 0 ≤ B0R := by dsimp [B0R, epsR]; positivity
  have hB0L_pos : 0 < B0L := by dsimp [B0L, epsL]; positivity
  have hterm_sub : ∀ (lhs rhs : List Bool), SubUnital
      (if accept (fourierWordLSB lhs.reverse) (fourierWordLSB rhs.reverse) then resetTerminal25 else List.nil) :=
    fun _ _ => subUnital_ite _ _ (fun φ => le_of_eq (resetTerminal25_mass φ))
  have hlenR : (rightApprox25 Q hQ hn).length = 12 := by simp [rightApprox25, rightTailDigits25]
  have hlenL : (leftRestApprox25 Q hQ hn).length = 13 := by simp [leftRestApprox25, leftDigits25]
  have hR_step : ∀ w ∈ rightApprox25 Q hQ hn, ∀ pr bits φ, PointSupported φ → PointSupported (w.model.step pr bits φ) := by
    intro w hw pr bits φ hφ
    rcases List.mem_cons.mp hw with rfl | hw
    · exact rightHeadModel_step_pointSupported Q hQ hn pr bits φ hφ
    · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hw
      exact bodyModel_step_pointSupported Q hQ hn d pr bits φ hφ
  have hL_step : ∀ w ∈ leftRestApprox25 Q hQ hn, ∀ pr bits φ, PointSupported φ → PointSupported (w.model.step pr bits φ) := by
    intro w hw pr bits φ hφ
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp hw
    exact bodyModel_step_pointSupported Q hQ hn d pr bits φ hφ
  have hR_bound (lHist lhs : List Bool) (φ : State) (hφ : PointSupported φ) :
      (selectedAxisDep (rightApprox25 Q hQ hn) (0 + axisCount ((leftApprox25 Q hQ hn).map ApproxCatWindow.catPhys))
        (Single.historyAfter _ Fin.elim0 lHist) List.nil
        (fun _ rhs => if accept (fourierWordLSB lhs.reverse) (fourierWordLSB rhs.reverse) then resetTerminal25 else List.nil)).bornMass (LocalFour.Prep 1 φ) ≤
      αR ^ 12 * (idealAxis ((rightApprox25 Q hQ hn).map ApproxCatWindow.model) List.nil
        (fun rhs => if accept (fourierWordLSB lhs.reverse) (fourierWordLSB rhs.reverse) then resetTerminal25 else List.nil)).bornMass φ +
      B0L * ((B0R * αR ^ 12 / B0L) * axisBad (rightApprox25 Q hQ hn) List.nil (fun _ _ => 0) φ) := by
    have h := selectedAxisDep_mass_upper (rightApprox25 Q hQ hn)
      (0 + axisCount ((leftApprox25 Q hQ hn).map ApproxCatWindow.catPhys))
      (Single.historyAfter _ Fin.elim0 lHist) List.nil
      (fun _ rhs => if accept (fourierWordLSB lhs.reverse) (fourierWordLSB rhs.reverse) then resetTerminal25 else List.nil)
      (fun rhs => if accept (fourierWordLSB lhs.reverse) (fourierWordLSB rhs.reverse) then resetTerminal25 else List.nil)
      (fun _ _ => 0) PointSupported epsR 1 B0R hepsR (by norm_num) hB0R_nn le_rfl hR_step
      (fun w hw φ' hφ' => approx_bad_iso Q hQ hn w (Or.inr hw) φ' hφ')
      (fun _ rhs => hterm_sub lhs rhs)
      (fun _ rhs φ' _ _ => by
        simp only [one_mul, mul_zero, add_zero]
        split_ifs
        · rw [resetTerminal25_mass, resetTerminal25_mass, LocalFour.normSq_prep]
        · simp [Instrument.bornMass])
      φ hφ (pointSupported_y1 φ hφ)
    have hcancel : B0L * ((B0R * αR ^ 12 / B0L) * axisBad (rightApprox25 Q hQ hn) List.nil (fun _ _ => 0) φ) =
        (B0R * αR ^ 12) * axisBad (rightApprox25 Q hQ hn) List.nil (fun _ _ => 0) φ := by
      field_simp [hB0L_pos.ne']
    rw [hcancel]
    simpa [hlenR] using h
  let physTermL : List Bool → List Bool → Instrument := fun lHist lhs =>
    selectedAxisDep (rightApprox25 Q hQ hn)
      (0 + axisCount ((leftApprox25 Q hQ hn).map ApproxCatWindow.catPhys))
      (Single.historyAfter _ Fin.elim0 lHist) List.nil
      (fun _ rhs => if accept (fourierWordLSB lhs.reverse) (fourierWordLSB rhs.reverse) then resetTerminal25 else List.nil)
  let idealTermL : List Bool → Instrument := fun lhs =>
    idealAxis ((rightApprox25 Q hQ hn).map ApproxCatWindow.model) List.nil
      (fun rhs => if accept (fourierWordLSB lhs.reverse) (fourierWordLSB rhs.reverse) then resetTerminal25 else List.nil)
  have hfirst_good : SupportedOn First20Input0
      (Quantum.run (sineFromPlus top10Left)
        (Quantum.run (First20Signed.bits.reverse.reverse.map Gate.H) (ket zeroBasisState))) := by
    rw [List.reverse_reverse]
    have hH : SupportedOn First20Input0 (Quantum.run (First20Signed.bits.map Gate.H) (ket zeroBasisState)) :=
      circuit_preserves_pred (First20Signed.bits.map Gate.H) First20Input0
        (fun s w b hw hs => first20Input0_upd s w b (by
          simp only [circuitWires, List.mem_flatMap, List.mem_map] at hw
          obtain ⟨g, ⟨v, hv, rfl⟩, hwg⟩ := hw
          simp only [gateWires, List.mem_singleton] at hwg
          exact hwg ▸ hv) hs)
        zeroBasisState zeroBasisState_first20Input0
    exact Support.linear First20Input0 First20Input0 (Quantum.run (sineFromPlus top10Left))
      (fun s hs => circuit_preserves_pred (sineFromPlus top10Left) First20Input0
        (fun t w b hw ht => first20Input0_upd t w b
          (top10Left_sub_bits (sineFromPlus_wires top10Left top10Left_length hw)) ht) s hs)
      _ hH
  have hmain := selectedAxisDep_cons_exact_upper (first20ApproxWin Q hQ hn) (leftRestApprox25 Q hQ hn)
    0 Fin.elim0 List.nil physTermL idealTermL
    (fun bits => axisBad (leftRestApprox25 Q hQ hn) bits.reverse
      (fun _ φ => (B0R * αR ^ 12 / B0L) * axisBad (rightApprox25 Q hQ hn) List.nil (fun _ _ => 0) φ)
      ((first20Model Q hQ hn).step List.nil bits (ket zeroBasisState)))
    (αR ^ 12 * αL ^ 13) (B0L * αL ^ 13) (ket zeroBasisState) (supportedOn_ket _ _ rfl) hfirst_good (by
      intro a bits ha_mem hb_mem
      have ha_len : a.history.length = cFirst20 := by
        change a.history.length = (first20ApproxWin Q hQ hn).catPhys.count
        have h := straight_history_length _ (readConstant coefficientAt25 Q) Fin.elim0 a ha_mem; omega
      have hnp : (nextPrior cFirst20 20 List.nil).map
          (Single.historyAfter (0 + cFirst20 + 20)
            (Single.historyAfter (0 + cFirst20) Fin.elim0 a.history) bits) = bits.reverse := by
        simpa using nextPrior_map cFirst20 20 List.nil Fin.elim0 a.history bits ha_len
          ((fourierOutcomes_mem 20 bits).mp hb_mem)
      have hL := selectedAxisDep_mass_upper (leftRestApprox25 Q hQ hn)
        (0 + cFirst20 + First20Signed.bits.reverse.length)
        (Single.historyAfter (0 + cFirst20 + First20Signed.bits.reverse.length)
          (Single.historyAfter (0 + cFirst20) Fin.elim0 a.history) bits)
        (nextPrior cFirst20 First20Signed.bits.reverse.length List.nil)
        (fun hRest lhs => physTermL (a.history ++ bits ++ hRest) lhs)
        idealTermL (fun _ φ => (B0R * αR ^ 12 / B0L) * axisBad (rightApprox25 Q hQ hn) List.nil (fun _ _ => 0) φ)
        PointSupported epsL (αR ^ 12) B0L hepsL (by positivity) hB0L_pos.le le_rfl hL_step
        (fun w hw φ' hφ' => approx_bad_iso Q hQ hn w (Or.inl hw) φ' hφ')
        (fun hRest lhs => selectedAxisDep_subUnital _ _ _ _ _ (fun _ rhs => hterm_sub lhs rhs))
        (fun hRest lhs φ' hφ' _ => hR_bound (a.history ++ bits ++ hRest) lhs φ' hφ')
        ((first20Model Q hQ hn).step List.nil bits (ket zeroBasisState))
        (first20Model_step_pointSupported Q hQ hn List.nil bits)
        (pointSupported_y1 _ (first20Model_step_pointSupported Q hQ hn List.nil bits))
      have hnp' : (nextPrior cFirst20 First20Signed.bits.reverse.length List.nil).map
          (Single.historyAfter (0 + cFirst20 + First20Signed.bits.reverse.length)
            (Single.historyAfter (0 + cFirst20) Fin.elim0 a.history) bits) = bits.reverse := by
        simpa [First20Signed.bits_length] using hnp
      rw [hnp', hlenL] at hL
      simpa [List.append_nil] using hL)
  have hlhs : (idealAxis ((leftApprox25 Q hQ hn).map ApproxCatWindow.model) List.nil idealTermL).bornMass (ket zeroBasisState) =
      windowedEventMass Q zeroBasisState 256 206 accept := by
    have heq := windowed_idealTwoAxes_event_mass_anyBias Q zeroBasisState (ket zeroBasisState)
      (first20Model Q hQ hn) (leftDigits25.map (bodyModel Q hQ hn))
      (rightHeadModel Q hQ hn) (rightTailDigits25.map (bodyModel Q hQ hn))
      (first20Model_rule Q hQ hn) (rightHeadModel_rule Q hQ hn)
      (fun w hw => by
        rcases List.mem_append.mp hw with hw | hw <;>
        · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hw; exact bodyModel_rule Q hQ hn d)
      (leftModels25_weights Q hQ hn) (rightModels25_weights Q hQ hn)
      resetTerminal25 resetTerminal25_mass accept
    have hpl : precision (leftModels25 Q hQ hn) = 256 := by
      simp [precision, leftModels25, leftDigits25, List.ofFn_succ, first20Model, bodyModel,
        First20Signed.bits_length, Digit25.bank, Digit25.k, GenericW.bankW_length]
    have hpr : precision (rightModels25 Q hQ hn) = 206 := by
      simp [precision, rightModels25, rightTailDigits25, List.ofFn_succ, rightHeadModel, rightHeadDigit, bodyModel,
        Digit25.bank, Digit25.k, GenericW.bankW_length]
    have hpl' : precision (first20Model Q hQ hn :: leftDigits25.map (bodyModel Q hQ hn)) = 256 := hpl
    have hpr' : precision (rightHeadModel Q hQ hn :: rightTailDigits25.map (bodyModel Q hQ hn)) = 206 := hpr
    rw [hpl', hpr'] at heq
    rw [leftApprox25_model]
    dsimp only [idealTermL]; rw [rightApprox25_model]
    simpa only [idealTwoAxes, leftModels25, rightModels25] using heq
  have hrhs : (selectedAxisDep (leftApprox25 Q hQ hn) 0 Fin.elim0 List.nil physTermL).bornMass
        (LocalFour.Prep 1 (ket zeroBasisState)) =
      Instrument.bornMass ((program25Cat.instantiate (readConstant coefficientAt25 Q) Fin.elim0).run.filter
        (fun b => fineEvent25Cat accept b.history)) (ket zeroBasisState) := by
    rw [program25Cat_run_data, prefix_filter_mass]
    rw [← selectedTwoAxesApprox_expand (leftApprox25 Q hQ hn) (rightApprox25 Q hQ hn) 0 Fin.elim0]
    rw [selectedTwoAxesApprox_fixed_filter (leftApprox25 Q hQ hn) (rightApprox25 Q hQ hn) resetTerminal25 accept]
    unfold physicalAxesApprox
    rw [leftApprox25_catPhys, rightApprox25_catPhys]
    have hposL : Single.axisPositions leftWins25Cat 0 = leftPositions25Cat := by
      rw [Single.axisPositions, leftWins25Cat_meta]; rfl
    have hposR : Single.axisPositions rightWins25Cat (axisCount leftWins25Cat) = rightPositions25Cat := by
      rw [Single.axisPositions, rightWins25Cat_meta]; rfl
    rw [hposL, hposR]
    rfl
  have hbad := totalBad25_bound Q hQ hn (B0R * αR ^ 12 / B0L) (div_nonneg (mul_nonneg hB0R_nn (by positivity)) hB0L_pos.le)
  have hB0L_aL_nn : 0 ≤ B0L * αL ^ 13 := mul_nonneg hB0L_pos.le (by positivity)
  have hmb := mul_le_mul_of_nonneg_left hbad hB0L_aL_nn
  have hsimp : (B0L * αL ^ 13) * ((4 : ℝ) / (2 : ℝ) ^ 236 + (B0R * αR ^ 12 / B0L) * ((145 : ℝ) / 10 ^ 10)) =
      (αL ^ 13 * B0L) * ((4 : ℝ) / (2 : ℝ) ^ 236) + (αR ^ 12 * αL ^ 13 * B0R) * ((145 : ℝ) / 10 ^ 10) := by
    field_simp [hB0L_pos.ne']
  rw [hsimp] at hmb
  change _ ≤ αR ^ 12 * αL ^ 13 * _ + (B0L * αL ^ 13) * _ at hmain
  rw [show (first20ApproxWin Q hQ hn :: leftRestApprox25 Q hQ hn) = leftApprox25 Q hQ hn from rfl,
    List.map_nil, hlhs, hrhs] at hmain
  have hlen20 : (first20ApproxWin Q hQ hn).model.physical.wires.length = 20 := by
    simp [first20ApproxWin, first20Model, First20Signed.bits_length]
  rw [hlen20] at hmain
  change _ ≤ αR ^ 12 * αL ^ 13 * _ + (αL ^ 13 * (2 + epsL) * (1 + 1 / epsL)) * _ +
    (αR ^ 12 * αL ^ 13 * (2 + epsR) * (1 + 1 / epsR)) * _
  have heq_f : αL ^ 13 * B0L = αL ^ 13 * (2 + epsL) * (1 + 1 / epsL) := by dsimp [B0L]; ring
  have heq_r : αR ^ 12 * αL ^ 13 * B0R = αR ^ 12 * αL ^ 13 * (2 + epsR) * (1 + 1 / epsR) := by dsimp [B0R]; ring
  rw [heq_f, heq_r] at hmb
  linarith

theorem program25Cat_clean (read : ConstantBit 3407872 → Bool) (b : InstrumentBranch)
    (hb : b ∈ (program25Cat.instantiate read Fin.elim0).run) (ψ : State) :
    SupportedOn RoundedReadout.CleanReadout (b.kraus ψ) := by
  rw [program25Cat_run_data] at hb
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
  obtain ⟨a, _, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
  have h := resetRegister_clean resetWires resetWires_nodup c hc
    (a.kraus (Quantum.run (Catalyst.prepare 1) ψ))
  intro s hs
  exact ⟨h s hs 0 resourceInst25.reset_zero, h s hs 1 resourceInst25.reset_one⟩

theorem verified_of_reads25Cat (p : ℤ × ℤ) (hp : p ∈ offsets13)
    (Q : Point) (d : Nat) (hd : Q = d • G) (hist : List Bool) (a b : Nat)
    (hl : readWord hist (Readout5.wordAt5 leftBits25Cat p.1).toList = some a)
    (hr : readWord hist (Readout5.wordAt5 rightBits25Mid p.2).toList = some b)
    (hm : (d : ZMod order) ∈ fixedCandidates params256 a b) :
    (verifiedCandidate rawLayout25Cat Q hist).isSome := by
  classical
  apply List.find?_isSome.mpr
  refine ⟨(d : ZMod order), ?_, ?_⟩
  · unfold candidates
    apply List.mem_flatMap.mpr
    refine ⟨⟨Readout5.wordAt5 leftBits25Cat p.1, Readout5.wordAt5 rightBits25Mid p.2⟩,
      List.mem_map.mpr ⟨p, hp, rfl⟩, ?_⟩
    simpa only [decodeTrial, trialCandidates, rawLayout25Cat, hl, hr,
      fixedCandidates_take, Finset.mem_toList] using hm
  · simp only [decide_eq_true_eq, ZMod.val_natCast]
    rw [hd]
    exact nsmul_eq_nsmul_iff_modEq.mpr (by rw [generator_order]; exact Nat.mod_mod _ _)

theorem readout25Cat_wellFormed : readout25Cat.WellFormed := by
  unfold readout25Cat readoutL25 readoutR25
  rw [castFinish_wellFormed]
  apply straight_append_wellFormed
  · rw [castFinish_wellFormed]; exact Readout5.suffix5_wellFormed _ _ _ _
  · rw [castFinish_wellFormed]; exact Readout5.suffix5_wellFormed _ _ _ _

theorem suffix25Cat_accept (Q : Point) (d : Nat) (hd : Q = d • G)
    (read : ConstantBit 3407872 → Bool) (history : Fin cursor25Cat → Bool)
    (ψ : State) (hψ : SupportedOn RoundedReadout.CleanReadout ψ)
    (hf : fineEvent25Cat (pairRecovered256 d) (List.ofFn history) = true)
    (b : InstrumentBranch) (hb : b ∈ (readout25Cat.instantiate read history).run)
    (hn : b.kraus ψ ≠ 0) :
    (verifiedCandidate rawLayout25Cat Q (List.ofFn history ++ b.history)).isSome := by
  have hrl := NeighborReadout.input_read leftBits25Cat history
  have hrr := NeighborReadout.input_read rightBits25Cat history
  rw [leftBits25Cat_vals] at hrl
  rw [rightBits25Cat_vals] at hrr
  obtain ⟨a, ha, hrec⟩ := Rounded.pairAccept_value _ _ _ _ _ hrr hf
  have ha_eq : a = NeighborReadout.inputValue leftBits25Cat history := Option.some.inj (ha.symm.trans hrl)
  rw [ha_eq] at hrec
  unfold pairRecovered256 at hrec
  obtain ⟨p, hp, hmem⟩ := of_decide_eq_true hrec
  have hpb := offsets13_bounds p hp
  unfold readout25Cat at hb
  rw [castFinish_instantiate] at hb
  obtain ⟨h₁, bL, bR, hbL, hbR, he₁, rfl⟩ := straight_append_branch readoutL25 readoutR25 read history b hb
  have hbLn : bL.kraus ψ ≠ 0 := by
    intro h; apply hn; simp only [InstrumentBranch.seq, LinearMap.comp_apply, h, map_zero]
  have hreadL := Readout5.suffix5_reads 3407872 cursor25Cat 256 leftBits25Cat read history ψ hψ bL
    (by simpa only [readoutL25, castFinish_instantiate] using hbL) hbLn p.1 hpb.1
  have hbRn : bR.kraus ψ ≠ 0 := by
    simpa only [InstrumentBranch.seq, LinearMap.comp_apply, hreadL.1] using hn
  have hreadR := Readout5.suffix5_reads 3407872 cursor25Mid 206 rightBits25Mid read h₁ ψ hψ bR
    (by simpa only [readoutR25, castFinish_instantiate] using hbR) hbRn p.2 hpb.2
  have hfull : List.ofFn history ++ (bL.seq bR).history = List.ofFn h₁ ++ bR.history := by
    simp only [InstrumentBranch.seq, ← List.append_assoc, ← he₁]
  have hL_final : readWord (List.ofFn history ++ (bL.seq bR).history)
      (Readout5.wordAt5 leftBits25Cat p.1).toList =
      some (neighborWord 256 (NeighborReadout.inputValue leftBits25Cat history) p.1) := by
    rw [hfull, NeighborReadout.readWord_append_left (List.ofFn h₁) bR.history _ (by
      intro x hx
      have hlt := Readout5.wordAt5_lt leftBits25Cat p.1 x hx
      simp only [List.length_ofFn, cursor25Mid]; omega), he₁]
    exact hreadL.2
  have hvalR : NeighborReadout.inputValue rightBits25Mid h₁ =
      NeighborReadout.inputValue rightBits25Cat history := by
    have hbit : ∀ i : Fin 206, h₁ (rightBits25Mid[i.val]) = history (rightBits25Cat[i.val]) := by
      intro i
      have hidx : (rightBits25Mid[i.val]).val = (rightBits25Cat[i.val]).val := by
        simp [rightBits25Mid]
      have hget := congrArg (fun l : List Bool => l[(rightBits25Cat[i.val]).val]?) he₁
      dsimp only at hget
      have hlt1 : (rightBits25Cat[i.val]).val < cursor25Mid :=
        (rightBits25Cat[i.val]).isLt.trans_le (by unfold cursor25Mid; omega)
      have hlt0 : (rightBits25Cat[i.val]).val < cursor25Cat := (rightBits25Cat[i.val]).isLt
      rw [List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using hlt1),
          List.getElem_ofFn,
          List.getElem?_append_left (by simpa only [List.length_ofFn] using hlt0),
          List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using hlt0),
          List.getElem_ofFn] at hget
      have hfin : (⟨(rightBits25Cat[i.val]).val, hlt1⟩ : Fin cursor25Mid) = rightBits25Mid[i.val] :=
        Fin.ext hidx.symm
      rw [hfin] at hget
      exact Option.some.inj hget
    unfold NeighborReadout.inputValue
    apply congrArg boolWordToNat
    apply List.ext_getElem (by simp)
    intro i hi1 hi2
    simp only [List.getElem_map, Vector.getElem_toList]
    have hi : i < 206 := by simpa using hi1
    exact hbit ⟨i, hi⟩
  have hR_final : readWord (List.ofFn history ++ (bL.seq bR).history)
      (Readout5.wordAt5 rightBits25Mid p.2).toList =
      some (neighborWord 206 (NeighborReadout.inputValue rightBits25Cat history) p.2) := by
    rw [hfull, ← hvalR]
    exact hreadR.2
  exact verified_of_reads25Cat p hp Q d hd _ _ _ hL_final hR_final hmem

/-! ### Part 4: Static budgets (`wellFormed`, `slots`, `support`, `tCount`, `cost18`, `measurements`) -/

def IsWin25Cat (w : Window 3407872) : Prop :=
  w = first20CatWin ∨ w = rightHeadCatWin ∨ ∃ d, w = bodyCatWin d

theorem bodyCatWin_support (d : Digit25) (start : Nat) :
    straightWires ((bodyCatWin d).program start) ⊆ List.range 1612 := by
  cases d with
  | left18 j =>
    change straightWires (castFinish _ (reindexStraight _ (relabelStraight _ (GenericW.compiledProgram17 start)))) ⊆ _
    rw [straightWires_castFinish, straightWires_reindex]; exact GenericW.compiled17_packed_support start
  | left19 j =>
    change straightWires (castFinish _ (reindexStraight _ (relabelStraight _ (GenericW.compiledProgram18 start)))) ⊆ _
    rw [straightWires_castFinish, straightWires_reindex]; exact GenericW.compiled18_packed_support start
  | right17 j =>
    change straightWires (castFinish _ (reindexStraight _ (relabelStraight _ (GenericW.compiledProgramTrunc16 start)))) ⊆ _
    rw [straightWires_castFinish, straightWires_reindex]; exact GenericW.compiledTrunc16_packed_support start
  | right18 j =>
    change straightWires (castFinish _ (reindexStraight _ (relabelStraight _ (GenericW.compiledProgramTrunc17 start)))) ⊆ _
    rw [straightWires_castFinish, straightWires_reindex]; exact GenericW.compiledTrunc17_packed_support start

theorem bodyCatWin_slots (d : Digit25) (start : Nat) : ((bodyCatWin d).program start).gateSlots ≤ 80000000000 := by
  cases d with
  | left18 j =>
    change (castFinish _ (reindexStraight _ (relabelStraight _ (GenericW.compiledProgram17 start)))).gateSlots ≤ _
    rw [castFinish_gateSlots, reindexStraight_gateSlots, relabelStraight_slots]; exact GenericW.compiled17_slots start
  | left19 j =>
    change (castFinish _ (reindexStraight _ (relabelStraight _ (GenericW.compiledProgram18 start)))).gateSlots ≤ _
    rw [castFinish_gateSlots, reindexStraight_gateSlots, relabelStraight_slots]; exact GenericW.compiled18_slots start
  | right17 j =>
    change (castFinish _ (reindexStraight _ (relabelStraight _ (GenericW.compiledProgramTrunc16 start)))).gateSlots ≤ _
    rw [castFinish_gateSlots, reindexStraight_gateSlots, relabelStraight_slots]; exact GenericW.compiledTrunc16_slots start
  | right18 j =>
    change (castFinish _ (reindexStraight _ (relabelStraight _ (GenericW.compiledProgramTrunc17 start)))).gateSlots ≤ _
    rw [castFinish_gateSlots, reindexStraight_gateSlots, relabelStraight_slots]; exact GenericW.compiledTrunc17_slots start

theorem bodyCatWin_tCount (d : Digit25) (start : Nat) (read : ConstantBit 3407872 → Bool) (h : Fin start → Bool) :
    (((bodyCatWin d).program start).instantiate read h).tCount ≤ 4 * d.tof := by
  cases d with
  | left18 j =>
    change ((castFinish _ (reindexStraight _ (relabelStraight _ (GenericW.compiledProgram17 start)))).instantiate read h).tCount ≤ _
    rw [castFinish_instantiate, reindexStraight_instantiate, relabelStraight_instantiate, AdaptiveCircuit.relabel_tCount]
    exact GenericW.compiled17_tCount start _ h
  | left19 j =>
    change ((castFinish _ (reindexStraight _ (relabelStraight _ (GenericW.compiledProgram18 start)))).instantiate read h).tCount ≤ _
    rw [castFinish_instantiate, reindexStraight_instantiate, relabelStraight_instantiate, AdaptiveCircuit.relabel_tCount]
    exact GenericW.compiled18_tCount start _ h
  | right17 j =>
    change ((castFinish _ (reindexStraight _ (relabelStraight _ (GenericW.compiledProgramTrunc16 start)))).instantiate read h).tCount ≤ _
    rw [castFinish_instantiate, reindexStraight_instantiate, relabelStraight_instantiate, AdaptiveCircuit.relabel_tCount]
    exact GenericW.compiledTrunc16_tCount start _ h
  | right18 j =>
    change ((castFinish _ (reindexStraight _ (relabelStraight _ (GenericW.compiledProgramTrunc17 start)))).instantiate read h).tCount ≤ _
    rw [castFinish_instantiate, reindexStraight_instantiate, relabelStraight_instantiate, AdaptiveCircuit.relabel_tCount]
    exact GenericW.compiledTrunc17_tCount start _ h

theorem bodyCatWin_cost18 (d : Digit25) (start : Nat) : cost18 ((bodyCatWin d).program start) = 0 := by
  apply CatAxis.cost18_zero_of_removed18
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
  cases d with
  | left18 j =>
    change removed 18 (castFinish _ (reindexStraight _ (relabelStraight _ (GenericW.compiledProgram17 start)))) = 0
    rw [LocalFour.removed_castFinish, removed18_reindex, hrel]; exact GenericW.compiled17_removed18 start
  | left19 j =>
    change removed 18 (castFinish _ (reindexStraight _ (relabelStraight _ (GenericW.compiledProgram18 start)))) = 0
    rw [LocalFour.removed_castFinish, removed18_reindex, hrel]; exact GenericW.compiled18_removed18 start
  | right17 j =>
    change removed 18 (castFinish _ (reindexStraight _ (relabelStraight _ (GenericW.compiledProgramTrunc16 start)))) = 0
    rw [LocalFour.removed_castFinish, removed18_reindex, hrel]; exact GenericW.compiledTrunc16_removed18 start
  | right18 j =>
    change removed 18 (castFinish _ (reindexStraight _ (relabelStraight _ (GenericW.compiledProgramTrunc17 start)))) = 0
    rw [LocalFour.removed_castFinish, removed18_reindex, hrel]; exact GenericW.compiledTrunc17_removed18 start

theorem first20CatWin_wellFormed (start : Nat) : (first20CatWin.program start).WellFormed := by
  apply straight_append_wellFormed
  · apply ConditionalCatalyst.compile_wellFormed 1 _ _
      (literalProgram_wellFormed _ (sineFromPlus_wellFormed top10Left top10Left_length top10Left_nodup))
    apply LocalFour.fresh_of_not_mem_straightWires
    intro hm
    exact wire01_not_first20Bits.2 (top10Left_sub_bits (sineFromPlus_wires top10Left top10Left_length
      (literalProgram_straightWires _ hm)))
  · exact first20Core_wellFormed start

theorem first20CatWin_slots (start : Nat) : (first20CatWin.program start).gateSlots ≤ 60000000000 := by
  change ((ConditionalCatalyst.compile 1 (literalProgram (sineFromPlus top10Left))).append (first20Core start)).gateSlots ≤ _
  rw [Straight.gateSlots_append]
  unfold first20Core
  rw [Straight.gateSlots_append, Straight.gateSlots_append, castFinish_gateSlots,
    ChallengeMigration.literalProgram_slots, ChallengeMigration.literalProgram_slots]
  have hs1 := ConditionalCatalyst.compile_slots 1 (literalProgram (n := 3407872) (s := start) (sineFromPlus top10Left))
  have hs2 := ConditionalCatalyst.phaseTwos_le_slots (literalProgram (n := 3407872) (s := start) (sineFromPlus top10Left))
  have hs3 : (literalProgram (n := 3407872) (s := start) (sineFromPlus top10Left)).gateSlots = 52 := by
    rw [ChallengeMigration.literalProgram_slots, sineFromPlus_length top10Left top10Left_length]
  have hl1 := LocalFour.compileLower_slots 0 1 (first20RawWin.program 0) start Fin.elim0
  have hl2 : (first20RawWin.program 0).gateSlots ≤ 13100000000 := First20Signed.window_slots firstRow25 0
  have hl3 : AndGadget.added (first20RawWin.program 0) ≤ 193625 := by
    unfold first20RawWin First20Signed.windowGeneric; rw [added_reindex]; exact First20Signed.program_added 0
  simp only [List.length_singleton]
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

theorem first20CatWin_tCount (start : Nat) (read : ConstantBit 3407872 → Bool) (h : Fin start → Bool) :
    ((first20CatWin.program start).instantiate read h).tCount ≤ 4 * 193625 + 28 := by
  change (((ConditionalCatalyst.compile 1 (literalProgram (sineFromPlus top10Left))).append
    (first20Core start)).instantiate read h).tCount ≤ _
  have hlitX_t : ∀ (s : Nat) (h' : Fin s → Bool),
      ((literalProgram (n := 3407872) (s := s) [.X 836]).instantiate read h').tCount = 0 := fun s h' => by
    simp [literalProgram, gateProgram, Straight.instantiate, TemplateGate.instantiate,
      AdaptiveCircuit.tCount, ShorECDLP.tCount, tCost]
  have hcore_t : ∀ h' : Fin start → Bool, ((first20Core start).instantiate read h').tCount ≤ 4 * 193625 := by
    intro h'
    unfold first20Core
    have h1 := CatAxis.append_tCount_le
      ((literalProgram (n := 3407872) (s := start) [.X 836]).append
        (castFinish (first20Cat_finish_eq start)
          (LocalFour.compileLower 0 1 (first20RawWin.program 0) start Fin.elim0).program))
      (literalProgram [.X 836]) read h' 0 (fun h'' => le_of_eq (hlitX_t _ h''))
    have h2 := CatAxis.append_tCount_le
      (literalProgram (n := 3407872) (s := start) [.X 836])
      (castFinish (first20Cat_finish_eq start)
        (LocalFour.compileLower 0 1 (first20RawWin.program 0) start Fin.elim0).program)
      read h' (4 * 193625) (fun h'' => by
        rw [castFinish_instantiate]
        have hlo := LocalFour.compileLower_tCount 0 1 (first20RawWin.program 0) start Fin.elim0 read h''
        have hz : residue (first20RawWin.program 0) = 0 := First20Signed.window_residue firstRow25 0
        have ha : added (first20RawWin.program 0) ≤ 193625 := by
          unfold first20RawWin First20Signed.windowGeneric; rw [added_reindex]; exact First20Signed.program_added 0
        rw [weight4_zero _ hz] at hlo
        omega)
    rw [hlitX_t] at h2
    omega
  have h1 := CatAxis.append_tCount_le
    (ConditionalCatalyst.compile 1 (literalProgram (n := 3407872) (s := start) (sineFromPlus top10Left)))
    (first20Core start) read h (4 * 193625) hcore_t
  have hsine_t : ((ConditionalCatalyst.compile 1 (literalProgram (n := 3407872) (s := start)
      (sineFromPlus top10Left))).instantiate read h).tCount ≤ 28 := by
    have ht := ConditionalCatalyst.compile_t 1
      (literalProgram (n := 3407872) (s := start) (sineFromPlus top10Left)) read h
    rw [sineFromPlus_weight7_eq_weight4, sineFromPlus_weight4 top10Left top10Left_length] at ht
    exact ht
  omega

theorem rightHeadCatWin_wellFormed (start : Nat) : (rightHeadCatWin.program start).WellFormed := by
  apply straight_append_wellFormed
  · apply ConditionalCatalyst.compile_wellFormed 1 _ _
      (literalProgram_wellFormed _ (sineFromPlus_wellFormed top10Right top10Right_length top10Right_nodup))
    apply LocalFour.fresh_of_not_mem_straightWires
    intro hm
    exact wire1_not_bankW (top10Right_sub_bank (sineFromPlus_wires top10Right top10Right_length
      (literalProgram_straightWires _ hm)))
  · exact bodyCatWin_wellFormed rightHeadDigit start

theorem rightHeadCatWin_slots (start : Nat) : (rightHeadCatWin.program start).gateSlots ≤ 80000000400 := by
  change ((ConditionalCatalyst.compile 1 (literalProgram (sineFromPlus top10Right))).append
    ((bodyCatWin rightHeadDigit).program start)).gateSlots ≤ _
  rw [Straight.gateSlots_append]
  have hs : (ConditionalCatalyst.compile 1 (literalProgram (n := 3407872) (s := start) (sineFromPlus top10Right))).gateSlots ≤ 400 := by
    have hs1 := ConditionalCatalyst.compile_slots 1 (literalProgram (n := 3407872) (s := start) (sineFromPlus top10Right))
    have hs2 := ConditionalCatalyst.phaseTwos_le_slots (literalProgram (n := 3407872) (s := start) (sineFromPlus top10Right))
    have hs3 : (literalProgram (n := 3407872) (s := start) (sineFromPlus top10Right)).gateSlots = 52 := by
      rw [ChallengeMigration.literalProgram_slots, sineFromPlus_length top10Right top10Right_length]
    omega
  exact (Nat.add_le_add hs (bodyCatWin_slots rightHeadDigit start)).trans (by decide)

theorem rightHeadCatWin_tCount (start : Nat) (read : ConstantBit 3407872 → Bool) (h : Fin start → Bool) :
    ((rightHeadCatWin.program start).instantiate read h).tCount ≤ 4 * 2171700 + 28 := by
  change (((ConditionalCatalyst.compile 1 (literalProgram (sineFromPlus top10Right))).append
    ((bodyCatWin rightHeadDigit).program start)).instantiate read h).tCount ≤ _
  have h1 := CatAxis.append_tCount_le
    (ConditionalCatalyst.compile 1 (literalProgram (n := 3407872) (s := start) (sineFromPlus top10Right)))
    ((bodyCatWin rightHeadDigit).program start) read h (4 * 2171700)
    (fun h' => bodyCatWin_tCount rightHeadDigit start read h')
  have hsine_t : ((ConditionalCatalyst.compile 1 (literalProgram (n := 3407872) (s := start)
      (sineFromPlus top10Right))).instantiate read h).tCount ≤ 28 := by
    have ht := ConditionalCatalyst.compile_t 1
      (literalProgram (n := 3407872) (s := start) (sineFromPlus top10Right)) read h
    rw [sineFromPlus_weight7_eq_weight4, sineFromPlus_weight4 top10Right top10Right_length] at ht
    exact ht
  exact h1.trans (Nat.add_le_add_right hsine_t _ |>.trans (by omega))

theorem win25Cat_wellFormed (w : Window 3407872) (hw : IsWin25Cat w) (start : Nat) :
    (w.program start).WellFormed := by
  rcases hw with rfl | rfl | ⟨d, rfl⟩
  · exact first20CatWin_wellFormed start
  · exact rightHeadCatWin_wellFormed start
  · exact bodyCatWin_wellFormed d start

theorem win25Cat_bank_support (w : Window 3407872) (hw : IsWin25Cat w) : w.wires ⊆ List.range 1612 := by
  rcases hw with rfl | rfl | ⟨d, rfl⟩
  · intro v hv; exact range1610_sub_1612 (First20Signed.bits_subset_range (List.mem_reverse.mp hv))
  · intro v hv; exact bankW_sub_range (by decide) (List.mem_reverse.mp hv)
  · intro v hv; rw [bodyCatWin_wires] at hv; exact bankW_sub_range d.k_hi (List.mem_reverse.mp hv)

theorem win25Cat_noY (w : Window 3407872) (hw : IsWin25Cat w) : (1 : Wire) ∉ w.wires := by
  rcases hw with rfl | rfl | ⟨d, rfl⟩
  · exact fun hm => wire01_not_first20Bits.2 (List.mem_reverse.mp hm)
  · exact fun hm => wire1_not_bankW (List.mem_reverse.mp hm)
  · rw [bodyCatWin_wires]; exact fun hm => wire1_not_bankW (List.mem_reverse.mp hm)

theorem win25Cat_support (w : Window 3407872) (hw : IsWin25Cat w) (start : Nat)
    (read : ConstantBit 3407872 → Bool) (history : Fin start → Bool) :
    ((w.program start).instantiate read history).wires ⊆ List.range 1612 := by
  rcases hw with rfl | rfl | ⟨d, rfl⟩
  · apply outer_append_support _ _ read history (List.range 1612)
    · have hw1 : Within (List.range 1612)
          (literalProgram (n := 3407872) (s := start) (sineFromPlus top10Left)) :=
        LocalFour.within_of_straightWires _ _
          ((literalProgram_straightWires _).trans
            ((sineFromPlus_wires top10Left top10Left_length).trans top10Left_sub_range))
      have hsup := (ConditionalCatalyst.compile_within 1 _ _ hw1).instantiate read history
      intro u hu
      rcases List.mem_cons.mp (hsup hu) with rfl | hm
      · exact List.mem_range.mpr (by decide)
      · exact hm
    · intro h'
      unfold first20Core
      have hx_sup : ∀ (s : Nat) (hs : Fin s → Bool),
          ((literalProgram (n := 3407872) (s := s) [.X 836]).instantiate read hs).wires ⊆ List.range 1612 := by
        intro s hs u hu
        have hm := literalProgram_straightWires [.X 836] (straight_instantiate_support _ read hs hu)
        simp only [circuitWires, gateWires, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          List.mem_singleton] at hm
        subst hm; exact List.mem_range.mpr (by decide)
      apply outer_append_support _ _ read h' (List.range 1612) _ (fun h'' => hx_sup _ h'')
      apply outer_append_support _ _ read h' (List.range 1612) (hx_sup start h')
      intro h''
      rw [castFinish_instantiate]
      refine (straight_instantiate_support _ read h'').trans ?_
      exact LocalFour.compileLower_straightWires 0 1 (first20RawWin.program 0) (List.range 1612)
        ((First20Signed.window_support firstRow25 0).trans range1610_sub_1612)
        (List.mem_range.mpr (by decide)) (List.mem_range.mpr (by decide)) start Fin.elim0
  · apply outer_append_support _ _ read history (List.range 1612)
    · have hw1 : Within (List.range 1612)
          (literalProgram (n := 3407872) (s := start) (sineFromPlus top10Right)) :=
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

theorem win25Cat_cost18 (w : Window 3407872) (hw : IsWin25Cat w) (start : Nat) :
    cost18 (w.program start) = 0 := by
  rcases hw with rfl | rfl | ⟨d, rfl⟩
  · change cost18 ((ConditionalCatalyst.compile 1 (literalProgram (sineFromPlus top10Left))).append
      (first20Core start)) = 0
    rw [cost18_append, CatAxis.cost18_compile,
      cost18_literal_zero _ (sineFromPlus_largePhase_false top10Left 18 (by decide)), zero_add]
    unfold first20Core
    rw [cost18_append, cost18_append,
      cost18_literal_zero [.X 836] (by decide), cost18_literal_zero [.X 836] (by decide),
      zero_add, add_zero, cost18_cast]
    apply CatAxis.cost18_zero_of_removed18
    rw [LocalFour.compileLower_removed18]
    exact LocalFour.removed18_zero_of_residue _ (First20Signed.window_residue firstRow25 0)
  · change cost18 ((ConditionalCatalyst.compile 1 (literalProgram (sineFromPlus top10Right))).append _) = 0
    rw [cost18_append, CatAxis.cost18_compile,
      cost18_literal_zero _ (sineFromPlus_largePhase_false top10Right 18 (by decide)), zero_add]
    exact bodyCatWin_cost18 rightHeadDigit start
  · exact bodyCatWin_cost18 d start

theorem program25Cat_wellFormed : program25Cat.WellFormed := by
  unfold program25Cat
  apply Catalyst.literals_wellFormed _ _ (LocalFour.prepare_wellFormed 1)
  rw [castFinish_wellFormed]
  apply straight_append_wellFormed _ _ _ (resetProgram_wellFormed _ _ _)
  apply straight_append_wellFormed
  · exact CatAxis.axisCat_wellFormed 1 leftWins25Cat
      (fun w hw => by
        rcases List.mem_cons.mp hw with rfl | hw
        · exact win25Cat_noY _ (Or.inl rfl)
        · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hw
          exact win25Cat_noY _ (Or.inr (Or.inr ⟨d, rfl⟩)))
      (fun w hw start => by
        rcases List.mem_cons.mp hw with rfl | hw
        · exact win25Cat_wellFormed _ (Or.inl rfl) start
        · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hw
          exact win25Cat_wellFormed _ (Or.inr (Or.inr ⟨d, rfl⟩)) start) _ _
  · exact CatAxis.axisCat_wellFormed 1 rightWins25Cat
      (fun w hw => by
        rcases List.mem_cons.mp hw with rfl | hw
        · exact win25Cat_noY _ (Or.inr (Or.inl rfl))
        · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hw
          exact win25Cat_noY _ (Or.inr (Or.inr ⟨d, rfl⟩)))
      (fun w hw start => by
        rcases List.mem_cons.mp hw with rfl | hw
        · exact win25Cat_wellFormed _ (Or.inr (Or.inl rfl)) start
        · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hw
          exact win25Cat_wellFormed _ (Or.inr (Or.inr ⟨d, rfl⟩)) start) _ _

theorem full25Cat_wellFormed : fullProgram25Cat.WellFormed :=
  straight_append_wellFormed _ _ program25Cat_wellFormed readout25Cat_wellFormed

theorem strong_success25Cat (Q : Point) (d : Nat) (hn : Q ≠ 0) (hd : Q = d • G) :
    (9922 / 10000 : ℝ) ≤ Instrument.bornMass
      ((rawEntry25Cat.instantiate Q).run.filter (fun b => (verifiedCandidate rawLayout25Cat Q b.history).isSome))
      (ket zeroBasisState) := by
  have hQ : order • Q = 0 := by rw [hd, smul_comm order d, generator_nsmul_eq_zero, nsmul_zero]
  rw [rawEntry25Cat, Single.fixedEntry_instantiate]
  have hneighbor : (9922 / 10000 : ℝ) ≤ Instrument.bornMass
      ((program25Cat.instantiate (readConstant coefficientAt25 Q) Fin.elim0).run.filter
        (fun b => fineEvent25Cat (pairRecovered256 d) b.history)) (ket zeroBasisState) := by
    have hideal_succ : (9924 / 10000 : ℝ) ≤ windowedEventMass Q zeroBasisState 256 206 (pairRecovered256 d) := by
      rw [windowedEventMass_distribution Q d hd zeroBasisState 256 206]
      exact sine_pair_success_256_206 Q d hn hd
    have hideal_compl : windowedEventMass Q zeroBasisState 256 206 (pairRecovered256 d) +
        windowedEventMass Q zeroBasisState 256 206 (fun a b => !pairRecovered256 d a b) = 1 := by
      rw [windowedEventMass_distribution Q d hd zeroBasisState 256 206,
        windowedEventMass_distribution Q d hd zeroBasisState 256 206]
      have hadd : (∑ a : Fin (2 ^ 256), ∑ b : Fin (2 ^ 206),
            if pairRecovered256 d a.val b.val then sinePairMass order 256 206 d (a, b) else 0) +
          (∑ a : Fin (2 ^ 256), ∑ b : Fin (2 ^ 206),
            if !pairRecovered256 d a.val b.val then sinePairMass order 256 206 d (a, b) else 0) =
          ∑ a : Fin (2 ^ 256), ∑ b : Fin (2 ^ 206), sinePairMass order 256 206 d (a, b) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro a _
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro b _
        cases pairRecovered256 d a.val b.val <;> simp
      rw [hadd]
      have hswap : ∀ k : Fin order,
          ∑ a : Fin (2 ^ 256), ∑ b : Fin (2 ^ 206),
            Complex.normSq (sinePhaseAmplitude 256 ((k.val : ℝ) / order) a.val) *
            Complex.normSq (sinePhaseAmplitude 206 (((d * k.val % order : Nat) : ℝ) / order) b.val) = 1 := by
        intro k
        rw [← Finset.sum_mul_sum,
          Fin.sum_univ_eq_sum_range (fun a => Complex.normSq (sinePhaseAmplitude 256 _ a)),
          Fin.sum_univ_eq_sum_range (fun b => Complex.normSq (sinePhaseAmplitude 206 _ b)),
          sinePhaseAmplitude_parseval 256 (by decide), sinePhaseAmplitude_parseval 206 (by decide), mul_one]
      simp only [sinePairMass]
      simp_rw [← Finset.mul_sum]
      have hcomm1 : (∑ a : Fin (2 ^ 256), ∑ b : Fin (2 ^ 206), ∑ k : Fin order,
            Complex.normSq (sinePhaseAmplitude 256 ((k.val : ℝ) / order) a.val) *
            Complex.normSq (sinePhaseAmplitude 206 (((d * k.val % order : Nat) : ℝ) / order) b.val)) =
          ∑ k : Fin order, ∑ a : Fin (2 ^ 256), ∑ b : Fin (2 ^ 206),
            Complex.normSq (sinePhaseAmplitude 256 ((k.val : ℝ) / order) a.val) *
            Complex.normSq (sinePhaseAmplitude 206 (((d * k.val % order : Nat) : ℝ) / order) b.val) := by
        trans (∑ a : Fin (2 ^ 256), ∑ k : Fin order, ∑ b : Fin (2 ^ 206),
            Complex.normSq (sinePhaseAmplitude 256 ((k.val : ℝ) / order) a.val) *
            Complex.normSq (sinePhaseAmplitude 206 (((d * k.val % order : Nat) : ℝ) / order) b.val))
        · apply Finset.sum_congr rfl; intro a _; exact Finset.sum_comm
        · exact Finset.sum_comm
      rw [hcomm1]
      simp_rw [hswap]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr order_prime.ne_zero)
    have hideal_fail : windowedEventMass Q zeroBasisState 256 206 (fun a b => !pairRecovered256 d a b) ≤ 76 / 10000 := by
      linarith
    have hread_some : ∀ (h : List Bool) (ws : List Nat), (∀ i ∈ ws, i < h.length) → ∃ v, readWord h ws = some v := by
      intro h ws
      induction ws with
      | nil => intro _; exact ⟨0, rfl⟩
      | cons i rest ih =>
        intro hlt
        obtain ⟨v, hv⟩ := ih (fun j hj => hlt j (List.mem_cons_of_mem _ hj))
        have hi : i < h.length := hlt i List.mem_cons_self
        refine ⟨(if h[i] then 1 else 0) + 2 * v, ?_⟩
        simp [readWord, List.getElem?_eq_getElem hi, hv]
    set runL := (program25Cat.instantiate (readConstant coefficientAt25 Q) Fin.elim0).run
    have hfilt_compl : runL.filter (fun b => fineEvent25Cat (fun a c => !pairRecovered256 d a c) b.history) =
        runL.filter (fun b => !fineEvent25Cat (pairRecovered256 d) b.history) := by
      apply List.filter_congr
      intro b hb
      have hlen : b.history.length = cursor25Cat := by
        have h := straight_history_length program25Cat (readConstant coefficientAt25 Q) Fin.elim0 b hb
        simpa only [Nat.zero_add, Nat.sub_zero] using h
      obtain ⟨va, hva⟩ := hread_some b.history trialPositions25Cat.left.toList (fun i hi => by
        rw [hlen]; exact (leftPositions25Cat_bound i hi).trans_le (by unfold cursor25Cat; omega))
      obtain ⟨vb, hvb⟩ := hread_some b.history trialPositions25Cat.right.toList (fun i hi => by
        rw [hlen]; exact (rightPositions25Cat_bound i hi).trans_le (by unfold cursor25Cat; omega))
      simp [fineEvent25Cat, pairAccept, hva, hvb]
    have hphys_compl : Instrument.bornMass (runL.filter (fun b => fineEvent25Cat (pairRecovered256 d) b.history)) (ket zeroBasisState) +
        Instrument.bornMass (runL.filter (fun b => fineEvent25Cat (fun a c => !pairRecovered256 d a c) b.history)) (ket zeroBasisState) = 1 := by
      rw [hfilt_compl]
      have hsplit : ∀ (I : Instrument) (p : InstrumentBranch → Bool) (ψ : State),
          Instrument.bornMass (I.filter p) ψ + Instrument.bornMass (I.filter (fun b => !p b)) ψ = I.bornMass ψ := by
        intro I p ψ
        induction I with
        | nil => simp [Instrument.bornMass]
        | cons b bs ih =>
          cases hp : p b <;> simp only [List.filter_cons, hp, Bool.not_true, Bool.not_false,
            Bool.false_eq_true, ite_true, ite_false, Instrument.bornMass, List.map_cons, List.sum_cons] at ih ⊢ <;> linarith
      rw [hsplit]
      have hp := AdaptiveCircuit.run_preservesBornMass _
        (program25Cat.instantiate_wellFormed (readConstant coefficientAt25 Q) Fin.elim0 program25Cat_wellFormed)
        (ket zeroBasisState)
      simpa only [runL, normSq_ket] using hp
    have hup := program25Cat_event_mass_upper Q hQ hn (fun a b => !pairRecovered256 d a b)
    have hpowR : ((1 + (1 / 3000 : ℝ)) ^ 2) ^ 12 ≤ 10081 / 10000 := by norm_num
    have hpowL : ((1 + (1 / 10 ^ 8 : ℝ)) ^ 2) ^ 13 ≤ 1 + 52 / 10 ^ 8 := by
      rw [← pow_mul]
      have h1 := one_add_pow_le (1 / 10 ^ 8 : ℝ) 26 (by positivity) (by norm_num)
      linarith
    have hpowLR : ((1 + (1 / 3000 : ℝ)) ^ 2) ^ 12 * ((1 + (1 / 10 ^ 8 : ℝ)) ^ 2) ^ 13 ≤ 10082 / 10000 := by
      have h0 : 0 ≤ ((1 + (1 / 3000 : ℝ)) ^ 2) ^ 12 := by positivity
      have h1 : 0 ≤ ((1 + (1 / 10 ^ 8 : ℝ)) ^ 2) ^ 13 := by positivity
      nlinarith
    have hF_nn : 0 ≤ windowedEventMass Q zeroBasisState 256 206 (fun a b => !pairRecovered256 d a b) := by
      rw [windowedEventMass_distribution Q d hd zeroBasisState 256 206]
      apply Finset.sum_nonneg; intro a _
      apply Finset.sum_nonneg; intro b _
      split_ifs
      · unfold sinePairMass
        apply mul_nonneg (by positivity)
        apply Finset.sum_nonneg; intro k _
        exact mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
      · exact le_rfl
    have herrL : (((1 + (1 / 10 ^ 8 : ℝ)) ^ 2) ^ 13 *
        (2 + 1 / 10 ^ 8) * (1 + 1 / (1 / 10 ^ 8))) * ((4 : ℝ) / (2 : ℝ) ^ 236) ≤ 1 / 10 ^ 6 := by
      have hBL : ((1 + (1 / 10 ^ 8 : ℝ)) ^ 2) ^ 13 *
          (2 + 1 / 10 ^ 8) * (1 + 1 / (1 / 10 ^ 8)) ≤ 10 ^ 9 := by nlinarith
      have h236 : (10 ^ 9 : ℝ) * ((4 : ℝ) / (2 : ℝ) ^ 236) ≤ 1 / 10 ^ 6 := by norm_num
      nlinarith
    have herrR : (((1 + (1 / 3000 : ℝ)) ^ 2) ^ 12 * ((1 + (1 / 10 ^ 8 : ℝ)) ^ 2) ^ 13 *
        (2 + 1 / 3000) * (1 + 1 / (1 / 3000))) * ((145 : ℝ) / 10 ^ 10) ≤ 9 / 10 ^ 5 := by
      have hBR : ((1 + (1 / 3000 : ℝ)) ^ 2) ^ 12 * ((1 + (1 / 10 ^ 8 : ℝ)) ^ 2) ^ 13 *
          (2 + 1 / 3000) * (1 + 1 / (1 / 3000)) ≤ 6100 := by nlinarith
      nlinarith
    nlinarith
  apply hneighbor.trans
  unfold fullProgram25Cat
  rw [Single.append_run_history]
  apply Rounded.appended_mass_lower
  · intro a _
    exact AdaptiveCircuit.run_preservesBornMass _
      (readout25Cat.instantiate_wellFormed _ _ readout25Cat_wellFormed) _
  · intro a ha hf b hb hne
    have hlen : a.history.length = cursor25Cat := by
      have h := straight_history_length program25Cat (readConstant coefficientAt25 Q) Fin.elim0 a ha
      simpa only [Nat.zero_add, Nat.sub_zero] using h
    have hh : List.ofFn (Single.historyAfter cursor25Cat Fin.elim0 a.history) = a.history := by
      simpa only [List.ofFn_zero, List.nil_append] using Single.historyAfter_list Fin.elim0 a.history
        (by simpa only [Nat.zero_add] using hlen)
    have h := suffix25Cat_accept Q d hd (readConstant coefficientAt25 Q)
      (Single.historyAfter cursor25Cat Fin.elim0 a.history) (a.kraus (ket zeroBasisState))
      (program25Cat_clean _ a ha _) (by simpa only [hh] using hf) b hb hne
    simpa only [hh, InstrumentBranch.seq] using h

theorem full25Cat_slots : fullProgram25Cat.gateSlots ≤ 10000000000000 := by
  have hL := CatAxis.axisCat_slots 1 leftWins25Cat 80000000400
    (fun w hw start => by
      rcases List.mem_cons.mp hw with rfl | hw
      · exact (first20CatWin_slots start).trans (by omega)
      · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hw
        exact (bodyCatWin_slots d start).trans (by omega))
    0 List.nil
  have hR := CatAxis.axisCat_slots 1 rightWins25Cat 80000000400
    (fun w hw start => by
      rcases List.mem_cons.mp hw with rfl | hw
      · exact rightHeadCatWin_slots start
      · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hw
        exact (bodyCatWin_slots d start).trans (by omega))
    (0 + axisCount leftWins25Cat) List.nil
  rw [leftWins25Cat_meta, List.length_nil] at hL
  rw [rightWins25Cat_meta, List.length_nil] at hR
  have hLnum : metadataSlots 80000000400 leftMeta25Cat 0 ≤ 1300000000000 := by
    simp only [leftMeta25Cat, List.replicate, List.cons_append, List.nil_append,
      metadataSlots, fourierSlots]
    omega
  have hRnum : metadataSlots 80000000400 rightMeta25Cat 0 ≤ 1100000000000 := by
    simp only [rightMeta25Cat, List.replicate, List.cons_append, List.nil_append,
      metadataSlots, fourierSlots]
    omega
  have hro : readout25Cat.gateSlots = 22652 := by
    unfold readout25Cat readoutL25 readoutR25
    rw [castFinish_gateSlots, Straight.gateSlots_append, castFinish_gateSlots, castFinish_gateSlots,
      Readout5.suffix5_slots, Readout5.suffix5_slots]
  unfold fullProgram25Cat program25Cat
  rw [Straight.gateSlots_append, AndGadget.literals_slots, castFinish_gateSlots,
    Straight.gateSlots_append, Straight.gateSlots_append, resetProgram_gateSlots, hro]
  have hres : resetWires.length ≤ 2000 := by simp [resetWires]
  have hprep : (Catalyst.prepare 1).length = 2 := rfl
  omega

theorem full25Cat_support (read : ConstantBit 3407872 → Bool) (history : Fin 0 → Bool) :
    (fullProgram25Cat.instantiate read history).wires ⊆ List.range 1612 := by
  apply outer_append_support _ _ read history (List.range 1612)
  · unfold program25Cat
    have hlit : Within (List.range 1612)
        (AndGadget.literals (Catalyst.prepare 1)
          (castFinish (show 0 + axisCount leftWins25Cat + axisCount rightWins25Cat + resetWires.length = cursor25Cat by unfold cursor25Cat; omega)
            (((CatAxis.axisCat 1 leftWins25Cat 0 List.nil).append
              (CatAxis.axisCat 1 rightWins25Cat (0 + axisCount leftWins25Cat) List.nil)).append
                (resetProgram 3407872 (0 + axisCount leftWins25Cat + axisCount rightWins25Cat) resetWires)))) := by
      apply Catalyst.literals_within
      · intro u hu
        simp only [Catalyst.prepare, circuitWires, gateWires, List.flatMap_cons, List.flatMap_nil,
          List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl <;> exact List.mem_range.mpr (by decide)
      · apply within_of_instantiate
        intro r h0
        rw [castFinish_instantiate]
        apply outer_append_support _ _ r h0 (List.range 1612) _
          (fun h2 => resetProgram_support _ _ _ _ r h2 (Width16Actual.reset_range.trans range1610_sub_1612))
        apply outer_append_support _ _ r h0 (List.range 1612)
        · exact CatAxis.axisCat_support 1 leftWins25Cat (List.range 1612)
            (List.mem_range.mpr (by decide))
            (fun w hw => by
              rcases List.mem_cons.mp hw with rfl | hw
              · exact win25Cat_bank_support _ (Or.inl rfl)
              · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hw
                exact win25Cat_bank_support _ (Or.inr (Or.inr ⟨d, rfl⟩)))
            (fun w hw start r' h' => by
              rcases List.mem_cons.mp hw with rfl | hw
              · exact win25Cat_support _ (Or.inl rfl) start r' h'
              · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hw
                exact win25Cat_support _ (Or.inr (Or.inr ⟨d, rfl⟩)) start r' h')
            0 List.nil r h0
        · intro h1
          exact CatAxis.axisCat_support 1 rightWins25Cat (List.range 1612)
            (List.mem_range.mpr (by decide))
            (fun w hw => by
              rcases List.mem_cons.mp hw with rfl | hw
              · exact win25Cat_bank_support _ (Or.inr (Or.inl rfl))
              · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hw
                exact win25Cat_bank_support _ (Or.inr (Or.inr ⟨d, rfl⟩)))
            (fun w hw start r' h' => by
              rcases List.mem_cons.mp hw with rfl | hw
              · exact win25Cat_support _ (Or.inr (Or.inl rfl)) start r' h'
              · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hw
                exact win25Cat_support _ (Or.inr (Or.inr ⟨d, rfl⟩)) start r' h')
            (0 + axisCount leftWins25Cat) List.nil r h1
    exact hlit.instantiate read history
  · intro h
    unfold readout25Cat readoutL25 readoutR25
    rw [castFinish_instantiate]
    have h01 : ([0, 1] : List Wire) ⊆ List.range 1612 := fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> exact List.mem_range.mpr (by decide)
    apply outer_append_support _ _ read h (List.range 1612)
    · rw [castFinish_instantiate]; exact (Readout5.suffix5_support _ _ _ _ read h).trans h01
    · intro h1; rw [castFinish_instantiate]; exact (Readout5.suffix5_support _ _ _ _ read h1).trans h01

theorem source25Cat_within : Within (List.range 1612) rawEntry25Cat.program := by
  unfold rawEntry25Cat Single.fixedEntry
  dsimp only
  exact Width16Actual.within_reindex fullProgram25Cat _ (List.range 1612)
    (within_of_instantiate fullProgram25Cat (List.range 1612) full25Cat_support)

def leftTCountMeta25Cat : List (Nat × Nat) :=
  (4 * 193625 + 28, 20) :: List.replicate 11 (4 * 2319661, 18) ++ List.replicate 2 (4 * 2483757, 19)

def rightTCountMeta25Cat : List (Nat × Nat) :=
  (4 * 2171700 + 28, 17) :: List.replicate 9 (4 * 2171700, 17) ++ List.replicate 2 (4 * 2253875, 18)

theorem exact_trimmed_tCount25Cat :
    CatAxis.metadataTrimmedWeight leftTCountMeta25Cat 0 +
      CatAxis.metadataTrimmedWeight rightTCountMeta25Cat 0 = 227615784 := by
  decide +kernel

theorem left25Cat_tCount_relation :
    List.Forall₂ (fun w k => w.wires.length = k.2 ∧
        ∀ start read h, ((w.program start).instantiate read h).tCount ≤ k.1)
      leftWins25Cat leftTCountMeta25Cat := by
  refine .cons ⟨by simp [first20CatWin, First20Signed.bits_length], first20CatWin_tCount⟩ ?_
  have hmap : List.replicate 11 (4 * 2319661, 18) ++ List.replicate 2 (4 * 2483757, 19) =
      leftDigits25.map (fun d => (4 * d.tof, d.width)) := by
    simp [leftDigits25, List.ofFn_succ, List.replicate, Digit25.tof, Digit25.width, Digit25.k]
  change List.Forall₂ _ (leftDigits25.map bodyCatWin) (List.replicate 11 (4 * 2319661, 18) ++ List.replicate 2 (4 * 2483757, 19))
  rw [hmap]
  induction leftDigits25 with
  | nil => exact .nil
  | cons d ds ih =>
    exact .cons ⟨by simp [bodyCatWin_wires, Digit25.bank, Digit25.width, GenericW.bankW_length], bodyCatWin_tCount d⟩ ih

theorem right25Cat_tCount_relation :
    List.Forall₂ (fun w k => w.wires.length = k.2 ∧
        ∀ start read h, ((w.program start).instantiate read h).tCount ≤ k.1)
      rightWins25Cat rightTCountMeta25Cat := by
  refine .cons ⟨by simp [rightHeadCatWin, GenericW.bankW_length], rightHeadCatWin_tCount⟩ ?_
  have hmap : List.replicate 9 (4 * 2171700, 17) ++ List.replicate 2 (4 * 2253875, 18) =
      rightTailDigits25.map (fun d => (4 * d.tof, d.width)) := by
    simp [rightTailDigits25, List.ofFn_succ, List.replicate, Digit25.tof, Digit25.width, Digit25.k]
  change List.Forall₂ _ (rightTailDigits25.map bodyCatWin) (List.replicate 9 (4 * 2171700, 17) ++ List.replicate 2 (4 * 2253875, 18))
  rw [hmap]
  induction rightTailDigits25 with
  | nil => exact .nil
  | cons d ds ih =>
    exact .cons ⟨by simp [bodyCatWin_wires, Digit25.bank, Digit25.width, GenericW.bankW_length], bodyCatWin_tCount d⟩ ih

theorem full25Cat_trim18_tCount (read : ConstantBit 3407872 → Bool) (h : Fin 0 → Bool) :
    ((trim 18 fullProgram25Cat).instantiate read h).tCount ≤ 227615785 := by
  unfold fullProgram25Cat program25Cat
  have hprep_nf : ∀ g ∈ Catalyst.prepare 1, largePhase 18 g = false := by decide
  rw [CatAxis.trim18_append, CatAxis.trim18_literals_false _ _ hprep_nf]
  have hro_t : ∀ h' : Fin cursor25Cat → Bool, ((trim 18 readout25Cat).instantiate read h').tCount ≤ 0 := by
    intro h'
    have h1 := trim18_t readout25Cat read h'
    have h2 : (readout25Cat.instantiate read h').tCount = 0 := by
      unfold readout25Cat readoutL25 readoutR25
      rw [castFinish_instantiate]
      apply Readout56.append_t_zero _ _ read
      · intro h0; rw [castFinish_instantiate]; exact Readout5.suffix5_t _ _ _ _ read h0
      · intro h1; rw [castFinish_instantiate]; exact Readout5.suffix5_t _ _ _ _ read h1
    omega
  have h1 := CatAxis.append_tCount_le
    (AndGadget.literals (Catalyst.prepare 1)
      (trim 18 (castFinish (show 0 + axisCount leftWins25Cat + axisCount rightWins25Cat + resetWires.length = cursor25Cat by unfold cursor25Cat; omega)
        (((CatAxis.axisCat 1 leftWins25Cat 0 List.nil).append
          (CatAxis.axisCat 1 rightWins25Cat (0 + axisCount leftWins25Cat) List.nil)).append
            (resetProgram 3407872 (0 + axisCount leftWins25Cat + axisCount rightWins25Cat) resetWires)))))
    (trim 18 readout25Cat) read h 0 hro_t
  rw [Catalyst.literals_t] at h1
  have hprep_t : ShorECDLP.tCount (Catalyst.prepare 1) = 1 := by decide
  rw [hprep_t] at h1
  have hbody_t : ((trim 18 (castFinish (show 0 + axisCount leftWins25Cat + axisCount rightWins25Cat + resetWires.length = cursor25Cat by unfold cursor25Cat; omega)
      (((CatAxis.axisCat 1 leftWins25Cat 0 List.nil).append
        (CatAxis.axisCat 1 rightWins25Cat (0 + axisCount leftWins25Cat) List.nil)).append
          (resetProgram 3407872 (0 + axisCount leftWins25Cat + axisCount rightWins25Cat) resetWires)))).instantiate read h).tCount ≤ 227615784 := by
    rw [CatAxis.trim18_castFinish, castFinish_instantiate, CatAxis.trim18_append, CatAxis.trim18_append]
    have hres_t : ∀ h' : Fin (0 + axisCount leftWins25Cat + axisCount rightWins25Cat) → Bool,
        ((trim 18 (resetProgram 3407872 (0 + axisCount leftWins25Cat + axisCount rightWins25Cat) resetWires)).instantiate read h').tCount ≤ 0 := by
      intro h'
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
      have hle := trim18_t (resetProgram 3407872 (0 + axisCount leftWins25Cat + axisCount rightWins25Cat) resetWires) read h'
      rw [hrt] at hle
      exact hle
    have hLR := CatAxis.append_tCount_le
      ((trim 18 (CatAxis.axisCat 1 leftWins25Cat 0 List.nil)).append
        (trim 18 (CatAxis.axisCat 1 rightWins25Cat (0 + axisCount leftWins25Cat) List.nil)))
      (trim 18 (resetProgram 3407872 (0 + axisCount leftWins25Cat + axisCount rightWins25Cat) resetWires))
      read h 0 hres_t
    have hR_t : ∀ h' : Fin (0 + axisCount leftWins25Cat) → Bool,
        ((trim 18 (CatAxis.axisCat 1 rightWins25Cat (0 + axisCount leftWins25Cat) List.nil)).instantiate read h').tCount ≤
          CatAxis.metadataTrimmedWeight rightTCountMeta25Cat 0 := fun h' => by
      have hax := CatAxis.axisCat_tCount_trim18 1 rightWins25Cat rightTCountMeta25Cat
        right25Cat_tCount_relation (0 + axisCount leftWins25Cat) List.nil read h'
      rwa [List.length_nil] at hax
    have hL := CatAxis.append_tCount_le
      (trim 18 (CatAxis.axisCat 1 leftWins25Cat 0 List.nil))
      (trim 18 (CatAxis.axisCat 1 rightWins25Cat (0 + axisCount leftWins25Cat) List.nil))
      read h _ hR_t
    have hLax := CatAxis.axisCat_tCount_trim18 1 leftWins25Cat leftTCountMeta25Cat
      left25Cat_tCount_relation 0 List.nil read h
    rw [List.length_nil] at hLax
    have hex := exact_trimmed_tCount25Cat
    omega
  omega

theorem source25Cat_cost18 : cost18 rawEntry25Cat.program ≤ 51 / 10000 := by
  have hL := CatAxis.axisCat_cost18_exact 1 leftWins25Cat
    (fun w hw start => by
      rcases List.mem_cons.mp hw with rfl | hw
      · exact win25Cat_cost18 _ (Or.inl rfl) start
      · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hw
        exact win25Cat_cost18 _ (Or.inr (Or.inr ⟨d, rfl⟩)) start) 0 List.nil
  have hR := CatAxis.axisCat_cost18_exact 1 rightWins25Cat
    (fun w hw start => by
      rcases List.mem_cons.mp hw with rfl | hw
      · exact win25Cat_cost18 _ (Or.inr (Or.inl rfl)) start
      · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hw
        exact win25Cat_cost18 _ (Or.inr (Or.inr ⟨d, rfl⟩)) start) (0 + axisCount leftWins25Cat) List.nil
  have hlw : (leftWins25Cat.map (fun w => w.wires.length)).sum = 256 := by
    have h := congrArg (fun l => (l.map Prod.snd).sum) leftWins25Cat_meta
    simp only [List.map_map, Function.comp_def] at h
    rw [h]; simp only [leftMeta25Cat, List.replicate, List.cons_append, List.nil_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; rfl
  have hrw : (rightWins25Cat.map (fun w => w.wires.length)).sum = 206 := by
    have h := congrArg (fun l => (l.map Prod.snd).sum) rightWins25Cat_meta
    simp only [List.map_map, Function.comp_def] at h
    rw [h]; simp only [rightMeta25Cat, List.replicate, List.cons_append, List.nil_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; rfl
  rw [hlw, List.length_nil] at hL
  rw [hrw, List.length_nil] at hR
  have hreset : cost18 (resetProgram 3407872 (0 + axisCount leftWins25Cat + axisCount rightWins25Cat) resetWires) = 0 := by
    apply cost18_zero_of_residue
    have hz : ∀ (n start : Nat) (ws : List Wire), residue (resetProgram n start ws) = 0 := by
      intro n start ws; induction ws generalizing start with
      | nil => simp [resetProgram, residue]
      | cons w ws ih => simpa [resetProgram, residue_cast, residue] using ih (start + 1)
    exact hz _ _ _
  have hro : cost18 readout25Cat = 0 := by
    apply cost18_zero_of_residue
    simp only [readout25Cat, readoutL25, readoutR25, residue_cast, residue_append, Readout5.residue_suffix5]
  unfold rawEntry25Cat Single.fixedEntry
  dsimp only
  rw [cost18_reindex]
  simp only [fullProgram25Cat, cost18_append, program25Cat]
  rw [CatAxis.cost18_literals _ _ (by decide)]
  simp only [cost18_cast, cost18_append, zero_add, add_zero, hreset, hro, hL, hR]
  exact joint_error18_256_206

theorem source25Cat_cursor_le : rawEntry25Cat.finalCursor ≤ 99000000 := by
  have hfc : rawEntry25Cat.finalCursor = cursor25Cat + 6472 := by
    unfold rawEntry25Cat; rw [Single.fixedEntry_cursor]
  have h1 := first20Cat_count_le
  have h16t := cBody16Trunc_le
  have h17 := cBody17_le
  have h17t := cBody17Trunc_le
  have h18 := cBody18_le
  have hL := leftWins25Cat_count_eq
  have hR := rightWins25Cat_count_eq
  have hres : resetWires.length ≤ 2000 := by simp [resetWires]
  unfold cursor25Cat at hfc
  omega

/-! ### Part 5: Raw certificate, `trim 18`, specialization, and final `1,612 × 227,692,785` certificate -/

section Cert25
attribute [local irreducible] rawEntry25Cat fullProgram25Cat program25Cat readout25Cat

def rawBounds25Cat : Bounds := ⟨1612, 70000000000000, 99000000⟩

theorem raw_certificate25Cat : Certificate rawLimits25 rawLayout25Cat rawEntry25Cat rawBounds25Cat where
  gateBudget := by
    rw [rawEntry25Cat, Single.fixedEntry_slots]
    exact full25Cat_slots.trans (by unfold rawLimits25 officialLimits; dsimp only; omega)
  recordBudget := source25Cat_cursor_le.trans (by unfold rawLimits25 officialLimits; dsimp only; omega)
  tableBudget := by rw [rawEntry25Cat, Single.fixedEntry_rows]; unfold rawLimits25; exact le_rfl
  candidateBudget := by
    change rawLayout25Cat.trials.length * (2 * (order / 2 ^ 206 + 2)) ≤ 56 * (2 ^ 49 + 2)
    have hl : rawLayout25Cat.trials.length = 13 := by
      simp only [rawLayout25Cat, List.length_map, offsets13_length]
    rw [hl]
    exact decoder_budget256
  wellFormed := by rw [rawEntry25Cat, Single.fixedEntry_wellFormed]; exact full25Cat_wellFormed
  resources := by
    intro Q
    have hs := source25Cat_within.instantiate (readConstant rawEntry25Cat.coefficients.get Q) Fin.elim0
    have hq : (rawEntry25Cat.instantiate Q).qubitCount ≤ 1612 := by
      have ht : (rawEntry25Cat.instantiate Q).wires.dedup.toFinset ⊆ (List.range 1612).toFinset := by
        intro v hv
        exact List.mem_toFinset.mpr (hs (by simpa only [List.mem_toFinset, List.mem_dedup] using hv))
      have hc := (Finset.card_le_card ht).trans (List.toFinset_card_le _)
      rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
      simpa only [AdaptiveCircuit.qubitCount, List.length_range] using hc
    refine ⟨hq, ?_, ?_⟩
    · have ht := Width16Actual.straight_t_bound rawEntry25Cat.program
        (readConstant rawEntry25Cat.coefficients.get Q) Fin.elim0
      have hb : rawEntry25Cat.program.gateSlots ≤ 10000000000000 := by
        rw [rawEntry25Cat, Single.fixedEntry_slots]; exact full25Cat_slots
      exact ht.trans (by change _ ≤ 70000000000000; omega)
    · have hm := source25Cat_cursor_le
      change (rawEntry25Cat.program.instantiate _ _).measurementCount ≤ 99000000
      rw [Straight.measurementCount]; omega
  success := by
    intro Q d hn hd
    exact (by norm_num : (99 / 100 : ℝ) ≤ 9922 / 10000).trans (strong_success25Cat Q d hn hd)

def entryTrim18 (e : StraightEntry) : StraightEntry where
  coefficients := e.coefficients
  finalCursor := e.finalCursor
  program := trim 18 e.program

theorem trim18_certificate_generic (limits : Limits) (layout : DecodeLayout) (entry : StraightEntry)
    (bounds : Bounds) (ws : List Wire) (cert : Certificate limits layout entry bounds)
    (hs : Within ws entry.program) (hcost : cost18 entry.program ≤ 51 / 10000)
    (hstrong : ∀ (Q : Point) (d : Nat), Q ≠ 0 → Q = d • G →
      (9922 / 10000 : ℝ) ≤ Instrument.bornMass ((entry.instantiate Q).run.filter
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
    change 9922 / 10000 ≤ Instrument.bornMass
      ((entry.program.instantiate (readConstant entry.coefficients.get Q) Fin.elim0).run.filter
        (fun b => (verifiedCandidate layout Q b.history).isSome)) (ket zeroBasisState) at hS
    have hf : expectation (readConstant entry.coefficients.get Q) entry.program Fin.elim0
        (ket zeroBasisState) (fun h => !(verifiedCandidate layout Q (List.ofFn h)).isSome) ≤
        1 - 9922 / 10000 := by linarith
    have hm := mul_le_mul_of_nonneg_left hf
      (show 0 ≤ 1 + (106 / 10) * cost18 entry.program by positivity)
    change 99 / 100 ≤ Instrument.bornMass
      (((trim 18 entry.program).instantiate (readConstant entry.coefficients.get Q) Fin.elim0).run.filter
        (fun b => (verifiedCandidate layout Q b.history).isSome)) (ket zeroBasisState)
    nlinarith

theorem trimmed25Cat_coefficients :
    (entryTrim18 rawEntry25Cat).coefficients = List.ofFn coefficientAt25 := by
  unfold entryTrim18 rawEntry25Cat Single.fixedEntry; rfl

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

theorem trimmed25Cat_tCount (Q : Point) :
    ((entryTrim18 rawEntry25Cat).instantiate Q).tCount ≤ 227615785 := by
  rw [rawEntry25Cat]
  exact trim18_fixedEntry_tCount coefficientAt25 fullProgram25Cat Q 227615785
    (fun r => full25Cat_trim18_tCount r Fin.elim0)

theorem trim18_certificate25Cat :
    Certificate rawLimits25 rawLayout25Cat (entryTrim18 rawEntry25Cat) ⟨1612, 227615785, 99000000⟩ := by
  have hbase := trim18_certificate_generic rawLimits25 rawLayout25Cat rawEntry25Cat rawBounds25Cat
    (List.range 1612) raw_certificate25Cat source25Cat_within source25Cat_cost18 strong_success25Cat
  refine ⟨hbase.gateBudget, hbase.recordBudget, hbase.tableBudget, hbase.candidateBudget,
    hbase.wellFormed, ?_, hbase.success⟩
  intro Q
  have hq : ((entryTrim18 rawEntry25Cat).instantiate Q).qubitCount ≤ 1612 := by
    simpa only [List.length_range] using (hbase.resources Q).1
  have hm : ((entryTrim18 rawEntry25Cat).instantiate Q).measurementCount ≤ 99000000 :=
    (hbase.resources Q).2.2.trans source25Cat_cursor_le
  exact ⟨hq, trimmed25Cat_tCount Q, hm⟩

end Cert25

end
end ShorECDLP.Entrant.Schedule25

namespace ShorECDLP.Entrant.Schedule25Actual
open Quantum Challenge Secp256k1 AndGadget WEXCredit ConditionalCatalyst ApproximatePhase34
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open Schedule25 Trim18
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
attribute [local irreducible] List.ofFn Single.axis Single.fixedEntry
  GenericW.compiledProgramW GenericW.compiledProgramFnW
  GenericW.compiledProgram16 GenericW.compiledProgram17 GenericW.compiledProgram18
  GenericW.compiledProgramTrunc16 GenericW.compiledProgramTrunc17
  GenericW.arithSpecFull GenericW.arithSpecTrunc96
  GenericW.fixupSpec16 GenericW.fixupSpec17 GenericW.fixupSpec18
  GenericW.compiledFixup16 GenericW.compiledFixup9 GenericW.rawFixup16 GenericW.rawFixup9
  GenericW.compact1612 Readout5.suffix5
  LocalFour.compileLower CatAxis.axisCat
  Schedule25.rawEntry25Cat Schedule25.fullProgram25Cat Schedule25.program25Cat Schedule25.readout25Cat
  Schedule25.entryTrim18 Schedule25.rawLayout25Cat Schedule25.specializeEntry25
  ConditionalCatalyst.compile

def entry : StraightEntry :=
  specializeEntry25 (entryTrim18 rawEntry25Cat) trimmed25Cat_coefficients

def layout : DecodeLayout := rawLayout25Cat

def bounds : Bounds := ⟨1612, 227615785, 99000000⟩

theorem certificate : Certificate officialLimits layout entry bounds :=
  specializeEntry25_certificate (entryTrim18 rawEntry25Cat) trimmed25Cat_coefficients
    rawLayout25Cat bounds trim18_certificate25Cat

end
end ShorECDLP.Entrant.Schedule25Actual
end

/-! ### Consolidated from `Main.lean` -/
section
-- Entrant/Main.lean
section
namespace ShorECDLP.Entrant
open Challenge
noncomputable section
def bounds : Bounds := ⟨1612, 227615785, 99000000⟩
def entry : StraightEntry := Schedule25Actual.entry
def layout : DecodeLayout := Schedule25Actual.layout
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem certificate : Certificate officialLimits layout entry bounds :=
  Schedule25Actual.certificate
end
end ShorECDLP.Entrant
end
end
