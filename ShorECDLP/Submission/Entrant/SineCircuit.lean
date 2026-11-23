import ShorECDLP.Submission.Entrant.Prefix

/-! Centered 10-bit sine window state preparation circuit (`sineFromPlus`) and exact
semiclassical QPE + character-expansion bridge (`windowedEventMass_distribution`).

Given `ws` (10 wires, LSB-first) already in `|+⟩^{⊗10}` via `prepareOuterBank`,
`sineFromPlus ws` transforms `|+⟩^{⊗10}` into:
  `2^{-5} ∑_{u < 1024} sineWeight 10 u |u⟩`
where `sineWeight h u = (√2)⁻¹ (e^{iπ u / 2^h} - e^{-iπ u / 2^h}) = i √2 sin(π u / 2^h)`.

Cost per axis: 52 gate slots, 0 CCXs (`added = 0`), 28 non-Clifford T-model phase gates
(`weight4 = 28`, with 2 catalyzed `k = 2` S-gates), all phase depths `k ≤ 11` (untouched by
phase trimming `cutoff ≥ 11`), zero extra qubits (`circuitWires ⊆ ws`). -/

set_option Elab.async false

namespace ShorECDLP.Entrant.SineCircuit
open Classical Quantum Secp256k1 Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
open Quantum.PhaseEstimation Quantum.OrderFinding Single Single.Distribution
open scoped BigOperators
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

/-! ### Part 1: `sineWeight` and `sineFromPlus` circuit -/

/-- Normalized sine-window amplitude multiplier on top-`h` index `u`. -/
def sineWeight (h u : Nat) : ℂ :=
  (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) *
    (Complex.exp (Complex.I * ((Real.pi * (u : ℝ) / (2 : ℝ) ^ h : ℝ) : ℂ)) -
     Complex.exp (-(Complex.I * ((Real.pi * (u : ℝ) / (2 : ℝ) ^ h : ℝ) : ℂ))))

theorem sineWeight_eq_sin (h u : Nat) :
    sineWeight h u = ((Real.sqrt 2 : ℝ) : ℂ) * Complex.I *
      ((Real.sin (Real.pi * (u : ℝ) / (2 : ℝ) ^ h) : ℝ) : ℂ) := by
  unfold sineWeight
  set θ : ℝ := Real.pi * (u : ℝ) / (2 : ℝ) ^ h
  have hsin : ((Real.sin θ : ℝ) : ℂ) =
      (Complex.exp (Complex.I * (θ : ℂ)) - Complex.exp (-(Complex.I * (θ : ℂ)))) / (2 * Complex.I) := by
    rw [Complex.ofReal_sin, Complex.sin]
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    field_simp [hI]
    ring_nf
    simp [Complex.I_sq]
  have hsq : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (2 : ℂ) = ((Real.sqrt 2 : ℝ) : ℂ) := by
    have hne : Real.sqrt 2 ≠ 0 := by positivity
    have hr : (Real.sqrt 2)⁻¹ * 2 = Real.sqrt 2 := by
      rw [inv_mul_eq_iff_eq_mul₀ hne, Real.mul_self_sqrt (by norm_num)]
    have hC : ((((Real.sqrt 2)⁻¹ * 2 : ℝ) : ℂ)) = ((Real.sqrt 2 : ℝ) : ℂ) := congrArg Complex.ofReal hr
    simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using hC
  rw [hsin]
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  have hden : (2 : ℂ) * Complex.I ≠ 0 := mul_ne_zero h2 hI
  rw [mul_div_assoc', eq_div_iff hden]
  calc
    (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) *
        (Complex.exp (Complex.I * (θ : ℂ)) - Complex.exp (-(Complex.I * (θ : ℂ)))) * (2 * Complex.I)
      = ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * 2) * Complex.I *
          (Complex.exp (Complex.I * (θ : ℂ)) - Complex.exp (-(Complex.I * (θ : ℂ)))) := by ring
    _ = ((Real.sqrt 2 : ℝ) : ℂ) * Complex.I *
          (Complex.exp (Complex.I * (θ : ℂ)) - Complex.exp (-(Complex.I * (θ : ℂ)))) := by rw [hsq]

theorem sineWeight_normSq (h u : Nat) :
    Complex.normSq (sineWeight h u) = 2 * Real.sin (Real.pi * (u : ℝ) / (2 : ℝ) ^ h) ^ 2 := by
  rw [sineWeight_eq_sin, Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_ofReal,
    Complex.normSq_ofReal, Complex.normSq_I, mul_one, Real.mul_self_sqrt (by norm_num), sq]

/-- Controlled phase kickback block on `(c, t)` applying `± 2π / 2^k` when `c = true`. -/
def cPhaseBlock (c t : Wire) (k : Nat) : Circuit :=
  [.P .inverse k t, .CX c t, .P .forward k t, .CX c t]

def cPhaseLoop (c : Wire) : List Wire → Nat → Circuit
  | [], _ => []
  | t :: ts, k => cPhaseBlock c t k ++ cPhaseLoop c ts (k - 1)

def centerLoop : List Wire → Nat → Circuit
  | [], _ => []
  | t :: ts, k => .P .forward k t :: centerLoop ts (k - 1)

/-- 10-qubit circuit transforming `|+⟩^{⊗10}` (on LSB-first `ws`) into the centered sine window state. -/
def sineFromPlus (ws : List Wire) : Circuit :=
  let lo := ws.take 9
  let msb := ws.getD 9 0
  ([.H msb, .X msb, .H msb, .P .inverse 2 msb, .P .forward 11 msb] : Circuit) ++
    cPhaseLoop msb lo 11 ++ [.H msb] ++ centerLoop ws 11

theorem cPhaseBlock_ket (c t : Wire) (hne : c ≠ t) (k : Nat) (s : BasisState) :
    Quantum.run (cPhaseBlock c t k) (ket s) =
      (if s c then (if s t then phaseCoeff .inverse k else phaseCoeff .forward k) else 1) • ket s := by
  have h1 : Quantum.run (cPhaseBlock c t k) (ket s) =
      applyGate (.CX c t) (applyGate (.P .forward k t) (applyGate (.CX c t) (applyGate (.P .inverse k t) (ket s)))) := by
    simp only [cPhaseBlock, Quantum.run_cons, Quantum.run_nil]
  rw [h1]
  have hupd_same_state (b : Bool) (hb : s t = b) : s[t ↦ b] = s := by
    funext w; by_cases hw : w = t <;> simp [upd, hw, hb]
  have hupd_twice (b1 b2 : Bool) (hb : s t = b2) : (s[t ↦ b1])[t ↦ b2] = s := by
    funext w; by_cases hw : w = t <;> simp [upd, hw, hb]
  cases hsc : s c <;> cases hst : s t
  · rw [applyGate_P_ket, hst]; simp only [Bool.false_eq_true, if_false, one_smul]
    rw [applyGate_CX_ket, hsc, hst]; simp only [Bool.xor_false, hupd_same_state false hst]
    rw [applyGate_P_ket, hst]; simp only [Bool.false_eq_true, if_false, one_smul]
    rw [applyGate_CX_ket, hsc, hst]; simp only [Bool.xor_false, hupd_same_state false hst]
  · rw [applyGate_P_ket, hst]; simp only [if_true, map_smul]
    rw [applyGate_CX_ket, hsc, hst]; simp only [Bool.xor_false, hupd_same_state true hst]
    rw [applyGate_P_ket, hst]; simp only [if_true, map_smul, smul_smul]
    rw [applyGate_CX_ket, hsc, hst]; simp only [Bool.xor_false, hupd_same_state true hst]
    have hmul : phaseCoeff .inverse k * phaseCoeff .forward k = 1 := by
      simpa [PhaseDir.adjoint] using phaseCoeff_adjoint_mul .forward k
    rw [hmul]; simp only [Bool.false_eq_true, if_false]
  · have hc1 : (s[t ↦ true]) c = true := by rw [upd_other s t true hne, hsc]
    rw [applyGate_P_ket, hst]; simp only [Bool.false_eq_true, if_false, one_smul]
    rw [applyGate_CX_ket, hsc, hst]; simp only [Bool.xor_true, Bool.not_false]
    rw [applyGate_P_ket, upd_same]; simp only [if_true, map_smul]
    rw [applyGate_CX_ket, upd_same, hc1]; simp only [Bool.xor_true, Bool.not_true, hupd_twice true false hst]
  · have hc1 : (s[t ↦ false]) c = true := by rw [upd_other s t false hne, hsc]
    rw [applyGate_P_ket, hst]; simp only [if_true, map_smul]
    rw [applyGate_CX_ket, hsc, hst]; simp only [Bool.xor_true, Bool.not_true]
    rw [applyGate_P_ket, upd_same]; simp only [Bool.false_eq_true, if_false, one_smul]
    rw [applyGate_CX_ket, upd_same, hc1]; simp only [Bool.xor_true, Bool.not_false, hupd_twice false true hst]

theorem cPhaseLoop_ket (c : Wire) : ∀ (ts : List Wire) (k : Nat),
    c ∉ ts → ts.length < k → ∀ s : BasisState,
    Quantum.run (cPhaseLoop c ts k) (ket s) =
      (if s c then
        Complex.exp (Complex.I *
          (((2 * Real.pi / (2 : ℝ) ^ k) *
            (((2 ^ ts.length - 1 : Nat) : ℝ) - 2 * (tableAddressValue ts s : ℝ)) : ℝ) : ℂ))
       else 1) • ket s
  | [], k, _, _, s => by
    simp [cPhaseLoop, Quantum.run, tableAddressValue]
  | t :: ts, k, hc, hk, s => by
    have hct : c ≠ t := fun h => hc (h ▸ List.mem_cons_self)
    have hcts : c ∉ ts := fun h => hc (List.mem_cons_of_mem _ h)
    have hk' : ts.length < k - 1 := by simp only [List.length_cons] at hk; omega
    have hk1 : 1 ≤ k := by simp only [List.length_cons] at hk; omega
    rw [cPhaseLoop, Quantum.run_append, cPhaseBlock_ket c t hct k s, map_smul,
      cPhaseLoop_ket c ts (k - 1) hcts hk' s, smul_smul]
    cases hsc : s c
    · simp
    · simp only [if_true]
      congr 1
      have hpow : (2 : ℝ) ^ k = (2 : ℝ) ^ (k - 1) * 2 := by
        rw [← pow_succ, Nat.sub_add_cancel hk1]
      have hsub1 : (1 : Nat) ≤ 2 ^ ts.length := Nat.one_le_pow _ _ (by decide)
      have hsub2 : (1 : Nat) ≤ 2 ^ (ts.length + 1) := Nat.one_le_pow _ _ (by decide)
      have hcast1 : ((2 ^ ts.length - 1 : Nat) : ℝ) = (2 : ℝ) ^ ts.length - 1 := by
        rw [Nat.cast_sub hsub1]; push_cast; rfl
      have hcast2 : ((2 ^ (t :: ts).length - 1 : Nat) : ℝ) = 2 * (2 : ℝ) ^ ts.length - 1 := by
        rw [List.length_cons, Nat.cast_sub hsub2, pow_succ]; push_cast; ring
      have haddr : (tableAddressValue (t :: ts) s : ℝ) =
          ((s t).toNat : ℝ) + 2 * (tableAddressValue ts s : ℝ) := by
        change (((s t).toNat + 2 * tableAddressValue ts s : Nat) : ℝ) = _
        push_cast; rfl
      cases hst : s t
      · simp only [Bool.false_eq_true, if_false, phaseCoeff, phaseAngle]
        rw [← Complex.exp_add]
        congr 1
        rw [hcast1, hcast2, haddr, hst]
        simp only [Bool.toNat_false, Nat.cast_zero, zero_add]
        have h2ne : (2 : ℝ) ^ (k - 1) ≠ 0 := by positivity
        have hreal : 2 * Real.pi / (2 : ℝ) ^ k +
            2 * Real.pi / (2 : ℝ) ^ (k - 1) * ((2 : ℝ) ^ ts.length - 1 - 2 * ↑(tableAddressValue ts s)) =
            2 * Real.pi / (2 : ℝ) ^ k * (2 * (2 : ℝ) ^ ts.length - 1 - 2 * (2 * ↑(tableAddressValue ts s))) := by
          rw [hpow]; field_simp [h2ne]; ring
        have hC := congrArg (fun x : ℝ => Complex.I * (x : ℂ)) hreal
        simpa [Complex.ofReal_add, mul_add] using hC
      · simp only [if_true, phaseCoeff, phaseAngle]
        rw [← Complex.exp_add]
        congr 1
        rw [hcast1, hcast2, haddr, hst]
        simp only [Bool.toNat_true, Nat.cast_one]
        have h2ne : (2 : ℝ) ^ (k - 1) ≠ 0 := by positivity
        have hreal : -(2 * Real.pi / (2 : ℝ) ^ k) +
            2 * Real.pi / (2 : ℝ) ^ (k - 1) * ((2 : ℝ) ^ ts.length - 1 - 2 * ↑(tableAddressValue ts s)) =
            2 * Real.pi / (2 : ℝ) ^ k * (2 * (2 : ℝ) ^ ts.length - 1 - 2 * (1 + 2 * ↑(tableAddressValue ts s))) := by
          rw [hpow]; field_simp [h2ne]; ring
        have hC := congrArg (fun x : ℝ => Complex.I * (x : ℂ)) hreal
        simpa [Complex.ofReal_add, Complex.ofReal_neg, mul_add] using hC

theorem centerLoop_ket : ∀ (ts : List Wire) (k : Nat),
    ts.length ≤ k → ∀ s : BasisState,
    Quantum.run (centerLoop ts k) (ket s) =
      Complex.exp (Complex.I * (((2 * Real.pi / (2 : ℝ) ^ k) * (tableAddressValue ts s : ℝ) : ℝ) : ℂ)) • ket s
  | [], k, _, s => by simp [centerLoop, Quantum.run, tableAddressValue]
  | t :: ts, k, hk, s => by
    have hk' : ts.length ≤ k - 1 := by simp only [List.length_cons] at hk; omega
    have hk1 : 1 ≤ k := by simp only [List.length_cons] at hk; omega
    rw [centerLoop, Quantum.run_cons, applyGate_P_ket, map_smul, centerLoop_ket ts (k - 1) hk' s, smul_smul]
    congr 1
    have hpow : (2 : ℝ) ^ k = (2 : ℝ) ^ (k - 1) * 2 := by
      rw [← pow_succ, Nat.sub_add_cancel hk1]
    have h2ne : (2 : ℝ) ^ (k - 1) ≠ 0 := by positivity
    have haddr : (tableAddressValue (t :: ts) s : ℝ) =
        ((s t).toNat : ℝ) + 2 * (tableAddressValue ts s : ℝ) := by
      change (((s t).toNat + 2 * tableAddressValue ts s : Nat) : ℝ) = _
      push_cast; rfl
    cases hst : s t
    · simp only [Bool.false_eq_true, if_false, one_mul]
      congr 1
      rw [haddr, hst]
      simp only [Bool.toNat_false, Nat.cast_zero, zero_add]
      have hreal : 2 * Real.pi / (2 : ℝ) ^ (k - 1) * ↑(tableAddressValue ts s) =
          2 * Real.pi / (2 : ℝ) ^ k * (2 * ↑(tableAddressValue ts s)) := by
        rw [hpow]; field_simp [h2ne]
      exact congrArg (fun x : ℝ => Complex.I * (x : ℂ)) hreal
    · simp only [if_true, phaseCoeff, phaseAngle]
      rw [← Complex.exp_add]
      congr 1
      rw [haddr, hst]
      simp only [Bool.toNat_true, Nat.cast_one]
      have hreal : 2 * Real.pi / (2 : ℝ) ^ k + 2 * Real.pi / (2 : ℝ) ^ (k - 1) * ↑(tableAddressValue ts s) =
          2 * Real.pi / (2 : ℝ) ^ k * (1 + 2 * ↑(tableAddressValue ts s)) := by
        rw [hpow]; field_simp [h2ne]
      have hC := congrArg (fun x : ℝ => Complex.I * (x : ℂ)) hreal
      simpa [Complex.ofReal_add, mul_add] using hC

theorem tableAddressValue_phaseWordState (ws : List Wire) (hnd : ws.Nodup)
    (bs : List Bool) (hl : bs.length = ws.length) (s : BasisState) :
    tableAddressValue ws (phaseWordState ws bs s) = boolWordToNat bs := by
  have he : ∀ (vs : List Wire) (t : BasisState), tableAddressValue vs t = boolWordToNat (wireValues vs t) := by
    intro vs; induction vs with
    | nil => intro _; rfl
    | cons w vs ih =>
      intro t
      change (t w).toNat + 2 * tableAddressValue vs t = (t w).toNat + 2 * boolWordToNat (wireValues vs t)
      rw [ih]
  rw [he, phaseWordState_word ws hnd bs hl s]

theorem boolWordToNat_append (a b : List Bool) :
    boolWordToNat (a ++ b) = boolWordToNat a + 2 ^ a.length * boolWordToNat b := by
  induction a with
  | nil => simp [boolWordToNat]
  | cons x xs ih =>
    simp only [List.cons_append, boolWordToNat, ih, List.length_cons, pow_succ]
    ring

theorem boolWordToNat_lt (a : List Bool) : boolWordToNat a < 2 ^ a.length := by
  induction a with
  | nil => simp [boolWordToNat]
  | cons x xs ih =>
    simp only [boolWordToNat, List.length_cons, pow_succ]
    cases x <;> simp <;> omega

theorem fourierOutcomes_add (n m : Nat) :
    fourierOutcomes (n + m) = (fourierOutcomes n).flatMap (fun a => (fourierOutcomes m).map (fun b => a ++ b)) := by
  induction n with
  | zero => simp [fourierOutcomes]
  | succ n ih =>
    simp only [Nat.succ_add, fourierOutcomes, ih, List.flatMap_append, List.flatMap_map,
      List.map_flatMap, List.map_map, Function.comp_def, List.cons_append]

theorem fourierOutcomes_one : fourierOutcomes 1 = [[false], [true]] := rfl

attribute [local irreducible] fourierOutcomes

theorem applyGate_H_twice (w : Wire) (s : BasisState) :
    applyGate (.H w) (applyGate (.H w) (ket s)) = ket s := by
  have h2 : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = (2 : ℂ)⁻¹ := by
    have hr : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (2 : ℝ)⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
    have hC := congrArg Complex.ofReal hr
    simpa only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_ofNat] using hC
  have hs0 : (s[w ↦ false])[w ↦ false] = s[w ↦ false] := by
    funext v; by_cases hv : v = w <;> simp [upd, hv]
  have hs1 : (s[w ↦ false])[w ↦ true] = s[w ↦ true] := by
    funext v; by_cases hv : v = w <;> simp [upd, hv]
  have hs2 : (s[w ↦ true])[w ↦ false] = s[w ↦ false] := by
    funext v; by_cases hv : v = w <;> simp [upd, hv]
  have hs3 : (s[w ↦ true])[w ↦ true] = s[w ↦ true] := by
    funext v; by_cases hv : v = w <;> simp [upd, hv]
  have hsw : ∀ b, s w = b → s[w ↦ b] = s := by
    intro b hb; funext v; by_cases hv : v = w <;> simp [upd, hv, hb]
  cases h : s w
  · simp only [applyGate_H_ket, h, Bool.false_eq_true, if_false, mul_one, map_add, map_smul,
      upd_same, if_true, mul_neg, hs0, hs1, hs2, hs3, smul_add, smul_smul, h2]
    rw [hsw false h]
    module
  · simp only [applyGate_H_ket, h, if_true, mul_neg, mul_one, map_add, map_smul,
      upd_same, Bool.false_eq_true, if_false, hs0, hs1, hs2, hs3, smul_add, smul_smul,
      neg_mul, mul_neg, neg_neg, h2]
    rw [hsw true h]
    module

theorem applyGate_H_twice_state (w : Wire) (ψ : State) :
    applyGate (.H w) (applyGate (.H w) ψ) = ψ := by
  induction ψ using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]
  | single s c =>
    have hs : Finsupp.single s c = c • ket s := by simp [ket, Finsupp.smul_single]
    rw [hs, map_smul, map_smul, applyGate_H_twice]

private theorem ws_split_10 (ws : List Wire) (hl : ws.length = 10) :
    ws = ws.take 9 ++ [ws.getD 9 0] := by
  have hdrop : ws.drop 9 = [ws.getD 9 0] := by
    cases h : ws.drop 9 with
    | nil => have := congrArg List.length h; simp [hl] at this
    | cons a rest =>
      have hlen := congrArg List.length h
      simp [hl] at hlen
      subst hlen
      have ha : ws.getD 9 0 = a := by
        have h1 : (ws.drop 9)[0]? = some a := by rw [h]; rfl
        rw [List.getElem?_drop, Nat.add_zero] at h1
        simp [List.getD_eq_getElem?_getD, h1]
      rw [ha]
  simpa [hdrop] using (List.take_append_drop 9 ws).symm

/-- Exact action of `sineFromPlus ws` after `ws.map Gate.H` on any clean 10-wire bank `ws`. -/
theorem sineFromPlus_ket (ws : List Wire) (hl : ws.length = 10) (hnd : ws.Nodup)
    (s : BasisState) (hclean : Clean ws s) :
    Quantum.run (sineFromPlus ws) (Quantum.run (ws.map Gate.H) (ket s)) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 10) •
        ((fourierOutcomes 10).map (fun bs =>
          sineWeight 10 (boolWordToNat bs) • ket (phaseWordState ws bs s))).sum := by
  let lo := ws.take 9
  let msb := ws.getD 9 0
  have hws : ws = lo ++ [msb] := ws_split_10 ws hl
  have hlo_len : lo.length = 9 := by simp [lo, hl]
  have hnd' : (lo ++ [msb]).Nodup := by rwa [← hws]
  have hlo_nd : lo.Nodup := (List.nodup_append.mp hnd').1
  have hmsb_not_lo : msb ∉ lo := fun hm => (List.nodup_append.mp hnd').2.2 msb hm msb List.mem_cons_self rfl
  have hclean_lo : Clean lo s := fun w hw => hclean w (by rw [hws]; exact List.mem_append_left _ hw)
  have hclean_msb : s msb = false := hclean msb (by rw [hws]; simp)
  have hH_split : Quantum.run (ws.map Gate.H) (ket s) =
      applyGate (.H msb) (Quantum.run (lo.map Gate.H) (ket s)) := by
    rw [hws, List.map_append, Quantum.run_append]
    simp [Quantum.run]
  have hstep1 : Quantum.run (sineFromPlus ws) (Quantum.run (ws.map Gate.H) (ket s)) =
      Quantum.run (centerLoop ws 11)
        (applyGate (.H msb)
          (Quantum.run (cPhaseLoop msb lo 11)
            (Quantum.run [.X msb, .H msb, .P .inverse 2 msb, .P .forward 11 msb]
              (Quantum.run (lo.map Gate.H) (ket s))))) := by
    unfold sineFromPlus
    rw [hH_split]
    simp only [Quantum.run_append, Quantum.run_cons, Quantum.run_nil, LinearMap.id_apply]
    change Quantum.run (centerLoop ws 11) (applyGate (.H msb) (Quantum.run (cPhaseLoop msb lo 11)
      (applyGate (.P .forward 11 msb) (applyGate (.P .inverse 2 msb) (applyGate (.H msb) (applyGate (.X msb)
        (applyGate (.H msb) (applyGate (.H msb) (Quantum.run (lo.map Gate.H) (ket s)))))))))) = _
    rw [applyGate_H_twice_state]
  rw [hstep1, phaseHadamards_uniform lo hlo_nd s hclean_lo, hlo_len]
  simp only [phaseUniformSum, hlo_len, map_smul, stateLinear_list_sum, List.map_map, Function.comp_def]
  have hterm (bs : List Bool) (hbs : bs ∈ fourierOutcomes 9) :
      Quantum.run (centerLoop ws 11)
        (applyGate (.H msb)
          (Quantum.run (cPhaseLoop msb lo 11)
            (Quantum.run [.X msb, .H msb, .P .inverse 2 msb, .P .forward 11 msb]
              (ket (phaseWordState lo bs s))))) =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
        (sineWeight 10 (boolWordToNat (bs ++ [false])) • ket (phaseWordState ws (bs ++ [false]) s) +
         sineWeight 10 (boolWordToNat (bs ++ [true])) • ket (phaseWordState ws (bs ++ [true]) s)) := by
    have hbl : bs.length = 9 := (fourierOutcomes_mem 9 bs).mp hbs
    let t := phaseWordState lo bs s
    have ht_msb : t msb = false := (phaseWordState_frame lo bs s msb hmsb_not_lo).trans hclean_msb
    have ht_lo : tableAddressValue lo t = boolWordToNat bs :=
      tableAddressValue_phaseWordState lo hlo_nd bs (hbl.trans hlo_len.symm) s
    have ht0_eq : t[msb ↦ false] = phaseWordState ws (bs ++ [false]) s := by
      rw [hws, phaseWordState_append lo ([msb]) bs ([false]) (hbl.trans hlo_len.symm) s]; rfl
    have ht1_eq : t[msb ↦ true] = phaseWordState ws (bs ++ [true]) s := by
      rw [hws, phaseWordState_append lo ([msb]) bs ([true]) (hbl.trans hlo_len.symm) s]; rfl
    have ht1_lo : tableAddressValue lo (t[msb ↦ true]) = boolWordToNat bs :=
      (tableAddressValue_congr lo _ t (fun w hw => upd_other t msb true (fun h => hmsb_not_lo (h ▸ hw)))).trans ht_lo
    have hprep : Quantum.run [.X msb, .H msb, .P .inverse 2 msb, .P .forward 11 msb] (ket t) =
        (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • ket (t[msb ↦ false]) +
        ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (-1) * phaseCoeff .inverse 2 * phaseCoeff .forward 11) •
          ket (t[msb ↦ true]) := by
      have hu1 : (t[msb ↦ true])[msb ↦ false] = t[msb ↦ false] := by
        funext w; by_cases hw : w = msb <;> simp [upd, hw]
      have hu2 : (t[msb ↦ true])[msb ↦ true] = t[msb ↦ true] := by
        funext w; by_cases hw : w = msb <;> simp [upd, hw]
      have hrun : Quantum.run [.X msb, .H msb, .P .inverse 2 msb, .P .forward 11 msb] (ket t) =
          applyGate (.P .forward 11 msb) (applyGate (.P .inverse 2 msb)
            (applyGate (.H msb) (applyGate (.X msb) (ket t)))) := by
        simp only [Quantum.run_cons, Quantum.run_nil]
      rw [hrun, applyGate_X_ket, ht_msb]; simp only [Bool.not_false]
      rw [applyGate_H_ket, upd_same, hu1, hu2]
      simp only [if_true, map_add, map_smul, applyGate_P_ket, upd_same,
        Bool.false_eq_true, if_false, one_smul, smul_smul]
    rw [hprep, map_add, map_smul, map_smul,
      cPhaseLoop_ket msb lo 11 hmsb_not_lo (by rw [hlo_len]; decide) (t[msb ↦ false]),
      cPhaseLoop_ket msb lo 11 hmsb_not_lo (by rw [hlo_len]; decide) (t[msb ↦ true])]
    simp only [upd_same, Bool.false_eq_true, if_false, if_true, one_smul, hlo_len, ht1_lo, smul_smul]
    set v : Nat := boolWordToNat bs
    have hphase1 : phaseCoeff .inverse 2 * phaseCoeff .forward 11 *
        Complex.exp (Complex.I * (((2 * Real.pi / (2 : ℝ) ^ 11) * (((2 ^ 9 - 1 : Nat) : ℝ) - 2 * (v : ℝ)) : ℝ) : ℂ)) =
        Complex.exp (-(Complex.I * ((2 * Real.pi * (v : ℝ) / 1024 : ℝ) : ℂ))) := by
      simp only [phaseCoeff, phaseAngle, ← Complex.exp_add]
      congr 1
      have hreal : -(2 * Real.pi / (2 : ℝ) ^ 2) + 2 * Real.pi / (2 : ℝ) ^ 11 +
          2 * Real.pi / (2 : ℝ) ^ 11 * (((2 ^ 9 - 1 : Nat) : ℝ) - 2 * (v : ℝ)) =
          -(2 * Real.pi * (v : ℝ) / 1024) := by
        norm_num; ring
      have hC := congrArg (fun x : ℝ => Complex.I * (x : ℂ)) hreal
      simpa [Complex.ofReal_add, Complex.ofReal_neg, mul_add] using hC
    have hmul_reassoc :
        ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (-1) * phaseCoeff .inverse 2 * phaseCoeff .forward 11) *
          Complex.exp (Complex.I * (((2 * Real.pi / (2 : ℝ) ^ 11) * (((2 ^ 9 - 1 : Nat) : ℝ) - 2 * (v : ℝ)) : ℝ) : ℂ)) =
        (-((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * Complex.exp (-(Complex.I * ((2 * Real.pi * (v : ℝ) / 1024 : ℝ) : ℂ))))) := by
      rw [← hphase1]; ring
    rw [hmul_reassoc]
    have hu00 : (t[msb ↦ false])[msb ↦ false] = t[msb ↦ false] := by funext w; by_cases hw : w = msb <;> simp [upd, hw]
    have hu01 : (t[msb ↦ false])[msb ↦ true] = t[msb ↦ true] := by funext w; by_cases hw : w = msb <;> simp [upd, hw]
    have hu10 : (t[msb ↦ true])[msb ↦ false] = t[msb ↦ false] := by funext w; by_cases hw : w = msb <;> simp [upd, hw]
    have hu11 : (t[msb ↦ true])[msb ↦ true] = t[msb ↦ true] := by funext w; by_cases hw : w = msb <;> simp [upd, hw]
    have hH : applyGate (.H msb) ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • ket (t[msb ↦ false]) +
        -((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * Complex.exp (-(Complex.I * ((2 * Real.pi * (v : ℝ) / 1024 : ℝ) : ℂ)))) •
          ket (t[msb ↦ true])) =
        (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • ket (t[msb ↦ false]) +
          ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * 1) • ket (t[msb ↦ true])) +
        -((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * Complex.exp (-(Complex.I * ((2 * Real.pi * (v : ℝ) / 1024 : ℝ) : ℂ)))) •
          ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • ket (t[msb ↦ false]) +
          ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * -1) • ket (t[msb ↦ true])) := by
      rw [map_add, map_smul, map_smul, applyGate_H_ket, applyGate_H_ket, upd_same, upd_same,
        hu00, hu01, hu10, hu11]
      simp only [Bool.false_eq_true, if_false, if_true]
    rw [hH]
    simp only [map_add, map_smul, mul_one, mul_neg]
    rw [centerLoop_ket ws 11 (by rw [hl]; decide) (t[msb ↦ false]),
      centerLoop_ket ws 11 (by rw [hl]; decide) (t[msb ↦ true]), ht0_eq, ht1_eq]
    have haddr0 : tableAddressValue ws (phaseWordState ws (bs ++ [false]) s) = v := by
      rw [tableAddressValue_phaseWordState ws hnd _ (by simp [hbl, hl]) s, boolWordToNat_append, hbl]
      simp [boolWordToNat, v]
    have haddr1 : tableAddressValue ws (phaseWordState ws (bs ++ [true]) s) = v + 512 := by
      rw [tableAddressValue_phaseWordState ws hnd _ (by simp [hbl, hl]) s, boolWordToNat_append, hbl]
      simp [boolWordToNat, v]
    have hv0 : boolWordToNat (bs ++ [false]) = v := by
      rw [boolWordToNat_append, hbl]; simp [boolWordToNat, v]
    have hv1 : boolWordToNat (bs ++ [true]) = v + 512 := by
      rw [boolWordToNat_append, hbl]; simp [boolWordToNat, v]
    rw [haddr0, haddr1, hv0, hv1]
    have he0_p : Complex.exp (Complex.I * (((2 * Real.pi / (2 : ℝ) ^ 11) * (v : ℝ) : ℝ) : ℂ)) =
        Complex.exp (Complex.I * ((Real.pi * (v : ℝ) / (2 : ℝ) ^ 10 : ℝ) : ℂ)) := by
      congr 2; push_cast; ring
    have he0_m : Complex.exp (-(Complex.I * ((2 * Real.pi * (v : ℝ) / 1024 : ℝ) : ℂ))) *
        Complex.exp (Complex.I * (((2 * Real.pi / (2 : ℝ) ^ 11) * (v : ℝ) : ℝ) : ℂ)) =
        Complex.exp (-(Complex.I * ((Real.pi * (v : ℝ) / (2 : ℝ) ^ 10 : ℝ) : ℂ))) := by
      rw [← Complex.exp_add]; congr 1
      have hreal : -(2 * Real.pi * (v : ℝ) / 1024) + 2 * Real.pi / (2 : ℝ) ^ 11 * (v : ℝ) =
          -(Real.pi * (v : ℝ) / (2 : ℝ) ^ 10) := by norm_num; ring
      have hC := congrArg (fun x : ℝ => Complex.I * (x : ℂ)) hreal
      simpa [Complex.ofReal_add, Complex.ofReal_neg, mul_add] using hC
    have he1_p : Complex.exp (Complex.I * (((2 * Real.pi / (2 : ℝ) ^ 11) * ((v + 512 : Nat) : ℝ) : ℝ) : ℂ)) =
        Complex.exp (Complex.I * ((Real.pi * ((v + 512 : Nat) : ℝ) / (2 : ℝ) ^ 10 : ℝ) : ℂ)) := by
      congr 2; push_cast; ring
    have he1_m : -(Complex.exp (-(Complex.I * ((2 * Real.pi * (v : ℝ) / 1024 : ℝ) : ℂ))) *
        Complex.exp (Complex.I * (((2 * Real.pi / (2 : ℝ) ^ 11) * ((v + 512 : Nat) : ℝ) : ℝ) : ℂ))) =
        Complex.exp (-(Complex.I * ((Real.pi * ((v + 512 : Nat) : ℝ) / (2 : ℝ) ^ 10 : ℝ) : ℂ))) := by
      rw [← Complex.exp_add]
      have hreal : -(2 * Real.pi * (v : ℝ) / 1024) + 2 * Real.pi / (2 : ℝ) ^ 11 * ((v + 512 : Nat) : ℝ) =
          -(Real.pi * ((v + 512 : Nat) : ℝ) / (2 : ℝ) ^ 10) + Real.pi := by
        push_cast; norm_num; ring
      have hC : -(Complex.I * ((2 * Real.pi * (v : ℝ) / 1024 : ℝ) : ℂ)) +
          Complex.I * (((2 * Real.pi / (2 : ℝ) ^ 11) * ((v + 512 : Nat) : ℝ) : ℝ) : ℂ) =
          -(Complex.I * ((Real.pi * ((v + 512 : Nat) : ℝ) / (2 : ℝ) ^ 10 : ℝ) : ℂ)) +
            (Real.pi : ℂ) * Complex.I := by
        have := congrArg (fun x : ℝ => Complex.I * (x : ℂ)) hreal
        simpa [Complex.ofReal_add, Complex.ofReal_neg, mul_add, mul_comm] using this
      rw [hC, Complex.exp_add, Complex.exp_pi_mul_I]; ring
    simp only [smul_add, smul_smul, sineWeight]
    have hcoeff0 :
        (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) *
            Complex.exp (Complex.I * (((2 * Real.pi / (2 : ℝ) ^ 11) * (v : ℝ) : ℝ) : ℂ)) +
          -((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * Complex.exp (-(Complex.I * ((2 * Real.pi * (v : ℝ) / 1024 : ℝ) : ℂ)))) *
            (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) *
            Complex.exp (Complex.I * (((2 * Real.pi / (2 : ℝ) ^ 11) * (v : ℝ) : ℝ) : ℂ)) =
        (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) *
          (Complex.exp (Complex.I * ((Real.pi * (v : ℝ) / (2 : ℝ) ^ 10 : ℝ) : ℂ)) -
           Complex.exp (-(Complex.I * ((Real.pi * (v : ℝ) / (2 : ℝ) ^ 10 : ℝ) : ℂ))))) := by
      rw [← he0_p, ← he0_m]; ring
    have hcoeff1 :
        (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) *
            Complex.exp (Complex.I * (((2 * Real.pi / (2 : ℝ) ^ 11) * ((v + 512 : Nat) : ℝ) : ℝ) : ℂ)) +
          -((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * Complex.exp (-(Complex.I * ((2 * Real.pi * (v : ℝ) / 1024 : ℝ) : ℂ)))) *
            -(((Real.sqrt 2)⁻¹ : ℝ) : ℂ) *
            Complex.exp (Complex.I * (((2 * Real.pi / (2 : ℝ) ^ 11) * ((v + 512 : Nat) : ℝ) : ℝ) : ℂ)) =
        (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) *
          (Complex.exp (Complex.I * ((Real.pi * ((v + 512 : Nat) : ℝ) / (2 : ℝ) ^ 10 : ℝ) : ℂ)) -
           Complex.exp (-(Complex.I * ((Real.pi * ((v + 512 : Nat) : ℝ) / (2 : ℝ) ^ 10 : ℝ) : ℂ))))) := by
      rw [← he1_p, ← he1_m]; ring
    rw [← hcoeff0, ← hcoeff1]
    module
  have hmap : ((fourierOutcomes 9).map (fun bs =>
      Quantum.run (centerLoop ws 11)
        (applyGate (.H msb)
          (Quantum.run (cPhaseLoop msb lo 11)
            (Quantum.run [.X msb, .H msb, .P .inverse 2 msb, .P .forward 11 msb]
              (ket (phaseWordState lo bs s))))))).sum =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
        ((fourierOutcomes 10).map (fun bs =>
          sineWeight 10 (boolWordToNat bs) • ket (phaseWordState ws bs s))).sum := by
    rw [List.map_congr_left hterm]
    rw [show (10 : Nat) = 9 + 1 from rfl, fourierOutcomes_add 9 1, fourierOutcomes_one]
    simp only [List.map_cons, List.map_nil, List.map_flatMap, List.flatMap_map]
    have hflat : ∀ (xs : List (List Bool)) (f : List Bool → State),
        (xs.flatMap (fun a => [f (a ++ [false]), f (a ++ [true])])).sum =
        (xs.map (fun a => f (a ++ [false]) + f (a ++ [true]))).sum := by
      intro xs f; induction xs with
      | nil => simp
      | cons x xs ih => simp [ih, add_assoc]
    rw [hflat (fourierOutcomes 9) (fun bs =>
      sineWeight (9 + 1) (boolWordToNat bs) • ket (phaseWordState ws bs s))]
    have hsmul : ∀ (xs : List (List Bool)) (c : ℂ) (f : List Bool → State),
        (xs.map (fun a => c • f a)).sum = c • (xs.map f).sum := by
      intro xs c f; induction xs with
      | nil => simp
      | cons x xs ih => simp [ih, smul_add]
    exact hsmul _ _ _
  rw [hmap, smul_smul, ← pow_succ]

/-! ### Static properties of `sineFromPlus` -/

theorem cPhaseLoop_wf (c : Wire) : ∀ (ts : List Wire) (k : Nat),
    c ∉ ts → CircuitWellFormed (cPhaseLoop c ts k)
  | [], _, _ => by simp [cPhaseLoop, CircuitWellFormed]
  | t :: ts, k, hc => by
    rw [cPhaseLoop, circuitWellFormed_append]
    have hne : c ≠ t := fun h => hc (h ▸ List.mem_cons_self)
    exact ⟨by simp [cPhaseBlock, CircuitWellFormed, Gate.WellFormed, hne],
      cPhaseLoop_wf c ts (k - 1) (fun h => hc (List.mem_cons_of_mem _ h))⟩

theorem centerLoop_wf : ∀ (ts : List Wire) (k : Nat), CircuitWellFormed (centerLoop ts k)
  | [], _ => by simp [centerLoop, CircuitWellFormed]
  | t :: ts, k => by
    rw [centerLoop, CircuitWellFormed, List.forall_mem_cons]
    exact ⟨trivial, centerLoop_wf ts (k - 1)⟩

theorem sineFromPlus_wellFormed (ws : List Wire) (hl : ws.length = 10) (hnd : ws.Nodup) :
    CircuitWellFormed (sineFromPlus ws) := by
  let lo := ws.take 9
  let msb := ws.getD 9 0
  have hws : ws = lo ++ [msb] := ws_split_10 ws hl
  have hnd' : (lo ++ [msb]).Nodup := by rwa [← hws]
  have hmsb_not_lo : msb ∉ lo := fun hm => (List.nodup_append.mp hnd').2.2 msb hm msb List.mem_cons_self rfl
  unfold sineFromPlus
  simp only [circuitWellFormed_append]
  exact ⟨⟨⟨by simp [CircuitWellFormed, Gate.WellFormed], cPhaseLoop_wf msb lo 11 hmsb_not_lo⟩,
    by simp [CircuitWellFormed, Gate.WellFormed]⟩, centerLoop_wf ws 11⟩

theorem cPhaseLoop_wires (c : Wire) : ∀ (ts : List Wire) (k : Nat),
    circuitWires (cPhaseLoop c ts k) ⊆ c :: ts
  | [], _, _, h => by simp [cPhaseLoop, circuitWires] at h
  | t :: ts, k, w, h => by
    rw [cPhaseLoop, MeasuredClear.circuitWires_append] at h
    rcases List.mem_append.mp h with h | h
    · simp only [cPhaseBlock, circuitWires, gateWires, List.flatMap_cons, List.flatMap_nil,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | (rfl | rfl) | rfl | (rfl | rfl) <;> simp
    · have hw := cPhaseLoop_wires c ts (k - 1) h
      rcases List.mem_cons.mp hw with rfl | hw
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)

theorem centerLoop_wires : ∀ (ts : List Wire) (k : Nat), circuitWires (centerLoop ts k) ⊆ ts
  | [], _, _, h => by simp [centerLoop, circuitWires] at h
  | t :: ts, k, w, h => by
    simp only [centerLoop, circuitWires, List.flatMap_cons, gateWires, List.mem_append,
      List.mem_singleton] at h
    rcases h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (centerLoop_wires ts (k - 1) h)

theorem sineFromPlus_wires (ws : List Wire) (hl : ws.length = 10) :
    circuitWires (sineFromPlus ws) ⊆ ws := by
  have hmsb_mem : ws.getD 9 0 ∈ ws := by
    rw [List.getD_eq_getElem _ _ (by omega : 9 < ws.length)]
    exact List.getElem_mem (by omega)
  unfold sineFromPlus
  intro w hw
  simp only [MeasuredClear.circuitWires_append, List.mem_append] at hw
  rcases hw with ((h1 | h2) | h3) | h4
  · simp only [circuitWires, gateWires, List.flatMap_cons, List.flatMap_nil, List.mem_append,
      List.mem_singleton, List.not_mem_nil, or_false] at h1
    rcases h1 with rfl | rfl | rfl | rfl | rfl <;> exact hmsb_mem
  · have h := cPhaseLoop_wires _ _ 11 h2
    rcases List.mem_cons.mp h with rfl | h
    · exact hmsb_mem
    · exact List.mem_of_mem_take h
  · simp only [circuitWires, gateWires, List.flatMap_cons, List.flatMap_nil, List.mem_append,
      List.mem_singleton, List.not_mem_nil, or_false] at h3
    subst h3; exact hmsb_mem
  · exact centerLoop_wires ws 11 h4

theorem cPhaseLoop_length (c : Wire) : ∀ (ts : List Wire) (k : Nat),
    (cPhaseLoop c ts k).length = 4 * ts.length
  | [], _ => rfl
  | t :: ts, k => by
    rw [cPhaseLoop, List.length_append, cPhaseLoop_length c ts (k - 1)]
    simp [cPhaseBlock]; omega

theorem centerLoop_length : ∀ (ts : List Wire) (k : Nat), (centerLoop ts k).length = ts.length
  | [], _ => rfl
  | _ :: ts, k => by simp [centerLoop, centerLoop_length ts (k - 1)]

theorem sineFromPlus_length (ws : List Wire) (hl : ws.length = 10) :
    (sineFromPlus ws).length = 52 := by
  unfold sineFromPlus
  simp only [List.length_append, List.length_cons, List.length_nil, cPhaseLoop_length,
    centerLoop_length, List.length_take, hl]
  decide

theorem literalProgram_weight4_eq {n s : Nat} (c : Circuit) :
    ConditionalCatalyst.weight4 (literalProgram (n := n) (s := s) c) =
      (c.map ConditionalCatalyst.weightedLiteral).sum := by
  induction c with
  | nil => rfl
  | cons g gs ih =>
    change ConditionalCatalyst.weight4 (.gate (.literal g) (literalProgram gs)) = _
    simp [ConditionalCatalyst.weight4, ih]

theorem literalProgram_added_eq {n s : Nat} (c : Circuit) :
    AndGadget.added (literalProgram (n := n) (s := s) c) =
      (c.map (fun g => match g with | .CCX _ _ _ => 1 | _ => 0)).sum := by
  induction c with
  | nil => rfl
  | cons g gs ih =>
    change AndGadget.added (.gate (.literal g) (literalProgram gs)) = _
    cases g <;> simp [AndGadget.added, ih]

theorem cPhaseLoop_weight4 (c : Wire) : ∀ (ts : List Wire) (k : Nat),
    ts.length + 2 ≤ k →
    ((cPhaseLoop c ts k).map ConditionalCatalyst.weightedLiteral).sum = 2 * ts.length
  | [], _, _ => rfl
  | t :: ts, k, hk => by
    have hk2 : k ≠ 2 := by simp at hk; omega
    have hk' : ts.length + 2 ≤ k - 1 := by simp at hk; omega
    rw [cPhaseLoop, List.map_append, List.sum_append, cPhaseLoop_weight4 c ts (k - 1) hk']
    simp [cPhaseBlock, ConditionalCatalyst.weightedLiteral, ConditionalCatalyst.weightedGate,
      ConditionalCatalyst.phaseTwoGate, tCost, hk2]
    omega

theorem centerLoop_weight4 : ∀ (ts : List Wire) (k : Nat),
    k = ts.length + 1 → 1 ≤ ts.length →
    ((centerLoop ts k).map ConditionalCatalyst.weightedLiteral).sum = ts.length - 1
  | [], _, _, h1 => by simp at h1
  | [t], k, hk, _ => by
    have hk2 : k = 2 := by simp at hk; omega
    subst hk2
    simp [centerLoop, ConditionalCatalyst.weightedLiteral, ConditionalCatalyst.weightedGate,
      ConditionalCatalyst.phaseTwoGate, tCost]
  | t :: t2 :: ts, k, hk, _ => by
    have hk2 : k ≠ 2 := by simp at hk; omega
    have hk' : k - 1 = (t2 :: ts).length + 1 := by simp at hk ⊢; omega
    rw [centerLoop, List.map_cons, List.sum_cons, centerLoop_weight4 (t2 :: ts) (k - 1) hk' (by simp)]
    simp [ConditionalCatalyst.weightedLiteral, ConditionalCatalyst.weightedGate,
      ConditionalCatalyst.phaseTwoGate, tCost, hk2]
    omega

theorem sineFromPlus_weight4 {n s : Nat} (ws : List Wire) (hl : ws.length = 10) :
    ConditionalCatalyst.weight4 (literalProgram (n := n) (s := s) (sineFromPlus ws)) = 28 := by
  rw [literalProgram_weight4_eq]
  unfold sineFromPlus
  simp only [List.map_append, List.sum_append]
  rw [cPhaseLoop_weight4 _ _ 11 (by simp [hl]), centerLoop_weight4 ws 11 (by omega) (by omega)]
  simp [ConditionalCatalyst.weightedLiteral, ConditionalCatalyst.weightedGate,
    ConditionalCatalyst.phaseTwoGate, tCost, hl]

theorem sineFromPlus_added {n s : Nat} (ws : List Wire) :
    AndGadget.added (literalProgram (n := n) (s := s) (sineFromPlus ws)) = 0 := by
  rw [literalProgram_added_eq]
  have hc : ∀ (c : Wire) (ts : List Wire) (k : Nat),
      ((cPhaseLoop c ts k).map (fun g => match g with | .CCX _ _ _ => 1 | _ => 0)).sum = 0 := by
    intro c ts; induction ts with
    | nil => intro _; rfl
    | cons t ts ih => intro k; simp [cPhaseLoop, cPhaseBlock, ih]
  have hd : ∀ (ts : List Wire) (k : Nat),
      ((centerLoop ts k).map (fun g => match g with | .CCX _ _ _ => 1 | _ => 0)).sum = 0 := by
    intro ts; induction ts with
    | nil => intro _; rfl
    | cons t ts ih => intro k; simp [centerLoop, ih]
  unfold sineFromPlus
  simp [List.map_append, List.sum_append, hc, hd]

theorem sineFromPlus_largePhase_false (ws : List Wire) (cutoff : Nat) (hc : 11 ≤ cutoff) :
    ∀ g ∈ sineFromPlus ws, ApproximatePhase34.largePhase cutoff g = false := by
  have h1 : ∀ (c : Wire) (ts : List Wire) (k : Nat), k ≤ cutoff →
      ∀ g ∈ cPhaseLoop c ts k, ApproximatePhase34.largePhase cutoff g = false := by
    intro c ts; induction ts with
    | nil => intro _ _ _ hg; simp [cPhaseLoop] at hg
    | cons t ts ih =>
      intro k hk g hg
      rw [cPhaseLoop, List.mem_append] at hg
      rcases hg with hg | hg
      · simp only [cPhaseBlock, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl | rfl <;>
          simp [ApproximatePhase34.largePhase, show ¬ cutoff < k by omega]
      · exact ih (k - 1) (by omega) g hg
  have h2 : ∀ (ts : List Wire) (k : Nat), k ≤ cutoff →
      ∀ g ∈ centerLoop ts k, ApproximatePhase34.largePhase cutoff g = false := by
    intro ts; induction ts with
    | nil => intro _ _ _ hg; simp [centerLoop] at hg
    | cons t ts ih =>
      intro k hk g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · simp [ApproximatePhase34.largePhase, show ¬ cutoff < k by omega]
      · exact ih (k - 1) (by omega) g hg
  unfold sineFromPlus
  intro g hg
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with (((rfl | rfl | rfl | rfl | rfl) | hg) | rfl) | hg
  · rfl
  · rfl
  · rfl
  · simp [ApproximatePhase34.largePhase, show ¬ cutoff < 2 by omega]
  · simp [ApproximatePhase34.largePhase, show ¬ cutoff < 11 by omega]
  · exact h1 _ _ 11 hc g hg
  · rfl
  · exact h2 ws 11 hc g hg

theorem literalProgram_removed_zero {n s : Nat} (cutoff : Nat) (c : Circuit)
    (h : ∀ g ∈ c, ApproximatePhase34.largePhase cutoff g = false) :
    ApproximatePhase34.removed cutoff (literalProgram (n := n) (s := s) c) = 0 := by
  induction c with
  | nil => rfl
  | cons g gs ih =>
    change ApproximatePhase34.removed cutoff (.gate (.literal g) (literalProgram gs)) = 0
    simp [ApproximatePhase34.removed, h g List.mem_cons_self,
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem sineFromPlus_removed {n s : Nat} (ws : List Wire) (cutoff : Nat) (hc : 11 ≤ cutoff) :
    ApproximatePhase34.removed cutoff (literalProgram (n := n) (s := s) (sineFromPlus ws)) = 0 :=
  literalProgram_removed_zero cutoff (sineFromPlus ws) (sineFromPlus_largePhase_false ws cutoff hc)

/-! ### Extending `sineFromPlus` to a full window bank `bank = pref ++ top10` -/

theorem sineFromPlus_bank (bank : List Wire) (hw : 10 ≤ bank.length) (hnd : bank.Nodup)
    (s : BasisState) (hclean : Clean bank s) :
    Quantum.run (sineFromPlus (bank.drop (bank.length - 10))) (Quantum.run (bank.map Gate.H) (ket s)) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ bank.length) •
        ((fourierOutcomes bank.length).map (fun bs =>
          sineWeight 10 (boolWordToNat bs / 2 ^ (bank.length - 10)) • ket (phaseWordState bank bs s))).sum := by
  let d := bank.length - 10
  let pref := bank.take d
  let top := bank.drop d
  have hbank : bank = pref ++ top := (List.take_append_drop d bank).symm
  have hpref_len : pref.length = d := by simp [pref, d]
  have htop_len : top.length = 10 := by simp [top, d]; omega
  have hnd' : (pref ++ top).Nodup := by rwa [← hbank]
  obtain ⟨hpref_nd, htop_nd, hdisj⟩ := List.nodup_append.mp hnd'
  have hclean_pref : Clean pref s := fun w hm => hclean w (by rw [hbank]; exact List.mem_append_left _ hm)
  have hclean_top : Clean top s := fun w hm => hclean w (by rw [hbank]; exact List.mem_append_right _ hm)
  have hH_split : Quantum.run (bank.map Gate.H) (ket s) =
      Quantum.run (top.map Gate.H) (Quantum.run (pref.map Gate.H) (ket s)) := by
    rw [hbank, List.map_append, Quantum.run_append]
  rw [hH_split, phaseHadamards_uniform pref hpref_nd s hclean_pref, hpref_len]
  simp only [phaseUniformSum, hpref_len, map_smul, stateLinear_list_sum, List.map_map, Function.comp_def]
  have hper (a : List Bool) (ha : a ∈ fourierOutcomes d) :
      Quantum.run (sineFromPlus top) (Quantum.run (top.map Gate.H) (ket (phaseWordState pref a s))) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 10) •
        ((fourierOutcomes 10).map (fun b =>
          sineWeight 10 (boolWordToNat (a ++ b) / 2 ^ d) • ket (phaseWordState bank (a ++ b) s))).sum := by
    have hal : a.length = d := (fourierOutcomes_mem d a).mp ha
    have hct : Clean top (phaseWordState pref a s) := fun w hm => by
      rw [phaseWordState_frame pref a s w (fun hp => hdisj w hp w hm rfl)]
      exact hclean_top w hm
    rw [sineFromPlus_ket top htop_len htop_nd (phaseWordState pref a s) hct]
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro b hb
    have hdiv : boolWordToNat (a ++ b) / 2 ^ d = boolWordToNat b := by
      rw [boolWordToNat_append, hal, Nat.add_mul_div_left _ _ (pow_pos (by decide) d),
        Nat.div_eq_of_lt (by simpa [hal] using boolWordToNat_lt a), Nat.zero_add]
    have hst : phaseWordState top b (phaseWordState pref a s) = phaseWordState bank (a ++ b) s := by
      rw [hbank, phaseWordState_append pref top a b (hal.trans hpref_len.symm) s]
    rw [hdiv, hst]
  rw [List.map_congr_left hper]
  have hsmul : ∀ (xs : List (List Bool)) (c : ℂ) (f : List Bool → State),
      (xs.map (fun a => c • f a)).sum = c • (xs.map f).sum := by
    intro xs c f; induction xs with
    | nil => simp
    | cons x xs ih => simp [ih, smul_add]
  have hflat_sum : ∀ (xs : List (List Bool)) (f : List Bool → List State),
      (xs.flatMap f).sum = (xs.map (fun a => (f a).sum)).sum := by
    intro xs f; induction xs with
    | nil => simp
    | cons x xs ih => simp [ih]
  rw [hsmul, smul_smul, ← pow_add]
  have hlen : d + 10 = bank.length := by omega
  rw [← hlen, fourierOutcomes_add d 10, List.map_flatMap]
  congr 1
  rw [hflat_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  simp [List.map_map, Function.comp_def, Nat.add_sub_cancel]

/-! ### Part 2: `sinePhaseAmplitude`, `windowedPointState`, and character expansion -/

/-- Exact 1D phase-estimation amplitude for the 10-bit centered sine window. -/
def sinePhaseAmplitude (precision : Nat) (phase : ℝ) (value : Nat) : ℂ :=
  ((2 ^ precision : Nat) : ℂ)⁻¹ *
    ∑ x ∈ Finset.range (2 ^ precision),
      sineWeight 10 (x / 2 ^ (precision - 10)) * eigenvalue (phase - (value : ℝ) / (2 ^ precision : Nat)) ^ x

theorem sinePhaseAmplitude_mod (precision r x value : Nat) (hr : 0 < r) :
    sinePhaseAmplitude precision ((x : ℝ) / r) value =
      sinePhaseAmplitude precision (((x % r : Nat) : ℝ) / r) value := by
  unfold sinePhaseAmplitude
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have hr0 : (r : ℝ) ≠ 0 := by positivity
  have hdiv : (x : ℝ) / r - (value : ℝ) / (2 ^ precision : Nat) =
      (((x % r : Nat) : ℝ) / r - (value : ℝ) / (2 ^ precision : Nat)) + ((x / r : Nat) : ℝ) := by
    have h := Nat.mod_add_div x r
    have hR : (x : ℝ) = ((x % r : Nat) : ℝ) + r * ((x / r : Nat) : ℝ) := by exact_mod_cast h.symm
    rw [hR]; field_simp [hr0]; ring
  rw [hdiv]
  have he : ∀ (θ : ℝ) (m : Nat), eigenvalue (θ + (m : ℝ)) = eigenvalue θ := by
    intro θ m
    rw [eigenvalue_add]
    have hm : eigenvalue (m : ℝ) = 1 := by
      unfold eigenvalue
      have : Complex.I * ((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) = (m : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast; ring
      rw [this, Complex.exp_nat_mul_two_pi_mul_I]
    rw [hm, mul_one]
  rw [he]

/-- Exact 2D character-mixture output probability for the 10-bit sine-windowed Shor circuit. -/
def sinePairMass (r n m d : Nat) (out : Fin (2 ^ n) × Fin (2 ^ m)) : ℝ :=
  (r : ℝ)⁻¹ * ∑ k : Fin r,
    Complex.normSq (sinePhaseAmplitude n ((k.val : ℝ) / r) out.1.val) *
    Complex.normSq (sinePhaseAmplitude m (((d * k.val % r : Nat) : ℝ) / r) out.2.val)

/-- Coherent Fourier sum for two sine-windowed axes, before measuring the point register. -/
def windowedPointState (Q : Point) (root : BasisState) (n m : Nat) (x y : List Bool) : State :=
  let c : ℂ := ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ (n + m)
  c • ((fourierOutcomes n).map (fun a =>
    ((fourierOutcomes m).map (fun b =>
      (c * (sineWeight 10 (boolWordToNat a / 2 ^ (n - 10)) *
            dyadicFourierKernel .inverse n (boolWordToNat a) (fourierWordLSB x)) *
           (sineWeight 10 (boolWordToNat b / 2 ^ (m - 10)) *
            dyadicFourierKernel .inverse m (boolWordToNat b) (fourierWordLSB y))) •
      ket (pointWrite (boolWordToNat a • G + boolWordToNat b • Q) root))).sum)).sum

def windowedEventMass (Q : Point) (root : BasisState) (n m : Nat)
    (accept : Nat → Nat → Bool) : ℝ :=
  ((fourierOutcomes n).map (fun x => ((fourierOutcomes m).map (fun y =>
    if accept (fourierWordLSB x) (fourierWordLSB y) then
      normSq (windowedPointState Q root n m x y) else 0)).sum)).sum

private theorem outcome_words_perm_local (n : Nat) :
    ((fourierOutcomes n).map boolWordToNat).Perm (List.range (2 ^ n)) := by
  have hbw : ∀ bs : List Bool, boolWordToNat bs = fourierWordLSB bs := by
    intro bs; induction bs with
    | nil => rfl
    | cons x xs ih => simp [boolWordToNat, fourierWordLSB, ih]
  have hn : ((fourierOutcomes n).map boolWordToNat).Nodup :=
    (fourierOutcomes_nodup n).map_on (by
      intro a ha b hb hv
      rw [hbw a, hbw b] at hv
      exact fourierWordLSB_injective a b
        (((fourierOutcomes_mem _ _).mp ha).trans ((fourierOutcomes_mem _ _).mp hb).symm) hv)
  apply (List.perm_ext_iff_of_nodup hn List.nodup_range).mpr
  intro k
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨bs, hbs, rfl⟩
    rw [hbw bs]
    simpa only [(fourierOutcomes_mem _ _).mp hbs] using fourierWordLSB_lt bs
  · intro hk
    obtain ⟨bs, hlen, hv⟩ := fourierWordLSB_surjective n k hk
    exact ⟨bs, (fourierOutcomes_mem _ _).mpr hlen, (hbw bs).trans hv⟩

private theorem sum_map_range_local (n : Nat) (f : Nat → ℂ) :
    ((List.range n).map f).sum = ∑ x ∈ Finset.range n, f x := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, ih, Finset.sum_range_succ]

private theorem norm_sq_half (n : Nat) :
    ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ n) * ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ n) = ((2 ^ n : Nat) : ℂ)⁻¹ := by
  have hh : ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ 2) = (2 : ℂ)⁻¹ := by
    have h : ((Real.sqrt 2)⁻¹) ^ 2 = (2 : ℝ)⁻¹ := by
      rw [inv_pow, Real.sq_sqrt (by norm_num)]
    rw [← Complex.ofReal_pow, h, Complex.ofReal_inv]
    norm_num
  rw [← pow_two, ← pow_mul, Nat.mul_comm n 2, pow_mul, hh, inv_pow]
  norm_cast

private theorem kernel_mul_eigenvalue (phase : ℝ) (n v : Nat) (out : List Bool) (hlen : out.length = n) :
    dyadicFourierKernel .inverse n v (fourierWordLSB out) * eigenvalue (phase * v) =
      eigenvalue (phase - (fourierWordLSB out : ℝ) / (2 ^ n : Nat)) ^ v := by
  rw [dyadicFourierKernel, eigenvalue_pow_eq_eigenvalue_mul]
  unfold phaseCoeff phaseAngle eigenvalue
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem sineWord_weighted_sum (phase : ℝ) (n : Nat) (out : List Bool) (hlen : out.length = n) :
    ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ n) * ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ n) *
      ((fourierOutcomes n).map (fun bs =>
        (sineWeight 10 (boolWordToNat bs / 2 ^ (n - 10)) *
          dyadicFourierKernel .inverse n (boolWordToNat bs) (fourierWordLSB out)) *
          eigenvalue (phase * boolWordToNat bs))).sum =
      sinePhaseAmplitude n phase (fourierWordLSB out) := by
  rw [norm_sq_half]
  have hperm := ((outcome_words_perm_local n).map (fun v =>
    sineWeight 10 (v / 2 ^ (n - 10)) *
      (dyadicFourierKernel .inverse n v (fourierWordLSB out) * eigenvalue (phase * v)))).sum_eq
  simp only [List.map_map, Function.comp_def, sum_map_range_local] at hperm
  have hre : ((fourierOutcomes n).map (fun bs =>
      (sineWeight 10 (boolWordToNat bs / 2 ^ (n - 10)) *
        dyadicFourierKernel .inverse n (boolWordToNat bs) (fourierWordLSB out)) *
        eigenvalue (phase * boolWordToNat bs))).sum =
      ∑ x ∈ Finset.range (2 ^ n),
        sineWeight 10 (x / 2 ^ (n - 10)) *
          eigenvalue (phase - (fourierWordLSB out : ℝ) / (2 ^ n : Nat)) ^ x := by
    calc
      _ = ((fourierOutcomes n).map (fun bs =>
            sineWeight 10 (boolWordToNat bs / 2 ^ (n - 10)) *
              (dyadicFourierKernel .inverse n (boolWordToNat bs) (fourierWordLSB out) *
                eigenvalue (phase * boolWordToNat bs)))).sum := by
        congr 1; apply List.map_congr_left; intro bs _; ring
      _ = ∑ x ∈ Finset.range (2 ^ n),
            sineWeight 10 (x / 2 ^ (n - 10)) *
              (dyadicFourierKernel .inverse n x (fourierWordLSB out) * eigenvalue (phase * x)) := hperm
      _ = _ := by
        apply Finset.sum_congr rfl; intro x _
        rw [kernel_mul_eigenvalue phase n x out hlen]
  rw [hre]; rfl

theorem windowedPointState_mass (Q : Point) (d : Nat) (hd : Q = d • G)
    (root : BasisState) (n m : Nat) (x y : List Bool)
    (hx : x.length = n) (hy : y.length = m)
    (out : Fin (2 ^ n) × Fin (2 ^ m))
    (hox : fourierWordLSB x = out.1.val) (hoy : fourierWordLSB y = out.2.val) :
    normSq (windowedPointState Q root n m x y) = sinePairMass order n m d out := by
  unfold windowedPointState
  rw [pointDoubleSum_normalize _ _ _ _ _ G Q d hd root, pow_add]
  have hw := weighted_point_character_sum order_prime G generator_order root
    ((fourierOutcomes n).map boolWordToNat) ((fourierOutcomes m).map boolWordToNat)
    (fun a => sineWeight 10 (a / 2 ^ (n - 10)) * dyadicFourierKernel .inverse n a (fourierWordLSB x))
    (fun b => sineWeight 10 (b / 2 ^ (m - 10)) * dyadicFourierKernel .inverse m b (fourierWordLSB y)) d
  simp only [List.map_map, Function.comp_def] at hw
  rw [hw, smul_comm, Finset.smul_sum]
  have hterm (k : Fin order) :
      ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ n * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ m *
        ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ n * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ m)) •
      ((((fourierOutcomes n).map (fun a =>
          sineWeight 10 (boolWordToNat a / 2 ^ (n - 10)) *
            dyadicFourierKernel .inverse n (boolWordToNat a) (fourierWordLSB x) *
            eigenvalue ((k.val : ℝ) / (order : ℝ) * boolWordToNat a))).sum *
        ((fourierOutcomes m).map (fun b =>
          sineWeight 10 (boolWordToNat b / 2 ^ (m - 10)) *
            dyadicFourierKernel .inverse m (boolWordToNat b) (fourierWordLSB y) *
            eigenvalue (((k.val * d : Nat) : ℝ) / (order : ℝ) * boolWordToNat b))).sum) •
        pointCyclicState G root k) =
      (sinePhaseAmplitude n ((k.val : ℝ) / (order : ℝ)) out.1.val *
       sinePhaseAmplitude m (((d * k.val % order : Nat) : ℝ) / (order : ℝ)) out.2.val) •
        pointCyclicState G root k := by
    rw [smul_smul]
    congr 1
    have ha := sineWord_weighted_sum ((k.val : ℝ) / (order : ℝ)) n x hx
    have hb := sineWord_weighted_sum (((k.val * d : Nat) : ℝ) / (order : ℝ)) m y hy
    rw [hox] at ha; rw [hoy] at hb
    have hbm : sinePhaseAmplitude m (((k.val * d : Nat) : ℝ) / (order : ℝ)) out.2.val =
        sinePhaseAmplitude m (((d * k.val % order : Nat) : ℝ) / (order : ℝ)) out.2.val := by
      rw [Nat.mul_comm k.val d]
      exact sinePhaseAmplitude_mod m order (d * k.val) out.2.val order_prime.pos
    rw [hox, hoy, ← ha, ← hbm, ← hb]
    ring
  simp_rw [hterm]
  rw [Finset.smul_sum]
  simp only [smul_smul, pointCyclicState]
  rw [cyclicState_mass order_prime _ (pointCyclicBasis_orthonormal G root generator_order)]
  have hn : Complex.normSq ((((Real.sqrt order)⁻¹ : ℝ) : ℂ)) = 1 / (order : ℝ) := by
    simp [Complex.normSq_ofReal]
  simp_rw [Complex.normSq_mul, hn]
  rw [← Finset.mul_sum]
  simp [sinePairMass, one_div]

private theorem outcome_sum_local (n : Nat) (f : List Bool → ℝ) :
    ((fourierOutcomes n).map f).sum = ∑ v : Fin (2 ^ n), f (paperOutcomeBits n v) := by
  rw [← List.sum_toFinset _ (fourierOutcomes_nodup n)]
  symm
  apply Finset.sum_bij (fun v _ => paperOutcomeBits n v)
  · intro v _
    exact List.mem_toFinset.mpr ((fourierOutcomes_mem n _).mpr (paperOutcomeBits_length n v))
  · intro u _ v _ huv
    apply Fin.ext
    rw [← paperOutcomeBits_word n u, ← paperOutcomeBits_word n v, huv]
  · intro bs hbs
    have hlen : bs.length = n := (fourierOutcomes_mem n bs).mp (List.mem_toFinset.mp hbs)
    refine ⟨⟨fourierWordLSB bs, by simpa only [hlen] using fourierWordLSB_lt bs⟩, Finset.mem_univ _, ?_⟩
    exact fourierWordLSB_injective _ _ ((paperOutcomeBits_length n _).trans hlen.symm)
      (paperOutcomeBits_word n _)
  · intro _ _; rfl

theorem windowedEventMass_distribution (Q : Point) (d : Nat) (hd : Q = d • G)
    (root : BasisState) (n m : Nat) (accept : Nat → Nat → Bool) :
    windowedEventMass Q root n m accept =
      ∑ a : Fin (2 ^ n), ∑ b : Fin (2 ^ m),
        if accept a.val b.val then sinePairMass order n m d (a, b) else 0 := by
  unfold windowedEventMass
  rw [outcome_sum_local n]
  apply Finset.sum_congr rfl
  intro a _
  rw [outcome_sum_local m]
  apply Finset.sum_congr rfl
  intro b _
  simp only [paperOutcomeBits_word]
  split_ifs
  · exact windowedPointState_mass Q d hd root n m _ _ (paperOutcomeBits_length n a)
      (paperOutcomeBits_length m b) (a, b) (paperOutcomeBits_word n a) (paperOutcomeBits_word m b)
  · rfl

/-! ### Part 3: Windowed semiclassical QPE bridge (`selectedTwoAxes` → `windowedEventMass`) -/

section WindowedBridge
variable [b : Single.WindowBody] [ledger : Single.ProducerResources b]

def WindowedFirstRule {n : Nat} {read : ConstantBit n → Bool}
    (root : BasisState) (ψ : State) (w : WindowModel read) : Prop :=
  10 ≤ w.physical.wires.length ∧
  ∀ prior bits, w.step prior bits ψ =
    (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ w.physical.wires.length) •
      ((fourierOutcomes w.physical.wires.length).map (fun input =>
        (sineWeight 10 (boolWordToNat input / 2 ^ (w.physical.wires.length - 10)) *
          fourierBitAmplitude .inverse input.reverse prior bits) •
          ket (pointWrite (w.point (boolWordToNat input)) root))).sum

def WindowedPointRule {n : Nat} {read : ConstantBit n → Bool}
    (root : BasisState) (w : WindowModel read) : Prop :=
  10 ≤ w.physical.wires.length ∧
  ∀ prior bits P, w.step prior bits (ket (pointWrite P root)) =
    (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ w.physical.wires.length) •
      ((fourierOutcomes w.physical.wires.length).map (fun input =>
        (sineWeight 10 (boolWordToNat input / 2 ^ (w.physical.wires.length - 10)) *
          fourierBitAmplitude .inverse input.reverse prior bits) •
          ket (pointWrite (P + w.point (boolWordToNat input)) root))).sum

theorem scalarWord_head_div (input : List Bool) (inputs : List (List Bool)) (h10 : 10 ≤ input.length) :
    boolWordToNat (scalarWord (input :: inputs)) / 2 ^ ((input.length + inputs.flatten.length) - 10) =
      boolWordToNat input / 2 ^ (input.length - 10) := by
  have hlt : boolWordToNat (scalarWord inputs) < 2 ^ inputs.flatten.length := by
    have hlen : (scalarWord inputs).length = inputs.flatten.length := by
      simp [scalarWord, List.length_flatten, List.map_map, Function.comp_def, List.length_reverse]
    simpa [hlen] using boolWordToNat_lt (scalarWord inputs)
  have hpow : 2 ^ ((input.length + inputs.flatten.length) - 10) =
      2 ^ inputs.flatten.length * 2 ^ (input.length - 10) := by
    rw [← pow_add]; congr 1; omega
  rw [scalarWord_cons, hpow, ← Nat.div_div_eq_div_mul,
    Nat.mul_comm (boolWordToNat input), Nat.mul_add_div (pow_pos (by decide) _),
    Nat.div_eq_of_lt hlt, Nat.add_zero]

private theorem windowed_axis_expand {n : Nat} {read : ConstantBit n → Bool}
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
  apply List.map_congr_left
  intro input _
  apply congrArg List.sum
  apply List.map_congr_left
  intro inputs _
  congr 1; simp only [List.headD_cons]; ring

theorem windowed_two_modelBranches {n : Nat} {read : ConstantBit n → Bool}
    (Q : Point) (root : BasisState) (ψ : State)
    (fL : WindowModel read) (restL : List (WindowModel read))
    (fR : WindowModel read) (restR : List (WindowModel read))
    (hfL : WindowedFirstRule root ψ fL)
    (hfR : WindowedPointRule root fR)
    (hrest : ∀ w ∈ restL ++ restR, PointRule root w)
    (hwL : ModelWeights G (fL :: restL)) (hwR : ModelWeights Q (fR :: restR))
    (hbias : ((fL :: restL).map WindowModel.bias).sum + ((fR :: restR).map WindowModel.bias).sum = 0)
    (lbp : List (WindowModel read × List Bool)) (hlbp : lbp ∈ outputPaths (fL :: restL))
    (rbp : List (WindowModel read × List Bool)) (hrbp : rbp ∈ outputPaths (fR :: restR)) :
    modelBranch rbp List.nil (modelBranch lbp List.nil ψ) =
      windowedPointState Q root (precision (fL :: restL)) (precision (fR :: restR))
        (lbp.map Prod.snd).flatten (rbp.map Prod.snd).flatten := by
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
    windowed_axis_expand root fR bR rtail hruleR A (hfR.2 List.nil bR A)
  simp only [Function.comp_def, map_smul, hR_exp, List.smul_sum, List.map_map, smul_smul]
  have hlenL := outputPath_lengths (fL :: restL) ((fL, bL) :: ltail) hlbp
  have hlenR := outputPath_lengths (fR :: restR) ((fR, bR) :: rtail) hrbp
  have hdescL := outputPath_weights G (fL :: restL) hwL ((fL, bL) :: ltail) hlbp
  have hdescR := outputPath_weights Q (fR :: restR) hwR ((fR, bR) :: rtail) hrbp
  have hbias_zero : (0 : Point) = biasSum DigitWindow.bias pathL + biasSum DigitWindow.bias pathR := by
    have h1 := outputPath_bias (fL :: restL) ((fL, bL) :: ltail) hlbp
    have h2 := outputPath_bias (fR :: restR) ((fR, bR) :: rtail) hrbp
    dsimp only [pathL, pathR]
    rw [h1, h2]
    exact hbias.symm
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
      ket (pointWrite (boolWordToNat a • G + boolWordToNat b • Q) root)
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
    have hrec := two_axes_reconstruct Q DigitWindow.bias DigitWindow.bias pathL pathR hdescL hdescR
      0 hbias_zero inputsL inputsR ((inputWords_mem _ _).mp hinL) ((inputWords_mem _ _).mp hinR)
    rw [hrec, hhead_divL inputsL hinL, hhead_divR inputsR hinR,
      inputWeight_kernel pathL inputsL hlenL ((inputWords_mem _ _).mp hinL),
      inputWeight_kernel pathR inputsR hlenR ((inputWords_mem _ _).mp hinR)]
    unfold F c
    congr 1
    change _ = (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ (nL + nR)) * _
    rw [show 2 * (pathWidths pathL).sum = nL + nL by dsimp [nL]; omega,
      show 2 * (pathWidths pathR).sum = nR + nR by dsimp [nR]; omega]
    simp only [pow_add]
    ring
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
  simp only [List.smul_sum, List.map_map, Function.comp_def, smul_smul]
  rw [← hwl, ← hwr, ← hsl, ← hsr]

theorem windowed_idealTwoAxes_event_mass {n : Nat} {read : ConstantBit n → Bool}
    (Q : Point) (root : BasisState) (ψ : State)
    (fL : WindowModel read) (restL : List (WindowModel read))
    (fR : WindowModel read) (restR : List (WindowModel read))
    (hfL : WindowedFirstRule root ψ fL)
    (hfR : WindowedPointRule root fR)
    (hrest : ∀ w ∈ restL ++ restR, PointRule root w)
    (hwL : ModelWeights G (fL :: restL)) (hwR : ModelWeights Q (fR :: restR))
    (hbias : ((fL :: restL).map WindowModel.bias).sum + ((fR :: restR).map WindowModel.bias).sum = 0)
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
    rw [windowed_two_modelBranches Q root ψ fL restL fR restR hfL hfR hrest hwL hwR hbias lbp hlbp rbp hrbp]
    simp only [List.append_nil, List.reverse_reverse]
    split_ifs
    · exact hJ _
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

theorem windowed_physicalTwoAxes_event_mass {n : Nat} {read : ConstantBit n → Bool}
    (Q : Point) (root : BasisState) (ψ : State)
    (fL : WindowModel read) (restL : List (WindowModel read))
    (fR : WindowModel read) (restR : List (WindowModel read))
    (hfL : WindowedFirstRule root ψ fL)
    (hfR : WindowedPointRule root fR)
    (hrest : ∀ w ∈ restL ++ restR, PointRule root w)
    (hwL : ModelWeights G (fL :: restL)) (hwR : ModelWeights Q (fR :: restR))
    (hbias : ((fL :: restL).map WindowModel.bias).sum + ((fR :: restR).map WindowModel.bias).sum = 0)
    (hready : Ready ((fL :: restL) ++ (fR :: restR)) ψ)
    (start : Nat) (history : Fin start → Bool)
    (J : Instrument) (hJ : ∀ φ, J.bornMass φ = normSq φ) (accept : Nat → Nat → Bool) :
    (selectedTwoAxes (fL :: restL) (fR :: restR) start history (fun lhs rhs =>
      if accept (fourierWordLSB lhs.reverse) (fourierWordLSB rhs.reverse) then J else List.nil)).bornMass ψ =
      windowedEventMass Q root (precision (fL :: restL)) (precision (fR :: restR)) accept := by
  rw [selectedTwoAxes_mass (fL :: restL) (fR :: restR) start history _ ψ hready]
  exact windowed_idealTwoAxes_event_mass Q root ψ fL restL fR restR hfL hfR hrest hwL hwR hbias J hJ accept

end WindowedBridge

#print axioms sineFromPlus_ket
#print axioms sineFromPlus_weight4
#print axioms windowedEventMass_distribution
#print axioms windowed_physicalTwoAxes_event_mass

end
end ShorECDLP.Entrant.SineCircuit
