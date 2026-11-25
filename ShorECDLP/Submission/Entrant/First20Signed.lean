import ShorECDLP.Submission.Entrant.WideBank8

set_option Elab.async false

/-! ### Consolidated from `Readout3.lean` -/
section
/-! Three neighbouring right words from one 204-bit sample: the centre, `+1`, and `-1`.
Direct specialization of `NeighborReadout` (matching `Readout56` at 1 positive and 1 negative step).
Every gate is a record-controlled Clifford on wires 0 and 1 (`weight4 = 0`, `residue = 0`). -/


namespace ShorECDLP.Entrant.Readout3
open Quantum ShorECDLP.Challenge ShorECDLP.Entrant.RoundedReadout ShorECDLP.Entrant.NeighborReadout
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def suffix3 (n start width : Nat) (bits : Vector (Fin start) width) :
    Straight n start (start + 2 + 8 * width) :=
  let c := initialCursor bits
  let q := c.lift (1 * (2 * width))
  castFinish (by omega)
    ((constantStep n start).append
      ((positiveWords n 1 (start + 2) width c).append
        ((complementStep n q).append
          (negativeWords n 1 (start + 2 + 1 * (2 * width) + 2 * width) width q.next))))

def rightWords3 {start width : Nat} (bits : Vector (Fin start) width) : List (Vector Nat width) :=
  bits.map Fin.val ::
    List.ofFn (fun i : Fin 1 => sumPositions (start + 2 + i.val * (2 * width)) width) ++
    List.ofFn (fun i : Fin 1 => sumPositions
      (start + 2 + 1 * (2 * width) + 2 * width + i.val * (4 * width) + 2 * width) width)

theorem rightWords3_length {start width : Nat} (bits : Vector (Fin start) width) :
    (rightWords3 bits).length = 3 := by simp [rightWords3]

attribute [local irreducible] positiveWords negativeWords incrementStep complementStep

theorem suffix3_wellFormed (n start width : Nat) (bits : Vector (Fin start) width) :
    (suffix3 n start width bits).WellFormed := by
  unfold suffix3
  rw [castFinish_wellFormed]
  apply straight_append_wellFormed _ _ (constantStep_wellFormed _ _)
  apply straight_append_wellFormed _ _ (positiveWords_wellFormed _ _ _ _ _)
  exact straight_append_wellFormed _ _ (complementStep_wellFormed _ _)
    (negativeWords_wellFormed _ _ _ _ _)

theorem suffix3_slots (n start width : Nat) (bits : Vector (Fin start) width) :
    (suffix3 n start width bits).gateSlots = 7 + 28 * width := by
  simp only [suffix3, castFinish_gateSlots, Straight.gateSlots_append,
    constantStep_slots, positiveWords_slots, complementStep_slots, negativeWords_slots]
  ring

theorem suffix3_t (n start width : Nat) (bits : Vector (Fin start) width)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((suffix3 n start width bits).instantiate read history).tCount = 0 := by
  unfold suffix3
  rw [castFinish_instantiate]
  apply Readout56.append_t_zero _ _ read (constantStep_t _ _ _)
  intro h
  apply Readout56.append_t_zero _ _ read (positiveWords_t _ _ _ _ _ _)
  intro h
  exact Readout56.append_t_zero _ _ read (complementStep_t _ _ _)
    (negativeWords_t _ _ _ _ _ _) h

theorem suffix3_support (n start width : Nat) (bits : Vector (Fin start) width)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((suffix3 n start width bits).instantiate read history).wires ⊆ [0, 1] := by
  unfold suffix3
  rw [castFinish_instantiate]
  apply outer_append_support _ _ read history ([0, 1] : List Wire) (constantStep_support _ _ _ _)
  intro h
  apply outer_append_support _ _ read h ([0, 1] : List Wire) (positiveWords_support _ _ _ _ _ _ _)
  intro h
  exact outer_append_support _ _ read h ([0, 1] : List Wire) (complementStep_support _ _ _ _)
    (fun hh => negativeWords_support _ _ _ _ _ _ hh)

theorem weight4_suffix3 (n start width : Nat) (bits : Vector (Fin start) width) :
    ConditionalCatalyst.weight4 (suffix3 n start width bits) = 0 := by
  simp [suffix3, ConditionalCatalyst.weight4_cast, ConditionalCatalyst.weight4_append,
    ConditionalCatalyst.weight4_positive, ConditionalCatalyst.weight4_negative,
    ConditionalCatalyst.weight4_complement]
  rfl

theorem residue_suffix3 (n start width : Nat) (bits : Vector (Fin start) width) :
    AndGadget.residue (suffix3 n start width bits) = 0 := by
  simp [suffix3, AndGadget.residue_cast, AndGadget.residue_append,
    ApproximatePhase34.residue_positive, ApproximatePhase34.residue_negative,
    ApproximatePhase34.residue_complement]
  rfl

/-- Every nonzero readout branch writes all 3 neighbouring 204-bit residues explicitly. -/
theorem suffix3_branch (n start : Nat) (bits : Vector (Fin start) 204)
    (read : ConstantBit n → Bool) (history : Fin start → Bool)
    (ψ : State) (hψ : SupportedOn CleanReadout ψ) (b : InstrumentBranch)
    (hb : b ∈ ((suffix3 n start 204 bits).instantiate read history).run)
    (hn : b.kraus ψ ≠ 0) :
    b.kraus ψ = ψ ∧
      (∀ i : Fin 1, readWord (List.ofFn history ++ b.history)
        (sumPositions (start + 2 + i.val * 408) 204).toList =
        some ((i.val + 1 + inputValue bits history) % 2^204)) ∧
      (∀ i : Fin 1, readWord (List.ofFn history ++ b.history)
        (sumPositions (start + 2 + 408 + 408 + i.val * 816 + 408) 204).toList =
        some (2^204 - 1 - ((i.val + 1 + (2^204 - 1 - inputValue bits history)) % 2^204))) := by
  unfold suffix3 at hb
  rw [castFinish_instantiate] at hb
  obtain ⟨h₁, a, u, ha, hu, he₁, rfl⟩ := straight_append_branch _ _ read history b hb
  have han : a.kraus ψ ≠ 0 := by
    intro h; apply hn; simp only [InstrumentBranch.seq, LinearMap.comp_apply, h, map_zero]
  have hc := constantStep_branch n start read history ψ hψ a ha han
  have hun : u.kraus ψ ≠ 0 := by
    simpa only [InstrumentBranch.seq, LinearMap.comp_apply, hc.1] using hn
  have hcarr := initial_carry bits history h₁ (he₁.trans (by rw [hc.2]))
  have hval := initial_value bits history h₁ a.history he₁
  obtain ⟨h₂, p, v, hp, hv, he₂, rfl⟩ := straight_append_branch _ _ read h₁ u hu
  have hpn : p.kraus ψ ≠ 0 := by
    intro h; apply hun; simp only [InstrumentBranch.seq, LinearMap.comp_apply, h, map_zero]
  have hpos := positiveWords_branch n 1 (start + 2) 204 (initialCursor bits)
    read h₁ hcarr ψ hψ p hp hpn
  have hvn : v.kraus ψ ≠ 0 := by
    simpa only [InstrumentBranch.seq, LinearMap.comp_apply, hpos.1] using hun
  let q := (initialCursor bits).lift (1 * (2 * 204))
  have hqc : h₂ q.carry = true := (lift_carry (initialCursor bits) _ h₁ h₂ p.history he₂).trans hcarr
  have hqv : cursorValue q h₂ = inputValue bits history :=
    (lift_value (initialCursor bits) _ h₁ h₂ p.history he₂).trans hval
  obtain ⟨h₃, c, t, hc', ht, he₃, rfl⟩ := straight_append_branch _ _ read h₂ v hv
  have hcn : c.kraus ψ ≠ 0 := by
    intro h; apply hvn; simp only [InstrumentBranch.seq, LinearMap.comp_apply, h, map_zero]
  have hcomp := complementStep_post n q read h₂ hqc ψ hψ c hc' hcn h₃ he₃
  have htn : t.kraus ψ ≠ 0 := by
    simpa only [InstrumentBranch.seq, LinearMap.comp_apply, hcomp.1] using hvn
  have hneg := negativeWords_branch n 1 (start + 2 + 1 * (2 * 204) + 2 * 204) 204 q.next
    read h₃ hcomp.2.1 ψ hψ t ht htn
  have hfull₁ : List.ofFn history ++ (a.seq (p.seq (c.seq t))).history =
      List.ofFn h₁ ++ (p.seq (c.seq t)).history := by
    rw [he₁]; simp only [InstrumentBranch.seq, List.append_assoc]
  have hfull₂ : List.ofFn history ++ (a.seq (p.seq (c.seq t))).history =
      List.ofFn h₂ ++ (c.seq t).history := by
    rw [hfull₁, he₂]; simp only [InstrumentBranch.seq, List.append_assoc]
  have hfull₃ : List.ofFn history ++ (a.seq (p.seq (c.seq t))).history =
      List.ofFn h₃ ++ t.history := by
    rw [hfull₂, he₃]; simp only [InstrumentBranch.seq, List.append_assoc]
  refine ⟨by simp only [InstrumentBranch.seq, LinearMap.comp_apply, hc.1, hpos.1, hcomp.1, hneg.1], ?_, ?_⟩
  · intro i
    rw [hfull₂, readWord_append_left (List.ofFn h₂) (c.seq t).history _ (by
      intro j hj
      have hj' := sumPositions_bound (start + 2 + i.val * 408) 204 j hj
      have hi := i.isLt
      simp only [List.length_ofFn]
      omega), he₂]
    simpa only [hval] using hpos.2 i
  · intro i
    rw [hfull₃]
    simpa only [hcomp.2.2, hqv] using hneg.2 i

theorem positive_word_mod204 (b i : Nat) :
    (i + b) % 2^204 = ((((b : Nat) : ℤ) + (i : ℤ)) % (2^204 : Nat)).toNat := by
  omega

theorem negative_word_mod204 (b i : Nat) (hb : b < 2^204) :
    2^204 - 1 - (i + (2^204 - 1 - b)) % 2^204 =
      ((((b : Nat) : ℤ) - (i : ℤ)) % (2^204 : Nat)).toNat := by
  omega

/-- The physical word list contains a correct explicit record for every offset `-1, 0, +1`. -/
theorem suffix3_reads (n start : Nat) (bits : Vector (Fin start) 204)
    (read : ConstantBit n → Bool) (history : Fin start → Bool)
    (ψ : State) (hψ : SupportedOn CleanReadout ψ) (b : InstrumentBranch)
    (hb : b ∈ ((suffix3 n start 204 bits).instantiate read history).run)
    (hn : b.kraus ψ ≠ 0) (j : ℤ) (hj : -1 ≤ j ∧ j ≤ 1) :
    ∃ ps ∈ rightWords3 bits, readWord (List.ofFn history ++ b.history) ps.toList =
      some ((((inputValue bits history : Nat) : ℤ) + j) % (2^204 : Nat)).toNat := by
  have hs := suffix3_branch n start bits read history ψ hψ b hb hn
  by_cases hz : j = 0
  · subst j
    refine ⟨bits.map Fin.val, by simp [rightWords3], ?_⟩
    rw [readWord_append_left (List.ofFn history) b.history _ (by
      intro i hi
      simp only [Vector.toList_map, List.mem_map] at hi
      obtain ⟨k, _, rfl⟩ := hi
      simpa only [List.length_ofFn] using k.isLt), input_read]
    congr 1
    simpa only [Nat.zero_add, Int.natCast_zero, Nat.mod_eq_of_lt (input_lt bits history)] using
      (positive_word_mod204 (inputValue bits history) 0)
  · by_cases hp : 0 < j
    · let i : Fin 1 := ⟨0, by omega⟩
      have hi : (i.val + 1 : ℤ) = j := by dsimp [i]; omega
      refine ⟨sumPositions (start + 2 + i.val * 408) 204, ?_, ?_⟩
      · unfold rightWords3
        apply List.mem_cons_of_mem
        apply List.mem_append_left
        exact List.mem_ofFn.mpr ⟨i, rfl⟩
      · rw [hs.2.1 i, positive_word_mod204]
        congr 2
        exact congrArg (fun z : ℤ => (((inputValue bits history : Nat) : ℤ) + z) % (2^204 : Nat)) hi
    · let i : Fin 1 := ⟨0, by omega⟩
      have hi : -((i.val + 1 : Nat) : ℤ) = j := by dsimp [i]; omega
      refine ⟨sumPositions (start + 2 + 408 + 408 + i.val * 816 + 408) 204, ?_, ?_⟩
      · unfold rightWords3
        apply List.mem_cons_of_mem
        apply List.mem_append_right
        exact List.mem_ofFn.mpr ⟨i, rfl⟩
      · rw [hs.2.2 i, negative_word_mod204 _ _ (input_lt bits history)]
        congr 2
        rw [sub_eq_add_neg, hi]

#print axioms suffix3_reads

end
end ShorECDLP.Entrant.Readout3
end

/-! ### Consolidated from `ComplementLoss.lean` -/
section
namespace ShorECDLP.Entrant.ComplementLoss
open Quantum Challenge AndGadget ApproximatePhase34 WeightedPhase28
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

theorem mass_upper (psi phi : State) (eps : ℝ) :
    eps*normSq (psi+phi) ≤ (eps+eps^2)*normSq psi + (1+eps)*normSq phi := by
  classical
  let S := psi.support ∪ phi.support
  have ha : (psi+phi).support ⊆ S := Finsupp.support_add
  rw [mass_on psi S Finset.subset_union_left,mass_on phi S Finset.subset_union_right,
    mass_on (psi+phi) S ha]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro s _
  simp only [Finsupp.add_apply,Complex.normSq_apply,Complex.add_re,Complex.add_im]
  nlinarith [sq_nonneg (eps*(psi s).re-(phi s).re),sq_nonneg (eps*(psi s).im-(phi s).im)]

theorem expectation_upper {n s e} (read : ConstantBit n → Bool)
    (p : Straight n s e) (history : Fin s → Bool) (psi phi : State)
    (accept : (Fin e → Bool) → Bool) (eps : ℝ) :
    eps*expectation read p history (psi+phi) accept ≤
    (eps+eps^2)*expectation read p history psi accept +
      (1+eps)*expectation read p history phi accept := by
  induction p generalizing psi phi with
  | done =>
    simp only [expectation]
    split_ifs
    · exact mass_upper psi phi eps
    · simp
  | gate g p ih =>
    simpa only [expectation,map_add] using ih history
      (Quantum.run (g.instantiate read) psi) (Quantum.run (g.instantiate read) phi) accept
  | recordGate i v g p ih =>
    simpa only [expectation,map_add] using ih history
      (Quantum.run (if history i=v then [g] else []) psi)
      (Quantum.run (if history i=v then [g] else []) phi) accept
  | measure w p ih =>
    have h0 := ih (Fin.lastCases false history) (xResetKraus w false psi) (xResetKraus w false phi) accept
    have h1 := ih (Fin.lastCases true history) (xResetKraus w true psi) (xResetKraus w true phi) accept
    simp only [expectation,map_add]
    linarith

theorem expectation_neg {n s e} (read : ConstantBit n → Bool)
    (p : Straight n s e) (history : Fin s → Bool) (psi : State)
    (accept : (Fin e → Bool) → Bool) :
    expectation read p history (-psi) accept = expectation read p history psi accept := by
  induction p generalizing psi with
  | done => simp [expectation]
  | gate g p ih => simp only [expectation,map_neg,ih]
  | recordGate i v g p ih => simp only [expectation,map_neg,ih]
  | measure w p ih => simp only [expectation,map_neg,ih]

theorem expectation_compl {n s e} (read : ConstantBit n → Bool)
    (p : Straight n s e) (history : Fin s → Bool) (psi : State)
    (accept : (Fin e → Bool) → Bool) (hp : p.WellFormed) :
    expectation read p history psi accept +
      expectation read p history psi (fun h => !accept h) = normSq psi := by
  induction p generalizing psi with
  | done => cases ha : accept history <;> simp [expectation,ha]
  | gate g p ih =>
    simp only [expectation]
    rw [ih _ _ accept hp.2]
    exact normSq_run _ (g.instantiate_wellFormed read hp.1) psi
  | recordGate i v g p ih =>
    simp only [expectation]
    rw [ih _ _ accept hp.2]
    apply normSq_run
    split_ifs
    · simpa [CircuitWellFormed] using hp.1
    · simp [CircuitWellFormed]
  | measure w p ih =>
    have h0 := ih (Fin.lastCases false history) (xResetKraus w false psi) accept hp
    have h1 := ih (Fin.lastCases true history) (xResetKraus w true psi) accept hp
    have hm := normSq_xResetKraus_false_add_true w psi
    simp only [expectation]
    linarith

theorem loss {n s e} (read : ConstantBit n → Bool)
    (p : Straight n s e) (history : Fin s → Bool) (psi phi : State)
    (accept : (Fin e → Bool) → Bool) (hp : p.WellFormed)
    (delta : ℝ) (hd : 0 < delta) (hn : normSq phi = normSq psi)
    (he : normSq (phi-psi) ≤ delta^2*normSq psi) :
    expectation read p history phi accept ≤ expectation read p history psi accept + delta*normSq psi := by
  have hA := expectation_upper read p history psi (phi-psi) accept delta
  have hB := expectation_upper read p history phi (psi-phi) (fun h => !accept h) delta
  have hsumA : psi+(phi-psi)=phi := by abel
  have hsumB : phi+(psi-phi)=psi := by abel
  rw [hsumA] at hA
  rw [hsumB] at hB
  have hphi := expectation_compl read p history phi accept hp
  have hpsi := expectation_compl read p history psi accept hp
  rw [hn] at hphi
  have hdiff := expectation_compl read p history (phi-psi) accept hp
  have hneg : psi-phi = -(phi-psi) := by abel
  rw [hneg,expectation_neg] at hB
  have hscaled := mul_le_mul_of_nonneg_left he (show 0 ≤ 1+delta by positivity)
  have hprod : (delta*(2+delta)) * (expectation read p history phi accept - expectation read p history psi accept) ≤
      (delta*(2+delta)) * (delta*normSq psi) := by nlinarith
  have hpos : 0 < delta*(2+delta) := by positivity
  have hle := (mul_le_mul_iff_right₀ hpos).mp hprod
  linarith
theorem phase_loss {n s e} (read : ConstantBit n → Bool)
    (p : Straight n s e) (history : Fin s → Bool) (psi : State)
    (accept : (Fin e → Bool) → Bool) (hp : p.WellFormed)
    (dir : PhaseDir) (k : Nat) (t : Wire) (delta : ℝ) (hd : 0 < delta)
    (ha : (phaseAngle dir k/2)^2 ≤ delta^2) :
    expectation read p history (applyGate (.P dir k t) psi) accept ≤
      expectation read p history psi accept + delta*normSq psi := by
  have hw : Complex.normSq (Complex.exp (Complex.I * ((-(phaseAngle dir k/2) : ℝ) : ℂ))) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]
    simp
  let phi := Complex.exp (Complex.I * ((-(phaseAngle dir k/2) : ℝ) : ℂ)) • applyGate (.P dir k t) psi
  have hphi : expectation read p history phi accept =
      expectation read p history (applyGate (.P dir k t) psi) accept := by
    simp only [phi, AndGadget.expectation_smul, hw, one_mul]
  have hn : normSq phi = normSq psi := by
    simp only [phi, centered_smul_mass, hw, one_mul]
    exact applyGate_preservesNormSq _ (by trivial) psi
  rw [← hphi]
  have hdiff : normSq (phi-psi) ≤ delta^2 * normSq psi :=
    (phase_centered_mass dir k t psi).trans
      (mul_le_mul_of_nonneg_right ha (mass_nonneg psi))
  exact loss read p history psi phi accept hp delta hd hn hdiff

theorem dropped_loss {n s e} (read : ConstantBit n → Bool) (p : Straight n s e)
    (history : Fin s → Bool) (psi : State) (accept : (Fin e → Bool) → Bool)
    (hp : p.WellFormed) (g : Gate) (hg : largePhase 27 g = true) :
    expectation read p history (applyGate g psi) accept ≤
      expectation read p history psi accept + charge g*normSq psi := by
  cases g <;> simp only [largePhase, Bool.false_eq_true, decide_eq_true_eq] at hg
  case P dir k t =>
    have hd : 0 < (6283186/1000000:ℝ)/(2:ℝ)^(k+1) := by positivity
    have hangle : (phaseAngle dir k/2)^2 ≤ ((6283186/1000000:ℝ)/(2:ℝ)^(k+1))^2 := by
      have hpi := Real.pi_lt_d6
      have hb : 2*Real.pi/(2:ℝ)^k/2 ≤ (6283186/1000000:ℝ)/(2:ℝ)^(k+1) := by
        rw [pow_succ, div_div]
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith
      have hz : 0 ≤ 2*Real.pi/(2:ℝ)^k/2 := by positivity
      cases dir <;> simp only [phaseAngle, neg_div, neg_sq] <;> nlinarith
    simpa only [charge, hg, if_true] using
      phase_loss read p history psi accept hp dir k t _ hd hangle

theorem dropped_loss27 {n s e} (read : ConstantBit n → Bool) (p : Straight n s e)
    (history : Fin s → Bool) (psi : State) (accept : (Fin e → Bool) → Bool)
    (hp : p.WellFormed) (g : ShorECDLP.Gate) (hg : largePhase 26 g = true)
    (hg27 : largePhase 27 g = false) :
    expectation read p history (applyGate g psi) accept ≤
      expectation read p history psi accept + unit*normSq psi := by
  cases g <;> simp only [largePhase, Bool.false_eq_true] at hg hg27
  case P dir k t =>
    have h1 : 26 < k := by simpa using hg
    have h2 : ¬ 27 < k := by simpa using hg27
    have hk : k = 27 := by omega
    subst hk
    have hd : 0 < (6283186/1000000:ℝ)/(2)^28 := by positivity
    have hangle : (phaseAngle dir (27:Nat)/2)^2 ≤ ((6283186/1000000:ℝ)/(2)^28)^2 := by
      have hpi := Real.pi_lt_d6
      have hb : 2*Real.pi/(2:ℝ)^27/2 ≤ (6283186/1000000:ℝ)/(2)^28 := by
        rw [pow_succ, div_div]
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith
      have hz : 0 ≤ 2*Real.pi/(2:ℝ)^27/2 := by positivity
      cases dir <;> simp only [phaseAngle, neg_div, neg_sq] <;> nlinarith
    have hunit : (6283186/1000000:ℝ)/(2)^28 = unit := rfl
    simpa only [hunit] using
      phase_loss read p history psi accept hp dir (27:Nat) t _ hd hangle

theorem trimN_expectation {n s e} (read : ConstantBit n → Bool)
    (p : Straight n s e) (N : Nat) (history : Fin s → Bool) (psi : State)
    (accept : (Fin e → Bool) → Bool) (hp : p.WellFormed) :
    expectation read p history psi accept ≤
      expectation read (trimN N p) history psi accept +
      (errorCost p + N*unit)*normSq psi := by
  induction p generalizing psi N with
  | done =>
    have hu : (0:ℝ) ≤ unit := by simp only [unit]; positivity
    have hN : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
    have hpsi : (0:ℝ) ≤ normSq psi := mass_nonneg psi
    have hprod : (0:ℝ) ≤ (↑N*unit)*normSq psi :=
      mul_nonneg (mul_nonneg hN hu) hpsi
    simp [trimN, errorCost, expectation]
    exact hprod
  | measure w p ih =>
    have h0 := ih N (Fin.lastCases false history) (xResetKraus w false psi) accept hp
    have h1 := ih N (Fin.lastCases true history) (xResetKraus w true psi) accept hp
    have hm := normSq_xResetKraus_false_add_true w psi
    have hme := congrArg (fun x : ℝ => (errorCost p + N*unit)*x) hm
    simp only [trimN, errorCost, expectation]
    nlinarith
  | recordGate i v g p ih =>
    by_cases h27 : largePhase 27 g = true
    · have hi := ih N history psi accept hp.2
      have hs := dropped_loss read p history psi accept hp.2 g h27
      simp only [trimN, h27, if_true, errorCost, expectation]
      by_cases hr : history i = v
      · simp only [hr, if_true, run_singleton]
        nlinarith
      · simp only [hr, if_false, run_nil, LinearMap.id_coe, id_eq]
        have hsq : (0:ℝ) ≤ normSq psi := mass_nonneg psi
        have hu2 : (0:ℝ) ≤ unit := by simp only [unit]; positivity
        have hn := mul_nonneg (charge_nonneg g) (mass_nonneg psi)
        nlinarith
    · have h27f : largePhase 27 g = false := Bool.eq_false_iff.mpr h27
      by_cases hN : (decide (N > 0) && largePhase 26 g) = true
      · have hg26 : largePhase 26 g = true := by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hN
          exact hN.2
        have hs := dropped_loss27 read p history psi accept hp.2 g hg26 h27f
        have hi := ih (N - 1) history psi accept hp.2
        have hc0 : charge g = 0 := charge_false g h27f
        have hNpos : 0 < N := by
          have h := hN
          simp at h
          exact h.1
        have hcast : ((N - 1 : Nat) : ℝ) = (N:ℝ) - 1 := Nat.cast_pred hNpos
        simp only [hcast] at hi
        simp only [trimN, h27f, Bool.false_eq_true, if_false, hN, if_true,
          errorCost, hc0, zero_add, expectation]
        by_cases hr : history i = v
        · simp only [hr, if_true, run_singleton]
          nlinarith
        · simp only [hr, if_false, run_nil, LinearMap.id_coe, id_eq]
          have hsq : (0:ℝ) ≤ normSq psi := mass_nonneg psi
          have hu2 : (0:ℝ) ≤ unit := by simp only [unit]; positivity
          have hn := mul_nonneg (charge_nonneg g) (mass_nonneg psi)
          nlinarith
      · have hNf : (decide (N > 0) && largePhase 26 g) = false :=
          Bool.eq_false_iff.mpr hN
        have hi := ih N history (run (if history i=v then [g] else []) psi)
          accept hp.2
        have hc0 : charge g = 0 := charge_false g h27f
        have hn : normSq (run (if history i=v then [g] else []) psi) = normSq psi := by
          apply normSq_run
          split_ifs
          · simpa [ShorECDLP.CircuitWellFormed] using hp.1
          · simp [ShorECDLP.CircuitWellFormed]
        rw [hn] at hi
        simp only [trimN, h27f, if_false, hNf, if_false, errorCost, hc0,
          zero_add, expectation]
        exact hi
  | gate g p ih =>
    cases g with
    | literal g =>
      by_cases h27 : largePhase 27 g = true
      · have hs := dropped_loss read p history psi accept hp.2 g h27
        have hi := ih N history psi accept hp.2
        simp only [trimN, h27, if_true, errorCost, expectation,
          TemplateGate.instantiate, run_singleton]
        nlinarith
      · have h27f : largePhase 27 g = false := Bool.eq_false_iff.mpr h27
        by_cases hN : (decide (N > 0) && largePhase 26 g) = true
        · have hg26 : largePhase 26 g = true := by
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hN
            exact hN.2
          have hs := dropped_loss27 read p history psi accept hp.2 g hg26 h27f
          have hi := ih (N - 1) history psi accept hp.2
          have hc0 : charge g = 0 := charge_false g h27f
          have hNpos : 0 < N := by
            have h := hN
            simp at h
            exact h.1
          have hcast : ((N - 1 : Nat) : ℝ) = (N:ℝ) - 1 := Nat.cast_pred hNpos
          simp only [hcast] at hi
          simp only [trimN, h27f, Bool.false_eq_true, if_false, hN, if_true,
            errorCost, hc0, zero_add, expectation, TemplateGate.instantiate,
            run_singleton]
          nlinarith
        · have hNf : (decide (N > 0) && largePhase 26 g) = false :=
            Bool.eq_false_iff.mpr hN
          have hi := ih N history (applyGate g psi) accept hp.2
          rw [normSq_gate g hp.1 psi] at hi
          have hc0 : charge g = 0 := charge_false g h27f
          simp only [trimN, h27f, if_false, hNf, if_false, errorCost, hc0,
            zero_add, expectation, TemplateGate.instantiate, run_singleton]
          exact hi
    | whenBit r v g =>
      by_cases h27 : largePhase 27 g = true
      · have hi := ih N history psi accept hp.2
        have hs := dropped_loss read p history psi accept hp.2 g h27
        simp only [trimN, h27, if_true, errorCost, expectation, TemplateGate.instantiate]
        by_cases hr : read r = v
        · simp only [hr, if_true, run_singleton]
          nlinarith
        · simp only [hr, if_false, run_nil, LinearMap.id_coe, id_eq]
          have hsq : (0:ℝ) ≤ normSq psi := mass_nonneg psi
          have hu2 : (0:ℝ) ≤ unit := by simp only [unit]; positivity
          have hn := mul_nonneg (charge_nonneg g) (mass_nonneg psi)
          nlinarith
      · have h27f : largePhase 27 g = false := Bool.eq_false_iff.mpr h27
        by_cases hN : (decide (N > 0) && largePhase 26 g) = true
        · have hg26 : largePhase 26 g = true := by
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hN
            exact hN.2
          have hs := dropped_loss27 read p history psi accept hp.2 g hg26 h27f
          have hi := ih (N - 1) history psi accept hp.2
          have hc0 : charge g = 0 := charge_false g h27f
          have hNpos : 0 < N := by
            have h := hN
            simp at h
            exact h.1
          have hcast : ((N - 1 : Nat) : ℝ) = (N:ℝ) - 1 := Nat.cast_pred hNpos
          simp only [hcast] at hi
          simp only [trimN, h27f, Bool.false_eq_true, if_false, hN, if_true,
            errorCost, hc0, zero_add, expectation, TemplateGate.instantiate]
          by_cases hr : read r = v
          · simp only [hr, if_true, run_singleton]
            nlinarith
          · simp only [hr, if_false, run_nil, LinearMap.id_coe, id_eq]
            have hsq : (0:ℝ) ≤ normSq psi := mass_nonneg psi
            have hu2 : (0:ℝ) ≤ unit := by simp only [unit]; positivity
            have hn := mul_nonneg (charge_nonneg g) (mass_nonneg psi)
            nlinarith
        · have hNf : (decide (N > 0) && largePhase 26 g) = false :=
            Bool.eq_false_iff.mpr hN
          have hi := ih N history (run ((TemplateGate.whenBit r v g).instantiate read) psi)
            accept hp.2
          rw [normSq_template read (.whenBit r v g) hp.1 psi] at hi
          have hc0 : charge g = 0 := charge_false g h27f
          simp only [trimN, h27f, if_false, hNf, if_false, errorCost, hc0,
            zero_add, expectation]
          exact hi


theorem affine_loss {n s e} (read : ConstantBit n → Bool)
    (p : Straight n s e) (history : Fin s → Bool) (psi phi : State)
    (accept : (Fin e → Bool) → Bool) (hp : p.WellFormed)
    (delta : ℝ) (hd : 0 < delta)
    (he : normSq (phi-psi) ≤ delta^2*normSq psi) :
    expectation read p history phi accept ≤
      (1+10*delta)*expectation read p history psi accept +
        (delta/10+delta^2)*normSq psi := by
  have h := expectation_upper read p history psi (phi-psi) accept (10*delta)
  have hs : psi+(phi-psi)=phi := by abel
  rw [hs] at h
  have hu := expectation_le_mass read p history (phi-psi) accept hp
  have hm := mul_le_mul_of_nonneg_left (hu.trans he) (show 0 ≤ 1+10*delta by positivity)
  have hh : 10*delta * expectation read p history phi accept ≤
      10*delta*((1+10*delta)*expectation read p history psi accept +
        (delta/10+delta^2)*normSq psi) := by nlinarith
  exact (mul_le_mul_iff_right₀ (show 0<10*delta by positivity)).mp hh

theorem phase_affine {n s e} (read : ConstantBit n → Bool)
    (p : Straight n s e) (history : Fin s → Bool) (psi : State)
    (accept : (Fin e → Bool) → Bool) (hp : p.WellFormed)
    (dir : PhaseDir) (k : Nat) (t : Wire) (delta : ℝ) (hd : 0 < delta)
    (ha : (phaseAngle dir k/2)^2 ≤ delta^2) :
    expectation read p history psi accept ≤
      (1+10*delta)*expectation read p history (applyGate (.P dir k t) psi) accept +
        (delta/10+delta^2)*normSq psi := by
  have hw : Complex.normSq (Complex.exp (Complex.I * ((-(phaseAngle dir k/2) : ℝ) : ℂ))) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]
    simp
  let phi := Complex.exp (Complex.I * ((-(phaseAngle dir k/2) : ℝ) : ℂ)) • applyGate (.P dir k t) psi
  have hphi : expectation read p history phi accept =
      expectation read p history (applyGate (.P dir k t) psi) accept := by
    simp only [phi, AndGadget.expectation_smul, hw, one_mul]
  have hn : normSq phi = normSq psi := by
    simp only [phi, centered_smul_mass, hw, one_mul]
    exact applyGate_preservesNormSq _ (by trivial) psi
  have hdiff : normSq (psi-phi) ≤ delta^2 * normSq phi := by
    rw [hn]
    have hneg : psi-phi = -(phi-psi) := by abel
    rw [hneg, normSq_neg]
    exact (phase_centered_mass dir k t psi).trans
      (mul_le_mul_of_nonneg_right ha (mass_nonneg psi))
  simpa only [hphi,hn] using affine_loss read p history phi psi accept hp delta hd hdiff

theorem expectation_nonneg {n s e} (read : ConstantBit n → Bool)
    (p : Straight n s e) (history : Fin s → Bool) (psi : State)
    (accept : (Fin e → Bool) → Bool) : 0 ≤ expectation read p history psi accept := by
  induction p generalizing psi with
  | done => simp only [expectation]; split_ifs; exact mass_nonneg psi; rfl
  | gate g p ih => exact ih history _ accept
  | recordGate i v g p ih => exact ih history _ accept
  | measure w p ih => exact add_nonneg (ih _ _ accept) (ih _ _ accept)

theorem idle_affine (d E M : ℝ) (hd : 0≤d) (hE : 0≤E) (hM : 0≤M) :
    E ≤ (1+10*d)*E+(d/10+d^2)*M := by
  nlinarith [mul_nonneg hd hE,mul_nonneg (show 0≤d/10+d^2 by positivity) hM]

#print axioms trimN_expectation
end
end ShorECDLP.Entrant.ComplementLoss
end

/-! ### Consolidated from `SineCircuit.lean` -/
section
/-! Centered 10-bit sine window state preparation circuit (`sineFromPlus`) and exact
semiclassical QPE + character-expansion bridge (`windowedEventMass_distribution`).

Given `ws` (10 wires, LSB-first) already in `|+⟩^{⊗10}` via `prepareOuterBank`,
`sineFromPlus ws` transforms `|+⟩^{⊗10}` into:
  `2^{-5} ∑_{u < 1024} sineWeight 10 u |u⟩`
where `sineWeight h u = (√2)⁻¹ (e^{iπ u / 2^h} - e^{-iπ u / 2^h}) = i √2 sin(π u / 2^h)`.

Cost per axis: 52 gate slots, 0 CCXs (`added = 0`), 28 non-Clifford T-model phase gates
(`weight4 = 28`, with 2 catalyzed `k = 2` S-gates), all phase depths `k ≤ 11` (untouched by
phase trimming `cutoff ≥ 11`), zero extra qubits (`circuitWires ⊆ ws`). -/


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
end

/-! ### Consolidated from `SineBounds.lean` -/
section
/-! Analytical success probability lower bound (`≥ 9911 / 10000`) for the 10-bit centered sine
window at precisions `(L, R) = (258, 204)` with `K = 3` neighbouring right shifts `{-1, 0, +1}`.

Structure:
1. Discrete Parseval (`dft_parseval`) → exact unit mass `sinePhaseAmplitude_parseval`.
2. Factorization `sinePhaseAmplitude M β a = N⁻¹ * W(ω^B) * G(B, ω)` →
   - Far tail (`512 < phiR ∧ 512 < phiL`): `≤ 12 / 1000000` via 1024-point Parseval on first differences.
   - Closed form & small/medium pointwise bounds on `3/2 ≤ φ ≤ 512`:
     `small (≤ 17): ≤ (508/10000) * cos²(πNβ) / (φ² - 1/4)²`
     `medium (16..512): ≤ (31/100) * cos²(πNβ) / (φ - 1/2)⁴`, summing over both sides to `≤ (68/1000000) * cos²(πNβ)`.
3. Elementary box bounds in `|σ| ∈ [0, 1/2]` using rational `smallSumQ` and `cos x ≤ min(1 - x²/2 + x⁴/24, π/2 - x)`:
   - Left axis (`258` bits, `4 * order < 2^258`): `miss_L ≤ (586/100000) * cos²(πNβ) + 12/1000000`.
   - Right axis (`204` bits, `3` shifts `-1, 0, +1`): `miss_R ≤ 136/100000 + (900/100000) * cos²(πNβ) + 12/1000000`.
4. Exact character average `∑_{k : Fin r} cos²(π M k / r) = r / 2` for `r` prime, `r ∤ M` →
   `sine_pair_success` (`≥ 9911 / 10000`) and `decoder_budget258`. -/


namespace ShorECDLP.Entrant.SineBounds
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Entrant.SineCircuit ShorECDLP.Entrant.WindowMassSharpProof
open ShorECDLP.Entrant.NeighborReadout ShorECDLP.Entrant.SinAverage ShorECDLP.Entrant.SinAverage261
open ShorECDLP.Paper2607_13816 ShorECDLP.Quantum.OrderFinding ShorECDLP.Quantum.PhaseEstimation
open Finset
open scoped BigOperators
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
set_option exponentiation.threshold 300
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

/-! ### Part 1: Elementary trig & DFT Parseval -/

theorem eigenvalue_normSq (θ : ℝ) : Complex.normSq (eigenvalue θ) = 1 := by
  unfold eigenvalue
  rw [Complex.normSq_eq_norm_sq, show Complex.I * ((2 * Real.pi * θ : ℝ) : ℂ) =
    ((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I by ring, Complex.norm_exp_ofReal_mul_I, one_pow]

theorem eigenvalue_int (m : ℤ) : eigenvalue (m : ℝ) = 1 := by
  unfold eigenvalue
  rw [show Complex.I * ((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) = (m : ℂ) * (2 * Real.pi * Complex.I) by
    push_cast; ring, Complex.exp_int_mul_two_pi_mul_I]

theorem eigenvalue_add_int (θ : ℝ) (m : ℤ) : eigenvalue (θ + m) = eigenvalue θ := by
  rw [eigenvalue_add, eigenvalue_int, mul_one]

theorem eigenvalue_sub_int (θ : ℝ) (m : ℤ) : eigenvalue (θ - m) = eigenvalue θ := by
  simpa [sub_eq_add_neg] using eigenvalue_add_int θ (-m)

theorem normSq_eigenvalue_sub_one (θ : ℝ) :
    Complex.normSq (eigenvalue θ - 1) = 4 * Real.sin (Real.pi * θ) ^ 2 := by
  unfold eigenvalue
  rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, show |(2 : ℝ)| = 2 by norm_num,
    show 2 * Real.pi * θ / 2 = Real.pi * θ by ring, mul_pow, sq_abs]
  norm_num

theorem normSq_eigenvalue_add_one (θ : ℝ) :
    Complex.normSq (eigenvalue θ + 1) = 4 * Real.cos (Real.pi * θ) ^ 2 := by
  have h1 : eigenvalue θ + 1 = -(eigenvalue (θ - 1/2) - 1) := by
    have hhalf : eigenvalue (-(1/2 : ℝ)) = -1 := by
      unfold eigenvalue
      have : Complex.I * ((2 * Real.pi * (-(1/2 : ℝ)) : ℝ) : ℂ) = -((Real.pi : ℂ) * Complex.I) := by
        push_cast; ring
      rw [this, Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num
    have hsub : eigenvalue (θ - 1/2) = -eigenvalue θ := by
      rw [sub_eq_add_neg, eigenvalue_add, hhalf]; ring
    rw [hsub]; ring
  rw [h1, Complex.normSq_neg, normSq_eigenvalue_sub_one]
  have hs : Real.sin (Real.pi * (θ - 1/2)) = -Real.cos (Real.pi * θ) := by
    rw [show Real.pi * (θ - 1/2) = Real.pi * θ - Real.pi / 2 by ring, Real.sin_sub_pi_div_two]
  rw [hs, neg_sq]

theorem sin_jordan (u : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ 1/2) :
    2 * u ≤ Real.sin (Real.pi * u) := by
  have hx0 : 0 ≤ Real.pi * u := mul_nonneg Real.pi_pos.le hu0
  have hx : Real.pi * u ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
  have h := Real.mul_le_sin hx0 hx
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have he : 2 / Real.pi * (Real.pi * u) = 2 * u := by field_simp [hpi.ne']
  linarith

theorem cos_le_taylor4 (x : ℝ) (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  let f : ℝ → ℝ := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t
  have hderiv : ∀ t : ℝ, HasDerivAt f (Real.sin t - t + t ^ 3 / 6) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => (1 : ℝ) - s ^ 2 / 2 + s ^ 4 / 24) (-t + t ^ 3 / 6) t := by
      have ha : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 t := hasDerivAt_const t 1
      have hb : HasDerivAt (fun s : ℝ => s ^ 2 / 2) t t := by
        simpa [mul_comm] using (hasDerivAt_pow 2 t).div_const (2 : ℝ)
      have hc : HasDerivAt (fun s : ℝ => s ^ 4 / 24) (t ^ 3 / 6) t := by
        convert (hasDerivAt_pow 4 t).div_const (24 : ℝ) using 1; ring
      convert (ha.sub hb).add hc using 1; ring
    convert h1.sub (Real.hasDerivAt_cos t) using 1; ring
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact (show Differentiable ℝ f from fun t => (hderiv t).differentiableAt).continuous.continuousOn
    · exact fun t _ => (hderiv t).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht0 : 0 ≤ t := le_of_lt (by simpa [interior_Ici] using ht)
      rw [(hderiv t).deriv]
      linarith [sin_ge_cubic t ht0]
  have h0 : f 0 ≤ f x := hmono (by simp) (by simpa using hx) hx
  simp only [f, Real.cos_zero] at h0
  linarith

theorem cos_le_pi_div_two_sub (x : ℝ) (hx : x ≤ Real.pi / 2) :
    Real.cos x ≤ Real.pi / 2 - x := by
  rw [← Real.sin_pi_div_two_sub]
  exact Real.sin_le (by linarith)

/-- General discrete Parseval identity on `Finset.range N`. -/
theorem dft_parseval (N : ℕ) (hN : 0 < N) (f : ℕ → ℂ) :
    ∑ a ∈ range N, Complex.normSq (∑ x ∈ range N, f x * eigenvalue (-((a * x : ℕ) : ℝ) / N)) =
      (N : ℝ) * ∑ x ∈ range N, Complex.normSq (f x) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have horth (x y : ℕ) (hx : x < N) (hy : y < N) :
      (∑ a ∈ range N, eigenvalue (-((a * x : ℕ) : ℝ) / N) *
        starRingEnd ℂ (eigenvalue (-((a * y : ℕ) : ℝ) / N))) = if x = y then (N : ℂ) else 0 := by
    have hterm (a : ℕ) :
        eigenvalue (-((a * x : ℕ) : ℝ) / N) * starRingEnd ℂ (eigenvalue (-((a * y : ℕ) : ℝ) / N)) =
        eigenvalue (((y : ℝ) - (x : ℝ)) / N) ^ a := by
      unfold eigenvalue
      rw [← Complex.exp_conj, ← Complex.exp_nat_mul, ← Complex.exp_add]
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
      congr 1; push_cast; ring
    simp_rw [hterm]
    by_cases hxy : x = y
    · subst hxy
      simp [eigenvalue]
    · rw [if_neg hxy]
      set ω : ℂ := eigenvalue (((y : ℝ) - (x : ℝ)) / N)
      have hne : ω ≠ 1 := by
        intro h1
        unfold ω eigenvalue at h1
        rw [Complex.exp_eq_one_iff] at h1
        obtain ⟨k, hk⟩ := h1
        have h2pi : (2 : ℂ) * Real.pi * Complex.I ≠ 0 := by
          exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
            Complex.I_ne_zero
        have hratio : ((((y : ℝ) - (x : ℝ)) / N : ℝ) : ℂ) = (k : ℂ) := by
          apply mul_right_cancel₀ h2pi
          calc
            ((((y : ℝ) - (x : ℝ)) / N : ℝ) : ℂ) * (2 * Real.pi * Complex.I)
              = Complex.I * ((2 * Real.pi * (((y : ℝ) - (x : ℝ)) / N) : ℝ) : ℂ) := by push_cast; ring
            _ = (k : ℂ) * (2 * Real.pi * Complex.I) := hk
        have hR : ((y : ℝ) - (x : ℝ)) / N = k := by exact_mod_cast hratio
        have hmul : (y : ℝ) - (x : ℝ) = (k : ℝ) * (N : ℝ) := (div_eq_iff hNR.ne').mp hR
        have hZ : (y : ℤ) - (x : ℤ) = k * (N : ℤ) := by exact_mod_cast hmul
        have hlt1 : -(N : ℤ) < (y : ℤ) - (x : ℤ) := by omega
        have hlt2 : (y : ℤ) - (x : ℤ) < (N : ℤ) := by omega
        have hk0 : k = 0 := by nlinarith
        subst hk0
        omega
      rw [geom_sum_eq hne]
      have hpow : ω ^ N = 1 := by
        unfold ω
        rw [eigenvalue_pow_eq_eigenvalue_mul]
        have harg : (N : ℝ) * (((y : ℝ) - (x : ℝ)) / N) = ((y : ℤ) - (x : ℤ) : ℤ) := by
          push_cast; field_simp [hNR.ne']
        rw [harg, eigenvalue_int]
      rw [hpow, sub_self, zero_div]
  have hC : (∑ a ∈ range N, ((∑ x ∈ range N, f x * eigenvalue (-((a * x : ℕ) : ℝ) / N)) *
      starRingEnd ℂ (∑ y ∈ range N, f y * eigenvalue (-((a * y : ℕ) : ℝ) / N)))) =
      (N : ℂ) * ∑ x ∈ range N, f x * starRingEnd ℂ (f x) := by
    simp_rw [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hinner (x : ℕ) (hx : x ∈ range N) :
        (∑ a ∈ range N, ∑ y ∈ range N,
          f x * eigenvalue (-((a * x : ℕ) : ℝ) / N) *
            (starRingEnd ℂ (f y) * starRingEnd ℂ (eigenvalue (-((a * y : ℕ) : ℝ) / N)))) =
        (N : ℂ) * (f x * starRingEnd ℂ (f x)) := by
      rw [Finset.sum_comm]
      have hy (y : ℕ) (hy : y ∈ range N) :
          (∑ a ∈ range N,
            f x * eigenvalue (-((a * x : ℕ) : ℝ) / N) *
              (starRingEnd ℂ (f y) * starRingEnd ℂ (eigenvalue (-((a * y : ℕ) : ℝ) / N)))) =
          if x = y then (N : ℂ) * (f x * starRingEnd ℂ (f x)) else 0 := by
        have hrw : ∀ a ∈ range N,
            f x * eigenvalue (-((a * x : ℕ) : ℝ) / N) *
              (starRingEnd ℂ (f y) * starRingEnd ℂ (eigenvalue (-((a * y : ℕ) : ℝ) / N))) =
            (f x * starRingEnd ℂ (f y)) *
              (eigenvalue (-((a * x : ℕ) : ℝ) / N) * starRingEnd ℂ (eigenvalue (-((a * y : ℕ) : ℝ) / N))) := by
          intro a _; ring
        rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum, horth x y (mem_range.mp hx) (mem_range.mp hy)]
        split_ifs with hxy
        · subst hxy; ring
        · ring
      rw [Finset.sum_congr rfl hy]
      simp [mem_range.mp hx]
    rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum]
  have hre := congrArg Complex.re hC
  have hns : ∀ z : ℂ, (z * starRingEnd ℂ z).re = Complex.normSq z := fun z => by
    rw [Complex.mul_conj, Complex.ofReal_re]
  rw [Complex.re_sum, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero, Complex.re_sum] at hre
  simpa only [hns] using hre

/-- Exact sum of `cos (2π M k / r)` is `0` when `0 < r` and `¬ r ∣ M`. -/
theorem sum_cos_eq_zero (r M : ℕ) (hr : 0 < r) (hndvd : ¬ r ∣ M) :
    ∑ k ∈ range r, Real.cos (2 * Real.pi * M * (k : ℝ) / r) = 0 := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  set ω : ℂ := eigenvalue ((M : ℝ) / r)
  have hterm (k : ℕ) : Real.cos (2 * Real.pi * M * (k : ℝ) / r) = (ω ^ k).re := by
    rw [eigenvalue_pow_eq_eigenvalue_mul]
    unfold eigenvalue
    rw [show Complex.I * ((2 * Real.pi * ((k : ℝ) * ((M : ℝ) / r)) : ℝ) : ℂ) =
      ((2 * Real.pi * M * (k : ℝ) / r : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_ofReal_mul_I_re]
  have hsum : ∑ k ∈ range r, Real.cos (2 * Real.pi * M * (k : ℝ) / r) = (∑ k ∈ range r, ω ^ k).re := by
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl (fun k _ => hterm k)
  rw [hsum]
  have hne : ω ≠ 1 := by
    intro h1
    unfold ω eigenvalue at h1
    rw [Complex.exp_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    have h2pi : (2 : ℂ) * Real.pi * Complex.I ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        Complex.I_ne_zero
    have hratio : (((M : ℝ) / r : ℝ) : ℂ) = (n : ℂ) := by
      apply mul_right_cancel₀ h2pi
      calc
        (((M : ℝ) / r : ℝ) : ℂ) * (2 * Real.pi * Complex.I)
          = Complex.I * ((2 * Real.pi * ((M : ℝ) / r) : ℝ) : ℂ) := by push_cast; ring
        _ = (n : ℂ) * (2 * Real.pi * Complex.I) := hn
    have hR : (M : ℝ) / r = n := by exact_mod_cast hratio
    have hmul : (M : ℝ) = (n : ℝ) * (r : ℝ) := (div_eq_iff hrR.ne').mp hR
    have hZ : (M : ℤ) = n * (r : ℤ) := by exact_mod_cast hmul
    have hn0 : 0 ≤ n := by nlinarith
    lift n to ℕ using hn0
    have hN : M = r * n := by rw [mul_comm] at hZ; exact_mod_cast hZ
    exact hndvd ⟨n, hN⟩
  have hpow : ω ^ r = 1 := by
    unfold ω
    rw [eigenvalue_pow_eq_eigenvalue_mul]
    have harg : (r : ℝ) * ((M : ℝ) / r) = ((M : ℤ) : ℝ) := by push_cast; field_simp [hrR.ne']
    rw [harg, eigenvalue_int]
  rw [geom_sum_eq hne, hpow, sub_self, zero_div, Complex.zero_re]

/-- Exact average of `cos²(π M k / r)` over `Fin r` when `¬ r ∣ M`. -/
theorem sum_cos_sq_eq (r M : ℕ) (hr : 0 < r) (hndvd : ¬ r ∣ M) :
    ∑ k : Fin r, Real.cos (Real.pi * M * (k.val : ℝ) / r) ^ 2 = (r : ℝ) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => Real.cos (Real.pi * M * (k : ℝ) / r) ^ 2)]
  have he : ∀ k ∈ range r, Real.cos (Real.pi * M * (k : ℝ) / r) ^ 2 =
      1 / 2 + Real.cos (2 * Real.pi * M * (k : ℝ) / r) / 2 := by
    intro k _
    rw [Real.cos_sq, show 2 * (Real.pi * (M : ℝ) * (k : ℝ) / r) = 2 * Real.pi * M * (k : ℝ) / r by ring]
  have hsum2 : ∑ k ∈ range r, Real.cos (2 * Real.pi * M * (k : ℝ) / r) / 2 = 0 := by
    rw [← Finset.sum_div, sum_cos_eq_zero r M hr hndvd, zero_div]
  rw [Finset.sum_congr rfl he, Finset.sum_add_distrib, hsum2]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, add_zero]
  ring

theorem cos_sq_mod (r m t : ℕ) (hr : 0 < r) :
    Real.cos (Real.pi * m * ((t % r : ℕ) : ℝ) / r) ^ 2 = Real.cos (Real.pi * m * t / r) ^ 2 := by
  have hrR : (r : ℝ) ≠ 0 := by positivity
  have ht : (t : ℝ) = ((t % r : ℕ) : ℝ) + r * ((t / r : ℕ) : ℝ) := by
    have := Nat.mod_add_div t r
    exact_mod_cast this.symm
  have he : Real.pi * m * ((t % r : ℕ) : ℝ) / r =
      Real.pi * m * t / r - ((m * (t / r) : ℕ) : ℝ) * Real.pi := by
    rw [ht]; push_cast; field_simp; ring
  rw [he, Real.cos_sub_nat_mul_pi, mul_pow, ← pow_mul, mul_comm _ 2, pow_mul, neg_one_sq,
    one_pow, one_mul]

/-! ### Part 2: Factorization, Parseval, and Far Tail (`≤ 12 / 1000000`) -/

def sineW (z : ℂ) : ℂ := ∑ u ∈ range 1024, sineWeight 10 u * z ^ u

def geomB (B : ℕ) (ω : ℂ) : ℂ := ∑ j ∈ range B, ω ^ j

theorem range_mul_sum {A : Type*} [AddCommMonoid A] (P Q : ℕ) (f : ℕ → A) :
    ∑ x ∈ range (P * Q), f x = ∑ u ∈ range P, ∑ j ∈ range Q, f (u * Q + j) := by
  induction P with
  | zero => simp
  | succ P ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

theorem sinePhaseAmplitude_factor (M : ℕ) (hM : 10 ≤ M) (β : ℝ) (a : ℕ) :
    let B : ℕ := 2 ^ (M - 10)
    let ω := eigenvalue (β - (a : ℝ) / (2 ^ M : ℕ))
    sinePhaseAmplitude M β a = ((2 ^ M : ℕ) : ℂ)⁻¹ * sineW (ω ^ B) * geomB B ω := by
  dsimp only
  set B : ℕ := 2 ^ (M - 10)
  set ω := eigenvalue (β - (a : ℝ) / (2 ^ M : ℕ))
  have hBpos : 0 < B := pow_pos (by decide) _
  have hN : 2 ^ M = 1024 * B := by
    have : 2 ^ M = 2 ^ 10 * 2 ^ (M - 10) := by rw [← pow_add, Nat.add_sub_cancel' hM]
    simpa [B] using this
  unfold sinePhaseAmplitude sineW geomB
  rw [mul_assoc, Finset.sum_mul_sum]
  congr 1
  change ∑ x ∈ range (2 ^ M), sineWeight 10 (x / B) * ω ^ x = _
  rw [hN, range_mul_sum 1024 B]
  apply Finset.sum_congr rfl; intro u _
  apply Finset.sum_congr rfl; intro j hj
  have hjlt : j < B := mem_range.mp hj
  have hdiv : (u * B + j) / B = u := by
    rw [Nat.mul_comm u B, Nat.mul_add_div hBpos, Nat.div_eq_of_lt hjlt, Nat.add_zero]
  rw [hdiv, pow_add, Nat.mul_comm u B, pow_mul, mul_assoc]

theorem sineWeight_sum_normSq :
    ∑ u ∈ range 1024, Complex.normSq (sineWeight 10 u) = 1024 := by
  have he : ∀ u ∈ range 1024,
      Complex.normSq (sineWeight 10 u) = 1 - Real.cos (2 * Real.pi * ((1 : ℕ) : ℝ) * (u : ℝ) / (1024 : ℕ)) := by
    intro u _
    rw [sineWeight_normSq, Real.sin_sq_eq_half_sub]
    have harg : 2 * (Real.pi * (u : ℝ) / (2 : ℝ) ^ 10) = 2 * Real.pi * ((1 : ℕ) : ℝ) * (u : ℝ) / (1024 : ℕ) := by
      push_cast; norm_num; ring
    rw [harg]; ring
  rw [Finset.sum_congr rfl he, Finset.sum_sub_distrib, sum_cos_eq_zero 1024 1 (by decide) (by decide)]
  simp

theorem sinePhaseAmplitude_parseval (M : ℕ) (hM : 10 ≤ M) (β : ℝ) :
    ∑ a ∈ range (2 ^ M), Complex.normSq (sinePhaseAmplitude M β a) = 1 := by
  set N := 2 ^ M
  set B := 2 ^ (M - 10)
  have hNpos : 0 < N := pow_pos (by decide) M
  have hBpos : 0 < B := pow_pos (by decide) _
  have hNB : N = 1024 * B := by
    have : 2 ^ M = 2 ^ 10 * 2 ^ (M - 10) := by rw [← pow_add, Nat.add_sub_cancel' hM]
    simpa [N, B] using this
  let f : ℕ → ℂ := fun x => sineWeight 10 (x / B) * eigenvalue (β * x)
  have hamp (a : ℕ) :
      Complex.normSq (sinePhaseAmplitude M β a) =
        ((N : ℝ) ^ 2)⁻¹ * Complex.normSq (∑ x ∈ range N, f x * eigenvalue (-((a * x : ℕ) : ℝ) / N)) := by
    unfold sinePhaseAmplitude
    rw [Complex.normSq_mul, Complex.normSq_inv, Complex.normSq_natCast, ← sq]
    congr 2
    apply Finset.sum_congr rfl
    intro x _
    dsimp only [f]
    rw [mul_assoc, ← eigenvalue_add, eigenvalue_pow_eq_eigenvalue_mul]
    congr 2; dsimp only [N]; push_cast; ring
  simp_rw [hamp]
  rw [← Finset.mul_sum, dft_parseval N hNpos f]
  have hf_norm (x : ℕ) : Complex.normSq (f x) = Complex.normSq (sineWeight 10 (x / B)) := by
    dsimp only [f]
    rw [Complex.normSq_mul, eigenvalue_normSq, mul_one]
  simp_rw [hf_norm]
  have hsum : ∑ x ∈ range N, Complex.normSq (sineWeight 10 (x / B)) = (N : ℝ) := by
    rw [hNB, range_mul_sum 1024 B]
    have hinner (u : ℕ) (_ : u ∈ range 1024) :
        ∑ j ∈ range B, Complex.normSq (sineWeight 10 ((u * B + j) / B)) =
          (B : ℝ) * Complex.normSq (sineWeight 10 u) := by
      have hcongr : ∀ j ∈ range B,
          Complex.normSq (sineWeight 10 ((u * B + j) / B)) = Complex.normSq (sineWeight 10 u) := by
        intro j hj
        rw [Nat.mul_comm u B, Nat.mul_add_div hBpos, Nat.div_eq_of_lt (mem_range.mp hj), Nat.add_zero]
      rw [Finset.sum_congr rfl hcongr]
      simp
    rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum, sineWeight_sum_normSq]
    push_cast; ring
  rw [hsum]
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hNpos.ne'
  field_simp [hNR]

theorem one_sub_mul_sineW (z : ℂ) :
    (1 - z) * sineW z =
      (-sineWeight 10 1023 * z ^ 1024) +
      ∑ u ∈ range 1023, (sineWeight 10 (u + 1) - sineWeight 10 u) * z ^ (u + 1) := by
  unfold sineW
  rw [sub_mul, one_mul, Finset.mul_sum]
  have hsplit : ∑ u ∈ range 1024, sineWeight 10 u * z ^ u =
      sineWeight 10 0 * z ^ 0 + ∑ u ∈ range 1023, sineWeight 10 (u + 1) * z ^ (u + 1) :=
    (Finset.sum_range_succ' (fun u => sineWeight 10 u * z ^ u) 1023).trans (add_comm _ _)
  have hsplit2 : ∑ u ∈ range 1024, z * (sineWeight 10 u * z ^ u) =
      (∑ u ∈ range 1023, sineWeight 10 u * z ^ (u + 1)) + sineWeight 10 1023 * z ^ 1024 := by
    rw [Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl; intro u _; rw [pow_succ]; ring
    · rw [show (1024 : ℕ) = 1023 + 1 from rfl, pow_succ]; ring
  have hw0 : sineWeight 10 0 = 0 := by simp [sineWeight]
  rw [hsplit, hsplit2, hw0, zero_mul, zero_add]
  have hsub : (∑ u ∈ range 1023, sineWeight 10 (u + 1) * z ^ (u + 1)) -
      (∑ u ∈ range 1023, sineWeight 10 u * z ^ (u + 1)) =
      ∑ u ∈ range 1023, (sineWeight 10 (u + 1) - sineWeight 10 u) * z ^ (u + 1) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro u _; ring
  rw [← hsub]; ring

theorem sineW_diff_parseval (M : ℕ) (hM : 10 ≤ M) (β : ℝ) :
    let B : ℕ := 2 ^ (M - 10)
    ∑ r ∈ range 1024, Complex.normSq ((eigenvalue ((B : ℝ) * β - (r : ℝ) / 1024) - 1) *
      sineW (eigenvalue ((B : ℝ) * β - (r : ℝ) / 1024))) ≤ 2 * Real.pi ^ 2 := by
  dsimp only
  set B : ℕ := 2 ^ (M - 10)
  let d : ℕ → ℂ := fun u =>
    if u = 0 then -sineWeight 10 1023 * eigenvalue ((1024 * B : ℕ) * β)
    else sineWeight 10 u - sineWeight 10 (u - 1)
  let g : ℕ → ℂ := fun u => d u * eigenvalue ((B : ℝ) * β * u)
  have hmatch (r : ℕ) :
      Complex.normSq ((eigenvalue ((B : ℝ) * β - (r : ℝ) / 1024) - 1) *
        sineW (eigenvalue ((B : ℝ) * β - (r : ℝ) / 1024))) =
      Complex.normSq (∑ u ∈ range 1024, g u * eigenvalue (-((r * u : ℕ) : ℝ) / 1024)) := by
    set z := eigenvalue ((B : ℝ) * β - (r : ℝ) / 1024)
    have hneg : (z - 1) * sineW z = -((1 - z) * sineW z) := by ring
    rw [hneg, Complex.normSq_neg, one_sub_mul_sineW]
    congr 1
    have hz1024 : z ^ 1024 = eigenvalue ((1024 * B : ℕ) * β) := by
      unfold z
      rw [eigenvalue_pow_eq_eigenvalue_mul]
      have harg : ((1024 : ℕ) : ℝ) * ((B : ℝ) * β - (r : ℝ) / 1024) = ((1024 * B : ℕ) : ℝ) * β - (r : ℤ) := by
        push_cast; ring
      rw [harg, eigenvalue_sub_int]
    have hzu (u : ℕ) : g u * eigenvalue (-((r * u : ℕ) : ℝ) / 1024) = d u * z ^ u := by
      dsimp only [g, z]
      rw [mul_assoc, ← eigenvalue_add, eigenvalue_pow_eq_eigenvalue_mul]
      congr 2; push_cast; ring
    simp_rw [hzu]
    rw [Finset.sum_range_succ' _ 1023]
    simp only [d, ↓reduceIte, pow_zero, mul_one, hz1024, Nat.add_one_ne_zero, Nat.add_sub_cancel]
    ring
  simp_rw [hmatch]
  have hdft := dft_parseval 1024 (by decide) g
  simp only [Nat.cast_ofNat] at hdft
  rw [hdft]
  have hg (u : ℕ) (_ : u ∈ range 1024) : Complex.normSq (g u) ≤ 2 * (Real.pi / 1024) ^ 2 := by
    dsimp only [g]
    rw [Complex.normSq_mul, eigenvalue_normSq, mul_one]
    by_cases hu : u = 0
    · simp only [d, hu, ↓reduceIte, Complex.normSq_mul, Complex.normSq_neg, eigenvalue_normSq,
        mul_one, sineWeight_normSq]
      have hsin : Real.sin (Real.pi * (1023 : ℝ) / (2 : ℝ) ^ 10) = Real.sin (Real.pi / 1024) := by
        rw [show Real.pi * (1023 : ℝ) / (2 : ℝ) ^ 10 = Real.pi - Real.pi / 1024 by norm_num; ring,
          Real.sin_pi_sub]
      rw [Nat.cast_ofNat, hsin]
      have hpi1024 : 0 < Real.pi / 1024 := div_pos Real.pi_pos (by norm_num)
      have hle : Real.sin (Real.pi / 1024) ≤ Real.pi / 1024 := Real.sin_le hpi1024.le
      have h0 : 0 ≤ Real.sin (Real.pi / 1024) := Real.sin_nonneg_of_nonneg_of_le_pi hpi1024.le
        (by linarith [Real.pi_pos])
      nlinarith
    · simp only [d, hu, ↓reduceIte]
      rw [sineWeight_eq_sin, sineWeight_eq_sin, ← mul_sub, Complex.normSq_mul, Complex.normSq_mul,
        Complex.normSq_ofReal, Complex.normSq_I, mul_one, Real.mul_self_sqrt (by norm_num),
        ← Complex.ofReal_sub, Complex.normSq_ofReal, ← sq]
      have hlip := Real.abs_sin_sub_sin_le (Real.pi * (u : ℝ) / (2 : ℝ) ^ 10)
        (Real.pi * ((u - 1 : ℕ) : ℝ) / (2 : ℝ) ^ 10)
      have h1 : 1 ≤ u := Nat.one_le_iff_ne_zero.mpr hu
      have hdiff : Real.pi * (u : ℝ) / (2 : ℝ) ^ 10 - Real.pi * ((u - 1 : ℕ) : ℝ) / (2 : ℝ) ^ 10 =
          Real.pi / 1024 := by
        rw [Nat.cast_sub h1]; push_cast; norm_num; ring
      have hpi1024 : 0 < Real.pi / 1024 := div_pos Real.pi_pos (by norm_num)
      rw [hdiff, abs_of_pos hpi1024] at hlip
      have hsq : (Real.sin (Real.pi * (u : ℝ) / (2 : ℝ) ^ 10) -
          Real.sin (Real.pi * ((u - 1 : ℕ) : ℝ) / (2 : ℝ) ^ 10)) ^ 2 ≤ (Real.pi / 1024) ^ 2 := by
        calc
          _ = |Real.sin (Real.pi * (u : ℝ) / (2 : ℝ) ^ 10) -
              Real.sin (Real.pi * ((u - 1 : ℕ) : ℝ) / (2 : ℝ) ^ 10)| ^ 2 := (sq_abs _).symm
          _ ≤ (Real.pi / 1024) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hlip 2
      linarith
  have hsum := Finset.sum_le_sum hg
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hcalc : (1024 : ℝ) * ((1024 : ℝ) * (2 * (Real.pi / 1024) ^ 2)) = 2 * Real.pi ^ 2 := by ring
  nlinarith

theorem sum_inv_sq_half_ge (S : Finset ℕ) (φ : ℕ → ℝ)
    (hφ : ∀ q ∈ S, (1 / 2 : ℝ) ≤ φ q)
    (hsep : ∀ q1 ∈ S, ∀ q2 ∈ S, |φ q1 - φ q2| < 1 → q1 = q2) :
    ∑ q ∈ S, 1 / (φ q) ^ 2 ≤ 5 := by
  let S0 := S.filter (fun q => φ q < 3 / 2)
  let S1 := S.filter (fun q => 3 / 2 ≤ φ q)
  have hS1 : S.filter (fun q => ¬ φ q < 3 / 2) = S1 := by
    ext q; simp [S1, not_lt]
  have hpart : ∑ q ∈ S, 1 / (φ q) ^ 2 = (∑ q ∈ S0, 1 / (φ q) ^ 2) + ∑ q ∈ S1, 1 / (φ q) ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not S (fun q => φ q < 3 / 2), hS1]
  have h0 : ∑ q ∈ S0, 1 / (φ q) ^ 2 ≤ 4 := by
    by_cases he : S0 = ∅
    · simp [he]
    · obtain ⟨q0, hq0⟩ := Finset.nonempty_iff_ne_empty.mpr he
      have hsub : S0 ⊆ {q0} := by
        intro q hq
        rw [Finset.mem_singleton]
        have h1 := Finset.mem_filter.mp hq
        have h2 := Finset.mem_filter.mp hq0
        have hp1 := hφ q h1.1
        have hp2 := hφ q0 h2.1
        exact hsep q h1.1 q0 h2.1 (abs_lt.mpr ⟨by linarith [h1.2, h2.2], by linarith [h1.2, h2.2]⟩)
      have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := fun q => 1 / (φ q) ^ 2) hsub (fun _ _ _ => by positivity)
      rw [Finset.sum_singleton] at hle
      have hp0 := hφ q0 (Finset.mem_filter.mp hq0).1
      have h4 : 1 / (φ q0) ^ 2 ≤ 4 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      linarith
  have h1 : ∑ q ∈ S1, 1 / (φ q) ^ 2 ≤ 1 := by
    have hi := sum_inv_sq_le_first S1 φ (3 / 2) (by norm_num)
      (fun q hq => (Finset.mem_filter.mp hq).2)
      (fun q1 hq1 q2 hq2 => hsep q1 (Finset.mem_filter.mp hq1).1 q2 (Finset.mem_filter.mp hq2).1)
    unfold tailBound at hi
    linarith
  linarith

theorem phiR_add_phiL (N : ℕ) (c : ℝ) (a : ℕ) (hne : (a : ℝ) ≠ c) :
    phiR N c a + phiL N c a = N := by
  unfold phiR phiL
  by_cases h : c ≤ (a : ℝ)
  · have hlt : ¬ (a : ℝ) ≤ c := fun h2 => hne (le_antisymm h2 h)
    rw [if_pos h, if_neg hlt]; ring
  · have hle : (a : ℝ) ≤ c := le_of_not_ge h
    rw [if_neg h, if_pos hle]; ring

theorem abs_sin_phiR_half (N : ℕ) (hN : 0 < N) (β : ℝ) (a : ℕ)
    (hd : 0 < phiR N ((N : ℝ) * β) a) (hle : phiR N ((N : ℝ) * β) a ≤ (N : ℝ) / 2) :
    |Real.sin (Real.pi * (β - (a : ℝ) / N))| = Real.sin (Real.pi * (phiR N ((N : ℝ) * β) a / N)) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos : 0 ≤ Real.sin (Real.pi * (phiR N ((N : ℝ) * β) a / N)) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
    have : phiR N ((N : ℝ) * β) a / N ≤ 1 / 2 := (div_le_iff₀ hNR).mpr (by linarith)
    nlinarith [Real.pi_pos]
  by_cases hca : (N : ℝ) * β ≤ a
  · have he : Real.pi * (β - (a : ℝ) / N) = -(Real.pi * (phiR N ((N : ℝ) * β) a / N)) := by
      simp only [phiR, if_pos hca]; field_simp [hNR.ne']; ring
    rw [he, Real.sin_neg, abs_neg, abs_of_nonneg hpos]
  · have he : Real.pi * (β - (a : ℝ) / N) = Real.pi - Real.pi * (phiR N ((N : ℝ) * β) a / N) := by
      simp only [phiR, if_neg hca]; field_simp [hNR.ne']; ring
    rw [he, Real.sin_pi_sub, abs_of_nonneg hpos]

theorem abs_sin_phiL_half (N : ℕ) (hN : 0 < N) (β : ℝ) (a : ℕ)
    (hd : 0 < phiL N ((N : ℝ) * β) a) (hle : phiL N ((N : ℝ) * β) a ≤ (N : ℝ) / 2) :
    |Real.sin (Real.pi * (β - (a : ℝ) / N))| = Real.sin (Real.pi * (phiL N ((N : ℝ) * β) a / N)) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos : 0 ≤ Real.sin (Real.pi * (phiL N ((N : ℝ) * β) a / N)) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
    have : phiL N ((N : ℝ) * β) a / N ≤ 1 / 2 := (div_le_iff₀ hNR).mpr (by linarith)
    nlinarith [Real.pi_pos]
  by_cases hca : (a : ℝ) ≤ (N : ℝ) * β
  · have he : Real.pi * (β - (a : ℝ) / N) = Real.pi * (phiL N ((N : ℝ) * β) a / N) := by
      simp only [phiL, if_pos hca]; field_simp [hNR.ne']
    rw [he, abs_of_nonneg hpos]
  · have he : Real.pi * (β - (a : ℝ) / N) = Real.pi * (phiL N ((N : ℝ) * β) a / N) - Real.pi := by
      simp only [phiL, if_neg hca]; field_simp [hNR.ne']; ring
    rw [he, Real.sin_sub_pi, abs_neg, abs_of_nonneg hpos]

theorem phiR_sep_1024 (N : ℕ) (B : ℕ) (hN : N = 1024 * B) (c : ℝ) (r : ℕ)
    (q1 q2 : ℕ) (hq1 : q1 < B) (hq2 : q2 < B)
    (h : |phiR N c (1024 * q1 + r) / 1024 - phiR N c (1024 * q2 + r) / 1024| < 1) :
    q1 = q2 := by
  have h1024 : |phiR N c (1024 * q1 + r) - phiR N c (1024 * q2 + r)| < 1024 := by
    have := mul_lt_mul_of_pos_right h (by norm_num : (0 : ℝ) < 1024)
    rw [← abs_of_pos (by norm_num : (0 : ℝ) < 1024), ← abs_mul] at this
    simpa [sub_mul, div_mul_cancel₀] using this
  unfold phiR at h1024
  split_ifs at h1024 <;>
    (have hNR : (N : ℝ) = 1024 * (B : ℝ) := by exact_mod_cast hN
     have hZ : |(q1 : ℤ) - (q2 : ℤ)| < 1 ∨ |(q1 : ℤ) - (q2 : ℤ) + (B : ℤ)| < 1 ∨
         |(q1 : ℤ) - (q2 : ℤ) - (B : ℤ)| < 1 := by
       try rw [hNR] at h1024
       first
       | left; have : |(q1 : ℝ) - (q2 : ℝ)| < 1 := by rw [abs_lt] at h1024 ⊢; constructor <;> push_cast at h1024 <;> linarith
         exact_mod_cast this
       | right; left; have : |(q1 : ℝ) - (q2 : ℝ) + (B : ℝ)| < 1 := by rw [abs_lt] at h1024 ⊢; constructor <;> push_cast at h1024 <;> linarith
         exact_mod_cast this
       | right; right; have : |(q1 : ℝ) - (q2 : ℝ) - (B : ℝ)| < 1 := by rw [abs_lt] at h1024 ⊢; constructor <;> push_cast at h1024 <;> linarith
         exact_mod_cast this
     rcases hZ with hZ | hZ | hZ <;> rw [abs_lt] at hZ <;> omega)

theorem phiL_sep_1024 (N : ℕ) (B : ℕ) (hN : N = 1024 * B) (c : ℝ) (r : ℕ)
    (q1 q2 : ℕ) (hq1 : q1 < B) (hq2 : q2 < B)
    (h : |phiL N c (1024 * q1 + r) / 1024 - phiL N c (1024 * q2 + r) / 1024| < 1) :
    q1 = q2 := by
  have h1024 : |phiL N c (1024 * q1 + r) - phiL N c (1024 * q2 + r)| < 1024 := by
    have := mul_lt_mul_of_pos_right h (by norm_num : (0 : ℝ) < 1024)
    rw [← abs_of_pos (by norm_num : (0 : ℝ) < 1024), ← abs_mul] at this
    simpa [sub_mul, div_mul_cancel₀] using this
  unfold phiL at h1024
  split_ifs at h1024 <;>
    (have hNR : (N : ℝ) = 1024 * (B : ℝ) := by exact_mod_cast hN
     have hZ : |(q1 : ℤ) - (q2 : ℤ)| < 1 ∨ |(q1 : ℤ) - (q2 : ℤ) + (B : ℤ)| < 1 ∨
         |(q1 : ℤ) - (q2 : ℤ) - (B : ℤ)| < 1 := by
       try rw [hNR] at h1024
       first
       | left; have : |(q1 : ℝ) - (q2 : ℝ)| < 1 := by rw [abs_lt] at h1024 ⊢; constructor <;> push_cast at h1024 <;> linarith
         exact_mod_cast this
       | right; left; have : |(q1 : ℝ) - (q2 : ℝ) + (B : ℝ)| < 1 := by rw [abs_lt] at h1024 ⊢; constructor <;> push_cast at h1024 <;> linarith
         exact_mod_cast this
       | right; right; have : |(q1 : ℝ) - (q2 : ℝ) - (B : ℝ)| < 1 := by rw [abs_lt] at h1024 ⊢; constructor <;> push_cast at h1024 <;> linarith
         exact_mod_cast this
     rcases hZ with hZ | hZ | hZ <;> rw [abs_lt] at hZ <;> omega)

/-- Far-tail bound: total mass outside circular radius `512` is at most `12 / 1000000`. -/
theorem sinePhaseAmplitude_far_tail (M : ℕ) (hM : 11 ≤ M) (β : ℝ) :
    (∑ a ∈ range (2 ^ M),
      if 512 < phiR (2 ^ M) ((2 ^ M : ℕ) * β) a ∧ 512 < phiL (2 ^ M) ((2 ^ M : ℕ) * β) a
      then Complex.normSq (sinePhaseAmplitude M β a) else 0) ≤ 12 / 1000000 := by
  set N := 2 ^ M
  set B := 2 ^ (M - 10)
  have hM10 : 10 ≤ M := by omega
  have hNpos : 0 < N := pow_pos (by decide) M
  have hBpos : 0 < B := pow_pos (by decide) _
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hBR : (0 : ℝ) < B := by exact_mod_cast hBpos
  have hNB : N = 1024 * B := by
    have : 2 ^ M = 2 ^ 10 * 2 ^ (M - 10) := by rw [← pow_add, Nat.add_sub_cancel' hM10]
    simpa [N, B] using this
  have hNBR : (N : ℝ) = 1024 * (B : ℝ) := by exact_mod_cast hNB
  have hreidx :
      (∑ a ∈ range N,
        if 512 < phiR N ((N : ℝ) * β) a ∧ 512 < phiL N ((N : ℝ) * β) a
        then Complex.normSq (sinePhaseAmplitude M β a) else 0) =
      ∑ r ∈ range 1024, ∑ q ∈ range B,
        if 512 < phiR N ((N : ℝ) * β) (q * 1024 + r) ∧ 512 < phiL N ((N : ℝ) * β) (q * 1024 + r)
        then Complex.normSq (sinePhaseAmplitude M β (q * 1024 + r)) else 0 := by
    rw [Finset.sum_comm, hNB, Nat.mul_comm 1024 B, range_mul_sum B 1024]
  rw [hreidx]
  have hper_r (r : ℕ) (hr : r ∈ range 1024) :
      (∑ q ∈ range B,
        if 512 < phiR N ((N : ℝ) * β) (q * 1024 + r) ∧ 512 < phiL N ((N : ℝ) * β) (q * 1024 + r)
        then Complex.normSq (sinePhaseAmplitude M β (q * 1024 + r)) else 0) ≤
      (5 / 8 : ℝ) / (1024 : ℝ) ^ 2 *
        Complex.normSq ((eigenvalue ((B : ℝ) * β - (r : ℝ) / 1024) - 1) *
          sineW (eigenvalue ((B : ℝ) * β - (r : ℝ) / 1024))) := by
    set zr := eigenvalue ((B : ℝ) * β - (r : ℝ) / 1024)
    set num := Complex.normSq ((zr - 1) * sineW zr)
    have hnum0 : 0 ≤ num := Complex.normSq_nonneg _
    let Rq := (range B).filter (fun q =>
      512 < phiR N ((N : ℝ) * β) (q * 1024 + r) ∧ phiR N ((N : ℝ) * β) (q * 1024 + r) ≤ (N : ℝ) / 2)
    let Lq := (range B).filter (fun q =>
      512 < phiL N ((N : ℝ) * β) (q * 1024 + r) ∧ phiL N ((N : ℝ) * β) (q * 1024 + r) ≤ (N : ℝ) / 2)
    have hpt (q : ℕ) (hq : q ∈ range B) (hfar : 512 < phiR N ((N : ℝ) * β) (q * 1024 + r) ∧
        512 < phiL N ((N : ℝ) * β) (q * 1024 + r)) :
        Complex.normSq (sinePhaseAmplitude M β (q * 1024 + r)) ≤
          num / (16 * (1024 : ℝ) ^ 2) *
            ((if 512 < phiR N ((N : ℝ) * β) (q * 1024 + r) ∧
                 phiR N ((N : ℝ) * β) (q * 1024 + r) ≤ (N : ℝ) / 2
              then 1 / (phiR N ((N : ℝ) * β) (q * 1024 + r) / 1024) ^ 2 else 0) +
             (if 512 < phiL N ((N : ℝ) * β) (q * 1024 + r) ∧
                 phiL N ((N : ℝ) * β) (q * 1024 + r) ≤ (N : ℝ) / 2
              then 1 / (phiL N ((N : ℝ) * β) (q * 1024 + r) / 1024) ^ 2 else 0)) := by
      set a := q * 1024 + r
      set ω := eigenvalue (β - (a : ℝ) / N)
      have hωB : ω ^ B = zr := by
        unfold ω zr
        rw [eigenvalue_pow_eq_eigenvalue_mul]
        have harg : (B : ℝ) * (β - (a : ℝ) / N) = ((B : ℝ) * β - (r : ℝ) / 1024) - (q : ℤ) := by
          dsimp only [a]; rw [hNBR]; push_cast; field_simp [hBR.ne']; ring
        rw [harg, eigenvalue_sub_int]
      have hne_c : (a : ℝ) ≠ (N : ℝ) * β := by
        intro heq
        have h0 : phiR N ((N : ℝ) * β) a = 0 := by simp [phiR, heq]
        linarith [hfar.1]
      have hsum_phi := phiR_add_phiL N ((N : ℝ) * β) a hne_c
      have hbd (d : ℝ) (hd : 512 < d) (hd2 : d ≤ (N : ℝ) / 2)
          (habs : |Real.sin (Real.pi * (β - (a : ℝ) / N))| = Real.sin (Real.pi * (d / N))) :
          Complex.normSq (sinePhaseAmplitude M β a) ≤
            num / (16 * (1024 : ℝ) ^ 2) * (1 / (d / 1024) ^ 2) := by
        have hsin_ge : 2 * (d / N) ≤ Real.sin (Real.pi * (d / N)) :=
          sin_jordan (d / N) (by positivity) ((div_le_iff₀ hNR).mpr (by linarith))
        have hsin_pos : 0 < |Real.sin (Real.pi * (β - (a : ℝ) / N))| := by
          rw [habs]; linarith [show (0 : ℝ) < 2 * (d / N) by positivity]
        have hω1 : ω ≠ 1 := by
          intro h1
          have h0 := normSq_eigenvalue_sub_one (β - (a : ℝ) / N)
          change Complex.normSq (ω - 1) = _ at h0
          rw [h1, sub_self, Complex.normSq_zero] at h0
          have hsp : 0 < 4 * Real.sin (Real.pi * (β - (a : ℝ) / N)) ^ 2 := by
            have := sq_pos_of_pos hsin_pos; rw [sq_abs] at this; linarith
          linarith
        have hfac := sinePhaseAmplitude_factor M hM10 β a
        change sinePhaseAmplitude M β a = ((N : ℂ)⁻¹) * sineW (ω ^ B) * geomB B ω at hfac
        rw [hfac, hωB, geomB, geom_sum_eq hω1, hωB]
        have heq : (N : ℂ)⁻¹ * sineW zr * ((zr - 1) / (ω - 1)) =
            (N : ℂ)⁻¹ * ((zr - 1) * sineW zr) / (ω - 1) := by ring
        rw [heq, Complex.normSq_div, Complex.normSq_mul, Complex.normSq_inv, Complex.normSq_natCast,
          normSq_eigenvalue_sub_one]
        have hden_ge : 16 * (d / N) ^ 2 ≤ 4 * Real.sin (Real.pi * (β - (a : ℝ) / N)) ^ 2 := by
          rw [← sq_abs (Real.sin _), habs]
          have hsq : (2 * (d / N)) ^ 2 ≤ Real.sin (Real.pi * (d / N)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) hsin_ge 2
          nlinarith
        have h1 : ((N : ℝ) * N)⁻¹ * num / (4 * Real.sin (Real.pi * (β - (a : ℝ) / N)) ^ 2) ≤
            ((N : ℝ) * N)⁻¹ * num / (16 * (d / N) ^ 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hden_ge
        refine h1.trans_eq ?_
        have hd0 : d ≠ 0 := by linarith
        field_simp [hNR.ne', hd0]
      by_cases hR : phiR N ((N : ℝ) * β) a ≤ (N : ℝ) / 2
      · have h1 := hbd _ hfar.1 hR (abs_sin_phiR_half N hNpos β a (by linarith [hfar.1]) hR)
        rw [if_pos ⟨hfar.1, hR⟩]
        have h2 : 0 ≤ (if 512 < phiL N ((N : ℝ) * β) a ∧ phiL N ((N : ℝ) * β) a ≤ (N : ℝ) / 2
            then 1 / (phiL N ((N : ℝ) * β) a / 1024) ^ 2 else 0) := by split_ifs <;> positivity
        have hmul : 0 ≤ num / (16 * (1024 : ℝ) ^ 2) := by positivity
        nlinarith
      · have hL : phiL N ((N : ℝ) * β) a ≤ (N : ℝ) / 2 := by linarith
        have h1 := hbd _ hfar.2 hL (abs_sin_phiL_half N hNpos β a (by linarith [hfar.2]) hL)
        rw [if_neg (fun h => hR h.2), if_pos ⟨hfar.2, hL⟩]
        have hmul : 0 ≤ num / (16 * (1024 : ℝ) ^ 2) := by positivity
        nlinarith
    have hsum1 :
        (∑ q ∈ range B,
          if 512 < phiR N ((N : ℝ) * β) (q * 1024 + r) ∧ 512 < phiL N ((N : ℝ) * β) (q * 1024 + r)
          then Complex.normSq (sinePhaseAmplitude M β (q * 1024 + r)) else 0) ≤
        num / (16 * (1024 : ℝ) ^ 2) *
          ((∑ q ∈ Rq, 1 / (phiR N ((N : ℝ) * β) (q * 1024 + r) / 1024) ^ 2) +
           (∑ q ∈ Lq, 1 / (phiL N ((N : ℝ) * β) (q * 1024 + r) / 1024) ^ 2)) := by
      rw [mul_add, Finset.mul_sum, Finset.mul_sum]
      have hRq : ∑ q ∈ Rq, num / (16 * (1024 : ℝ) ^ 2) *
            (1 / (phiR N ((N : ℝ) * β) (q * 1024 + r) / 1024) ^ 2) =
          ∑ q ∈ range B, num / (16 * (1024 : ℝ) ^ 2) *
            (if 512 < phiR N ((N : ℝ) * β) (q * 1024 + r) ∧
                phiR N ((N : ℝ) * β) (q * 1024 + r) ≤ (N : ℝ) / 2
             then 1 / (phiR N ((N : ℝ) * β) (q * 1024 + r) / 1024) ^ 2 else 0) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl; intro q _; split_ifs <;> ring
      have hLq : ∑ q ∈ Lq, num / (16 * (1024 : ℝ) ^ 2) *
            (1 / (phiL N ((N : ℝ) * β) (q * 1024 + r) / 1024) ^ 2) =
          ∑ q ∈ range B, num / (16 * (1024 : ℝ) ^ 2) *
            (if 512 < phiL N ((N : ℝ) * β) (q * 1024 + r) ∧
                phiL N ((N : ℝ) * β) (q * 1024 + r) ≤ (N : ℝ) / 2
             then 1 / (phiL N ((N : ℝ) * β) (q * 1024 + r) / 1024) ^ 2 else 0) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl; intro q _; split_ifs <;> ring
      rw [hRq, hLq, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro q hq
      rw [← mul_add]
      by_cases hfar : 512 < phiR N ((N : ℝ) * β) (q * 1024 + r) ∧
          512 < phiL N ((N : ℝ) * β) (q * 1024 + r)
      · rw [if_pos hfar]
        exact hpt q hq hfar
      · rw [if_neg hfar]
        apply mul_nonneg (by positivity)
        apply add_nonneg <;> (split_ifs <;> positivity)
    have hR5 : ∑ q ∈ Rq, 1 / (phiR N ((N : ℝ) * β) (q * 1024 + r) / 1024) ^ 2 ≤ 5 := by
      apply sum_inv_sq_half_ge Rq (fun q => phiR N ((N : ℝ) * β) (q * 1024 + r) / 1024)
      · intro q hq; have := (Finset.mem_filter.mp hq).2.1; linarith
      · intro q1 hq1 q2 hq2 hlt
        rw [Nat.mul_comm q1 1024, Nat.mul_comm q2 1024] at hlt
        exact phiR_sep_1024 N B hNB ((N : ℝ) * β) r q1 q2
          (mem_range.mp (Finset.mem_filter.mp hq1).1) (mem_range.mp (Finset.mem_filter.mp hq2).1) hlt
    have hL5 : ∑ q ∈ Lq, 1 / (phiL N ((N : ℝ) * β) (q * 1024 + r) / 1024) ^ 2 ≤ 5 := by
      apply sum_inv_sq_half_ge Lq (fun q => phiL N ((N : ℝ) * β) (q * 1024 + r) / 1024)
      · intro q hq; have := (Finset.mem_filter.mp hq).2.1; linarith
      · intro q1 hq1 q2 hq2 hlt
        rw [Nat.mul_comm q1 1024, Nat.mul_comm q2 1024] at hlt
        exact phiL_sep_1024 N B hNB ((N : ℝ) * β) r q1 q2
          (mem_range.mp (Finset.mem_filter.mp hq1).1) (mem_range.mp (Finset.mem_filter.mp hq2).1) hlt
    calc
      _ ≤ num / (16 * (1024 : ℝ) ^ 2) * (5 + 5) := hsum1.trans (mul_le_mul_of_nonneg_left (add_le_add hR5 hL5) (by positivity))
      _ = (5 / 8 : ℝ) / (1024 : ℝ) ^ 2 * num := by ring
  calc
    _ ≤ ∑ r ∈ range 1024, (5 / 8 : ℝ) / (1024 : ℝ) ^ 2 *
          Complex.normSq ((eigenvalue ((B : ℝ) * β - (r : ℝ) / 1024) - 1) *
            sineW (eigenvalue ((B : ℝ) * β - (r : ℝ) / 1024))) := Finset.sum_le_sum hper_r
    _ = (5 / 8 : ℝ) / (1024 : ℝ) ^ 2 * ∑ r ∈ range 1024,
          Complex.normSq ((eigenvalue ((B : ℝ) * β - (r : ℝ) / 1024) - 1) *
            sineW (eigenvalue ((B : ℝ) * β - (r : ℝ) / 1024))) := by rw [← Finset.mul_sum]
    _ ≤ (5 / 8 : ℝ) / (1024 : ℝ) ^ 2 * (2 * Real.pi ^ 2) :=
          mul_le_mul_of_nonneg_left (sineW_diff_parseval M hM10 β) (by positivity)
    _ ≤ 12 / 1000000 := by
          have hpi : Real.pi < 3141593 / 1000000 := by
            have := Real.pi_lt_d6; norm_num at this ⊢; linarith
          have hpi0 : 0 ≤ Real.pi := Real.pi_pos.le
          nlinarith

/-! ### Part 3: Closed form & small/medium pointwise bounds -/

theorem sineW_closed_form (z : ℂ) (θ : ℝ) (hz : z = eigenvalue θ)
    (hp : Real.sin (Real.pi * (θ + 1 / 2048)) ≠ 0)
    (hm : Real.sin (Real.pi * (θ - 1 / 2048)) ≠ 0) :
    Complex.normSq (sineW z) =
      Real.cos (Real.pi * (1024 * θ)) ^ 2 * Real.sin (Real.pi / 1024) ^ 2 /
        (2 * Real.sin (Real.pi * (θ + 1 / 2048)) ^ 2 * Real.sin (Real.pi * (θ - 1 / 2048)) ^ 2) := by
  set ζ : ℂ := eigenvalue (1 / 2048)
  set ζm : ℂ := eigenvalue (-(1 / 2048))
  have hζp : ζ * z = eigenvalue (θ + 1 / 2048) := by
    rw [hz, ← eigenvalue_add]; congr 1; ring
  have hζm : ζm * z = eigenvalue (θ - 1 / 2048) := by
    rw [hz, ← eigenvalue_add]; congr 1; ring
  have hp_ne : ζ * z ≠ 1 := by
    intro h1
    have h0 := normSq_eigenvalue_sub_one (θ + 1 / 2048)
    rw [← hζp, h1, sub_self, Complex.normSq_zero] at h0
    have : 0 < 4 * Real.sin (Real.pi * (θ + 1 / 2048)) ^ 2 := by
      have := sq_pos_of_ne_zero hp; linarith
    linarith
  have hm_ne : ζm * z ≠ 1 := by
    intro h1
    have h0 := normSq_eigenvalue_sub_one (θ - 1 / 2048)
    rw [← hζm, h1, sub_self, Complex.normSq_zero] at h0
    have : 0 < 4 * Real.sin (Real.pi * (θ - 1 / 2048)) ^ 2 := by
      have := sq_pos_of_ne_zero hm; linarith
    linarith
  have hζ1024 : ζ ^ 1024 = -1 := by
    unfold ζ
    rw [eigenvalue_pow_eq_eigenvalue_mul]
    unfold eigenvalue
    have : Complex.I * ((2 * Real.pi * (((1024 : ℕ) : ℝ) * (1 / 2048)) : ℝ) : ℂ) = (Real.pi : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.exp_pi_mul_I]
  have hζm1024 : ζm ^ 1024 = -1 := by
    unfold ζm
    rw [eigenvalue_pow_eq_eigenvalue_mul]
    unfold eigenvalue
    have : Complex.I * ((2 * Real.pi * (((1024 : ℕ) : ℝ) * (-(1 / 2048))) : ℝ) : ℂ) = -((Real.pi : ℂ) * Complex.I) := by
      push_cast; ring
    rw [this, Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num
  have hW : sineW z = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) *
      ((∑ u ∈ range 1024, (ζ * z) ^ u) - ∑ u ∈ range 1024, (ζm * z) ^ u) := by
    unfold sineW
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    unfold sineWeight ζ ζm
    rw [mul_pow, mul_pow, eigenvalue_pow_eq_eigenvalue_mul, eigenvalue_pow_eq_eigenvalue_mul]
    unfold eigenvalue
    have ha : Complex.I * ((2 * Real.pi * ((u : ℝ) * (1 / 2048)) : ℝ) : ℂ) =
        Complex.I * ((Real.pi * (u : ℝ) / (2 : ℝ) ^ 10 : ℝ) : ℂ) := by push_cast; norm_num; ring
    have hb : Complex.I * ((2 * Real.pi * ((u : ℝ) * (-(1 / 2048))) : ℝ) : ℂ) =
        -(Complex.I * ((Real.pi * (u : ℝ) / (2 : ℝ) ^ 10 : ℝ) : ℂ)) := by push_cast; norm_num; ring
    rw [ha, hb]; ring
  rw [hW, geom_sum_eq hp_ne, geom_sum_eq hm_ne, mul_pow, mul_pow, hζ1024, hζm1024]
  have hcomb : ((-1) * z ^ 1024 - 1) / (ζ * z - 1) - ((-1) * z ^ 1024 - 1) / (ζm * z - 1) =
      (z ^ 1024 + 1) * ((ζ - ζm) * z) / ((ζ * z - 1) * (ζm * z - 1)) := by
    have h1 : ζ * z - 1 ≠ 0 := sub_ne_zero.mpr hp_ne
    have h2 : ζm * z - 1 ≠ 0 := sub_ne_zero.mpr hm_ne
    rw [div_sub_div _ _ h1 h2]; congr 1; ring
  rw [hcomb, Complex.normSq_mul, Complex.normSq_div, Complex.normSq_mul, Complex.normSq_mul,
    Complex.normSq_mul, Complex.normSq_ofReal, ← sq, inv_pow, Real.sq_sqrt (by norm_num)]
  have hz1024 : z ^ 1024 = eigenvalue (1024 * θ) := by
    rw [hz, eigenvalue_pow_eq_eigenvalue_mul]; push_cast; rfl
  have hdiff : Complex.normSq (ζ - ζm) = 4 * Real.sin (Real.pi / 1024) ^ 2 := by
    have hmul : ζ - ζm = ζm * (eigenvalue (1 / 1024) - 1) := by
      unfold ζ ζm
      rw [mul_sub, mul_one, ← eigenvalue_add]
      congr 2; ring
    rw [hmul, Complex.normSq_mul, eigenvalue_normSq, one_mul, normSq_eigenvalue_sub_one,
      show Real.pi * (1 / 1024 : ℝ) = Real.pi / 1024 by ring]
  rw [hz1024, hζp, hζm, hz, eigenvalue_normSq, mul_one, normSq_eigenvalue_add_one, hdiff,
    normSq_eigenvalue_sub_one, normSq_eigenvalue_sub_one]
  ring

/-- Exact closed form of `Complex.normSq (sinePhaseAmplitude M β a)` in terms of `φ = phiR` or `phiL`. -/
theorem sinePhaseAmplitude_closed_form (M : ℕ) (hM : 204 ≤ M) (β : ℝ) (a : ℕ) (φ : ℝ)
    (hlo : 3 / 2 ≤ φ) (hhi : φ ≤ 512)
    (hφ : φ = phiR (2 ^ M) ((2 ^ M : ℕ) * β) a ∨ φ = phiL (2 ^ M) ((2 ^ M : ℕ) * β) a) :
    let N := (2 ^ M : ℕ)
    Complex.normSq (sinePhaseAmplitude M β a) =
      Real.cos (Real.pi * (N : ℝ) * β) ^ 2 * Real.sin (Real.pi / 1024) ^ 2 *
        Real.sin (Real.pi * φ / 1024) ^ 2 /
      (2 * (N : ℝ) ^ 2 * Real.sin (Real.pi * φ / N) ^ 2 *
        Real.sin (Real.pi * (φ + 1 / 2) / 1024) ^ 2 * Real.sin (Real.pi * (φ - 1 / 2) / 1024) ^ 2) := by
  dsimp only
  set N := (2 ^ M : ℕ)
  set B := 2 ^ (M - 10)
  have hM10 : 10 ≤ M := by omega
  have hNpos : 0 < N := pow_pos (by decide) M
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hNB : N = 1024 * B := by
    have : 2 ^ M = 2 ^ 10 * 2 ^ (M - 10) := by rw [← pow_add, Nat.add_sub_cancel' hM10]
    simpa [N, B] using this
  have hNBR : (N : ℝ) = 1024 * (B : ℝ) := by exact_mod_cast hNB
  have hNbig : (1024 : ℝ) ≤ N := by
    have : 1024 ≤ N := by rw [hNB]; exact Nat.le_mul_of_pos_right 1024 (pow_pos (by decide) _)
    exact_mod_cast this
  set θ := (B : ℝ) * (β - (a : ℝ) / N)
  set ω := eigenvalue (β - (a : ℝ) / N)
  have hωB : ω ^ B = eigenvalue θ := by
    unfold ω θ; rw [eigenvalue_pow_eq_eigenvalue_mul]
  -- Relate `1024 * θ = N * β - a` to `± φ` modulo `N` (hence also modulo `1024`)
  have hrel : ∃ sgn : ℝ, (sgn = 1 ∨ sgn = -1) ∧ ∃ k : ℤ,
      (N : ℝ) * β - (a : ℝ) = sgn * φ + (k : ℝ) * (N : ℝ) := by
    rcases hφ with rfl | rfl
    · unfold phiR; split_ifs
      · exact ⟨-1, Or.inr rfl, 0, by ring⟩
      · exact ⟨-1, Or.inr rfl, 1, by ring⟩
    · unfold phiL; split_ifs
      · exact ⟨1, Or.inl rfl, 0, by ring⟩
      · exact ⟨1, Or.inl rfl, -1, by ring⟩
  obtain ⟨sgn, hsgn, k, hrel⟩ := hrel
  have hθ : θ = (sgn * φ) / 1024 + (k * B : ℤ) := by
    unfold θ
    have hB0 : (B : ℝ) ≠ 0 := by positivity
    have : (N : ℝ) * (β - (a : ℝ) / N) = (N : ℝ) * β - (a : ℝ) := by field_simp [hNR.ne']
    have : (1024 : ℝ) * ((B : ℝ) * (β - (a : ℝ) / N)) = sgn * φ + (k : ℝ) * (1024 * (B : ℝ)) := by
      rw [← mul_assoc, ← hNBR, this, hrel, hNBR]
    push_cast; linarith
  have hneg1_sq : ∀ m : ℤ, ((-1 : ℝ) ^ m) ^ 2 = 1 := fun m => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]; norm_num
  have hsin_sq_shift : ∀ (u : ℝ) (m : ℤ), Real.sin (u + (m : ℝ) * Real.pi) ^ 2 = Real.sin u ^ 2 := by
    intro u m
    rw [Real.sin_add_int_mul_pi, mul_pow, hneg1_sq, one_mul]
  have hcos_sq_shift : ∀ (u : ℝ) (m : ℤ), Real.cos (u + (m : ℝ) * Real.pi) ^ 2 = Real.cos u ^ 2 := by
    intro u m
    rw [Real.cos_add_int_mul_pi, mul_pow, hneg1_sq, one_mul]
  have hsinN : Real.sin (Real.pi * (β - (a : ℝ) / N)) ^ 2 = Real.sin (Real.pi * φ / N) ^ 2 := by
    have harg : Real.pi * (β - (a : ℝ) / N) = sgn * (Real.pi * φ / N) + (k : ℝ) * Real.pi := by
      have h1 : (N : ℝ) * (β - (a : ℝ) / N) = sgn * φ + (k : ℝ) * (N : ℝ) := by
        rw [← hrel]; field_simp [hNR.ne']
      have h2 : β - (a : ℝ) / N = sgn * φ / N + (k : ℝ) := by
        field_simp [hNR.ne'] at h1 ⊢; linarith
      rw [h2]; ring
    rw [harg, hsin_sq_shift]
    rcases hsgn with rfl | rfl <;> simp
  have hsinθ : Real.sin (Real.pi * θ) ^ 2 = Real.sin (Real.pi * φ / 1024) ^ 2 := by
    rw [hθ, show Real.pi * (sgn * φ / 1024 + ((k * B : ℤ) : ℝ)) =
      sgn * (Real.pi * φ / 1024) + ((k * B : ℤ) : ℝ) * Real.pi by ring, hsin_sq_shift]
    rcases hsgn with rfl | rfl <;> simp
  have hcos1024 : Real.cos (Real.pi * (1024 * θ)) ^ 2 = Real.cos (Real.pi * (N : ℝ) * β) ^ 2 := by
    have harg : Real.pi * (1024 * θ) = Real.pi * (N : ℝ) * β + (((-(a : ℤ) : ℤ) : ℝ)) * Real.pi := by
      unfold θ
      have : (1024 : ℝ) * ((B : ℝ) * (β - (a : ℝ) / N)) = (N : ℝ) * β - (a : ℝ) := by
        rw [← mul_assoc, ← hNBR]; field_simp [hNR.ne']
      rw [this]; rw [Int.cast_neg, Int.cast_natCast]; ring
    rw [harg, hcos_sq_shift]
  have hsinPM :
      Real.sin (Real.pi * (θ + 1 / 2048)) ^ 2 * Real.sin (Real.pi * (θ - 1 / 2048)) ^ 2 =
      Real.sin (Real.pi * (φ + 1 / 2) / 1024) ^ 2 * Real.sin (Real.pi * (φ - 1 / 2) / 1024) ^ 2 := by
    rw [hθ]
    rw [show Real.pi * (sgn * φ / 1024 + ((k * B : ℤ) : ℝ) + 1 / 2048) =
        Real.pi * (sgn * φ + 1 / 2) / 1024 + ((k * B : ℤ) : ℝ) * Real.pi by ring, hsin_sq_shift]
    rw [show Real.pi * (sgn * φ / 1024 + ((k * B : ℤ) : ℝ) - 1 / 2048) =
        Real.pi * (sgn * φ - 1 / 2) / 1024 + ((k * B : ℤ) : ℝ) * Real.pi by ring, hsin_sq_shift]
    rcases hsgn with rfl | rfl
    · simp
    · have ha : Real.pi * (-1 * φ + 1 / 2) / 1024 = -(Real.pi * (φ - 1 / 2) / 1024) := by ring
      have hb : Real.pi * (-1 * φ - 1 / 2) / 1024 = -(Real.pi * (φ + 1 / 2) / 1024) := by ring
      rw [ha, hb, Real.sin_neg, Real.sin_neg, neg_sq, neg_sq, mul_comm]
  have hpos_p : 0 < Real.sin (Real.pi * (φ + 1 / 2) / 1024) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hpos_m : 0 < Real.sin (Real.pi * (φ - 1 / 2) / 1024) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  have hpos_N : 0 < Real.sin (Real.pi * φ / N) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by
      have h1 : φ / N ≤ 1 / 2 := (div_le_iff₀ hNR).mpr (by linarith)
      have h2 : Real.pi * φ / N = Real.pi * (φ / N) := by ring
      nlinarith [Real.pi_pos])
  have hpm_ne : Real.sin (Real.pi * (θ + 1 / 2048)) ≠ 0 ∧ Real.sin (Real.pi * (θ - 1 / 2048)) ≠ 0 := by
    have hprod_pos : 0 < Real.sin (Real.pi * (θ + 1 / 2048)) ^ 2 * Real.sin (Real.pi * (θ - 1 / 2048)) ^ 2 := by
      rw [hsinPM]; positivity
    constructor
    · intro hz; rw [hz, zero_pow (by decide), zero_mul] at hprod_pos; exact lt_irrefl 0 hprod_pos
    · intro hz; rw [hz, zero_pow (by decide), mul_zero] at hprod_pos; exact lt_irrefl 0 hprod_pos
  have hω_ne : ω ≠ 1 := by
    intro h1
    have h0 := normSq_eigenvalue_sub_one (β - (a : ℝ) / N)
    change Complex.normSq (ω - 1) = _ at h0
    rw [h1, sub_self, Complex.normSq_zero, hsinN] at h0
    have : 0 < 4 * Real.sin (Real.pi * φ / N) ^ 2 := by positivity
    linarith
  have hfac := sinePhaseAmplitude_factor M hM10 β a
  change sinePhaseAmplitude M β a = ((N : ℂ)⁻¹) * sineW (ω ^ B) * geomB B ω at hfac
  rw [hfac, hωB, geomB, geom_sum_eq hω_ne, hωB]
  rw [Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_inv, Complex.normSq_natCast,
    Complex.normSq_div, normSq_eigenvalue_sub_one, normSq_eigenvalue_sub_one,
    sineW_closed_form (eigenvalue θ) θ rfl hpm_ne.1 hpm_ne.2,
    hcos1024, hsinθ, hsinN]
  have hrw_den : 2 * Real.sin (Real.pi * (θ + 1 / 2048)) ^ 2 * Real.sin (Real.pi * (θ - 1 / 2048)) ^ 2 =
      2 * (Real.sin (Real.pi * (φ + 1 / 2) / 1024) ^ 2 * Real.sin (Real.pi * (φ - 1 / 2) / 1024) ^ 2) := by
    rw [mul_assoc, hsinPM]
  rw [hrw_den]
  field_simp [hNR.ne', hpos_N.ne', hpos_p.ne', hpos_m.ne']

/-- Small-range sharp pointwise bound (`3/2 ≤ φ ≤ 17`, `M ≥ 204`). -/
theorem sinePhaseAmplitude_small_bound (M : ℕ) (hM : 204 ≤ M) (β : ℝ) (a : ℕ) (φ : ℝ)
    (hlo : 3 / 2 ≤ φ) (hhi : φ ≤ 17)
    (hφ : φ = phiR (2 ^ M) ((2 ^ M : ℕ) * β) a ∨ φ = phiL (2 ^ M) ((2 ^ M : ℕ) * β) a) :
    Complex.normSq (sinePhaseAmplitude M β a) ≤
      (508 / 10000 : ℝ) * Real.cos (Real.pi * ((2 ^ M : ℕ) : ℝ) * β) ^ 2 / (φ ^ 2 - 1 / 4) ^ 2 := by
  set N := (2 ^ M : ℕ)
  have hNbig : (2 ^ 204 : ℝ) ≤ (N : ℝ) := by
    have : 2 ^ 204 ≤ 2 ^ M := Nat.pow_le_pow_right (by decide) hM
    exact_mod_cast this
  have hNR : (0 : ℝ) < N := by linarith [show (0 : ℝ) < 2 ^ 204 by positivity]
  rw [sinePhaseAmplitude_closed_form M hM β a φ hlo (by linarith) hφ]
  have hpi_lo : (3141592 / 1000000 : ℝ) < Real.pi := by
    have := Real.pi_gt_d6; norm_num at this ⊢; linarith
  have hpi_hi : Real.pi < (3141593 / 1000000 : ℝ) := by
    have := Real.pi_lt_d6; norm_num at this ⊢; linarith
  -- Upper bounds on numerator sines
  have hnum1 : Real.sin (Real.pi / 1024) ^ 2 ≤ (3141593 / 1000000 / 1024 : ℝ) ^ 2 := by
    have h0 : 0 ≤ Real.sin (Real.pi / 1024) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith)
    have hle : Real.sin (Real.pi / 1024) ≤ 3141593 / 1000000 / 1024 :=
      (Real.sin_le (by positivity)).trans (by linarith)
    exact pow_le_pow_left₀ h0 hle 2
  have hnum2 : Real.sin (Real.pi * φ / 1024) ^ 2 ≤ ((3141593 / 1000000 : ℝ) * φ / 1024) ^ 2 := by
    have h0 : 0 ≤ Real.sin (Real.pi * φ / 1024) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith)
    have hle : Real.sin (Real.pi * φ / 1024) ≤ (3141593 / 1000000 : ℝ) * φ / 1024 :=
      (Real.sin_le (by positivity)).trans (by nlinarith)
    exact pow_le_pow_left₀ h0 hle 2
  -- Lower bound on `N * sin(π φ / N)`
  have hNsin : (3141591 / 1000000 : ℝ) * φ ≤ (N : ℝ) * Real.sin (Real.pi * φ / N) := by
    have hu : φ / N ≤ 1 / 2 ^ 20 := by
      rw [div_le_iff₀ hNR]
      have : (2 : ℝ) ^ 20 * 17 ≤ (2 : ℝ) ^ 204 := by norm_num
      nlinarith
    have h := sin_pi_mul_ge_sharp (φ / N) (by positivity) hu
    have hm := mul_le_mul_of_nonneg_left h hNR.le
    rw [show Real.pi * (φ / N) = Real.pi * φ / N by ring] at hm
    calc (3141591 / 1000000 : ℝ) * φ = (N : ℝ) * ((3141591 / 1000000 : ℝ) * (φ / N)) := by
          field_simp [hNR.ne']
      _ ≤ _ := hm
  -- Lower bound on `sin(π u / 1024)` for `0 ≤ u ≤ 35/2`:
  -- `1 - (3.141593 * 17.5 / 1024)^2 / 6 > 99951 / 100000`
  have hsin_small (u : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ 35 / 2) :
      (314005 / 100000 : ℝ) * (u / 1024) ≤ Real.sin (Real.pi * u / 1024) := by
    have hx0 : 0 ≤ Real.pi * u / 1024 := by positivity
    have hx_le : Real.pi * u / 1024 ≤ (3141593 / 1000000 : ℝ) * (35 / 2) / 1024 := by nlinarith
    have hx_ge : (3141592 / 1000000 : ℝ) * (u / 1024) ≤ Real.pi * u / 1024 := by nlinarith
    have hc := sin_ge_cubic (Real.pi * u / 1024) hx0
    have hsq : (Real.pi * u / 1024) ^ 2 ≤ ((3141593 / 1000000 : ℝ) * (35 / 2) / 1024) ^ 2 :=
      pow_le_pow_left₀ hx0 hx_le 2
    have hfac : 1 - (Real.pi * u / 1024) ^ 2 / 6 ≥ 99951 / 100000 := by
      have : ((3141593 / 1000000 : ℝ) * (35 / 2) / 1024) ^ 2 / 6 ≤ 49 / 100000 := by norm_num
      linarith
    have hprod : (Real.pi * u / 1024) * (99951 / 100000 : ℝ) ≤
        Real.pi * u / 1024 - (Real.pi * u / 1024) ^ 3 / 6 := by nlinarith
    have hcoef : (314005 / 100000 : ℝ) ≤ (3141592 / 1000000 : ℝ) * (99951 / 100000 : ℝ) := by norm_num
    nlinarith
  have hsp := hsin_small (φ + 1 / 2) (by linarith) (by linarith)
  have hsm := hsin_small (φ - 1 / 2) (by linarith) (by linarith)
  have hφm : 0 < φ - 1 / 2 := by linarith
  have hden_ge :
      2 * ((3141591 / 1000000 : ℝ) * φ) ^ 2 *
        ((314005 / 100000 : ℝ) * ((φ + 1 / 2) / 1024)) ^ 2 *
        ((314005 / 100000 : ℝ) * ((φ - 1 / 2) / 1024)) ^ 2 ≤
      2 * (N : ℝ) ^ 2 * Real.sin (Real.pi * φ / N) ^ 2 *
        Real.sin (Real.pi * (φ + 1 / 2) / 1024) ^ 2 * Real.sin (Real.pi * (φ - 1 / 2) / 1024) ^ 2 := by
    have h1 : ((3141591 / 1000000 : ℝ) * φ) ^ 2 ≤ (N : ℝ) ^ 2 * Real.sin (Real.pi * φ / N) ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hNsin 2
    have h2 : ((314005 / 100000 : ℝ) * ((φ + 1 / 2) / 1024)) ^ 2 ≤ Real.sin (Real.pi * (φ + 1 / 2) / 1024) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hsp 2
    have h3 : ((314005 / 100000 : ℝ) * ((φ - 1 / 2) / 1024)) ^ 2 ≤ Real.sin (Real.pi * (φ - 1 / 2) / 1024) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hsm 2
    have h12 : 2 * ((3141591 / 1000000 : ℝ) * φ) ^ 2 *
          ((314005 / 100000 : ℝ) * ((φ + 1 / 2) / 1024)) ^ 2 ≤
        2 * ((N : ℝ) ^ 2 * Real.sin (Real.pi * φ / N) ^ 2) *
          Real.sin (Real.pi * (φ + 1 / 2) / 1024) ^ 2 :=
      mul_le_mul (by linarith) h2 (by positivity) (by positivity)
    have h123 := mul_le_mul h12 h3 (by positivity) (by positivity)
    linarith [show 2 * ((N : ℝ) ^ 2 * Real.sin (Real.pi * φ / N) ^ 2) *
        Real.sin (Real.pi * (φ + 1 / 2) / 1024) ^ 2 * Real.sin (Real.pi * (φ - 1 / 2) / 1024) ^ 2 =
      2 * (N : ℝ) ^ 2 * Real.sin (Real.pi * φ / N) ^ 2 *
        Real.sin (Real.pi * (φ + 1 / 2) / 1024) ^ 2 * Real.sin (Real.pi * (φ - 1 / 2) / 1024) ^ 2 by ring]
  have hnum_le :
      Real.cos (Real.pi * (N : ℝ) * β) ^ 2 * Real.sin (Real.pi / 1024) ^ 2 *
        Real.sin (Real.pi * φ / 1024) ^ 2 ≤
      Real.cos (Real.pi * (N : ℝ) * β) ^ 2 * (3141593 / 1000000 / 1024 : ℝ) ^ 2 *
        ((3141593 / 1000000 : ℝ) * φ / 1024) ^ 2 := by
    have h12 := mul_le_mul hnum1 hnum2 (by positivity) (by positivity)
    have := mul_le_mul_of_nonneg_left h12 (sq_nonneg (Real.cos (Real.pi * (N : ℝ) * β)))
    linarith [show Real.cos (Real.pi * (N : ℝ) * β) ^ 2 * (Real.sin (Real.pi / 1024) ^ 2 * Real.sin (Real.pi * φ / 1024) ^ 2) =
      Real.cos (Real.pi * (N : ℝ) * β) ^ 2 * Real.sin (Real.pi / 1024) ^ 2 * Real.sin (Real.pi * φ / 1024) ^ 2 by ring,
      show Real.cos (Real.pi * (N : ℝ) * β) ^ 2 * ((3141593 / 1000000 / 1024 : ℝ) ^ 2 * ((3141593 / 1000000 : ℝ) * φ / 1024) ^ 2) =
      Real.cos (Real.pi * (N : ℝ) * β) ^ 2 * (3141593 / 1000000 / 1024 : ℝ) ^ 2 * ((3141593 / 1000000 : ℝ) * φ / 1024) ^ 2 by ring]
  have hφ_pos : 0 < φ := by linarith
  have hsq_pos : 0 < φ ^ 2 - 1 / 4 := by nlinarith
  have hden_pos : 0 < 2 * ((3141591 / 1000000 : ℝ) * φ) ^ 2 *
      ((314005 / 100000 : ℝ) * ((φ + 1 / 2) / 1024)) ^ 2 *
      ((314005 / 100000 : ℝ) * ((φ - 1 / 2) / 1024)) ^ 2 := by positivity
  refine (div_le_div₀ (by positivity) hnum_le hden_pos hden_ge).trans ?_
  have hsimp :
      Real.cos (Real.pi * (N : ℝ) * β) ^ 2 * (3141593 / 1000000 / 1024 : ℝ) ^ 2 *
        ((3141593 / 1000000 : ℝ) * φ / 1024) ^ 2 /
      (2 * ((3141591 / 1000000 : ℝ) * φ) ^ 2 *
        ((314005 / 100000 : ℝ) * ((φ + 1 / 2) / 1024)) ^ 2 *
        ((314005 / 100000 : ℝ) * ((φ - 1 / 2) / 1024)) ^ 2) =
      ((3141593 / 1000000 : ℝ) ^ 4 / (2 * (3141591 / 1000000 : ℝ) ^ 2 * (314005 / 100000 : ℝ) ^ 4)) *
        Real.cos (Real.pi * (N : ℝ) * β) ^ 2 / (φ ^ 2 - 1 / 4) ^ 2 := by
    have hpm : (φ + 1 / 2) * (φ - 1 / 2) = φ ^ 2 - 1 / 4 := by ring
    have h1 : φ + 1 / 2 ≠ 0 := by linarith
    have h2 : φ - 1 / 2 ≠ 0 := by linarith
    rw [← hpm]
    field_simp [hφ_pos.ne', h1, h2]
  rw [hsimp]
  have hconst : (3141593 / 1000000 : ℝ) ^ 4 /
      (2 * (3141591 / 1000000 : ℝ) ^ 2 * (314005 / 100000 : ℝ) ^ 4) ≤ 508 / 10000 := by norm_num
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hconst (sq_nonneg _)) (sq_nonneg _)

/-- Medium-range pointwise bound (`16 ≤ φ ≤ 512`, `M ≥ 204`). -/
theorem sinePhaseAmplitude_med_bound (M : ℕ) (hM : 204 ≤ M) (β : ℝ) (a : ℕ) (φ : ℝ)
    (hlo : 16 ≤ φ) (hhi : φ ≤ 512)
    (hφ : φ = phiR (2 ^ M) ((2 ^ M : ℕ) * β) a ∨ φ = phiL (2 ^ M) ((2 ^ M : ℕ) * β) a) :
    Complex.normSq (sinePhaseAmplitude M β a) ≤
      (31 / 100 : ℝ) * Real.cos (Real.pi * ((2 ^ M : ℕ) : ℝ) * β) ^ 2 / (φ - 1 / 2) ^ 4 := by
  set N := (2 ^ M : ℕ)
  have hNbig : (2 ^ 204 : ℝ) ≤ (N : ℝ) := by
    have : 2 ^ 204 ≤ 2 ^ M := Nat.pow_le_pow_right (by decide) hM
    exact_mod_cast this
  have hNR : (0 : ℝ) < N := by linarith [show (0 : ℝ) < 2 ^ 204 by positivity]
  rw [sinePhaseAmplitude_closed_form M hM β a φ (by linarith) hhi hφ]
  have hpi_hi : Real.pi < (3141593 / 1000000 : ℝ) := by
    have := Real.pi_lt_d6; norm_num at this ⊢; linarith
  have hnum1 : Real.sin (Real.pi / 1024) ^ 2 ≤ (3141593 / 1000000 / 1024 : ℝ) ^ 2 := by
    have h0 : 0 ≤ Real.sin (Real.pi / 1024) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos])
    exact pow_le_pow_left₀ h0 ((Real.sin_le (by positivity)).trans (by linarith)) 2
  have hnum2 : Real.sin (Real.pi * φ / 1024) ^ 2 ≤ ((3141593 / 1000000 : ℝ) * φ / 1024) ^ 2 := by
    have h0 : 0 ≤ Real.sin (Real.pi * φ / 1024) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [Real.pi_pos])
    exact pow_le_pow_left₀ h0 ((Real.sin_le (by positivity)).trans (by nlinarith)) 2
  have hNsin : (3141591 / 1000000 : ℝ) * φ ≤ (N : ℝ) * Real.sin (Real.pi * φ / N) := by
    have hu : φ / N ≤ 1 / 2 ^ 20 := by
      rw [div_le_iff₀ hNR]
      have : (2 : ℝ) ^ 20 * 512 ≤ (2 : ℝ) ^ 204 := by norm_num
      nlinarith
    have h := sin_pi_mul_ge_sharp (φ / N) (by positivity) hu
    have hm := mul_le_mul_of_nonneg_left h hNR.le
    rw [show Real.pi * (φ / N) = Real.pi * φ / N by ring] at hm
    calc (3141591 / 1000000 : ℝ) * φ = (N : ℝ) * ((3141591 / 1000000 : ℝ) * (φ / N)) := by
          field_simp [hNR.ne']
      _ ≤ _ := hm
  have hsm : 2 * ((φ - 1 / 2) / 1024) ≤ Real.sin (Real.pi * (φ - 1 / 2) / 1024) := by
    rw [show Real.pi * (φ - 1 / 2) / 1024 = Real.pi * ((φ - 1 / 2) / 1024) by ring]
    exact sin_jordan ((φ - 1 / 2) / 1024) (by linarith) (by linarith)
  have hsp : 2 * ((φ - 1 / 2) / 1024) ≤ Real.sin (Real.pi * (φ + 1 / 2) / 1024) := by
    by_cases h512 : φ + 1 / 2 ≤ 512
    · have hj := sin_jordan ((φ + 1 / 2) / 1024) (by linarith) (by linarith)
      rw [show Real.pi * ((φ + 1 / 2) / 1024) = Real.pi * (φ + 1 / 2) / 1024 by ring] at hj
      linarith
    · have hsub : Real.sin (Real.pi * (φ + 1 / 2) / 1024) =
          Real.sin (Real.pi * ((1023.5 - φ) / 1024)) := by
        rw [show Real.pi * (φ + 1 / 2) / 1024 = Real.pi - Real.pi * ((1023.5 - φ) / 1024) by ring,
          Real.sin_pi_sub]
      rw [hsub]
      have hj := sin_jordan ((1023.5 - φ) / 1024) (by linarith) (by linarith)
      linarith
  have hden_ge :
      2 * ((3141591 / 1000000 : ℝ) * φ) ^ 2 *
        (2 * ((φ - 1 / 2) / 1024)) ^ 2 * (2 * ((φ - 1 / 2) / 1024)) ^ 2 ≤
      2 * (N : ℝ) ^ 2 * Real.sin (Real.pi * φ / N) ^ 2 *
        Real.sin (Real.pi * (φ + 1 / 2) / 1024) ^ 2 * Real.sin (Real.pi * (φ - 1 / 2) / 1024) ^ 2 := by
    have h1 : ((3141591 / 1000000 : ℝ) * φ) ^ 2 ≤ (N : ℝ) ^ 2 * Real.sin (Real.pi * φ / N) ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hNsin 2
    have h2 : (2 * ((φ - 1 / 2) / 1024)) ^ 2 ≤ Real.sin (Real.pi * (φ + 1 / 2) / 1024) ^ 2 :=
      pow_le_pow_left₀ (by linarith) hsp 2
    have h3 : (2 * ((φ - 1 / 2) / 1024)) ^ 2 ≤ Real.sin (Real.pi * (φ - 1 / 2) / 1024) ^ 2 :=
      pow_le_pow_left₀ (by linarith) hsm 2
    have h12 : 2 * ((3141591 / 1000000 : ℝ) * φ) ^ 2 * (2 * ((φ - 1 / 2) / 1024)) ^ 2 ≤
        2 * ((N : ℝ) ^ 2 * Real.sin (Real.pi * φ / N) ^ 2) *
          Real.sin (Real.pi * (φ + 1 / 2) / 1024) ^ 2 :=
      mul_le_mul (by linarith) h2 (by positivity) (by positivity)
    have h123 := mul_le_mul h12 h3 (by positivity) (by positivity)
    linarith [show 2 * ((N : ℝ) ^ 2 * Real.sin (Real.pi * φ / N) ^ 2) *
        Real.sin (Real.pi * (φ + 1 / 2) / 1024) ^ 2 * Real.sin (Real.pi * (φ - 1 / 2) / 1024) ^ 2 =
      2 * (N : ℝ) ^ 2 * Real.sin (Real.pi * φ / N) ^ 2 *
        Real.sin (Real.pi * (φ + 1 / 2) / 1024) ^ 2 * Real.sin (Real.pi * (φ - 1 / 2) / 1024) ^ 2 by ring]
  have hnum_le :
      Real.cos (Real.pi * (N : ℝ) * β) ^ 2 * Real.sin (Real.pi / 1024) ^ 2 *
        Real.sin (Real.pi * φ / 1024) ^ 2 ≤
      Real.cos (Real.pi * (N : ℝ) * β) ^ 2 * (3141593 / 1000000 / 1024 : ℝ) ^ 2 *
        ((3141593 / 1000000 : ℝ) * φ / 1024) ^ 2 := by
    have h12 := mul_le_mul hnum1 hnum2 (by positivity) (by positivity)
    have := mul_le_mul_of_nonneg_left h12 (sq_nonneg (Real.cos (Real.pi * (N : ℝ) * β)))
    linarith [show Real.cos (Real.pi * (N : ℝ) * β) ^ 2 * (Real.sin (Real.pi / 1024) ^ 2 * Real.sin (Real.pi * φ / 1024) ^ 2) =
      Real.cos (Real.pi * (N : ℝ) * β) ^ 2 * Real.sin (Real.pi / 1024) ^ 2 * Real.sin (Real.pi * φ / 1024) ^ 2 by ring,
      show Real.cos (Real.pi * (N : ℝ) * β) ^ 2 * ((3141593 / 1000000 / 1024 : ℝ) ^ 2 * ((3141593 / 1000000 : ℝ) * φ / 1024) ^ 2) =
      Real.cos (Real.pi * (N : ℝ) * β) ^ 2 * (3141593 / 1000000 / 1024 : ℝ) ^ 2 * ((3141593 / 1000000 : ℝ) * φ / 1024) ^ 2 by ring]
  have hφ_pos : 0 < φ := by linarith
  have hm_pos : 0 < φ - 1 / 2 := by linarith
  have hden_pos : 0 < 2 * ((3141591 / 1000000 : ℝ) * φ) ^ 2 *
      (2 * ((φ - 1 / 2) / 1024)) ^ 2 * (2 * ((φ - 1 / 2) / 1024)) ^ 2 := by positivity
  refine (div_le_div₀ (by positivity) hnum_le hden_pos hden_ge).trans ?_
  have hsimp :
      Real.cos (Real.pi * (N : ℝ) * β) ^ 2 * (3141593 / 1000000 / 1024 : ℝ) ^ 2 *
        ((3141593 / 1000000 : ℝ) * φ / 1024) ^ 2 /
      (2 * ((3141591 / 1000000 : ℝ) * φ) ^ 2 *
        (2 * ((φ - 1 / 2) / 1024)) ^ 2 * (2 * ((φ - 1 / 2) / 1024)) ^ 2) =
      ((3141593 / 1000000 : ℝ) ^ 4 / (32 * (3141591 / 1000000 : ℝ) ^ 2)) *
        Real.cos (Real.pi * (N : ℝ) * β) ^ 2 / (φ - 1 / 2) ^ 4 := by
    field_simp [hφ_pos.ne', hm_pos.ne']; ring
  rw [hsimp]
  have hconst : (3141593 / 1000000 : ℝ) ^ 4 / (32 * (3141591 / 1000000 : ℝ) ^ 2) ≤ 31 / 100 := by
    norm_num
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hconst (sq_nonneg _)) (by positivity)

/-! ### Part 4: Summing small & medium tails -/

theorem sum_range_inv_fourth (R : ℝ) (hR : 1 < R) (M : ℕ) :
    ∑ k ∈ range M, 1 / (R + k) ^ 4 ≤ 1 / (3 * (R - 1) ^ 3) - 1 / (3 * (R - 1 + M) ^ 3) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ]
    have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    have hx : 1 < R + M := by linarith
    have hstep : 1 / (R + M) ^ 4 ≤
        1 / (3 * (R - 1 + M) ^ 3) - 1 / (3 * (R - 1 + ((M + 1 : ℕ) : ℝ)) ^ 3) := by
      set x := R + M
      have hx1 : 0 < x - 1 := by linarith
      have hx0 : 0 < x := by linarith
      have hre : R - 1 + ((M + 1 : ℕ) : ℝ) = x := by push_cast; dsimp [x]; ring
      have hre2 : R - 1 + M = x - 1 := by dsimp [x]; ring
      rw [hre, hre2, div_sub_div _ _ (by positivity) (by positivity),
        div_le_div_iff₀ (by positivity) (by positivity)]
      have hpoly : (1 * (3 * x ^ 3) - 3 * (x - 1) ^ 3 * 1) * x ^ 4 -
          1 * (3 * (x - 1) ^ 3 * (3 * x ^ 3)) = 3 * x ^ 3 * (6 * x ^ 2 - 8 * x + 3) := by ring
      have hq : 0 < 6 * x ^ 2 - 8 * x + 3 := by nlinarith [sq_nonneg (x - 2 / 3)]
      have hpos : 0 < 3 * x ^ 3 * (6 * x ^ 2 - 8 * x + 3) := mul_pos (by positivity) hq
      linarith
    linarith

theorem sum_inv_fourth_ge (S : Finset ℕ) (φ : ℕ → ℝ) (R : ℝ) (hR : 3 / 2 < R)
    (hφ : ∀ a ∈ S, R ≤ φ a)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, |φ a - φ b| < 1 → a = b) :
    ∑ a ∈ S, 1 / (φ a - 1 / 2) ^ 4 ≤ 1 / (3 * (R - 3 / 2) ^ 3) := by
  set g : ℕ → ℕ := fun a => ⌊φ a - R⌋₊
  have hinj : Set.InjOn g S := by
    intro a ha b hb hab
    have h1 := Nat.floor_le (sub_nonneg.mpr (hφ a ha))
    have h2 := Nat.lt_floor_add_one (φ a - R)
    have h3 := Nat.floor_le (sub_nonneg.mpr (hφ b hb))
    have h4 := Nat.lt_floor_add_one (φ b - R)
    dsimp only [g] at hab; rw [hab] at h1 h2
    exact hsep a ha b hb (abs_lt.mpr ⟨by linarith, by linarith⟩)
  have h1 : ∑ a ∈ S, 1 / (φ a - 1 / 2) ^ 4 ≤ ∑ a ∈ S, 1 / ((R - 1 / 2) + g a) ^ 4 := by
    apply Finset.sum_le_sum; intro a ha
    have hfl : (g a : ℝ) ≤ φ a - R := Nat.floor_le (sub_nonneg.mpr (hφ a ha))
    have h0 : 0 < (R - 1 / 2) + g a := by linarith [Nat.cast_nonneg (α := ℝ) (g a)]
    exact one_div_le_one_div_of_le (pow_pos h0 4) (pow_le_pow_left₀ h0.le (by linarith) 4)
  have h2 : ∑ a ∈ S, 1 / ((R - 1 / 2) + g a) ^ 4 = ∑ k ∈ S.image g, 1 / ((R - 1 / 2) + k) ^ 4 := by
    rw [Finset.sum_image hinj]
  have h3 : ∑ k ∈ S.image g, 1 / ((R - 1 / 2) + k) ^ 4 ≤
      ∑ k ∈ range (S.sup g + 1), 1 / ((R - 1 / 2) + k) ^ 4 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
      exact mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup ha))
    · intro k _ _; positivity
  have h4 := sum_range_inv_fourth (R - 1 / 2) (by linarith) (S.sup g + 1)
  have h5 : 0 ≤ 1 / (3 * (R - 1 / 2 - 1 + ((S.sup g + 1 : ℕ) : ℝ)) ^ 3) := by
    have : (0 : ℝ) ≤ ((S.sup g + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have : 0 < R - 1 / 2 - 1 + ((S.sup g + 1 : ℕ) : ℝ) := by linarith
    positivity
  have hre : R - 1 / 2 - 1 = R - 3 / 2 := by ring
  rw [hre] at h4 h5
  linarith

theorem sum_small_tail (S : Finset ℕ) (φ : ℕ → ℝ) (R : ℝ) (K : ℕ)
    (hR : 1 < R)
    (hφ : ∀ a ∈ S, R ≤ φ a ∧ φ a < R + K)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, |φ a - φ b| < 1 → a = b) :
    ∑ a ∈ S, 1 / (φ a ^ 2 - 1 / 4) ^ 2 ≤ ∑ k ∈ range K, 1 / ((R + k) ^ 2 - 1 / 4) ^ 2 := by
  set g : ℕ → ℕ := fun a => ⌊φ a - R⌋₊
  have hinj : Set.InjOn g S := by
    intro a ha b hb hab
    have h1 := Nat.floor_le (sub_nonneg.mpr (hφ a ha).1)
    have h2 := Nat.lt_floor_add_one (φ a - R)
    have h3 := Nat.floor_le (sub_nonneg.mpr (hφ b hb).1)
    have h4 := Nat.lt_floor_add_one (φ b - R)
    dsimp only [g] at hab; rw [hab] at h1 h2
    exact hsep a ha b hb (abs_lt.mpr ⟨by linarith, by linarith⟩)
  have h1 : ∑ a ∈ S, 1 / (φ a ^ 2 - 1 / 4) ^ 2 ≤ ∑ a ∈ S, 1 / ((R + g a) ^ 2 - 1 / 4) ^ 2 := by
    apply Finset.sum_le_sum; intro a ha
    have hfl : (g a : ℝ) ≤ φ a - R := Nat.floor_le (sub_nonneg.mpr (hφ a ha).1)
    have h0 : 0 < R + g a := by linarith [Nat.cast_nonneg (α := ℝ) (g a)]
    have hpos : 0 < (R + g a) ^ 2 - 1 / 4 := by nlinarith
    have hle : (R + g a) ^ 2 - 1 / 4 ≤ φ a ^ 2 - 1 / 4 := by nlinarith
    exact one_div_le_one_div_of_le (pow_pos hpos 2) (pow_le_pow_left₀ hpos.le hle 2)
  have h2 : ∑ a ∈ S, 1 / ((R + g a) ^ 2 - 1 / 4) ^ 2 =
      ∑ k ∈ S.image g, 1 / ((R + k) ^ 2 - 1 / 4) ^ 2 := by rw [Finset.sum_image hinj]
  have h3 : ∑ k ∈ S.image g, 1 / ((R + k) ^ 2 - 1 / 4) ^ 2 ≤
      ∑ k ∈ range K, 1 / ((R + k) ^ 2 - 1 / 4) ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
      rw [mem_range]
      exact Nat.floor_lt (sub_nonneg.mpr (hφ a ha).1) |>.mpr (by linarith [(hφ a ha).2])
    · intro k _ _; positivity
  linarith

/-- Master two-sided circular mass lower bound for `sinePhaseAmplitude` (`M ≥ 204`). -/
theorem sine_circular_mass_two (M : ℕ) (hM : 204 ≤ M) (β : ℝ)
    (R1 R2 : ℝ) (K1 K2 : ℕ)
    (hR1_lo : 3 / 2 ≤ R1) (hR2_lo : 3 / 2 ≤ R2)
    (hR1_hi : R1 + K1 ≤ 17) (hR2_hi : R2 + K2 ≤ 17)
    (hM1 : 16 ≤ R1 + K1) (hM2 : 16 ≤ R2 + K2) :
    1 - Real.cos (Real.pi * ((2 ^ M : ℕ) : ℝ) * β) ^ 2 *
        ((508 / 10000 : ℝ) *
          ((∑ k ∈ range K1, 1 / ((R1 + k) ^ 2 - 1 / 4) ^ 2) +
           (∑ k ∈ range K2, 1 / ((R2 + k) ^ 2 - 1 / 4) ^ 2)) + 68 / 1000000) -
        12 / 1000000 ≤
      ∑ a ∈ range (2 ^ M),
        if phiR (2 ^ M) ((2 ^ M : ℕ) * β) a < R1 ∨ phiL (2 ^ M) ((2 ^ M : ℕ) * β) a < R2
        then Complex.normSq (sinePhaseAmplitude M β a) else 0 := by
  classical
  set N := 2 ^ M
  set c := ((N : ℕ) : ℝ) * β
  set cs := Real.cos (Real.pi * (N : ℝ) * β) ^ 2
  have hcs0 : 0 ≤ cs := sq_nonneg _
  have hM10 : 10 ≤ M := by omega
  have hM11 : 11 ≤ M := by omega
  let RSs := (range N).filter (fun a => R1 ≤ phiR N c a ∧ phiR N c a < R1 + K1)
  let RSm := (range N).filter (fun a => R1 + K1 ≤ phiR N c a ∧ phiR N c a ≤ 512)
  let LSs := (range N).filter (fun a => R2 ≤ phiL N c a ∧ phiL N c a < R2 + K2)
  let LSm := (range N).filter (fun a => R2 + K2 ≤ phiL N c a ∧ phiL N c a ≤ 512)
  have hRSs : ∑ a ∈ RSs, Complex.normSq (sinePhaseAmplitude M β a) ≤
      (508 / 10000 : ℝ) * cs * ∑ k ∈ range K1, 1 / ((R1 + k) ^ 2 - 1 / 4) ^ 2 := by
    have hpt : ∀ a ∈ RSs, Complex.normSq (sinePhaseAmplitude M β a) ≤
        ((508 / 10000 : ℝ) * cs) * (1 / (phiR N c a ^ 2 - 1 / 4) ^ 2) := by
      intro a ha
      have hd := (Finset.mem_filter.mp ha).2
      have h := sinePhaseAmplitude_small_bound M hM β a (phiR N c a) (by linarith [hd.1])
        (by linarith [hd.2]) (Or.inl rfl)
      linarith [show ((508 / 10000 : ℝ) * cs) * (1 / (phiR N c a ^ 2 - 1 / 4) ^ 2) =
        (508 / 10000 : ℝ) * cs / (phiR N c a ^ 2 - 1 / 4) ^ 2 by ring]
    calc
      _ ≤ ∑ a ∈ RSs, ((508 / 10000 : ℝ) * cs) * (1 / (phiR N c a ^ 2 - 1 / 4) ^ 2) :=
        Finset.sum_le_sum hpt
      _ = ((508 / 10000 : ℝ) * cs) * ∑ a ∈ RSs, 1 / (phiR N c a ^ 2 - 1 / 4) ^ 2 := by
        rw [← Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (sum_small_tail RSs (phiR N c) R1 K1 (by linarith)
          (fun a ha => (Finset.mem_filter.mp ha).2)
          (fun a ha b hb => phiR_sep N c a b (mem_range.mp (Finset.mem_filter.mp ha).1)
            (mem_range.mp (Finset.mem_filter.mp hb).1))) (by positivity)
  have hLSs : ∑ a ∈ LSs, Complex.normSq (sinePhaseAmplitude M β a) ≤
      (508 / 10000 : ℝ) * cs * ∑ k ∈ range K2, 1 / ((R2 + k) ^ 2 - 1 / 4) ^ 2 := by
    have hpt : ∀ a ∈ LSs, Complex.normSq (sinePhaseAmplitude M β a) ≤
        ((508 / 10000 : ℝ) * cs) * (1 / (phiL N c a ^ 2 - 1 / 4) ^ 2) := by
      intro a ha
      have hd := (Finset.mem_filter.mp ha).2
      have h := sinePhaseAmplitude_small_bound M hM β a (phiL N c a) (by linarith [hd.1])
        (by linarith [hd.2]) (Or.inr rfl)
      linarith [show ((508 / 10000 : ℝ) * cs) * (1 / (phiL N c a ^ 2 - 1 / 4) ^ 2) =
        (508 / 10000 : ℝ) * cs / (phiL N c a ^ 2 - 1 / 4) ^ 2 by ring]
    calc
      _ ≤ ∑ a ∈ LSs, ((508 / 10000 : ℝ) * cs) * (1 / (phiL N c a ^ 2 - 1 / 4) ^ 2) :=
        Finset.sum_le_sum hpt
      _ = ((508 / 10000 : ℝ) * cs) * ∑ a ∈ LSs, 1 / (phiL N c a ^ 2 - 1 / 4) ^ 2 := by
        rw [← Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (sum_small_tail LSs (phiL N c) R2 K2 (by linarith)
          (fun a ha => (Finset.mem_filter.mp ha).2)
          (fun a ha b hb => phiL_sep N c a b (mem_range.mp (Finset.mem_filter.mp ha).1)
            (mem_range.mp (Finset.mem_filter.mp hb).1))) (by positivity)
  have hRSm : ∑ a ∈ RSm, Complex.normSq (sinePhaseAmplitude M β a) ≤ (34 / 1000000 : ℝ) * cs := by
    have hpt : ∀ a ∈ RSm, Complex.normSq (sinePhaseAmplitude M β a) ≤
        ((31 / 100 : ℝ) * cs) * (1 / (phiR N c a - 1 / 2) ^ 4) := by
      intro a ha
      have hd := (Finset.mem_filter.mp ha).2
      have h := sinePhaseAmplitude_med_bound M hM β a (phiR N c a) (by linarith [hd.1]) hd.2 (Or.inl rfl)
      linarith [show ((31 / 100 : ℝ) * cs) * (1 / (phiR N c a - 1 / 2) ^ 4) =
        (31 / 100 : ℝ) * cs / (phiR N c a - 1 / 2) ^ 4 by ring]
    have hsum := sum_inv_fourth_ge RSm (phiR N c) 16 (by norm_num)
      (fun a ha => by linarith [(Finset.mem_filter.mp ha).2.1])
      (fun a ha b hb => phiR_sep N c a b (mem_range.mp (Finset.mem_filter.mp ha).1)
        (mem_range.mp (Finset.mem_filter.mp hb).1))
    calc
      _ ≤ ((31 / 100 : ℝ) * cs) * ∑ a ∈ RSm, 1 / (phiR N c a - 1 / 2) ^ 4 := by
        rw [Finset.mul_sum]; exact Finset.sum_le_sum hpt
      _ ≤ ((31 / 100 : ℝ) * cs) * (1 / (3 * (16 - 3 / 2 : ℝ) ^ 3)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ (34 / 1000000 : ℝ) * cs := by
        have : (31 / 100 : ℝ) * (1 / (3 * (16 - 3 / 2 : ℝ) ^ 3)) ≤ 34 / 1000000 := by norm_num
        nlinarith
  have hLSm : ∑ a ∈ LSm, Complex.normSq (sinePhaseAmplitude M β a) ≤ (34 / 1000000 : ℝ) * cs := by
    have hpt : ∀ a ∈ LSm, Complex.normSq (sinePhaseAmplitude M β a) ≤
        ((31 / 100 : ℝ) * cs) * (1 / (phiL N c a - 1 / 2) ^ 4) := by
      intro a ha
      have hd := (Finset.mem_filter.mp ha).2
      have h := sinePhaseAmplitude_med_bound M hM β a (phiL N c a) (by linarith [hd.1]) hd.2 (Or.inr rfl)
      linarith [show ((31 / 100 : ℝ) * cs) * (1 / (phiL N c a - 1 / 2) ^ 4) =
        (31 / 100 : ℝ) * cs / (phiL N c a - 1 / 2) ^ 4 by ring]
    have hsum := sum_inv_fourth_ge LSm (phiL N c) 16 (by norm_num)
      (fun a ha => by linarith [(Finset.mem_filter.mp ha).2.1])
      (fun a ha b hb => phiL_sep N c a b (mem_range.mp (Finset.mem_filter.mp ha).1)
        (mem_range.mp (Finset.mem_filter.mp hb).1))
    calc
      _ ≤ ((31 / 100 : ℝ) * cs) * ∑ a ∈ LSm, 1 / (phiL N c a - 1 / 2) ^ 4 := by
        rw [Finset.mul_sum]; exact Finset.sum_le_sum hpt
      _ ≤ ((31 / 100 : ℝ) * cs) * (1 / (3 * (16 - 3 / 2 : ℝ) ^ 3)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ (34 / 1000000 : ℝ) * cs := by
        have : (31 / 100 : ℝ) * (1 / (3 * (16 - 3 / 2 : ℝ) ^ 3)) ≤ 34 / 1000000 := by norm_num
        nlinarith
  have hfar := sinePhaseAmplitude_far_tail M hM11 β
  have hcov (a : ℕ) :
      (if ¬ (phiR N c a < R1 ∨ phiL N c a < R2) then Complex.normSq (sinePhaseAmplitude M β a) else 0) ≤
      (if R1 ≤ phiR N c a ∧ phiR N c a < R1 + K1 then Complex.normSq (sinePhaseAmplitude M β a) else 0) +
      (if R1 + K1 ≤ phiR N c a ∧ phiR N c a ≤ 512 then Complex.normSq (sinePhaseAmplitude M β a) else 0) +
      (if R2 ≤ phiL N c a ∧ phiL N c a < R2 + K2 then Complex.normSq (sinePhaseAmplitude M β a) else 0) +
      (if R2 + K2 ≤ phiL N c a ∧ phiL N c a ≤ 512 then Complex.normSq (sinePhaseAmplitude M β a) else 0) +
      (if 512 < phiR N c a ∧ 512 < phiL N c a then Complex.normSq (sinePhaseAmplitude M β a) else 0) := by
    have ha0 : 0 ≤ Complex.normSq (sinePhaseAmplitude M β a) := Complex.normSq_nonneg _
    by_cases hb : ¬ (phiR N c a < R1 ∨ phiL N c a < R2)
    · rw [if_pos hb]
      have hr : R1 ≤ phiR N c a := le_of_not_gt (fun h => hb (Or.inl h))
      have hl : R2 ≤ phiL N c a := le_of_not_gt (fun h => hb (Or.inr h))
      by_cases h1 : phiR N c a < R1 + K1
      · rw [if_pos ⟨hr, h1⟩]; split_ifs <;> linarith
      · rw [if_neg (fun h => h1 h.2)]
        by_cases h2 : phiR N c a ≤ 512
        · rw [if_pos ⟨le_of_not_gt h1, h2⟩]; split_ifs <;> linarith
        · rw [if_neg (fun h => h2 h.2)]
          by_cases h3 : phiL N c a < R2 + K2
          · rw [if_pos ⟨hl, h3⟩]; split_ifs <;> linarith
          · rw [if_neg (fun h => h3 h.2)]
            by_cases h4 : phiL N c a ≤ 512
            · rw [if_pos ⟨le_of_not_gt h3, h4⟩]; split_ifs <;> linarith
            · rw [if_neg (fun h => h4 h.2), if_pos ⟨lt_of_not_ge h2, lt_of_not_ge h4⟩]; linarith
    · rw [if_neg hb]; split_ifs <;> linarith
  have hbad : (∑ a ∈ range N,
      if ¬ (phiR N c a < R1 ∨ phiL N c a < R2) then Complex.normSq (sinePhaseAmplitude M β a) else 0) ≤
      cs * ((508 / 10000 : ℝ) *
          ((∑ k ∈ range K1, 1 / ((R1 + k) ^ 2 - 1 / 4) ^ 2) +
           (∑ k ∈ range K2, 1 / ((R2 + k) ^ 2 - 1 / 4) ^ 2)) + 68 / 1000000) + 12 / 1000000 := by
    have hsum := Finset.sum_le_sum (fun a (_ : a ∈ range N) => hcov a)
    simp only [Finset.sum_add_distrib] at hsum
    have h1 := hRSs
    simp only [RSs, Finset.sum_filter] at h1
    have h2 := hRSm
    simp only [RSm, Finset.sum_filter] at h2
    have h3 := hLSs
    simp only [LSs, Finset.sum_filter] at h3
    have h4 := hLSm
    simp only [LSm, Finset.sum_filter] at h4
    linarith
  have htot : (∑ a ∈ range N,
      if phiR N c a < R1 ∨ phiL N c a < R2 then Complex.normSq (sinePhaseAmplitude M β a) else 0) +
    (∑ a ∈ range N,
      if ¬ (phiR N c a < R1 ∨ phiL N c a < R2) then Complex.normSq (sinePhaseAmplitude M β a) else 0) = 1 := by
    rw [← Finset.sum_add_distrib]
    convert sinePhaseAmplitude_parseval M hM10 β using 1
    apply Finset.sum_congr rfl; intro a _; split_ifs <;> ring
  linarith

/-! ### Part 5: Rational small-sum evaluators and Left/Right axis box bounds -/

def smallSumQ : ℕ → ℚ → ℚ
  | 0, _ => 0
  | K + 1, R => smallSumQ K R + 1 / ((R + K) ^ 2 - 1 / 4) ^ 2

theorem smallSum_cast (K : ℕ) (R : ℚ) :
    ∑ k ∈ range K, 1 / (((R : ℝ) + k) ^ 2 - 1 / 4) ^ 2 = ((smallSumQ K R : ℚ) : ℝ) := by
  induction K with
  | zero => simp [smallSumQ]
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, smallSumQ]
    push_cast; rfl

theorem smallSum_antitone (K : ℕ) (R R' : ℝ) (h1 : 1 < R) (hle : R ≤ R') :
    ∑ k ∈ range K, 1 / ((R' + k) ^ 2 - 1 / 4) ^ 2 ≤ ∑ k ∈ range K, 1 / ((R + k) ^ 2 - 1 / 4) ^ 2 := by
  apply Finset.sum_le_sum; intro k _
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hpos : 0 < (R + k) ^ 2 - 1 / 4 := by nlinarith
  have hsq : (R + k) ^ 2 - 1 / 4 ≤ (R' + k) ^ 2 - 1 / 4 := by nlinarith
  exact one_div_le_one_div_of_le (pow_pos hpos 2) (pow_le_pow_left₀ hpos.le hsq 2)

theorem left_box_sum (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    (508 / 10000 : ℝ) *
      ((∑ k ∈ range 14, 1 / ((3 - t + k) ^ 2 - 1 / 4) ^ 2) +
       (∑ k ∈ range 14, 1 / ((2 + t + k) ^ 2 - 1 / 4) ^ 2)) + 68 / 1000000 ≤ 586 / 100000 := by
  have hbox (a b : ℚ) (ha : (a : ℝ) ≤ t) (hb : t ≤ (b : ℝ)) (h1 : (0 : ℚ) ≤ a) (h2 : b ≤ 1 / 2)
      (hcheck : (508 / 10000 : ℚ) * (smallSumQ 14 (3 - b) + smallSumQ 14 (2 + a)) + 68 / 1000000 ≤
        586 / 100000) :
      (508 / 10000 : ℝ) *
        ((∑ k ∈ range 14, 1 / ((3 - t + k) ^ 2 - 1 / 4) ^ 2) +
         (∑ k ∈ range 14, 1 / ((2 + t + k) ^ 2 - 1 / 4) ^ 2)) + 68 / 1000000 ≤ 586 / 100000 := by
    have haR : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast h1
    have hbR : (b : ℝ) ≤ 1 / 2 := by
      have h := Rat.cast_le (K := ℝ).mpr h2; push_cast at h; exact h
    have hA := smallSum_antitone 14 ((3 - b : ℚ) : ℝ) (3 - t) (by push_cast; linarith) (by push_cast; linarith)
    have hB := smallSum_antitone 14 ((2 + a : ℚ) : ℝ) (2 + t) (by push_cast; linarith) (by push_cast; linarith)
    rw [smallSum_cast] at hA hB
    have hR : (508 / 10000 : ℝ) * (((smallSumQ 14 (3 - b) : ℚ) : ℝ) + ((smallSumQ 14 (2 + a) : ℚ) : ℝ)) +
        68 / 1000000 ≤ 586 / 100000 := by
      have h := Rat.cast_le (K := ℝ).mpr hcheck; push_cast at h; exact h
    linarith
  by_cases h1 : t ≤ 1 / 16
  · exact hbox 0 (1 / 16) (by push_cast; linarith) (by push_cast; linarith) (by norm_num) (by norm_num) (by decide +kernel)
  · by_cases h2 : t ≤ 1 / 4
    · exact hbox (1 / 16) (1 / 4) (by push_cast; linarith) (by push_cast; linarith) (by norm_num) (by norm_num) (by decide +kernel)
    · exact hbox (1 / 4) (1 / 2) (by push_cast; linarith) (by push_cast; linarith) (by norm_num) (by norm_num) (by decide +kernel)

def cosUbQ (a : ℚ) : ℚ :=
  let xlo := (3141592 / 1000000 : ℚ) * a
  let xhi := (3141593 / 1000000 : ℚ) * a
  min (1 - xlo ^ 2 / 2 + xhi ^ 4 / 24) ((3141593 / 1000000 : ℚ) * (1 / 2 - a))

theorem cos_le_cosUbQ (a : ℚ) (t : ℝ) (ha0 : (0 : ℚ) ≤ a) (ha : (a : ℝ) ≤ t) (ht : t ≤ 1 / 2) :
    0 ≤ Real.cos (Real.pi * t) ∧ Real.cos (Real.pi * t) ≤ (cosUbQ a : ℝ) := by
  have hpi_lo : (3141592 / 1000000 : ℝ) < Real.pi := by
    have := Real.pi_gt_d6; norm_num at this ⊢; linarith
  have hpi_hi : Real.pi < (3141593 / 1000000 : ℝ) := by
    have := Real.pi_lt_d6; norm_num at this ⊢; linarith
  have haR : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha0
  have hcos0 : 0 ≤ Real.cos (Real.pi * t) :=
    Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  have hanti : Real.cos (Real.pi * t) ≤ Real.cos (Real.pi * (a : ℝ)) := by
    apply Real.strictAntiOn_cos.antitoneOn
    · exact ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
    · exact ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
    · nlinarith [Real.pi_pos]
  refine ⟨hcos0, hanti.trans ?_⟩
  simp only [cosUbQ, Rat.cast_min]
  apply le_min
  · have htay := cos_le_taylor4 (Real.pi * (a : ℝ)) (by positivity)
    have hxlo : (3141592 / 1000000 : ℝ) * (a : ℝ) ≤ Real.pi * (a : ℝ) := by nlinarith
    have hxhi : Real.pi * (a : ℝ) ≤ (3141593 / 1000000 : ℝ) * (a : ℝ) := by nlinarith
    have hsq : ((3141592 / 1000000 : ℝ) * (a : ℝ)) ^ 2 ≤ (Real.pi * (a : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hxlo 2
    have h4 : (Real.pi * (a : ℝ)) ^ 4 ≤ ((3141593 / 1000000 : ℝ) * (a : ℝ)) ^ 4 :=
      pow_le_pow_left₀ (by positivity) hxhi 4
    push_cast; linarith
  · have hlin := cos_le_pi_div_two_sub (Real.pi * (a : ℝ)) (by nlinarith [Real.pi_pos])
    push_cast
    have : Real.pi / 2 - Real.pi * (a : ℝ) = Real.pi * (1 / 2 - (a : ℝ)) := by ring
    nlinarith

theorem right_box_bound (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    Real.cos (Real.pi * t) ^ 2 *
      ((508 / 10000 : ℝ) *
        ((∑ k ∈ range 15, 1 / ((2 - t + k) ^ 2 - 1 / 4) ^ 2) +
         (∑ k ∈ range 14, 1 / ((2 + t + k) ^ 2 - 1 / 4) ^ 2)) + 68 / 1000000) ≤
    136 / 100000 + (900 / 100000 : ℝ) * Real.cos (Real.pi * t) ^ 2 := by
  have hbox (a b : ℚ) (ha : (a : ℝ) ≤ t) (hb : t ≤ (b : ℝ)) (h1 : (0 : ℚ) ≤ a) (h2 : b ≤ 1 / 2)
      (hcheck : ((508 / 10000 : ℚ) * (smallSumQ 15 (2 - b) + smallSumQ 14 (2 + a)) + 68 / 1000000 -
        900 / 100000) * (cosUbQ a) ^ 2 ≤ 136 / 100000) :
      Real.cos (Real.pi * t) ^ 2 *
        ((508 / 10000 : ℝ) *
          ((∑ k ∈ range 15, 1 / ((2 - t + k) ^ 2 - 1 / 4) ^ 2) +
           (∑ k ∈ range 14, 1 / ((2 + t + k) ^ 2 - 1 / 4) ^ 2)) + 68 / 1000000) ≤
      136 / 100000 + (900 / 100000 : ℝ) * Real.cos (Real.pi * t) ^ 2 := by
    have haR : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast h1
    have hbR : (b : ℝ) ≤ 1 / 2 := by
      have h := Rat.cast_le (K := ℝ).mpr h2; push_cast at h; exact h
    have hA := smallSum_antitone 15 ((2 - b : ℚ) : ℝ) (2 - t) (by push_cast; linarith) (by push_cast; linarith)
    have hB := smallSum_antitone 14 ((2 + a : ℚ) : ℝ) (2 + t) (by push_cast; linarith) (by push_cast; linarith)
    rw [smallSum_cast] at hA hB
    set S_hi : ℝ := (508 / 10000 : ℝ) * (((smallSumQ 15 (2 - b) : ℚ) : ℝ) + ((smallSumQ 14 (2 + a) : ℚ) : ℝ)) +
      68 / 1000000
    have hS : (508 / 10000 : ℝ) *
          ((∑ k ∈ range 15, 1 / ((2 - t + k) ^ 2 - 1 / 4) ^ 2) +
           (∑ k ∈ range 14, 1 / ((2 + t + k) ^ 2 - 1 / 4) ^ 2)) + 68 / 1000000 ≤ S_hi := by
      dsimp only [S_hi]; linarith
    have hR : (S_hi - 900 / 100000) * ((cosUbQ a : ℚ) : ℝ) ^ 2 ≤ 136 / 100000 := by
      dsimp only [S_hi]
      have h := Rat.cast_le (K := ℝ).mpr hcheck; push_cast at h; exact h
    have hcos := cos_le_cosUbQ a t h1 ha ht1
    have hcs_le : Real.cos (Real.pi * t) ^ 2 ≤ ((cosUbQ a : ℚ) : ℝ) ^ 2 :=
      pow_le_pow_left₀ hcos.1 hcos.2 2
    by_cases hpos : 0 ≤ S_hi - 900 / 100000
    · nlinarith [sq_nonneg (Real.cos (Real.pi * t))]
    · nlinarith [sq_nonneg (Real.cos (Real.pi * t))]
  by_cases h1 : t ≤ 1 / 24
  · exact hbox 0 (1 / 24) (by push_cast; linarith) (by push_cast; linarith) (by norm_num) (by norm_num) (by decide +kernel)
  · by_cases h2 : t ≤ 2 / 24
    · exact hbox (1 / 24) (2 / 24) (by push_cast; linarith) (by push_cast; linarith) (by norm_num) (by norm_num) (by decide +kernel)
    · by_cases h3 : t ≤ 3 / 24
      · exact hbox (2 / 24) (3 / 24) (by push_cast; linarith) (by push_cast; linarith) (by norm_num) (by norm_num) (by decide +kernel)
      · by_cases h4 : t ≤ 4 / 24
        · exact hbox (3 / 24) (4 / 24) (by push_cast; linarith) (by push_cast; linarith) (by norm_num) (by norm_num) (by decide +kernel)
        · by_cases h5 : t ≤ 5 / 24
          · exact hbox (4 / 24) (5 / 24) (by push_cast; linarith) (by push_cast; linarith) (by norm_num) (by norm_num) (by decide +kernel)
          · by_cases h6 : t ≤ 6 / 24
            · exact hbox (5 / 24) (6 / 24) (by push_cast; linarith) (by push_cast; linarith) (by norm_num) (by norm_num) (by decide +kernel)
            · by_cases h7 : t ≤ 7 / 24
              · exact hbox (6 / 24) (7 / 24) (by push_cast; linarith) (by push_cast; linarith) (by norm_num) (by norm_num) (by decide +kernel)
              · by_cases h8 : t ≤ 8 / 24
                · exact hbox (7 / 24) (8 / 24) (by push_cast; linarith) (by push_cast; linarith) (by norm_num) (by norm_num) (by decide +kernel)
                · by_cases h9 : t ≤ 9 / 24
                  · exact hbox (8 / 24) (9 / 24) (by push_cast; linarith) (by push_cast; linarith) (by norm_num) (by norm_num) (by decide +kernel)
                  · by_cases h10 : t ≤ 10 / 24
                    · exact hbox (9 / 24) (10 / 24) (by push_cast; linarith) (by push_cast; linarith) (by norm_num) (by norm_num) (by decide +kernel)
                    · by_cases h11 : t ≤ 11 / 24
                      · exact hbox (10 / 24) (11 / 24) (by push_cast; linarith) (by push_cast; linarith) (by norm_num) (by norm_num) (by decide +kernel)
                      · exact hbox (11 / 24) (1 / 2) (by push_cast; linarith) (by push_cast; linarith) (by norm_num) (by norm_num) (by decide +kernel)

/-! ### Part 6: Left (`258`) and Right (`204`, 3 shifts) window coverage & main success theorem -/

theorem cos_sq_eq_abs_round (c : ℝ) :
    Real.cos (Real.pi * c) ^ 2 = Real.cos (Real.pi * |c - round c|) ^ 2 := by
  have h1 : Real.pi * c = Real.pi * (c - round c) + (round c : ℝ) * Real.pi := by ring
  have hsq : ((-1 : ℝ) ^ round c) ^ 2 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]; norm_num
  rw [h1, Real.cos_add_int_mul_pi, mul_pow, hsq, one_mul]
  rcases le_or_gt 0 (c - round c) with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, mul_neg, Real.cos_neg]

/-- Left axis (`L = 258`, `4 * r < 2^258`): nearest-numerator coverage bound. -/
theorem sine_left_mass_258 (r n : ℕ) (hn0 : 0 < n) (hnr : n < r) (hrN : 4 * r < 2 ^ 258) :
    1 - Real.cos (Real.pi * ((2 ^ 258 : ℕ) : ℝ) * ((n : ℝ) / r)) ^ 2 * (586 / 100000 : ℝ) -
        12 / 1000000 ≤
      ∑ a ∈ range (2 ^ 258),
        if (2 * r * a + 2 ^ 258) / (2 * 2 ^ 258) = n
        then Complex.normSq (sinePhaseAmplitude 258 ((n : ℝ) / r) a) else 0 := by
  set N := 2 ^ 258
  have hr : 0 < r := by omega
  have hN : 0 < N := pow_pos (by decide) 258
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set β : ℝ := (n : ℝ) / r
  set c : ℝ := (N : ℝ) * β
  set L : ℝ := (N : ℝ) / (2 * r)
  have hcr : c * r = N * n := by dsimp only [c, β]; field_simp [hrR.ne']
  have hLr : L * (2 * r) = N := by dsimp only [L]; field_simp [hrR.ne']
  have hL2 : 2 < L := by
    have : 4 * (r : ℝ) < N := by exact_mod_cast hrN
    nlinarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  have hnr' : (n : ℝ) + 1 ≤ r := by exact_mod_cast hnr
  have hc2L : 2 * L ≤ c := by nlinarith
  have hcN : c ≤ N - 2 * L := by nlinarith
  set m : ℤ := round c
  set σ : ℝ := c - m
  have hσ : |σ| ≤ 1 / 2 := abs_sub_round c
  have hσ1 := (abs_le.mp hσ).1
  have hσ2 := (abs_le.mp hσ).2
  set R1 : ℝ := if 0 ≤ σ then 3 - σ else 2 - σ
  set R2 : ℝ := if 0 ≤ σ then 2 + σ else 3 + σ
  have hR_sum :
      (508 / 10000 : ℝ) *
        ((∑ k ∈ range 14, 1 / ((R1 + k) ^ 2 - 1 / 4) ^ 2) +
         (∑ k ∈ range 14, 1 / ((R2 + k) ^ 2 - 1 / 4) ^ 2)) + 68 / 1000000 ≤ 586 / 100000 := by
    by_cases hs : 0 ≤ σ
    · simp only [R1, R2, if_pos hs]
      exact left_box_sum σ hs hσ2
    · simp only [R1, R2, if_neg hs]
      have hL := left_box_sum (-σ) (by linarith) (by linarith)
      have he1 : 3 - -σ = 3 + σ := by ring
      have he2 : 2 + -σ = 2 - σ := by ring
      rw [he1, he2, add_comm (∑ k ∈ range 14, 1 / ((3 + σ + ↑k) ^ 2 - 1 / 4) ^ 2)] at hL
      exact hL
  have hcirc := sine_circular_mass_two 258 (by decide) β R1 R2 14 14
    (by unfold R1; split_ifs <;> linarith)
    (by unfold R2; split_ifs <;> linarith)
    (by unfold R1; push_cast; split_ifs <;> linarith)
    (by unfold R2; push_cast; split_ifs <;> linarith)
    (by unfold R1; push_cast; split_ifs <;> linarith)
    (by unfold R2; push_cast; split_ifs <;> linarith)
  have hweak :
      1 - Real.cos (Real.pi * (N : ℝ) * β) ^ 2 * (586 / 100000 : ℝ) - 12 / 1000000 ≤
      ∑ a ∈ range N,
        if phiR N c a < R1 ∨ phiL N c a < R2
        then Complex.normSq (sinePhaseAmplitude 258 β a) else 0 := by
    have hm := mul_le_mul_of_nonneg_left hR_sum (sq_nonneg (Real.cos (Real.pi * (N : ℝ) * β)))
    change 1 - Real.cos (Real.pi * (N : ℝ) * β) ^ 2 * _ - _ ≤
      ∑ a ∈ range N, if phiR N c a < R1 ∨ phiL N c a < R2
      then Complex.normSq (sinePhaseAmplitude 258 β a) else 0 at hcirc
    linarith
  refine hweak.trans (Finset.sum_le_sum (fun a ha => ?_))
  have haN : (a : ℝ) < N := by exact_mod_cast (mem_range.mp ha)
  have hgood : (phiR N c a < R1 ∨ phiL N c a < R2) → (2 * r * a + N) / (2 * N) = n := by
    intro hnear
    by_contra hbad
    rcases window_cases r N n a hN hbad with h | h
    · have h' : (2 * N * n + N : ℝ) ≤ 2 * r * a := by exact_mod_cast h
      have hca : c + L ≤ (a : ℝ) := by nlinarith
      have hpr : R1 ≤ phiR N c a := by
        unfold phiR
        rw [if_pos (by linarith)]
        by_cases hs : 0 ≤ σ
        · simp only [R1, if_pos hs]
          have hgt : (m : ℝ) + 2 < (a : ℝ) := by linarith
          have hZ : m + 2 < (a : ℤ) := by exact_mod_cast hgt
          have hZ' : (m : ℝ) + 3 ≤ (a : ℝ) := by exact_mod_cast (show m + 3 ≤ (a : ℤ) by omega)
          linarith
        · simp only [R1, if_neg hs]
          have hgt : (m : ℝ) + 1 < (a : ℝ) := by linarith
          have hZ : m + 1 < (a : ℤ) := by exact_mod_cast hgt
          have hZ' : (m : ℝ) + 2 ≤ (a : ℝ) := by exact_mod_cast (show m + 2 ≤ (a : ℤ) by omega)
          linarith
      have hpl : R2 ≤ phiL N c a := by
        unfold phiL
        rw [if_neg (by linarith)]
        unfold R2; split_ifs <;> linarith
      rcases hnear with hn | hn <;> linarith
    · have h' : (2 * r * a + N : ℝ) < 2 * N * n := by exact_mod_cast h
      have hca : (a : ℝ) < c - L := by nlinarith
      have hpl : R2 ≤ phiL N c a := by
        unfold phiL
        rw [if_pos (by linarith)]
        by_cases hs : 0 ≤ σ
        · simp only [R2, if_pos hs]
          have hlt : (a : ℝ) < (m : ℝ) - 1 := by linarith
          have hZ : (a : ℤ) < m - 1 := by exact_mod_cast hlt
          have hZ' : (a : ℝ) ≤ (m : ℝ) - 2 := by exact_mod_cast (show (a : ℤ) ≤ m - 2 by omega)
          linarith
        · simp only [R2, if_neg hs]
          have hlt : (a : ℝ) < (m : ℝ) - 2 := by linarith
          have hZ : (a : ℤ) < m - 2 := by exact_mod_cast hlt
          have hZ' : (a : ℝ) ≤ (m : ℝ) - 3 := by exact_mod_cast (show (a : ℤ) ≤ m - 3 by omega)
          linarith
      have hpr : R1 ≤ phiR N c a := by
        unfold phiR
        rw [if_neg (by linarith)]
        unfold R1; split_ifs <;> linarith
      rcases hnear with hn | hn <;> linarith
  split_ifs with hn hg
  · exact le_rfl
  · exact (hg (hgood hn)).elim
  · exact Complex.normSq_nonneg _
  · exact le_rfl

/-- Modular 204-bit neighbour word `b + j (mod 2^204)`. -/
def neighborWord204 (b : ℕ) (j : ℤ) : ℕ := ((((b : ℤ) + j) % (2 ^ 204 : ℕ))).toNat

def rightGood3 (r : ℕ) (k : Fin r) (b : Fin (2 ^ 204)) : Prop :=
  ∃ j : ℤ, -1 ≤ j ∧ j ≤ 1 ∧ neighborWord204 b.val j = (reducedPeak r 204 k).val

theorem neighbor_coverage3 (r : ℕ) (hr : 0 < r) (k : Fin r) (b : Fin (2 ^ 204))
    (hc : phiR (2 ^ 204) (((2 ^ 204 : ℕ) : ℝ) * ((k.val : ℝ) / r)) b.val <
        2 - (((2 ^ 204 : ℕ) : ℝ) * ((k.val : ℝ) / r) - round (((2 ^ 204 : ℕ) : ℝ) * ((k.val : ℝ) / r))) ∨
      phiL (2 ^ 204) (((2 ^ 204 : ℕ) : ℝ) * ((k.val : ℝ) / r)) b.val <
        2 + (((2 ^ 204 : ℕ) : ℝ) * ((k.val : ℝ) / r) - round (((2 ^ 204 : ℕ) : ℝ) * ((k.val : ℝ) / r)))) :
    rightGood3 r k b := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  set c : ℝ := ((2 ^ 204 : ℕ) : ℝ) * ((k.val : ℝ) / r)
  set m : ℤ := round c
  have hround := abs_le.mp (abs_sub_round c)
  have hkr : (k.val : ℝ) / r < 1 := (div_lt_one hrR).mpr (by exact_mod_cast k.isLt)
  have hc0 : 0 ≤ c := by positivity
  have hcN : c < ((2 ^ 204 : ℕ) : ℝ) := by
    have : (0 : ℝ) < ((2 ^ 204 : ℕ) : ℝ) := by positivity
    dsimp only [c]; nlinarith
  have hb0 : (0 : ℝ) ≤ (b.val : ℝ) := Nat.cast_nonneg _
  have hbN : (b.val : ℝ) < ((2 ^ 204 : ℕ) : ℝ) := by exact_mod_cast b.isLt
  obtain ⟨z, hz1, hz2⟩ : ∃ z : ℤ, (-2 : ℝ) < (m : ℝ) - ((b.val : ℝ) + z * ((2 ^ 204 : ℕ) : ℝ)) ∧
      (m : ℝ) - ((b.val : ℝ) + z * ((2 ^ 204 : ℕ) : ℝ)) < 2 := by
    rcases hc with hc | hc
    · unfold phiR at hc
      split_ifs at hc with h
      · exact ⟨0, by simp only [Int.cast_zero, zero_mul, add_zero]; linarith,
          by simp only [Int.cast_zero, zero_mul, add_zero]; linarith⟩
      · exact ⟨1, by simp only [Int.cast_one, one_mul]; linarith,
          by simp only [Int.cast_one, one_mul]; linarith⟩
    · unfold phiL at hc
      split_ifs at hc with h
      · exact ⟨0, by simp only [Int.cast_zero, zero_mul, add_zero]; linarith,
          by simp only [Int.cast_zero, zero_mul, add_zero]; linarith⟩
      · exact ⟨-1, by simp only [Int.cast_neg, Int.cast_one, neg_one_mul]; linarith,
          by simp only [Int.cast_neg, Int.cast_one, neg_one_mul]; linarith⟩
  set j : ℤ := m - ((b.val : ℤ) + z * ((2 ^ 204 : ℕ) : ℤ))
  have hjR : (j : ℝ) = (m : ℝ) - ((b.val : ℝ) + z * ((2 ^ 204 : ℕ) : ℝ)) := by
    dsimp only [j]; push_cast; ring
  have hj1 : (-2 : ℤ) < j := by exact_mod_cast (show (-2 : ℝ) < (j : ℝ) by rw [hjR]; exact hz1)
  have hj2 : j < 2 := by exact_mod_cast (show (j : ℝ) < 2 by rw [hjR]; exact hz2)
  refine ⟨j, by omega, by omega, ?_⟩
  have he : m = (reducedPeakRaw r 204 k : ℤ) := by
    have hc' : c = ((2 ^ 204 * k.val : ℕ) : ℝ) / r := by dsimp only [c]; push_cast; ring
    rw [show m = round c from rfl, hc', ShorECDLP.Entrant.RoundedReadout.round_nat_ratio _ r hr]
    simp only [reducedPeakRaw, Nat.mul_assoc]
  have hmod : (reducedPeakRaw r 204 k : ℤ) % (2 ^ 204 : ℕ) = ((b.val : ℤ) + j) % (2 ^ 204 : ℕ) := by
    rw [← he]
    dsimp only [j]
    rw [show (b.val : ℤ) + (m - ((b.val : ℤ) + z * ((2 ^ 204 : ℕ) : ℤ))) =
      m + (-z) * ((2 ^ 204 : ℕ) : ℤ) by ring, Int.add_mul_emod_self_right]
  have ht := congrArg Int.toNat hmod
  simpa only [neighborWord204, reducedPeak, ← Int.natCast_mod, Int.toNat_natCast] using ht.symm

def sineRightMass3 (r : ℕ) (k : Fin r) : ℝ := by
  classical
  exact ∑ b : Fin (2 ^ 204), if rightGood3 r k b then
    Complex.normSq (sinePhaseAmplitude 204 ((k.val : ℝ) / r) b.val) else 0

theorem sine_right_mass_204 (r : ℕ) (hr : 0 < r) (k : Fin r) :
    1 - 136 / 100000 - (900 / 100000 : ℝ) * Real.cos (Real.pi * ((2 ^ 204 : ℕ) : ℝ) * ((k.val : ℝ) / r)) ^ 2 -
        12 / 1000000 ≤ sineRightMass3 r k := by
  classical
  set β : ℝ := (k.val : ℝ) / r
  set c : ℝ := ((2 ^ 204 : ℕ) : ℝ) * β
  set σ : ℝ := c - round c
  have hσ := abs_le.mp (abs_sub_round c)
  have hcos_eq : Real.cos (Real.pi * ((2 ^ 204 : ℕ) : ℝ) * β) ^ 2 = Real.cos (Real.pi * |σ|) ^ 2 := by
    rw [mul_assoc]; exact cos_sq_eq_abs_round c
  have hstep :
      1 - 136 / 100000 - (900 / 100000 : ℝ) * Real.cos (Real.pi * ((2 ^ 204 : ℕ) : ℝ) * β) ^ 2 -
        12 / 1000000 ≤
      ∑ b ∈ range (2 ^ 204),
        if phiR (2 ^ 204) c b < 2 - σ ∨ phiL (2 ^ 204) c b < 2 + σ
        then Complex.normSq (sinePhaseAmplitude 204 β b) else 0 := by
    by_cases hs : 0 ≤ σ
    · have hcirc := sine_circular_mass_two 204 (by decide) β (2 - σ) (2 + σ) 15 14
        (by linarith) (by linarith) (by push_cast; linarith) (by push_cast; linarith)
        (by push_cast; linarith) (by push_cast; linarith)
      have hbox := right_box_bound σ hs hσ.2
      rw [hcos_eq, abs_of_nonneg hs] at hcirc ⊢
      change _ ≤ ∑ b ∈ range (2 ^ 204),
        if phiR (2 ^ 204) c b < 2 - σ ∨ phiL (2 ^ 204) c b < 2 + σ
        then Complex.normSq (sinePhaseAmplitude 204 β b) else 0 at hcirc
      linarith
    · have hcirc := sine_circular_mass_two 204 (by decide) β (2 - σ) (2 + σ) 14 15
        (by linarith) (by linarith) (by push_cast; linarith) (by push_cast; linarith)
        (by push_cast; linarith) (by push_cast; linarith)
      have hbox := right_box_bound (-σ) (by linarith) (by linarith)
      rw [hcos_eq, abs_of_neg (lt_of_not_ge hs)] at hcirc ⊢
      have he1 : 2 - -σ = 2 + σ := by ring
      have he2 : 2 + -σ = 2 - σ := by ring
      rw [he1, he2, add_comm (∑ k ∈ range 15, 1 / ((2 + σ + ↑k) ^ 2 - 1 / 4) ^ 2)] at hbox
      change _ ≤ ∑ b ∈ range (2 ^ 204),
        if phiR (2 ^ 204) c b < 2 - σ ∨ phiL (2 ^ 204) c b < 2 + σ
        then Complex.normSq (sinePhaseAmplitude 204 β b) else 0 at hcirc
      linarith
  have hfin :
      ∑ b ∈ range (2 ^ 204),
        (if phiR (2 ^ 204) c b < 2 - σ ∨ phiL (2 ^ 204) c b < 2 + σ
        then Complex.normSq (sinePhaseAmplitude 204 β b) else 0) =
      ∑ b : Fin (2 ^ 204),
        if phiR (2 ^ 204) c b.val < 2 - σ ∨ phiL (2 ^ 204) c b.val < 2 + σ
        then Complex.normSq (sinePhaseAmplitude 204 β b.val) else 0 :=
    (Fin.sum_univ_eq_sum_range (fun b =>
      if phiR (2 ^ 204) c b < 2 - σ ∨ phiL (2 ^ 204) c b < 2 + σ
      then Complex.normSq (sinePhaseAmplitude 204 β b) else 0) (2 ^ 204)).symm
  rw [hfin] at hstep
  refine hstep.trans (Finset.sum_le_sum (fun b _ => ?_))
  dsimp only [sineRightMass3]
  split_ifs with hnear hgood
  · exact le_rfl
  · exact (hgood (neighbor_coverage3 r hr k b hnear)).elim
  · exact Complex.normSq_nonneg _
  · exact le_rfl

def params258 : DecoderParams := ⟨258, 204, by decide, by decide, by decide, by decide⟩

def pairRecovered258 (d a b : ℕ) : Bool :=
  decide (∃ i : Fin 3, (d : ZMod order) ∈ fixedCandidates params258 a (neighborWord204 b ((i.val : ℤ) - 1)))

theorem pairRecovered258_of_character (d : ℕ) (k : Fin order) (hk : k.val ≠ 0)
    (a : Fin (2 ^ 258)) (b : Fin (2 ^ 204))
    (ha : ShorECDLP.Quantum.OrderFinding.nearestNumerator order 258 a.val = k.val)
    (hb : rightGood3 order ⟨d * k.val % order, Nat.mod_lt _ order_prime.pos⟩ b) :
    pairRecovered258 d a.val b.val = true := by
  classical
  obtain ⟨j, hlo, hhi, hj⟩ := hb
  let i : Fin 3 := ⟨(j + 1).toNat, by omega⟩
  have hi : (i.val : ℤ) - 1 = j := by dsimp [i]; omega
  haveI : Fact (Nat.Prime order) := ⟨order_prime⟩
  have hk0 : ((k.val : ℕ) : ZMod order) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    exact hk (Nat.eq_zero_of_dvd_of_lt h k.isLt)
  apply decide_eq_true
  refine ⟨i, ?_⟩
  rw [hi]
  unfold fixedCandidates
  apply Finset.mem_image.mpr
  refine ⟨d * k.val % order, ?_, ?_⟩
  · change d * k.val % order ∈ wrappedNumeratorCandidates order 204 (neighborWord204 b.val j)
    rw [hj]
    exact reducedPeak_mem_candidates order 204 _
  · change ((d * k.val % order : ℕ) : ZMod order) *
        (ShorECDLP.Quantum.OrderFinding.nearestNumerator order 258 a.val : ZMod order)⁻¹ = d
    rw [ha]
    simp only [ZMod.natCast_mod, Nat.cast_mul]
    field_simp

theorem precision258 : 4 * order < 2 ^ 258 := by norm_num [order]

theorem order_not_dvd_pow2 (k : ℕ) : ¬ order ∣ 2 ^ k := by
  intro h
  have h2 := order_prime.dvd_of_dvd_pow h
  have hlt : 2 < order := by norm_num [order]
  exact (Nat.le_of_dvd (by decide) h2).not_gt hlt

theorem order_not_dvd_of_ne_zero (Q : Point) (d : ℕ) (hn : Q ≠ 0) (hd : Q = d • G) :
    ¬ order ∣ d := by
  rintro ⟨m, rfl⟩
  apply hn
  rw [hd, mul_comm, mul_smul, generator_nsmul_eq_zero, nsmul_zero]

/-- Main ideal recovery lower bound (`≥ 9911 / 10000`) for the 10-bit sine-windowed `(258, 204, K=3)` circuit. -/
theorem sine_pair_success (Q : Point) (d : ℕ) (hn : Q ≠ 0) (hd : Q = d • G) :
    (9911 / 10000 : ℝ) ≤ ∑ a : Fin (2 ^ 258), ∑ b : Fin (2 ^ 204),
      if pairRecovered258 d a.val b.val then sinePairMass order 258 204 d (a, b) else 0 := by
  classical
  let r := order
  have hr : r.Prime := order_prime
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr.pos
  have hrinv : (0 : ℝ) ≤ (r : ℝ)⁻¹ := by positivity
  let A : Fin r → Fin (2 ^ 258) → ℝ := fun k a =>
    Complex.normSq (sinePhaseAmplitude 258 ((k.val : ℝ) / r) a.val)
  let B : Fin r → Fin (2 ^ 204) → ℝ := fun k b =>
    Complex.normSq (sinePhaseAmplitude 204 (((d * k.val % r : ℕ) : ℝ) / r) b.val)
  let good : Fin r → Fin (2 ^ 258) → Fin (2 ^ 204) → Prop := fun k a b =>
    k.val ≠ 0 ∧ ShorECDLP.Quantum.OrderFinding.nearestNumerator r 258 a.val = k.val ∧
      rightGood3 r ⟨d * k.val % r, Nat.mod_lt _ hr.pos⟩ b
  let F : Fin r → Fin (2 ^ 258) → Fin (2 ^ 204) → ℝ := fun k a b =>
    if good k a b then A k a * B k b else 0
  let cL : Fin r → ℝ := fun k => Real.cos (Real.pi * ((2 ^ 258 : ℕ) : ℝ) * ((k.val : ℝ) / r)) ^ 2
  let cR : Fin r → ℝ := fun k =>
    Real.cos (Real.pi * ((2 ^ 204 : ℕ) : ℝ) * (((d * k.val % r : ℕ) : ℝ) / r)) ^ 2
  have step1 :
      ∑ a : Fin (2 ^ 258), ∑ b : Fin (2 ^ 204), (r : ℝ)⁻¹ * ∑ k : Fin r, F k a b ≤
        ∑ a : Fin (2 ^ 258), ∑ b : Fin (2 ^ 204),
          if pairRecovered258 d a.val b.val then sinePairMass r 258 204 d (a, b) else 0 := by
    apply Finset.sum_le_sum; intro a _
    apply Finset.sum_le_sum; intro b _
    by_cases hp : pairRecovered258 d a.val b.val = true
    · rw [if_pos hp]
      unfold sinePairMass
      apply mul_le_mul_of_nonneg_left _ hrinv
      apply Finset.sum_le_sum; intro k _
      dsimp only [F, A, B]
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
    · rw [if_neg hp]
      have hz : ∀ k, F k a b = 0 := by
        intro k; dsimp only [F]; rw [if_neg]
        rintro ⟨hk, ha, hb⟩
        exact hp (pairRecovered258_of_character d k hk a b ha hb)
      simp [hz]
  have step2 :
      (r : ℝ)⁻¹ * ∑ k : Fin r, ∑ a : Fin (2 ^ 258), ∑ b : Fin (2 ^ 204), F k a b =
        ∑ a : Fin (2 ^ 258), ∑ b : Fin (2 ^ 204), (r : ℝ)⁻¹ * ∑ k : Fin r, F k a b := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro a _
    rw [Finset.sum_comm]
  have step3 (k : Fin r) :
      (if k.val = 0 then (0 : ℝ) else (1 - 24 / 1000000 - 136 / 100000 : ℝ)) -
        cL k * (586 / 100000) - cR k * (900 / 100000) ≤
      ∑ a : Fin (2 ^ 258), ∑ b : Fin (2 ^ 204), F k a b := by
    have hcL0 : 0 ≤ cL k := sq_nonneg _
    have hcR0 : 0 ≤ cR k := sq_nonneg _
    have hcL1 : cL k ≤ 1 := Real.cos_sq_le_one _
    have hcR1 : cR k ≤ 1 := Real.cos_sq_le_one _
    by_cases hk : k.val = 0
    · rw [if_pos hk]
      have h0 : 0 ≤ ∑ a : Fin (2 ^ 258), ∑ b : Fin (2 ^ 204), F k a b :=
        Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => by
          dsimp only [F, A, B]; split_ifs
          · exact mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
          · exact le_rfl))
      linarith
    · rw [if_neg hk]
      have he : (∑ a : Fin (2 ^ 258), ∑ b : Fin (2 ^ 204), F k a b) =
          (∑ a : Fin (2 ^ 258), if ShorECDLP.Quantum.OrderFinding.nearestNumerator r 258 a.val = k.val then A k a else 0) *
            sineRightMass3 r ⟨d * k.val % r, Nat.mod_lt _ hr.pos⟩ := by
        rw [sineRightMass3, Finset.sum_mul_sum]
        apply Finset.sum_congr rfl; intro a _
        apply Finset.sum_congr rfl; intro b _
        dsimp only [F, good, B]
        rw [ite_zero_mul_ite_zero]
        simp only [hk, ne_eq, not_false_eq_true, true_and]
      rw [he]
      have hleft : 1 - cL k * (586 / 100000) - 12 / 1000000 ≤
          ∑ a : Fin (2 ^ 258), if ShorECDLP.Quantum.OrderFinding.nearestNumerator r 258 a.val = k.val then A k a else 0 := by
        have h := sine_left_mass_258 r k.val (Nat.pos_of_ne_zero hk) k.isLt precision258
        dsimp only [A, cL]
        rw [Fin.sum_univ_eq_sum_range (fun a => if ShorECDLP.Quantum.OrderFinding.nearestNumerator r 258 a = k.val then
          Complex.normSq (sinePhaseAmplitude 258 ((k.val : ℝ) / r) a) else 0) (2 ^ 258)]
        simpa only [ShorECDLP.Quantum.OrderFinding.nearestNumerator] using h
      have hright : 1 - (136 / 100000 + cR k * (900 / 100000)) - 12 / 1000000 ≤
          sineRightMass3 r ⟨d * k.val % r, Nat.mod_lt _ hr.pos⟩ := by
        have h := sine_right_mass_204 r hr.pos ⟨d * k.val % r, Nat.mod_lt _ hr.pos⟩
        dsimp only [cR]; linarith
      have hp := prod_lower
        (∑ a : Fin (2 ^ 258), if ShorECDLP.Quantum.OrderFinding.nearestNumerator r 258 a.val = k.val then A k a else 0)
        (sineRightMass3 r ⟨d * k.val % r, Nat.mod_lt _ hr.pos⟩)
        (cL k * (586 / 100000)) (136 / 100000 + cR k * (900 / 100000))
        (12 / 1000000)
        (mul_nonneg hcL0 (by norm_num))
        (by linarith [hcR0])
        (by norm_num)
        hleft hright (by linarith [hcL1]) (by linarith [hcR1])
      linarith
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => step3 k)
  have hcount : (∑ k : Fin r, if k.val = 0 then (0 : ℝ) else (1 - 24 / 1000000 - 136 / 100000 : ℝ)) =
      ((r : ℝ) - 1) * (1 - 24 / 1000000 - 136 / 100000) := by
    have hz : (∑ k : Fin r, if k.val = 0 then (1 : ℝ) else 0) = 1 := by
      rw [Fin.sum_univ_eq_sum_range (fun k => if k = 0 then (1 : ℝ) else 0)]
      simp [hr.pos]
    calc
      _ = ∑ k : Fin r, ((1 - 24 / 1000000 - 136 / 100000 : ℝ) -
            (1 - 24 / 1000000 - 136 / 100000) * (if k.val = 0 then 1 else 0)) := by
        apply Finset.sum_congr rfl; intro k _; split_ifs <;> ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hz]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        ring
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hcount, ← Finset.sum_mul, ← Finset.sum_mul] at hsum
  have hcL_sum : ∑ k : Fin r, cL k = (r : ℝ) / 2 := by
    have h := sum_cos_sq_eq r (2 ^ 258) hr.pos (order_not_dvd_pow2 258)
    simpa only [cL, mul_div_assoc] using h
  have hcR_sum : ∑ k : Fin r, cR k = (r : ℝ) / 2 := by
    have hndvd : ¬ r ∣ 2 ^ 204 * d := by
      intro h
      rcases hr.dvd_mul.mp h with h1 | h2
      · exact order_not_dvd_pow2 204 h1
      · exact order_not_dvd_of_ne_zero Q d hn hd h2
    have h := sum_cos_sq_eq r (2 ^ 204 * d) hr.pos hndvd
    rw [← h]
    apply Finset.sum_congr rfl; intro k _
    dsimp only [cR]
    rw [← mul_div_assoc, cos_sq_mod r (2 ^ 204) (d * k.val) hr.pos]
    have harg : Real.pi * ((2 ^ 204 * d : ℕ) : ℝ) * (k.val : ℝ) / (r : ℝ) =
        Real.pi * ((2 ^ 204 : ℕ) : ℝ) * ((d * k.val : ℕ) : ℝ) / (r : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_mul]; ring
    rw [harg]
  rw [hcL_sum, hcR_sum] at hsum
  have hlower := mul_le_mul_of_nonneg_left hsum hrinv
  have heval : (r : ℝ)⁻¹ * (((r : ℝ) - 1) * (1 - 24 / 1000000 - 136 / 100000) -
      (r : ℝ) / 2 * (586 / 100000) - (r : ℝ) / 2 * (900 / 100000)) =
      (1 - 1 / (r : ℝ)) * (1 - 24 / 1000000 - 136 / 100000) - 586 / 200000 - 900 / 200000 := by
    field_simp [hrR.ne']; ring
  rw [heval, step2] at hlower
  have hrbig_nat : 1000000 ≤ r := by dsimp only [r]; norm_num [order]
  have hrbig : (1000000 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hrbig_nat
  have hinv : 1 / (r : ℝ) ≤ (1 : ℝ) / 1000000 := one_div_le_one_div_of_le (by norm_num) hrbig
  have hnum : (9911 / 10000 : ℝ) ≤ (1 - 1 / (r : ℝ)) * (1 - 24 / 1000000 - 136 / 100000) -
      586 / 200000 - 900 / 200000 := by linarith
  exact hnum.trans (hlower.trans step1)

theorem decoder_budget258 : 3 * (2 * (order / 2 ^ 204 + 2)) ≤ 56 * (2 ^ 49 + 2) := by
  norm_num [order]

#print axioms sine_pair_success
#print axioms decoder_budget258

end
end ShorECDLP.Entrant.SineBounds
end

/-! ### Consolidated from `First18Loader.lean` -/
section
namespace ShorECDLP.Entrant.SelectSchedule18
open Quantum Secp256k1 Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
def bits : List Wire := List.range' 855 17 ++ [537]
def Input (s : BasisState) : Prop := s 836=true ∧ ∀ v,v≠836 → v∉bits → s v=false
def tablePoint (coeffs : Fin 262144 → PointCoeff) (Q : Point) (a : Nat) : Point :=
  constantPoint Q (coeffs ⟨a%262144,Nat.mod_lt _ (by decide +kernel)⟩)
def update (init : Point → Nat → Point) (Q : Point) (s : BasisState) : BasisState :=
  pointWrite (init Q (tableAddressValue bits s)) s
end
end ShorECDLP.Entrant.SelectSchedule18
namespace ShorECDLP.Entrant.First18
open Quantum Challenge Secp256k1 Paper2607_13816 Paper2607_13816.ChallengeMigration AndGadget WEXCredit
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false

/-! ### Registers -/

/-- The high sixteen address bits, little-endian. -/
def selBits : List Wire := List.range' 856 16 ++ [537]
def selPaths : List Wire := List.range' 519 17
/-- The partner register: 513 pool wires that are clean before the first window. -/
def garb : List Wire := List.range' 872 513
def high : List Wire := List.range' 864 8 ++ [537]
def clearPaths : List Wire := List.range' 519 9
def scratch : Wire := 872
def hot (i : Fin 512) : Wire := 873 + i.val
def low (i : Fin 9) : Wire := 855 + i.val

def row (a : Nat) : Fin 262144 := ⟨a % 262144, Nat.mod_lt _ (by decide +kernel)⟩
/-- The address that differs from `a` in bit 0. -/
def partner (a : Nat) : Nat := 2 * (a / 2) + (1 - a % 2)

theorem mem_point {w : Nat} (h : w ∈ pointLogicalWires) :
    (263 ≤ w ∧ w < 519) ∨ (580 ≤ w ∧ w < 836) ∨ w = 838 := by
  simp only [pointLogicalWires, pointCorrectionX, pointCorrectionYInf, List.mem_append,
    List.mem_range'_1, List.mem_singleton, List.not_mem_nil, or_false] at h
  (try dsimp only [Wire] at *); omega

theorem mem_garb {w : Nat} (h : w ∈ garb) : 872 ≤ w ∧ w < 1385 := by
  simp only [garb, List.mem_range'_1] at h
  (try dsimp only [Wire] at *); omega

theorem point_length : pointLogicalWires.length = 513 := by
  simp [pointLogicalWires, pointCorrectionX, pointCorrectionYInf]

theorem garb_length : garb.length = 513 := by simp [garb]

theorem garb_nodup : garb.Nodup := List.nodup_range'

theorem point_not_garb {w : Nat} (h1 : w ∈ pointLogicalWires) (h2 : w ∈ garb) : False := by
  have := mem_point h1
  have := mem_garb h2
  (try dsimp only [Wire] at *); omega

theorem point_garb_nodup : (pointLogicalWires ++ garb).Nodup :=
  List.nodup_append.mpr ⟨pointLogicalWires_nodup, garb_nodup,
    fun _ ha _ hb he => point_not_garb ha (by rw [he]; exact hb)⟩

theorem n855_point : (855 : Wire) ∉ pointLogicalWires := fun h => by have := mem_point h; (try dsimp only [Wire] at *); omega
theorem n855_garb : (855 : Wire) ∉ garb := fun h => by have := mem_garb h; (try dsimp only [Wire] at *); omega

theorem low_eq : List.ofFn low = List.range' 855 9 := by decide +kernel
theorem hot_eq : List.ofFn hot = List.range' 873 512 := by decide +kernel

theorem input_clean (s : BasisState) (hs : SelectSchedule18.Input s) (w : Nat)
    (h1 : w ≠ 836) (h2 : w < 855 ∨ 872 ≤ w) (h3 : w ≠ 537) : s w = false := by
  apply hs.2 w h1
  simp only [SelectSchedule18.bits, List.mem_append, List.mem_range'_1, List.mem_singleton, List.not_mem_nil, or_false]
  (try dsimp only [Wire] at *); omega

theorem input_selPaths (s : BasisState) (hs : SelectSchedule18.Input s) : Clean selPaths s := by
  intro w hw
  simp only [selPaths, List.mem_range'_1] at hw
  exact input_clean s hs w (by (try dsimp only [Wire] at *); omega) (by (try dsimp only [Wire] at *); omega) (by (try dsimp only [Wire] at *); omega)

/-! ### The select -/

def selLeaf (l : Nat) (q : Wire) : List (TemplateGate 262144) :=
  lookupLeafGates q ((pointRefs (row (2 * l))).zip pointLogicalWires ++
    (pointRefs (row (2 * l + 1))).zip garb)

def selOps : List (LookupOp 262144) :=
  unaryLookupOps selLeaf (tableAddressTree selBits 0 1) 836 selPaths

theorem sel_layout : (tableAddressTree selBits 0 1).Layout 836 selPaths :=
  tableAddressTree_layout _ _ _ _ _ (by decide +kernel) (by decide +kernel)

theorem sel_nodes : (tableAddressTree selBits 0 1).internalNodes = 131071 := by
  have h := tableAddressTree_nodes selBits 0 1
  change _ + 1 = 131072 at h
  (try dsimp only [Wire] at *); omega

theorem selOps_measurements : lookupMeasurements selOps = 131071 := by
  rw [selOps, unaryLookupOps_measurements _ _ _ _ sel_layout, sel_nodes]

def word (read : ConstantBit 262144 → Bool) (a : Nat) : List Bool := (pointRefs (row a)).map read

def selMask (read : ConstantBit 262144 → Bool) (l : Nat) : List Wire :=
  tableBitsMask pointLogicalWires (word read (2 * l)) ++ tableBitsMask garb (word read (2 * l + 1))

theorem pointRefs_length (r : Fin 262144) : (pointRefs r).length = 513 := by
  rw [pointRefs, List.length_append, List.length_append, List.length_ofFn, List.length_ofFn,
    List.length_singleton] <;> rfl

theorem word_length (read : ConstantBit 262144 → Bool) (a : Nat) : (word read a).length = 513 := by
  rw [word, List.length_map, pointRefs_length]

theorem selLeaf_instantiate (read : ConstantBit 262144 → Bool) (l : Nat) (q : Wire) :
    (selLeaf l q).flatMap (TemplateGate.instantiate read) = tableXorGates q (selMask read l) := by
  rw [selLeaf, lookupLeafGates_instantiate,
    show (fun p : ConstantBit 262144 × Wire => Gate.CX q p.2) = (Gate.CX q) ∘ Prod.snd from rfl,
    ← List.map_map, List.filter_append, List.map_append, filtered_zip_mask, filtered_zip_mask]
  rfl

theorem selOps_circuit (read : ConstantBit 262144 → Bool) :
    lookupCircuit read selOps = tableLookupProgram (selMask read) selBits 836 selPaths := by
  rw [selOps, unaryLookupOps_circuit]
  unfold tableLookupProgram tableLookup
  apply unaryAction_leaf_congr
  intro l _ q
  exact selLeaf_instantiate read l q

attribute [irreducible] selOps

theorem selMask_sub (read : ConstantBit 262144 → Bool) (l : Nat) {w : Wire} (h : w ∈ selMask read l) :
    w ∈ pointLogicalWires ∨ w ∈ garb := by
  rcases List.mem_append.mp h with h | h
  · exact Or.inl (tableBitsMask_subset _ _ h)
  · exact Or.inr (tableBitsMask_subset _ _ h)

theorem selMask_nodup (read : ConstantBit 262144 → Bool) (l : Nat) : (selMask read l).Nodup :=
  List.nodup_append.mpr ⟨tableBitsMask_nodup _ _ pointLogicalWires_nodup,
    tableBitsMask_nodup _ _ garb_nodup, fun _ ha _ hb he => point_not_garb
      (tableBitsMask_subset _ _ ha) (by rw [he]; exact tableBitsMask_subset _ _ hb)⟩

theorem sel_coherent (read : ConstantBit 262144 → Bool) :
    CoherentlyImplementsOn (lookupCircuit read selOps)
      (Finsupp.lmapDomain ℂ ℂ (tableLookupState (selMask read) selBits 836)) (Clean selPaths) := by
  rw [selOps_circuit]
  apply tableLookupProgram_coherent_state _ _ _ _ (by decide +kernel) (by decide +kernel) (selMask_nodup read)
  intro l w hw hm
  simp only [selBits, selPaths, List.mem_cons, List.mem_append, List.mem_range'_1,
    List.mem_singleton, List.not_mem_nil, or_false] at hw
  rcases selMask_sub read l hm with h | h
  · have := mem_point h; (try dsimp only [Wire] at *); omega
  · have := mem_garb h; (try dsimp only [Wire] at *); omega

theorem sel_frame (read : ConstantBit 262144 → Bool) (s : BasisState) (w : Wire)
    (h1 : w ∉ pointLogicalWires) (h2 : w ∉ garb) :
    tableLookupState (selMask read) selBits 836 s w = s w := by
  unfold tableLookupState
  apply tableXorState_outside
  intro hm
  rcases selMask_sub read _ hm with h | h
  · exact h1 h
  · exact h2 h

theorem input_point (s : BasisState) (hs : SelectSchedule18.Input s) : Clean pointLogicalWires s :=
  fun w hw => by
    have := mem_point hw
    exact input_clean s hs w (by (try dsimp only [Wire] at *); omega) (by (try dsimp only [Wire] at *); omega) (by (try dsimp only [Wire] at *); omega)

theorem input_garb (s : BasisState) (hs : SelectSchedule18.Input s) : Clean garb s :=
  fun w hw => by
    have := mem_garb hw
    exact input_clean s hs w (by (try dsimp only [Wire] at *); omega) (by (try dsimp only [Wire] at *); omega) (by (try dsimp only [Wire] at *); omega)

theorem sel_point (read : ConstantBit 262144 → Bool) (s : BasisState) (hs : SelectSchedule18.Input s) :
    wireValues pointLogicalWires (tableLookupState (selMask read) selBits 836 s) =
      word read (2 * tableAddressValue selBits s) := by
  have he : wireValues pointLogicalWires (tableLookupState (selMask read) selBits 836 s) =
      wireValues pointLogicalWires (tableXorState (tableBitsMask pointLogicalWires
        (word read (2 * tableAddressValue selBits s))) true s) := by
    apply List.map_congr_left
    intro w hw
    have hg : w ∉ tableBitsMask garb (word read (2 * tableAddressValue selBits s + 1)) :=
      fun h => point_not_garb hw (tableBitsMask_subset _ _ h)
    simp only [tableLookupState, tableXorState, selMask, List.mem_append, hg, or_false, hs.1]
  rw [he, tableBitsMask_read _ _ s pointLogicalWires_nodup (by rw [point_length, word_length])
    (input_point s hs)]

theorem sel_garb (read : ConstantBit 262144 → Bool) (s : BasisState) (hs : SelectSchedule18.Input s) :
    wireValues garb (tableLookupState (selMask read) selBits 836 s) =
      word read (2 * tableAddressValue selBits s + 1) := by
  have he : wireValues garb (tableLookupState (selMask read) selBits 836 s) =
      wireValues garb (tableXorState (tableBitsMask garb
        (word read (2 * tableAddressValue selBits s + 1))) true s) := by
    apply List.map_congr_left
    intro w hw
    have hp : w ∉ tableBitsMask pointLogicalWires (word read (2 * tableAddressValue selBits s)) :=
      fun h => point_not_garb (tableBitsMask_subset _ _ h) hw
    simp only [tableLookupState, tableXorState, selMask, List.mem_append, hp, false_or, hs.1]
  rw [he, tableBitsMask_read _ _ s garb_nodup (by rw [garb_length, word_length]) (input_garb s hs)]

/-! ### The swap layer -/

def swapWords (c : Wire) : List Wire → List Wire → Circuit
  | a :: as, b :: bs => controlledSwap c a b ++ swapWords c as bs
  | _, _ => []

theorem swapWords_run (c : Wire) : ∀ (as bs : List Wire), c ∉ as → c ∉ bs → (as ++ bs).Nodup →
    as.length = bs.length → ∀ s : BasisState,
    (∀ w, w ∉ as → w ∉ bs → Classical.run (swapWords c as bs) s w = s w) ∧
    wireValues as (Classical.run (swapWords c as bs) s) =
      (if s c then wireValues bs s else wireValues as s) ∧
    wireValues bs (Classical.run (swapWords c as bs) s) =
      (if s c then wireValues as s else wireValues bs s)
  | [], [], _, _, _, _, s => by simp [swapWords, wireValues]
  | [], _ :: _, _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, _, h, _ => by simp at h
  | a :: as, b :: bs, hca, hcb, hn, hl, s => by
    have hca' : c ≠ a := fun h => hca (by simp [h])
    have hcas : c ∉ as := fun h => hca (by simp [h])
    have hcb' : c ≠ b := fun h => hcb (by simp [h])
    have hcbs : c ∉ bs := fun h => hcb (by simp [h])
    have hn1 := List.nodup_cons.mp (by simpa only [List.cons_append] using hn)
    have ha_as : a ∉ as := fun h => hn1.1 (by simp [h])
    have ha_bs : a ∉ bs := fun h => hn1.1 (by simp [h])
    have hab : a ≠ b := fun h => hn1.1 (by simp [h])
    have hn2 := List.nodup_cons.mp (List.nodup_middle.mp hn1.2)
    have hb_as : b ∉ as := fun h => hn2.1 (List.mem_append_left _ h)
    have hb_bs : b ∉ bs := fun h => hn2.1 (List.mem_append_right _ h)
    have hl' : as.length = bs.length := by simpa using hl
    have hsw := run_controlledSwap c a b s hca' hcb' hab
    have hsc : Classical.run (controlledSwap c a b) s c = s c := by
      by_cases hc : s c = true <;> simp [hsw, hc, upd, hca', hcb']
    have hfr : ∀ w, w ≠ a → w ≠ b → Classical.run (controlledSwap c a b) s w = s w := by
      intro w h1 h2
      by_cases hc : s c = true <;> simp [hsw, hc, upd, h1, h2]
    have hsa : Classical.run (controlledSwap c a b) s a = (if s c then s b else s a) := by
      by_cases hc : s c = true <;> simp [hsw, hc, upd, hab]
    have hsb : Classical.run (controlledSwap c a b) s b = (if s c then s a else s b) := by
      by_cases hc : s c = true <;> simp [hsw, hc, upd]
    obtain ⟨ihf, iha, ihb⟩ :=
      swapWords_run c as bs hcas hcbs hn2.2 hl' (Classical.run (controlledSwap c a b) s)
    have hvas : wireValues as (Classical.run (controlledSwap c a b) s) = wireValues as s :=
      List.map_congr_left (fun w hw => hfr w (fun h => ha_as (h ▸ hw)) (fun h => hb_as (h ▸ hw)))
    have hvbs : wireValues bs (Classical.run (controlledSwap c a b) s) = wireValues bs s :=
      List.map_congr_left (fun w hw => hfr w (fun h => ha_bs (h ▸ hw)) (fun h => hb_bs (h ▸ hw)))
    have hrun : Classical.run (swapWords c (a :: as) (b :: bs)) s =
        Classical.run (swapWords c as bs) (Classical.run (controlledSwap c a b) s) := by
      rw [swapWords, Classical.run_append]
    rw [hrun]
    refine ⟨?_, ?_, ?_⟩
    · intro w hw1 hw2
      rw [ihf w (fun h => hw1 (List.mem_cons_of_mem _ h)) (fun h => hw2 (List.mem_cons_of_mem _ h))]
      exact hfr w (fun h => hw1 (by simp [h])) (fun h => hw2 (by simp [h]))
    · show Classical.run (swapWords c as bs) (Classical.run (controlledSwap c a b) s) a ::
          wireValues as (Classical.run (swapWords c as bs) (Classical.run (controlledSwap c a b) s)) = _
      rw [ihf a ha_as ha_bs, iha, hsc, hvas, hvbs, hsa]
      cases s c <;> rfl
    · show Classical.run (swapWords c as bs) (Classical.run (controlledSwap c a b) s) b ::
          wireValues bs (Classical.run (swapWords c as bs) (Classical.run (controlledSwap c a b) s)) = _
      rw [ihf b hb_as hb_bs, ihb, hsc, hvas, hvbs, hsb]
      cases s c <;> rfl

theorem swapWords_length (c : Wire) : ∀ as bs : List Wire,
    (swapWords c as bs).length = 3 * min as.length bs.length
  | [], _ => by simp [swapWords]
  | _ :: _, [] => by simp [swapWords]
  | a :: as, b :: bs => by
    rw [swapWords, List.length_append, swapWords_length c as bs]
    simp only [controlledSwap, List.length_cons, List.length_nil]
    (try dsimp only [Wire] at *); omega

theorem swapWords_ccx (c : Wire) : ∀ as bs : List Wire,
    ccxCount (swapWords c as bs) = min as.length bs.length
  | [], _ => by simp [swapWords, ccxCount]
  | _ :: _, [] => by simp [swapWords, ccxCount]
  | a :: as, b :: bs => by
    show Nat.succ (ccxCount (swapWords c as bs)) = min (as.length + 1) (bs.length + 1)
    rw [swapWords_ccx c as bs]
    (try dsimp only [Wire] at *); omega

theorem swapWords_hp (c : Wire) : ∀ as bs : List Wire, Classical.HPFree (swapWords c as bs)
  | [], _ => by simp [swapWords]
  | _ :: _, [] => by simp [swapWords]
  | a :: as, b :: bs => by
    rw [swapWords, Classical.hpFree_append]
    exact ⟨controlledSwap_HPFree c a b, swapWords_hp c as bs⟩

theorem swapWords_wf (c : Wire) : ∀ as bs : List Wire, c ∉ as → c ∉ bs → (as ++ bs).Nodup →
    CircuitWellFormed (swapWords c as bs)
  | [], _, _, _, _ => by simp [swapWords]
  | _ :: _, [], _, _, _ => by simp [swapWords]
  | a :: as, b :: bs, hca, hcb, hn => by
    rw [swapWords, circuitWellFormed_append]
    have hn1 := List.nodup_cons.mp (by simpa only [List.cons_append] using hn)
    have hn2 := List.nodup_cons.mp (List.nodup_middle.mp hn1.2)
    exact ⟨controlledSwap_wellFormed c a b (fun h => hca (by simp [h])) (fun h => hcb (by simp [h]))
      (fun h => hn1.1 (by simp [h])),
      swapWords_wf c as bs (fun h => hca (by simp [h])) (fun h => hcb (by simp [h])) hn2.2⟩

theorem swapWords_wires (c : Wire) : ∀ (as bs : List Wire) (w : Wire),
    w ∈ circuitWires (swapWords c as bs) → w = c ∨ w ∈ as ∨ w ∈ bs
  | [], _, w, h => by simp [swapWords, circuitWires] at h
  | _ :: _, [], w, h => by simp [swapWords, circuitWires] at h
  | a :: as, b :: bs, w, h => by
    rw [swapWords, circuitWires, List.flatMap_append] at h
    rcases List.mem_append.mp h with h | h
    · have hw : w = b ∨ w = a ∨ w = c := by
        simp only [controlledSwap, List.flatMap_cons, List.flatMap_nil, gateWires, List.mem_append,
          List.mem_cons, List.not_mem_nil, or_false, List.append_nil] at h
        tauto
      rcases hw with rfl | rfl | rfl
      · exact Or.inr (Or.inr List.mem_cons_self)
      · exact Or.inr (Or.inl List.mem_cons_self)
      · exact Or.inl rfl
    · rcases swapWords_wires c as bs w h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (List.mem_cons_of_mem _ h))
      · exact Or.inr (Or.inr (List.mem_cons_of_mem _ h))

def swapCircuit : Circuit := swapWords 855 pointLogicalWires garb

theorem swap_hp : Classical.HPFree swapCircuit := swapWords_hp _ _ _

theorem swap_wf : CircuitWellFormed swapCircuit :=
  swapWords_wf _ _ _ n855_point n855_garb point_garb_nodup

theorem swap_facts (s : BasisState) :
    (∀ w, w ∉ pointLogicalWires → w ∉ garb → Classical.run swapCircuit s w = s w) ∧
    wireValues pointLogicalWires (Classical.run swapCircuit s) =
      (if s 855 then wireValues garb s else wireValues pointLogicalWires s) ∧
    wireValues garb (Classical.run swapCircuit s) =
      (if s 855 then wireValues pointLogicalWires s else wireValues garb s) :=
  swapWords_run 855 pointLogicalWires garb n855_point n855_garb point_garb_nodup
    (by rw [point_length, garb_length]) s

theorem swap_wires (w : Wire) (h : w ∈ circuitWires swapCircuit) :
    w = 855 ∨ w ∈ pointLogicalWires ∨ w ∈ garb :=
  swapWords_wires 855 pointLogicalWires garb w h

attribute [irreducible] swapCircuit

/-! ### The loaded state -/

def loaded (read : ConstantBit 262144 → Bool) (s : BasisState) : BasisState :=
  Classical.run swapCircuit (tableLookupState (selMask read) selBits 836 s)

theorem bits_eq : SelectSchedule18.bits = 855 :: selBits := rfl

theorem address_split (s : BasisState) :
    tableAddressValue SelectSchedule18.bits s = (s 855).toNat + 2 * tableAddressValue selBits s := by
  rw [bits_eq] <;> rfl

theorem word_cases (read : ConstantBit 262144 → Bool) (b : Bool) (h : Nat) :
    (if b = true then word read (2 * h + 1) else word read (2 * h)) = word read (b.toNat + 2 * h) ∧
    (if b = true then word read (2 * h) else word read (2 * h + 1)) =
      word read (partner (b.toNat + 2 * h)) := by
  cases b
  · constructor
    · show word read (2 * h) = word read (Bool.toNat false + 2 * h)
      congr 1
      simp only [Bool.toNat_false]
      (try dsimp only [Wire] at *); omega
    · show word read (2 * h + 1) = word read (partner (Bool.toNat false + 2 * h))
      congr 1
      simp only [Bool.toNat_false, partner]
      (try dsimp only [Wire] at *); omega
  · constructor
    · show word read (2 * h + 1) = word read (Bool.toNat true + 2 * h)
      congr 1
      simp only [Bool.toNat_true]
      (try dsimp only [Wire] at *); omega
    · show word read (2 * h) = word read (partner (Bool.toNat true + 2 * h))
      congr 1
      simp only [Bool.toNat_true, partner]
      (try dsimp only [Wire] at *); omega

theorem loaded_facts (read : ConstantBit 262144 → Bool) (s : BasisState) (hs : SelectSchedule18.Input s) :
    (∀ w, w ∉ pointLogicalWires → w ∉ garb → loaded read s w = s w) ∧
    wireValues pointLogicalWires (loaded read s) = word read (tableAddressValue SelectSchedule18.bits s) ∧
    wireValues garb (loaded read s) =
      word read (partner (tableAddressValue SelectSchedule18.bits s)) := by
  obtain ⟨sf, sp, sg⟩ := swap_facts (tableLookupState (selMask read) selBits 836 s)
  have h855 : tableLookupState (selMask read) selBits 836 s 855 = s 855 :=
    sel_frame read s 855 n855_point n855_garb
  rw [h855, sel_point read s hs, sel_garb read s hs] at sp sg
  refine ⟨fun w h1 h2 => (sf w h1 h2).trans (sel_frame read s w h1 h2), ?_, ?_⟩
  · show wireValues pointLogicalWires (Classical.run swapCircuit _) = _
    rw [sp, address_split]
    exact (word_cases read (s 855) _).1
  · show wireValues garb (Classical.run swapCircuit _) = _
    rw [sg, address_split]
    exact (word_cases read (s 855) _).2

/-! ### The measured clear of the partner register -/

def slots : List (Fin 262144 → ConstantBit 262144) :=
  List.ofFn (fun i : Fin 256 => fun r => (⟨r, .x, i⟩ : ConstantBit 262144)) ++
  List.ofFn (fun i : Fin 256 => fun r => (⟨r, .y, i⟩ : ConstantBit 262144)) ++
  [fun r => (⟨r, .infinity, ⟨0, by decide +kernel⟩⟩ : ConstantBit 262144)]

theorem pointRefs_slots (r : Fin 262144) : pointRefs r = slots.map (fun f => f r) := by
  rw [pointRefs, slots, List.map_append, List.map_append, List.map_ofFn, List.map_ofFn, List.map_cons,
    List.map_nil] <;> rfl

theorem slots_length : slots.length = 513 := by
  rw [slots, List.length_append, List.length_append, List.length_ofFn, List.length_ofFn,
    List.length_singleton] <;> rfl

def clearData : List (MeasuredClear.ClearPort 262144) :=
  List.zipWith (fun f w => (⟨fun x => f (row (partner x)), true, w⟩ : MeasuredClear.ClearPort 262144))
    slots garb

theorem zipWith_targets {α : Type} (g : α → Wire → MeasuredClear.ClearPort 262144)
    (hg : ∀ x w, (g x w).target = w) :
    ∀ (xs : List α) (ws : List Wire), xs.length = ws.length →
      (List.zipWith g xs ws).map MeasuredClear.ClearPort.target = ws
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, w :: ws, h => by
    rw [List.zipWith_cons_cons, List.map_cons, hg, zipWith_targets g hg xs ws (by simpa using h)]

theorem clearData_targets : clearData.map MeasuredClear.ClearPort.target = garb :=
  zipWith_targets _ (fun _ _ => rfl) slots garb (by rw [slots_length, garb_length])

theorem clearData_length : clearData.length = 513 := by
  have h := congrArg List.length clearData_targets
  rw [List.length_map, garb_length] at h
  exact h

theorem clear_layout : (tableAddressTree high 0 1).Layout 836 clearPaths :=
  tableAddressTree_layout _ _ _ _ _ (by decide +kernel) (by decide +kernel)

theorem high_index : (tableAddressTree high 0 1).indexWires.dedup = high :=
  tableAddressTree_index _ _ _ (by decide +kernel)

theorem clear_nodes : (tableAddressTree high 0 1).internalNodes = 511 := by
  have h := tableAddressTree_nodes high 0 1
  change _ + 1 = 512 at h
  (try dsimp only [Wire] at *); omega

theorem clear_leaves : (tableAddressTree high 0 1).leaves = 512 := by
  rw [MeasuredClear.addressTree_leaves] <;> rfl

theorem clear_measurements : MeasuredClear.recordMeasurements
    (MeasuredClear.recordUnaryOps (tableAddressTree high 0 1) 836 clearPaths) = 511 := by
  rw [(MeasuredClear.recordUnary_counts _ _ _ clear_layout 0).1, clear_nodes]

theorem hot_injective : Function.Injective hot := by
  intro i j h
  simp only [hot] at h
  exact Fin.ext (by (try dsimp only [Wire] at *); omega)

theorem low_ne_hot : ∀ i j, low i ≠ hot j := by
  intro i j h
  simp only [low, hot] at h
  have := i.isLt
  (try dsimp only [Wire] at *); omega

theorem hot_disjoint : (MeasuredClear.hotBank9 hot).Disjoint
    (836 :: (tableAddressTree high 0 1).indexWires.dedup ++ clearPaths) := by
  rw [high_index]
  intro w hw hm
  simp only [MeasuredClear.hotBank9, hot_eq, high, clearPaths, List.mem_cons, List.mem_append,
    List.mem_range'_1, List.mem_singleton, List.not_mem_nil, or_false] at hw hm
  (try dsimp only [Wire] at *); omega

theorem scratch_not_tree : scratch ∉ 836 :: (tableAddressTree high 0 1).indexWires.dedup ++ clearPaths := by
  rw [high_index]
  decide +kernel

theorem scratch_not_hot : scratch ∉ MeasuredClear.hotBank9 hot := by
  rw [MeasuredClear.hotBank9, hot_eq]
  decide +kernel

theorem tree_not_targets : ∀ w ∈ 836 :: List.ofFn low ++ (tableAddressTree high 0 1).indexWires.dedup ++ clearPaths,
    w ∉ clearData.map MeasuredClear.ClearPort.target := by
  rw [high_index, clearData_targets, low_eq]
  intro w hw hg
  have hb := mem_garb hg
  simp only [high, clearPaths, List.mem_cons, List.mem_append, List.mem_range'_1,
    List.mem_singleton, List.not_mem_nil, or_false] at hw
  (try dsimp only [Wire] at *); omega

theorem hot_targets : ∀ i, hot i ∈ clearData.map MeasuredClear.ClearPort.target := by
  intro i
  rw [clearData_targets]
  simp only [hot, garb, List.mem_range'_1]
  have := i.isLt
  (try dsimp only [Wire] at *); omega

theorem low_high_bits : [MeasuredClear.lowN9 low 0, MeasuredClear.lowN9 low 1, MeasuredClear.lowN9 low 2,
    MeasuredClear.lowN9 low 3, MeasuredClear.lowN9 low 4, MeasuredClear.lowN9 low 5,
    MeasuredClear.lowN9 low 6, MeasuredClear.lowN9 low 7, MeasuredClear.lowN9 low 8] ++ high =
      SelectSchedule18.bits := by
  decide +kernel

theorem zip_loaded (read : ConstantBit 262144 → Bool) (a : Nat) (t : BasisState) :
    ∀ (fs : List (Fin 262144 → ConstantBit 262144)) (ws : List Wire),
    wireValues ws t = fs.map (fun f => read (f (row (partner a)))) →
    ∀ p ∈ List.zipWith (fun f w => (⟨fun x => f (row (partner x)), true, w⟩ :
        MeasuredClear.ClearPort 262144)) fs ws,
      t p.target = (true && decide (read (p.ref a) = p.value))
  | [], _, _, p, hp => by simp at hp
  | _ :: _, [], _, p, hp => by simp at hp
  | f :: fs, w :: ws, h, p, hp => by
    have h' : t w = read (f (row (partner a))) ∧
        wireValues ws t = fs.map (fun f => read (f (row (partner a)))) := List.cons.inj h
    rw [List.zipWith_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · show t w = (true && decide (read (f (row (partner a))) = true))
      rw [h'.1]
      cases read (f (row (partner a))) <;> rfl
    · exact zip_loaded read a t fs ws h'.2 p hp

theorem loaded_clear (read : ConstantBit 262144 → Bool) (s : BasisState) (hs : SelectSchedule18.Input s) :
    MeasuredClear.LoadedClear9 clearData read low (tableAddressTree high 0 1) 836 (loaded read s) := by
  obtain ⟨tf, -, tg⟩ := loaded_facts read s hs
  have haddr : 512 * (tableAddressTree high 0 1).routeLabel (loaded read s) +
      MeasuredClear.hotAddress9 low (loaded read s) = tableAddressValue SelectSchedule18.bits s := by
    rw [MeasuredClear.splitAddress_value9, low_high_bits]
    apply tableAddressValue_congr
    intro w hw
    have hw' : (855 ≤ w ∧ w < 872) ∨ w = 537 := by
      simp only [SelectSchedule18.bits, List.mem_append, List.mem_range'_1, List.mem_singleton, List.not_mem_nil, or_false] at hw
      (try dsimp only [Wire] at *); omega
    apply tf w
    · intro h; have := mem_point h; (try dsimp only [Wire] at *); omega
    · intro h; have := mem_garb h; (try dsimp only [Wire] at *); omega
  have h836 : loaded read s 836 = true := by
    rw [tf 836 (fun h => by have := mem_point h; (try dsimp only [Wire] at *); omega) (fun h => by have := mem_garb h; (try dsimp only [Wire] at *); omega)]
    exact hs.1
  unfold MeasuredClear.LoadedClear9
  intro p hp
  rw [haddr, h836]
  apply zip_loaded read _ (loaded read s) slots garb _ p hp
  rw [tg, word, pointRefs_slots, List.map_map] <;> rfl

theorem clear_paths_clean (read : ConstantBit 262144 → Bool) (s : BasisState)
    (hs : SelectSchedule18.Input s) : Clean clearPaths (loaded read s) := by
  obtain ⟨tf, -, -⟩ := loaded_facts read s hs
  intro w hw
  simp only [clearPaths, List.mem_range'_1] at hw
  rw [tf w (fun h => by have := mem_point h; (try dsimp only [Wire] at *); omega) (fun h => by have := mem_garb h; (try dsimp only [Wire] at *); omega)]
  exact input_clean s hs w (by (try dsimp only [Wire] at *); omega) (by (try dsimp only [Wire] at *); omega) (by (try dsimp only [Wire] at *); omega)

theorem final_state (coeffs : Fin 262144 → PointCoeff) (Q : Point) (s : BasisState)
    (hs : SelectSchedule18.Input s) :
    clearRegister garb (loaded (readConstant coeffs Q) s) =
      pointWrite (SelectSchedule18.tablePoint coeffs Q (tableAddressValue SelectSchedule18.bits s)) s := by
  obtain ⟨tf, tp, -⟩ := loaded_facts (readConstant coeffs Q) s hs
  have hw : wireValues pointLogicalWires (loaded (readConstant coeffs Q) s) =
      wireValues pointLogicalWires (pointWrite (SelectSchedule18.tablePoint coeffs Q
        (tableAddressValue SelectSchedule18.bits s)) s) := by
    rw [tp, pointWrite_word, word, pointRefs_read] <;> rfl
  funext w
  by_cases hg : w ∈ garb
  · rw [clearRegister_clean garb _ w hg, pointWrite_frame _ _ w (fun h => point_not_garb h hg)]
    exact (input_garb s hs w hg).symm
  · rw [MeasuredClear.clearRegister_frame _ _ _ hg]
    by_cases hp : w ∈ pointLogicalWires
    · exact List.map_inj_left.mp hw w hp
    · rw [tf w hp hg, pointWrite_frame _ _ w hp]

/-! ### Programs -/

def selProgram (start : Nat) : Straight 262144 start (start + 131071) :=
  castFinish (by rw [selOps_measurements]) (lookupProgram 262144 selOps start)

def swapProgram (start : Nat) : Straight 262144 start start := literalProgram swapCircuit

theorem clear_finish (start : Nat) : start + clearData.length + (MeasuredClear.recordMeasurements
    (MeasuredClear.recordUnaryOps (tableAddressTree high 0 1) 836 clearPaths) + 511) = start + 1535 := by
  rw [clearData_length, clear_measurements, Nat.add_assoc] <;> rfl

def clearProgram (start : Nat) : Straight 262144 start (start + 1535) :=
  castFinish (clear_finish start)
    (MeasuredClear.measuredClear9 clearData low hot (tableAddressTree high 0 1) 836 scratch clearPaths start)

theorem program_finish (start : Nat) : start + 131071 + 1535 = start + 132606 := by
  rw [Nat.add_assoc] <;> rfl

def program (start : Nat) : Straight 262144 start (start + 132606) :=
  castFinish (program_finish start)
    (((selProgram start).append (swapProgram (start + 131071))).append (clearProgram (start + 131071)))

attribute [irreducible] selProgram swapProgram clearProgram program

def clearSource (read : ConstantBit 262144 → Bool) : AdaptiveCircuit :=
  (MeasuredClear.measuredClear9 clearData low hot (tableAddressTree high 0 1) 836 scratch clearPaths 0).instantiate
    read Fin.elim0

def source (read : ConstantBit 262144 → Bool) : AdaptiveCircuit :=
  ((lookupCircuit read selOps).seq (.unitary swapCircuit .done)).seq (clearSource read)

theorem sel_run (read : ConstantBit 262144 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((selProgram start).instantiate read history).run = (lookupCircuit read selOps).run := by
  rw [selProgram, castFinish_instantiate, lookupProgram_run]

theorem swap_run (read : ConstantBit 262144 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((swapProgram start).instantiate read history).run = (AdaptiveCircuit.unitary swapCircuit .done).run := by
  rw [swapProgram]
  exact literalProgram_run _ _ _

theorem clear_run (read : ConstantBit 262144 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((clearProgram start).instantiate read history).run = (clearSource read).run := by
  simp only [clearProgram, clearSource, castFinish_instantiate, MeasuredClear.measuredClear_run9]

theorem program_run (read : ConstantBit 262144 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((program start).instantiate read history).run = (source read).run := by
  rw [program, castFinish_instantiate,
    append_run_fixed _ _ _ _ _ (fun h => clear_run read _ h), AdaptiveCircuit.run_seq,
    append_run_fixed _ _ _ _ _ (fun h => swap_run read _ h), AdaptiveCircuit.run_seq,
    sel_run read start history]
  simp only [source, AdaptiveCircuit.run_seq]

/-! ### Semantics -/

theorem lmap_ket (f : BasisState → BasisState) (s : BasisState) :
    Finsupp.lmapDomain ℂ ℂ f (ket s) = ket (f s) := by
  simp [ket, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem coherent_restrict {p : AdaptiveCircuit} {I : State →ₗ[ℂ] State} {V W : BasisState → Prop}
    (h : CoherentlyImplementsOn p I V) (hw : ∀ s, W s → V s) : CoherentlyImplementsOn p I W := by
  obtain ⟨cs, ha, hm⟩ := h
  exact ⟨cs, ha.imp (fun _ _ hb s hs => hb s (hw s hs)), hm⟩

theorem sel_swap_coherent (read : ConstantBit 262144 → Bool) :
    CoherentlyImplementsOn ((lookupCircuit read selOps).seq (.unitary swapCircuit .done))
      ((Quantum.run swapCircuit).comp
        (Finsupp.lmapDomain ℂ ℂ (tableLookupState (selMask read) selBits 836)))
      SelectSchedule18.Input :=
  (coherent_restrict (sel_coherent read) (fun s hs => input_selPaths s hs)).seq
    (CoherentlyImplementsOn.unitary swapCircuit (fun _ => True)) (fun _ _ _ _ => trivial)

theorem clear_coherent (read : ConstantBit 262144 → Bool) :
    CoherentlyImplementsOn (clearSource read)
      (Finsupp.lmapDomain ℂ ℂ (clearRegister (clearData.map MeasuredClear.ClearPort.target)))
      (fun s => Clean clearPaths s ∧
        MeasuredClear.LoadedClear9 clearData read low (tableAddressTree high 0 1) 836 s) :=
  MeasuredClear.measuredClear_recycled_coherent9 clearData read low hot (tableAddressTree high 0 1) 836
    scratch clearPaths clear_layout hot_injective low_ne_hot hot_disjoint scratch_not_tree scratch_not_hot
    (by rw [clearData_targets]; exact garb_nodup) tree_not_targets hot_targets 0 Fin.elim0

theorem sel_swap_ket (read : ConstantBit 262144 → Bool) (s : BasisState) :
    ((Quantum.run swapCircuit).comp
        (Finsupp.lmapDomain ℂ ℂ (tableLookupState (selMask read) selBits 836))) (ket s) =
      ket (loaded read s) := by
  rw [LinearMap.comp_apply, lmap_ket, run_ket_agrees_classical _ _ swap_hp]
  rfl

theorem loaded_supported (read : ConstantBit 262144 → Bool) (s : BasisState)
    (hs : SelectSchedule18.Input s) :
    SupportedOn (fun s => Clean clearPaths s ∧
        MeasuredClear.LoadedClear9 clearData read low (tableAddressTree high 0 1) 836 s)
      (((Quantum.run swapCircuit).comp
        (Finsupp.lmapDomain ℂ ℂ (tableLookupState (selMask read) selBits 836))) (ket s)) := by
  rw [sel_swap_ket]
  exact supportedOn_ket _ _ ⟨clear_paths_clean read s hs, loaded_clear read s hs⟩

theorem source_ket (coeffs : Fin 262144 → PointCoeff) (Q : Point) (s : BasisState)
    (hs : SelectSchedule18.Input s) :
    ((Finsupp.lmapDomain ℂ ℂ (clearRegister (clearData.map MeasuredClear.ClearPort.target))).comp
      ((Quantum.run swapCircuit).comp
        (Finsupp.lmapDomain ℂ ℂ (tableLookupState (selMask (readConstant coeffs Q)) selBits 836)))) (ket s) =
      Finsupp.lmapDomain ℂ ℂ (fun s => pointWrite (SelectSchedule18.tablePoint coeffs Q
        (tableAddressValue SelectSchedule18.bits s)) s) (ket s) := by
  rw [LinearMap.comp_apply, sel_swap_ket, lmap_ket, lmap_ket, clearData_targets, final_state coeffs Q s hs]

theorem source_coherent (coeffs : Fin 262144 → PointCoeff) (Q : Point) :
    CoherentlyImplementsOn (source (readConstant coeffs Q))
      (Finsupp.lmapDomain ℂ ℂ (fun s => pointWrite (SelectSchedule18.tablePoint coeffs Q
        (tableAddressValue SelectSchedule18.bits s)) s)) SelectSchedule18.Input := by
  have h12 := sel_swap_coherent (readConstant coeffs Q)
  have h123 := h12.seq (clear_coherent (readConstant coeffs Q)) (by
    intro s hs
    rw [sel_swap_ket]
    exact supportedOn_ket _ _ ⟨clear_paths_clean _ s hs, loaded_clear _ s hs⟩)
  rw [source]
  refine h123.congrIdeal (fun s hs => ?_)
  rw [LinearMap.comp_apply, sel_swap_ket, lmap_ket, lmap_ket, clearData_targets, final_state coeffs Q s hs]

theorem program_coherent (coeffs : Fin 262144 → PointCoeff) (Q : Point) (start : Nat)
    (history : Fin start → Bool) :
    CoherentlyImplementsOn ((program start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (fun s => pointWrite (SelectSchedule18.tablePoint coeffs Q
        (tableAddressValue SelectSchedule18.bits s)) s)) SelectSchedule18.Input := by
  unfold CoherentlyImplementsOn
  rw [program_run]
  exact source_coherent coeffs Q

/-! ### Resources -/

theorem selOps_physical : ∀ op ∈ selOps, op.Physical := by
  rw [selOps]
  apply unaryLookupOps_physical _ _ _ _ sel_layout
  intro l c hc g hg
  simp only [selLeaf, lookupLeafGates, List.mem_map] at hg
  obtain ⟨⟨ref, target⟩, hm, rfl⟩ := hg
  change c ≠ target
  have ht : target ∈ pointLogicalWires ∨ target ∈ garb := by
    rcases List.mem_append.mp hm with h | h
    · exact Or.inl (List.of_mem_zip h).2
    · exact Or.inr (List.of_mem_zip h).2
  have hc' : c = 836 ∨ (519 ≤ c ∧ c < 536) := by
    simp only [selPaths, List.mem_cons, List.mem_range'_1] at hc
    (try dsimp only [Wire] at *); omega
  intro he
  subst he
  rcases ht with h | h
  · have := mem_point h; (try dsimp only [Wire] at *); omega
  · have := mem_garb h; (try dsimp only [Wire] at *); omega

theorem sel_wellFormed (start : Nat) : (selProgram start).WellFormed := by
  rw [selProgram, castFinish_wellFormed]
  exact lookupProgram_wellFormed _ selOps_physical _

theorem swap_wellFormed (start : Nat) : (swapProgram start).WellFormed := by
  rw [swapProgram]
  exact literalProgram_wellFormed _ swap_wf

theorem clear_wellFormed (start : Nat) : (clearProgram start).WellFormed := by
  rw [clearProgram, castFinish_wellFormed]
  generalize htree : tableAddressTree high 0 1 = tree
  exact MeasuredClear.measuredClear_wellFormed9 clearData low hot tree 836 scratch clearPaths
    (by rw [← htree]; exact clear_layout) hot_injective low_ne_hot
    (by rw [← htree]; exact scratch_not_tree) scratch_not_hot start

theorem program_wellFormed (start : Nat) : (program start).WellFormed := by
  have h := straight_append_wellFormed _ _
    (straight_append_wellFormed _ _ (sel_wellFormed start) (swap_wellFormed (start + 131071)))
    (clear_wellFormed (start + 131071))
  rw [program, castFinish_wellFormed]
  exact h

theorem selLeaf_length (l : Nat) (q : Wire) : (selLeaf l q).length ≤ 1026 := by
  rw [selLeaf, lookupLeafGates, List.length_map, List.length_append, List.length_zip, List.length_zip,
    pointRefs_length, pointRefs_length, point_length, garb_length] <;> decide +kernel

theorem sel_slots (start : Nat) : (selProgram start).gateSlots ≤ 1026 * (131071 + 1) + 10 * 131071 := by
  rw [selProgram, castFinish_gateSlots, lookupProgram_slots]
  have h := unaryLookupOps_slots_le selLeaf 1026 selLeaf_length (tableAddressTree selBits 0 1) 836 selPaths
  rw [sel_nodes] at h
  rw [selOps]
  exact h

theorem swap_slots (start : Nat) : (swapProgram start).gateSlots = 3 * 513 := by
  rw [swapProgram, literalProgram_slots, swapCircuit, swapWords_length, point_length, garb_length,
    Nat.min_self]

theorem clear_slots (start : Nat) :
    (clearProgram start).gateSlots = 2048 * 513 * 512 + 10 * 511 + 4594 := by
  rw [clearProgram, castFinish_gateSlots, MeasuredClear.measuredClear_slots9 _ _ _ _ _ _ _ clear_layout,
    clearData_length, clear_leaves, clear_nodes]

theorem program_slots (start : Nat) : (program start).gateSlots ≤ 1000000000 := by
  rw [program, castFinish_gateSlots, Straight.gateSlots_append, Straight.gateSlots_append, swap_slots,
    clear_slots]
  exact Nat.le_trans (Nat.add_le_add_right (Nat.add_le_add_right (sel_slots start) _) _) (by decide +kernel)

/-- Every wire the first window touches. -/
def support : List Wire := 836 :: SelectSchedule18.bits ++ selPaths ++ pointLogicalWires ++ garb

theorem mem_support {w : Nat} (h : w = 836 ∨ (855 ≤ w ∧ w < 872) ∨ w = 537 ∨ (519 ≤ w ∧ w < 536) ∨
    (263 ≤ w ∧ w < 519) ∨ (580 ≤ w ∧ w < 836) ∨ w = 838 ∨ (872 ≤ w ∧ w < 1385)) : w ∈ support := by
  simp only [support, SelectSchedule18.bits, selPaths, pointLogicalWires, pointCorrectionX,
    pointCorrectionYInf, garb, List.mem_cons, List.mem_append, List.mem_range'_1, List.mem_singleton, List.not_mem_nil, or_false]
  (try dsimp only [Wire] at *); omega

theorem support_range : support ⊆ List.range 1616 := by
  intro w hw
  rw [List.mem_range]
  simp only [support, SelectSchedule18.bits, selPaths, pointLogicalWires, pointCorrectionX,
    pointCorrectionYInf, garb, List.mem_cons, List.mem_append, List.mem_range'_1,
    List.mem_singleton, List.not_mem_nil, or_false] at hw
  (try dsimp only [Wire] at *); omega

theorem sel_support (start : Nat) : straightWires (selProgram start) ⊆ support := by
  have hl : ∀ op ∈ selOps, lookupOpWires op ⊆ support := by
    rw [selOps]
    apply unaryLookupOps_support
    · exact mem_support (Or.inl rfl)
    · intro w hw
      simp only [selPaths, List.mem_range'_1] at hw
      exact mem_support (by (try dsimp only [Wire] at *); omega)
    · intro w hw
      have hb := (tableAddressTree_mem_index selBits 0 1 w).mp hw
      simp only [selBits, List.mem_append, List.mem_range'_1, List.mem_singleton, List.not_mem_nil, or_false] at hb
      exact mem_support (by (try dsimp only [Wire] at *); omega)
    · intro label q hq
      apply lookupLeafGates_support _ _ _ hq
      intro port hp
      rcases List.mem_append.mp hp with h | h
      · have := mem_point (List.of_mem_zip h).2
        exact mem_support (by (try dsimp only [Wire] at *); omega)
      · have := mem_garb (List.of_mem_zip h).2
        exact mem_support (by (try dsimp only [Wire] at *); omega)
  rw [selProgram, straightWires_castFinish, lookupProgram_support]
  intro w hw
  obtain ⟨op, hop, hw⟩ := List.mem_flatMap.mp hw
  exact hl op hop hw

theorem swap_support (start : Nat) : straightWires (swapProgram start) ⊆ support := by
  rw [swapProgram, literalProgram_support]
  intro w hw
  rcases swap_wires w hw with h | h | h
  · exact mem_support (by (try dsimp only [Wire] at *); omega)
  · have := mem_point h
    exact mem_support (by (try dsimp only [Wire] at *); omega)
  · have := mem_garb h
    exact mem_support (by (try dsimp only [Wire] at *); omega)

theorem clear_support (start : Nat) : straightWires (clearProgram start) ⊆ support := by
  rw [clearProgram, straightWires_castFinish, WEX.support_agrees]
  have hsc : scratch ∈ clearData.map MeasuredClear.ClearPort.target := by
    rw [clearData_targets]
    simp [scratch, garb]
  apply List.Subset.trans (MeasuredClear.measuredClear_static9 _ _ _ _ _ _ _ hsc start)
  intro w hw
  rw [MeasuredClear.clearSupport9, clearData_targets, high_index, MeasuredClear.hotBank9, hot_eq,
    low_eq] at hw
  simp only [high, clearPaths, garb, List.mem_cons, List.mem_append, List.mem_range'_1,
    List.mem_singleton, List.not_mem_nil, or_false] at hw
  exact mem_support (by (try dsimp only [Wire] at *); omega)

theorem program_support (start : Nat) : straightWires (program start) ⊆ support := by
  rw [program, straightWires_castFinish, straightWires_append, straightWires_append]
  exact List.append_subset.mpr ⟨List.append_subset.mpr ⟨sel_support start, swap_support _⟩,
    clear_support _⟩

theorem sel_residue (start : Nat) : residue (selProgram start) = 0 := by
  rw [selProgram, residue_cast, residue_lookup, selOps]
  apply WEXCredit.residue_unary
  intro label root
  unfold selLeaf
  generalize ((pointRefs (row (2 * label))).zip pointLogicalWires ++
    (pointRefs (row (2 * label + 1))).zip garb) = ports
  unfold lookupLeafGates
  induction ports with
  | nil => rfl
  | cons p ps ih => simpa [templateResidue, tCost] using ih

theorem swap_residue (start : Nat) : residue (swapProgram start) = 0 := by
  rw [swapProgram]
  exact residue_literal_HPFree _ swap_hp

theorem clear_residue (start : Nat) : residue (clearProgram start) = 0 := by
  rw [clearProgram, residue_cast]
  exact MeasuredClear.measuredClear_residue9 _ _ _ _ _ _ _ _

theorem program_residue (start : Nat) : residue (program start) = 0 := by
  rw [program, residue_cast, residue_append, residue_append, sel_residue, swap_residue, clear_residue] <;> rfl

theorem sel_added (start : Nat) : added (selProgram start) = 131071 := by
  have h := exact_t (selProgram start) (sel_residue start) (fun _ => false) (fun _ => false)
  have ht : ((selProgram start).instantiate (fun _ => false) (fun _ => false)).tCount = 7 * 131071 := by
    rw [selProgram, castFinish_instantiate, lookupProgram_tCount, selOps_circuit,
      tableLookupProgram_tCount (selMask (fun _ => false)) selBits selPaths 836 (by decide +kernel) (by decide +kernel)] <;> rfl
  exact Nat.eq_of_mul_eq_mul_left (by decide +kernel) (h.symm.trans ht)

theorem swap_added (start : Nat) : added (swapProgram start) = 513 := by
  rw [swapProgram, added_literal, swapCircuit, swapWords_ccx, point_length, garb_length, Nat.min_self]

theorem clear_added (start : Nat) : added (clearProgram start) = 1013 := by
  have h := exact_t (clearProgram start) (clear_residue start) (fun _ => false) (fun _ => false)
  have ht : ((clearProgram start).instantiate (fun _ => false) (fun _ => false)).tCount = 7 * 1013 := by
    rw [clearProgram, castFinish_instantiate,
      MeasuredClear.measuredClear_tCount9 _ _ _ _ _ _ _ clear_layout, clear_nodes] <;> rfl
  exact Nat.eq_of_mul_eq_mul_left (by decide +kernel) (h.symm.trans ht)

theorem program_added (start : Nat) : added (program start) = 132597 := by
  rw [program, added_cast, added_append, added_append, sel_added, swap_added, clear_added] <;> rfl

theorem program_credit (coeffs : Fin 262144 → PointCoeff) (Q : Point) (start : Nat)
    (history : Fin start → Bool) : added (program start) = 132597 := program_added start

theorem program_tCount (coeffs : Fin 262144 → PointCoeff) (Q : Point) (start : Nat)
    (history : Fin start → Bool) :
    ((program start).instantiate (readConstant coeffs Q) history).tCount = 928179 := by
  rw [exact_t _ (program_residue start), program_added] <;> rfl

/-! ### The window -/

def windowGeneric {n : Nat} (rows : Fin 262144 → Fin n) : Single.Window n :=
  ⟨SelectSchedule18.bits.reverse, 132606, fun start => reindexStraight rows (program start)⟩

theorem window_law_generic {n : Nat} (coeffs : Fin n → PointCoeff) (rows : Fin 262144 → Fin n)
    (init : Point → Nat → Point)
    (hcoeff : ∀ Q, order • Q = 0 → ∀ a : Fin 262144,
      constantPoint Q (coeffs (rows a)) = init Q a.val) :
    Single.WindowLaw coeffs (windowGeneric rows) (SelectSchedule18.update init)
      SelectSchedule18.Input := by
  intro Q hQ hn start history
  have hvalid := program_coherent (fun a => coeffs (rows a)) Q start history
  have hupdate : (fun s => pointWrite
      (SelectSchedule18.tablePoint (fun a => coeffs (rows a)) Q
        (tableAddressValue SelectSchedule18.bits s)) s) = SelectSchedule18.update init Q := by
    funext s
    unfold SelectSchedule18.tablePoint SelectSchedule18.update
    have hbound : tableAddressValue SelectSchedule18.bits s < 262144 := by
      have hb := tableAddressValue_lt SelectSchedule18.bits s
      have hlen : SelectSchedule18.bits.length = 18 := by decide +kernel
      simpa only [hlen] using hb
    simp only [Nat.mod_eq_of_lt hbound]
    rw [hcoeff Q hQ]
  rw [hupdate] at hvalid
  unfold windowGeneric
  rw [reindexStraight_instantiate,
    readConstant_reindex rows (fun a => coeffs (rows a)) coeffs Q (fun _ => rfl)]
  exact hvalid

theorem window_wellFormed {n : Nat} (rows : Fin 262144 → Fin n) (start : Nat) :
    ((windowGeneric rows).program start).WellFormed := by
  unfold windowGeneric
  exact (reindexStraight_wellFormed rows (program start)).mpr (program_wellFormed start)

theorem window_slots {n : Nat} (rows : Fin 262144 → Fin n) (start : Nat) :
    ((windowGeneric rows).program start).gateSlots ≤ 1000000000 := by
  unfold windowGeneric
  rw [reindexStraight_gateSlots]
  exact program_slots start

theorem window_support {n : Nat} (rows : Fin 262144 → Fin n) (start : Nat) :
    straightWires ((windowGeneric rows).program start) ⊆ support := by
  unfold windowGeneric
  rw [straightWires_reindex]
  exact program_support start

theorem window_t {n : Nat} (coeffs : Fin n → PointCoeff) (rows : Fin 262144 → Fin n)
    (Q : Point) (start : Nat) (history : Fin start → Bool) :
    (((windowGeneric rows).program start).instantiate (readConstant coeffs Q) history).tCount = 928179 := by
  unfold windowGeneric
  rw [reindexStraight_instantiate,
    readConstant_reindex rows (fun a => coeffs (rows a)) coeffs Q (fun _ => rfl)]
  exact program_tCount (fun a => coeffs (rows a)) Q start history

theorem window_credit {n : Nat} (coeffs : Fin n → PointCoeff) (rows : Fin 262144 → Fin n)
    (Q : Point) (start : Nat) (history : Fin start → Bool) :
    added ((windowGeneric rows).program start) = 132597 := by
  unfold windowGeneric
  rw [added_reindex]
  exact program_added start

end
end ShorECDLP.Entrant.First18


namespace ShorECDLP.Entrant.Single
open Quantum Secp256k1 Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] fourierOutcomes
theorem select18_nodup : SelectSchedule18.bits.Nodup := by decide +kernel

theorem select18_not_point : ∀ v ∈ SelectSchedule18.bits, v ∉ pointLogicalWires := by decide +kernel

theorem select18_clean (s : BasisState) (hs : FirstWindowInput s)
    (hz : Clean streamAddress s) : Clean SelectSchedule18.bits s := by
  intro v hv
  simp only [SelectSchedule18.bits,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with hv | rfl
  · have hb : 855 ≤ v ∧ v < 872 := by simpa only [List.mem_range'_1] using hv
    by_cases he : v = 871
    · subst v; exact hs.2 871 (by decide +kernel) (by decide +kernel)
    · apply hz v
      simp only [streamAddress, List.mem_range'_1]
      dsimp only [Wire] at *
      omega
  · exact hs.2 537 (by decide +kernel) (by decide +kernel)

theorem select18_assigned_digit (s : BasisState) (input : List Bool)
    (hi : input.length = SelectSchedule18.bits.length) :
    tableAddressValue SelectSchedule18.bits (phaseWordState SelectSchedule18.bits input s) = boolWordToNat input := by
  have he (ws : List Wire) (t : BasisState) :
      tableAddressValue ws t = boolWordToNat (wireValues ws t) := by
    induction ws with
    | nil => rfl
    | cons w ws ih =>
      change (t w).toNat + 2 * tableAddressValue ws t =
        (t w).toNat + 2 * boolWordToNat (wireValues ws t)
      rw [ih]
  rw [he,phaseWordState_word _ select18_nodup input hi s]


theorem select18_window_point_sum_generic (init : Point → Nat → Point) (Q : Point) (prior output : List Bool)
    (s : BasisState) (hs : FirstWindowInput s) (hz : Clean streamAddress s) :
    fourierBranch .inverse SelectSchedule18.bits.reverse prior output
      (Finsupp.lmapDomain ℂ ℂ (SelectSchedule18.update init Q)
        (Quantum.run (SelectSchedule18.bits.map Gate.H) (ket s))) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 18) •
        ((fourierOutcomes 18).map (fun input =>
          fourierBitAmplitude .inverse input.reverse prior output •
            ket (pointWrite (init Q (boolWordToNat input)) s))).sum := by
  have hlen : SelectSchedule18.bits.length = 18 := by decide +kernel
  rw [window_branch_uniform .inverse SelectSchedule18.bits select18_nodup
    (SelectSchedule18.update init Q) prior output s (select18_clean s hs hz) (by
      intro input hi
      have he : SelectSchedule18.bits.map (SelectSchedule18.update init Q (phaseWordState SelectSchedule18.bits input s)) =
          SelectSchedule18.bits.map (phaseWordState SelectSchedule18.bits input s) := by
        apply List.map_congr_left
        intro v hv
        exact pointWrite_frame _ _ v (select18_not_point v hv)
      rw [he]
      exact phaseWordState_word _ select18_nodup input
        ((fourierOutcomes_mem _ _).mp hi) s), hlen]
  apply congrArg (fun ψ : State => (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 18) • ψ)
  apply congrArg List.sum
  apply List.map_congr_left
  intro input hi
  unfold SelectSchedule18.update
  rw [select18_assigned_digit s input (by simpa only [hlen] using (fourierOutcomes_mem _ _).mp hi),
    clear_assigned_point _ input s (select18_clean s hs hz) select18_not_point]
end
end ShorECDLP.Entrant.Single


namespace ShorECDLP.Entrant.SelectSchedule18
open Quantum Secp256k1 Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
theorem input_of_strong (s : BasisState) (hs : FirstWindowInput s) : Input s := by
  refine ⟨hs.1,?_⟩
  intro v hv ha
  apply hs.2 v hv
  intro hh
  apply ha
  simp only [streamAddress] at hh
  change v ∈ List.range' 855 17 ++ [537]
  apply List.mem_append_left
  have hb : 855 ≤ v ∧ v < 871 := by simpa only [List.mem_range'_1] using hh
  simp only [List.mem_range'_1]
  dsimp only [Wire] at *
  omega

theorem input_update (s : BasisState) (hs : Input s) (w : Wire) (hw : w∈bits) (b : Bool) :
    Input (s[w↦b]) := by
  have ne : (836:Wire)≠w := by
    simp only [bits,List.mem_append,List.mem_range'_1,List.mem_cons,List.not_mem_nil,or_false] at hw
    dsimp only [Wire] at *
    omega
  refine ⟨by simpa only [upd,if_neg ne] using hs.1,?_⟩
  intro v hv ha
  have nvw : v≠w := by intro e; exact ha (e ▸ hw)
  simpa only [upd,if_neg nvw] using hs.2 v hv ha


private theorem support_add {V : BasisState → Prop} {ψ φ : State}
    (hψ : SupportedOn V ψ) (hφ : SupportedOn V φ) : SupportedOn V (ψ+φ) := by
  intro s hs
  by_cases h : ψ s=0
  · exact hφ s (by simpa [h] using hs)
  · exact hψ s h
private theorem support_smul {V : BasisState → Prop} {ψ : State} (c : ℂ)
    (hψ : SupportedOn V ψ) : SupportedOn V (c • ψ) := by
  intro s hs
  apply hψ s
  intro h
  exact hs (by simp [h])

private theorem support_linear_FirstValidity (V W : BasisState → Prop) (L : State →ₗ[ℂ] State)
    (hL : ∀ s, V s → SupportedOn W (L (ket s))) (ψ : State)
    (hψ : SupportedOn V ψ) : SupportedOn W (L ψ) := by
  classical
  induction ψ using Finsupp.induction with
  | zero => simp
  | single_add s c ψ hs hc ih =>
    have hz : ψ s=0 := by simpa using hs
    have hvs : V s := hψ s (by simp [hz,hc])
    have hvψ : SupportedOn V ψ := by
      intro u hu
      apply hψ u
      by_cases he : u=s
      · subst u; exact (hu hz).elim
      · simpa [he] using hu
    have he : Finsupp.single s c=c • ket s := by ext u; simp [ket]
    rw [map_add,he,map_smul]
    exact support_add (support_smul c (hL s hvs)) (ih hvψ)

theorem input_H (w : Wire) (hw : w∈bits) (ψ : State) (hψ : SupportedOn Input ψ) :
    SupportedOn Input (applyGate (.H w) ψ) := by
  apply support_linear_FirstValidity Input Input (applyGate (.H w)) ?_ ψ hψ
  intro s hs
  rw [applyGate_ket]
  exact support_add
    (support_smul _ (supportedOn_ket _ _ (input_update s hs w hw false)))
    (support_smul _ (supportedOn_ket _ _ (input_update s hs w hw true)))

theorem input_prepare (ws : List Wire) (hws : ∀ w∈ws,w∈bits) (ψ : State) (hψ : SupportedOn Input ψ) :
    SupportedOn Input (Quantum.run (ws.map Gate.H) ψ) := by
  induction ws generalizing ψ with
  | nil => exact hψ
  | cons w ws ih =>
    exact ih (fun v hv=>hws v (List.mem_cons_of_mem w hv)) _
      (input_H w (hws w (by simp)) ψ hψ)
end ShorECDLP.Entrant.SelectSchedule18
end

/-! ### Consolidated from `KnownRoot.lean` -/
section
namespace ShorECDLP.Entrant.KnownRoot
open Quantum Challenge AndGadget Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem unitary_prefix_congr (old new : Circuit) (tail : AdaptiveCircuit)
    (ideal : State →ₗ[ℂ] State) (Valid : BasisState → Prop)
    (he : ∀ s, Valid s → Quantum.run old (ket s) = Quantum.run new (ket s))
    (hc : CoherentlyImplementsOn (.unitary old tail) ideal Valid) :
    CoherentlyImplementsOn (.unitary new tail) ideal Valid := by
  obtain ⟨cs,hc,hm⟩ := hc
  refine ⟨cs,?_,hm⟩
  simp only [AdaptiveCircuit.run,List.forall₂_map_left_iff] at hc ⊢
  apply hc.imp
  intro b c hb s hs
  change b.kraus (Quantum.run new (ket s)) = c • ideal (ket s)
  rw [← he s hs]
  exact hb s hs

def seededZeroAnd (_root bit path : Wire) : Circuit := [.X bit,.CX bit path,.X bit]

theorem seededZeroAnd_ket (root bit path : Wire) (s : BasisState)
    (hr : s root=true) (hneq : root≠bit) :
    Quantum.run (computeZeroAnd root bit path) (ket s) = Quantum.run (seededZeroAnd root bit path) (ket s) := by
  rw [run_ket_agrees_classical _ _ (by simp [computeZeroAnd]),
    run_ket_agrees_classical _ _ (by simp [seededZeroAnd])]
  congr 1
  funext w
  simp [computeZeroAnd,seededZeroAnd,Classical.run,Classical.applyGate,upd,hr,hneq]


theorem lookup_prefix_congr {n} (root bit path : Wire) (ops : List (LookupOp n))
    (read : ConstantBit n → Bool) (ideal : State →ₗ[ℂ] State) (Valid : BasisState → Prop)
    (hneq : root≠bit) (hr : ∀ s,Valid s→s root=true)
    (hc : CoherentlyImplementsOn (lookupCircuit read (ordinaryOp (computeZeroAnd root bit path)::ops)) ideal Valid) :
    CoherentlyImplementsOn (lookupCircuit read (ordinaryOp (seededZeroAnd root bit path)::ops)) ideal Valid := by
  simp only [lookupCircuit,ordinaryOp,literal_gates] at hc ⊢
  exact unitary_prefix_congr _ _ _ _ _ (fun s hs => seededZeroAnd_ket root bit path s (hr s hs) hneq) hc

theorem lookup_prefix_measurements {n} (root bit path : Wire) (ops : List (LookupOp n)) :
    lookupMeasurements (ordinaryOp (seededZeroAnd root bit path)::ops) =
      lookupMeasurements (ordinaryOp (computeZeroAnd root bit path)::ops) := rfl

theorem lookup_prefix_weight {n} (root bit path : Wire) (ops : List (LookupOp n)) (start : Nat) :
    ConditionalCatalyst.weight4 (lookupProgram n (ordinaryOp (seededZeroAnd root bit path)::ops) start)+4 =
      ConditionalCatalyst.weight4 (lookupProgram n (ordinaryOp (computeZeroAnd root bit path)::ops) start) := by
  simp [lookupProgram,ordinaryOp,seededZeroAnd,computeZeroAnd,gateProgram,
    ConditionalCatalyst.weight4_append,ConditionalCatalyst.weight4,ConditionalCatalyst.weightedLiteral,
    ConditionalCatalyst.weightedGate,ConditionalCatalyst.phaseTwoGate,ShorECDLP.tCost]
  omega


theorem first18_head : First18.selOps = ordinaryOp (computeZeroAnd 836 856 519)::First18.selOps.tail := by
  rw [First18.selOps,First18.selBits,First18.selPaths]
  rfl

def first18_seededOps : List (LookupOp 262144) :=
  ordinaryOp (seededZeroAnd 836 856 519)::First18.selOps.tail

theorem first18_seeded_coherent (read : ConstantBit 262144 → Bool) :
    CoherentlyImplementsOn (lookupCircuit read first18_seededOps)
      (Finsupp.lmapDomain ℂ ℂ (tableLookupState (First18.selMask read) First18.selBits 836))
      SelectSchedule18.Input := by
  have hc := First18.sel_coherent read
  obtain ⟨cs,ha,hm⟩ := hc
  have hc : CoherentlyImplementsOn (lookupCircuit read First18.selOps)
      (Finsupp.lmapDomain ℂ ℂ (tableLookupState (First18.selMask read) First18.selBits 836))
      SelectSchedule18.Input :=
    ⟨cs,ha.imp (fun b c hb s hs => hb s (First18.input_selPaths s hs)),hm⟩
  rw [first18_head] at hc
  exact lookup_prefix_congr 836 856 519 First18.selOps.tail read _ _ (by decide) (fun s hs => hs.1) hc


open WEXCredit

theorem lookup_prefix_residue {n} (root bit path : Wire) (ops : List (LookupOp n)) (start : Nat) :
    residue (lookupProgram n (ordinaryOp (seededZeroAnd root bit path)::ops) start) =
      residue (lookupProgram n (ordinaryOp (computeZeroAnd root bit path)::ops) start) := by
  simp [lookupProgram,ordinaryOp,seededZeroAnd,computeZeroAnd,gateProgram,residue_append,residue,primitivePhaseCost]

theorem lookup_prefix_slots {n} (root bit path : Wire) (ops : List (LookupOp n)) (start : Nat) :
    (lookupProgram n (ordinaryOp (seededZeroAnd root bit path)::ops) start).gateSlots =
      (lookupProgram n (ordinaryOp (computeZeroAnd root bit path)::ops) start).gateSlots := by
  simp [lookupProgram,ordinaryOp,seededZeroAnd,computeZeroAnd,gateProgram,Straight.gateSlots_append,Straight.gateSlots]

theorem lookup_prefix_support {n} (root bit path : Wire) (ops : List (LookupOp n)) (start : Nat) :
    straightWires (lookupProgram n (ordinaryOp (seededZeroAnd root bit path)::ops) start) ⊆
      straightWires (lookupProgram n (ordinaryOp (computeZeroAnd root bit path)::ops) start) := by
  intro w hw
  simp only [lookupProgram,ordinaryOp,seededZeroAnd,computeZeroAnd,straightWires_append,
    gateProgram_support,List.flatMap_map,templateGateWires,gateWires,List.flatMap_cons,
    List.flatMap_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw ⊢
  tauto

theorem first18_seeded_measurements : lookupMeasurements first18_seededOps = 131071 := by
  have h := First18.selOps_measurements
  rw [first18_head] at h
  simpa only [first18_seededOps,ordinaryOp,lookupMeasurements] using h

def first18_seededSel (start : Nat) : Straight 262144 start (start+131071) :=
  castFinish (by rw [first18_seeded_measurements]) (lookupProgram 262144 first18_seededOps start)

def first18_seededProgram (start : Nat) : Straight 262144 start (start+132606) :=
  castFinish (First18.program_finish start)
    (((first18_seededSel start).append (First18.swapProgram (start+131071))).append (First18.clearProgram (start+131071)))

def first18_seededSource (read : ConstantBit 262144 → Bool) : AdaptiveCircuit :=
  ((lookupCircuit read first18_seededOps).seq (.unitary First18.swapCircuit .done)).seq (First18.clearSource read)

theorem first18_seededSource_coherent (coeffs : Fin 262144 → PointCoeff) (Q : Secp256k1.Point) :
    CoherentlyImplementsOn (first18_seededSource (readConstant coeffs Q))
      (Finsupp.lmapDomain ℂ ℂ (fun s => pointWrite (SelectSchedule18.tablePoint coeffs Q
        (tableAddressValue SelectSchedule18.bits s)) s)) SelectSchedule18.Input := by
  have h := First18.source_coherent coeffs Q
  unfold First18.source at h
  rw [first18_head] at h
  simp only [first18_seededSource,first18_seededOps,lookupCircuit,ordinaryOp,literal_gates,
    AdaptiveCircuit.seq] at h ⊢
  exact unitary_prefix_congr _ _ _ _ _ (fun s hs => seededZeroAnd_ket 836 856 519 s hs.1 (by decide)) h

theorem first18_seededSel_run (read : ConstantBit 262144 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((first18_seededSel start).instantiate read history).run = (lookupCircuit read first18_seededOps).run := by
  rw [first18_seededSel,castFinish_instantiate,lookupProgram_run]

theorem first18_seededProgram_run (read : ConstantBit 262144 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((first18_seededProgram start).instantiate read history).run = (first18_seededSource read).run := by
  rw [first18_seededProgram,castFinish_instantiate,
    append_run_fixed _ _ _ _ _ (fun h => First18.clear_run read _ h),AdaptiveCircuit.run_seq,
    append_run_fixed _ _ _ _ _ (fun h => First18.swap_run read _ h),AdaptiveCircuit.run_seq,
    first18_seededSel_run read start history]
  simp only [first18_seededSource,AdaptiveCircuit.run_seq]

theorem first18_seededProgram_coherent (coeffs : Fin 262144 → PointCoeff) (Q : Secp256k1.Point)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((first18_seededProgram start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (fun s => pointWrite (SelectSchedule18.tablePoint coeffs Q
        (tableAddressValue SelectSchedule18.bits s)) s)) SelectSchedule18.Input := by
  unfold CoherentlyImplementsOn
  rw [first18_seededProgram_run]
  exact first18_seededSource_coherent coeffs Q


open ConditionalCatalyst Secp256k1
set_option linter.unusedSimpArgs false

theorem first18_seededSel_residue (start : Nat) : residue (first18_seededSel start) = 0 := by
  have h := lookup_prefix_residue 836 856 519 First18.selOps.tail start
  have he : residue (first18_seededSel start) = residue (First18.selProgram start) := by
    simp only [first18_seededSel,First18.selProgram,residue_cast,first18_seededOps]
    conv_rhs => rw [first18_head]
    exact h
  exact he.trans (First18.sel_residue start)

theorem first18_seededProgram_residue (start : Nat) : residue (first18_seededProgram start) = 0 := by
  rw [first18_seededProgram,residue_cast,residue_append,residue_append,first18_seededSel_residue,
    First18.swap_residue,First18.clear_residue]

theorem first18_seededSel_weight (start : Nat) : weight4 (first18_seededSel start)+4 = weight4 (First18.selProgram start) := by
  have h := lookup_prefix_weight 836 856 519 First18.selOps.tail start
  simp only [first18_seededSel,First18.selProgram,weight4_cast,first18_seededOps]
  conv_rhs => rw [first18_head]
  exact h

theorem first18_seededProgram_added (start : Nat) : added (first18_seededProgram start) = 132596 := by
  have hs := first18_seededSel_weight start
  have h : weight4 (first18_seededProgram start)+4 = weight4 (First18.program start) := by
    simp only [first18_seededProgram,First18.program,weight4_cast,weight4_append]
    omega
  rw [weight4_zero _ (first18_seededProgram_residue start),weight4_zero _ (First18.program_residue start),First18.program_added] at h
  omega

theorem first18_seededSel_slots (start : Nat) : (first18_seededSel start).gateSlots = (First18.selProgram start).gateSlots := by
  have h := lookup_prefix_slots 836 856 519 First18.selOps.tail start
  simp only [first18_seededSel,First18.selProgram,castFinish_gateSlots,first18_seededOps]
  conv_rhs => rw [first18_head]
  exact h

theorem first18_seededProgram_slots (start : Nat) : (first18_seededProgram start).gateSlots ≤ 1000000000 := by
  have h := First18.program_slots start
  simpa only [first18_seededProgram,First18.program,castFinish_gateSlots,Straight.gateSlots_append,
    first18_seededSel_slots] using h

theorem first18_seededSel_support (start : Nat) : straightWires (first18_seededSel start) ⊆ First18.support := by
  have h := lookup_prefix_support 836 856 519 First18.selOps.tail start
  have he : straightWires (first18_seededSel start) ⊆ straightWires (First18.selProgram start) := by
    simp only [first18_seededSel,First18.selProgram,straightWires_castFinish,first18_seededOps]
    conv_rhs => rw [first18_head]
    exact h
  exact he.trans (First18.sel_support start)

theorem first18_seededProgram_support (start : Nat) : straightWires (first18_seededProgram start) ⊆ First18.support := by
  rw [first18_seededProgram,straightWires_castFinish,straightWires_append,straightWires_append]
  exact List.append_subset.mpr ⟨List.append_subset.mpr ⟨first18_seededSel_support start,First18.swap_support _⟩,First18.clear_support _⟩

theorem first18_seededOps_physical : ∀ op ∈ first18_seededOps, op.Physical := by
  intro op ho
  simp only [first18_seededOps,List.mem_cons] at ho
  rcases ho with rfl | ho
  · simp [ordinaryOp,seededZeroAnd,LookupOp.Physical,TemplateGate.WellFormed,Gate.WellFormed]
  · exact First18.selOps_physical op (List.mem_of_mem_tail ho)

theorem first18_seededProgram_wellFormed (start : Nat) : (first18_seededProgram start).WellFormed := by
  have hs : (first18_seededSel start).WellFormed := by
    rw [first18_seededSel,castFinish_wellFormed]
    exact lookupProgram_wellFormed _ first18_seededOps_physical _
  rw [first18_seededProgram,castFinish_wellFormed]
  exact straight_append_wellFormed _ _
    (straight_append_wellFormed _ _ hs (First18.swap_wellFormed _)) (First18.clear_wellFormed _)

def windowGeneric {n : Nat} (rows : Fin 262144 → Fin n) : Single.Window n :=
  ⟨SelectSchedule18.bits.reverse,132606,fun start => reindexStraight rows (first18_seededProgram start)⟩

theorem program_tCount (coeffs : Fin 262144 → PointCoeff) (Q : Secp256k1.Point) (start : Nat) (history : Fin start → Bool) :
    ((first18_seededProgram start).instantiate (readConstant coeffs Q) history).tCount = 928172 := by
  rw [exact_t _ (first18_seededProgram_residue start),first18_seededProgram_added]

theorem window_law_generic {n : Nat} (coeffs : Fin n → PointCoeff) (rows : Fin 262144 → Fin n)
    (init : Point → Nat → Point)
    (hcoeff : ∀ Q, order • Q = 0 → ∀ a : Fin 262144,
      constantPoint Q (coeffs (rows a)) = init Q a.val) :
    Single.WindowLaw coeffs (windowGeneric rows) (SelectSchedule18.update init)
      SelectSchedule18.Input := by
  intro Q hQ hn start history
  have hvalid := first18_seededProgram_coherent (fun a => coeffs (rows a)) Q start history
  have hupdate : (fun s => pointWrite
      (SelectSchedule18.tablePoint (fun a => coeffs (rows a)) Q
        (tableAddressValue SelectSchedule18.bits s)) s) = SelectSchedule18.update init Q := by
    funext s
    unfold SelectSchedule18.tablePoint SelectSchedule18.update
    have hbound : tableAddressValue SelectSchedule18.bits s < 262144 := by
      have hb := tableAddressValue_lt SelectSchedule18.bits s
      have hlen : SelectSchedule18.bits.length = 18 := by decide +kernel
      simpa only [hlen] using hb
    simp only [Nat.mod_eq_of_lt hbound]
    rw [hcoeff Q hQ]
  rw [hupdate] at hvalid
  unfold windowGeneric
  rw [reindexStraight_instantiate,
    readConstant_reindex rows (fun a => coeffs (rows a)) coeffs Q (fun _ => rfl)]
  exact hvalid

theorem window_wellFormed {n : Nat} (rows : Fin 262144 → Fin n) (start : Nat) :
    ((windowGeneric rows).program start).WellFormed := by
  unfold windowGeneric
  exact (reindexStraight_wellFormed rows (first18_seededProgram start)).mpr (first18_seededProgram_wellFormed start)

theorem window_slots {n : Nat} (rows : Fin 262144 → Fin n) (start : Nat) :
    ((windowGeneric rows).program start).gateSlots ≤ 1000000000 := by
  unfold windowGeneric
  rw [reindexStraight_gateSlots]
  exact first18_seededProgram_slots start

theorem window_support {n : Nat} (rows : Fin 262144 → Fin n) (start : Nat) :
    straightWires ((windowGeneric rows).program start) ⊆ First18.support := by
  unfold windowGeneric
  rw [straightWires_reindex]
  exact first18_seededProgram_support start

theorem window_t {n : Nat} (coeffs : Fin n → PointCoeff) (rows : Fin 262144 → Fin n)
    (Q : Point) (start : Nat) (history : Fin start → Bool) :
    (((windowGeneric rows).program start).instantiate (readConstant coeffs Q) history).tCount = 928172 := by
  unfold windowGeneric
  rw [reindexStraight_instantiate,
    readConstant_reindex rows (fun a => coeffs (rows a)) coeffs Q (fun _ => rfl)]
  exact program_tCount (fun a => coeffs (rows a)) Q start history

theorem window_credit {n : Nat} (_coeffs : Fin n → PointCoeff) (rows : Fin 262144 → Fin n)
    (_Q : Point) (start : Nat) (_history : Fin start → Bool) :
    added ((windowGeneric rows).program start) = 132596 := by
  unfold windowGeneric
  rw [added_reindex]
  exact first18_seededProgram_added start

#print axioms first18_seededProgram_added
#print axioms window_law_generic
end
end ShorECDLP.Entrant.KnownRoot
end

/-! ### Consolidated from `RootPass.lean` -/
section
namespace ShorECDLP.Entrant.RootPass
open Quantum Challenge AndGadget Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

theorem supported_add (P : BasisState → Prop) (a b : State) (ha : SupportedOn P a) (hb : SupportedOn P b) :
    SupportedOn P (a+b) := by
  intro s hs
  by_cases h : a s = 0
  · apply hb s
    simpa [Finsupp.add_apply,h] using hs
  · exact ha s h

theorem supported_smul (P : BasisState → Prop) (c : ℂ) (a : State) (ha : SupportedOn P a) :
    SupportedOn P (c • a) := by
  intro s hs
  apply ha s
  intro h
  exact hs (by simp [h])

theorem linear_on_supported (P : BasisState → Prop) (f g : State →ₗ[ℂ] State)
    (h : ∀ s,P s → f (ket s)=g (ket s)) (psi : State) (hp : SupportedOn P psi) : f psi=g psi := by
  induction psi using Finsupp.induction with
  | zero => simp
  | single_add s c psi hs hc ih =>
    have hzero : psi s=0 := by simpa using hs
    have hsP : P s := by apply hp s; simp [hzero,hc]
    have hpP : SupportedOn P psi := by
      intro u hu
      apply hp u
      by_cases he : u=s
      · subst u; exact (hu hzero).elim
      · simp [he,hu]
    have hsingle : Finsupp.single s c=c • ket s := by ext u; simp [ket]
    rw [map_add,map_add,hsingle,map_smul,map_smul,h s hsP,ih hpP]

theorem linear_preserves_supported (P : BasisState → Prop) (f : State →ₗ[ℂ] State)
    (h : ∀ s,P s → SupportedOn P (f (ket s))) (psi : State) (hp : SupportedOn P psi) : SupportedOn P (f psi) := by
  induction psi using Finsupp.induction with
  | zero => simpa only [map_zero] using supportedOn_zero P
  | single_add s c psi hs hc ih =>
    have hzero : psi s=0 := by simpa using hs
    have hsP : P s := by apply hp s; simp [hzero,hc]
    have hpP : SupportedOn P psi := by
      intro u hu
      apply hp u
      by_cases he : u=s
      · subst u; exact (hu hzero).elim
      · simp [he,hu]
    have hsingle : Finsupp.single s c=c • ket s := by ext u; simp [ket]
    rw [map_add,hsingle,map_smul]
    exact supported_add P _ _ (supported_smul P c _ (h s hsP)) (ih hpP)

def safe (root : Wire) : Gate → Prop
  | .X t | .H t | .CX _ t | .CCX _ _ t => t≠root
  | .P _ _ _ => True

def seed (root : Wire) : Gate → Gate
  | .CCX a b t => if a=root then .CX b t else if b=root then .CX a t else .CCX a b t
  | g => g

theorem gate_preserves_basis (root : Wire) (g : Gate) (s : BasisState) (hs : s root=true) (hg : safe root g) :
    SupportedOn (fun u => u root=true) (applyGate g (ket s)) := by
  cases g with
  | X t =>
    rw [applyGate_X_ket]
    apply supportedOn_ket
    simpa [upd,Ne.symm hg] using hs
  | CX c t =>
    rw [applyGate_CX_ket]
    apply supportedOn_ket
    simpa [upd,Ne.symm hg] using hs
  | CCX a b t =>
    rw [applyGate_CCX_ket]
    apply supportedOn_ket
    simpa [upd,Ne.symm hg] using hs
  | P dir k t =>
    rw [applyGate_P_ket]
    exact supported_smul _ _ _ (supportedOn_ket _ _ hs)
  | H t =>
    rw [applyGate_H_ket]
    apply supported_add
    · apply supported_smul
      apply supportedOn_ket
      simpa [upd,Ne.symm hg] using hs
    · apply supported_smul
      apply supportedOn_ket
      simpa [upd,Ne.symm hg] using hs

theorem seed_basis (root : Wire) (g : Gate) (s : BasisState) (hs : s root=true) :
    applyGate (seed root g) (ket s)=applyGate g (ket s) := by
  cases g with
  | X t => rfl
  | H t => rfl
  | CX c t => rfl
  | P dir k t => rfl
  | CCX a b t =>
    by_cases ha : a=root
    · subst a; simp [seed,hs,onKet]
    · by_cases hb : b=root
      · subst b; simp [seed,hs,ha,onKet]
      · simp [seed,ha,hb]

theorem gate_preserves (root : Wire) (g : Gate) (psi : State)
    (hp : SupportedOn (fun u => u root=true) psi) (hg : safe root g) :
    SupportedOn (fun u => u root=true) (applyGate g psi) :=
  linear_preserves_supported _ _ (fun s hs => gate_preserves_basis root g s hs hg) psi hp

theorem seed_eq (root : Wire) (g : Gate) (psi : State)
    (hp : SupportedOn (fun u => u root=true) psi) : applyGate (seed root g) psi=applyGate g psi :=
  linear_on_supported _ _ _ (fun s hs => seed_basis root g s hs) psi hp


def safeCircuit (root : Wire) (cs : Circuit) : Prop := ∀ g∈cs,safe root g

def seedCircuit (root : Wire) (cs : Circuit) : Circuit := cs.map (seed root)

theorem circuit_eq_preserves (root : Wire) (cs : Circuit) (psi : State)
    (hp : SupportedOn (fun s => s root=true) psi) (hc : safeCircuit root cs) :
    Quantum.run (seedCircuit root cs) psi=Quantum.run cs psi ∧
      SupportedOn (fun s => s root=true) (Quantum.run cs psi) := by
  induction cs generalizing psi with
  | nil => exact ⟨rfl,hp⟩
  | cons g gs ih =>
    have hg := hc g (by simp)
    have ht := ih (applyGate g psi) (gate_preserves root g psi hp hg) (by intro a ha; exact hc a (by simp [ha]))
    constructor
    · simp only [seedCircuit,List.map_cons,Quantum.run_cons]
      rw [seed_eq root g psi hp]
      exact ht.1
    · exact ht.2

def safeAdaptive (root : Wire) : AdaptiveCircuit → Prop
  | .done => True
  | .unitary cs p => safeCircuit root cs ∧ safeAdaptive root p
  | .xMeasureReset w p0 p1 => w≠root ∧ safeAdaptive root p0 ∧ safeAdaptive root p1

def seedAdaptive (root : Wire) : AdaptiveCircuit → AdaptiveCircuit
  | .done => .done
  | .unitary cs p => .unitary (seedCircuit root cs) (seedAdaptive root p)
  | .xMeasureReset w p0 p1 => .xMeasureReset w (seedAdaptive root p0) (seedAdaptive root p1)

theorem reset_preserves (root w : Wire) (b : Bool) (psi : State) (hw : root≠w)
    (hp : SupportedOn (fun s => s root=true) psi) :
    SupportedOn (fun s => s root=true) (xResetKraus w b psi) := by
  apply AdaptiveCircuit.branch_frame (.xMeasureReset w .done .done) root true
    (by simpa [AdaptiveCircuit.wires] using hw)
    ⟨[b],xResetKraus w b⟩ ?_ psi hp
  cases b <;> simp only [AdaptiveCircuit.run,List.map_singleton,List.mem_append,List.mem_singleton]
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem adaptive_relation (root : Wire) (p : AdaptiveCircuit) (hp : safeAdaptive root p) :
    List.Forall₂ (fun bnew bold => ∀ psi,SupportedOn (fun s => s root=true) psi →
        bnew.kraus psi=bold.kraus psi) (seedAdaptive root p).run p.run := by
  induction p with
  | done => exact .cons (by intro psi hp; rfl) .nil
  | unitary cs p ih =>
    simp only [seedAdaptive,AdaptiveCircuit.run,List.forall₂_map_left_iff,List.forall₂_map_right_iff]
    apply (ih hp.2).imp
    intro bnew bold hb psi hs
    change bnew.kraus (Quantum.run (seedCircuit root cs) psi)=bold.kraus (Quantum.run cs psi)
    have h := circuit_eq_preserves root cs psi hs hp.1
    rw [h.1]
    exact hb _ h.2
  | xMeasureReset w p0 p1 ih0 ih1 =>
    simp only [seedAdaptive,AdaptiveCircuit.run]
    apply List.rel_append
    · simp only [List.forall₂_map_left_iff,List.forall₂_map_right_iff]
      apply (ih0 hp.2.1).imp
      intro bnew bold hb psi hs
      change bnew.kraus (xResetKraus w false psi)=bold.kraus (xResetKraus w false psi)
      exact hb _ (reset_preserves root w false psi (Ne.symm hp.1) hs)
    · simp only [List.forall₂_map_left_iff,List.forall₂_map_right_iff]
      apply (ih1 hp.2.2).imp
      intro bnew bold hb psi hs
      change bnew.kraus (xResetKraus w true psi)=bold.kraus (xResetKraus w true psi)
      exact hb _ (reset_preserves root w true psi (Ne.symm hp.1) hs)

theorem coherent_transfer (root : Wire) (p : AdaptiveCircuit) (ideal : State →ₗ[ℂ] State)
    (Valid : BasisState → Prop) (hs : safeAdaptive root p) (hr : ∀ s,Valid s→s root=true)
    (hc : CoherentlyImplementsOn p ideal Valid) :
    CoherentlyImplementsOn (seedAdaptive root p) ideal Valid := by
  obtain ⟨cs,ha,hm⟩ := hc
  refine ⟨cs,?_,hm⟩
  clear hm
  have he := adaptive_relation root p hs
  generalize hn : (seedAdaptive root p).run = new at he ⊢
  generalize ho : p.run = old at he ha
  clear hn ho
  induction he generalizing cs with
  | nil => cases ha; exact .nil
  | @cons bnew bold new old he ht ih =>
    cases ha with
    | cons hb hc =>
      apply List.Forall₂.cons
      · intro s hs
        rw [he (ket s) (supportedOn_ket _ _ (hr s hs))]
        exact hb s hs
      · exact ih _ hc


def seedTemplate {n} (root : Wire) : TemplateGate n → TemplateGate n
  | .literal g => .literal (seed root g)
  | .whenBit i v g => .whenBit i v (seed root g)

def safeTemplate {n} (root : Wire) : TemplateGate n → Prop
  | .literal g | .whenBit _ _ g => safe root g

def seedProgram {n s e} (root : Wire) : Straight n s e → Straight n s e
  | .done => .done
  | .gate g p => .gate (seedTemplate root g) (seedProgram root p)
  | .recordGate i v g p => .recordGate i v (seed root g) (seedProgram root p)
  | .measure w p => .measure w (seedProgram root p)

def safeProgram {n s e} (root : Wire) : Straight n s e → Prop
  | .done => True
  | .gate g p => safeTemplate root g ∧ safeProgram root p
  | .recordGate _ _ g p => safe root g ∧ safeProgram root p
  | .measure w p => w≠root ∧ safeProgram root p

theorem seedTemplate_instantiate {n} (root : Wire) (g : TemplateGate n)
    (read : ConstantBit n → Bool) :
    (seedTemplate root g).instantiate read = seedCircuit root (g.instantiate read) := by
  cases g with
  | literal g => rfl
  | whenBit i v g =>
    simp only [seedTemplate,TemplateGate.instantiate]
    split <;> rfl

theorem safeTemplate_instantiate {n} (root : Wire) (g : TemplateGate n)
    (read : ConstantBit n → Bool) (h : safeTemplate root g) :
    safeCircuit root (g.instantiate read) := by
  cases g with
  | literal g => simpa [TemplateGate.instantiate,safeCircuit] using h
  | whenBit i v g =>
    simp only [TemplateGate.instantiate]
    split <;> simp_all [safeCircuit,safeTemplate]

theorem seedProgram_instantiate {n s e} (root : Wire) (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    (seedProgram root p).instantiate read history = seedAdaptive root (p.instantiate read history) := by
  induction p with
  | done => rfl
  | gate g p ih => simp only [seedProgram,Straight.instantiate,seedAdaptive,seedTemplate_instantiate,ih]
  | recordGate i v g p ih =>
    simp only [seedProgram,Straight.instantiate,seedAdaptive,ih]
    congr 1
    split <;> rfl
  | measure w p ih => simp only [seedProgram,Straight.instantiate,seedAdaptive,ih]

theorem safeProgram_instantiate {n s e} (root : Wire) (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) (h : safeProgram root p) :
    safeAdaptive root (p.instantiate read history) := by
  induction p with
  | done => trivial
  | gate g p ih => exact ⟨safeTemplate_instantiate root g read h.1,ih history h.2⟩
  | recordGate i v g p ih =>
    refine ⟨?_,ih history h.2⟩
    simp only [safeCircuit]
    split <;> simp_all [safeProgram]
  | measure w p ih => exact ⟨h.1,ih _ h.2,ih _ h.2⟩

theorem seedProgram_coherent {n s e} (root : Wire) (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool)
    (ideal : State →ₗ[ℂ] State) (Valid : BasisState → Prop)
    (hs : safeProgram root p) (hr : ∀ s,Valid s→s root=true)
    (hc : CoherentlyImplementsOn (p.instantiate read history) ideal Valid) :
    CoherentlyImplementsOn ((seedProgram root p).instantiate read history) ideal Valid := by
  rw [seedProgram_instantiate]
  exact coherent_transfer root _ ideal Valid (safeProgram_instantiate root p read history hs) hr hc


theorem seed_wellFormed (root : Wire) (g : Gate) (h : g.WellFormed) : (seed root g).WellFormed := by
  cases g <;> simp only [seed] <;> try exact h
  split
  · exact h.2.2
  · split
    · exact h.2.1
    · exact h

theorem seedTemplate_wellFormed {n} (root : Wire) (g : TemplateGate n)
    (h : g.WellFormed) : (seedTemplate root g).WellFormed := by
  cases g <;> exact seed_wellFormed root _ h

theorem seedProgram_wellFormed {n s e} (root : Wire) (p : Straight n s e)
    (h : p.WellFormed) : (seedProgram root p).WellFormed := by
  induction p with
  | done => trivial
  | gate g p ih => exact ⟨seedTemplate_wellFormed root g h.1,ih h.2⟩
  | recordGate i v g p ih => exact ⟨seed_wellFormed root g h.1,ih h.2⟩
  | measure w p ih => exact ih h

theorem seedProgram_slots {n s e} (root : Wire) (p : Straight n s e) :
    (seedProgram root p).gateSlots=p.gateSlots := by
  induction p <;> simp_all [seedProgram,Straight.gateSlots]

def hit (root : Wire) : Gate → Nat
  | .CCX a b _ => if a=root ∨ b=root then 1 else 0
  | _ => 0

theorem seed_literal_weight (root : Wire) (g : Gate) :
    ConditionalCatalyst.weightedLiteral (seed root g)+4*hit root g=ConditionalCatalyst.weightedLiteral g := by
  cases g <;> simp only [seed,hit]
  all_goals first | rfl | skip
  split <;> split <;> simp_all [ConditionalCatalyst.weightedLiteral,ConditionalCatalyst.weightedGate,
    ShorECDLP.tCost,ConditionalCatalyst.phaseTwoGate]

theorem seed_conditional_weight (root : Wire) (g : Gate) :
    ConditionalCatalyst.weightedGate (seed root g)+7*hit root g=ConditionalCatalyst.weightedGate g := by
  cases g <;> simp only [seed,hit]
  all_goals first | rfl | skip
  split <;> split <;> simp_all [ConditionalCatalyst.weightedGate,
    ShorECDLP.tCost,ConditionalCatalyst.phaseTwoGate]

def literalHits {n s e} (root : Wire) : Straight n s e → Nat
  | .done => 0
  | .gate (.literal g) p => hit root g+literalHits root p
  | .gate (.whenBit _ _ _) p => literalHits root p
  | .recordGate _ _ _ p => literalHits root p
  | .measure _ p => literalHits root p

def conditionalHits {n s e} (root : Wire) : Straight n s e → Nat
  | .done => 0
  | .gate (.literal _) p => conditionalHits root p
  | .gate (.whenBit _ _ g) p => hit root g+conditionalHits root p
  | .recordGate _ _ g p => hit root g+conditionalHits root p
  | .measure _ p => conditionalHits root p

theorem seedProgram_weight {n s e} (root : Wire) (p : Straight n s e) :
    ConditionalCatalyst.weight4 (seedProgram root p)+4*literalHits root p+7*conditionalHits root p=
      ConditionalCatalyst.weight4 p := by
  induction p with
  | done => rfl
  | gate g p ih =>
    cases g with
    | literal g =>
      have h := seed_literal_weight root g
      simp only [seedProgram,seedTemplate,ConditionalCatalyst.weight4,literalHits,conditionalHits]
      omega
    | whenBit i v g =>
      have h := seed_conditional_weight root g
      simp only [seedProgram,seedTemplate,ConditionalCatalyst.weight4,literalHits,conditionalHits]
      omega
  | recordGate i v g p ih =>
    have h := seed_conditional_weight root g
    simp only [seedProgram,ConditionalCatalyst.weight4,literalHits,conditionalHits]
    omega
  | measure w p ih => exact ih


theorem seed_wires (root : Wire) (g : Gate) : gateWires (seed root g) ⊆ gateWires g := by
  cases g <;> simp only [seed] <;> try exact List.Subset.refl _
  split
  · simp [gateWires,List.Subset]
  · split
    · simp [gateWires,List.Subset]
    · exact List.Subset.refl _

theorem seedTemplate_wires {n} (root : Wire) (g : TemplateGate n) :
    templateGateWires (seedTemplate root g) ⊆ templateGateWires g := by
  cases g <;> exact seed_wires root _

theorem seedProgram_wires {n s e} (root : Wire) (p : Straight n s e) :
    straightWires (seedProgram root p) ⊆ straightWires p := by
  induction p with
  | done => exact List.Subset.refl _
  | gate g p ih =>
    exact List.append_subset.mpr ⟨(seedTemplate_wires root g).trans (List.subset_append_left _ _),
      ih.trans (List.subset_append_right _ _)⟩
  | recordGate i v g p ih =>
    exact List.append_subset.mpr ⟨(seed_wires root g).trans (List.subset_append_left _ _),
      ih.trans (List.subset_append_right _ _)⟩
  | measure w p ih =>
    intro x hx
    simp only [seedProgram,straightWires,List.mem_cons] at hx ⊢
    exact hx.imp id (fun h => ih h)

theorem seed_literalCCX (root : Wire) (g : Gate) :
    ConditionalCatalyst.literalCCX (seed root g)+hit root g=ConditionalCatalyst.literalCCX g := by
  cases g <;> simp only [seed,hit]
  all_goals first | rfl | skip
  split <;> split <;> simp_all [ConditionalCatalyst.literalCCX]

theorem seedProgram_added {n s e} (root : Wire) (p : Straight n s e) :
    added (seedProgram root p)+literalHits root p=added p := by
  induction p with
  | done => rfl
  | gate g p ih =>
    cases g with
    | literal g =>
      have h := seed_literalCCX root g
      have ha {a b : Nat} (g : Gate) (q : Straight n a b) :
          added (.gate (.literal g) q)=ConditionalCatalyst.literalCCX g+added q := by cases g <;> simp [added,ConditionalCatalyst.literalCCX]
      rw [seedProgram,seedTemplate,ha,ha]
      simp only [literalHits]
      omega
    | whenBit i v g => exact ih
  | recordGate i v g p ih => exact ih
  | measure w p ih => exact ih


theorem safeProgram_append {n a b c} (root : Wire) (p : Straight n a b) (q : Straight n b c) :
    safeProgram root (p.append q) ↔ safeProgram root p ∧ safeProgram root q := by
  induction p <;> simp_all [Straight.append,safeProgram,and_assoc]

theorem safeProgram_cast {n a b c} (root : Wire) (p : Straight n a b) (h : b=c) :
    safeProgram root (castFinish h p) ↔ safeProgram root p := by subst c; rfl

theorem gateProgram_safe {n start} (root : Wire) (gs : List (TemplateGate n))
    (h : ∀ g∈gs,safeTemplate root g) : safeProgram root (gateProgram (cursor:=start) gs) := by
  induction gs with
  | nil => trivial
  | cons g gs ih => exact ⟨h g (by simp),ih (fun x hx => h x (by simp [hx]))⟩

theorem recordGates_safe {n s e} (root : Wire) (i : Fin s) (gs : Circuit) (p : Straight n s e)
    (hg : safeCircuit root gs) (hp : safeProgram root p) : safeProgram root (recordGates i gs p) := by
  induction gs with
  | nil => exact hp
  | cons g gs ih => exact ⟨hg g (by simp),ih (fun x hx => hg x (by simp [hx]))⟩

def safeOp {n} (root : Wire) : LookupOp n → Prop
  | .gates gs => ∀ g∈gs,safeTemplate root g
  | .erase _ b t => b≠root ∧ t≠root

theorem lookupProgram_safe {n} (root : Wire) (ops : List (LookupOp n)) (start : Nat)
    (h : ∀ op∈ops,safeOp root op) : safeProgram root (lookupProgram n ops start) := by
  induction ops generalizing start with
  | nil => trivial
  | cons op ops ih =>
    have hh := h op (by simp)
    have ht (j : Nat) := ih j (fun op ho => h op (by simp [ho]))
    cases op with
    | gates gs =>
      rw [lookupProgram,safeProgram_append]
      exact ⟨gateProgram_safe root gs hh,ht start⟩
    | erase a b t =>
      rw [lookupProgram,safeProgram_cast,safeProgram_append]
      refine ⟨?_,ht (start+1)⟩
      simp only [andEraseProgram,safeProgram]
      refine ⟨hh.2,recordGates_safe root _ _ _ ?_ trivial⟩
      simp [safeCircuit,controlledZ,safe,hh.1]

theorem ordinaryOp_safe {n} (root : Wire) (gs : Circuit) (h : safeCircuit root gs) :
    safeOp root (ordinaryOp (n:=n) gs) := by
  intro g hg
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hg
  exact h x hx

theorem unaryOps_safe {n} (root : Wire) (leaf : Nat → Wire → List (TemplateGate n))
    (tree : UnaryActionTree) (q : Wire) (paths : List Wire)
    (hl : ∀ label c g,g∈leaf label c → safeTemplate root g)
    (hb : ∀ w∈tree.indexWires,w≠root) (hp : ∀ w∈paths,w≠root) :
    ∀ op∈unaryLookupOps leaf tree q paths,safeOp root op := by
  induction tree generalizing q paths with
  | leaf label => simpa [unaryLookupOps,safeOp] using hl label q
  | node bit zero one iz io =>
    cases paths with
    | nil => simp [unaryLookupOps]
    | cons path rest =>
      have hbit : bit≠root := hb bit (by simp [UnaryActionTree.indexWires])
      have hpath : path≠root := hp path (by simp)
      have hz := iz path rest (fun w hw => hb w (by simp [UnaryActionTree.indexWires,hw]))
        (fun w hw => hp w (by simp [hw]))
      have ho := io path rest (fun w hw => hb w (by simp [UnaryActionTree.indexWires,hw]))
        (fun w hw => hp w (by simp [hw]))
      have h0 : safeOp root (ordinaryOp (n:=n) (computeZeroAnd q bit path)) := by
        apply ordinaryOp_safe
        simp [safeCircuit,computeZeroAnd,safe,hbit,hpath]
      have hc : safeOp root (ordinaryOp (n:=n) [.CX q path]) := by
        apply ordinaryOp_safe
        simp [safeCircuit,safe,hpath]
      have hx : safeOp root (ordinaryOp (n:=n) [.X bit]) := by
        apply ordinaryOp_safe
        simp [safeCircuit,safe,hbit]
      intro op hop
      simp only [unaryLookupOps,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hop
      rcases hop with (((rfl | hz') | rfl) | ho') | rfl | rfl | rfl | rfl
      · exact h0
      · exact hz _ hz'
      · exact hc
      · exact ho _ ho'
      · exact hc
      · exact hx
      · exact ⟨hbit,hpath⟩
      · exact hx



def templateHits {n} (root : Wire) : TemplateGate n → Nat
  | .literal g => hit root g
  | .whenBit _ _ _ => 0

def opHits {n} (root : Wire) : LookupOp n → Nat
  | .gates gs => (gs.map (templateHits root)).sum
  | .erase _ _ _ => 0

def opsHits {n} (root : Wire) (ops : List (LookupOp n)) : Nat := (ops.map (opHits root)).sum

theorem literalHits_append {n a b c} (root : Wire) (p : Straight n a b) (q : Straight n b c) :
    literalHits root (p.append q)=literalHits root p+literalHits root q := by
  induction p with
  | done => simp [Straight.append,literalHits]
  | gate g p ih => cases g <;> simp_all [Straight.append,literalHits,Nat.add_assoc]
  | recordGate i v g p ih => exact ih q
  | measure w p ih => exact ih q

theorem literalHits_cast {n a b c} (root : Wire) (p : Straight n a b) (h : b=c) :
    literalHits root (castFinish h p)=literalHits root p := by subst c; rfl

theorem literalHits_gateProgram {n start} (root : Wire) (gs : List (TemplateGate n)) :
    literalHits root (gateProgram (cursor:=start) gs)=(gs.map (templateHits root)).sum := by
  induction gs with
  | nil => rfl
  | cons g gs ih => cases g <;> simp_all [gateProgram,literalHits,templateHits]

theorem literalHits_recordGates {n s e} (root : Wire) (i : Fin s) (gs : Circuit) (p : Straight n s e) :
    literalHits root (recordGates i gs p)=literalHits root p := by
  induction gs <;> simp_all [recordGates,literalHits]

theorem literalHits_lookupProgram {n} (root : Wire) (ops : List (LookupOp n)) (start : Nat) :
    literalHits root (lookupProgram n ops start)=opsHits root ops := by
  induction ops generalizing start with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | gates gs =>
      simp only [lookupProgram,literalHits_append,literalHits_gateProgram,ih,opsHits,
        List.map_cons,List.sum_cons,opHits]
    | erase a b t =>
      simp only [lookupProgram,literalHits_cast,literalHits_append,andEraseProgram,
        literalHits,literalHits_recordGates,ih,opsHits,List.map_cons,List.sum_cons,opHits,zero_add]

theorem opsHits_append {n} (root : Wire) (a b : List (LookupOp n)) :
    opsHits root (a++b)=opsHits root a+opsHits root b := by simp [opsHits]

theorem unaryOps_hits_zero {n} (root : Wire) (leaf : Nat → Wire → List (TemplateGate n))
    (tree : UnaryActionTree) (q : Wire) (paths : List Wire)
    (hl : ∀ label c,(leaf label c |>.map (templateHits root)).sum=0)
    (hq : q≠root) (hb : ∀ w∈tree.indexWires,w≠root) (hp : ∀ w∈paths,w≠root) :
    opsHits root (unaryLookupOps leaf tree q paths)=0 := by
  induction tree generalizing q paths with
  | leaf label => simpa [unaryLookupOps,opsHits,opHits] using hl label q
  | node bit zero one iz io =>
    cases paths with
    | nil => rfl
    | cons path rest =>
      have hbit : bit≠root := hb bit (by simp [UnaryActionTree.indexWires])
      have hpath : path≠root := hp path (by simp)
      have hz := iz path rest hpath (fun w hw => hb w (by simp [UnaryActionTree.indexWires,hw]))
        (fun w hw => hp w (by simp [hw]))
      have ho := io path rest hpath (fun w hw => hb w (by simp [UnaryActionTree.indexWires,hw]))
        (fun w hw => hp w (by simp [hw]))
      simp only [unaryLookupOps,opsHits_append]
      rw [hz,ho]
      simp [opsHits,opHits,ordinaryOp,computeZeroAnd,templateHits,hit,hq,hbit]

theorem unaryOps_hits_one {n} (root bit path : Wire) (leaf : Nat → Wire → List (TemplateGate n))
    (zero one : UnaryActionTree) (rest : List Wire)
    (hl : ∀ label c,(leaf label c |>.map (templateHits root)).sum=0)
    (hb : ∀ w∈(UnaryActionTree.node bit zero one).indexWires,w≠root)
    (hp : ∀ w∈path::rest,w≠root) :
    opsHits root (unaryLookupOps leaf (.node bit zero one) root (path::rest))=1 := by
  have hpath : path≠root := hp path (by simp)
  have hz := unaryOps_hits_zero root leaf zero path rest hl hpath
    (fun w hw => hb w (by simp [UnaryActionTree.indexWires,hw])) (fun w hw => hp w (by simp [hw]))
  have ho := unaryOps_hits_zero root leaf one path rest hl hpath
    (fun w hw => hb w (by simp [UnaryActionTree.indexWires,hw])) (fun w hw => hp w (by simp [hw]))
  simp only [unaryLookupOps,opsHits_append]
  rw [hz,ho]
  simp [opsHits,opHits,ordinaryOp,computeZeroAnd,templateHits,hit]


open MeasuredClear

def safeRecordOp (root : Wire) : RecordLookupOp → Prop
  | .gates gs => safeCircuit root gs
  | .leaf _ _ => True
  | .erase _ b t => b≠root ∧ t≠root

theorem recordLeaf_safe {n base} (root : Wire) (ports : List (RecordPort n base))
    (scratch row control start : Nat) (hb : base≤start)
    (hs : scratch≠root) (ht : ∀ p∈ports,p.target≠root) :
    safeProgram root (recordLeaf ports scratch row control start hb) := by
  induction ports with
  | nil => trivial
  | cons p ps ih =>
    rw [recordLeaf,safeProgram_append]
    refine ⟨?_,ih (fun p hp => ht p (by simp [hp]))⟩
    simp [mixedCX,safeProgram,safeTemplate,safe,hs,ht p (by simp)]

theorem recordLookupProgram_safe {n base} (root : Wire) (ports : List (RecordPort n base))
    (scratch : Wire) (ops : List RecordLookupOp) (start : Nat) (hb : base≤start)
    (hs : scratch≠root) (ht : ∀ p∈ports,p.target≠root)
    (h : ∀ op∈ops,safeRecordOp root op) :
    safeProgram root (recordLookupProgram ports scratch ops start hb) := by
  induction ops generalizing start with
  | nil => trivial
  | cons op ops ih =>
    have hh := h op (by simp)
    have htail (j : Nat) (hj : base≤j) := ih j hj (fun op ho => h op (by simp [ho]))
    cases op with
    | gates gs =>
      rw [recordLookupProgram,safeProgram_append]
      refine ⟨gateProgram_safe root _ ?_,htail start hb⟩
      intro g hg
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hg
      exact hh x hx
    | leaf row control =>
      rw [recordLookupProgram,safeProgram_append]
      exact ⟨recordLeaf_safe root ports scratch row control start hb hs ht,htail start hb⟩
    | erase a b t =>
      rw [recordLookupProgram,safeProgram_cast,safeProgram_append]
      refine ⟨?_,htail (start+1) (hb.trans (Nat.le_succ start))⟩
      simp only [andEraseProgram,safeProgram]
      refine ⟨hh.2,recordGates_safe root _ _ _ ?_ trivial⟩
      simp [safeCircuit,controlledZ,safe,hh.1]

theorem recordUnaryOps_safe (root : Wire) (tree : UnaryActionTree) (q : Wire) (paths : List Wire)
    (hb : ∀ w∈tree.indexWires,w≠root) (hp : ∀ w∈paths,w≠root) :
    ∀ op∈recordUnaryOps tree q paths,safeRecordOp root op := by
  induction tree generalizing q paths with
  | leaf label => simp [recordUnaryOps,safeRecordOp]
  | node bit zero one iz io =>
    cases paths with
    | nil => simp [recordUnaryOps]
    | cons path rest =>
      have hbit : bit≠root := hb bit (by simp [UnaryActionTree.indexWires])
      have hpath : path≠root := hp path (by simp)
      have hz := iz path rest (fun w hw => hb w (by simp [UnaryActionTree.indexWires,hw]))
        (fun w hw => hp w (by simp [hw]))
      have ho := io path rest (fun w hw => hb w (by simp [UnaryActionTree.indexWires,hw]))
        (fun w hw => hp w (by simp [hw]))
      have h0 : safeRecordOp root (.gates (computeZeroAnd q bit path)) := by
        simp [safeRecordOp,safeCircuit,computeZeroAnd,safe,hbit,hpath]
      have hc : safeRecordOp root (.gates [.CX q path]) := by simp [safeRecordOp,safeCircuit,safe,hpath]
      have hx : safeRecordOp root (.gates [.X bit]) := by simp [safeRecordOp,safeCircuit,safe,hbit]
      intro op hop
      simp only [recordUnaryOps,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hop
      rcases hop with (((rfl | hz') | rfl) | ho') | rfl | rfl | rfl | rfl
      · exact h0
      · exact hz _ hz'
      · exact hc
      · exact ho _ ho'
      · exact hc
      · exact hx
      · exact ⟨hbit,hpath⟩
      · exact hx


def recordOpHits (root : Wire) : RecordLookupOp → Nat
  | .gates gs => (gs.map (hit root)).sum
  | _ => 0

def recordOpsHits (root : Wire) (ops : List RecordLookupOp) : Nat := (ops.map (recordOpHits root)).sum

theorem literalHits_recordLeaf {n base} (root : Wire) (ports : List (RecordPort n base))
    (scratch row control start : Nat) (hb : base≤start) :
    literalHits root (recordLeaf ports scratch row control start hb)=0 := by
  induction ports with
  | nil => rfl
  | cons p ps ih =>
    rw [recordLeaf,literalHits_append]
    simpa [mixedCX,literalHits] using ih

theorem literalHits_recordLookupProgram {n base} (root : Wire) (ports : List (RecordPort n base))
    (scratch : Wire) (ops : List RecordLookupOp) (start : Nat) (hb : base≤start) :
    literalHits root (recordLookupProgram ports scratch ops start hb)=recordOpsHits root ops := by
  induction ops generalizing start with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | gates gs =>
      simp [recordLookupProgram,literalHits_append,literalProgram,literalHits_gateProgram,ih,
        recordOpsHits,List.map_map,Function.comp_def,templateHits,recordOpHits]
    | leaf row control =>
      simp [recordLookupProgram,literalHits_append,literalHits_recordLeaf,ih,recordOpsHits,recordOpHits]
    | erase a b t =>
      simp [recordLookupProgram,literalHits_cast,literalHits_append,andEraseProgram,literalHits,
        literalHits_recordGates,ih,recordOpsHits,recordOpHits]

theorem recordOpsHits_append (root : Wire) (a b : List RecordLookupOp) :
    recordOpsHits root (a++b)=recordOpsHits root a+recordOpsHits root b := by simp [recordOpsHits]
theorem recordUnaryOps_hits_zero (root : Wire) (tree : UnaryActionTree) (q : Wire) (paths : List Wire)
    (hq : q≠root) (hb : ∀ w∈tree.indexWires,w≠root) (hp : ∀ w∈paths,w≠root) :
    recordOpsHits root (recordUnaryOps tree q paths)=0 := by
  induction tree generalizing q paths with
  | leaf label => simp [recordUnaryOps,recordOpsHits,recordOpHits]
  | node bit zero one iz io =>
    cases paths with
    | nil => rfl
    | cons path rest =>
      have hbit : bit≠root := hb bit (by simp [UnaryActionTree.indexWires])
      have hpath : path≠root := hp path (by simp)
      have hz := iz path rest hpath (fun w hw => hb w (by simp [UnaryActionTree.indexWires,hw]))
        (fun w hw => hp w (by simp [hw]))
      have ho := io path rest hpath (fun w hw => hb w (by simp [UnaryActionTree.indexWires,hw]))
        (fun w hw => hp w (by simp [hw]))
      simp only [recordUnaryOps,recordOpsHits_append]
      rw [hz,ho]
      simp [recordOpsHits,recordOpHits,computeZeroAnd,hit,hq,hbit]

theorem recordUnaryOps_hits_one (root bit path : Wire) (zero one : UnaryActionTree) (rest : List Wire)
    (hb : ∀ w∈(UnaryActionTree.node bit zero one).indexWires,w≠root)
    (hp : ∀ w∈path::rest,w≠root) :
    recordOpsHits root (recordUnaryOps (.node bit zero one) root (path::rest))=1 := by
  have hpath : path≠root := hp path (by simp)
  have hz := recordUnaryOps_hits_zero root zero path rest hpath
    (fun w hw => hb w (by simp [UnaryActionTree.indexWires,hw])) (fun w hw => hp w (by simp [hw]))
  have ho := recordUnaryOps_hits_zero root one path rest hpath
    (fun w hw => hb w (by simp [UnaryActionTree.indexWires,hw])) (fun w hw => hp w (by simp [hw]))
  simp only [recordUnaryOps,recordOpsHits_append]
  rw [hz,ho]
  simp [recordOpsHits,recordOpHits,computeZeroAnd,hit]



open WEXCredit
set_option linter.unnecessarySeqFocus false

theorem seed_phaseCost (root : Wire) (g : Gate) : primitivePhaseCost (seed root g)=primitivePhaseCost g := by
  cases g <;> simp only [seed] <;> try rfl
  split <;> first | rfl | skip
  split <;> rfl

theorem seed_tCost_le (root : Wire) (g : Gate) : tCost (seed root g)≤tCost g := by
  cases g <;> simp only [seed] <;> try exact le_rfl
  split
  · simp [tCost]
  · split <;> simp [tCost]

theorem seedProgram_residue_le {n s e} (root : Wire) (p : Straight n s e) :
    residue (seedProgram root p)≤residue p := by
  induction p with
  | done => exact le_rfl
  | gate g p ih =>
    cases g with
    | literal g =>
      simp only [seedProgram,seedTemplate,residue,seed_phaseCost]
      exact Nat.add_le_add_left ih _
    | whenBit i v g => exact Nat.add_le_add (seed_tCost_le root g) ih
  | recordGate i v g p ih => exact Nat.add_le_add (seed_tCost_le root g) ih
  | measure w p ih => exact ih

theorem seedProgram_credit {n s e} (root : Wire) (p : Straight n s e) (credit : Nat)
    (h : ProgramCredit p credit) : ProgramCredit (seedProgram root p) (credit-literalHits root p) := by
  constructor
  · have hh := seedProgram_residue_le root p
    rw [h.1] at hh
    exact Nat.eq_zero_of_le_zero hh
  · have hh := seedProgram_added root p
    rw [h.2] at hh
    omega

theorem safe_of_not_mem (root : Wire) (g : Gate) (h : root∉gateWires g) : safe root g := by
  cases g <;> simp_all [gateWires,safe] <;> aesop

theorem hit_zero_of_not_mem (root : Wire) (g : Gate) (h : root∉gateWires g) : hit root g=0 := by
  cases g <;> simp_all [gateWires,hit] <;> aesop

theorem safeTemplate_of_not_mem {n} (root : Wire) (g : TemplateGate n)
    (h : root∉templateGateWires g) : safeTemplate root g := by
  cases g <;> exact safe_of_not_mem root _ h

theorem safeProgram_of_not_mem {n s e} (root : Wire) (p : Straight n s e)
    (h : root∉straightWires p) : safeProgram root p := by
  induction p with
  | done => trivial
  | gate g p ih =>
    exact ⟨safeTemplate_of_not_mem root g (fun hw => h (List.mem_append_left _ hw)),
      ih (fun hw => h (List.mem_append_right _ hw))⟩
  | recordGate i v g p ih =>
    exact ⟨safe_of_not_mem root g (fun hw => h (List.mem_append_left _ hw)),
      ih (fun hw => h (List.mem_append_right _ hw))⟩
  | measure w p ih =>
    exact ⟨fun he => h (by simp [straightWires,he]),ih (fun hw => h (by simp [straightWires,hw]))⟩

theorem literalHits_zero_of_not_mem {n s e} (root : Wire) (p : Straight n s e)
    (h : root∉straightWires p) : literalHits root p=0 := by
  induction p with
  | done => rfl
  | gate g p ih =>
    have ht := ih (fun hw => h (List.mem_append_right _ hw))
    cases g with
    | literal g =>
      have hg := hit_zero_of_not_mem root g (fun hw => h (List.mem_append_left _ hw))
      simpa only [literalHits,hg,zero_add] using ht
    | whenBit i v g => exact ht
  | recordGate i v g p ih => exact ih (fun hw => h (List.mem_append_right _ hw))
  | measure w p ih => exact ih (fun hw => h (by simp [straightWires,hw]))


theorem literalProgram_noRoot {n start} (root : Wire) (gs : Circuit) (S : List Wire)
    (hg : circuitWires gs⊆S) (hn : root∉S) : root∉straightWires (literalProgram (n:=n) (s:=start) gs) := by
  rw [literalProgram_support]
  exact fun h => hn (hg h)

theorem measureThen_safe {n R} (root : Wire)
    (next : (cursor : Nat) → List (Fin cursor) → Straight n cursor (cursor+R))
    (hn : ∀ cursor refs,safeProgram root (next cursor refs))
    (wires : List Wire) (start : Nat) (refs : List (Fin start))
    (hw : ∀ w∈wires,w≠root) : safeProgram root (measureThen next wires start refs) := by
  induction wires generalizing start with
  | nil => exact hn start refs
  | cons w ws ih =>
    rw [measureThen,safeProgram_cast]
    exact ⟨hw w (by simp),ih (start+1) _ (fun x hx => hw x (by simp [hx]))⟩

theorem literalHits_measureThen {n R} (root : Wire) (count : Nat)
    (next : (cursor : Nat) → List (Fin cursor) → Straight n cursor (cursor+R))
    (hn : ∀ cursor refs,literalHits root (next cursor refs)=count)
    (wires : List Wire) (start : Nat) (refs : List (Fin start)) :
    literalHits root (measureThen next wires start refs)=count := by
  induction wires generalizing start with
  | nil => exact hn start refs
  | cons w ws ih =>
    rw [measureThen,literalHits_cast]
    exact ih (start+1) _

theorem straightWires_eq_naive {n s e} (p : Straight n s e) :
    straightWires p=NaiveChallenge.straightWires p := by
  induction p with
  | done => rfl
  | gate g p ih => cases g <;> simp_all [straightWires,NaiveChallenge.straightWires,templateGateWires,NaiveChallenge.slotGate]
  | recordGate i v g p ih => simp_all [straightWires,NaiveChallenge.straightWires]
  | measure w p ih => simp_all [straightWires,NaiveChallenge.straightWires]

theorem fixup9_noRoot_parts {n} (known : Wire) (low : Fin 9 → Wire) (hot : Fin 512 → Wire)
    (hl : ∀ i,low i≠known) (hh : ∀ i,hot i≠known) :
    let S := List.ofFn low++hotBank9 hot
    known∉S ∧ (circuitWires (hotPrepare9 low hot)⊆S) ∧
      (∀ start,straightWires (eraseNetwork n (hotNetwork9 low hot) start)⊆S) := by
  dsimp
  have hn : known∉List.ofFn low++hotBank9 hot := by
    simp only [List.mem_append,hotBank9,List.mem_ofFn,not_or,not_exists]
    exact ⟨fun i he => hl i he,fun i he => hh i he⟩
  have hb := hotNetwork_within9 low hot (List.ofFn low++hotBank9 hot)
    (fun i => List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
    (fun i => List.mem_append_right _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
  refine ⟨hn,hotPrepare_within9 low hot _ ?_ ?_,fun start => by rw [straightWires_eq_naive]; exact eraseNetwork_within n _ start _ hb⟩
  · intro i; exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
  · intro i; exact List.mem_append_right _ (List.mem_ofFn.mpr ⟨i,rfl⟩)

theorem fixupProgram9_safe {n base} (known : Wire) (data : List (ClearPort n)) (refs : List (Fin base))
    (low : Fin 9 → Wire) (hot : Fin 512 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire)
    (hl : ∀ i,low i≠known) (hh : ∀ i,hot i≠known) (hs : scratch≠known)
    (hb : ∀ w∈tree.indexWires,w≠known) (hp : ∀ w∈paths,w≠known) :
    safeProgram known (fixupProgram9 data refs low hot tree root scratch paths) := by
  obtain ⟨hn,hprep,herase⟩ := fixup9_noRoot_parts (n:=n) known low hot hl hh
  have hbank : known∉hotBank9 hot := fun h => hn (List.mem_append_right _ h)
  have hhad : ∀ start,safeProgram known (literalProgram (n:=n) (s:=start) ((hotBank9 hot).map Gate.H)) := by
    intro start
    apply safeProgram_of_not_mem
    rw [literalProgram_support,hadamards_wires]
    exact hbank
  have hadj : ∀ start,safeProgram known (literalProgram (n:=n) (s:=start) (Circuit.adjoint ((hotBank9 hot).map Gate.H))) := by
    intro start
    apply safeProgram_of_not_mem
    rw [literalProgram_support,hadamards_adjoint_wires]
    exact fun h => hbank (List.mem_reverse.mp h)
  simp only [fixupProgram9,safeProgram_append,safeProgram_cast]
  refine ⟨safeProgram_of_not_mem known _ (literalProgram_noRoot known _ _ hprep hn),
    hhad _,recordLookupProgram_safe known _ scratch _ base (Nat.le_refl base) hs ?_
      (recordUnaryOps_safe known tree root paths hb hp),hadj _,safeProgram_of_not_mem known _ ?_,?_⟩
  · intro p h
    have ht := phasePorts_targets9 hot (data.zip refs) p h
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp ht
    exact hi ▸ hh i
  · exact fun h => hn (herase _ h)
  · apply safeProgram_of_not_mem
    rw [literalProgram_support]
    simpa [circuitWires,gateWires,eq_comm] using hh 0


theorem literalHits_hadamards {n start} (root : Wire) (ws : List Wire) :
    literalHits root (literalProgram (n:=n) (s:=start) (ws.map Gate.H))=0 := by
  simp [literalProgram,literalHits_gateProgram,List.map_map,Function.comp_def,templateHits,hit]

theorem literalHits_adjoint_hadamards {n start} (root : Wire) (ws : List Wire) :
    literalHits root (literalProgram (n:=n) (s:=start) (Circuit.adjoint (ws.map Gate.H)))=0 := by
  simp [literalProgram,literalHits_gateProgram,Circuit.adjoint,List.map_map,Function.comp_def,templateHits,hit,Gate.adjoint]

theorem literalHits_eraseNetwork (root : Wire) (n : Nat) (cs : List SplitCell) (start : Nat) :
    literalHits root (eraseNetwork n cs start)=0 := by
  induction cs generalizing start with
  | nil => rfl
  | cons c cs ih =>
    rw [eraseNetwork,literalHits_cast,literalHits_append,ih]
    simp [eraseSplit,andEraseProgram,literalHits,literalHits_recordGates,hit]

theorem literalHits_X {n start} (root w : Wire) :
    literalHits root (literalProgram (n:=n) (s:=start) [.X w])=0 := rfl

theorem fixupProgram9_hits {n base} (known : Wire) (data : List (ClearPort n)) (refs : List (Fin base))
    (low : Fin 9 → Wire) (hot : Fin 512 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire)
    (hl : ∀ i,low i≠known) (hh : ∀ i,hot i≠known) :
    literalHits known (fixupProgram9 data refs low hot tree root scratch paths)=
      recordOpsHits known (recordUnaryOps tree root paths) := by
  obtain ⟨hn,hprep,_⟩ := fixup9_noRoot_parts (n:=n) known low hot hl hh
  have hz (start : Nat) : literalHits known (literalProgram (n:=n) (s:=start) (hotPrepare9 low hot))=0 :=
    literalHits_zero_of_not_mem known _ (literalProgram_noRoot known _ _ hprep hn)
  simp only [fixupProgram9,literalHits_append,literalHits_cast,literalHits_recordLookupProgram,
    literalHits_hadamards,literalHits_adjoint_hadamards,literalHits_eraseNetwork,literalHits_X,hz,
    zero_add,add_zero]

theorem measuredClear9_safe {n} (known : Wire) (data : List (ClearPort n))
    (low : Fin 9 → Wire) (hot : Fin 512 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire) (start : Nat)
    (hl : ∀ i,low i≠known) (hh : ∀ i,hot i≠known) (hs : scratch≠known)
    (hb : ∀ w∈tree.indexWires,w≠known) (hp : ∀ w∈paths,w≠known)
    (hd : ∀ p∈data,p.target≠known) :
    safeProgram known (measuredClear9 data low hot tree root scratch paths start) := by
  rw [measuredClear9,safeProgram_cast]
  apply measureThen_safe
  · intro cursor refs
    rw [safeProgram_cast]
    exact fixupProgram9_safe known data refs low hot tree root scratch paths hl hh hs hb hp
  · intro w hw
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hw
    exact hd p hp

theorem measuredClear9_hits {n} (known : Wire) (data : List (ClearPort n))
    (low : Fin 9 → Wire) (hot : Fin 512 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire) (start : Nat)
    (hl : ∀ i,low i≠known) (hh : ∀ i,hot i≠known) :
    literalHits known (measuredClear9 data low hot tree root scratch paths start)=
      recordOpsHits known (recordUnaryOps tree root paths) := by
  rw [measuredClear9,literalHits_cast]
  apply literalHits_measureThen
  intro cursor refs
  rw [literalHits_cast]
  exact fixupProgram9_hits known data refs low hot tree root scratch paths hl hh


attribute [local irreducible] KnownRoot.first18_seededOps
  KnownRoot.first18_seededSel KnownRoot.first18_seededProgram

theorem layout_avoids {tree : UnaryActionTree} {root : Wire} {paths : List Wire}
    (h : tree.Layout root paths) :
    (∀ w∈tree.indexWires,w≠root) ∧ (∀ w∈paths,w≠root) := by
  have hn := (List.nodup_cons.mp (unaryLayout_decoderNodup h)).1
  constructor
  · intro w hw he
    subst w
    exact hn (List.mem_append_left _ (List.mem_dedup.mpr hw))
  · intro w hw he
    subst w
    exact hn (List.mem_append_right _ hw)

theorem unaryOps_root_hits {n} (root : Wire) (leaf : Nat → Wire → List (TemplateGate n))
    (tree : UnaryActionTree) (paths : List Wire) (h : tree.Layout root paths)
    (hn : 0<tree.internalNodes)
    (hl : ∀ label c,(leaf label c |>.map (templateHits root)).sum=0) :
    opsHits root (unaryLookupOps leaf tree root paths)=1 := by
  obtain ⟨hb,hp⟩ := layout_avoids h
  cases h with
  | leaf label root paths _ => simp [UnaryActionTree.internalNodes] at hn
  | node bit root path zero one rest _ _ _ => exact unaryOps_hits_one root bit path leaf zero one rest hl hb hp

theorem recordUnaryOps_root_hits (root : Wire) (tree : UnaryActionTree) (paths : List Wire)
    (h : tree.Layout root paths) (hn : 0<tree.internalNodes) :
    recordOpsHits root (recordUnaryOps tree root paths)=1 := by
  obtain ⟨hb,hp⟩ := layout_avoids h
  cases h with
  | leaf label root paths _ => simp [UnaryActionTree.internalNodes] at hn
  | node bit root path zero one rest _ _ _ => exact recordUnaryOps_hits_one root bit path zero one rest hb hp

theorem first18_leaf_safe (label : Nat) (control : Wire) (g : TemplateGate 262144)
    (hg : g∈First18.selLeaf label control) : safeTemplate 836 g := by
  simp only [First18.selLeaf,lookupLeafGates,List.mem_map] at hg
  obtain ⟨⟨ref,target⟩,hm,rfl⟩ := hg
  change target≠836
  have ht : target∈pointLogicalWires ∨ target∈First18.garb := by
    rcases List.mem_append.mp hm with h | h
    · exact Or.inl (List.of_mem_zip h).2
    · exact Or.inr (List.of_mem_zip h).2
  intro he
  subst target
  rcases ht with hp | hg
  · have h := First18.mem_point hp
    omega
  · have h := First18.mem_garb hg
    omega

theorem first18_leaf_hits (label : Nat) (control : Wire) :
    ((First18.selLeaf label control).map (templateHits 836)).sum=0 := by
  simp [First18.selLeaf,lookupLeafGates,List.map_map,Function.comp_def,templateHits]

theorem first18_selOps_safe : ∀ op∈First18.selOps,safeOp 836 op := by
  rw [First18.selOps]
  obtain ⟨hb,hp⟩ := layout_avoids First18.sel_layout
  exact unaryOps_safe 836 First18.selLeaf _ _ _ first18_leaf_safe hb hp

theorem first18_selOps_hits : opsHits 836 First18.selOps=1 := by
  rw [First18.selOps]
  exact unaryOps_root_hits 836 First18.selLeaf _ _ First18.sel_layout
    (by rw [First18.sel_nodes]; decide) first18_leaf_hits

theorem first18_seededOps_safe : ∀ op∈KnownRoot.first18_seededOps,safeOp 836 op := by
  intro op hop
  rw [KnownRoot.first18_seededOps] at hop
  rcases List.mem_cons.mp hop with rfl | ht
  · apply ordinaryOp_safe
    simp [safeCircuit,KnownRoot.seededZeroAnd,safe]
  · exact first18_selOps_safe op (List.mem_of_mem_tail ht)

theorem prefix_hits_drop {n} (root bit path : Wire) (ops : List (LookupOp n))
    (h : opsHits root (ordinaryOp (computeZeroAnd root bit path)::ops)=1) :
    opsHits root (ordinaryOp (KnownRoot.seededZeroAnd root bit path)::ops)=0 := by
  simp [opsHits,opHits,ordinaryOp,computeZeroAnd,KnownRoot.seededZeroAnd,templateHits,hit] at h ⊢
  omega

theorem first18_seededOps_hits : opsHits 836 KnownRoot.first18_seededOps=0 := by
  have h := congrArg (opsHits 836) KnownRoot.first18_head
  rw [first18_selOps_hits] at h
  rw [KnownRoot.first18_seededOps]
  exact prefix_hits_drop 836 856 519 First18.selOps.tail h.symm

theorem first18_seededSel_safe (start : Nat) : safeProgram 836 (KnownRoot.first18_seededSel start) := by
  rw [KnownRoot.first18_seededSel,safeProgram_cast]
  exact lookupProgram_safe 836 _ start first18_seededOps_safe

theorem first18_seededSel_hits (start : Nat) : literalHits 836 (KnownRoot.first18_seededSel start)=0 := by
  rw [KnownRoot.first18_seededSel,literalHits_cast,literalHits_lookupProgram,first18_seededOps_hits]

theorem first18_swap_noRoot (start : Nat) : 836∉straightWires (First18.swapProgram start) := by
  rw [First18.swapProgram,literalProgram_support]
  intro h
  rcases First18.swap_wires 836 h with h | h | h
  · dsimp only [Wire] at *; omega
  · have h := First18.mem_point h
    dsimp only [Wire] at *; omega
  · have h := First18.mem_garb h
    dsimp only [Wire] at *; omega

theorem first18_low_ne (i : Fin 9) : First18.low i≠836 := by
  simp only [First18.low]
  dsimp only [Wire] at *
  omega

theorem first18_hot_ne (i : Fin 512) : First18.hot i≠836 := by
  simp only [First18.hot]
  dsimp only [Wire] at *
  omega

theorem first18_clear_safe (start : Nat) : safeProgram 836 (First18.clearProgram start) := by
  obtain ⟨hb,hp⟩ := layout_avoids First18.clear_layout
  rw [First18.clearProgram,safeProgram_cast]
  apply measuredClear9_safe 836 _ _ _ _ _ _ _ _ first18_low_ne first18_hot_ne (by decide) hb hp
  intro p hp he
  apply First18.tree_not_targets 836 (by simp)
  exact List.mem_map.mpr ⟨p,hp,he⟩

theorem first18_clear_hits (start : Nat) : literalHits 836 (First18.clearProgram start)=1 := by
  rw [First18.clearProgram,literalHits_cast,measuredClear9_hits 836 _ _ _ _ _ _ _ _ first18_low_ne first18_hot_ne]
  exact recordUnaryOps_root_hits 836 _ _ First18.clear_layout (by rw [First18.clear_nodes]; decide)

theorem first18_program_safe (start : Nat) : safeProgram 836 (KnownRoot.first18_seededProgram start) := by
  simp only [KnownRoot.first18_seededProgram,safeProgram_cast,safeProgram_append]
  exact ⟨⟨first18_seededSel_safe start,safeProgram_of_not_mem 836 _ (first18_swap_noRoot _)⟩,first18_clear_safe _⟩

theorem first18_program_hits (start : Nat) : literalHits 836 (KnownRoot.first18_seededProgram start)=1 := by
  simp only [KnownRoot.first18_seededProgram,literalHits_cast,literalHits_append,first18_seededSel_hits,
    first18_clear_hits,literalHits_zero_of_not_mem 836 _ (first18_swap_noRoot _),zero_add]


open ConditionalCatalyst Secp256k1
set_option maxHeartbeats 2000000

def first18_rootProgram (start : Nat) : Straight 262144 start (start+132606) :=
  seedProgram 836 (KnownRoot.first18_seededProgram start)

theorem first18_rootProgram_coherent (coeffs : Fin 262144 → PointCoeff) (Q : Point)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((first18_rootProgram start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (fun s => pointWrite (SelectSchedule18.tablePoint coeffs Q
        (tableAddressValue SelectSchedule18.bits s)) s)) SelectSchedule18.Input := by
  apply seedProgram_coherent 836 _ _ _ _ _ (first18_program_safe start) (fun _ hs => hs.1)
  exact KnownRoot.first18_seededProgram_coherent coeffs Q start history

theorem first18_rootProgram_residue (start : Nat) : residue (first18_rootProgram start)=0 := by
  have h := seedProgram_residue_le 836 (KnownRoot.first18_seededProgram start)
  rw [KnownRoot.first18_seededProgram_residue] at h
  exact Nat.eq_zero_of_le_zero h

theorem first18_rootProgram_added (start : Nat) : added (first18_rootProgram start)=132595 := by
  have h := seedProgram_added 836 (KnownRoot.first18_seededProgram start)
  rw [KnownRoot.first18_seededProgram_added,first18_program_hits] at h
  change added (seedProgram 836 (KnownRoot.first18_seededProgram start))=132595
  omega

theorem first18_rootProgram_slots (start : Nat) : (first18_rootProgram start).gateSlots≤1000000000 := by
  rw [first18_rootProgram,seedProgram_slots]
  exact KnownRoot.first18_seededProgram_slots start

theorem first18_rootProgram_support (start : Nat) :
    straightWires (first18_rootProgram start)⊆First18.support :=
  (seedProgram_wires 836 _).trans (KnownRoot.first18_seededProgram_support start)

theorem first18_rootProgram_wellFormed (start : Nat) : (first18_rootProgram start).WellFormed :=
  seedProgram_wellFormed 836 _ (KnownRoot.first18_seededProgram_wellFormed start)

def windowGeneric {n : Nat} (rows : Fin 262144 → Fin n) : Single.Window n :=
  ⟨SelectSchedule18.bits.reverse,132606,fun start => reindexStraight rows (first18_rootProgram start)⟩

theorem program_tCount (coeffs : Fin 262144 → PointCoeff) (Q : Secp256k1.Point) (start : Nat) (history : Fin start → Bool) :
    ((first18_rootProgram start).instantiate (readConstant coeffs Q) history).tCount = 928165 := by
  rw [exact_t _ (first18_rootProgram_residue start),first18_rootProgram_added]

theorem window_law_generic {n : Nat} (coeffs : Fin n → PointCoeff) (rows : Fin 262144 → Fin n)
    (init : Point → Nat → Point)
    (hcoeff : ∀ Q, order • Q = 0 → ∀ a : Fin 262144,
      constantPoint Q (coeffs (rows a)) = init Q a.val) :
    Single.WindowLaw coeffs (windowGeneric rows) (SelectSchedule18.update init)
      SelectSchedule18.Input := by
  intro Q hQ hn start history
  have hvalid := first18_rootProgram_coherent (fun a => coeffs (rows a)) Q start history
  have hupdate : (fun s => pointWrite
      (SelectSchedule18.tablePoint (fun a => coeffs (rows a)) Q
        (tableAddressValue SelectSchedule18.bits s)) s) = SelectSchedule18.update init Q := by
    funext s
    unfold SelectSchedule18.tablePoint SelectSchedule18.update
    have hbound : tableAddressValue SelectSchedule18.bits s < 262144 := by
      have hb := tableAddressValue_lt SelectSchedule18.bits s
      have hlen : SelectSchedule18.bits.length = 18 := by decide +kernel
      simpa only [hlen] using hb
    simp only [Nat.mod_eq_of_lt hbound]
    rw [hcoeff Q hQ]
  rw [hupdate] at hvalid
  unfold windowGeneric
  rw [reindexStraight_instantiate,
    readConstant_reindex rows (fun a => coeffs (rows a)) coeffs Q (fun _ => rfl)]
  exact hvalid

theorem window_wellFormed {n : Nat} (rows : Fin 262144 → Fin n) (start : Nat) :
    ((windowGeneric rows).program start).WellFormed := by
  unfold windowGeneric
  exact (reindexStraight_wellFormed rows (first18_rootProgram start)).mpr (first18_rootProgram_wellFormed start)

theorem window_slots {n : Nat} (rows : Fin 262144 → Fin n) (start : Nat) :
    ((windowGeneric rows).program start).gateSlots ≤ 1000000000 := by
  unfold windowGeneric
  rw [reindexStraight_gateSlots]
  exact first18_rootProgram_slots start

theorem window_support {n : Nat} (rows : Fin 262144 → Fin n) (start : Nat) :
    straightWires ((windowGeneric rows).program start) ⊆ First18.support := by
  unfold windowGeneric
  rw [straightWires_reindex]
  exact first18_rootProgram_support start

theorem window_t {n : Nat} (coeffs : Fin n → PointCoeff) (rows : Fin 262144 → Fin n)
    (Q : Point) (start : Nat) (history : Fin start → Bool) :
    (((windowGeneric rows).program start).instantiate (readConstant coeffs Q) history).tCount = 928165 := by
  unfold windowGeneric
  rw [reindexStraight_instantiate,
    readConstant_reindex rows (fun a => coeffs (rows a)) coeffs Q (fun _ => rfl)]
  exact program_tCount (fun a => coeffs (rows a)) Q start history

theorem window_credit {n : Nat} (_coeffs : Fin n → PointCoeff) (rows : Fin 262144 → Fin n)
    (_Q : Point) (start : Nat) (_history : Fin start → Bool) :
    added ((windowGeneric rows).program start) = 132595 := by
  unfold windowGeneric
  rw [added_reindex]
  exact first18_rootProgram_added start


#print axioms first18_rootProgram_coherent
#print axioms first18_rootProgram_added
#print axioms window_law_generic
end
end ShorECDLP.Entrant.RootPass
end

/-! ### Consolidated from `First20Signed.lean` -/
section
/-! Signed five-pass global-optimal SelectSwap loader for the 20-bit left-axis first window.

Exploits `(-P) = (x, -y)` to halve the table from `2^20 = 1,048,576` to `2^19 = 524,288` rows
using bit 19 (`874`) as sign control and bits `0..18` (`855..873`) as a 19-bit table address:
- Pre-XOR (`20` Cliffords, `0` Toffolis): flips `874` and XORs `855..873` with it, mapping
  `v ∈ [0, 2^19)` to `(524287 - v, neg=true)` and `v ∈ [2^19, 2^20)` to `(v - 524288, neg=false)`.
- Every table point is non-zero (`infinity` wire `838` stays `false`, freeing `838` into the
  clean ancilla pool during the 5 QROM passes and cutting the payload from 513 to 512 bits).
- Five-pass SelectSwap over `512` coordinate bits (`x` + `y`) inside `List.range 1613`:
  - Pass 1 (`k=9`,   3 bits): 10-bit QROM (`  1,023`) + `511 ×   3 = 1,533` swaps
  - Pass 2 (`k=2`, 393 bits): 17-bit QROM (`131,071`) + `  3 × 393 = 1,179` swaps
  - Pass 3 (`k=7`,   9 bits): 12-bit QROM (`  4,095`) + `127 ×   9 = 1,143` swaps
  - Pass 4 (`k=4`,  73 bits): 15-bit QROM (` 32,767`) + ` 15 ×  73 = 1,095` swaps
  - Pass 5 (`k=5`,  34 bits): 14-bit QROM (` 16,383`) + ` 31 ×  34 = 1,054` swaps
  - One fused 9-bit measured-clear phase fixup (`1,023 + 502 = 1,525` Toffolis) over all
    `6,004` garbage measurement records, followed by `RootPass.seedProgram 836` (`-6` root hits).
- Conditional modular negation of `point.y` (`580..835`) controlled on `874` via
  `CompactRecoveryNegateLayout.reflection` (`255` Toffolis, `255` measurements).
- Post-XOR (`20` Cliffords, `0` Toffolis): restores `855..874`.

Total: `193,117` Toffolis (down from `380,701`, saving `187,584` Toffolis = `750,336` T-model gates)
and `193,132` measurement records, within `List.range 1613`. -/


namespace ShorECDLP.Entrant.MeasuredClear
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

theorem fixupFactor9_append {n : Nat} (d1 d2 : List (ClearPort n)) (o1 o2 : List Bool)
    (h : o1.length = d1.length) (read : ConstantBit n → Bool) (low : Fin 9 → Wire) (hot : Fin 512 → Wire)
    (tree : UnaryActionTree) (root : Wire) (s : BasisState) :
    fixupFactor9 (d1 ++ d2) (o1 ++ o2) read low hot tree root s =
      fixupFactor9 d1 o1 read low hot tree root s * fixupFactor9 d2 o2 read low hot tree root s := by
  have hz : (d1 ++ d2).zip ((o1 ++ o2).map boolRecord) =
      d1.zip (o1.map boolRecord) ++ d2.zip (o2.map boolRecord) := by
    rw [List.map_append]
    exact List.zip_append (by simp [h])
  simp only [fixupFactor9, phaseLookupFactor, logicalPorts9, hz, phasePorts9, List.flatMap_append,
    recordTargets_append, xorPhase_append]

theorem fixupFactor9_loaded {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (read : ConstantBit n → Bool) (low : Fin 9 → Wire) (hot : Fin 512 → Wire)
    (tree : UnaryActionTree) (root : Wire) (paths : List Wire)
    (hi : Function.Injective hot) (hdlow : ∀ i j, low i ≠ hot j)
    (hbank : (hotBank9 hot).Disjoint (root :: tree.indexWires.dedup ++ paths))
    (t u : BasisState) (hhot : HotClean9 hot t)
    (hw : ∀ p ∈ data, u p.target =
      (t root && decide (read (p.ref (512 * tree.routeLabel t + hotAddress9 low t)) = p.value))) :
    fixupFactor9 data outcomes read low hot tree root t =
      registerXPhase (data.map ClearPort.target) outcomes u := by
  let prepared := Classical.run (hotPrepare9 low hot) t
  have hframe (w : Wire) (hw : w ∈ root :: tree.indexWires.dedup ++ paths) : prepared w = t w :=
    hotPrepare_frame9 low hot t w (by
      intro i he
      exact List.disjoint_left.mp hbank (List.mem_ofFn.mpr ⟨i, he.symm⟩) hw)
  have hroute : tree.routeLabel prepared = tree.routeLabel t := by
    apply tree.routeLabel_congr prepared t
    intro w hw
    exact hframe w (by simp [hw])
  let selected : Fin 512 := ⟨hotAddress9 low t, hotAddress_bound9 low t⟩
  apply phaseFactor_loaded9 data outcomes read hot tree root u prepared selected
  · intro i
    simpa only [Fin.ext_iff] using hotPrepare_marker9 low hot hi hdlow t hhot i
  · intro p hp
    rw [hframe root (by simp), hroute]
    exact hw p hp

end
end ShorECDLP.Entrant.MeasuredClear

namespace ShorECDLP.Entrant.First20Signed
open Quantum Challenge Secp256k1 Paper2607_13816 Paper2607_13816.ChallengeMigration AndGadget WEXCredit
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.constructorNameAsVariable false

/-! ### Part 1: Generic `k`-bit binary SelectSwap tree -/

def chunks {α : Type} : Nat → Nat → List α → List (List α)
  | 0, _, _ => []
  | c + 1, m, xs => xs.take m :: chunks c m (xs.drop m)

theorem chunks_length {α : Type} : ∀ (c m : Nat) (xs : List α), (chunks c m xs).length = c
  | 0, _, _ => rfl
  | c + 1, m, xs => by simp [chunks, chunks_length c m]

theorem chunks_mem_length {α : Type} : ∀ (c m : Nat) (xs : List α),
    xs.length = c * m → ∀ r ∈ chunks c m xs, r.length = m
  | 0, _, _, _, _, hr => by simp [chunks] at hr
  | c + 1, m, xs, hl, r, hr => by
    simp only [chunks, List.mem_cons] at hr
    rcases hr with rfl | hr
    · rw [List.length_take, hl, Nat.add_mul, Nat.one_mul]; omega
    · exact chunks_mem_length c m (xs.drop m) (by rw [List.length_drop, hl, Nat.add_mul, Nat.one_mul]; omega) r hr

theorem chunks_flatten {α : Type} : ∀ (c m : Nat) (xs : List α),
    xs.length = c * m → (chunks c m xs).flatten = xs
  | 0, _, xs, hl => by
    simp only [chunks, List.flatten_nil]
    exact (List.eq_nil_of_length_eq_zero (by simpa using hl)).symm
  | c + 1, m, xs, hl => by
    rw [chunks, List.flatten_cons, chunks_flatten c m (xs.drop m)
      (by rw [List.length_drop, hl, Nat.add_mul, Nat.one_mul]; omega), List.take_append_drop]

def evens {α : Type} : List α → List α
  | a :: _ :: rest => a :: evens rest
  | xs => xs

def odds {α : Type} : List α → List α
  | _ :: b :: rest => b :: odds rest
  | _ => []

def pairSwaps (c : Wire) : List (List Wire) → Circuit
  | a :: b :: rest => First18.swapWords c a b ++ pairSwaps c rest
  | _ => []

def swapTree : List Wire → List (List Wire) → Circuit
  | [], _ => []
  | c :: cs, regs => pairSwaps c regs ++ swapTree cs (evens regs)

def treeGarbs : List Wire → List (List Wire) → List (List Wire)
  | [], _ => []
  | _ :: cs, regs => odds regs ++ treeGarbs cs (evens regs)

def oddAddrs (k : Nat) : List (Nat → Nat) :=
  List.ofFn fun j : Fin (2 ^ k) => fun x => 2 * (2 ^ k * (x / 2 ^ (k + 1)) + j.val) + (1 - x % 2)

def treeAddrs : Nat → List (Nat → Nat)
  | 0 => []
  | k + 1 => oddAddrs k ++ (treeAddrs k).map (fun g => fun x => 2 * g (x / 2) + x % 2)

theorem evens_length {α : Type} : ∀ (n : Nat) (xs : List α),
    xs.length = 2 * n → (evens xs).length = n
  | 0, [], _ => rfl
  | 0, _ :: _, h => by simp at h
  | n + 1, _ :: _ :: rest, h => by
    simp only [evens, List.length_cons]
    have h' : rest.length = 2 * n := by simp at h; omega
    rw [evens_length n rest h']
  | n + 1, [], h => by simp at h
  | n + 1, [_], h => by simp at h; omega

theorem odds_length {α : Type} : ∀ (n : Nat) (xs : List α),
    xs.length = 2 * n → (odds xs).length = n
  | 0, [], _ => rfl
  | 0, _ :: _, h => by simp at h
  | n + 1, _ :: _ :: rest, h => by
    simp only [odds, List.length_cons]
    have h' : rest.length = 2 * n := by simp at h; omega
    rw [odds_length n rest h']
  | n + 1, [], h => by simp at h
  | n + 1, [_], h => by simp at h; omega

theorem mem_evens_sub {α : Type} : ∀ (xs : List α) {x : α}, x ∈ evens xs → x ∈ xs
  | [], _, h => h
  | [a], _, h => h
  | a :: b :: rest, x, h => by
    simp only [evens, List.mem_cons] at h ⊢
    rcases h with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (mem_evens_sub rest h))

theorem mem_odds_sub {α : Type} : ∀ (xs : List α) {x : α}, x ∈ odds xs → x ∈ xs
  | [], _, h => by simp [odds] at h
  | [_], _, h => by simp [odds] at h
  | a :: b :: rest, x, h => by
    simp only [odds, List.mem_cons] at h ⊢
    rcases h with rfl | h
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (mem_odds_sub rest h))

theorem mem_evens_or_odds {α : Type} : ∀ (xs : List α) {x : α},
    x ∈ xs ↔ x ∈ evens xs ∨ x ∈ odds xs
  | [], x => by simp [evens, odds]
  | [a], x => by simp [evens, odds]
  | a :: b :: rest, x => by
    simp only [evens, odds, List.mem_cons, mem_evens_or_odds rest]
    tauto

theorem evens_head {α : Type} : ∀ (a : α) (rest : List α),
    ∃ t, evens (a :: rest) = a :: t
  | a, [] => ⟨[], rfl⟩
  | a, _ :: rest => ⟨evens rest, rfl⟩

theorem nodup_evens_odds {α : Type} : ∀ (xs : List (List α)),
    xs.flatten.Nodup → (evens xs).flatten.Nodup ∧ (odds xs).flatten.Nodup ∧
      (evens xs).flatten.Disjoint (odds xs).flatten
  | [], _ => ⟨List.nodup_nil, List.nodup_nil, List.disjoint_nil_left _⟩
  | [a], h => ⟨by simpa [evens] using h, List.nodup_nil, List.disjoint_nil_right _⟩
  | a :: b :: rest, h => by
    simp only [List.flatten_cons, List.nodup_append] at h
    obtain ⟨ha, ⟨hb, hrest, hbr⟩, habr⟩ := h
    obtain ⟨he, ho, heo⟩ := nodup_evens_odds rest hrest
    have ha_sub : ∀ x ∈ a, ∀ y ∈ rest.flatten, x ≠ y :=
      fun x hx y hy => habr x hx y (List.mem_append_right _ hy)
    have ha_b : ∀ x ∈ a, ∀ y ∈ b, x ≠ y :=
      fun x hx y hy => habr x hx y (List.mem_append_left _ hy)
    have he_sub : ∀ y ∈ (evens rest).flatten, y ∈ rest.flatten := fun y hy => by
      obtain ⟨r, hr, hyr⟩ := List.mem_flatten.mp hy
      exact List.mem_flatten.mpr ⟨r, mem_evens_sub rest hr, hyr⟩
    have ho_sub : ∀ y ∈ (odds rest).flatten, y ∈ rest.flatten := fun y hy => by
      obtain ⟨r, hr, hyr⟩ := List.mem_flatten.mp hy
      exact List.mem_flatten.mpr ⟨r, mem_odds_sub rest hr, hyr⟩
    refine ⟨?_, ?_, ?_⟩
    · simp only [evens, List.flatten_cons, List.nodup_append]
      exact ⟨ha, he, fun x hx y hy => ha_sub x hx y (he_sub y hy)⟩
    · simp only [odds, List.flatten_cons, List.nodup_append]
      exact ⟨hb, ho, fun x hx y hy => hbr x hx y (ho_sub y hy)⟩
    · apply List.disjoint_left.mpr
      intro x hx hy
      simp only [evens, odds, List.flatten_cons, List.mem_append] at hx hy
      rcases hx with hxa | hxe <;> rcases hy with hyb | hyo
      · exact ha_b x hxa x hyb rfl
      · exact ha_sub x hxa x (ho_sub x hyo) rfl
      · exact hbr x hyb x (he_sub x hxe) rfl
      · exact List.disjoint_left.mp heo hxe hyo

theorem treeGarbs_nodup_and_mem : ∀ (ctrl : List Wire) (regs : List (List Wire)),
    regs.length = 2 ^ ctrl.length → regs.flatten.Nodup →
    (treeGarbs ctrl regs).flatten.Nodup ∧
    ∀ a rest, regs = a :: rest →
      (∀ w, w ∈ (treeGarbs ctrl regs).flatten ↔ w ∈ rest.flatten) ∧
      a.Disjoint (treeGarbs ctrl regs).flatten
  | [], regs, hl, hnd => by
    refine ⟨List.nodup_nil, fun a rest he => ?_⟩
    subst he
    have hnil : rest = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst hnil
    exact ⟨fun w => by simp [treeGarbs], List.disjoint_nil_right _⟩
  | c :: cs, regs, hl, hnd => by
    have h2 : regs.length = 2 * 2 ^ cs.length := by
      simpa only [List.length_cons, pow_succ, Nat.mul_comm] using hl
    obtain ⟨he_nd, ho_nd, heo⟩ := nodup_evens_odds regs hnd
    obtain ⟨ih_nd, ih_mem⟩ := treeGarbs_nodup_and_mem cs (evens regs) (evens_length _ _ h2) he_nd
    have hdisj_og : (odds regs).flatten.Disjoint (treeGarbs cs (evens regs)).flatten := by
      apply List.disjoint_left.mpr
      intro w hwo hwg
      obtain ⟨r, hr, hwr⟩ := List.mem_flatten.mp hwg
      have hne_ev : evens regs ≠ [] := by
        intro hnil; have := evens_length _ _ h2; rw [hnil] at this
        exact absurd this.symm (Nat.ne_of_gt (pow_pos (by decide) cs.length))
      cases hev : evens regs with
      | nil => exact hne_ev hev
      | cons a' t' =>
        rw [hev] at ih_mem hwg
        have hwt := (ih_mem a' t' rfl).1 w |>.mp hwg
        exact List.disjoint_left.mp heo (by rw [hev]; exact List.mem_flatten.mpr (by
          obtain ⟨q, hq, hwq⟩ := List.mem_flatten.mp hwt
          exact ⟨q, List.mem_cons_of_mem _ hq, hwq⟩)) hwo
    refine ⟨?_, fun a rest he => ?_⟩
    · simp only [treeGarbs, List.flatten_append, List.nodup_append]
      exact ⟨ho_nd, ih_nd, fun x hx y hy hxy => List.disjoint_left.mp hdisj_og hx (hxy ▸ hy)⟩
    · subst he
      cases rest with
      | nil =>
        have hp : 1 ≤ 2 ^ cs.length := Nat.one_le_pow _ _ (by decide)
        simp at h2; omega
      | cons b tail =>
        simp only [treeGarbs, evens, odds, List.flatten_append, List.flatten_cons]
        obtain ⟨ih_iff, ih_da⟩ := ih_mem a (evens tail) rfl
        have ih_iff' : ∀ w, w ∈ (treeGarbs cs (a :: evens tail)).flatten ↔ w ∈ (evens tail).flatten := by
          intro w; simpa only [evens] using ih_iff w
        have ha_b : a.Disjoint b := by
          simp only [List.flatten_cons, List.nodup_append] at hnd
          exact List.disjoint_left.mpr (fun x hx hy => hnd.2.2 x hx x (List.mem_append_left _ hy) rfl)
        have ha_ot : a.Disjoint (odds tail).flatten := by
          apply List.disjoint_left.mpr
          intro x hxa hxo
          simp only [List.flatten_cons, List.nodup_append] at hnd
          obtain ⟨r, hr, hxr⟩ := List.mem_flatten.mp hxo
          exact hnd.2.2 x hxa x (List.mem_append_right _ (List.mem_flatten.mpr ⟨r, mem_odds_sub tail hr, hxr⟩)) rfl
        refine ⟨fun w => ?_, ?_⟩
        · simp only [List.mem_append, ih_iff']
          constructor
          · rintro ((h | h) | h)
            · exact Or.inl h
            · obtain ⟨r, hr, hwr⟩ := List.mem_flatten.mp h
              exact Or.inr (List.mem_flatten.mpr ⟨r, mem_odds_sub tail hr, hwr⟩)
            · obtain ⟨r, hr, hwr⟩ := List.mem_flatten.mp h
              exact Or.inr (List.mem_flatten.mpr ⟨r, mem_evens_sub tail hr, hwr⟩)
          · rintro (h | h)
            · exact Or.inl (Or.inl h)
            · obtain ⟨r, hr, hwr⟩ := List.mem_flatten.mp h
              rcases (mem_evens_or_odds tail).mp hr with he | ho
              · exact Or.inr (List.mem_flatten.mpr ⟨r, he, hwr⟩)
              · exact Or.inl (Or.inr (List.mem_flatten.mpr ⟨r, ho, hwr⟩))
        · apply List.disjoint_left.mpr
          intro w hwa hwg
          simp only [List.mem_append] at hwg
          rcases hwg with (h | h) | h
          · exact List.disjoint_left.mp ha_b hwa h
          · exact List.disjoint_left.mp ha_ot hwa h
          · exact List.disjoint_left.mp ih_da hwa h

theorem treeGarbs_length : ∀ (ctrl : List Wire) (regs : List (List Wire)),
    regs.length = 2 ^ ctrl.length → (treeGarbs ctrl regs).length = 2 ^ ctrl.length - 1
  | [], regs, hl => by simp [treeGarbs]
  | c :: cs, regs, hl => by
    have h2 : regs.length = 2 * 2 ^ cs.length := by
      simpa only [List.length_cons, pow_succ, Nat.mul_comm] using hl
    simp only [treeGarbs, List.length_append, odds_length _ _ h2,
      treeGarbs_length cs (evens regs) (evens_length _ _ h2)]
    have hp : 1 ≤ 2 ^ cs.length := Nat.one_le_pow _ _ (by decide)
    simp only [List.length_cons, pow_succ]
    omega

theorem treeGarbs_mem_length : ∀ (ctrl : List Wire) (regs : List (List Wire)) (m : Nat),
    (∀ r ∈ regs, r.length = m) → ∀ r ∈ treeGarbs ctrl regs, r.length = m
  | [], _, _, _, _, hr => by simp [treeGarbs] at hr
  | c :: cs, regs, m, hm, r, hr => by
    simp only [treeGarbs, List.mem_append] at hr
    rcases hr with ho | ht
    · exact hm r (mem_odds_sub regs ho)
    · exact treeGarbs_mem_length cs (evens regs) m (fun x hx => hm x (mem_evens_sub regs hx)) r ht

theorem treeGarbs_flatten_length (ctrl : List Wire) (regs : List (List Wire)) (m : Nat)
    (hl : regs.length = 2 ^ ctrl.length) (hm : ∀ r ∈ regs, r.length = m) :
    (treeGarbs ctrl regs).flatten.length = (2 ^ ctrl.length - 1) * m := by
  have hf : ∀ (L : List (List Wire)), (∀ r ∈ L, r.length = m) → L.flatten.length = L.length * m := by
    intro L; induction L with
    | nil => intro _; simp
    | cons a L ih =>
      intro h
      rw [List.flatten_cons, List.length_append, h a List.mem_cons_self,
        ih (fun x hx => h x (List.mem_cons_of_mem _ hx)), List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm]
  rw [hf _ (treeGarbs_mem_length ctrl regs m hm), treeGarbs_length ctrl regs hl]

theorem treeAddrs_length : ∀ k : Nat, (treeAddrs k).length = 2 ^ k - 1
  | 0 => rfl
  | k + 1 => by
    simp only [treeAddrs, List.length_append, oddAddrs, List.length_ofFn, List.length_map, treeAddrs_length k]
    have hp : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by decide)
    rw [pow_succ]; omega

theorem pairSwaps_hp (c : Wire) : ∀ regs : List (List Wire), Classical.HPFree (pairSwaps c regs)
  | [] => by simp [pairSwaps]
  | [_] => by simp [pairSwaps]
  | a :: b :: rest => by
    rw [pairSwaps, Classical.hpFree_append]
    exact ⟨First18.swapWords_hp c a b, pairSwaps_hp c rest⟩

theorem swapTree_hp : ∀ (ctrl : List Wire) (regs : List (List Wire)),
    Classical.HPFree (swapTree ctrl regs)
  | [], _ => by simp [swapTree]
  | c :: cs, regs => by
    rw [swapTree, Classical.hpFree_append]
    exact ⟨pairSwaps_hp c regs, swapTree_hp cs (evens regs)⟩

theorem pairSwaps_wf (c : Wire) : ∀ regs : List (List Wire),
    c ∉ regs.flatten → regs.flatten.Nodup → CircuitWellFormed (pairSwaps c regs)
  | [], _, _ => by simp [pairSwaps]
  | [_], _, _ => by simp [pairSwaps]
  | a :: b :: rest, hc, hnd => by
    simp only [List.flatten_cons, List.mem_append, not_or] at hc
    simp only [List.flatten_cons, List.nodup_append] at hnd
    have hab_nd : (a ++ b).Nodup := List.nodup_append.mpr
      ⟨hnd.1, hnd.2.1.1, fun x hx y hy => hnd.2.2 x hx y (List.mem_append_left _ hy)⟩
    rw [pairSwaps, circuitWellFormed_append]
    exact ⟨First18.swapWords_wf c a b hc.1 hc.2.1 hab_nd,
      pairSwaps_wf c rest hc.2.2 hnd.2.1.2.1⟩

theorem swapTree_wf : ∀ (ctrl : List Wire) (regs : List (List Wire)),
    ctrl.Disjoint regs.flatten → regs.flatten.Nodup → CircuitWellFormed (swapTree ctrl regs)
  | [], _, _, _ => by simp [swapTree]
  | c :: cs, regs, hdisj, hnd => by
    have hc : c ∉ regs.flatten := List.disjoint_left.mp hdisj List.mem_cons_self
    have hcs : cs.Disjoint (evens regs).flatten := by
      apply List.disjoint_left.mpr
      intro x hxc hxe
      obtain ⟨r, hr, hxr⟩ := List.mem_flatten.mp hxe
      exact List.disjoint_left.mp hdisj (List.mem_cons_of_mem _ hxc)
        (List.mem_flatten.mpr ⟨r, mem_evens_sub regs hr, hxr⟩)
    rw [swapTree, circuitWellFormed_append]
    exact ⟨pairSwaps_wf c regs hc hnd, swapTree_wf cs (evens regs) hcs (nodup_evens_odds regs hnd).1⟩

theorem pairSwaps_wires (c : Wire) : ∀ (regs : List (List Wire)) (w : Wire),
    w ∈ circuitWires (pairSwaps c regs) → w = c ∨ w ∈ regs.flatten
  | [], _, h => by simp [pairSwaps, circuitWires] at h
  | [_], _, h => by simp [pairSwaps, circuitWires] at h
  | a :: b :: rest, w, h => by
    rw [pairSwaps, MeasuredClear.circuitWires_append] at h
    rcases List.mem_append.mp h with h | h
    · rcases First18.swapWords_wires c a b w h with rfl | ha | hb
      · exact Or.inl rfl
      · exact Or.inr (by simp [ha])
      · exact Or.inr (by simp [hb])
    · rcases pairSwaps_wires c rest w h with rfl | hr
      · exact Or.inl rfl
      · exact Or.inr (by simp [hr])

theorem swapTree_wires : ∀ (ctrl : List Wire) (regs : List (List Wire)) (w : Wire),
    w ∈ circuitWires (swapTree ctrl regs) → w ∈ ctrl ∨ w ∈ regs.flatten
  | [], _, _, h => by simp [swapTree, circuitWires] at h
  | c :: cs, regs, w, h => by
    rw [swapTree, MeasuredClear.circuitWires_append] at h
    rcases List.mem_append.mp h with h | h
    · rcases pairSwaps_wires c regs w h with rfl | hr
      · exact Or.inl List.mem_cons_self
      · exact Or.inr hr
    · rcases swapTree_wires cs (evens regs) w h with hc | hr
      · exact Or.inl (List.mem_cons_of_mem _ hc)
      · obtain ⟨r, hrm, hwr⟩ := List.mem_flatten.mp hr
        exact Or.inr (List.mem_flatten.mpr ⟨r, mem_evens_sub regs hrm, hwr⟩)

theorem pairSwaps_length (c : Wire) (m : Nat) : ∀ (n : Nat) (regs : List (List Wire)),
    regs.length = 2 * n → (∀ r ∈ regs, r.length = m) →
    (pairSwaps c regs).length = 3 * (n * m)
  | 0, [], _, _ => by simp [pairSwaps]
  | 0, _ :: _, h, _ => by simp at h
  | n + 1, a :: b :: rest, h, hm => by
    have h' : rest.length = 2 * n := by simp at h; omega
    rw [pairSwaps, List.length_append, First18.swapWords_length,
      hm a List.mem_cons_self, hm b (List.mem_cons_of_mem _ List.mem_cons_self), Nat.min_self,
      pairSwaps_length c m n rest h' (fun r hr => hm r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)))]
    ring
  | n + 1, [], h, _ => by simp at h
  | n + 1, [_], h, _ => by simp at h; omega

theorem ccxCount_append (c1 c2 : Circuit) : ccxCount (c1 ++ c2) = ccxCount c1 + ccxCount c2 := by
  induction c1 with
  | nil => simp [ccxCount]
  | cons g gs ih =>
    cases g <;> simp only [List.cons_append, ccxCount, ih] <;> omega

theorem pairSwaps_ccx (c : Wire) (m : Nat) : ∀ (n : Nat) (regs : List (List Wire)),
    regs.length = 2 * n → (∀ r ∈ regs, r.length = m) →
    ccxCount (pairSwaps c regs) = n * m
  | 0, [], _, _ => by simp [pairSwaps, ccxCount]
  | 0, _ :: _, h, _ => by simp at h
  | n + 1, a :: b :: rest, h, hm => by
    have h' : rest.length = 2 * n := by simp at h; omega
    rw [pairSwaps, ccxCount_append, First18.swapWords_ccx,
      hm a List.mem_cons_self, hm b (List.mem_cons_of_mem _ List.mem_cons_self), Nat.min_self,
      pairSwaps_ccx c m n rest h' (fun r hr => hm r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)))]
    ring
  | n + 1, [], h, _ => by simp at h
  | n + 1, [_], h, _ => by simp at h; omega

theorem swapTree_length (m : Nat) : ∀ (ctrl : List Wire) (regs : List (List Wire)),
    regs.length = 2 ^ ctrl.length → (∀ r ∈ regs, r.length = m) →
    (swapTree ctrl regs).length = 3 * ((2 ^ ctrl.length - 1) * m)
  | [], _, _, _ => by simp [swapTree]
  | c :: cs, regs, hl, hm => by
    have h2 : regs.length = 2 * 2 ^ cs.length := by
      simpa only [List.length_cons, pow_succ, Nat.mul_comm] using hl
    rw [swapTree, List.length_append, pairSwaps_length c m (2 ^ cs.length) regs h2 hm,
      swapTree_length m cs (evens regs) (evens_length _ _ h2) (fun r hr => hm r (mem_evens_sub regs hr))]
    have hp : 1 ≤ 2 ^ cs.length := Nat.one_le_pow _ _ (by decide)
    simp only [List.length_cons, pow_succ]
    zify [hp, show 1 ≤ 2 ^ cs.length * 2 by omega]
    ring

theorem swapTree_ccx (m : Nat) : ∀ (ctrl : List Wire) (regs : List (List Wire)),
    regs.length = 2 ^ ctrl.length → (∀ r ∈ regs, r.length = m) →
    ccxCount (swapTree ctrl regs) = (2 ^ ctrl.length - 1) * m
  | [], _, _, _ => by simp [swapTree, ccxCount]
  | c :: cs, regs, hl, hm => by
    have h2 : regs.length = 2 * 2 ^ cs.length := by
      simpa only [List.length_cons, pow_succ, Nat.mul_comm] using hl
    rw [swapTree, ccxCount_append, pairSwaps_ccx c m (2 ^ cs.length) regs h2 hm,
      swapTree_ccx m cs (evens regs) (evens_length _ _ h2) (fun r hr => hm r (mem_evens_sub regs hr))]
    have hp : 1 ≤ 2 ^ cs.length := Nat.one_le_pow _ _ (by decide)
    simp only [List.length_cons, pow_succ]
    zify [hp, show 1 ≤ 2 ^ cs.length * 2 by omega]
    ring

/-! ### Classical semantics of `pairSwaps` and `swapTree` -/

theorem pairSwaps_run (c : Wire) (m : Nat) : ∀ (n : Nat) (regs : List (List Wire))
    (wordFn : Nat → List Bool) (base : Nat),
    regs.length = 2 * n → (∀ r ∈ regs, r.length = m) →
    c ∉ regs.flatten → regs.flatten.Nodup →
    ∀ s : BasisState,
    (∀ (j : Nat) (hj : j < regs.length), wireValues (regs[j]'hj) s = wordFn (base + j)) →
    (∀ w, w ∉ regs.flatten → Classical.run (pairSwaps c regs) s w = s w) ∧
    (∀ (j : Nat) (hj : j < (evens regs).length),
      wireValues ((evens regs)[j]'hj) (Classical.run (pairSwaps c regs) s) =
        wordFn (base + 2 * j + (s c).toNat)) ∧
    (∀ (j : Nat) (hj : j < (odds regs).length),
      wireValues ((odds regs)[j]'hj) (Classical.run (pairSwaps c regs) s) =
        wordFn (base + 2 * j + (1 - (s c).toNat)))
  | 0, [], _, _, _, _, _, _, s, _ =>
    ⟨fun _ _ => rfl, fun j hj => by simp [evens] at hj, fun j hj => by simp [odds] at hj⟩
  | 0, _ :: _, _, _, h, _, _, _, _, _ => by simp at h
  | n + 1, [], _, _, h, _, _, _, _, _ => by simp at h
  | n + 1, [_], _, _, h, _, _, _, _, _ => by simp at h; omega
  | n + 1, a :: b :: rest, wordFn, base, hl, hm, hc, hnd, s, hinit => by
    have hl' : rest.length = 2 * n := by simp at hl; omega
    simp only [List.flatten_cons, List.mem_append, not_or] at hc
    simp only [List.flatten_cons, List.nodup_append] at hnd
    have hab_nd : (a ++ b).Nodup := List.nodup_append.mpr
      ⟨hnd.1, hnd.2.1.1, fun x hx y hy => hnd.2.2 x hx y (List.mem_append_left _ hy)⟩
    have ha_len : a.length = m := hm a List.mem_cons_self
    have hb_len : b.length = m := hm b (List.mem_cons_of_mem _ List.mem_cons_self)
    obtain ⟨hfr1, hva1, hvb1⟩ :=
      First18.swapWords_run c a b hc.1 hc.2.1 hab_nd (ha_len.trans hb_len.symm) s
    let s1 := Classical.run (First18.swapWords c a b) s
    have hs1_c : s1 c = s c := hfr1 c hc.1 hc.2.1
    have hs1_rest : ∀ w ∈ rest.flatten, s1 w = s w := fun w hw =>
      hfr1 w (fun ha => hnd.2.2 w ha w (List.mem_append_right _ hw) rfl)
             (fun hb => hnd.2.1.2.2 w hb w hw rfl)
    have hinit_rest : ∀ (j : Nat) (hj : j < rest.length),
        wireValues (rest[j]'hj) s1 = wordFn ((base + 2) + j) := by
      intro j hj
      have hcongr : wireValues (rest[j]'hj) s1 = wireValues (rest[j]'hj) s :=
        List.map_congr_left (fun w hw => hs1_rest w (List.mem_flatten.mpr ⟨rest[j]'hj, List.getElem_mem hj, hw⟩))
      rw [hcongr]
      have h0 := hinit (j + 2) (by simp; omega)
      simpa only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm 2 j] using h0
    obtain ⟨hfr2, hev2, hod2⟩ := pairSwaps_run c m n rest wordFn (base + 2) hl'
      (fun r hr => hm r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)))
      hc.2.2 hnd.2.1.2.1 s1 hinit_rest
    have hrun : Classical.run (pairSwaps c (a :: b :: rest)) s = Classical.run (pairSwaps c rest) s1 := by
      rw [pairSwaps, Classical.run_append]
    rw [hrun]
    have ha_out : ∀ w ∈ a, w ∉ rest.flatten := fun w hwa hwr =>
      hnd.2.2 w hwa w (List.mem_append_right _ hwr) rfl
    have hb_out : ∀ w ∈ b, w ∉ rest.flatten := fun w hwb hwr =>
      hnd.2.1.2.2 w hwb w hwr rfl
    refine ⟨?_, ?_, ?_⟩
    · intro w hw
      simp only [List.flatten_cons, List.mem_append, not_or] at hw
      rw [hfr2 w hw.2.2]
      exact hfr1 w hw.1 hw.2.1
    · intro j hj
      cases j with
      | zero =>
        change wireValues a (Classical.run (pairSwaps c rest) s1) = wordFn (base + 2 * 0 + (s c).toNat)
        have hstay : wireValues a (Classical.run (pairSwaps c rest) s1) = wireValues a s1 :=
          List.map_congr_left (fun w hw => hfr2 w (ha_out w hw))
        rw [hstay, hva1]
        have h0 := hinit 0 (by simp)
        have h1 := hinit 1 (by simp)
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1
        rw [h0, h1]; cases s c <;> simp
      | succ j =>
        change wireValues ((evens rest)[j]'(by simpa [evens] using hj)) (Classical.run (pairSwaps c rest) s1) = _
        rw [hev2 j (by simpa [evens] using hj), hs1_c]
        congr 1; omega
    · intro j hj
      cases j with
      | zero =>
        change wireValues b (Classical.run (pairSwaps c rest) s1) = wordFn (base + 2 * 0 + (1 - (s c).toNat))
        have hstay : wireValues b (Classical.run (pairSwaps c rest) s1) = wireValues b s1 :=
          List.map_congr_left (fun w hw => hfr2 w (hb_out w hw))
        rw [hstay, hvb1]
        have h0 := hinit 0 (by simp)
        have h1 := hinit 1 (by simp)
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1
        rw [h0, h1]; cases s c <;> simp
      | succ j =>
        change wireValues ((odds rest)[j]'(by simpa [odds] using hj)) (Classical.run (pairSwaps c rest) s1) = _
        rw [hod2 j (by simpa [odds] using hj), hs1_c]
        congr 1; omega

theorem swapTree_run (m : Nat) : ∀ (ctrl : List Wire) (regs : List (List Wire))
    (wordFn : Nat → List Bool) (hi : Nat),
    regs.length = 2 ^ ctrl.length → (∀ r ∈ regs, r.length = m) →
    ctrl.Disjoint regs.flatten → regs.flatten.Nodup →
    ∀ s : BasisState,
    (∀ (j : Nat) (hj : j < regs.length), wireValues (regs[j]'hj) s = wordFn (2 ^ ctrl.length * hi + j)) →
    let a := tableAddressValue ctrl s + 2 ^ ctrl.length * hi
    let t := Classical.run (swapTree ctrl regs) s
    (∀ w, w ∉ regs.flatten → t w = s w) ∧
    (∀ (h0 : 0 < regs.length), wireValues (regs[0]'h0) t = wordFn a) ∧
    (∀ p ∈ (treeAddrs ctrl.length).zip (treeGarbs ctrl regs), wireValues p.2 t = wordFn (p.1 a))
  | [], regs, wordFn, hi, hl, _, _, _, s, hinit => by
    dsimp only
    have hl1 : regs.length = 1 := by simpa using hl
    refine ⟨fun _ _ => rfl, fun h0 => ?_, fun p hp => by simp [treeAddrs, treeGarbs] at hp⟩
    simpa [tableAddressValue] using hinit 0 h0
  | c :: cs, regs, wordFn, hi, hl, hm, hdisj, hnd, s, hinit => by
    dsimp only
    have h2 : regs.length = 2 * 2 ^ cs.length := by
      simpa only [List.length_cons, pow_succ, Nat.mul_comm] using hl
    have hc_not : c ∉ regs.flatten := List.disjoint_left.mp hdisj List.mem_cons_self
    obtain ⟨he_nd, ho_nd, heo⟩ := nodup_evens_odds regs hnd
    have hinit' : ∀ (j : Nat) (hj : j < regs.length),
        wireValues (regs[j]'hj) s = wordFn (2 ^ (c :: cs).length * hi + j) := hinit
    obtain ⟨hfr1, hev1, hod1⟩ := pairSwaps_run c m (2 ^ cs.length) regs wordFn (2 ^ (c :: cs).length * hi)
      h2 hm hc_not hnd s hinit'
    let s1 := Classical.run (pairSwaps c regs) s
    let b0 := (s c).toNat
    let wordFn' : Nat → List Bool := fun y => wordFn (2 * y + b0)
    have hcs_disj : cs.Disjoint (evens regs).flatten := by
      apply List.disjoint_left.mpr
      intro x hxc hxe
      obtain ⟨r, hr, hxr⟩ := List.mem_flatten.mp hxe
      exact List.disjoint_left.mp hdisj (List.mem_cons_of_mem _ hxc)
        (List.mem_flatten.mpr ⟨r, mem_evens_sub regs hr, hxr⟩)
    have hs1_cs : tableAddressValue cs s1 = tableAddressValue cs s := by
      apply tableAddressValue_congr
      intro w hw
      exact hfr1 w (List.disjoint_left.mp hdisj (List.mem_cons_of_mem _ hw))
    have hinit_ev : ∀ (j : Nat) (hj : j < (evens regs).length),
        wireValues ((evens regs)[j]'hj) s1 = wordFn' (2 ^ cs.length * hi + j) := by
      intro j hj
      rw [hev1 j hj]
      simp only [wordFn', b0, List.length_cons, pow_succ]
      congr 1; ring
    obtain ⟨hfr2, h0_2, hgarb2⟩ := swapTree_run m cs (evens regs) wordFn' hi
      (evens_length _ _ h2) (fun r hr => hm r (mem_evens_sub regs hr)) hcs_disj he_nd s1 hinit_ev
    have hrun : Classical.run (swapTree (c :: cs) regs) s = Classical.run (swapTree cs (evens regs)) s1 := by
      rw [swapTree, Classical.run_append]
    rw [hrun]
    let a := tableAddressValue (c :: cs) s + 2 ^ (c :: cs).length * hi
    have ha_val : a = 2 * (tableAddressValue cs s + 2 ^ cs.length * hi) + b0 := by
      change (s c).toNat + 2 * tableAddressValue cs s + 2 ^ (cs.length + 1) * hi = _
      rw [pow_succ]; simp only [b0]; ring
    have ha_div2 : a / 2 = tableAddressValue cs s + 2 ^ cs.length * hi := by
      have hb0 : b0 < 2 := by simp only [b0]; cases s c <;> decide
      omega
    have ha_mod2 : a % 2 = b0 := by
      have hb0 : b0 < 2 := by simp only [b0]; cases s c <;> decide
      omega
    have ha_divK : a / 2 ^ (cs.length + 1) = hi := by
      have hlt : tableAddressValue (c :: cs) s < 2 ^ (cs.length + 1) := by
        simpa [List.length_cons] using tableAddressValue_lt (c :: cs) s
      change (tableAddressValue (c :: cs) s + 2 ^ (cs.length + 1) * hi) / 2 ^ (cs.length + 1) = hi
      rw [Nat.add_mul_div_left _ _ (pow_pos (by decide) _), Nat.div_eq_of_lt hlt, Nat.zero_add]
    refine ⟨?_, ?_, ?_⟩
    · intro w hw
      have hw_ev : w ∉ (evens regs).flatten := fun h => by
        obtain ⟨r, hr, hwr⟩ := List.mem_flatten.mp h
        exact hw (List.mem_flatten.mpr ⟨r, mem_evens_sub regs hr, hwr⟩)
      rw [hfr2 w hw_ev]
      exact hfr1 w hw
    · intro h0
      have h0_ev : 0 < (evens regs).length := by
        rw [evens_length _ _ h2]; exact pow_pos (by decide) _
      have hev0 : (evens regs)[0]'h0_ev = regs[0]'h0 := by
        cases regs with
        | nil => simp at h0
        | cons x xs =>
          cases xs with
          | nil =>
            have hp : 1 ≤ 2 ^ cs.length := Nat.one_le_pow _ _ (by decide)
            simp at h2; omega
          | cons y ys => rfl
      rw [← hev0, h0_2 h0_ev, hs1_cs]
      simp only [wordFn', a, ha_val]
    · intro p hp
      simp only [List.length_cons, treeAddrs, treeGarbs] at hp
      have hlen_odd : (oddAddrs cs.length).length = (odds regs).length := by
        rw [oddAddrs, List.length_ofFn, odds_length _ _ h2]
      rw [List.zip_append hlen_odd, List.mem_append] at hp
      rcases hp with hodd | htail
      · obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hodd
        have hj1 : j < (oddAddrs cs.length).length := by simp at hj; exact hj.1
        have hj2 : j < (odds regs).length := by simp at hj; exact hj.2
        have hpe : p = ((oddAddrs cs.length)[j]'hj1, (odds regs)[j]'hj2) := by
          simpa [List.getElem_zip] using heq.symm
        subst hpe
        have hdisj_r : ∀ w ∈ (odds regs)[j]'hj2, w ∉ (evens regs).flatten := fun w hw he =>
          List.disjoint_left.mp heo he (List.mem_flatten.mpr ⟨(odds regs)[j]'hj2, List.getElem_mem hj2, hw⟩)
        have hstay : wireValues ((odds regs)[j]'hj2) (Classical.run (swapTree cs (evens regs)) s1) =
            wireValues ((odds regs)[j]'hj2) s1 :=
          List.map_congr_left (fun w hw => hfr2 w (hdisj_r w hw))
        rw [hstay, hod1 j hj2]
        simp only [oddAddrs, List.getElem_ofFn]
        change wordFn (2 ^ (c :: cs).length * hi + 2 * j + (1 - (s c).toNat)) =
          wordFn (2 * (2 ^ cs.length * (a / 2 ^ (cs.length + 1)) + j) + (1 - a % 2))
        rw [ha_divK, ha_mod2]
        simp only [b0, List.length_cons, pow_succ]
        congr 1; ring
      · rw [List.zip_map_left, List.mem_map] at htail
        obtain ⟨⟨g, reg⟩, hmem, rfl⟩ := htail
        have h2' := hgarb2 (g, reg) hmem
        simp only [hs1_cs, wordFn'] at h2'
        dsimp only [Prod.map, id_eq]
        rw [h2', ha_div2, ha_mod2]

/-! ### Part 2: Address splitting and QROM multi-register loading -/

theorem tableAddressValue_append (lo hi : List Wire) (s : BasisState) :
    tableAddressValue (lo ++ hi) s = tableAddressValue lo s + 2 ^ lo.length * tableAddressValue hi s := by
  induction lo with
  | nil => simp [tableAddressValue]
  | cons w ws ih =>
    change (s w).toNat + 2 * tableAddressValue (ws ++ hi) s =
      ((s w).toNat + 2 * tableAddressValue ws s) + 2 ^ (ws.length + 1) * tableAddressValue hi s
    rw [ih, pow_succ]; ring


theorem mem_zipIdx_iff {α : Type} : ∀ (L : List α) (base : Nat) (x : α) (t : Nat),
    (x, t) ∈ L.zipIdx base ↔ ∃ i : Nat, ∃ hi : i < L.length, L[i]'hi = x ∧ base + i = t
  | [], _, _, _ => by simp
  | a :: as, base, x, t => by
    rw [List.zipIdx_cons, List.mem_cons, mem_zipIdx_iff as (base + 1) x t]
    constructor
    · rintro (h | ⟨i, hi, heq, ht⟩)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        exact ⟨0, by simp, rfl, by omega⟩
      · exact ⟨i + 1, by simp; omega, heq, by omega⟩
    · rintro ⟨i, hi, heq, ht⟩
      cases i with
      | zero => exact Or.inl (Prod.ext heq.symm (by omega))
      | succ i => exact Or.inr ⟨i, by simpa using hi, heq, by omega⟩


/-! ### Part 1: 20-bit window bank (`19` addr + `1` sign), 512-bit XY payload, and fixup bank -/

def bits : List Wire := List.range' 855 20
def addrBits : List Wire := List.range' 855 19
def signBit : Wire := 874
def xyWires : List Wire := List.range' 263 256 ++ List.range' 580 256

def Input (s : BasisState) : Prop :=
  s 836 = true ∧ ∀ v, v ≠ 836 → v ∉ bits → s v = false

def tablePoint (coeffs : Fin 524288 → PointCoeff) (Q : Point) (a : Nat) : Point :=
  constantPoint Q (coeffs ⟨a % 524288, Nat.mod_lt _ (by decide +kernel)⟩)

def signedPoint (coeffs : Fin 524288 → PointCoeff) (Q : Point) (v : Nat) : Point :=
  if v < 524288 then -(tablePoint coeffs Q (524287 - v)) else tablePoint coeffs Q (v - 524288)

def update (init : Point → Nat → Point) (Q : Point) (s : BasisState) : BasisState :=
  pointWrite (init Q (tableAddressValue bits s)) s

def row (a : Nat) : Fin 524288 := ⟨a % 524288, Nat.mod_lt _ (by decide +kernel)⟩

def slots : List (Fin 524288 → ConstantBit 524288) :=
  List.ofFn (fun i : Fin 256 => fun r => (⟨r, .x, i⟩ : ConstantBit 524288)) ++
  List.ofFn (fun i : Fin 256 => fun r => (⟨r, .y, i⟩ : ConstantBit 524288))

def xyRefs (r : Fin 524288) : List (ConstantBit 524288) :=
  slots.map (fun f => f r)

def word (read : ConstantBit 524288 → Bool) (a : Nat) : List Bool :=
  (xyRefs (row a)).map read

def low (i : Fin 9) : Wire := 855 + i.val
def high : List Wire := List.range' 864 10
def clearPaths : List Wire := List.range' 519 10
def scratch : Wire := 875
def hot (i : Fin 512) : Wire := 876 + i.val

theorem bits_length : bits.length = 20 := by decide +kernel
theorem bits_nodup : bits.Nodup := List.nodup_range'
theorem addrBits_length : addrBits.length = 19 := by decide +kernel
theorem addrBits_nodup : addrBits.Nodup := List.nodup_range'
theorem bits_eq_append : bits = addrBits ++ [signBit] := by decide +kernel

theorem mem_bits {w : Wire} : w ∈ bits ↔ 855 ≤ w ∧ w < 875 := by
  simp only [bits, List.mem_range'_1]

theorem mem_addrBits {w : Wire} : w ∈ addrBits ↔ 855 ≤ w ∧ w < 874 := by
  simp only [addrBits, List.mem_range'_1]

theorem mem_xyWires {w : Wire} : w ∈ xyWires ↔ (263 ≤ w ∧ w < 519) ∨ (580 ≤ w ∧ w < 836) := by
  simp only [xyWires, List.mem_append, List.mem_range'_1]

theorem xyWires_length : xyWires.length = 512 := by simp [xyWires]

theorem xyWires_nodup : xyWires.Nodup :=
  List.nodup_append.mpr ⟨List.nodup_range', List.nodup_range', fun a ha b hb hab => by
    subst hab; simp only [List.mem_range'_1] at ha hb; omega⟩

theorem pointLogicalWires_eq : pointLogicalWires = xyWires ++ [838] := by
  simp [pointLogicalWires, pointCorrectionX, pointCorrectionYInf, xyWires, List.append_assoc]

theorem bits_not_point (w : Wire) (hb : w ∈ bits) (hp : w ∈ pointLogicalWires) : False := by
  have h1 := mem_bits.mp hb
  have h2 := First18.mem_point hp
  (try dsimp only [Wire] at *); omega

theorem addrBits_not_xy (w : Wire) (hb : w ∈ addrBits) (hp : w ∈ xyWires) : False := by
  have h1 := mem_addrBits.mp hb
  have h2 := mem_xyWires.mp hp
  (try dsimp only [Wire] at *); omega

theorem bits_subset_range : bits ⊆ List.range 1610 := by
  intro w hw
  have h := mem_bits.mp hw
  rw [List.mem_range]; (try dsimp only [Wire] at *); omega

theorem input_clean (s : BasisState) (hs : Input s) (w : Nat)
    (h1 : w ≠ 836) (h2 : w < 855 ∨ 875 ≤ w) : s w = false := by
  apply hs.2 w h1
  intro hm
  have := mem_bits.mp hm
  (try dsimp only [Wire] at *); omega

theorem slots_length : slots.length = 512 := by
  rw [slots, List.length_append, List.length_ofFn, List.length_ofFn]

theorem pointRefs_eq_xyRefs (r : Fin 524288) :
    pointRefs r = xyRefs r ++ [⟨r, .infinity, ⟨0, by decide +kernel⟩⟩] := by
  rw [pointRefs, xyRefs, slots, List.map_append, List.map_ofFn, List.map_ofFn]
  rfl

theorem zipWith_targets {α : Type} (g : α → Wire → MeasuredClear.ClearPort 524288)
    (hg : ∀ x w, (g x w).target = w) :
    ∀ (xs : List α) (ws : List Wire), xs.length = ws.length →
      (List.zipWith g xs ws).map MeasuredClear.ClearPort.target = ws
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, w :: ws, h => by
    rw [List.zipWith_cons_cons, List.map_cons, hg, zipWith_targets g hg xs ws (by simpa using h)]

theorem hot_eq : List.ofFn hot = List.range' 876 512 := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_range']
  · intro i h1 h2
    simp only [List.getElem_ofFn, List.getElem_range', hot, Nat.one_mul]

theorem low_high_addrBits :
    [MeasuredClear.lowN9 low 0, MeasuredClear.lowN9 low 1, MeasuredClear.lowN9 low 2,
     MeasuredClear.lowN9 low 3, MeasuredClear.lowN9 low 4, MeasuredClear.lowN9 low 5,
     MeasuredClear.lowN9 low 6, MeasuredClear.lowN9 low 7, MeasuredClear.lowN9 low 8] ++ high = addrBits := by
  simp only [MeasuredClear.lowN9, low, high, addrBits]
  decide

theorem clear_layout : (tableAddressTree high 0 1).Layout 836 clearPaths :=
  tableAddressTree_layout _ _ _ _ _
    (by simp only [high, clearPaths, List.length_range']; omega)
    (by
      rw [List.cons_append, List.nodup_cons]
      refine ⟨by simp [high, clearPaths, List.mem_range'_1], ?_⟩
      exact List.nodup_append.mpr ⟨List.nodup_range', List.nodup_range', fun a ha b hb hab => by
        subst hab; simp only [high, clearPaths, List.mem_range'_1] at ha hb; omega⟩)

theorem high_index : (tableAddressTree high 0 1).indexWires.dedup = high :=
  tableAddressTree_index _ _ _ List.nodup_range'

theorem clear_nodes : (tableAddressTree high 0 1).internalNodes = 1023 := by
  have h := tableAddressTree_nodes high 0 1
  change _ + 1 = 1024 at h
  (try dsimp only [Wire] at *); omega

theorem clear_leaves : (tableAddressTree high 0 1).leaves = 1024 := by
  rw [MeasuredClear.addressTree_leaves]; rfl

theorem clear_measurements : MeasuredClear.recordMeasurements
    (MeasuredClear.recordUnaryOps (tableAddressTree high 0 1) 836 clearPaths) = 1023 := by
  rw [(MeasuredClear.recordUnary_counts _ _ _ clear_layout 0).1, clear_nodes]

theorem hot_injective : Function.Injective hot := by
  intro i j h
  simp only [hot] at h
  exact Fin.ext (by (try dsimp only [Wire] at *); omega)

theorem low_ne_hot : ∀ i j, low i ≠ hot j := by
  intro i j h
  simp only [low, hot] at h
  have := i.isLt
  (try dsimp only [Wire] at *); omega

theorem low_ne_836 (i : Fin 9) : low i ≠ 836 := by
  simp only [low]; have := i.isLt; (try dsimp only [Wire] at *); omega

theorem hot_ne_836 (i : Fin 512) : hot i ≠ 836 := by
  simp only [hot]; (try dsimp only [Wire] at *); omega

theorem hot_disjoint : (MeasuredClear.hotBank9 hot).Disjoint
    (836 :: (tableAddressTree high 0 1).indexWires.dedup ++ clearPaths) := by
  rw [high_index]
  intro w hw hm
  simp only [MeasuredClear.hotBank9, hot_eq, high, clearPaths, List.mem_cons, List.mem_append,
    List.mem_range'_1, List.mem_singleton, List.not_mem_nil, or_false] at hw hm
  (try dsimp only [Wire] at *); omega

theorem scratch_not_tree : scratch ∉ 836 :: (tableAddressTree high 0 1).indexWires.dedup ++ clearPaths := by
  rw [high_index]
  simp [scratch, high, clearPaths, List.mem_range'_1]

theorem scratch_not_hot : scratch ∉ MeasuredClear.hotBank9 hot := by
  rw [MeasuredClear.hotBank9, hot_eq, List.mem_range'_1]
  simp [scratch]

/-! ### Part 2: QROM multi-register loading for `n = 524288` -/

def sliceWord (sliceSlots : List (Fin 524288 → ConstantBit 524288))
    (read : ConstantBit 524288 → Bool) (a : Nat) : List Bool :=
  sliceSlots.map fun f => read (f (row a))

theorem sliceWord_length (sliceSlots : List (Fin 524288 → ConstantBit 524288))
    (read : ConstantBit 524288 → Bool) (a : Nat) :
    (sliceWord sliceSlots read a).length = sliceSlots.length := by
  simp [sliceWord]

def passLeaf (k : Nat) (sliceSlots : List (Fin 524288 → ConstantBit 524288))
    (regs : List (List Wire)) (l : Nat) (q : Wire) : List (TemplateGate 524288) :=
  lookupLeafGates q (regs.zipIdx.flatMap fun p =>
    (sliceSlots.map fun f => f (row (2 ^ k * l + p.2))).zip p.1)

def passMask (k : Nat) (sliceSlots : List (Fin 524288 → ConstantBit 524288))
    (regs : List (List Wire)) (read : ConstantBit 524288 → Bool) (l : Nat) : List Wire :=
  regs.zipIdx.flatMap fun p => tableBitsMask p.1 (sliceWord sliceSlots read (2 ^ k * l + p.2))

theorem passLeaf_instantiate (k : Nat) (sliceSlots : List (Fin 524288 → ConstantBit 524288))
    (regs : List (List Wire)) (read : ConstantBit 524288 → Bool) (l : Nat) (q : Wire) :
    (passLeaf k sliceSlots regs l q).flatMap (TemplateGate.instantiate read) =
      tableXorGates q (passMask k sliceSlots regs read l) := by
  rw [passLeaf, lookupLeafGates_instantiate]
  have h1 : ∀ (L : List (List Wire × Nat)),
      ((L.flatMap fun p => (sliceSlots.map fun f => f (row (2 ^ k * l + p.2))).zip p.1).filter
        (fun x => read x.1)).map (fun x => Gate.CX q x.2) =
      tableXorGates q (L.flatMap fun p => tableBitsMask p.1 (sliceWord sliceSlots read (2 ^ k * l + p.2))) := by
    intro L
    induction L with
    | nil => rfl
    | cons p ps ih =>
      rw [List.flatMap_cons, List.filter_append, List.map_append, ih, List.flatMap_cons,
        show tableXorGates q (_ ++ _) = tableXorGates q _ ++ tableXorGates q _ from List.map_append]
      congr 1
      rw [show (fun x : ConstantBit 524288 × Wire => Gate.CX q x.2) = (Gate.CX q) ∘ Prod.snd from rfl,
        ← List.map_map, filtered_zip_mask, List.map_map]
      rfl
  exact h1 regs.zipIdx

theorem passLeaf_length (k : Nat) (sliceSlots : List (Fin 524288 → ConstantBit 524288))
    (regs : List (List Wire)) (l : Nat) (q : Wire) :
    (passLeaf k sliceSlots regs l q).length ≤ regs.length * sliceSlots.length := by
  rw [passLeaf, lookupLeafGates, List.length_map]
  have h1 : ∀ (L : List (List Wire × Nat)),
      (L.flatMap fun p => (sliceSlots.map fun f => f (row (2 ^ k * l + p.2))).zip p.1).length ≤
        L.length * sliceSlots.length := by
    intro L; induction L with
    | nil => simp
    | cons p ps ih =>
      rw [List.flatMap_cons, List.length_append, List.length_zip, List.length_map, List.length_cons,
        Nat.add_mul, Nat.one_mul]
      have := Nat.min_le_left sliceSlots.length p.1.length
      omega
  simpa [List.length_zipIdx] using h1 regs.zipIdx

theorem passMask_sub (k : Nat) (sliceSlots : List (Fin 524288 → ConstantBit 524288))
    (regs : List (List Wire)) (read : ConstantBit 524288 → Bool) (l : Nat) :
    passMask k sliceSlots regs read l ⊆ regs.flatten := by
  intro w hw
  obtain ⟨⟨r, t⟩, hmem, hwm⟩ := List.mem_flatMap.mp hw
  have hr : r ∈ regs := by
    obtain ⟨i, hi, heq, _⟩ := (mem_zipIdx_iff regs 0 r t).mp hmem
    rw [← heq]; exact List.getElem_mem hi
  exact List.mem_flatten.mpr ⟨r, hr, tableBitsMask_subset _ _ hwm⟩

theorem passMask_nodup (k : Nat) (sliceSlots : List (Fin 524288 → ConstantBit 524288))
    (regs : List (List Wire)) (read : ConstantBit 524288 → Bool) (l : Nat)
    (hnd : regs.flatten.Nodup) : (passMask k sliceSlots regs read l).Nodup := by
  have hgen : ∀ (L : List (List Wire)) (idx : Nat), L.flatten.Nodup →
      ((L.zipIdx idx).flatMap fun p => tableBitsMask p.1 (sliceWord sliceSlots read (2 ^ k * l + p.2))).Nodup := by
    intro L
    induction L with
    | nil => intro _ _; simp
    | cons r rs ih =>
      intro idx hnd'
      simp only [List.flatten_cons, List.nodup_append] at hnd'
      rw [List.zipIdx_cons, List.flatMap_cons, List.nodup_append]
      refine ⟨tableBitsMask_nodup _ _ hnd'.1, ih (idx + 1) hnd'.2.1, ?_⟩
      intro x hx y hy hxy
      subst hxy
      obtain ⟨⟨r', t'⟩, hmem, hxm⟩ := List.mem_flatMap.mp hy
      obtain ⟨i, hi, heq, _⟩ := (mem_zipIdx_iff rs (idx + 1) r' t').mp hmem
      have hxr : x ∈ r := tableBitsMask_subset _ _ hx
      have hxr' : x ∈ rs.flatten := List.mem_flatten.mpr ⟨r', heq ▸ List.getElem_mem hi, tableBitsMask_subset _ _ hxm⟩
      exact hnd'.2.2 x hxr x hxr' rfl
  exact hgen regs 0 hnd

theorem passMask_read (k : Nat) (sliceSlots : List (Fin 524288 → ConstantBit 524288))
    (regs : List (List Wire)) (read : ConstantBit 524288 → Bool) (selBits : List Wire)
    (hnd : regs.flatten.Nodup) (hlen : ∀ r ∈ regs, r.length = sliceSlots.length)
    (s : BasisState) (hroot : s 836 = true) (hclean : Clean regs.flatten s) :
    ∀ (j : Nat) (hj : j < regs.length),
      wireValues (regs[j]'hj) (tableLookupState (passMask k sliceSlots regs read) selBits 836 s) =
        sliceWord sliceSlots read (2 ^ k * tableAddressValue selBits s + j) := by
  intro j hj
  let r := regs[j]'hj
  let l := tableAddressValue selBits s
  have hr_nd : r.Nodup := by
    have hmem : r ∈ regs := List.getElem_mem hj
    have hsplit : ∀ (L : List (List Wire)), L.flatten.Nodup → ∀ q ∈ L, q.Nodup := by
      intro L; induction L with
      | nil => intro _ _ h; cases h
      | cons a L ih =>
        intro h q hq
        rw [List.flatten_cons, List.nodup_append] at h
        rcases List.mem_cons.mp hq with rfl | hq
        · exact h.1
        · exact ih h.2.1 q hq
    exact hsplit regs hnd r hmem
  have hr_clean : Clean r s := fun w hw => hclean w (List.mem_flatten.mpr ⟨r, List.getElem_mem hj, hw⟩)
  have hmem_iff : ∀ w ∈ r, (w ∈ passMask k sliceSlots regs read l) ↔
      (w ∈ tableBitsMask r (sliceWord sliceSlots read (2 ^ k * l + j))) := by
    intro w hw
    constructor
    · intro hm
      obtain ⟨⟨r', t'⟩, hmt, hwm⟩ := List.mem_flatMap.mp hm
      obtain ⟨i, hi, heq1, heq2⟩ := (mem_zipIdx_iff regs 0 r' t').mp hmt
      simp only [Nat.zero_add] at heq2
      have hti : i = j := by
        by_contra hne
        have hdisj : ∀ (L : List (List Wire)), L.flatten.Nodup →
            ∀ (a b : Nat) (ha : a < L.length) (hb : b < L.length), a ≠ b →
              ∀ x ∈ L[a]'ha, x ∉ L[b]'hb := by
          intro L; induction L with
          | nil => intro _ _ _ ha; simp at ha
          | cons q qs ih =>
            intro h a b ha hb hne' x hxa hxb
            rw [List.flatten_cons, List.nodup_append] at h
            cases a with
            | zero =>
              cases b with
              | zero => exact hne' rfl
              | succ b =>
                exact h.2.2 x hxa x (List.mem_flatten.mpr ⟨qs[b]'(by simpa using hb), List.getElem_mem _, hxb⟩) rfl
            | succ a =>
              cases b with
              | zero =>
                exact h.2.2 x hxb x (List.mem_flatten.mpr ⟨qs[a]'(by simpa using ha), List.getElem_mem _, hxa⟩) rfl
              | succ b =>
                exact ih h.2.1 a b (by simpa using ha) (by simpa using hb) (by omega) x hxa hxb
        have hwi : w ∈ regs[i]'hi := heq1 ▸ tableBitsMask_subset _ _ hwm
        exact hdisj regs hnd i j hi hj hne w hwi hw
      subst hti
      rw [← heq1, ← heq2] at hwm
      exact hwm
    · intro hm
      refine List.mem_flatMap.mpr ⟨(r, j), ?_, hm⟩
      exact (mem_zipIdx_iff regs 0 r j).mpr ⟨j, hj, rfl, Nat.zero_add j⟩
  have heq : wireValues r (tableLookupState (passMask k sliceSlots regs read) selBits 836 s) =
      wireValues r (tableXorState (tableBitsMask r (sliceWord sliceSlots read (2 ^ k * l + j))) true s) := by
    apply List.map_congr_left
    intro w hw
    simp only [tableLookupState, tableXorState, hroot]
    have hl' : tableAddressValue selBits s = l := rfl
    rw [hl']
    simp only [hmem_iff w hw]
  rw [heq, tableBitsMask_read _ _ s hr_nd (by rw [hlen r (List.getElem_mem hj), sliceWord_length]) hr_clean]

/-! ### Part 3: Generic `Pass` structure for 19-bit SelectSwap -/

def passClearData (k : Nat) (sliceSlots : List (Fin 524288 → ConstantBit 524288))
    (ctrl : List Wire) (regs : List (List Wire)) : List (MeasuredClear.ClearPort 524288) :=
  ((treeAddrs k).zip (treeGarbs ctrl regs)).flatMap fun p =>
    List.zipWith (fun f w => (⟨fun x => f (row (p.1 x)), true, w⟩ : MeasuredClear.ClearPort 524288))
      sliceSlots p.2

theorem passClearData_targets (k : Nat) (sliceSlots : List (Fin 524288 → ConstantBit 524288))
    (ctrl : List Wire) (regs : List (List Wire))
    (hk : ctrl.length = k) (hl : regs.length = 2 ^ k)
    (hm : ∀ r ∈ regs, r.length = sliceSlots.length) :
    (passClearData k sliceSlots ctrl regs).map MeasuredClear.ClearPort.target =
      (treeGarbs ctrl regs).flatten := by
  have hlen : (treeAddrs k).length = (treeGarbs ctrl regs).length := by
    rw [treeAddrs_length, treeGarbs_length ctrl regs (by rw [hk]; exact hl), hk]
  have hml : ∀ r ∈ treeGarbs ctrl regs, r.length = sliceSlots.length :=
    treeGarbs_mem_length ctrl regs sliceSlots.length hm
  have hgen : ∀ (fs : List (Nat → Nat)) (gs : List (List Wire)),
      fs.length = gs.length → (∀ r ∈ gs, r.length = sliceSlots.length) →
      ((fs.zip gs).flatMap fun p =>
        List.zipWith (fun f w => (⟨fun x => f (row (p.1 x)), true, w⟩ : MeasuredClear.ClearPort 524288))
          sliceSlots p.2).map MeasuredClear.ClearPort.target = gs.flatten := by
    intro fs; induction fs with
    | nil =>
      intro gs h _
      have hnil : gs = [] := List.eq_nil_of_length_eq_zero (by simpa using h.symm)
      subst hnil; rfl
    | cons fn fs ih =>
      intro gs h hml'
      cases gs with
      | nil => simp at h
      | cons g gs =>
        simp only [List.zip_cons_cons, List.flatMap_cons, List.map_append, List.flatten_cons]
        rw [zipWith_targets _ (fun _ _ => rfl) sliceSlots g (hml' g List.mem_cons_self).symm,
          ih gs (by simpa using h) (fun r hr => hml' r (List.mem_cons_of_mem _ hr))]
  exact hgen (treeAddrs k) (treeGarbs ctrl regs) hlen hml

theorem passClearData_loaded (k : Nat) (sliceSlots : List (Fin 524288 → ConstantBit 524288))
    (ctrl : List Wire) (regs : List (List Wire))
    (read : ConstantBit 524288 → Bool) (a : Nat) (u : BasisState)
    (hvals : ∀ p ∈ (treeAddrs k).zip (treeGarbs ctrl regs),
      wireValues p.2 u = sliceWord sliceSlots read (p.1 a)) :
    ∀ q ∈ passClearData k sliceSlots ctrl regs,
      u q.target = (true && decide (read (q.ref a) = q.value)) := by
  intro q hq
  obtain ⟨⟨fn, reg⟩, hmem, hq'⟩ := List.mem_flatMap.mp hq
  have hv := hvals (fn, reg) hmem
  have hgen : ∀ (ss : List (Fin 524288 → ConstantBit 524288)) (ws : List Wire),
      wireValues ws u = ss.map (fun f => read (f (row (fn a)))) →
      ∀ port ∈ List.zipWith (fun f w => (⟨fun x => f (row (fn x)), true, w⟩ : MeasuredClear.ClearPort 524288)) ss ws,
        u port.target = (true && decide (read (port.ref a) = port.value)) := by
    intro ss; induction ss with
    | nil => intro _ _ _ hp; simp at hp
    | cons f ss ih =>
      intro ws h port hp
      cases ws with
      | nil => simp at hp
      | cons w ws =>
        have h' : u w = read (f (row (fn a))) ∧
            wireValues ws u = ss.map (fun f => read (f (row (fn a)))) := List.cons.inj h
        rw [List.zipWith_cons_cons, List.mem_cons] at hp
        rcases hp with rfl | hp
        · show u w = (true && decide (read (f (row (fn a))) = true))
          rw [h'.1]; cases read (f (row (fn a))) <;> rfl
        · exact ih ws h'.2 port hp
  exact hgen sliceSlots reg hv q hq'

structure Pass where
  k : Nat
  m : Nat
  sliceSlots : List (Fin 524288 → ConstantBit 524288)
  ctrl : List Wire
  selBits : List Wire
  selPaths : List Wire
  out : List Wire
  garb : List Wire

namespace Pass

def regs (P : Pass) : List (List Wire) := P.out :: chunks (2 ^ P.k - 1) P.m P.garb
def leaf (P : Pass) (l : Nat) (q : Wire) : List (TemplateGate 524288) :=
  passLeaf P.k P.sliceSlots P.regs l q
def selOps (P : Pass) : List (LookupOp 524288) :=
  unaryLookupOps P.leaf (tableAddressTree P.selBits 0 1) 836 P.selPaths
def swap (P : Pass) : Circuit := swapTree P.ctrl P.regs
def targets (P : Pass) : List Wire := (treeGarbs P.ctrl P.regs).flatten
def clearData (P : Pass) : List (MeasuredClear.ClearPort 524288) :=
  passClearData P.k P.sliceSlots P.ctrl P.regs
def selMeas (P : Pass) : Nat := 2 ^ (19 - P.k) - 1
def garbLen (P : Pass) : Nat := (2 ^ P.k - 1) * P.m

structure Geo (P : Pass) : Prop where
  hk : 0 < P.k ∧ P.k < 19
  hctrl_len : P.ctrl.length = P.k
  hsel_len : P.selBits.length = 19 - P.k
  hpaths_len : P.selPaths.length = 19 - P.k
  hbits : P.ctrl ++ P.selBits = addrBits
  hslots_len : P.sliceSlots.length = P.m
  hout_len : P.out.length = P.m
  hgarb_len : P.garb.length = (2 ^ P.k - 1) * P.m
  hsel_nodup : (836 :: P.selBits ++ P.selPaths).Nodup
  hregs_nodup : (P.out ++ P.garb).Nodup
  hdisj_sel : (836 :: bits ++ P.selPaths).Disjoint (P.out ++ P.garb)
  hsupp : (836 :: bits ++ P.selPaths ++ P.out ++ P.garb) ⊆ List.range' 2 1608

theorem regs_length (P : Pass) (g : P.Geo) : P.regs.length = 2 ^ P.k := by
  rw [regs, List.length_cons, chunks_length]
  have hp : 1 ≤ 2 ^ P.k := Nat.one_le_pow _ _ (by decide)
  omega

theorem regs_mem_length (P : Pass) (g : P.Geo) : ∀ r ∈ P.regs, r.length = P.m := by
  intro r hr
  rw [regs, List.mem_cons] at hr
  rcases hr with rfl | hr
  · exact g.hout_len
  · exact chunks_mem_length _ _ _ g.hgarb_len r hr

theorem regs_flatten (P : Pass) (g : P.Geo) : P.regs.flatten = P.out ++ P.garb := by
  rw [regs, List.flatten_cons, chunks_flatten _ _ _ g.hgarb_len]

theorem regs_nodup (P : Pass) (g : P.Geo) : P.regs.flatten.Nodup := by
  rw [P.regs_flatten g]; exact g.hregs_nodup

theorem targets_nodup (P : Pass) (g : P.Geo) : P.targets.Nodup :=
  (treeGarbs_nodup_and_mem P.ctrl P.regs (by rw [g.hctrl_len]; exact P.regs_length g) (P.regs_nodup g)).1

theorem targets_mem_iff (P : Pass) (g : P.Geo) (w : Wire) : w ∈ P.targets ↔ w ∈ P.garb := by
  have h := (treeGarbs_nodup_and_mem P.ctrl P.regs (by rw [g.hctrl_len]; exact P.regs_length g)
    (P.regs_nodup g)).2 P.out (chunks (2 ^ P.k - 1) P.m P.garb) rfl
  rw [targets, h.1 w, chunks_flatten _ _ _ g.hgarb_len]

theorem targets_length (P : Pass) (g : P.Geo) : P.targets.length = P.garbLen := by
  rw [targets, treeGarbs_flatten_length P.ctrl P.regs P.m (by rw [g.hctrl_len]; exact P.regs_length g)
    (P.regs_mem_length g), g.hctrl_len, garbLen]

theorem clearData_targets (P : Pass) (g : P.Geo) :
    P.clearData.map MeasuredClear.ClearPort.target = P.targets :=
  passClearData_targets P.k P.sliceSlots P.ctrl P.regs g.hctrl_len (P.regs_length g)
    (fun r hr => (P.regs_mem_length g r hr).trans g.hslots_len.symm)

theorem clearData_length (P : Pass) (g : P.Geo) : P.clearData.length = P.garbLen := by
  have h := congrArg List.length (P.clearData_targets g)
  rw [List.length_map, P.targets_length g] at h
  exact h

theorem sel_layout (P : Pass) (g : P.Geo) : (tableAddressTree P.selBits 0 1).Layout 836 P.selPaths :=
  tableAddressTree_layout _ _ _ _ _ (g.hsel_len.trans g.hpaths_len.symm).le g.hsel_nodup

theorem sel_nodes (P : Pass) (g : P.Geo) : (tableAddressTree P.selBits 0 1).internalNodes = P.selMeas := by
  have h := tableAddressTree_nodes P.selBits 0 1
  rw [g.hsel_len] at h
  rw [selMeas]; omega

theorem selOps_measurements (P : Pass) (g : P.Geo) : lookupMeasurements P.selOps = P.selMeas := by
  rw [selOps, unaryLookupOps_measurements _ _ _ _ (P.sel_layout g), P.sel_nodes g]

theorem selOps_circuit (P : Pass) (read : ConstantBit 524288 → Bool) :
    lookupCircuit read P.selOps =
      tableLookupProgram (passMask P.k P.sliceSlots P.regs read) P.selBits 836 P.selPaths := by
  rw [selOps, unaryLookupOps_circuit]
  unfold tableLookupProgram tableLookup
  apply unaryAction_leaf_congr
  intro l _ q
  exact passLeaf_instantiate P.k P.sliceSlots P.regs read l q

def loadProg (P : Pass) (g : P.Geo) (start : Nat) : Straight 524288 start (start + P.selMeas) :=
  (castFinish (by rw [P.selOps_measurements g]) (lookupProgram 524288 P.selOps start)).append
    (literalProgram P.swap)

def loadSrc (P : Pass) (read : ConstantBit 524288 → Bool) : AdaptiveCircuit :=
  (lookupCircuit read P.selOps).seq (.unitary P.swap .done)

theorem loadProg_run (P : Pass) (g : P.Geo) (read : ConstantBit 524288 → Bool)
    (start : Nat) (h : Fin start → Bool) :
    ((P.loadProg g start).instantiate read h).run = (P.loadSrc read).run := by
  rw [loadProg, append_run_fixed _ _ _ _ _ (fun h' => literalProgram_run P.swap read h'),
    AdaptiveCircuit.run_seq, castFinish_instantiate, lookupProgram_run, ← AdaptiveCircuit.run_seq, loadSrc]

theorem loadProg_tCount (P : Pass) (g : P.Geo) (read : ConstantBit 524288 → Bool)
    (start : Nat) (h : Fin start → Bool) :
    ((P.loadProg g start).instantiate read h).tCount = 7 * (P.selMeas + P.garbLen) := by
  have hsel_t : ((lookupProgram 524288 P.selOps start).instantiate read h).tCount = 7 * P.selMeas := by
    rw [lookupProgram_tCount, P.selOps_circuit,
      tableLookupProgram_tCount _ P.selBits P.selPaths 836 (g.hsel_len.trans g.hpaths_len.symm).le g.hsel_nodup,
      g.hsel_len, selMeas]
  have hsw_t : ShorECDLP.tCount P.swap = 7 * P.garbLen := by
    have hccx := swapTree_ccx P.m P.ctrl P.regs (by rw [g.hctrl_len]; exact P.regs_length g) (P.regs_mem_length g)
    have hhp := swapTree_hp P.ctrl P.regs
    have ht_ccx : ∀ c : Circuit, Classical.HPFree c → ShorECDLP.tCount c = 7 * ccxCount c := by
      intro c; induction c with
      | nil => intro _; rfl
      | cons g' gs ih =>
        intro hhp'
        have hhd := hhp' g' List.mem_cons_self
        have htl : Classical.HPFree gs := fun x hx => hhp' x (List.mem_cons_of_mem _ hx)
        cases g' with
        | X _ => simpa [ShorECDLP.tCount, tCost, ccxCount] using ih htl
        | CX _ _ => simpa [ShorECDLP.tCount, tCost, ccxCount] using ih htl
        | CCX _ _ _ =>
          have hih := ih htl
          simp only [ShorECDLP.tCount] at hih ⊢
          simp only [tCost, ccxCount, List.map_cons, List.sum_cons]
          omega
        | H _ => cases hhd
        | P _ _ _ => cases hhd
    rw [swap, ht_ccx _ hhp, hccx, g.hctrl_len, garbLen]
  rw [loadProg, append_tCount_fixed _ _ _ _ _ (fun h' => literalProgram_tCount P.swap read h'),
    castFinish_instantiate, hsel_t, hsw_t]
  ring

theorem loadProg_residue (P : Pass) (g : P.Geo) (start : Nat) :
    residue (P.loadProg g start) = 0 := by
  rw [loadProg, swap, residue_append, residue_cast, residue_lookup, selOps,
    residue_literal_HPFree _ (swapTree_hp P.ctrl P.regs), Nat.add_zero]
  apply WEXCredit.residue_unary
  intro label root
  unfold leaf passLeaf lookupLeafGates
  generalize (P.regs.zipIdx.flatMap fun p =>
    (P.sliceSlots.map fun f => f (row (2 ^ P.k * label + p.2))).zip p.1) = ports
  induction ports with
  | nil => rfl
  | cons p ps ih => simpa [templateResidue, tCost] using ih

theorem loadProg_slots (P : Pass) (g : P.Geo) (start : Nat) :
    (P.loadProg g start).gateSlots ≤
      (2 ^ P.k * P.m) * (P.selMeas + 1) + 10 * P.selMeas + 3 * P.garbLen := by
  rw [loadProg, Straight.gateSlots_append, castFinish_gateSlots, lookupProgram_slots, literalProgram_slots]
  have hs := unaryLookupOps_slots_le P.leaf (2 ^ P.k * P.m)
    (fun l q => by
      have h := passLeaf_length P.k P.sliceSlots P.regs l q
      rw [P.regs_length g, g.hslots_len] at h; exact h)
    (tableAddressTree P.selBits 0 1) 836 P.selPaths
  rw [P.sel_nodes g] at hs
  have hsw := swapTree_length P.m P.ctrl P.regs (by rw [g.hctrl_len]; exact P.regs_length g) (P.regs_mem_length g)
  rw [g.hctrl_len] at hsw
  rw [selOps, swap, hsw, garbLen]
  omega

theorem loadProg_wellFormed (P : Pass) (g : P.Geo) (start : Nat) :
    (P.loadProg g start).WellFormed := by
  rw [loadProg]
  refine straight_append_wellFormed _ _ ?_ ?_
  · rw [castFinish_wellFormed]
    apply lookupProgram_wellFormed
    rw [selOps]
    apply unaryLookupOps_physical _ _ _ _ (P.sel_layout g)
    intro l c hc gate hgate
    simp only [leaf, passLeaf, lookupLeafGates, List.mem_map] at hgate
    obtain ⟨⟨ref, tgt⟩, hm, rfl⟩ := hgate
    change c ≠ tgt
    obtain ⟨⟨reg, idx⟩, hreg, hzt⟩ := List.mem_flatMap.mp hm
    obtain ⟨i, hi, heq, _⟩ := (mem_zipIdx_iff P.regs 0 reg idx).mp hreg
    have htgt : tgt ∈ P.out ++ P.garb := by
      rw [← P.regs_flatten g]
      exact List.mem_flatten.mpr ⟨reg, heq ▸ List.getElem_mem hi, (List.of_mem_zip hzt).2⟩
    intro he; subst he
    have hc' : c ∈ 836 :: bits ++ P.selPaths := by
      rcases List.mem_cons.mp hc with rfl | hc
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ hc)
    exact List.disjoint_left.mp g.hdisj_sel hc' htgt
  · apply literalProgram_wellFormed
    apply swapTree_wf
    · rw [P.regs_flatten g]
      apply List.disjoint_left.mpr
      intro w hwc hwr
      have hwb : w ∈ bits := by
        rw [bits_eq_append, ← g.hbits]
        exact List.mem_append_left _ (List.mem_append_left _ hwc)
      exact List.disjoint_left.mp g.hdisj_sel (List.mem_cons_of_mem _ (List.mem_append_left _ hwb)) hwr
    · exact P.regs_nodup g

theorem loadProg_support (P : Pass) (g : P.Geo) (start : Nat) :
    straightWires (P.loadProg g start) ⊆ List.range' 2 1608 := by
  rw [loadProg, straightWires_append, straightWires_castFinish, lookupProgram_support, literalProgram_support]
  apply List.append_subset.mpr
  constructor
  · have hl : ∀ op ∈ P.selOps, lookupOpWires op ⊆ List.range' 2 1608 := by
      rw [selOps]
      apply unaryLookupOps_support
      · exact g.hsupp (by simp)
      · intro w hw; exact g.hsupp (by simp [hw])
      · intro w hw
        have hb := (tableAddressTree_mem_index P.selBits 0 1 w).mp hw
        have hwb : w ∈ bits := by
          rw [bits_eq_append, ← g.hbits]
          exact List.mem_append_left _ (List.mem_append_right _ hb)
        exact g.hsupp (by simp [hwb])
      · intro l q hq
        apply lookupLeafGates_support _ _ _ hq
        intro port hp
        obtain ⟨⟨reg, idx⟩, hreg, hzt⟩ := List.mem_flatMap.mp hp
        obtain ⟨i, hi, heq, _⟩ := (mem_zipIdx_iff P.regs 0 reg idx).mp hreg
        have htgt : port.2 ∈ P.out ++ P.garb := by
          rw [← P.regs_flatten g]
          exact List.mem_flatten.mpr ⟨reg, heq ▸ List.getElem_mem hi, (List.of_mem_zip hzt).2⟩
        rcases List.mem_append.mp htgt with h | h <;> exact g.hsupp (by simp [h])
    intro w hw
    obtain ⟨op, hop, hw⟩ := List.mem_flatMap.mp hw
    exact hl op hop hw
  · intro w hw
    rcases swapTree_wires P.ctrl P.regs w hw with h | h
    · have hwb : w ∈ bits := by
        rw [bits_eq_append, ← g.hbits]
        exact List.mem_append_left _ (List.mem_append_left _ h)
      exact g.hsupp (by simp [hwb])
    · rw [P.regs_flatten g] at h
      rcases List.mem_append.mp h with h | h <;> exact g.hsupp (by simp [h])

theorem loadProg_safe836 (P : Pass) (g : P.Geo) (start : Nat) :
    RootPass.safeProgram 836 (P.loadProg g start) := by
  rw [loadProg, RootPass.safeProgram_append, RootPass.safeProgram_cast]
  constructor
  · apply RootPass.lookupProgram_safe
    rw [selOps]
    obtain ⟨hb, hp⟩ := RootPass.layout_avoids (P.sel_layout g)
    apply RootPass.unaryOps_safe 836 P.leaf _ _ _ _ hb hp
    intro l c gate hg
    simp only [leaf, passLeaf, lookupLeafGates, List.mem_map] at hg
    obtain ⟨⟨ref, tgt⟩, hm, rfl⟩ := hg
    change tgt ≠ 836
    obtain ⟨⟨reg, idx⟩, hreg, hzt⟩ := List.mem_flatMap.mp hm
    obtain ⟨i, hi, heq, _⟩ := (mem_zipIdx_iff P.regs 0 reg idx).mp hreg
    have htgt : tgt ∈ P.out ++ P.garb := by
      rw [← P.regs_flatten g]
      exact List.mem_flatten.mpr ⟨reg, heq ▸ List.getElem_mem hi, (List.of_mem_zip hzt).2⟩
    intro he; subst he
    exact List.disjoint_left.mp g.hdisj_sel List.mem_cons_self htgt
  · apply RootPass.safeProgram_of_not_mem
    rw [literalProgram_support]
    intro h
    rcases swapTree_wires P.ctrl P.regs 836 h with hc | hr
    · have h836 : (836 : Wire) ∈ addrBits := by rw [← g.hbits]; exact List.mem_append_left _ hc
      have : (836 : Wire) ∉ addrBits := by decide
      exact this h836
    · rw [P.regs_flatten g] at hr
      exact List.disjoint_left.mp g.hdisj_sel List.mem_cons_self hr

theorem loadProg_hits836 (P : Pass) (g : P.Geo) (start : Nat) :
    RootPass.literalHits 836 (P.loadProg g start) = 1 := by
  rw [loadProg, RootPass.literalHits_append, RootPass.literalHits_cast,
    RootPass.literalHits_lookupProgram]
  have hsw : RootPass.literalHits 836 (literalProgram (n := 524288) (s := start + P.selMeas) P.swap) = 0 := by
    apply RootPass.literalHits_zero_of_not_mem
    rw [literalProgram_support]
    intro h
    rcases swapTree_wires P.ctrl P.regs 836 h with hc | hr
    · have h836 : (836 : Wire) ∈ addrBits := by rw [← g.hbits]; exact List.mem_append_left _ hc
      have : (836 : Wire) ∉ addrBits := by decide
      exact this h836
    · rw [P.regs_flatten g] at hr
      exact List.disjoint_left.mp g.hdisj_sel List.mem_cons_self hr
  rw [hsw, Nat.add_zero, selOps]
  apply RootPass.unaryOps_root_hits 836 P.leaf _ _ (P.sel_layout g)
  · rw [P.sel_nodes g, selMeas]
    have hpow : 2 ≤ 2 ^ (19 - P.k) := by
      have : 1 ≤ 19 - P.k := by have := g.hk; omega
      exact Nat.le_self_pow (by omega) 2
    omega
  · intro l c
    simp [leaf, passLeaf, lookupLeafGates, List.map_map, Function.comp_def, RootPass.templateHits]

def afterSwap (P : Pass) (read : ConstantBit 524288 → Bool) (s : BasisState) : BasisState :=
  Classical.run P.swap (tableLookupState (passMask P.k P.sliceSlots P.regs read) P.selBits 836 s)

def afterReset (P : Pass) (read : ConstantBit 524288 → Bool) (s : BasisState) : BasisState :=
  clearRegister P.targets (P.afterSwap read s)

theorem loadSrc_coherent (P : Pass) (g : P.Geo) (read : ConstantBit 524288 → Bool) :
    CoherentlyImplementsOn (P.loadSrc read)
      (Finsupp.lmapDomain ℂ ℂ (P.afterSwap read)) (Clean P.selPaths) := by
  have hsel : CoherentlyImplementsOn (lookupCircuit read P.selOps)
      (Finsupp.lmapDomain ℂ ℂ (tableLookupState (passMask P.k P.sliceSlots P.regs read) P.selBits 836))
      (Clean P.selPaths) := by
    rw [P.selOps_circuit]
    apply tableLookupProgram_coherent_state _ _ _ _ (g.hsel_len.trans g.hpaths_len.symm).le g.hsel_nodup
      (fun l => passMask_nodup P.k P.sliceSlots P.regs read l (P.regs_nodup g))
    intro l w hw hm
    have hmr : w ∈ P.out ++ P.garb := by rw [← P.regs_flatten g]; exact passMask_sub _ _ _ _ _ hm
    have hw' : w ∈ 836 :: bits ++ P.selPaths := by
      simp only [List.mem_cons, List.mem_append] at hw ⊢
      rcases hw with (rfl | hw) | hw
      · exact Or.inl (Or.inl rfl)
      · exact Or.inl (Or.inr (by rw [bits_eq_append, ← g.hbits]; exact List.mem_append_left _ (List.mem_append_right _ hw)))
      · exact Or.inr hw
    exact List.disjoint_left.mp g.hdisj_sel hw' hmr
  have hcomb := hsel.seq (CoherentlyImplementsOn.unitary P.swap (fun _ => True)) (fun _ _ _ _ => trivial)
  refine hcomb.congrIdeal (fun s _ => ?_)
  rw [LinearMap.comp_apply, First18.lmap_ket, First18.lmap_ket, swap,
    run_ket_agrees_classical _ _ (swapTree_hp P.ctrl P.regs)]
  rfl

theorem afterSwap_facts (P : Pass) (g : P.Geo) (read : ConstantBit 524288 → Bool)
    (s : BasisState) (h836 : s 836 = true) (hclean : Clean (P.out ++ P.garb) s) :
    (∀ w, w ∉ P.out → w ∉ P.garb → P.afterSwap read s w = s w) ∧
    wireValues P.out (P.afterSwap read s) = sliceWord P.sliceSlots read (tableAddressValue addrBits s) ∧
    (∀ q ∈ P.clearData, (P.afterSwap read s) q.target =
      (true && decide (read (q.ref (tableAddressValue addrBits s)) = q.value))) := by
  let s0 := tableLookupState (passMask P.k P.sliceSlots P.regs read) P.selBits 836 s
  have h0_fr : ∀ w, w ∉ P.out → w ∉ P.garb → s0 w = s w := by
    intro w h1 h2
    apply tableXorState_outside
    intro hm
    have hmr := passMask_sub P.k P.sliceSlots P.regs read _ hm
    rw [P.regs_flatten g] at hmr
    rcases List.mem_append.mp hmr with h | h
    · exact h1 h
    · exact h2 h
  have h0_ctrl : tableAddressValue P.ctrl s0 = tableAddressValue P.ctrl s := by
    apply tableAddressValue_congr
    intro w hw
    have hwb : w ∈ bits := by rw [bits_eq_append, ← g.hbits]; exact List.mem_append_left _ (List.mem_append_left _ hw)
    have hn : w ∉ P.out ++ P.garb := List.disjoint_left.mp g.hdisj_sel (by simp [hwb])
    exact h0_fr w (fun h => hn (List.mem_append_left _ h)) (fun h => hn (List.mem_append_right _ h))
  have h0_init : ∀ (j : Nat) (hj : j < P.regs.length),
      wireValues (P.regs[j]'hj) s0 = sliceWord P.sliceSlots read (2 ^ P.ctrl.length * tableAddressValue P.selBits s + j) := by
    rw [g.hctrl_len]
    exact passMask_read P.k P.sliceSlots P.regs read P.selBits (P.regs_nodup g)
      (fun r hr => (P.regs_mem_length g r hr).trans g.hslots_len.symm)
      s h836 (by rw [P.regs_flatten g]; exact hclean)
  have hctrl_disj : P.ctrl.Disjoint P.regs.flatten := by
    rw [P.regs_flatten g]
    apply List.disjoint_left.mpr
    intro w hw hmr
    have hwb : w ∈ bits := by rw [bits_eq_append, ← g.hbits]; exact List.mem_append_left _ (List.mem_append_left _ hw)
    exact List.disjoint_left.mp g.hdisj_sel (by simp [hwb]) hmr
  obtain ⟨hfr, h0, hgarb⟩ := swapTree_run P.m P.ctrl P.regs (sliceWord P.sliceSlots read)
    (tableAddressValue P.selBits s) (by rw [g.hctrl_len]; exact P.regs_length g)
    (P.regs_mem_length g) hctrl_disj (P.regs_nodup g) s0 h0_init
  have haddr : tableAddressValue P.ctrl s0 + 2 ^ P.ctrl.length * tableAddressValue P.selBits s =
      tableAddressValue addrBits s := by
    rw [h0_ctrl, ← tableAddressValue_append, g.hbits]
  rw [haddr] at h0 hgarb
  refine ⟨fun w h1 h2 => ?_, ?_, ?_⟩
  · have hnw : w ∉ P.regs.flatten := by rw [P.regs_flatten g, List.mem_append]; tauto
    exact (hfr w hnw).trans (h0_fr w h1 h2)
  · have hpos : 0 < P.regs.length := by rw [P.regs_length g]; exact pow_pos (by decide) _
    exact h0 hpos
  · apply passClearData_loaded P.k P.sliceSlots P.ctrl P.regs read
    rw [← g.hctrl_len]
    exact hgarb

theorem afterReset_facts (P : Pass) (g : P.Geo) (read : ConstantBit 524288 → Bool)
    (s : BasisState) (h836 : s 836 = true) (hclean : Clean (P.out ++ P.garb) s) :
    (∀ w, w ∉ P.out → P.afterReset read s w = s w) ∧
    wireValues P.out (P.afterReset read s) = sliceWord P.sliceSlots read (tableAddressValue addrBits s) := by
  obtain ⟨hfr, hout, _⟩ := P.afterSwap_facts g read s h836 hclean
  have hout_disj : P.out.Disjoint P.targets :=
    ((treeGarbs_nodup_and_mem P.ctrl P.regs (by rw [g.hctrl_len]; exact P.regs_length g)
      (P.regs_nodup g)).2 P.out (chunks (2 ^ P.k - 1) P.m P.garb) rfl).2
  refine ⟨fun w hw => ?_, ?_⟩
  · by_cases hg : w ∈ P.garb
    · have ht : w ∈ P.targets := (P.targets_mem_iff g w).mpr hg
      rw [afterReset, clearRegister_clean _ _ _ ht]
      exact (hclean w (List.mem_append_right _ hg)).symm
    · have ht : w ∉ P.targets := fun h => hg ((P.targets_mem_iff g w).mp h)
      rw [afterReset, MeasuredClear.clearRegister_frame _ _ _ ht]
      exact hfr w hw hg
  · rw [afterReset]
    have hcongr : wireValues P.out (clearRegister P.targets (P.afterSwap read s)) =
        wireValues P.out (P.afterSwap read s) :=
      List.map_congr_left (fun w hw => MeasuredClear.clearRegister_frame _ _ _
        (List.disjoint_left.mp hout_disj hw))
    rw [hcongr, hout]

def stepProg (P : Pass) (g : P.Geo) {R : Nat}
    (next : (c : Nat) → List (Fin c) → Straight 524288 c (c + R))
    (start : Nat) (refs : List (Fin start)) :
    Straight 524288 start (start + (P.selMeas + (P.garbLen + R))) :=
  castFinish (Nat.add_assoc start P.selMeas (P.garbLen + R))
    ((P.loadProg g start).append
      (castFinish (by rw [P.targets_length g]; exact Nat.add_assoc (start + P.selMeas) P.garbLen R)
        (MeasuredClear.measureThen (R := R) next P.targets (start + P.selMeas)
          (refs.map (Fin.castLE (Nat.le_add_right _ _))))))

def stepSrc (P : Pass) (read : ConstantBit 524288 → Bool)
    (nextSrc : List Bool → AdaptiveCircuit) (prior : List Bool) : AdaptiveCircuit :=
  (P.loadSrc read).seq (measureResetThen P.targets (fun o => nextSrc (prior ++ o)))

theorem stepProg_run (P : Pass) (g : P.Geo) {R : Nat}
    (next : (c : Nat) → List (Fin c) → Straight 524288 c (c + R))
    (nextSrc : List Bool → AdaptiveCircuit) (read : ConstantBit 524288 → Bool)
    (hn : ∀ c rs h, ((next c rs).instantiate read h).run = (nextSrc (rs.map h)).run)
    (start : Nat) (refs : List (Fin start)) (h : Fin start → Bool) :
    ((P.stepProg g next start refs).instantiate read h).run =
      (P.stepSrc read nextSrc (refs.map h)).run := by
  rw [stepProg, castFinish_instantiate,
    MeasuredClear.append_run_prefix _ _ read (Nat.le_refl start) h h rfl
      (measureResetThen P.targets (fun o => nextSrc (refs.map h ++ o))),
    AdaptiveCircuit.run_seq, P.loadProg_run g, ← AdaptiveCircuit.run_seq, stepSrc]
  intro h' hh'
  rw [castFinish_instantiate, MeasuredClear.measureThen_run _ nextSrc read hn, List.map_map]
  congr 2; ext o; congr 2; rw [← hh']; rfl

theorem stepProg_tCount (P : Pass) (g : P.Geo) {R t : Nat}
    (next : (c : Nat) → List (Fin c) → Straight 524288 c (c + R))
    (read : ConstantBit 524288 → Bool)
    (hn : ∀ c rs h, ((next c rs).instantiate read h).tCount = t)
    (start : Nat) (refs : List (Fin start)) (h : Fin start → Bool) :
    ((P.stepProg g next start refs).instantiate read h).tCount =
      7 * (P.selMeas + P.garbLen) + t := by
  rw [stepProg, castFinish_instantiate,
    append_tCount_fixed _ _ _ _ _ (fun h' => by
      rw [castFinish_instantiate, MeasuredClear.measureThen_tCount _ read hn]),
    P.loadProg_tCount g]

theorem stepProg_residue (P : Pass) (g : P.Geo) {R : Nat}
    (next : (c : Nat) → List (Fin c) → Straight 524288 c (c + R))
    (hn : ∀ c rs, residue (next c rs) = 0)
    (start : Nat) (refs : List (Fin start)) :
    residue (P.stepProg g next start refs) = 0 := by
  rw [stepProg, residue_cast, residue_append, P.loadProg_residue g, residue_cast,
    MeasuredClear.measureThen_residue _ hn]

theorem stepProg_slots (P : Pass) (g : P.Geo) {R B : Nat}
    (next : (c : Nat) → List (Fin c) → Straight 524288 c (c + R))
    (hn : ∀ c rs, (next c rs).gateSlots ≤ B)
    (start : Nat) (refs : List (Fin start)) :
    (P.stepProg g next start refs).gateSlots ≤
      (2 ^ P.k * P.m) * (P.selMeas + 1) + 10 * P.selMeas + 3 * P.garbLen + B := by
  rw [stepProg, castFinish_gateSlots, Straight.gateSlots_append, castFinish_gateSlots]
  have h1 := P.loadProg_slots g start
  have h2 : (MeasuredClear.measureThen (R := R) next P.targets (start + P.selMeas)
      (refs.map (Fin.castLE (Nat.le_add_right _ _)))).gateSlots ≤ B := by
    have hgen : ∀ (ws : List Wire) (st : Nat) (rs : List (Fin st)),
        (MeasuredClear.measureThen (R := R) next ws st rs).gateSlots ≤ B := by
      intro ws; induction ws with
      | nil => intro st rs; exact hn st rs
      | cons w ws ih =>
        intro st rs
        simp only [MeasuredClear.measureThen, castFinish_gateSlots, Straight.gateSlots]
        exact ih _ _
    exact hgen _ _ _
  omega

theorem stepProg_wellFormed (P : Pass) (g : P.Geo) {R : Nat}
    (next : (c : Nat) → List (Fin c) → Straight 524288 c (c + R))
    (hn : ∀ c rs, (next c rs).WellFormed)
    (start : Nat) (refs : List (Fin start)) :
    (P.stepProg g next start refs).WellFormed := by
  rw [stepProg, castFinish_wellFormed]
  refine straight_append_wellFormed _ _ (P.loadProg_wellFormed g start) ?_
  rw [castFinish_wellFormed]
  exact MeasuredClear.measureThen_wellFormed next hn _ _ _

theorem stepProg_support (P : Pass) (g : P.Geo) {R : Nat}
    (next : (c : Nat) → List (Fin c) → Straight 524288 c (c + R))
    (hn : ∀ c rs, straightWires (next c rs) ⊆ List.range' 2 1608)
    (start : Nat) (refs : List (Fin start)) :
    straightWires (P.stepProg g next start refs) ⊆ List.range' 2 1608 := by
  rw [stepProg, straightWires_castFinish, straightWires_append, straightWires_castFinish]
  refine List.append_subset.mpr ⟨P.loadProg_support g start, ?_⟩
  rw [RootPass.straightWires_eq_naive]
  apply MeasuredClear.measureThen_within next (List.range' 2 1608)
  · intro c rs; rw [← RootPass.straightWires_eq_naive]; exact hn c rs
  · intro w hw
    have hg := (P.targets_mem_iff g w).mp hw
    exact g.hsupp (by simp [hg])

theorem stepProg_safe836 (P : Pass) (g : P.Geo) {R : Nat}
    (next : (c : Nat) → List (Fin c) → Straight 524288 c (c + R))
    (hn : ∀ c rs, RootPass.safeProgram 836 (next c rs))
    (start : Nat) (refs : List (Fin start)) :
    RootPass.safeProgram 836 (P.stepProg g next start refs) := by
  rw [stepProg, RootPass.safeProgram_cast, RootPass.safeProgram_append, RootPass.safeProgram_cast]
  refine ⟨P.loadProg_safe836 g start, RootPass.measureThen_safe 836 next hn _ _ _ ?_⟩
  intro w hw he
  subst he
  have hg := (P.targets_mem_iff g 836).mp hw
  exact List.disjoint_left.mp g.hdisj_sel List.mem_cons_self (List.mem_append_right _ hg)

theorem stepProg_hits836 (P : Pass) (g : P.Geo) {R hCount : Nat}
    (next : (c : Nat) → List (Fin c) → Straight 524288 c (c + R))
    (hn : ∀ c rs, RootPass.literalHits 836 (next c rs) = hCount)
    (start : Nat) (refs : List (Fin start)) :
    RootPass.literalHits 836 (P.stepProg g next start refs) = 1 + hCount := by
  rw [stepProg, RootPass.literalHits_cast, RootPass.literalHits_append, P.loadProg_hits836 g,
    RootPass.literalHits_cast, RootPass.literalHits_measureThen 836 hCount next hn]

theorem stepSrc_sim (P : Pass) (g : P.Geo) (read : ConstantBit 524288 → Bool)
    (nextSrc : List Bool → AdaptiveCircuit) (prior : List Bool)
    (V : BasisState → Prop) (inState fNext : BasisState → BasisState)
    (phasePrior : BasisState → ℂ)
    (hV_pre : ∀ s, V s → Clean P.selPaths (inState s) ∧ (inState s) 836 = true ∧ Clean (P.out ++ P.garb) (inState s))
    (hNext : ∀ o, o.length = P.targets.length →
      ∃ cs : List ℂ,
        List.Forall₂ (fun b c => ∀ s, V s →
          b.kraus (ket (P.afterReset read (inState s))) =
            c • (phasePrior s *
              registerXPhase P.targets o (P.afterSwap read (inState s))) • ket (fNext s))
          (nextSrc (prior ++ o)).run cs ∧
        (cs.map Complex.normSq).sum = 1) :
    ∃ cs : List ℂ,
      List.Forall₂ (fun b c => ∀ s, V s →
        b.kraus (ket (inState s)) = c • (phasePrior s) • ket (fNext s))
        (P.stepSrc read nextSrc prior).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  obtain ⟨cL, aL, mL⟩ := P.loadSrc_coherent g read
  have hM := MeasuredClear.measureResetThen_sim P.targets (fun o => nextSrc (prior ++ o))
    (fun o b c => ∀ s, V s → b.kraus (ket (P.afterReset read (inState s))) =
      c • (phasePrior s *
        registerXPhase P.targets o (P.afterSwap read (inState s))) • ket (fNext s))
    (fun b c => ∀ s, V s → b.kraus (ket (P.afterSwap read (inState s))) =
      c • (phasePrior s) • ket (fNext s))
    hNext
    (by
      intro o ho b c hb s hs
      have hx := xResetRegisterKraus_ket P.targets o (P.afterSwap read (inState s))
        ho (P.targets_nodup g)
      change b.kraus (xResetRegisterKraus P.targets o (ket (P.afterSwap read (inState s)))) = _
      rw [hx, map_smul]
      change registerXResetCoeff P.targets o (P.afterSwap read (inState s)) •
        b.kraus (ket (P.afterReset read (inState s))) = _
      rw [hb s hs]
      have hsq := MeasuredClear.registerXPhase_square P.targets o (P.afterSwap read (inState s))
      rw [registerXResetCoeff_eq_magnitude_mul_phase _ _ _ ho, smul_smul, smul_smul, smul_smul]
      congr 1
      calc
        _ = registerXResetMagnitude P.targets.length * c * phasePrior s *
              (registerXPhase P.targets o (P.afterSwap read (inState s)) *
                registerXPhase P.targets o (P.afterSwap read (inState s))) := by ring
        _ = registerXResetMagnitude P.targets.length * c * phasePrior s := by rw [hsq, mul_one])
  obtain ⟨cM, aM, mM⟩ := hM
  refine ⟨coherentSeqCoefficients cL cM, ?_, by rw [WEX.simulationCoefficients_mass, mL, mM]; norm_num⟩
  rw [stepSrc, AdaptiveCircuit.run_seq]
  apply WEX.simulationAligned_seq aL aM
  intro bL kL bM kM hbL hbM s hs
  change bM.kraus (bL.kraus (ket (inState s))) = _
  rw [hbL (inState s) (hV_pre s hs).1, First18.lmap_ket, map_smul, hbM s hs, smul_smul, smul_smul]

end Pass

/-! ### Part 4: Five-pass instantiation `((2, 392), (7, 9), (4, 73), (5, 34), (8, 4))` (wires `0, 1` reserved) -/

def anc17 : List Wire :=
  List.range' 2 261 ++ List.range' 536 44 ++ List.range' 837 18 ++ List.range' 875 735

def anc15 : List Wire := anc17 ++ [534, 535]
def anc14 : List Wire := anc17 ++ [533, 534, 535]
def anc12 : List Wire := anc17 ++ [531, 532, 533, 534, 535]
def anc11 : List Wire := anc17 ++ [530, 531, 532, 533, 534, 535]

theorem mem_anc17 {w : Wire} : w ∈ anc17 ↔
    (2 ≤ w ∧ w < 263) ∨ (536 ≤ w ∧ w < 580) ∨ (837 ≤ w ∧ w < 855) ∨ (875 ≤ w ∧ w < 1610) := by
  simp only [anc17, List.mem_append, List.mem_range'_1]
  (try dsimp only [Wire] at *); omega

theorem anc17_length : anc17.length = 1058 := by simp [anc17]

theorem anc17_nodup : anc17.Nodup := by
  have h1 : (List.range' 2 261 ++ List.range' 536 44).Nodup :=
    List.nodup_append.mpr ⟨List.nodup_range', List.nodup_range', fun a ha b hb => by
      simp only [List.mem_range'_1] at ha hb; omega⟩
  have h2 : (List.range' 2 261 ++ List.range' 536 44 ++ List.range' 837 18).Nodup :=
    List.nodup_append.mpr ⟨h1, List.nodup_range', fun a ha b hb => by
      simp only [List.mem_append, List.mem_range'_1] at ha hb; omega⟩
  exact List.nodup_append.mpr ⟨h2, List.nodup_range', fun a ha b hb => by
    simp only [List.mem_append, List.mem_range'_1] at ha hb
    (try dsimp only [Wire] at *); omega⟩

theorem anc17_disj_xy : anc17.Disjoint xyWires := by
  apply List.disjoint_left.mpr
  intro w ha hp
  have h1 := mem_anc17.mp ha
  have h2 := mem_xyWires.mp hp
  (try dsimp only [Wire] at *); omega

theorem anc15_nodup : anc15.Nodup :=
  List.nodup_append.mpr ⟨anc17_nodup, by decide, fun a ha b hb => by
    have h1 := mem_anc17.mp ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    (try dsimp only [Wire] at *); omega⟩

theorem anc14_nodup : anc14.Nodup :=
  List.nodup_append.mpr ⟨anc17_nodup, by decide, fun a ha b hb => by
    have h1 := mem_anc17.mp ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    (try dsimp only [Wire] at *); omega⟩

theorem anc12_nodup : anc12.Nodup :=
  List.nodup_append.mpr ⟨anc17_nodup, by decide, fun a ha b hb => by
    have h1 := mem_anc17.mp ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    (try dsimp only [Wire] at *); omega⟩

theorem anc11_nodup : anc11.Nodup :=
  List.nodup_append.mpr ⟨anc17_nodup, by decide, fun a ha b hb => by
    have h1 := mem_anc17.mp ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    (try dsimp only [Wire] at *); omega⟩

theorem mem_anc15 {w : Wire} : w ∈ anc15 ↔
    (2 ≤ w ∧ w < 263) ∨ (534 ≤ w ∧ w < 580) ∨ (837 ≤ w ∧ w < 855) ∨ (875 ≤ w ∧ w < 1610) := by
  simp only [anc15, List.mem_append, mem_anc17, List.mem_cons, List.not_mem_nil, or_false]
  (try dsimp only [Wire] at *); omega

theorem mem_anc14 {w : Wire} : w ∈ anc14 ↔
    (2 ≤ w ∧ w < 263) ∨ (533 ≤ w ∧ w < 580) ∨ (837 ≤ w ∧ w < 855) ∨ (875 ≤ w ∧ w < 1610) := by
  simp only [anc14, List.mem_append, mem_anc17, List.mem_cons, List.not_mem_nil, or_false]
  (try dsimp only [Wire] at *); omega

theorem mem_anc12 {w : Wire} : w ∈ anc12 ↔
    (2 ≤ w ∧ w < 263) ∨ (531 ≤ w ∧ w < 580) ∨ (837 ≤ w ∧ w < 855) ∨ (875 ≤ w ∧ w < 1610) := by
  simp only [anc12, List.mem_append, mem_anc17, List.mem_cons, List.not_mem_nil, or_false]
  (try dsimp only [Wire] at *); omega

theorem mem_anc11 {w : Wire} : w ∈ anc11 ↔
    (2 ≤ w ∧ w < 263) ∨ (530 ≤ w ∧ w < 580) ∨ (837 ≤ w ∧ w < 855) ∨ (875 ≤ w ∧ w < 1610) := by
  simp only [anc11, List.mem_append, mem_anc17, List.mem_cons, List.not_mem_nil, or_false]
  (try dsimp only [Wire] at *); omega

def p1 : List Wire := xyWires.take 392
def rem1 : List Wire := xyWires.drop 392
def p2 : List Wire := rem1.take 9
def rem2 : List Wire := rem1.drop 9
def p3 : List Wire := rem2.take 73
def rem3 : List Wire := rem2.drop 73
def p4 : List Wire := rem3.take 34
def rem4 : List Wire := rem3.drop 34
def p5 : List Wire := rem4

def s1 : List (Fin 524288 → ConstantBit 524288) := slots.take 392
def s2 : List (Fin 524288 → ConstantBit 524288) := (slots.drop 392).take 9
def s3 : List (Fin 524288 → ConstantBit 524288) := (slots.drop 401).take 73
def s4 : List (Fin 524288 → ConstantBit 524288) := (slots.drop 474).take 34
def s5 : List (Fin 524288 → ConstantBit 524288) := slots.drop 508

theorem xy_split : p1 ++ p2 ++ p3 ++ p4 ++ p5 = xyWires := by
  simp only [p1, p2, p3, p4, p5, rem1, rem2, rem3, rem4, List.append_assoc, List.take_append_drop]

theorem slots_split : s1 ++ s2 ++ s3 ++ s4 ++ s5 = slots := by
  have h1 : slots.drop 401 = (slots.drop 392).drop 9 := by rw [List.drop_drop]
  have h2 : slots.drop 474 = (slots.drop 401).drop 73 := by rw [List.drop_drop]
  have h3 : slots.drop 508 = (slots.drop 474).drop 34 := by rw [List.drop_drop]
  simp only [s1, s2, s3, s4, s5, h3, h2, h1, List.append_assoc, List.take_append_drop]

theorem p1_len : p1.length = 392 := by rw [p1, List.length_take, xyWires_length]; decide
theorem rem1_len : rem1.length = 120 := by rw [rem1, List.length_drop, xyWires_length]
theorem p2_len : p2.length = 9 := by rw [p2, List.length_take, rem1_len]; decide
theorem rem2_len : rem2.length = 111 := by rw [rem2, List.length_drop, rem1_len]
theorem p3_len : p3.length = 73 := by rw [p3, List.length_take, rem2_len]; decide
theorem rem3_len : rem3.length = 38 := by rw [rem3, List.length_drop, rem2_len]
theorem p4_len : p4.length = 34 := by rw [p4, List.length_take, rem3_len]; decide
theorem rem4_len : rem4.length = 4 := by rw [rem4, List.length_drop, rem3_len]
theorem p5_len : p5.length = 4 := rem4_len

theorem s1_len : s1.length = 392 := by rw [s1, List.length_take, slots_length]; decide
theorem s2_len : s2.length = 9 := by rw [s2, List.length_take, List.length_drop, slots_length]; decide
theorem s3_len : s3.length = 73 := by rw [s3, List.length_take, List.length_drop, slots_length]; decide
theorem s4_len : s4.length = 34 := by rw [s4, List.length_take, List.length_drop, slots_length]; decide
theorem s5_len : s5.length = 4 := by rw [s5, List.length_drop, slots_length]

theorem p_mem_xy : ∀ w, (w ∈ p1 ∨ w ∈ p2 ∨ w ∈ p3 ∨ w ∈ p4 ∨ w ∈ p5) ↔ w ∈ xyWires := by
  intro w; rw [← xy_split]; simp only [List.mem_append, or_assoc]

theorem p1_rem1_eq : p1 ++ rem1 = xyWires := List.take_append_drop 392 xyWires
theorem p2_rem2_eq : p2 ++ rem2 = rem1 := List.take_append_drop 9 rem1
theorem p3_rem3_eq : p3 ++ rem3 = rem2 := List.take_append_drop 73 rem2
theorem p4_p5_eq : p4 ++ p5 = rem3 := List.take_append_drop 34 rem3

theorem p1_nodup : p1.Nodup :=
  (List.nodup_append.mp (by rw [p1_rem1_eq]; exact xyWires_nodup)).1
theorem rem1_nodup : rem1.Nodup :=
  (List.nodup_append.mp (by rw [p1_rem1_eq]; exact xyWires_nodup)).2.1
theorem p1_disj_rem1 : p1.Disjoint rem1 :=
  List.disjoint_left.mpr (fun a ha hb =>
    (List.nodup_append.mp (by rw [p1_rem1_eq]; exact xyWires_nodup)).2.2 a ha a hb rfl)

theorem p2_nodup : p2.Nodup :=
  (List.nodup_append.mp (by rw [p2_rem2_eq]; exact rem1_nodup)).1
theorem rem2_nodup : rem2.Nodup :=
  (List.nodup_append.mp (by rw [p2_rem2_eq]; exact rem1_nodup)).2.1
theorem p2_disj_rem2 : p2.Disjoint rem2 :=
  List.disjoint_left.mpr (fun a ha hb =>
    (List.nodup_append.mp (by rw [p2_rem2_eq]; exact rem1_nodup)).2.2 a ha a hb rfl)

theorem p3_nodup : p3.Nodup :=
  (List.nodup_append.mp (by rw [p3_rem3_eq]; exact rem2_nodup)).1
theorem rem3_nodup : rem3.Nodup :=
  (List.nodup_append.mp (by rw [p3_rem3_eq]; exact rem2_nodup)).2.1
theorem p3_disj_rem3 : p3.Disjoint rem3 :=
  List.disjoint_left.mpr (fun a ha hb =>
    (List.nodup_append.mp (by rw [p3_rem3_eq]; exact rem2_nodup)).2.2 a ha a hb rfl)

theorem p4_nodup : p4.Nodup :=
  (List.nodup_append.mp (by rw [p4_p5_eq]; exact rem3_nodup)).1
theorem p5_nodup : p5.Nodup :=
  (List.nodup_append.mp (by rw [p4_p5_eq]; exact rem3_nodup)).2.1
theorem p4_disj_p5 : p4.Disjoint p5 :=
  List.disjoint_left.mpr (fun a ha hb =>
    (List.nodup_append.mp (by rw [p4_p5_eq]; exact rem3_nodup)).2.2 a ha a hb rfl)

theorem p1_sub_xy {w} (h : w ∈ p1) : w ∈ xyWires := List.mem_of_mem_take h
theorem rem1_sub_xy {w} (h : w ∈ rem1) : w ∈ xyWires := List.mem_of_mem_drop h
theorem p2_sub_rem1 {w} (h : w ∈ p2) : w ∈ rem1 := List.mem_of_mem_take h
theorem rem2_sub_rem1 {w} (h : w ∈ rem2) : w ∈ rem1 := List.mem_of_mem_drop h
theorem p3_sub_rem2 {w} (h : w ∈ p3) : w ∈ rem2 := List.mem_of_mem_take h
theorem rem3_sub_rem2 {w} (h : w ∈ rem3) : w ∈ rem2 := List.mem_of_mem_drop h
theorem p4_sub_rem3 {w} (h : w ∈ p4) : w ∈ rem3 := List.mem_of_mem_take h
theorem p5_sub_rem3 {w} (h : w ∈ p5) : w ∈ rem3 := List.mem_of_mem_drop h

def pass1 : Pass :=
  ⟨2, 392, s1, addrBits.take 2, addrBits.drop 2, List.range' 519 17, p1, (anc17 ++ rem1).take 1176⟩

def pass2 : Pass :=
  ⟨7, 9, s2, addrBits.take 7, addrBits.drop 7, List.range' 519 12, p2, (anc12 ++ rem2).take 1143⟩

def pass3 : Pass :=
  ⟨4, 73, s3, addrBits.take 4, addrBits.drop 4, List.range' 519 15, p3, (anc15 ++ rem3).take 1095⟩

def pass4 : Pass :=
  ⟨5, 34, s4, addrBits.take 5, addrBits.drop 5, List.range' 519 14, p4, anc14.take 1054⟩

def pass5 : Pass :=
  ⟨8, 4, s5, addrBits.take 8, addrBits.drop 8, List.range' 519 11, p5, anc11.take 1020⟩

theorem pass1_geo : pass1.Geo where
  hk := by decide
  hctrl_len := by decide
  hsel_len := by decide
  hpaths_len := by decide
  hbits := List.take_append_drop 2 addrBits
  hslots_len := s1_len
  hout_len := p1_len
  hgarb_len := by simp [pass1, anc17_length, rem1_len]
  hsel_nodup := by decide
  hregs_nodup := by
    change (p1 ++ (anc17 ++ rem1).take 1176).Nodup
    have hfull : (p1 ++ (anc17 ++ rem1)).Nodup := by
      refine List.nodup_append.mpr ⟨p1_nodup, List.nodup_append.mpr ⟨anc17_nodup, rem1_nodup, ?_⟩, ?_⟩
      · intro a ha b hb he; subst he
        exact List.disjoint_left.mp anc17_disj_xy ha (rem1_sub_xy hb)
      · intro a ha b hb he; subst he
        rcases List.mem_append.mp hb with hb | hb
        · exact List.disjoint_left.mp anc17_disj_xy hb (p1_sub_xy ha)
        · exact List.disjoint_left.mp p1_disj_rem1 ha hb
    exact hfull.sublist (List.Sublist.append (List.Sublist.refl _) (List.take_sublist _ _))
  hdisj_sel := by
    apply List.disjoint_left.mpr
    intro w h1 h2
    simp only [pass1, bits, List.mem_cons, List.mem_append, List.mem_range'_1] at h1
    rcases List.mem_append.mp h2 with hp | hg
    · have := mem_xyWires.mp (p1_sub_xy hp); (try dsimp only [Wire] at *); omega
    · rcases List.mem_append.mp (List.mem_of_mem_take hg) with ha | hr
      · have := mem_anc17.mp ha; (try dsimp only [Wire] at *); omega
      · have := mem_xyWires.mp (rem1_sub_xy hr); (try dsimp only [Wire] at *); omega
  hsupp := by
    intro w hw
    rw [List.mem_range'_1]
    simp only [pass1, bits, List.mem_cons, List.mem_append, List.mem_range'_1] at hw
    rcases hw with (((rfl | h) | h) | hp) | hg
    · decide
    · (try dsimp only [Wire] at *); omega
    · (try dsimp only [Wire] at *); omega
    · have := mem_xyWires.mp (p1_sub_xy hp); (try dsimp only [Wire] at *); omega
    · rcases List.mem_append.mp (List.mem_of_mem_take hg) with ha | hr
      · have := mem_anc17.mp ha; (try dsimp only [Wire] at *); omega
      · have := mem_xyWires.mp (rem1_sub_xy hr); (try dsimp only [Wire] at *); omega

theorem pass2_geo : pass2.Geo where
  hk := by decide
  hctrl_len := by decide
  hsel_len := by decide
  hpaths_len := by decide
  hbits := List.take_append_drop 7 addrBits
  hslots_len := s2_len
  hout_len := p2_len
  hgarb_len := by simp [pass2, anc12, anc17_length, rem2_len]
  hsel_nodup := by decide
  hregs_nodup := by
    change (p2 ++ (anc12 ++ rem2).take 1143).Nodup
    have hfull : (p2 ++ (anc12 ++ rem2)).Nodup := by
      refine List.nodup_append.mpr ⟨p2_nodup, List.nodup_append.mpr ⟨anc12_nodup, rem2_nodup, ?_⟩, ?_⟩
      · intro a ha b hb he; subst he
        have h1 := mem_anc12.mp ha; have h2 := mem_xyWires.mp (rem1_sub_xy (rem2_sub_rem1 hb))
        (try dsimp only [Wire] at *); omega
      · intro a ha b hb he; subst he
        rcases List.mem_append.mp hb with hb | hb
        · have h1 := mem_anc12.mp hb; have h2 := mem_xyWires.mp (rem1_sub_xy (p2_sub_rem1 ha))
          (try dsimp only [Wire] at *); omega
        · exact List.disjoint_left.mp p2_disj_rem2 ha hb
    exact hfull.sublist (List.Sublist.append (List.Sublist.refl _) (List.take_sublist _ _))
  hdisj_sel := by
    apply List.disjoint_left.mpr
    intro w h1 h2
    simp only [pass2, bits, List.mem_cons, List.mem_append, List.mem_range'_1] at h1
    rcases List.mem_append.mp h2 with hp | hg
    · have := mem_xyWires.mp (rem1_sub_xy (p2_sub_rem1 hp)); (try dsimp only [Wire] at *); omega
    · rcases List.mem_append.mp (List.mem_of_mem_take hg) with ha | hr
      · have := mem_anc12.mp ha; (try dsimp only [Wire] at *); omega
      · have := mem_xyWires.mp (rem1_sub_xy (rem2_sub_rem1 hr)); (try dsimp only [Wire] at *); omega
  hsupp := by
    intro w hw
    rw [List.mem_range'_1]
    simp only [pass2, bits, List.mem_cons, List.mem_append, List.mem_range'_1] at hw
    rcases hw with (((rfl | h) | h) | hp) | hg
    · decide
    · (try dsimp only [Wire] at *); omega
    · (try dsimp only [Wire] at *); omega
    · have := mem_xyWires.mp (rem1_sub_xy (p2_sub_rem1 hp)); (try dsimp only [Wire] at *); omega
    · rcases List.mem_append.mp (List.mem_of_mem_take hg) with ha | hr
      · have := mem_anc12.mp ha; (try dsimp only [Wire] at *); omega
      · have := mem_xyWires.mp (rem1_sub_xy (rem2_sub_rem1 hr)); (try dsimp only [Wire] at *); omega

theorem pass3_geo : pass3.Geo where
  hk := by decide
  hctrl_len := by decide
  hsel_len := by decide
  hpaths_len := by decide
  hbits := List.take_append_drop 4 addrBits
  hslots_len := s3_len
  hout_len := p3_len
  hgarb_len := by simp [pass3, anc15, anc17_length, rem3_len]
  hsel_nodup := by decide
  hregs_nodup := by
    change (p3 ++ (anc15 ++ rem3).take 1095).Nodup
    have hfull : (p3 ++ (anc15 ++ rem3)).Nodup := by
      refine List.nodup_append.mpr ⟨p3_nodup, List.nodup_append.mpr ⟨anc15_nodup, rem3_nodup, ?_⟩, ?_⟩
      · intro a ha b hb he; subst he
        have h1 := mem_anc15.mp ha; have h2 := mem_xyWires.mp (rem1_sub_xy (rem2_sub_rem1 (rem3_sub_rem2 hb)))
        (try dsimp only [Wire] at *); omega
      · intro a ha b hb he; subst he
        rcases List.mem_append.mp hb with hb | hb
        · have h1 := mem_anc15.mp hb; have h2 := mem_xyWires.mp (rem1_sub_xy (rem2_sub_rem1 (p3_sub_rem2 ha)))
          (try dsimp only [Wire] at *); omega
        · exact List.disjoint_left.mp p3_disj_rem3 ha hb
    exact hfull.sublist (List.Sublist.append (List.Sublist.refl _) (List.take_sublist _ _))
  hdisj_sel := by
    apply List.disjoint_left.mpr
    intro w h1 h2
    simp only [pass3, bits, List.mem_cons, List.mem_append, List.mem_range'_1] at h1
    rcases List.mem_append.mp h2 with hp | hg
    · have := mem_xyWires.mp (rem1_sub_xy (rem2_sub_rem1 (p3_sub_rem2 hp))); (try dsimp only [Wire] at *); omega
    · rcases List.mem_append.mp (List.mem_of_mem_take hg) with ha | hr
      · have := mem_anc15.mp ha; (try dsimp only [Wire] at *); omega
      · have := mem_xyWires.mp (rem1_sub_xy (rem2_sub_rem1 (rem3_sub_rem2 hr))); (try dsimp only [Wire] at *); omega
  hsupp := by
    intro w hw
    rw [List.mem_range'_1]
    simp only [pass3, bits, List.mem_cons, List.mem_append, List.mem_range'_1] at hw
    rcases hw with (((rfl | h) | h) | hp) | hg
    · decide
    · (try dsimp only [Wire] at *); omega
    · (try dsimp only [Wire] at *); omega
    · have := mem_xyWires.mp (rem1_sub_xy (rem2_sub_rem1 (p3_sub_rem2 hp))); (try dsimp only [Wire] at *); omega
    · rcases List.mem_append.mp (List.mem_of_mem_take hg) with ha | hr
      · have := mem_anc15.mp ha; (try dsimp only [Wire] at *); omega
      · have := mem_xyWires.mp (rem1_sub_xy (rem2_sub_rem1 (rem3_sub_rem2 hr))); (try dsimp only [Wire] at *); omega

theorem pass4_geo : pass4.Geo where
  hk := by decide
  hctrl_len := by decide
  hsel_len := by decide
  hpaths_len := by decide
  hbits := List.take_append_drop 5 addrBits
  hslots_len := s4_len
  hout_len := p4_len
  hgarb_len := by simp [pass4, anc14, anc17_length]
  hsel_nodup := by decide
  hregs_nodup := by
    change (p4 ++ anc14.take 1054).Nodup
    refine List.nodup_append.mpr ⟨p4_nodup, anc14_nodup.sublist (List.take_sublist _ _), ?_⟩
    intro a ha b hb he; subst he
    have h1 := mem_xyWires.mp (rem1_sub_xy (rem2_sub_rem1 (rem3_sub_rem2 (p4_sub_rem3 ha))))
    have h2 := mem_anc14.mp (List.mem_of_mem_take hb)
    (try dsimp only [Wire] at *); omega
  hdisj_sel := by
    apply List.disjoint_left.mpr
    intro w h1 h2
    simp only [pass4, bits, List.mem_cons, List.mem_append, List.mem_range'_1] at h1
    rcases List.mem_append.mp h2 with hp | hg
    · have := mem_xyWires.mp (rem1_sub_xy (rem2_sub_rem1 (rem3_sub_rem2 (p4_sub_rem3 hp))))
      (try dsimp only [Wire] at *); omega
    · have := mem_anc14.mp (List.mem_of_mem_take hg); (try dsimp only [Wire] at *); omega
  hsupp := by
    intro w hw
    rw [List.mem_range'_1]
    simp only [pass4, bits, List.mem_cons, List.mem_append, List.mem_range'_1] at hw
    rcases hw with (((rfl | h) | h) | hp) | hg
    · decide
    · (try dsimp only [Wire] at *); omega
    · (try dsimp only [Wire] at *); omega
    · have := mem_xyWires.mp (rem1_sub_xy (rem2_sub_rem1 (rem3_sub_rem2 (p4_sub_rem3 hp))))
      (try dsimp only [Wire] at *); omega
    · have := mem_anc14.mp (List.mem_of_mem_take hg); (try dsimp only [Wire] at *); omega

theorem pass5_geo : pass5.Geo where
  hk := by decide
  hctrl_len := by decide
  hsel_len := by decide
  hpaths_len := by decide
  hbits := List.take_append_drop 8 addrBits
  hslots_len := s5_len
  hout_len := p5_len
  hgarb_len := by simp [pass5, anc11, anc17_length]
  hsel_nodup := by decide
  hregs_nodup := by
    change (p5 ++ anc11.take 1020).Nodup
    refine List.nodup_append.mpr ⟨p5_nodup, anc11_nodup.sublist (List.take_sublist _ _), ?_⟩
    intro a ha b hb he; subst he
    have h1 := mem_xyWires.mp (rem1_sub_xy (rem2_sub_rem1 (rem3_sub_rem2 (p5_sub_rem3 ha))))
    have h2 := mem_anc11.mp (List.mem_of_mem_take hb)
    (try dsimp only [Wire] at *); omega
  hdisj_sel := by
    apply List.disjoint_left.mpr
    intro w h1 h2
    simp only [pass5, bits, List.mem_cons, List.mem_append, List.mem_range'_1] at h1
    rcases List.mem_append.mp h2 with hp | hg
    · have := mem_xyWires.mp (rem1_sub_xy (rem2_sub_rem1 (rem3_sub_rem2 (p5_sub_rem3 hp))))
      (try dsimp only [Wire] at *); omega
    · have := mem_anc11.mp (List.mem_of_mem_take hg); (try dsimp only [Wire] at *); omega
  hsupp := by
    intro w hw
    rw [List.mem_range'_1]
    simp only [pass5, bits, List.mem_cons, List.mem_append, List.mem_range'_1] at hw
    rcases hw with (((rfl | h) | h) | hp) | hg
    · decide
    · (try dsimp only [Wire] at *); omega
    · (try dsimp only [Wire] at *); omega
    · have := mem_xyWires.mp (rem1_sub_xy (rem2_sub_rem1 (rem3_sub_rem2 (p5_sub_rem3 hp))))
      (try dsimp only [Wire] at *); omega
    · have := mem_anc11.mp (List.mem_of_mem_take hg); (try dsimp only [Wire] at *); omega

/-! ### Part 5: Chained 5-pass QROM + fused 9-bit fixup + root seeding -/

def tree10 : UnaryActionTree := tableAddressTree high 0 1

def fixRec9 : Nat :=
  MeasuredClear.recordMeasurements (MeasuredClear.recordUnaryOps tree10 836 clearPaths) + 511

theorem fixRec9_eq : fixRec9 = 1534 := by
  rw [fixRec9, tree10, clear_measurements]

def allData : List (MeasuredClear.ClearPort 524288) :=
  pass1.clearData ++ pass2.clearData ++ pass3.clearData ++ pass4.clearData ++ pass5.clearData

theorem pass1_nums : pass1.k = 2 ∧ pass1.m = 392 ∧ pass1.selMeas = 131071 ∧ pass1.garbLen = 1176 := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> simp [Pass.selMeas, Pass.garbLen, pass1]
theorem pass2_nums : pass2.k = 7 ∧ pass2.m = 9 ∧ pass2.selMeas = 4095 ∧ pass2.garbLen = 1143 := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> simp [Pass.selMeas, Pass.garbLen, pass2]
theorem pass3_nums : pass3.k = 4 ∧ pass3.m = 73 ∧ pass3.selMeas = 32767 ∧ pass3.garbLen = 1095 := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> simp [Pass.selMeas, Pass.garbLen, pass3]
theorem pass4_nums : pass4.k = 5 ∧ pass4.m = 34 ∧ pass4.selMeas = 16383 ∧ pass4.garbLen = 1054 := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> simp [Pass.selMeas, Pass.garbLen, pass4]
theorem pass5_nums : pass5.k = 8 ∧ pass5.m = 4 ∧ pass5.selMeas = 2047 ∧ pass5.garbLen = 1020 := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> simp [Pass.selMeas, Pass.garbLen, pass5]

theorem allData_length : allData.length = 5488 := by
  simp only [allData, List.length_append, pass1.clearData_length pass1_geo,
    pass2.clearData_length pass2_geo, pass3.clearData_length pass3_geo,
    pass4.clearData_length pass4_geo, pass5.clearData_length pass5_geo,
    pass1_nums.2.2.2, pass2_nums.2.2.2, pass3_nums.2.2.2, pass4_nums.2.2.2, pass5_nums.2.2.2]

attribute [local irreducible] pass1 pass2 pass3 pass4 pass5 allData tree10

def stepFix (c : Nat) (rs : List (Fin c)) : Straight 524288 c (c + fixRec9) :=
  castFinish (by rw [fixRec9]; exact Nat.add_assoc c _ 511)
    (MeasuredClear.fixupProgram9 allData rs low hot tree10 836 scratch clearPaths)

def step5 (c : Nat) (rs : List (Fin c)) :
    Straight 524288 c (c + (pass5.selMeas + (pass5.garbLen + fixRec9))) :=
  pass5.stepProg pass5_geo stepFix c rs

def step45 (c : Nat) (rs : List (Fin c)) :
    Straight 524288 c (c + (pass4.selMeas + (pass4.garbLen + (pass5.selMeas + (pass5.garbLen + fixRec9))))) :=
  pass4.stepProg pass4_geo step5 c rs

def step345 (c : Nat) (rs : List (Fin c)) :
    Straight 524288 c (c + (pass3.selMeas + (pass3.garbLen +
      (pass4.selMeas + (pass4.garbLen + (pass5.selMeas + (pass5.garbLen + fixRec9))))))) :=
  pass3.stepProg pass3_geo step45 c rs

def step2345 (c : Nat) (rs : List (Fin c)) :
    Straight 524288 c (c + (pass2.selMeas + (pass2.garbLen +
      (pass3.selMeas + (pass3.garbLen +
        (pass4.selMeas + (pass4.garbLen + (pass5.selMeas + (pass5.garbLen + fixRec9))))))))) :=
  pass2.stepProg pass2_geo step345 c rs

theorem qrom_rec_eq :
    pass1.selMeas + (pass1.garbLen + (pass2.selMeas + (pass2.garbLen +
      (pass3.selMeas + (pass3.garbLen + (pass4.selMeas + (pass4.garbLen +
        (pass5.selMeas + (pass5.garbLen + fixRec9))))))))) = 193385 := by
  rw [fixRec9_eq, pass1_nums.2.2.1, pass1_nums.2.2.2, pass2_nums.2.2.1, pass2_nums.2.2.2,
    pass3_nums.2.2.1, pass3_nums.2.2.2, pass4_nums.2.2.1, pass4_nums.2.2.2,
    pass5_nums.2.2.1, pass5_nums.2.2.2]

def rawQromProgram (start : Nat) : Straight 524288 start (start + 193385) :=
  castFinish (by rw [qrom_rec_eq])
    (pass1.stepProg pass1_geo step2345 start ([] : List (Fin start)))

def qromProgram (start : Nat) : Straight 524288 start (start + 193385) :=
  RootPass.seedProgram 836 (rawQromProgram start)

attribute [local irreducible] stepFix step5 step45 step345 step2345 rawQromProgram qromProgram

def stepFixSrc (read : ConstantBit 524288 → Bool) (o : List Bool) : AdaptiveCircuit :=
  MeasuredClear.fixupSource9 allData o read low hot tree10 836 scratch clearPaths

def step5Src (read : ConstantBit 524288 → Bool) (o : List Bool) : AdaptiveCircuit :=
  pass5.stepSrc read (stepFixSrc read) o

def step45Src (read : ConstantBit 524288 → Bool) (o : List Bool) : AdaptiveCircuit :=
  pass4.stepSrc read (step5Src read) o

def step345Src (read : ConstantBit 524288 → Bool) (o : List Bool) : AdaptiveCircuit :=
  pass3.stepSrc read (step45Src read) o

def step2345Src (read : ConstantBit 524288 → Bool) (o : List Bool) : AdaptiveCircuit :=
  pass2.stepSrc read (step345Src read) o

def rawQromSource (read : ConstantBit 524288 → Bool) : AdaptiveCircuit :=
  pass1.stepSrc read (step2345Src read) List.nil

theorem rawQromProgram_run (read : ConstantBit 524288 → Bool) (start : Nat) (h : Fin start → Bool) :
    ((rawQromProgram start).instantiate read h).run = (rawQromSource read).run := by
  have hFix : ∀ c rs hh, ((stepFix c rs).instantiate read hh).run = (stepFixSrc read (rs.map hh)).run := by
    intro c rs hh; rw [stepFix, castFinish_instantiate, MeasuredClear.fixupProgram_run9]; rfl
  have h5 : ∀ c rs hh, ((step5 c rs).instantiate read hh).run = (step5Src read (rs.map hh)).run :=
    fun c rs hh => by rw [step5]; exact pass5.stepProg_run pass5_geo stepFix (stepFixSrc read) read hFix c rs hh
  have h45 : ∀ c rs hh, ((step45 c rs).instantiate read hh).run = (step45Src read (rs.map hh)).run :=
    fun c rs hh => by rw [step45]; exact pass4.stepProg_run pass4_geo step5 (step5Src read) read h5 c rs hh
  have h345 : ∀ c rs hh, ((step345 c rs).instantiate read hh).run = (step345Src read (rs.map hh)).run :=
    fun c rs hh => by rw [step345]; exact pass3.stepProg_run pass3_geo step45 (step45Src read) read h45 c rs hh
  have h2345 : ∀ c rs hh, ((step2345 c rs).instantiate read hh).run = (step2345Src read (rs.map hh)).run :=
    fun c rs hh => by rw [step2345]; exact pass2.stepProg_run pass2_geo step345 (step345Src read) read h345 c rs hh
  rw [rawQromProgram, castFinish_instantiate]
  exact pass1.stepProg_run pass1_geo step2345 (step2345Src read) read h2345 start List.nil h

/-! ### Part 6: Semantics of 5-pass QROM on finite table points -/

theorem fig14PointEncoding_finite_false {P : Point} (hP : P ≠ 0) :
    (fig14PointEncoding P).1 = false := by
  cases P with
  | zero => exact (hP rfl).elim
  | some _ => rfl

theorem rawQromSource_coherent (coeffs : Fin 524288 → PointCoeff) (Q : Point)
    (hn : ∀ a : Fin 524288, constantPoint Q (coeffs a) ≠ 0) :
    CoherentlyImplementsOn (rawQromSource (readConstant coeffs Q))
      (Finsupp.lmapDomain ℂ ℂ (fun s => pointWrite (tablePoint coeffs Q
        (tableAddressValue addrBits s)) s)) Input := by
  let read := readConstant coeffs Q
  let st1 (s : BasisState) := pass1.afterReset read s
  let st2 (s : BasisState) := pass2.afterReset read (st1 s)
  let st3 (s : BasisState) := pass3.afterReset read (st2 s)
  let st4 (s : BasisState) := pass4.afterReset read (st3 s)
  let st5 (s : BasisState) := pass5.afterReset read (st4 s)
  let tgt (s : BasisState) := pointWrite (tablePoint coeffs Q (tableAddressValue addrBits s)) s
  have h_out1 : pass1.out = p1 := by unfold pass1; rfl
  have h_out2 : pass2.out = p2 := by unfold pass2; rfl
  have h_out3 : pass3.out = p3 := by unfold pass3; rfl
  have h_out4 : pass4.out = p4 := by unfold pass4; rfl
  have h_out5 : pass5.out = p5 := by unfold pass5; rfl
  have h_s1 : pass1.sliceSlots = s1 := by unfold pass1; rfl
  have h_s2 : pass2.sliceSlots = s2 := by unfold pass2; rfl
  have h_s3 : pass3.sliceSlots = s3 := by unfold pass3; rfl
  have h_s4 : pass4.sliceSlots = s4 := by unfold pass4; rfl
  have h_s5 : pass5.sliceSlots = s5 := by unfold pass5; rfl
  have h_in_519 (s : BasisState) (hs : Input s) (w : Wire) (hw : 519 ≤ w ∧ w < 536) : s w = false :=
    input_clean s hs w (by (try dsimp only [Wire] at *); omega) (by (try dsimp only [Wire] at *); omega)
  have h_paths1 (s : BasisState) (hs : Input s) : Clean pass1.selPaths s := fun w hw => by
    have : 519 ≤ w ∧ w < 536 := by unfold pass1 at hw; dsimp only at hw; simp only [List.mem_range'_1] at hw; (try dsimp only [Wire] at *); omega
    exact h_in_519 s hs w this
  have h_paths2_s (s : BasisState) (hs : Input s) : Clean pass2.selPaths s := fun w hw => by
    have : 519 ≤ w ∧ w < 536 := by unfold pass2 at hw; dsimp only at hw; simp only [List.mem_range'_1] at hw; (try dsimp only [Wire] at *); omega
    exact h_in_519 s hs w this
  have h_paths3_s (s : BasisState) (hs : Input s) : Clean pass3.selPaths s := fun w hw => by
    have : 519 ≤ w ∧ w < 536 := by unfold pass3 at hw; dsimp only at hw; simp only [List.mem_range'_1] at hw; (try dsimp only [Wire] at *); omega
    exact h_in_519 s hs w this
  have h_paths4_s (s : BasisState) (hs : Input s) : Clean pass4.selPaths s := fun w hw => by
    have : 519 ≤ w ∧ w < 536 := by unfold pass4 at hw; dsimp only at hw; simp only [List.mem_range'_1] at hw; (try dsimp only [Wire] at *); omega
    exact h_in_519 s hs w this
  have h_paths5_s (s : BasisState) (hs : Input s) : Clean pass5.selPaths s := fun w hw => by
    have : 519 ≤ w ∧ w < 536 := by unfold pass5 at hw; dsimp only at hw; simp only [List.mem_range'_1] at hw; (try dsimp only [Wire] at *); omega
    exact h_in_519 s hs w this
  have h_clean_reg (P : Pass) (g : P.Geo) (s : BasisState) (hs : Input s) :
      Clean (P.out ++ P.garb) s := fun w hw => by
    have hn' : w ∉ 836 :: bits ++ P.selPaths := fun hm => List.disjoint_left.mp g.hdisj_sel hm hw
    exact hs.2 w (fun e => hn' (by simp [e])) (fun hm => hn' (by simp [hm]))
  -- Pairwise disjointness among p1..p5
  have hp1_not_p2 : p1.Disjoint p2 := List.disjoint_left.mpr (fun w h1 h2 =>
    List.disjoint_left.mp p1_disj_rem1 h1 (p2_sub_rem1 h2))
  have hp1_not_p3 : p1.Disjoint p3 := List.disjoint_left.mpr (fun w h1 h3 =>
    List.disjoint_left.mp p1_disj_rem1 h1 (rem2_sub_rem1 (p3_sub_rem2 h3)))
  have hp1_not_p4 : p1.Disjoint p4 := List.disjoint_left.mpr (fun w h1 h4 =>
    List.disjoint_left.mp p1_disj_rem1 h1 (rem2_sub_rem1 (rem3_sub_rem2 (p4_sub_rem3 h4))))
  have hp1_not_p5 : p1.Disjoint p5 := List.disjoint_left.mpr (fun w h1 h5 =>
    List.disjoint_left.mp p1_disj_rem1 h1 (rem2_sub_rem1 (rem3_sub_rem2 (p5_sub_rem3 h5))))
  have hp2_not_p3 : p2.Disjoint p3 := List.disjoint_left.mpr (fun w h2 h3 =>
    List.disjoint_left.mp p2_disj_rem2 h2 (p3_sub_rem2 h3))
  have hp2_not_p4 : p2.Disjoint p4 := List.disjoint_left.mpr (fun w h2 h4 =>
    List.disjoint_left.mp p2_disj_rem2 h2 (rem3_sub_rem2 (p4_sub_rem3 h4)))
  have hp2_not_p5 : p2.Disjoint p5 := List.disjoint_left.mpr (fun w h2 h5 =>
    List.disjoint_left.mp p2_disj_rem2 h2 (rem3_sub_rem2 (p5_sub_rem3 h5)))
  have hp3_not_p4 : p3.Disjoint p4 := List.disjoint_left.mpr (fun w h3 h4 =>
    List.disjoint_left.mp p3_disj_rem3 h3 (p4_sub_rem3 h4))
  have hp3_not_p5 : p3.Disjoint p5 := List.disjoint_left.mpr (fun w h3 h5 =>
    List.disjoint_left.mp p3_disj_rem3 h3 (p5_sub_rem3 h5))
  -- Disjointness between earlier outputs and later garbage pools
  have hp1_not_garb2 : p1.Disjoint pass2.garb := by
    apply List.disjoint_left.mpr; intro w h1 hg
    unfold pass2 at hg
    rcases List.mem_append.mp (List.mem_of_mem_take hg) with ha | hr
    · have := mem_anc12.mp ha; have := mem_xyWires.mp (p1_sub_xy h1); (try dsimp only [Wire] at *); omega
    · exact List.disjoint_left.mp p1_disj_rem1 h1 (rem2_sub_rem1 hr)
  have hp12_not_garb3 (w : Wire) (h12 : w ∈ p1 ∨ w ∈ p2) (hg : w ∈ pass3.garb) : False := by
    unfold pass3 at hg
    rcases List.mem_append.mp (List.mem_of_mem_take hg) with ha | hr
    · have hpt : w ∈ xyWires := (p_mem_xy w).mp (by tauto)
      have := mem_anc15.mp ha; have := mem_xyWires.mp hpt; (try dsimp only [Wire] at *); omega
    · rcases h12 with h1 | h2
      · exact List.disjoint_left.mp p1_disj_rem1 h1 (rem2_sub_rem1 (rem3_sub_rem2 hr))
      · exact List.disjoint_left.mp p2_disj_rem2 h2 (rem3_sub_rem2 hr)
  have hp123_not_garb4 (w : Wire) (h123 : w ∈ p1 ∨ w ∈ p2 ∨ w ∈ p3) (hg : w ∈ pass4.garb) : False := by
    unfold pass4 at hg
    have hpt : w ∈ xyWires := (p_mem_xy w).mp (by tauto)
    have := mem_anc14.mp (List.mem_of_mem_take hg); have := mem_xyWires.mp hpt
    (try dsimp only [Wire] at *); omega
  have hp_not_garb5 (w : Wire) (hw : w ∈ xyWires) (hg : w ∈ pass5.garb) : False := by
    unfold pass5 at hg
    have := mem_anc11.mp (List.mem_of_mem_take hg); have := mem_xyWires.mp hw
    (try dsimp only [Wire] at *); omega
  -- Per-pass preconditions, frames, loaded words, and clearData facts
  have hpre1 : ∀ s, Input s → Clean pass1.selPaths s ∧ s 836 = true ∧ Clean (pass1.out ++ pass1.garb) s :=
    fun s hs => ⟨h_paths1 s hs, hs.1, h_clean_reg pass1 pass1_geo s hs⟩
  have hfr1 : ∀ s, Input s → ∀ w, w ∉ p1 → st1 s w = s w := fun s hs w hw =>
    (pass1.afterReset_facts pass1_geo read s hs.1 (h_clean_reg pass1 pass1_geo s hs)).1 w (by rwa [h_out1])
  have hval1 : ∀ s, Input s → wireValues p1 (st1 s) = sliceWord s1 read (tableAddressValue addrBits s) := fun s hs => by
    have h := (pass1.afterReset_facts pass1_geo read s hs.1 (h_clean_reg pass1 pass1_geo s hs)).2
    rwa [h_out1, h_s1] at h
  have hclr1 : ∀ s, Input s → ∀ q ∈ pass1.clearData,
      (pass1.afterSwap read s) q.target = (true && decide (read (q.ref (tableAddressValue addrBits s)) = q.value)) :=
    fun s hs => (pass1.afterSwap_facts pass1_geo read s hs.1 (h_clean_reg pass1 pass1_geo s hs)).2.2
  have haddr1 (s : BasisState) (hs : Input s) : tableAddressValue addrBits (st1 s) = tableAddressValue addrBits s :=
    tableAddressValue_congr _ _ _ (fun w hw => hfr1 s hs w (fun h1 => addrBits_not_xy w hw (p1_sub_xy h1)))
  have hpre2 : ∀ s, Input s → Clean pass2.selPaths (st1 s) ∧ st1 s 836 = true ∧ Clean (pass2.out ++ pass2.garb) (st1 s) := by
    intro s hs
    refine ⟨fun w hw => ?_, ?_, fun w hw => ?_⟩
    · rw [hfr1 s hs w (fun h1 => by
        have := mem_xyWires.mp (p1_sub_xy h1); unfold pass2 at hw; simp only [List.mem_range'_1] at hw
        (try dsimp only [Wire] at *); omega)]
      exact h_paths2_s s hs w hw
    · rw [hfr1 s hs 836 (fun h1 => by have := mem_xyWires.mp (p1_sub_xy h1); (try dsimp only [Wire] at *); omega)]
      exact hs.1
    · rw [hfr1 s hs w (fun h1 => by
        rcases List.mem_append.mp hw with h2 | hg2
        · rw [h_out2] at h2; exact List.disjoint_left.mp hp1_not_p2 h1 h2
        · exact List.disjoint_left.mp hp1_not_garb2 h1 hg2)]
      exact h_clean_reg pass2 pass2_geo s hs w hw
  have hfr2 : ∀ s, Input s → ∀ w, w ∉ p2 → st2 s w = st1 s w := fun s hs w hw =>
    (pass2.afterReset_facts pass2_geo read (st1 s) (hpre2 s hs).2.1 (hpre2 s hs).2.2).1 w (by rwa [h_out2])
  have hval2 : ∀ s, Input s → wireValues p2 (st2 s) = sliceWord s2 read (tableAddressValue addrBits s) := fun s hs => by
    have h := (pass2.afterReset_facts pass2_geo read (st1 s) (hpre2 s hs).2.1 (hpre2 s hs).2.2).2
    rwa [h_out2, h_s2, haddr1 s hs] at h
  have hclr2 : ∀ s, Input s → ∀ q ∈ pass2.clearData,
      (pass2.afterSwap read (st1 s)) q.target = (true && decide (read (q.ref (tableAddressValue addrBits s)) = q.value)) := fun s hs => by
    have h := (pass2.afterSwap_facts pass2_geo read (st1 s) (hpre2 s hs).2.1 (hpre2 s hs).2.2).2.2
    rwa [haddr1 s hs] at h
  have haddr2 (s : BasisState) (hs : Input s) : tableAddressValue addrBits (st2 s) = tableAddressValue addrBits s :=
    (tableAddressValue_congr _ _ _ (fun w hw => hfr2 s hs w (fun h2 =>
      addrBits_not_xy w hw (rem1_sub_xy (p2_sub_rem1 h2))))).trans (haddr1 s hs)
  have hnp12 (s : BasisState) (hs : Input s) (w : Wire) (h1 : w ∉ p1) (h2 : w ∉ p2) : st2 s w = s w :=
    (hfr2 s hs w h2).trans (hfr1 s hs w h1)
  have hpre3 : ∀ s, Input s → Clean pass3.selPaths (st2 s) ∧ st2 s 836 = true ∧ Clean (pass3.out ++ pass3.garb) (st2 s) := by
    intro s hs
    refine ⟨fun w hw => ?_, ?_, fun w hw => ?_⟩
    · have hnp : w ∉ xyWires := fun hp => by
        have := mem_xyWires.mp hp; unfold pass3 at hw; simp only [List.mem_range'_1] at hw
        (try dsimp only [Wire] at *); omega
      rw [hnp12 s hs w (fun h => hnp (p1_sub_xy h)) (fun h => hnp (rem1_sub_xy (p2_sub_rem1 h)))]
      exact h_paths3_s s hs w hw
    · have hnp : (836 : Wire) ∉ xyWires := fun hp => by have := mem_xyWires.mp hp; (try dsimp only [Wire] at *); omega
      rw [hnp12 s hs 836 (fun h => hnp (p1_sub_xy h)) (fun h => hnp (rem1_sub_xy (p2_sub_rem1 h)))]
      exact hs.1
    · rw [hnp12 s hs w
        (fun h1 => by rcases List.mem_append.mp hw with h3 | hg3
                      · rw [h_out3] at h3; exact List.disjoint_left.mp hp1_not_p3 h1 h3
                      · exact hp12_not_garb3 w (Or.inl h1) hg3)
        (fun h2 => by rcases List.mem_append.mp hw with h3 | hg3
                      · rw [h_out3] at h3; exact List.disjoint_left.mp hp2_not_p3 h2 h3
                      · exact hp12_not_garb3 w (Or.inr h2) hg3)]
      exact h_clean_reg pass3 pass3_geo s hs w hw
  have hfr3 : ∀ s, Input s → ∀ w, w ∉ p3 → st3 s w = st2 s w := fun s hs w hw =>
    (pass3.afterReset_facts pass3_geo read (st2 s) (hpre3 s hs).2.1 (hpre3 s hs).2.2).1 w (by rwa [h_out3])
  have hval3 : ∀ s, Input s → wireValues p3 (st3 s) = sliceWord s3 read (tableAddressValue addrBits s) := fun s hs => by
    have h := (pass3.afterReset_facts pass3_geo read (st2 s) (hpre3 s hs).2.1 (hpre3 s hs).2.2).2
    rwa [h_out3, h_s3, haddr2 s hs] at h
  have hclr3 : ∀ s, Input s → ∀ q ∈ pass3.clearData,
      (pass3.afterSwap read (st2 s)) q.target = (true && decide (read (q.ref (tableAddressValue addrBits s)) = q.value)) := fun s hs => by
    have h := (pass3.afterSwap_facts pass3_geo read (st2 s) (hpre3 s hs).2.1 (hpre3 s hs).2.2).2.2
    rwa [haddr2 s hs] at h
  have haddr3 (s : BasisState) (hs : Input s) : tableAddressValue addrBits (st3 s) = tableAddressValue addrBits s :=
    (tableAddressValue_congr _ _ _ (fun w hw => hfr3 s hs w (fun h3 =>
      addrBits_not_xy w hw (rem1_sub_xy (rem2_sub_rem1 (p3_sub_rem2 h3)))))).trans (haddr2 s hs)
  have hnp123 (s : BasisState) (hs : Input s) (w : Wire) (h1 : w ∉ p1) (h2 : w ∉ p2) (h3 : w ∉ p3) : st3 s w = s w :=
    (hfr3 s hs w h3).trans (hnp12 s hs w h1 h2)
  have hpre4 : ∀ s, Input s → Clean pass4.selPaths (st3 s) ∧ st3 s 836 = true ∧ Clean (pass4.out ++ pass4.garb) (st3 s) := by
    intro s hs
    refine ⟨fun w hw => ?_, ?_, fun w hw => ?_⟩
    · have hnp : w ∉ xyWires := fun hp => by
        have := mem_xyWires.mp hp; unfold pass4 at hw; simp only [List.mem_range'_1] at hw
        (try dsimp only [Wire] at *); omega
      rw [hnp123 s hs w (fun h => hnp (p1_sub_xy h)) (fun h => hnp (rem1_sub_xy (p2_sub_rem1 h)))
        (fun h => hnp (rem1_sub_xy (rem2_sub_rem1 (p3_sub_rem2 h))))]
      exact h_paths4_s s hs w hw
    · have hnp : (836 : Wire) ∉ xyWires := fun hp => by have := mem_xyWires.mp hp; (try dsimp only [Wire] at *); omega
      rw [hnp123 s hs 836 (fun h => hnp (p1_sub_xy h)) (fun h => hnp (rem1_sub_xy (p2_sub_rem1 h)))
        (fun h => hnp (rem1_sub_xy (rem2_sub_rem1 (p3_sub_rem2 h))))]
      exact hs.1
    · rw [hnp123 s hs w
        (fun h1 => by rcases List.mem_append.mp hw with h4 | hg4
                      · rw [h_out4] at h4; exact List.disjoint_left.mp hp1_not_p4 h1 h4
                      · exact hp123_not_garb4 w (Or.inl h1) hg4)
        (fun h2 => by rcases List.mem_append.mp hw with h4 | hg4
                      · rw [h_out4] at h4; exact List.disjoint_left.mp hp2_not_p4 h2 h4
                      · exact hp123_not_garb4 w (Or.inr (Or.inl h2)) hg4)
        (fun h3 => by rcases List.mem_append.mp hw with h4 | hg4
                      · rw [h_out4] at h4; exact List.disjoint_left.mp hp3_not_p4 h3 h4
                      · exact hp123_not_garb4 w (Or.inr (Or.inr h3)) hg4)]
      exact h_clean_reg pass4 pass4_geo s hs w hw
  have hfr4 : ∀ s, Input s → ∀ w, w ∉ p4 → st4 s w = st3 s w := fun s hs w hw =>
    (pass4.afterReset_facts pass4_geo read (st3 s) (hpre4 s hs).2.1 (hpre4 s hs).2.2).1 w (by rwa [h_out4])
  have hval4 : ∀ s, Input s → wireValues p4 (st4 s) = sliceWord s4 read (tableAddressValue addrBits s) := fun s hs => by
    have h := (pass4.afterReset_facts pass4_geo read (st3 s) (hpre4 s hs).2.1 (hpre4 s hs).2.2).2
    rwa [h_out4, h_s4, haddr3 s hs] at h
  have hclr4 : ∀ s, Input s → ∀ q ∈ pass4.clearData,
      (pass4.afterSwap read (st3 s)) q.target = (true && decide (read (q.ref (tableAddressValue addrBits s)) = q.value)) := fun s hs => by
    have h := (pass4.afterSwap_facts pass4_geo read (st3 s) (hpre4 s hs).2.1 (hpre4 s hs).2.2).2.2
    rwa [haddr3 s hs] at h
  have haddr4 (s : BasisState) (hs : Input s) : tableAddressValue addrBits (st4 s) = tableAddressValue addrBits s :=
    (tableAddressValue_congr _ _ _ (fun w hw => hfr4 s hs w (fun h4 =>
      addrBits_not_xy w hw (rem1_sub_xy (rem2_sub_rem1 (rem3_sub_rem2 (p4_sub_rem3 h4))))))).trans (haddr3 s hs)
  have hnp1234 (s : BasisState) (hs : Input s) (w : Wire) (h1 : w ∉ p1) (h2 : w ∉ p2) (h3 : w ∉ p3) (h4 : w ∉ p4) :
      st4 s w = s w :=
    (hfr4 s hs w h4).trans (hnp123 s hs w h1 h2 h3)
  have hpre5 : ∀ s, Input s → Clean pass5.selPaths (st4 s) ∧ st4 s 836 = true ∧ Clean (pass5.out ++ pass5.garb) (st4 s) := by
    intro s hs
    refine ⟨fun w hw => ?_, ?_, fun w hw => ?_⟩
    · have hnp : w ∉ xyWires := fun hp => by
        have := mem_xyWires.mp hp; unfold pass5 at hw; simp only [List.mem_range'_1] at hw
        (try dsimp only [Wire] at *); omega
      rw [hnp1234 s hs w (fun h => hnp (p1_sub_xy h)) (fun h => hnp (rem1_sub_xy (p2_sub_rem1 h)))
        (fun h => hnp (rem1_sub_xy (rem2_sub_rem1 (p3_sub_rem2 h))))
        (fun h => hnp (rem1_sub_xy (rem2_sub_rem1 (rem3_sub_rem2 (p4_sub_rem3 h)))))]
      exact h_paths5_s s hs w hw
    · have hnp : (836 : Wire) ∉ xyWires := fun hp => by have := mem_xyWires.mp hp; (try dsimp only [Wire] at *); omega
      rw [hnp1234 s hs 836 (fun h => hnp (p1_sub_xy h)) (fun h => hnp (rem1_sub_xy (p2_sub_rem1 h)))
        (fun h => hnp (rem1_sub_xy (rem2_sub_rem1 (p3_sub_rem2 h))))
        (fun h => hnp (rem1_sub_xy (rem2_sub_rem1 (rem3_sub_rem2 (p4_sub_rem3 h)))))]
      exact hs.1
    · rw [hnp1234 s hs w
        (fun h1 => by rcases List.mem_append.mp hw with h5 | hg5
                      · rw [h_out5] at h5; exact List.disjoint_left.mp hp1_not_p5 h1 h5
                      · exact hp_not_garb5 w (p1_sub_xy h1) hg5)
        (fun h2 => by rcases List.mem_append.mp hw with h5 | hg5
                      · rw [h_out5] at h5; exact List.disjoint_left.mp hp2_not_p5 h2 h5
                      · exact hp_not_garb5 w (rem1_sub_xy (p2_sub_rem1 h2)) hg5)
        (fun h3 => by rcases List.mem_append.mp hw with h5 | hg5
                      · rw [h_out5] at h5; exact List.disjoint_left.mp hp3_not_p5 h3 h5
                      · exact hp_not_garb5 w (rem1_sub_xy (rem2_sub_rem1 (p3_sub_rem2 h3))) hg5)
        (fun h4 => by rcases List.mem_append.mp hw with h5 | hg5
                      · rw [h_out5] at h5; exact List.disjoint_left.mp p4_disj_p5 h4 h5
                      · exact hp_not_garb5 w (rem1_sub_xy (rem2_sub_rem1 (rem3_sub_rem2 (p4_sub_rem3 h4)))) hg5)]
      exact h_clean_reg pass5 pass5_geo s hs w hw
  have hfr5 : ∀ s, Input s → ∀ w, w ∉ p5 → st5 s w = st4 s w := fun s hs w hw =>
    (pass5.afterReset_facts pass5_geo read (st4 s) (hpre5 s hs).2.1 (hpre5 s hs).2.2).1 w (by rwa [h_out5])
  have hval5 : ∀ s, Input s → wireValues p5 (st5 s) = sliceWord s5 read (tableAddressValue addrBits s) := fun s hs => by
    have h := (pass5.afterReset_facts pass5_geo read (st4 s) (hpre5 s hs).2.1 (hpre5 s hs).2.2).2
    rwa [h_out5, h_s5, haddr4 s hs] at h
  have hclr5 : ∀ s, Input s → ∀ q ∈ pass5.clearData,
      (pass5.afterSwap read (st4 s)) q.target = (true && decide (read (q.ref (tableAddressValue addrBits s)) = q.value)) := fun s hs => by
    have h := (pass5.afterSwap_facts pass5_geo read (st4 s) (hpre5 s hs).2.1 (hpre5 s hs).2.2).2.2
    rwa [haddr4 s hs] at h
  -- Final basis state equality: st5 s = tgt s (using 838 = false and finite table point!)
  have hst5_out (s : BasisState) (hs : Input s) (w : Wire) (hw : w ∉ xyWires) : st5 s w = s w := by
    have h12345 : w ∉ p1 ∧ w ∉ p2 ∧ w ∉ p3 ∧ w ∉ p4 ∧ w ∉ p5 := by
      have hm := (p_mem_xy w).not.mpr hw; tauto
    exact (hfr5 s hs w h12345.2.2.2.2).trans (hnp1234 s hs w h12345.1 h12345.2.1 h12345.2.2.1 h12345.2.2.2.1)
  have hst5_eq (s : BasisState) (hs : Input s) : st5 s = tgt s := by
    have h838_not_xy : (838 : Wire) ∉ xyWires := fun h => by
      have := mem_xyWires.mp h; (try dsimp only [Wire] at *); omega
    have h838 : st5 s 838 = false := by
      rw [hst5_out s hs 838 h838_not_xy]
      exact input_clean s hs 838 (by decide) (by omega)
    have hwp : wireValues pointLogicalWires (st5 s) = wireValues pointLogicalWires (tgt s) := by
      have hw1' : wireValues p1 (st5 s) = sliceWord s1 read (tableAddressValue addrBits s) := by
        rw [← hval1 s hs]
        exact List.map_congr_left (fun w hw => (hfr5 s hs w (List.disjoint_left.mp hp1_not_p5 hw)).trans
          ((hfr4 s hs w (List.disjoint_left.mp hp1_not_p4 hw)).trans
            ((hfr3 s hs w (List.disjoint_left.mp hp1_not_p3 hw)).trans
              (hfr2 s hs w (List.disjoint_left.mp hp1_not_p2 hw)))))
      have hw2' : wireValues p2 (st5 s) = sliceWord s2 read (tableAddressValue addrBits s) := by
        rw [← hval2 s hs]
        exact List.map_congr_left (fun w hw => (hfr5 s hs w (List.disjoint_left.mp hp2_not_p5 hw)).trans
          ((hfr4 s hs w (List.disjoint_left.mp hp2_not_p4 hw)).trans
            (hfr3 s hs w (List.disjoint_left.mp hp2_not_p3 hw))))
      have hw3' : wireValues p3 (st5 s) = sliceWord s3 read (tableAddressValue addrBits s) := by
        rw [← hval3 s hs]
        exact List.map_congr_left (fun w hw => (hfr5 s hs w (List.disjoint_left.mp hp3_not_p5 hw)).trans
          (hfr4 s hs w (List.disjoint_left.mp hp3_not_p4 hw)))
      have hw4' : wireValues p4 (st5 s) = sliceWord s4 read (tableAddressValue addrBits s) := by
        rw [← hval4 s hs]
        exact List.map_congr_left (fun w hw => hfr5 s hs w (List.disjoint_left.mp p4_disj_p5 hw))
      have hall_xy : wireValues xyWires (st5 s) = word read (tableAddressValue addrBits s) := by
        rw [← xy_split, wireValues, List.map_append, List.map_append, List.map_append, List.map_append]
        change wireValues p1 (st5 s) ++ wireValues p2 (st5 s) ++ wireValues p3 (st5 s) ++
          wireValues p4 (st5 s) ++ wireValues p5 (st5 s) = _
        rw [hw1', hw2', hw3', hw4', hval5 s hs]
        simp only [sliceWord, ← List.map_append, slots_split, word, xyRefs, List.map_map]
        rfl
      have hpr := pointRefs_read coeffs Q (row (tableAddressValue addrBits s))
      have hinf_false : read ⟨row (tableAddressValue addrBits s), .infinity, ⟨0, by decide +kernel⟩⟩ = false := by
        have hlen512 : ((xyRefs (row (tableAddressValue addrBits s))).map read).length = 512 := by
          simp [xyRefs, slots_length]
        have hpr' : ((xyRefs (row (tableAddressValue addrBits s))).map read) ++
            [read ⟨row (tableAddressValue addrBits s), .infinity, ⟨0, by decide +kernel⟩⟩] =
            (constantBits 256 (fig14PointEncoding (constantPoint Q (coeffs (row (tableAddressValue addrBits s))))).2.1.val ++
              constantBits 256 (fig14PointEncoding (constantPoint Q (coeffs (row (tableAddressValue addrBits s))))).2.2.val) ++
            [(fig14PointEncoding (constantPoint Q (coeffs (row (tableAddressValue addrBits s))))).1] := by
          rw [← List.map_singleton, ← List.map_append, ← pointRefs_eq_xyRefs]
          exact hpr
        have htail := (List.append_inj hpr' (by simp [hlen512])).2
        have hb : read ⟨row (tableAddressValue addrBits s), .infinity, ⟨0, by decide +kernel⟩⟩ =
            (fig14PointEncoding (constantPoint Q (coeffs (row (tableAddressValue addrBits s))))).1 :=
          (List.cons.inj htail).1
        rw [hb, fig14PointEncoding_finite_false (hn (row (tableAddressValue addrBits s)))]
      dsimp only [tgt]
      rw [pointWrite_word]
      conv_lhs => rw [pointLogicalWires_eq, wireValues, List.map_append, List.map_singleton]
      change wireValues xyWires (st5 s) ++ [st5 s 838] = _
      rw [hall_xy, h838, word, ← hinf_false, ← List.map_singleton, ← List.map_append, ← pointRefs_eq_xyRefs]
      exact hpr
    funext w
    by_cases hp : w ∈ pointLogicalWires
    · exact List.map_inj_left.mp hwp w hp
    · have hnotxy : w ∉ xyWires := fun h => hp (by rw [pointLogicalWires_eq]; exact List.mem_append_left _ h)
      rw [hst5_out s hs w hnotxy]; dsimp only [tgt]; rw [pointWrite_frame _ _ w hp]
  -- Apply 5 nested stepSrc_sim + fixupSource_coherent9
  have htree_lay : tree10.Layout 836 clearPaths := by unfold tree10; exact clear_layout
  have htree_hdisj : (MeasuredClear.hotBank9 hot).Disjoint
      (836 :: tree10.indexWires.dedup ++ clearPaths) := by unfold tree10; exact hot_disjoint
  have htree_scr : scratch ∉ 836 :: tree10.indexWires.dedup ++ clearPaths := by
    unfold tree10; exact scratch_not_tree
  have hst5_hot (s : BasisState) (hs : Input s) : MeasuredClear.HotClean9 hot (st5 s) := fun i => by
    have hhi : 876 ≤ hot i ∧ hot i < 1388 := by have := i.isLt; simp only [hot]; (try dsimp only [Wire] at *); omega
    rw [hst5_out s hs (hot i) (fun hp => by have := mem_xyWires.mp hp; (try dsimp only [Wire] at *); omega)]
    exact input_clean s hs (hot i) (by (try dsimp only [Wire] at *); omega) (by (try dsimp only [Wire] at *); omega)
  have hst5_cpaths (s : BasisState) (hs : Input s) : Clean clearPaths (st5 s) := fun w hw => by
    simp only [clearPaths, List.mem_range'_1] at hw
    rw [hst5_out s hs w (fun hp => by have := mem_xyWires.mp hp; (try dsimp only [Wire] at *); omega)]
    exact input_clean s hs w (by (try dsimp only [Wire] at *); omega) (by (try dsimp only [Wire] at *); omega)
  have hst5_836 (s : BasisState) (hs : Input s) : st5 s 836 = true := by
    rw [hst5_out s hs 836 (fun hp => by have := mem_xyWires.mp hp; (try dsimp only [Wire] at *); omega)]; exact hs.1
  have hst5_addr (s : BasisState) (hs : Input s) :
      512 * tree10.routeLabel (st5 s) + MeasuredClear.hotAddress9 low (st5 s) = tableAddressValue addrBits s := by
    unfold tree10
    rw [MeasuredClear.splitAddress_value9, low_high_addrBits]
    exact tableAddressValue_congr _ _ _ (fun w hw => hst5_out s hs w (addrBits_not_xy w hw))
  have hsim := pass1.stepSrc_sim pass1_geo read (step2345Src read) List.nil Input id tgt (fun _ => 1) hpre1
    (fun o1 ho1 =>
      pass2.stepSrc_sim pass2_geo read (step345Src read) (List.nil ++ o1) Input st1 tgt
        (fun s => 1 * registerXPhase pass1.targets o1 (pass1.afterSwap read s)) hpre2
        (fun o2 ho2 =>
          pass3.stepSrc_sim pass3_geo read (step45Src read) ((List.nil ++ o1) ++ o2) Input st2 tgt
            (fun s => (1 * registerXPhase pass1.targets o1 (pass1.afterSwap read s)) *
              registerXPhase pass2.targets o2 (pass2.afterSwap read (st1 s))) hpre3
            (fun o3 ho3 =>
              pass4.stepSrc_sim pass4_geo read (step5Src read) (((List.nil ++ o1) ++ o2) ++ o3) Input st3 tgt
                (fun s => ((1 * registerXPhase pass1.targets o1 (pass1.afterSwap read s)) *
                  registerXPhase pass2.targets o2 (pass2.afterSwap read (st1 s))) *
                  registerXPhase pass3.targets o3 (pass3.afterSwap read (st2 s))) hpre4
                (fun o4 ho4 =>
                  pass5.stepSrc_sim pass5_geo read (stepFixSrc read) ((((List.nil ++ o1) ++ o2) ++ o3) ++ o4) Input st4 tgt
                    (fun s => (((1 * registerXPhase pass1.targets o1 (pass1.afterSwap read s)) *
                      registerXPhase pass2.targets o2 (pass2.afterSwap read (st1 s))) *
                      registerXPhase pass3.targets o3 (pass3.afterSwap read (st2 s))) *
                      registerXPhase pass4.targets o4 (pass4.afterSwap read (st3 s))) hpre5
                    (fun o5 ho5 => by
                      have hfc := MeasuredClear.fixupSource_coherent9 allData
                        (((((List.nil ++ o1) ++ o2) ++ o3) ++ o4) ++ o5)
                        read low hot tree10 836 scratch clearPaths
                        htree_lay hot_injective low_ne_hot htree_hdisj htree_scr scratch_not_hot
                      obtain ⟨cs, al, ma⟩ := hfc
                      refine ⟨cs, al.imp (fun b c hb s hs => ?_), ma⟩
                      rw [hb (st5 s) ⟨hst5_hot s hs, hst5_cpaths s hs⟩, MeasuredClear.basisIdeal_ket]
                      simp only [id_eq, List.nil_append]
                      have hd1 : o1.length = pass1.clearData.length := by
                        rw [ho1, pass1.targets_length pass1_geo, pass1.clearData_length pass1_geo]
                      have hd2 : o2.length = pass2.clearData.length := by
                        rw [ho2, pass2.targets_length pass2_geo, pass2.clearData_length pass2_geo]
                      have hd3 : o3.length = pass3.clearData.length := by
                        rw [ho3, pass3.targets_length pass3_geo, pass3.clearData_length pass3_geo]
                      have hd4 : o4.length = pass4.clearData.length := by
                        rw [ho4, pass4.targets_length pass4_geo, pass4.clearData_length pass4_geo]
                      have hff : MeasuredClear.fixupFactor9 allData ((((o1 ++ o2) ++ o3) ++ o4) ++ o5) read
                          low hot tree10 836 (st5 s) =
                          registerXPhase pass1.targets o1 (pass1.afterSwap read s) *
                          registerXPhase pass2.targets o2 (pass2.afterSwap read (st1 s)) *
                          registerXPhase pass3.targets o3 (pass3.afterSwap read (st2 s)) *
                          registerXPhase pass4.targets o4 (pass4.afterSwap read (st3 s)) *
                          registerXPhase pass5.targets o5 (pass5.afterSwap read (st4 s)) := by
                        have ha : allData =
                            (((pass1.clearData ++ pass2.clearData) ++ pass3.clearData) ++ pass4.clearData) ++
                              pass5.clearData := by
                          unfold allData; rfl
                        rw [ha,
                          MeasuredClear.fixupFactor9_append _ pass5.clearData (((o1 ++ o2) ++ o3) ++ o4) o5
                            (by simp [hd1, hd2, hd3, hd4]),
                          MeasuredClear.fixupFactor9_append _ pass4.clearData ((o1 ++ o2) ++ o3) o4
                            (by simp [hd1, hd2, hd3]),
                          MeasuredClear.fixupFactor9_append _ pass3.clearData (o1 ++ o2) o3
                            (by simp [hd1, hd2]),
                          MeasuredClear.fixupFactor9_append pass1.clearData pass2.clearData o1 o2 hd1]
                        have hf1 := MeasuredClear.fixupFactor9_loaded pass1.clearData o1 read low hot
                          tree10 836 clearPaths hot_injective low_ne_hot htree_hdisj
                          (st5 s) (pass1.afterSwap read s) (hst5_hot s hs)
                          (fun q hq => by rw [hst5_836 s hs, hst5_addr s hs]; exact hclr1 s hs q hq)
                        have hf2 := MeasuredClear.fixupFactor9_loaded pass2.clearData o2 read low hot
                          tree10 836 clearPaths hot_injective low_ne_hot htree_hdisj
                          (st5 s) (pass2.afterSwap read (st1 s)) (hst5_hot s hs)
                          (fun q hq => by rw [hst5_836 s hs, hst5_addr s hs]; exact hclr2 s hs q hq)
                        have hf3 := MeasuredClear.fixupFactor9_loaded pass3.clearData o3 read low hot
                          tree10 836 clearPaths hot_injective low_ne_hot htree_hdisj
                          (st5 s) (pass3.afterSwap read (st2 s)) (hst5_hot s hs)
                          (fun q hq => by rw [hst5_836 s hs, hst5_addr s hs]; exact hclr3 s hs q hq)
                        have hf4 := MeasuredClear.fixupFactor9_loaded pass4.clearData o4 read low hot
                          tree10 836 clearPaths hot_injective low_ne_hot htree_hdisj
                          (st5 s) (pass4.afterSwap read (st3 s)) (hst5_hot s hs)
                          (fun q hq => by rw [hst5_836 s hs, hst5_addr s hs]; exact hclr4 s hs q hq)
                        have hf5 := MeasuredClear.fixupFactor9_loaded pass5.clearData o5 read low hot
                          tree10 836 clearPaths hot_injective low_ne_hot htree_hdisj
                          (st5 s) (pass5.afterSwap read (st4 s)) (hst5_hot s hs)
                          (fun q hq => by rw [hst5_836 s hs, hst5_addr s hs]; exact hclr5 s hs q hq)
                        rw [pass1.clearData_targets pass1_geo] at hf1
                        rw [pass2.clearData_targets pass2_geo] at hf2
                        rw [pass3.clearData_targets pass3_geo] at hf3
                        rw [pass4.clearData_targets pass4_geo] at hf4
                        rw [pass5.clearData_targets pass5_geo] at hf5
                        rw [hf1, hf2, hf3, hf4, hf5]
                      rw [hff, hst5_eq s hs, one_mul])))))
  obtain ⟨cs, al, ma⟩ := hsim
  refine ⟨cs, al.imp (fun b c hb s hs => ?_), ma⟩
  simpa only [id_eq, one_smul, First18.lmap_ket] using hb s hs

theorem rawQromProgram_coherent (coeffs : Fin 524288 → PointCoeff) (Q : Point)
    (hn : ∀ a : Fin 524288, constantPoint Q (coeffs a) ≠ 0)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((rawQromProgram start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (fun s => pointWrite (tablePoint coeffs Q
        (tableAddressValue addrBits s)) s)) Input := by
  unfold CoherentlyImplementsOn
  rw [rawQromProgram_run]
  exact rawQromSource_coherent coeffs Q hn

/-! ### Part 7: Resources of `qromProgram` -/

theorem rawQromProgram_tCount (read : ConstantBit 524288 → Bool) (start : Nat) (h : Fin start → Bool) :
    ((rawQromProgram start).instantiate read h).tCount = 7 * 193376 := by
  have hlay : tree10.Layout 836 clearPaths := by unfold tree10; exact clear_layout
  have hFix : ∀ c rs hh, ((stepFix c rs).instantiate read hh).tCount = 7 * 1525 := by
    intro c rs hh
    rw [stepFix, castFinish_instantiate,
      MeasuredClear.fixupProgram_tCount9 allData rs low hot tree10 836 scratch clearPaths hlay]
    have hn : tree10.internalNodes = 1023 := by unfold tree10; exact clear_nodes
    rw [hn]
  have h5 : ∀ c rs hh, ((step5 c rs).instantiate read hh).tCount = 7 * (pass5.selMeas + pass5.garbLen) + 7 * 1525 :=
    fun c rs hh => by rw [step5]; exact pass5.stepProg_tCount pass5_geo stepFix read hFix c rs hh
  have h45 : ∀ c rs hh, ((step45 c rs).instantiate read hh).tCount =
      7 * (pass4.selMeas + pass4.garbLen) + (7 * (pass5.selMeas + pass5.garbLen) + 7 * 1525) :=
    fun c rs hh => by rw [step45]; exact pass4.stepProg_tCount pass4_geo step5 read h5 c rs hh
  have h345 : ∀ c rs hh, ((step345 c rs).instantiate read hh).tCount =
      7 * (pass3.selMeas + pass3.garbLen) +
      (7 * (pass4.selMeas + pass4.garbLen) + (7 * (pass5.selMeas + pass5.garbLen) + 7 * 1525)) :=
    fun c rs hh => by rw [step345]; exact pass3.stepProg_tCount pass3_geo step45 read h45 c rs hh
  have h2345 : ∀ c rs hh, ((step2345 c rs).instantiate read hh).tCount =
      7 * (pass2.selMeas + pass2.garbLen) +
      (7 * (pass3.selMeas + pass3.garbLen) +
      (7 * (pass4.selMeas + pass4.garbLen) + (7 * (pass5.selMeas + pass5.garbLen) + 7 * 1525))) :=
    fun c rs hh => by rw [step2345]; exact pass2.stepProg_tCount pass2_geo step345 read h345 c rs hh
  rw [rawQromProgram, castFinish_instantiate, pass1.stepProg_tCount pass1_geo step2345 read h2345,
    pass1_nums.2.2.1, pass1_nums.2.2.2, pass2_nums.2.2.1, pass2_nums.2.2.2,
    pass3_nums.2.2.1, pass3_nums.2.2.2, pass4_nums.2.2.1, pass4_nums.2.2.2,
    pass5_nums.2.2.1, pass5_nums.2.2.2]

theorem rawQromProgram_residue (start : Nat) : residue (rawQromProgram start) = 0 := by
  have hFix : ∀ c rs, residue (stepFix c rs) = 0 := fun c rs => by
    rw [stepFix, residue_cast]; exact MeasuredClear.fixupProgram_residue9 _ _ _ _ _ _ _ _
  have h5 : ∀ c rs, residue (step5 c rs) = 0 := fun c rs => by
    rw [step5]; exact pass5.stepProg_residue pass5_geo stepFix hFix c rs
  have h45 : ∀ c rs, residue (step45 c rs) = 0 := fun c rs => by
    rw [step45]; exact pass4.stepProg_residue pass4_geo step5 h5 c rs
  have h345 : ∀ c rs, residue (step345 c rs) = 0 := fun c rs => by
    rw [step345]; exact pass3.stepProg_residue pass3_geo step45 h45 c rs
  have h2345 : ∀ c rs, residue (step2345 c rs) = 0 := fun c rs => by
    rw [step2345]; exact pass2.stepProg_residue pass2_geo step345 h345 c rs
  rw [rawQromProgram, residue_cast]
  exact pass1.stepProg_residue pass1_geo step2345 h2345 start List.nil

theorem rawQromProgram_added (start : Nat) : added (rawQromProgram start) = 193376 := by
  have h := exact_t (rawQromProgram start) (rawQromProgram_residue start) (fun _ => false) (fun _ => false)
  have ht := rawQromProgram_tCount (fun _ => false) start (fun _ => false)
  exact Nat.eq_of_mul_eq_mul_left (by decide) (h.symm.trans ht)

theorem rawQromProgram_slots (start : Nat) : (rawQromProgram start).gateSlots ≤ 13000000000 := by
  have hlay : tree10.Layout 836 clearPaths := by unfold tree10; exact clear_layout
  have hFix : ∀ c rs, (stepFix c rs).gateSlots ≤ 12600000000 := fun c rs => by
    rw [stepFix, castFinish_gateSlots,
      MeasuredClear.fixupProgram_slots9 allData rs low hot tree10 836 scratch clearPaths hlay]
    have hl : tree10.leaves = 1024 := by unfold tree10; exact clear_leaves
    have hn : tree10.internalNodes = 1023 := by unfold tree10; exact clear_nodes
    have hm : min allData.length rs.length ≤ 5488 := (Nat.min_le_left _ _).trans (by rw [allData_length])
    rw [hl, hn]
    omega
  have h5 : ∀ c rs, (step5 c rs).gateSlots ≤
      (2 ^ pass5.k * pass5.m) * (pass5.selMeas + 1) + 10 * pass5.selMeas + 3 * pass5.garbLen + 12600000000 :=
    fun c rs => by rw [step5]; exact pass5.stepProg_slots pass5_geo stepFix hFix c rs
  have h45 : ∀ c rs, (step45 c rs).gateSlots ≤
      (2 ^ pass4.k * pass4.m) * (pass4.selMeas + 1) + 10 * pass4.selMeas + 3 * pass4.garbLen +
      ((2 ^ pass5.k * pass5.m) * (pass5.selMeas + 1) + 10 * pass5.selMeas + 3 * pass5.garbLen + 12600000000) :=
    fun c rs => by rw [step45]; exact pass4.stepProg_slots pass4_geo step5 h5 c rs
  have h345 : ∀ c rs, (step345 c rs).gateSlots ≤
      (2 ^ pass3.k * pass3.m) * (pass3.selMeas + 1) + 10 * pass3.selMeas + 3 * pass3.garbLen +
      ((2 ^ pass4.k * pass4.m) * (pass4.selMeas + 1) + 10 * pass4.selMeas + 3 * pass4.garbLen +
      ((2 ^ pass5.k * pass5.m) * (pass5.selMeas + 1) + 10 * pass5.selMeas + 3 * pass5.garbLen + 12600000000)) :=
    fun c rs => by rw [step345]; exact pass3.stepProg_slots pass3_geo step45 h45 c rs
  have h2345 : ∀ c rs, (step2345 c rs).gateSlots ≤
      (2 ^ pass2.k * pass2.m) * (pass2.selMeas + 1) + 10 * pass2.selMeas + 3 * pass2.garbLen +
      ((2 ^ pass3.k * pass3.m) * (pass3.selMeas + 1) + 10 * pass3.selMeas + 3 * pass3.garbLen +
      ((2 ^ pass4.k * pass4.m) * (pass4.selMeas + 1) + 10 * pass4.selMeas + 3 * pass4.garbLen +
      ((2 ^ pass5.k * pass5.m) * (pass5.selMeas + 1) + 10 * pass5.selMeas + 3 * pass5.garbLen + 12600000000))) :=
    fun c rs => by rw [step2345]; exact pass2.stepProg_slots pass2_geo step345 h345 c rs
  rw [rawQromProgram, castFinish_gateSlots]
  refine (pass1.stepProg_slots pass1_geo step2345 h2345 start List.nil).trans ?_
  rw [pass1_nums.1, pass1_nums.2.1, pass1_nums.2.2.1, pass1_nums.2.2.2,
    pass2_nums.1, pass2_nums.2.1, pass2_nums.2.2.1, pass2_nums.2.2.2,
    pass3_nums.1, pass3_nums.2.1, pass3_nums.2.2.1, pass3_nums.2.2.2,
    pass4_nums.1, pass4_nums.2.1, pass4_nums.2.2.1, pass4_nums.2.2.2,
    pass5_nums.1, pass5_nums.2.1, pass5_nums.2.2.1, pass5_nums.2.2.2]
  norm_num

theorem rawQromProgram_wellFormed (start : Nat) : (rawQromProgram start).WellFormed := by
  have hlay : tree10.Layout 836 clearPaths := by unfold tree10; exact clear_layout
  have hscr : scratch ∉ 836 :: tree10.indexWires.dedup ++ clearPaths := by
    unfold tree10; exact scratch_not_tree
  have hFix : ∀ c rs, (stepFix c rs).WellFormed := fun c rs => by
    rw [stepFix, castFinish_wellFormed]
    exact MeasuredClear.fixupProgram_wellFormed9 allData rs low hot tree10 836 scratch
      clearPaths hlay hot_injective low_ne_hot hscr scratch_not_hot
  have h5 : ∀ c rs, (step5 c rs).WellFormed := fun c rs => by
    rw [step5]; exact pass5.stepProg_wellFormed pass5_geo stepFix hFix c rs
  have h45 : ∀ c rs, (step45 c rs).WellFormed := fun c rs => by
    rw [step45]; exact pass4.stepProg_wellFormed pass4_geo step5 h5 c rs
  have h345 : ∀ c rs, (step345 c rs).WellFormed := fun c rs => by
    rw [step345]; exact pass3.stepProg_wellFormed pass3_geo step45 h45 c rs
  have h2345 : ∀ c rs, (step2345 c rs).WellFormed := fun c rs => by
    rw [step2345]; exact pass2.stepProg_wellFormed pass2_geo step345 h345 c rs
  rw [rawQromProgram, castFinish_wellFormed]
  exact pass1.stepProg_wellFormed pass1_geo step2345 h2345 start List.nil

theorem rawQromProgram_support (start : Nat) : straightWires (rawQromProgram start) ⊆ List.range' 2 1608 := by
  have hFix : ∀ c rs, straightWires (stepFix c rs) ⊆ List.range' 2 1608 := fun c rs => by
    rw [stepFix, straightWires_castFinish, RootPass.straightWires_eq_naive]
    apply MeasuredClear.fixupProgram_within9
    · decide
    · decide
    · intro i; rw [List.mem_range'_1]; have := i.isLt; simp only [low]; (try dsimp only [Wire] at *); omega
    · intro i; rw [List.mem_range'_1]; have := i.isLt; simp only [hot]; (try dsimp only [Wire] at *); omega
    · intro w hw
      have hi : w ∈ high := by unfold tree10 at hw; exact (tableAddressTree_mem_index high 0 1 w).mp hw
      rw [List.mem_range'_1]; simp only [high, List.mem_range'_1] at hi; (try dsimp only [Wire] at *); omega
    · intro w hw
      rw [List.mem_range'_1]; simp only [clearPaths, List.mem_range'_1] at hw; (try dsimp only [Wire] at *); omega
  have h5 : ∀ c rs, straightWires (step5 c rs) ⊆ List.range' 2 1608 := fun c rs => by
    rw [step5]; exact pass5.stepProg_support pass5_geo stepFix hFix c rs
  have h45 : ∀ c rs, straightWires (step45 c rs) ⊆ List.range' 2 1608 := fun c rs => by
    rw [step45]; exact pass4.stepProg_support pass4_geo step5 h5 c rs
  have h345 : ∀ c rs, straightWires (step345 c rs) ⊆ List.range' 2 1608 := fun c rs => by
    rw [step345]; exact pass3.stepProg_support pass3_geo step45 h45 c rs
  have h2345 : ∀ c rs, straightWires (step2345 c rs) ⊆ List.range' 2 1608 := fun c rs => by
    rw [step2345]; exact pass2.stepProg_support pass2_geo step345 h345 c rs
  rw [rawQromProgram, straightWires_castFinish]
  exact pass1.stepProg_support pass1_geo step2345 h2345 start List.nil

theorem rawQromProgram_safe836 (start : Nat) : RootPass.safeProgram 836 (rawQromProgram start) := by
  have hlay : tree10.Layout 836 clearPaths := by unfold tree10; exact clear_layout
  obtain ⟨hb, hp⟩ := RootPass.layout_avoids hlay
  have hFix : ∀ c rs, RootPass.safeProgram 836 (stepFix c rs) := fun c rs => by
    rw [stepFix, RootPass.safeProgram_cast]
    exact RootPass.fixupProgram9_safe 836 allData rs low hot tree10 836 scratch
      clearPaths low_ne_836 hot_ne_836 (by decide) hb hp
  have h5 : ∀ c rs, RootPass.safeProgram 836 (step5 c rs) := fun c rs => by
    rw [step5]; exact pass5.stepProg_safe836 pass5_geo stepFix hFix c rs
  have h45 : ∀ c rs, RootPass.safeProgram 836 (step45 c rs) := fun c rs => by
    rw [step45]; exact pass4.stepProg_safe836 pass4_geo step5 h5 c rs
  have h345 : ∀ c rs, RootPass.safeProgram 836 (step345 c rs) := fun c rs => by
    rw [step345]; exact pass3.stepProg_safe836 pass3_geo step45 h45 c rs
  have h2345 : ∀ c rs, RootPass.safeProgram 836 (step2345 c rs) := fun c rs => by
    rw [step2345]; exact pass2.stepProg_safe836 pass2_geo step345 h345 c rs
  rw [rawQromProgram, RootPass.safeProgram_cast]
  exact pass1.stepProg_safe836 pass1_geo step2345 h2345 start List.nil

theorem rawQromProgram_hits836 (start : Nat) : RootPass.literalHits 836 (rawQromProgram start) = 6 := by
  have hlay : tree10.Layout 836 clearPaths := by unfold tree10; exact clear_layout
  have hnodes : tree10.internalNodes = 1023 := by unfold tree10; exact clear_nodes
  have hFix : ∀ c rs, RootPass.literalHits 836 (stepFix c rs) = 1 := fun c rs => by
    rw [stepFix, RootPass.literalHits_cast,
      RootPass.fixupProgram9_hits 836 allData rs low hot tree10 836 scratch
        clearPaths low_ne_836 hot_ne_836]
    exact RootPass.recordUnaryOps_root_hits 836 tree10 clearPaths hlay (by rw [hnodes]; decide)
  have h5 : ∀ c rs, RootPass.literalHits 836 (step5 c rs) = 2 := fun c rs => by
    rw [step5]; exact pass5.stepProg_hits836 pass5_geo stepFix hFix c rs
  have h45 : ∀ c rs, RootPass.literalHits 836 (step45 c rs) = 3 := fun c rs => by
    rw [step45]; exact pass4.stepProg_hits836 pass4_geo step5 h5 c rs
  have h345 : ∀ c rs, RootPass.literalHits 836 (step345 c rs) = 4 := fun c rs => by
    rw [step345]; exact pass3.stepProg_hits836 pass3_geo step45 h45 c rs
  have h2345 : ∀ c rs, RootPass.literalHits 836 (step2345 c rs) = 5 := fun c rs => by
    rw [step2345]; exact pass2.stepProg_hits836 pass2_geo step345 h345 c rs
  rw [rawQromProgram, RootPass.literalHits_cast]
  exact pass1.stepProg_hits836 pass1_geo step2345 h2345 start List.nil

theorem qromProgram_coherent (coeffs : Fin 524288 → PointCoeff) (Q : Point)
    (hn : ∀ a : Fin 524288, constantPoint Q (coeffs a) ≠ 0)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((qromProgram start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (fun s => pointWrite (tablePoint coeffs Q
        (tableAddressValue addrBits s)) s)) Input := by
  rw [qromProgram]
  exact RootPass.seedProgram_coherent 836 (rawQromProgram start) _ history _ _
    (rawQromProgram_safe836 start) (fun _ hs => hs.1) (rawQromProgram_coherent coeffs Q hn start history)

theorem qromProgram_residue (start : Nat) : residue (qromProgram start) = 0 := by
  have h := RootPass.seedProgram_residue_le 836 (rawQromProgram start)
  rw [rawQromProgram_residue] at h
  rw [qromProgram]
  exact Nat.eq_zero_of_le_zero h

theorem qromProgram_added (start : Nat) : added (qromProgram start) = 193370 := by
  have h := RootPass.seedProgram_added 836 (rawQromProgram start)
  rw [rawQromProgram_added, rawQromProgram_hits836] at h
  rw [qromProgram]
  omega

theorem qromProgram_slots (start : Nat) : (qromProgram start).gateSlots ≤ 13000000000 := by
  rw [qromProgram, RootPass.seedProgram_slots]
  exact rawQromProgram_slots start

theorem qromProgram_support (start : Nat) : straightWires (qromProgram start) ⊆ List.range' 2 1608 := by
  rw [qromProgram]
  exact (RootPass.seedProgram_wires 836 _).trans (rawQromProgram_support start)

theorem qromProgram_wellFormed (start : Nat) : (qromProgram start).WellFormed := by
  rw [qromProgram]
  exact RootPass.seedProgram_wellFormed 836 _ (rawQromProgram_wellFormed start)

/-! ### Part 8: Pre/post address-complement Clifford layers and conditional `negY` (`255` Toffolis) -/

def flipAddr : Circuit := [.X signBit] ++ addrBits.map (fun w => .CX signBit w)
def unflipAddr : Circuit := addrBits.map (fun w => .CX signBit w) ++ [.X signBit]

theorem flipAddr_hp : Classical.HPFree flipAddr := by
  intro g hg
  simp only [flipAddr, List.mem_append, List.mem_singleton, List.mem_map] at hg
  rcases hg with rfl | ⟨_, _, rfl⟩ <;> trivial

theorem unflipAddr_hp : Classical.HPFree unflipAddr := by
  intro g hg
  simp only [unflipAddr, List.mem_append, List.mem_singleton, List.mem_map] at hg
  rcases hg with ⟨_, _, rfl⟩ | rfl <;> trivial

theorem flipAddr_ccx : ccxCount flipAddr = 0 := by decide +kernel

theorem unflipAddr_ccx : ccxCount unflipAddr = 0 := by decide +kernel

theorem flipAddr_wf : CircuitWellFormed flipAddr := by
  intro g hg
  simp only [flipAddr, List.mem_append, List.mem_singleton, List.mem_map] at hg
  rcases hg with rfl | ⟨w, hw, rfl⟩
  · trivial
  · have := mem_addrBits.mp hw
    change signBit ≠ w
    unfold signBit; (try dsimp only [Wire] at *); omega

theorem unflipAddr_wf : CircuitWellFormed unflipAddr := by
  intro g hg
  simp only [unflipAddr, List.mem_append, List.mem_singleton, List.mem_map] at hg
  rcases hg with ⟨w, hw, rfl⟩ | rfl
  · have := mem_addrBits.mp hw
    change signBit ≠ w
    unfold signBit; (try dsimp only [Wire] at *); omega
  · trivial

theorem flipAddr_wires : ∀ w ∈ circuitWires flipAddr, w ∈ bits := by
  intro w hw
  simp only [circuitWires, flipAddr, List.mem_flatMap, List.mem_append, List.mem_singleton,
    List.mem_map] at hw
  obtain ⟨g, hg, hwg⟩ := hw
  rcases hg with rfl | ⟨u, hu, rfl⟩
  · simp only [gateWires, List.mem_singleton] at hwg
    rw [hwg, mem_bits]; unfold signBit; (try dsimp only [Wire] at *); omega
  · simp only [gateWires, List.mem_cons, List.not_mem_nil, or_false] at hwg
    rcases hwg with rfl | rfl
    · rw [mem_bits]; unfold signBit; (try dsimp only [Wire] at *); omega
    · have := mem_addrBits.mp hu; rw [mem_bits]; (try dsimp only [Wire] at *); omega

theorem unflipAddr_wires : ∀ w ∈ circuitWires unflipAddr, w ∈ bits := by
  intro w hw
  simp only [circuitWires, unflipAddr, List.mem_flatMap, List.mem_append, List.mem_singleton,
    List.mem_map] at hw
  obtain ⟨g, hg, hwg⟩ := hw
  rcases hg with ⟨u, hu, rfl⟩ | rfl
  · simp only [gateWires, List.mem_cons, List.not_mem_nil, or_false] at hwg
    rcases hwg with rfl | rfl
    · rw [mem_bits]; unfold signBit; (try dsimp only [Wire] at *); omega
    · have := mem_addrBits.mp hu; rw [mem_bits]; (try dsimp only [Wire] at *); omega
  · simp only [gateWires, List.mem_singleton] at hwg
    rw [hwg, mem_bits]; unfold signBit; (try dsimp only [Wire] at *); omega

theorem run_cxFanout (c : Wire) (ws : List Wire) (hnd : ws.Nodup) (hc : c ∉ ws)
    (s : BasisState) (w : Wire) :
    Classical.run (ws.map (fun u => .CX c u)) s w =
      if w ∈ ws then s w ^^ s c else s w := by
  induction ws generalizing s with
  | nil => simp [Classical.run]
  | cons a ws ih =>
    obtain ⟨ha_not, hnd'⟩ := List.nodup_cons.mp hnd
    have hca : c ≠ a := fun h => hc (by simp [h])
    have hc' : c ∉ ws := fun h => hc (List.mem_cons_of_mem _ h)
    rw [List.map_cons, Classical.run_cons]
    simp only [Classical.applyGate]
    rw [ih hnd' hc' (s[a ↦ s a ^^ s c])]
    by_cases hw : w = a
    · subst hw
      simp [ha_not, upd_same]
    · simp [hw, upd, hca]

theorem flipState_apply (s : BasisState) (w : Wire) :
    Classical.run flipAddr s w =
      if w = signBit then !s signBit
      else if w ∈ addrBits then s w ^^ !s signBit
      else s w := by
  rw [flipAddr, Classical.run_append]
  have hsign : signBit ∉ addrBits := fun h => by
    have := mem_addrBits.mp h; unfold signBit at this; (try dsimp only [Wire] at *); omega
  rw [run_cxFanout signBit addrBits addrBits_nodup hsign]
  simp only [Classical.run_cons, Classical.run_nil, Classical.applyGate, upd_same]
  by_cases hs : w = signBit
  · subst hs; simp [hsign, upd_same]
  · simp [hs, upd, Ne.symm hs]

theorem unflipState_apply (s : BasisState) (w : Wire) :
    Classical.run unflipAddr s w =
      if w = signBit then !s signBit
      else if w ∈ addrBits then s w ^^ s signBit
      else s w := by
  rw [unflipAddr, Classical.run_append]
  have hsign : signBit ∉ addrBits := fun h => by
    have := mem_addrBits.mp h; unfold signBit at this; (try dsimp only [Wire] at *); omega
  simp only [Classical.run_cons, Classical.run_nil, Classical.applyGate]
  by_cases hs : w = signBit
  · subst hs
    rw [upd_same, run_cxFanout signBit addrBits addrBits_nodup hsign]
    simp [hsign]
  · simp only [upd, if_neg hs, run_cxFanout signBit addrBits addrBits_nodup hsign]

theorem unflip_pointWrite_flip (R : Point) (s : BasisState) :
    Classical.run unflipAddr (pointWrite R (Classical.run flipAddr s)) = pointWrite R s := by
  funext w
  rw [unflipState_apply]
  have hsign_not_pt : signBit ∉ pointLogicalWires :=
    bits_not_point signBit (by rw [mem_bits]; unfold signBit; (try dsimp only [Wire] at *); omega)
  have hsign_val : pointWrite R (Classical.run flipAddr s) signBit = !s signBit := by
    rw [pointWrite_frame _ _ _ hsign_not_pt, flipState_apply]; simp
  by_cases hs : w = signBit
  · subst hs
    rw [if_pos rfl, hsign_val, Bool.not_not, pointWrite_frame _ _ _ hsign_not_pt]
  · rw [if_neg hs]
    by_cases ha : w ∈ addrBits
    · have hnotpt : w ∉ pointLogicalWires := bits_not_point w (by
        have := mem_addrBits.mp ha; rw [mem_bits]; (try dsimp only [Wire] at *); omega)
      rw [if_pos ha, pointWrite_frame _ _ _ hnotpt, pointWrite_frame _ _ _ hnotpt,
        hsign_val, flipState_apply, if_neg hs, if_pos ha, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
    · rw [if_neg ha]
      by_cases hp : w ∈ pointLogicalWires
      · simp only [pointWrite, if_pos hp]
      · rw [pointWrite_frame _ _ _ hp, pointWrite_frame _ _ _ hp, flipState_apply, if_neg hs, if_neg ha]

theorem flipState_input (s : BasisState) (hs : Input s) : Input (Classical.run flipAddr s) := by
  have h836_ne : (836 : Wire) ≠ signBit := by decide
  have h836_na : (836 : Wire) ∉ addrBits := by decide
  refine ⟨by rw [flipState_apply, if_neg h836_ne, if_neg h836_na]; exact hs.1, ?_⟩
  intro v hv hnb
  have hvs : v ≠ signBit := fun h => hnb (by rw [h, mem_bits]; unfold signBit; (try dsimp only [Wire] at *); omega)
  have hva : v ∉ addrBits := fun h => hnb (by have := mem_addrBits.mp h; rw [mem_bits]; (try dsimp only [Wire] at *); omega)
  rw [flipState_apply, if_neg hvs, if_neg hva]
  exact hs.2 v hv hnb

theorem tableAddressValue_complement (ws : List Wire) (s : BasisState) :
    tableAddressValue ws (fun w => !s w) = 2 ^ ws.length - 1 - tableAddressValue ws s := by
  induction ws with
  | nil => simp [tableAddressValue]
  | cons w ws ih =>
    have hlt := tableAddressValue_lt ws s
    have hpow : 1 ≤ 2 ^ ws.length := Nat.one_le_pow _ _ (by decide)
    simp only [tableAddressValue, List.length_cons, pow_succ, ih]
    cases s w <;> simp <;> omega

theorem flipState_addr (s : BasisState) :
    tableAddressValue addrBits (Classical.run flipAddr s) =
      if s signBit then tableAddressValue addrBits s else 524287 - tableAddressValue addrBits s := by
  have hsign : signBit ∉ addrBits := by decide
  cases hb : s signBit
  · simp only [Bool.false_eq_true, if_false]
    have hcongr : tableAddressValue addrBits (Classical.run flipAddr s) =
        tableAddressValue addrBits (fun w => !s w) := by
      apply tableAddressValue_congr
      intro w hw
      have hne : w ≠ signBit := fun h => hsign (h ▸ hw)
      rw [flipState_apply, if_neg hne, if_pos hw, hb]
      simp
    rw [hcongr, tableAddressValue_complement, addrBits_length]
    rfl
  · simp only [if_true]
    apply tableAddressValue_congr
    intro w hw
    have hne : w ≠ signBit := fun h => hsign (h ▸ hw)
    rw [flipState_apply, if_neg hne, if_pos hw, hb]
    simp

theorem bits_addr_split (s : BasisState) :
    tableAddressValue bits s =
      tableAddressValue addrBits s + 524288 * (if s signBit then 1 else 0) := by
  rw [bits_eq_append, tableAddressValue_append, addrBits_length]
  simp only [tableAddressValue]
  cases s signBit <;> simp

theorem signed_address_match (coeffs : Fin 524288 → PointCoeff) (Q : Point) (s : BasisState) :
    (if Classical.run flipAddr s signBit then
        -(tablePoint coeffs Q (tableAddressValue addrBits (Classical.run flipAddr s)))
      else
        tablePoint coeffs Q (tableAddressValue addrBits (Classical.run flipAddr s))) =
      signedPoint coeffs Q (tableAddressValue bits s) := by
  have hlt := tableAddressValue_lt addrBits s
  rw [addrBits_length] at hlt
  have hsplit := bits_addr_split s
  have hflipS : Classical.run flipAddr s signBit = !s signBit := by
    rw [flipState_apply]; simp
  rw [hflipS, flipState_addr, signedPoint, hsplit]
  cases hb : s signBit
  · simp only [Bool.not_false, if_true, Bool.false_eq_true, if_false, Nat.mul_zero, Nat.add_zero]
    rw [if_pos (by omega)]
  · simp only [Bool.not_true, Bool.false_eq_true, if_false, if_true, Nat.mul_one]
    rw [if_neg (by omega), show tableAddressValue addrBits s + 524288 - 524288 = tableAddressValue addrBits s by omega]

/-! Conditional modular negation of `point.y` (`580..835`) controlled on `signBit = 874`. -/

def negYLayout : ECDSAAdd.Arithmetic.CompactRecoveryNegateLayout where
  word := List.range' 580 256
  work := List.range' 2 256
  cin := 258
  zero := 259

def negYRaw : ECDSAAdd.Program := negYLayout.reflection signBit (ECDSAAdd.p + 1)
def negYNorm : ECDSAAdd.Program := ECDSAAdd.Baselines.normalizeProgram negYRaw

private theorem negYRaw_def : negYRaw = negYLayout.reflection signBit (ECDSAAdd.p + 1) := rfl
private theorem negYNorm_def : negYNorm = ECDSAAdd.Baselines.normalizeProgram negYRaw := rfl
private theorem negYLayout_word_len : negYLayout.word.length = 256 := by
  rw [negYLayout]; exact List.length_range'
private theorem negYLayout_work_len : negYLayout.work.length = 256 := by
  rw [negYLayout]; exact List.length_range'

attribute [local irreducible] ECDSAAdd.run negYRaw negYNorm

theorem negYLayout_nodup : (negYLayout.wires signBit).Nodup := by
  simp only [ECDSAAdd.Arithmetic.CompactRecoveryNegateLayout.wires, negYLayout, signBit]
  simp only [List.nodup_cons, List.nodup_append, List.mem_cons, List.mem_append, List.mem_range'_1,
    not_or]
  refine ⟨⟨by decide, by decide, by omega, by omega⟩, ⟨by decide, by omega, by omega⟩,
    ⟨by omega, by omega⟩, List.nodup_range', List.nodup_range', fun a ha b hb hab => by subst hab; omega⟩

theorem negYRaw_counts :
    ECDSAAdd.toffoliCount negYRaw = 255 ∧ ECDSAAdd.measurementCount negYRaw = 255 := by
  rw [negYRaw_def]
  have h := negYLayout.reflection_counts signBit (ECDSAAdd.p + 1)
    (negYLayout_word_len.trans negYLayout_work_len.symm) (by rw [negYLayout_word_len]; omega)
  rw [negYLayout_word_len] at h
  exact h

theorem negYNorm_counts :
    ECDSAAdd.toffoliCount negYNorm ≤ 255 ∧ ECDSAAdd.measurementCount negYNorm = 255 := by
  rw [negYNorm_def]
  have ht := (ECDSAAdd.Baselines.normalize_toffoli_exact negYRaw).trans negYRaw_counts.1
  refine ⟨?_, (ECDSAAdd.Baselines.normalize_measurements negYRaw).trans negYRaw_counts.2⟩
  generalize ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram negYRaw) = t at ht ⊢
  generalize ECDSAAdd.Baselines.repeatedControls negYRaw = rc at ht
  omega

theorem negYNorm_meas : Bridge.tmplMeas (WEX.literalT (n := 524288) negYNorm) = 255 :=
  (WEX.literal_meas (n := 524288) negYNorm).trans negYNorm_counts.2

def negYFixed (start : Nat) : Straight 524288 start (start + 255) :=
  WEX.literalFixed negYNorm 255 negYNorm_meas start

theorem negYFixed_wellFormed (start : Nat) : (negYFixed start).WellFormed :=
  WEX.literalFixed_wellFormed negYNorm 255 negYNorm_meas
    (by
      rw [negYNorm_def]
      exact ECDSAAdd.Baselines.normalize_physical negYRaw
        (by rw [negYRaw_def]; exact negYLayout.reflection_physical signBit (ECDSAAdd.p + 1) negYLayout_nodup)) start

theorem negYFixed_credit (start : Nat) : residue (negYFixed start) = 0 ∧ added (negYFixed start) ≤ 255 := by
  unfold negYFixed WEX.literalFixed
  constructor
  · rw [WEXCredit.residue_naive_cast]
    exact WEXCredit.literal_residue _ _
  · rw [WEXCredit.added_naive_cast, WEXCredit.literal_added]
    exact negYNorm_counts.1

theorem negYFixed_added_eq (start : Nat) : added (negYFixed start) = ECDSAAdd.toffoliCount negYNorm := by
  unfold negYFixed WEX.literalFixed
  rw [WEXCredit.added_naive_cast, WEXCredit.literal_added]

theorem negYFixed_support (start : Nat) : straightWires (negYFixed start) ⊆ List.range' 2 1608 := by
  apply WEX.literalFixed_support negYNorm 255 negYNorm_meas (List.range' 2 1608)
  intro w hw
  rw [negYNorm_def, ECDSAAdd.Baselines.normalize_wires, negYRaw_def] at hw
  have h2 := negYLayout.reflection_support signBit (ECDSAAdd.p + 1) hw
  rw [List.mem_toFinset] at h2 ⊢
  simp only [ECDSAAdd.Arithmetic.CompactRecoveryNegateLayout.wires, negYLayout, signBit,
    List.mem_cons, List.mem_append, List.mem_range'_1] at h2
  rw [List.mem_range'_1]
  (try dsimp only [Wire, ECDSAAdd.Wire] at *); omega

theorem negYFixed_slots (start : Nat) : (negYFixed start).gateSlots ≤ 300000 := by
  rw [negYFixed, WEX.literalFixed_slots]
  have h1 := WEX.literal_slot_bound (n := 524288) negYNorm
  have h2 : ECDSAAdd.Challenge.gateSlots negYNorm = ECDSAAdd.Challenge.gateSlots negYRaw := by
    rw [negYNorm_def]; exact ECDSAAdd.Baselines.normalize_slots negYRaw
  have hflip := ECDSAAdd.Baselines.maskedConstant_gateSlots_le signBit negYLayout.word
    (2 ^ negYLayout.word.length - 1)
  have hadd := ECDSAAdd.Baselines.mappedConst_gateSlots_le (some signBit) negYLayout.word
    negYLayout.carries negYLayout.cin (ECDSAAdd.p + 1)
  have hraw : ECDSAAdd.Challenge.gateSlots negYRaw ≤ 100000 := by
    rw [negYRaw_def]
    simp only [ECDSAAdd.Arithmetic.CompactRecoveryNegateLayout.reflection,
      ECDSAAdd.Arithmetic.CompactRecoveryNegateLayout.complement,
      ECDSAAdd.Arithmetic.CompactRecoveryNegateLayout.add,
      ECDSAAdd.Challenge.gateSlots_append]
    rw [negYLayout_word_len] at hflip hadd ⊢
    generalize ECDSAAdd.Challenge.gateSlots (ECDSAAdd.Arithmetic.maskedConstant signBit negYLayout.word (2 ^ 256 - 1)) = gF at hflip ⊢
    generalize ECDSAAdd.Challenge.gateSlots (ECDSAAdd.Arithmetic.mappedConstAdd (some signBit) negYLayout.word negYLayout.carries negYLayout.cin (ECDSAAdd.p + 1)) = gA at hadd ⊢
    omega
  generalize Bridge.tmplSlots (WEX.literalT (n := 524288) negYNorm) = S at h1 ⊢
  generalize ECDSAAdd.Challenge.gateSlots negYNorm = Gn at h1 h2
  generalize ECDSAAdd.Challenge.gateSlots negYRaw = Gr at h2 hraw
  omega

theorem regValue_cons (w : Wire) (ws : List Wire) (s : BasisState) :
    ECDSAAdd.regValue (w :: ws) s = (if s w then 1 else 0) + 2 * ECDSAAdd.regValue ws s := rfl

theorem regValue_eq_boolWordToNat (ws : List Wire) (s : BasisState) :
    ECDSAAdd.regValue ws s = boolWordToNat (wireValues ws s) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rw [regValue_cons, ih]
    cases h : s w <;> simp [wireValues, boolWordToNat, h]

theorem regValue_inj_bits (ws : List Wire) (s t : BasisState)
    (h : ECDSAAdd.regValue ws s = ECDSAAdd.regValue ws t) :
    wireValues ws s = wireValues ws t := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rw [regValue_cons, regValue_cons] at h
    have hbit : s w = t w := by
      cases hs : s w <;> cases ht : t w <;> rw [hs, ht] at h <;> simp at h <;> omega
    have htail : ECDSAAdd.regValue ws s = ECDSAAdd.regValue ws t := by
      rw [hbit] at h; cases ht : t w <;> rw [ht] at h <;> simp at h <;> omega
    change s w :: wireValues ws s = t w :: wireValues ws t
    rw [hbit, ih htail]

theorem order_mul_constantPoint (Q : Point) (hQ : order • Q = 0) (c : PointCoeff) :
    order • constantPoint Q c = 0 := by
  unfold constantPoint
  rw [nsmul_add, smul_comm order, generator_nsmul_eq_zero, nsmul_zero,
    smul_comm order, hQ, nsmul_zero, add_zero]

theorem point_y_ne_zero {x y : Fp} (hP : Secp256k1.curve.toAffine.Nonsingular x y)
    (hord : order • (WeierstrassCurve.Affine.Point.some hP : Point) = 0) : y ≠ 0 := by
  intro hy0
  have hneg : -(WeierstrassCurve.Affine.Point.some hP : Point) = .some hP := by
    apply fig14PointEncoding_injective
    rw [fig14PointEncoding_neg, fig14PointEncoding, encodedNegY, hy0, neg_zero]
  have h2 : 2 • (WeierstrassCurve.Affine.Point.some hP : Point) = 0 := by
    rw [two_nsmul]
    conv_lhs => rhs; rw [← hneg]
    exact add_neg_cancel _
  have hodd : order % 2 = 1 := by norm_num [order]
  have hdiv : order = 2 * (order / 2) + 1 := by omega
  have hzero : (WeierstrassCurve.Affine.Point.some hP : Point) = 0 := by
    have h1 := hord
    rw [hdiv, add_nsmul, mul_nsmul, h2, nsmul_zero, zero_add, one_nsmul] at h1
    exact h1
  cases hzero

theorem pointWrite_y_word (P : Point) (s : BasisState) :
    wireValues (List.range' 580 256) (pointWrite P s) =
      constantBits 256 (fig14PointEncoding P).2.2.val := by
  have h := pointWrite_word P s
  simp only [pointLogicalWires, pointCorrectionX, pointCorrectionYInf, wireValues, List.map_append,
    List.map_cons, List.map_nil, pointCoordinateWord, ← List.append_assoc] at h
  have ha := List.append_inj h (by simp)
  exact (List.append_inj ha.1 (by simp)).2

theorem pointWrite_x_word (P : Point) (s : BasisState) :
    wireValues (List.range' 263 256) (pointWrite P s) =
      constantBits 256 (fig14PointEncoding P).2.1.val := by
  have h := pointWrite_word P s
  simp only [pointLogicalWires, pointCorrectionX, pointCorrectionYInf, wireValues, List.map_append,
    List.map_cons, List.map_nil, pointCoordinateWord, ← List.append_assoc] at h
  have ha := List.append_inj h (by simp)
  exact (List.append_inj ha.1 (by simp)).1

theorem pointWrite_inf_bit (P : Point) (s : BasisState) :
    pointWrite P s 838 = (fig14PointEncoding P).1 := by
  have h := pointWrite_word P s
  simp only [pointLogicalWires, pointCorrectionX, pointCorrectionYInf, wireValues, List.map_append,
    List.map_cons, List.map_nil, pointCoordinateWord, ← List.append_assoc] at h
  have ha := List.append_inj h (by simp)
  simpa using ha.2

theorem eq_of_wireValues_eq {ws : List Wire} {s t : BasisState}
    (h : wireValues ws s = wireValues ws t) : ∀ w ∈ ws, s w = t w := by
  induction ws with
  | nil => intro w hw; cases hw
  | cons a ws ih =>
    simp only [wireValues, List.map_cons, List.cons.injEq] at h
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact h.1
    · exact ih h.2 w hw

def NegYValid (s : BasisState) : Prop :=
  ∃ (P : Point) (t : BasisState), P ≠ 0 ∧ order • P = 0 ∧ s = pointWrite P t ∧
    ∀ w, 2 ≤ w ∧ w < 260 → t w = false

def negYResult (s : BasisState) : BasisState :=
  pointWrite (if s signBit then -(WEX.inputPoint s) else WEX.inputPoint s) s

theorem negY_coherent :
    CoherentlyImplementsOn (WEX.literalSource negYNorm)
      (Finsupp.lmapDomain ℂ ℂ negYResult) NegYValid := by
  apply WEX.literal_coherent
  intro s hs m
  rw [negYNorm_def, ECDSAAdd.Baselines.normalize_run, negYRaw_def]
  obtain ⟨P, t, hPne, hPord, rfl, htclean⟩ := hs
  have hcoord : pointStateCoordinates (pointWrite P t) = fig14PointEncoding P :=
    pointWrite_coordinates P t
  have hinp : WEX.inputPoint (pointWrite P t) = P :=
    WEX.inputPoint_eq (pointWrite P t) P hcoord
  cases P with
  | zero => exact (hPne rfl).elim
  | @some x y hP =>
    have hyne : y ≠ 0 := point_y_ne_zero hP hPord
    have hylt : y.val < ShorECDLP.p := ZMod.val_lt y
    have hypos : 0 < y.val := Nat.pos_of_ne_zero (fun h0 => hyne (by
      rw [← ZMod.natCast_zmod_val y, h0]; rfl))
    have hp_eq : ECDSAAdd.p = ShorECDLP.p := rfl
    have hp_lt : ECDSAAdd.p + 1 < 2 ^ 256 := by norm_num [ECDSAAdd.p]
    have hreg_y : ECDSAAdd.regValue negYLayout.word (pointWrite (.some hP) t) = y.val := by
      rw [regValue_eq_boolWordToNat, negYLayout, pointWrite_y_word]
      simp only [fig14PointEncoding, boolWordToNat_constantBits]
      exact Nat.mod_eq_of_lt (by omega)
    have hreg_work : ECDSAAdd.regValue negYLayout.work (pointWrite (.some hP) t) = 0 := by
      rw [ECDSAAdd.Arithmetic.regValue_zero]
      intro w hw
      simp only [negYLayout, List.mem_range'_1] at hw
      have hnp : w ∉ pointLogicalWires := by
        intro hp
        have hmp := First18.mem_point hp
        (try dsimp only [Wire, ECDSAAdd.Wire] at *); omega
      rw [pointWrite_frame _ _ _ hnp]
      exact htclean w (by (try dsimp only [Wire, ECDSAAdd.Wire] at *); omega)
    have hcin : pointWrite (.some hP) t negYLayout.cin = false := by
      rw [pointWrite_frame _ _ _ (fun hp => by have := First18.mem_point hp; simp only [negYLayout] at this; (try dsimp only [Wire, ECDSAAdd.Wire] at *); omega)]
      exact htclean 258 (by decide)
    have hzero : pointWrite (.some hP) t negYLayout.zero = false := by
      rw [pointWrite_frame _ _ _ (fun hp => by have := First18.mem_point hp; simp only [negYLayout] at this; (try dsimp only [Wire, ECDSAAdd.Wire] at *); omega)]
      exact htclean 259 (by decide)
    have href := negYLayout.reflection_correct signBit negYLayout_nodup
      (negYLayout_word_len.trans negYLayout_work_len.symm) (by rw [negYLayout_word_len]; omega)
      (ECDSAAdd.p + 1) y.val hp_lt (by omega)
      ⟨false, pointWrite (.some hP) t⟩ m hreg_y hreg_work hcin hzero
    apply ECDSAAdd.State.extensionality
    · exact href.1
    · set out : BasisState := (ECDSAAdd.run (negYLayout.reflection signBit (ECDSAAdd.p + 1)) m ⟨false, pointWrite (.some hP) t⟩).basis
      set R : Point := if pointWrite (.some hP) t signBit then -(WeierstrassCurve.Affine.Point.some hP : Point)
        else .some hP
      have hres : negYResult (pointWrite (.some hP) t) = pointWrite R (pointWrite (.some hP) t) := by
        unfold negYResult; rw [hinp]
      rw [hres]
      have hR_x : (fig14PointEncoding R).2.1 = (fig14PointEncoding (.some hP)).2.1 := by
        dsimp only [R]; split_ifs
        · rw [fig14PointEncoding_neg]; rfl
        · rfl
      have hR_inf : (fig14PointEncoding R).1 = (fig14PointEncoding (.some hP)).1 := by
        dsimp only [R]; split_ifs
        · rw [fig14PointEncoding_neg]; rfl
        · rfl
      have hword_eq : negYLayout.word = List.range' 580 256 := rfl
      have hR_y_reg : ECDSAAdd.regValue (List.range' 580 256) (pointWrite R (pointWrite (.some hP) t)) =
          ECDSAAdd.regValue (List.range' 580 256) out := by
        rw [regValue_eq_boolWordToNat, pointWrite_y_word, boolWordToNat_constantBits]
        have hlt256 : (fig14PointEncoding R).2.2.val < 2 ^ 256 := (ZMod.val_lt _).trans (by norm_num [ShorECDLP.p])
        rw [Nat.mod_eq_of_lt hlt256]
        have hout_reg : ECDSAAdd.regValue (List.range' 580 256) out =
            if pointWrite (.some hP) t signBit then ECDSAAdd.p + 1 - 1 - y.val else y.val := by
          rw [← hword_eq]; exact href.2.1
        rw [hout_reg]
        dsimp only [R]
        cases hb : pointWrite (.some hP) t signBit
        · simp [fig14PointEncoding]
        · rw [if_pos rfl, if_pos rfl, fig14PointEncoding_neg]
          dsimp only [encodedNegY, fig14PointEncoding]
          have hneg_val : (-y : Fp).val = ShorECDLP.p - y.val := by
            rw [ZMod.neg_val]; simp [hyne]
          rw [hneg_val]; omega
      have hy_words : wireValues (List.range' 580 256) out =
          wireValues (List.range' 580 256) (pointWrite R (pointWrite (.some hP) t)) :=
        regValue_inj_bits _ _ _ hR_y_reg.symm
      have hx_words : wireValues (List.range' 263 256) (pointWrite (.some hP) t) =
          wireValues (List.range' 263 256) (pointWrite R (pointWrite (.some hP) t)) := by
        rw [pointWrite_x_word, pointWrite_x_word, hR_x]
      have hout_frame : ∀ q, q ∉ List.range' 580 256 → out q = pointWrite (.some hP) t q := by
        rw [← hword_eq]; exact href.2.2
      change out = pointWrite R (pointWrite (.some hP) t)
      funext q
      by_cases hqy : q ∈ List.range' 580 256
      · exact eq_of_wireValues_eq hy_words q hqy
      · rw [hout_frame q hqy]
        by_cases hqp : q ∈ pointLogicalWires
        · rw [pointLogicalWires_eq, xyWires, List.mem_append, List.mem_append, List.mem_singleton] at hqp
          rcases hqp with (hqx | hqy') | rfl
          · exact eq_of_wireValues_eq hx_words q hqx
          · exact (hqy hqy').elim
          · rw [pointWrite_inf_bit, pointWrite_inf_bit, hR_inf]
        · rw [pointWrite_frame _ _ _ hqp, pointWrite_frame _ _ _ hqp, pointWrite_frame _ _ _ hqp]

/-! ### Part 9: Full `First20Signed` program (`flipAddr ++ qromProgram ++ negYFixed ++ unflipAddr`) -/

theorem negYFixed_run (read : ConstantBit 524288 → Bool) (start : Nat) (h : Fin start → Bool) :
    ((negYFixed start).instantiate read h).run = (WEX.literalSource negYNorm).run :=
  WEX.literalFixed_run negYNorm 255 negYNorm_meas start read h

attribute [local irreducible] negYFixed

def program (start : Nat) : Straight 524288 start (start + 193640) :=
  castFinish (by omega)
    ((literalProgram (n := 524288) (s := start) flipAddr).append
      ((qromProgram start).append
        ((negYFixed (start + 193385)).append
          (literalProgram (n := 524288) (s := start + 193385 + 255) unflipAddr))))

theorem literal_append_run {n s e : Nat} (c : Circuit) (q : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    (((literalProgram c).append q).instantiate read history).run =
      ((AdaptiveCircuit.unitary c .done).seq (q.instantiate read history)).run := by
  have hlit : ((literalProgram (n := n) (s := s) c).instantiate read history).run =
      [{ history := List.nil, kraus := Quantum.run c }] := by
    rw [literalProgram_run]
    change ([{ history := List.nil, kraus := LinearMap.id.comp (Quantum.run c) }] : Instrument) = _
    simp
  rw [straight_append_run_history, hlit, AdaptiveCircuit.run_seq, ← literalProgram_run c read history, hlit]
  simp only [Instrument.seq, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [historyAfter_nil]

theorem program_run (read : ConstantBit 524288 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((program start).instantiate read history).run =
      ((AdaptiveCircuit.unitary flipAddr .done).seq
        (((qromProgram start).instantiate read history).seq
          ((WEX.literalSource negYNorm).seq (.unitary unflipAddr .done)))).run := by
  have hneg_unflip : ∀ h',
      (((negYFixed (start + 193385)).append
          (literalProgram (n := 524288) (s := start + 193385 + 255) unflipAddr)).instantiate
        read h').run =
      ((WEX.literalSource negYNorm).seq (.unitary unflipAddr .done)).run := by
    intro h'
    rw [append_run_fixed _ _ _ _ (.unitary unflipAddr .done)
        (fun h'' => literalProgram_run unflipAddr read h''),
      AdaptiveCircuit.run_seq, negYFixed_run read (start + 193385) h', ← AdaptiveCircuit.run_seq]
  rw [program, castFinish_instantiate, literal_append_run, AdaptiveCircuit.run_seq,
    append_run_fixed _ _ _ _ ((WEX.literalSource negYNorm).seq (.unitary unflipAddr .done)) hneg_unflip,
    ← AdaptiveCircuit.run_seq]

theorem coherent_of_run_eq {a b : AdaptiveCircuit} {U : State →ₗ[ℂ] State} {V : BasisState → Prop}
    (hr : a.run = b.run) (hb : CoherentlyImplementsOn b U V) : CoherentlyImplementsOn a U V := by
  unfold CoherentlyImplementsOn at hb ⊢
  rwa [hr]

theorem program_coherent (coeffs : Fin 524288 → PointCoeff) (Q : Point)
    (hQ : order • Q = 0) (hn : ∀ a : Fin 524288, constantPoint Q (coeffs a) ≠ 0)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((program start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (fun s => pointWrite (signedPoint coeffs Q
        (tableAddressValue bits s)) s)) Input := by
  apply coherent_of_run_eq (program_run (readConstant coeffs Q) start history)
  have h1 : CoherentlyImplementsOn (AdaptiveCircuit.unitary flipAddr .done)
      (Finsupp.lmapDomain ℂ ℂ (Classical.run flipAddr)) Input := by
    refine (CoherentlyImplementsOn.unitary flipAddr Input).congrIdeal (fun s _ => ?_)
    rw [First18.lmap_ket, run_ket_agrees_classical flipAddr s flipAddr_hp]
  have h2 : CoherentlyImplementsOn ((qromProgram start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (fun s => pointWrite (tablePoint coeffs Q
        (tableAddressValue addrBits s)) s)) Input :=
    qromProgram_coherent coeffs Q hn start history
  have h3 : CoherentlyImplementsOn (WEX.literalSource negYNorm)
      (Finsupp.lmapDomain ℂ ℂ negYResult) NegYValid := negY_coherent
  have h4 : CoherentlyImplementsOn (AdaptiveCircuit.unitary unflipAddr .done)
      (Finsupp.lmapDomain ℂ ℂ (Classical.run unflipAddr)) (fun _ => True) := by
    refine (CoherentlyImplementsOn.unitary unflipAddr (fun _ => True)).congrIdeal (fun s _ => ?_)
    rw [First18.lmap_ket, run_ket_agrees_classical unflipAddr s unflipAddr_hp]
  have h34 := h3.seq h4 (fun _ _ _ _ => trivial)
  have h234 := h2.seq h34 (fun s hs t ht => by
    rw [First18.lmap_ket] at ht
    have hts : t = pointWrite (tablePoint coeffs Q (tableAddressValue addrBits s)) s := by
      by_contra hne
      exact ht (Finsupp.single_eq_of_ne hne)
    subst hts
    refine ⟨tablePoint coeffs Q (tableAddressValue addrBits s), s,
      hn _, order_mul_constantPoint Q hQ _, rfl, fun w hw => ?_⟩
    exact input_clean s hs w (by (try dsimp only [Wire] at *); omega)
      (Or.inl (by (try dsimp only [Wire] at *); omega)))
  have h1234 := h1.seq h234 (fun s hs t ht => by
    rw [First18.lmap_ket] at ht
    have hts : t = Classical.run flipAddr s := by
      by_contra hne
      exact ht (Finsupp.single_eq_of_ne hne)
    subst hts
    exact flipState_input s hs)
  refine h1234.congrIdeal (fun s _ => ?_)
  simp only [LinearMap.comp_apply, First18.lmap_ket]
  congr 1
  set s1 := Classical.run flipAddr s
  set P1 := tablePoint coeffs Q (tableAddressValue addrBits s1)
  have hsign_np : signBit ∉ pointLogicalWires :=
    bits_not_point signBit (by rw [mem_bits]; unfold signBit; (try dsimp only [Wire] at *); omega)
  have hneg : negYResult (pointWrite P1 s1) =
      pointWrite (if s1 signBit then -P1 else P1) s1 := by
    unfold negYResult
    rw [pointWrite_frame P1 s1 signBit hsign_np,
      WEX.inputPoint_eq _ P1 (pointWrite_coordinates P1 s1), pointWrite_overwrite]
  rw [hneg, unflip_pointWrite_flip, signed_address_match coeffs Q s]

theorem program_residue (start : Nat) : residue (program start) = 0 := by
  rw [program, residue_cast, residue_append, residue_literal_HPFree flipAddr flipAddr_hp,
    residue_append, qromProgram_residue, residue_append, (negYFixed_credit _).1,
    residue_literal_HPFree unflipAddr unflipAddr_hp]

theorem program_added_eq (start : Nat) :
    added (program start) = 193370 + ECDSAAdd.toffoliCount negYNorm := by
  rw [program, added_cast, added_append, added_literal, flipAddr_ccx,
    added_append, qromProgram_added, added_append, negYFixed_added_eq, added_literal, unflipAddr_ccx]
  omega

theorem program_added (start : Nat) : added (program start) ≤ 193625 := by
  rw [program_added_eq]
  have h := negYNorm_counts.1
  omega

theorem program_slots (start : Nat) : (program start).gateSlots ≤ 13100000000 := by
  rw [program, castFinish_gateSlots, Straight.gateSlots_append, Straight.gateSlots_append,
    Straight.gateSlots_append, literalProgram_slots, literalProgram_slots]
  have h1 : flipAddr.length = 20 := by decide
  have h2 : unflipAddr.length = 20 := by decide
  have h3 := qromProgram_slots start
  have h4 := negYFixed_slots (start + 193385)
  omega

theorem bits_subset_drop01 : bits ⊆ List.range' 2 1608 := by
  intro w hw
  have h := mem_bits.mp hw
  rw [List.mem_range'_1]; (try dsimp only [Wire] at *); omega

theorem program_support_drop01 (start : Nat) : straightWires (program start) ⊆ List.range' 2 1608 := by
  rw [program, straightWires_castFinish, straightWires_append, straightWires_append,
    straightWires_append, literalProgram_support, literalProgram_support]
  refine List.append_subset.mpr ⟨fun w hw => bits_subset_drop01 (flipAddr_wires w hw),
    List.append_subset.mpr ⟨qromProgram_support start,
      List.append_subset.mpr ⟨negYFixed_support _, fun w hw => bits_subset_drop01 (unflipAddr_wires w hw)⟩⟩⟩

theorem program_support (start : Nat) : straightWires (program start) ⊆ List.range 1610 := by
  intro w hw
  have h := List.mem_range'_1.mp (program_support_drop01 start hw)
  rw [List.mem_range]; (try dsimp only [Wire] at *); omega

theorem program_wellFormed (start : Nat) : (program start).WellFormed := by
  rw [program, castFinish_wellFormed]
  exact straight_append_wellFormed _ _ (literalProgram_wellFormed flipAddr flipAddr_wf)
    (straight_append_wellFormed _ _ (qromProgram_wellFormed start)
      (straight_append_wellFormed _ _ (negYFixed_wellFormed _)
        (literalProgram_wellFormed unflipAddr unflipAddr_wf)))

def windowGeneric {n : Nat} (rows : Fin 524288 → Fin n) : Single.Window n :=
  ⟨bits.reverse, 193640, fun start => reindexStraight rows (program start)⟩

theorem window_law_generic {n : Nat} (coeffs : Fin n → PointCoeff) (rows : Fin 524288 → Fin n)
    (init : Point → Nat → Point)
    (hnonzero : ∀ Q, order • Q = 0 → Q ≠ 0 → ∀ a : Fin 524288,
      constantPoint Q (coeffs (rows a)) ≠ 0)
    (hcoeff : ∀ Q, order • Q = 0 → Q ≠ 0 → ∀ v, v < 1048576 →
      signedPoint (fun a => coeffs (rows a)) Q v = init Q v) :
    Single.WindowLaw coeffs (windowGeneric rows) (update init) Input := by
  intro Q hQ hn start history
  have hvalid := program_coherent (fun a => coeffs (rows a)) Q hQ (hnonzero Q hQ hn) start history
  have hupdate : (fun s => pointWrite
      (signedPoint (fun a => coeffs (rows a)) Q (tableAddressValue bits s)) s) = update init Q := by
    funext s
    unfold update
    have hbound : tableAddressValue bits s < 1048576 := by
      have hb := tableAddressValue_lt bits s
      simpa only [bits_length] using hb
    rw [hcoeff Q hQ hn _ hbound]
  rw [hupdate] at hvalid
  unfold windowGeneric
  rw [reindexStraight_instantiate,
    readConstant_reindex rows (fun a => coeffs (rows a)) coeffs Q (fun _ => rfl)]
  exact hvalid

theorem window_wellFormed {n : Nat} (rows : Fin 524288 → Fin n) (start : Nat) :
    ((windowGeneric rows).program start).WellFormed := by
  unfold windowGeneric
  exact (reindexStraight_wellFormed rows (program start)).mpr (program_wellFormed start)

theorem window_slots {n : Nat} (rows : Fin 524288 → Fin n) (start : Nat) :
    ((windowGeneric rows).program start).gateSlots ≤ 13100000000 := by
  unfold windowGeneric
  rw [reindexStraight_gateSlots]
  exact program_slots start

theorem window_support {n : Nat} (rows : Fin 524288 → Fin n) (start : Nat) :
    straightWires ((windowGeneric rows).program start) ⊆ List.range 1610 := by
  unfold windowGeneric
  rw [straightWires_reindex]
  exact program_support start

theorem window_credit {n : Nat} (_coeffs : Fin n → PointCoeff) (rows : Fin 524288 → Fin n)
    (_Q : Point) (start : Nat) (_history : Fin start → Bool) :
    added ((windowGeneric rows).program start) ≤ 193625 := by
  unfold windowGeneric
  rw [added_reindex]
  exact program_added start

theorem window_support_drop01 {n : Nat} (rows : Fin 524288 → Fin n) (start : Nat) :
    straightWires ((windowGeneric rows).program start) ⊆ List.range' 2 1608 := by
  unfold windowGeneric
  rw [straightWires_reindex]
  exact program_support_drop01 start

theorem window_added_eq {n : Nat} (rows : Fin 524288 → Fin n) (start : Nat) :
    added ((windowGeneric rows).program start) = 193370 + ECDSAAdd.toffoliCount negYNorm := by
  unfold windowGeneric
  rw [added_reindex]
  exact program_added_eq start

theorem window_residue {n : Nat} (rows : Fin 524288 → Fin n) (start : Nat) :
    residue ((windowGeneric rows).program start) = 0 := by
  unfold windowGeneric
  rw [WEXCredit.residue_reindex]
  exact program_residue start

end
end ShorECDLP.Entrant.First20Signed
end

/-! ### Wave 8B: 5-neighbor zero-T readout (`Readout5`) -/
section
namespace ShorECDLP.Entrant.Readout5
open Quantum ShorECDLP.Challenge ShorECDLP.Entrant.RoundedReadout ShorECDLP.Entrant.NeighborReadout
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def suffix5 (n start width : Nat) (bits : Vector (Fin start) width) :
    Straight n start (start + 2 + 14 * width) :=
  let c := initialCursor bits
  let q := c.lift (2 * (2 * width))
  castFinish (by omega)
    ((constantStep n start).append
      ((positiveWords n 2 (start + 2) width c).append
        ((complementStep n q).append
          (negativeWords n 2 (start + 2 + 2 * (2 * width) + 2 * width) width q.next))))

def wordAt5 {start width : Nat} (bits : Vector (Fin start) width) (j : ℤ) : Vector Nat width :=
  if j = 0 then bits.map Fin.val
  else if j = 1 then sumPositions (start + 2) width
  else if j = 2 then sumPositions (start + 2 + 2 * width) width
  else if j = -1 then sumPositions (start + 2 + 8 * width) width
  else if j = -2 then sumPositions (start + 2 + 12 * width) width
  else bits.map Fin.val

theorem wordAt5_lt {start width : Nat} (bits : Vector (Fin start) width) (j : ℤ)
    (x : Nat) (hx : x ∈ (wordAt5 bits j).toList) : x < start + 2 + 14 * width := by
  unfold wordAt5 at hx
  split_ifs at hx
  · simp only [Vector.toList_map, List.mem_map] at hx
    obtain ⟨k, _, rfl⟩ := hx
    have hk := k.isLt; omega
  · have h := sumPositions_bound (start + 2) width x hx; omega
  · have h := sumPositions_bound (start + 2 + 2 * width) width x hx; omega
  · have h := sumPositions_bound (start + 2 + 8 * width) width x hx; omega
  · have h := sumPositions_bound (start + 2 + 12 * width) width x hx; omega
  · simp only [Vector.toList_map, List.mem_map] at hx
    obtain ⟨k, _, rfl⟩ := hx
    have hk := k.isLt; omega

attribute [local irreducible] positiveWords negativeWords incrementStep complementStep

theorem suffix5_wellFormed (n start width : Nat) (bits : Vector (Fin start) width) :
    (suffix5 n start width bits).WellFormed := by
  unfold suffix5
  rw [castFinish_wellFormed]
  apply straight_append_wellFormed _ _ (constantStep_wellFormed _ _)
  apply straight_append_wellFormed _ _ (positiveWords_wellFormed _ _ _ _ _)
  exact straight_append_wellFormed _ _ (complementStep_wellFormed _ _)
    (negativeWords_wellFormed _ _ _ _ _)

theorem suffix5_slots (n start width : Nat) (bits : Vector (Fin start) width) :
    (suffix5 n start width bits).gateSlots = 7 + 49 * width := by
  simp only [suffix5, castFinish_gateSlots, Straight.gateSlots_append,
    constantStep_slots, positiveWords_slots, complementStep_slots, negativeWords_slots]
  ring

theorem suffix5_t (n start width : Nat) (bits : Vector (Fin start) width)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((suffix5 n start width bits).instantiate read history).tCount = 0 := by
  unfold suffix5
  rw [castFinish_instantiate]
  apply Readout56.append_t_zero _ _ read (constantStep_t _ _ _)
  intro h
  apply Readout56.append_t_zero _ _ read (positiveWords_t _ _ _ _ _ _)
  intro h
  exact Readout56.append_t_zero _ _ read (complementStep_t _ _ _)
    (negativeWords_t _ _ _ _ _ _) h

theorem suffix5_support (n start width : Nat) (bits : Vector (Fin start) width)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((suffix5 n start width bits).instantiate read history).wires ⊆ [0, 1] := by
  unfold suffix5
  rw [castFinish_instantiate]
  apply outer_append_support _ _ read history ([0, 1] : List Wire) (constantStep_support _ _ _ _)
  intro h
  apply outer_append_support _ _ read h ([0, 1] : List Wire) (positiveWords_support _ _ _ _ _ _ _)
  intro h
  exact outer_append_support _ _ read h ([0, 1] : List Wire) (complementStep_support _ _ _ _)
    (fun hh => negativeWords_support _ _ _ _ _ _ hh)

theorem weight4_suffix5 (n start width : Nat) (bits : Vector (Fin start) width) :
    ConditionalCatalyst.weight4 (suffix5 n start width bits) = 0 := by
  simp [suffix5, ConditionalCatalyst.weight4_cast, ConditionalCatalyst.weight4_append,
    ConditionalCatalyst.weight4_positive, ConditionalCatalyst.weight4_negative,
    ConditionalCatalyst.weight4_complement]
  rfl

theorem residue_suffix5 (n start width : Nat) (bits : Vector (Fin start) width) :
    AndGadget.residue (suffix5 n start width bits) = 0 := by
  simp [suffix5, AndGadget.residue_cast, AndGadget.residue_append,
    ApproximatePhase34.residue_positive, ApproximatePhase34.residue_negative,
    ApproximatePhase34.residue_complement]
  rfl

theorem positive_word_mod_gen (w b i : Nat) :
    (i + b) % 2 ^ w = ((((b : Nat) : ℤ) + (i : ℤ)) % (2 ^ w : Nat)).toNat := by
  simp only [← Int.natCast_add, ← Int.natCast_mod, Int.toNat_natCast, Nat.add_comm]

theorem negative_word_mod_gen (w b i : Nat) (hb : b < 2 ^ w) :
    2 ^ w - 1 - (i + (2 ^ w - 1 - b)) % 2 ^ w =
      ((((b : Nat) : ℤ) - (i : ℤ)) % (2 ^ w : Nat)).toNat := by
  set N := 2 ^ w
  have hN : 0 < N := pow_pos (by decide) w
  set r := (i + (N - 1 - b)) % N
  have hr : r < N := Nat.mod_lt _ hN
  have hdiv : N * ((i + (N - 1 - b)) / N) + r = i + (N - 1 - b) := Nat.div_add_mod _ _
  have hdivZ : (N : ℤ) * (((i + (N - 1 - b)) / N : Nat) : ℤ) + (r : ℤ) =
      (i : ℤ) + ((N - 1 - b : Nat) : ℤ) := by exact_mod_cast hdiv
  have hnb : ((N - 1 - b : Nat) : ℤ) = (N : ℤ) - 1 - (b : ℤ) := by omega
  have hnr : ((N - 1 - r : Nat) : ℤ) = (N : ℤ) - 1 - (r : ℤ) := by omega
  have hmod : ((b : ℤ) - (i : ℤ)) % (N : ℤ) = ((N - 1 - r : Nat) : ℤ) := by
    have hsub : (b : ℤ) - (i : ℤ) =
        ((N - 1 - r : Nat) : ℤ) + (N : ℤ) * (-(((i + (N - 1 - b)) / N : Nat) : ℤ)) := by
      linarith
    rw [hsub, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
  rw [hmod, Int.toNat_natCast]

theorem suffix5_branch (n start width : Nat) (bits : Vector (Fin start) width)
    (read : ConstantBit n → Bool) (history : Fin start → Bool)
    (ψ : State) (hψ : SupportedOn CleanReadout ψ) (b : InstrumentBranch)
    (hb : b ∈ ((suffix5 n start width bits).instantiate read history).run)
    (hn : b.kraus ψ ≠ 0) :
    b.kraus ψ = ψ ∧
      (∀ i : Fin 2, readWord (List.ofFn history ++ b.history)
        (sumPositions (start + 2 + i.val * (2 * width)) width).toList =
        some ((i.val + 1 + inputValue bits history) % 2 ^ width)) ∧
      (∀ i : Fin 2, readWord (List.ofFn history ++ b.history)
        (sumPositions (start + 2 + 6 * width + i.val * (4 * width) + 2 * width) width).toList =
        some (2 ^ width - 1 - ((i.val + 1 + (2 ^ width - 1 - inputValue bits history)) % 2 ^ width))) := by
  unfold suffix5 at hb
  rw [castFinish_instantiate] at hb
  obtain ⟨h₁, a, u, ha, hu, he₁, rfl⟩ := straight_append_branch _ _ read history b hb
  have han : a.kraus ψ ≠ 0 := by
    intro h; apply hn; simp only [InstrumentBranch.seq, LinearMap.comp_apply, h, map_zero]
  have hc := constantStep_branch n start read history ψ hψ a ha han
  have hun : u.kraus ψ ≠ 0 := by
    simpa only [InstrumentBranch.seq, LinearMap.comp_apply, hc.1] using hn
  have hcarr := initial_carry bits history h₁ (he₁.trans (by rw [hc.2]))
  have hval := initial_value bits history h₁ a.history he₁
  obtain ⟨h₂, p, v, hp, hv, he₂, rfl⟩ := straight_append_branch _ _ read h₁ u hu
  have hpn : p.kraus ψ ≠ 0 := by
    intro h; apply hun; simp only [InstrumentBranch.seq, LinearMap.comp_apply, h, map_zero]
  have hpos := positiveWords_branch n 2 (start + 2) width (initialCursor bits)
    read h₁ hcarr ψ hψ p hp hpn
  have hvn : v.kraus ψ ≠ 0 := by
    simpa only [InstrumentBranch.seq, LinearMap.comp_apply, hpos.1] using hun
  let q := (initialCursor bits).lift (2 * (2 * width))
  have hqc : h₂ q.carry = true := (lift_carry (initialCursor bits) _ h₁ h₂ p.history he₂).trans hcarr
  have hqv : cursorValue q h₂ = inputValue bits history :=
    (lift_value (initialCursor bits) _ h₁ h₂ p.history he₂).trans hval
  obtain ⟨h₃, c, t, hc', ht, he₃, rfl⟩ := straight_append_branch _ _ read h₂ v hv
  have hcn : c.kraus ψ ≠ 0 := by
    intro h; apply hvn; simp only [InstrumentBranch.seq, LinearMap.comp_apply, h, map_zero]
  have hcomp := complementStep_post n q read h₂ hqc ψ hψ c hc' hcn h₃ he₃
  have htn : t.kraus ψ ≠ 0 := by
    simpa only [InstrumentBranch.seq, LinearMap.comp_apply, hcomp.1] using hvn
  have hneg := negativeWords_branch n 2 (start + 2 + 2 * (2 * width) + 2 * width) width q.next
    read h₃ hcomp.2.1 ψ hψ t ht htn
  have hfull₁ : List.ofFn history ++ (a.seq (p.seq (c.seq t))).history =
      List.ofFn h₁ ++ (p.seq (c.seq t)).history := by
    rw [he₁]; simp only [InstrumentBranch.seq, List.append_assoc]
  have hfull₂ : List.ofFn history ++ (a.seq (p.seq (c.seq t))).history =
      List.ofFn h₂ ++ (c.seq t).history := by
    rw [hfull₁, he₂]; simp only [InstrumentBranch.seq, List.append_assoc]
  have hfull₃ : List.ofFn history ++ (a.seq (p.seq (c.seq t))).history =
      List.ofFn h₃ ++ t.history := by
    rw [hfull₂, he₃]; simp only [InstrumentBranch.seq, List.append_assoc]
  refine ⟨by simp only [InstrumentBranch.seq, LinearMap.comp_apply, hc.1, hpos.1, hcomp.1, hneg.1], ?_, ?_⟩
  · intro i
    rw [hfull₂, readWord_append_left (List.ofFn h₂) (c.seq t).history _ (by
      intro j hj
      have hj' := sumPositions_bound (start + 2 + i.val * (2 * width)) width j hj
      have hi := i.isLt
      have hmul : i.val * (2 * width) ≤ 2 * width := by nlinarith
      simp only [List.length_ofFn]
      omega), he₂]
    simpa only [hval] using hpos.2 i
  · intro i
    rw [hfull₃]
    have hidx : start + 2 + 6 * width + i.val * (4 * width) + 2 * width =
        start + 2 + 2 * (2 * width) + 2 * width + i.val * (4 * width) + 2 * width := by ring
    rw [hidx]
    simpa only [hcomp.2.2, hqv] using hneg.2 i

theorem suffix5_reads (n start width : Nat) (bits : Vector (Fin start) width)
    (read : ConstantBit n → Bool) (history : Fin start → Bool)
    (ψ : State) (hψ : SupportedOn CleanReadout ψ) (b : InstrumentBranch)
    (hb : b ∈ ((suffix5 n start width bits).instantiate read history).run)
    (hn : b.kraus ψ ≠ 0) (j : ℤ) (hj : -2 ≤ j ∧ j ≤ 2) :
    b.kraus ψ = ψ ∧
      readWord (List.ofFn history ++ b.history) (wordAt5 bits j).toList =
        some ((((inputValue bits history : Nat) : ℤ) + j) % (2 ^ width : Nat)).toNat := by
  have hs := suffix5_branch n start width bits read history ψ hψ b hb hn
  refine ⟨hs.1, ?_⟩
  have hcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = -1 ∨ j = -2 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl
  · simp only [wordAt5, ↓reduceIte]
    rw [readWord_append_left (List.ofFn history) b.history _ (by
      intro i hi
      simp only [Vector.toList_map, List.mem_map] at hi
      obtain ⟨k, _, rfl⟩ := hi
      simpa only [List.length_ofFn] using k.isLt), input_read]
    congr 1
    simpa only [Nat.zero_add, Int.natCast_zero, Nat.mod_eq_of_lt (input_lt bits history)] using
      (positive_word_mod_gen width (inputValue bits history) 0)
  · simp only [wordAt5, show (1 : ℤ) ≠ 0 by decide, ↓reduceIte]
    have h := hs.2.1 ⟨0, by decide⟩
    simp only [Nat.zero_mul, Nat.add_zero] at h
    rw [h, positive_word_mod_gen]
    rfl
  · simp only [wordAt5, show (2 : ℤ) ≠ 0 by decide, show (2 : ℤ) ≠ 1 by decide, ↓reduceIte]
    have h := hs.2.1 ⟨1, by decide⟩
    simp only [Nat.one_mul] at h
    rw [h, positive_word_mod_gen]
    rfl
  · simp only [wordAt5, show (-1 : ℤ) ≠ 0 by decide, show (-1 : ℤ) ≠ 1 by decide,
      show (-1 : ℤ) ≠ 2 by decide, ↓reduceIte]
    have h := hs.2.2 ⟨0, by decide⟩
    have hidx : start + 2 + 6 * width + 0 * (4 * width) + 2 * width = start + 2 + 8 * width := by ring
    rw [hidx] at h
    rw [h, negative_word_mod_gen width _ 1 (input_lt bits history)]
    rfl
  · simp only [wordAt5, show (-2 : ℤ) ≠ 0 by decide, show (-2 : ℤ) ≠ 1 by decide,
      show (-2 : ℤ) ≠ 2 by decide, show (-2 : ℤ) ≠ -1 by decide, ↓reduceIte]
    have h := hs.2.2 ⟨1, by decide⟩
    have hidx : start + 2 + 6 * width + 1 * (4 * width) + 2 * width = start + 2 + 12 * width := by ring
    rw [hidx] at h
    rw [h, negative_word_mod_gen width _ 2 (input_lt bits history)]
    rfl

end
end ShorECDLP.Entrant.Readout5
end

/-! ### Wave 8B: 13-trial `(L = 256, R = 206)` sine recovery lower bound (`≥ 9926 / 10000`) -/
section
namespace ShorECDLP.Entrant.SineBounds
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Entrant.SineCircuit ShorECDLP.Entrant.WindowMassSharpProof
open ShorECDLP.Entrant.NeighborReadout ShorECDLP.Entrant.SinAverage ShorECDLP.Entrant.SinAverage261
open ShorECDLP.Paper2607_13816 ShorECDLP.Quantum.OrderFinding ShorECDLP.Quantum.PhaseEstimation
open Finset
open scoped BigOperators
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 300
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

def neighborWord (m b : ℕ) (j : ℤ) : ℕ := ((((b : ℤ) + j) % (2 ^ m : ℕ))).toNat

def goodNeighbor (m r radius : ℕ) (k : Fin r) (x : Fin (2 ^ m)) : Prop :=
  ∃ j : ℤ, -(radius : ℤ) ≤ j ∧ j ≤ (radius : ℤ) ∧ neighborWord m x.val j = (reducedPeak r m k).val

theorem goodNeighbor_mono {m r rad1 rad2 : ℕ} (hle : rad1 ≤ rad2) {k : Fin r} {x : Fin (2 ^ m)}
    (h : goodNeighbor m r rad1 k x) : goodNeighbor m r rad2 k x := by
  obtain ⟨j, h1, h2, hj⟩ := h
  exact ⟨j, by omega, by omega, hj⟩

theorem neighbor_coverage_gen (m r radius : ℕ) (hr : 0 < r) (k : Fin r) (x : Fin (2 ^ m))
    (hc : phiR (2 ^ m) (((2 ^ m : ℕ) : ℝ) * ((k.val : ℝ) / r)) x.val <
        ((radius + 1 : ℕ) : ℝ) -
          (((2 ^ m : ℕ) : ℝ) * ((k.val : ℝ) / r) - round (((2 ^ m : ℕ) : ℝ) * ((k.val : ℝ) / r))) ∨
      phiL (2 ^ m) (((2 ^ m : ℕ) : ℝ) * ((k.val : ℝ) / r)) x.val <
        ((radius + 1 : ℕ) : ℝ) +
          (((2 ^ m : ℕ) : ℝ) * ((k.val : ℝ) / r) - round (((2 ^ m : ℕ) : ℝ) * ((k.val : ℝ) / r)))) :
    goodNeighbor m r radius k x := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  set c : ℝ := ((2 ^ m : ℕ) : ℝ) * ((k.val : ℝ) / r)
  set mm : ℤ := round c
  have hround := abs_le.mp (abs_sub_round c)
  have hkr : (k.val : ℝ) / r < 1 := (div_lt_one hrR).mpr (by exact_mod_cast k.isLt)
  have hc0 : 0 ≤ c := by positivity
  have hcN : c < ((2 ^ m : ℕ) : ℝ) := by
    have : (0 : ℝ) < ((2 ^ m : ℕ) : ℝ) := by positivity
    dsimp only [c]; nlinarith
  have hx0 : (0 : ℝ) ≤ (x.val : ℝ) := Nat.cast_nonneg _
  have hxN : (x.val : ℝ) < ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast x.isLt
  have hrad : (1 : ℝ) ≤ ((radius + 1 : ℕ) : ℝ) := by
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) radius]
  obtain ⟨z, hz1, hz2⟩ : ∃ z : ℤ, -((radius + 1 : ℕ) : ℝ) <
      (mm : ℝ) - ((x.val : ℝ) + z * ((2 ^ m : ℕ) : ℝ)) ∧
      (mm : ℝ) - ((x.val : ℝ) + z * ((2 ^ m : ℕ) : ℝ)) < ((radius + 1 : ℕ) : ℝ) := by
    rcases hc with hc | hc
    · unfold phiR at hc
      split_ifs at hc with h
      · exact ⟨0, by simp only [Int.cast_zero, zero_mul, add_zero]; linarith,
          by simp only [Int.cast_zero, zero_mul, add_zero]; linarith [hround.1, hround.2, hrad]⟩
      · exact ⟨1, by simp only [Int.cast_one, one_mul]; linarith,
          by simp only [Int.cast_one, one_mul]; linarith [hround.1, hround.2, hrad]⟩
    · unfold phiL at hc
      split_ifs at hc with h
      · exact ⟨0, by simp only [Int.cast_zero, zero_mul, add_zero]; linarith [hround.1, hround.2, hrad],
          by simp only [Int.cast_zero, zero_mul, add_zero]; linarith⟩
      · exact ⟨-1, by simp only [Int.cast_neg, Int.cast_one, neg_one_mul]; linarith [hround.1, hround.2, hrad],
          by simp only [Int.cast_neg, Int.cast_one, neg_one_mul]; linarith⟩
  set j : ℤ := mm - ((x.val : ℤ) + z * ((2 ^ m : ℕ) : ℤ))
  have hjR : (j : ℝ) = (mm : ℝ) - ((x.val : ℝ) + z * ((2 ^ m : ℕ) : ℝ)) := by
    dsimp only [j]; push_cast; ring
  have hj1 : -((radius + 1 : ℕ) : ℤ) < j := by
    exact_mod_cast (show -((radius + 1 : ℕ) : ℝ) < (j : ℝ) by rw [hjR]; exact hz1)
  have hj2 : j < ((radius + 1 : ℕ) : ℤ) := by
    exact_mod_cast (show (j : ℝ) < ((radius + 1 : ℕ) : ℝ) by rw [hjR]; exact hz2)
  refine ⟨j, by omega, by omega, ?_⟩
  have he : mm = (reducedPeakRaw r m k : ℤ) := by
    have hc' : c = ((2 ^ m * k.val : ℕ) : ℝ) / r := by dsimp only [c]; push_cast; ring
    rw [show mm = round c from rfl, hc', ShorECDLP.Entrant.RoundedReadout.round_nat_ratio _ r hr]
    simp only [reducedPeakRaw, Nat.mul_assoc]
  have hmod : (reducedPeakRaw r m k : ℤ) % (2 ^ m : ℕ) = ((x.val : ℤ) + j) % (2 ^ m : ℕ) := by
    rw [← he]
    dsimp only [j]
    rw [show (x.val : ℤ) + (mm - ((x.val : ℤ) + z * ((2 ^ m : ℕ) : ℤ))) =
      mm + (-z) * ((2 ^ m : ℕ) : ℤ) by ring, Int.add_mul_emod_self_right]
  have ht := congrArg Int.toNat hmod
  simpa only [neighborWord, reducedPeak, ← Int.natCast_mod, Int.toNat_natCast] using ht.symm

def sineNeighborMass (m r radius : ℕ) (k : Fin r) : ℝ := by
  classical
  exact ∑ x : Fin (2 ^ m), if goodNeighbor m r radius k x then
    Complex.normSq (sinePhaseAmplitude m ((k.val : ℝ) / r) x.val) else 0

theorem sineNeighborMass_mono (m r rad1 rad2 : ℕ) (hle : rad1 ≤ rad2) (k : Fin r) :
    sineNeighborMass m r rad1 k ≤ sineNeighborMass m r rad2 k := by
  classical
  unfold sineNeighborMass
  apply Finset.sum_le_sum; intro x _
  split_ifs with h1 h2
  · exact le_rfl
  · exact (h2 (goodNeighbor_mono hle h1)).elim
  · exact Complex.normSq_nonneg _
  · exact le_rfl

theorem sineNeighborMass_le_one (m : ℕ) (hm : 10 ≤ m) (r radius : ℕ) (k : Fin r) :
    sineNeighborMass m r radius k ≤ 1 := by
  classical
  unfold sineNeighborMass
  calc ∑ x : Fin (2 ^ m), (if goodNeighbor m r radius k x then
        Complex.normSq (sinePhaseAmplitude m ((k.val : ℝ) / r) x.val) else 0)
      ≤ ∑ x : Fin (2 ^ m), Complex.normSq (sinePhaseAmplitude m ((k.val : ℝ) / r) x.val) := by
        apply Finset.sum_le_sum; intro x _
        split_ifs
        · exact le_rfl
        · exact Complex.normSq_nonneg _
    _ = 1 := by
        rw [Fin.sum_univ_eq_sum_range (fun a => Complex.normSq (sinePhaseAmplitude m ((k.val : ℝ) / r) a))]
        exact sinePhaseAmplitude_parseval m hm _

theorem sine_neighbor_mass3_gen (m : ℕ) (hm : 204 ≤ m) (r : ℕ) (hr : 0 < r) (k : Fin r) :
    1 - 136 / 100000 - (900 / 100000 : ℝ) * Real.cos (Real.pi * ((2 ^ m : ℕ) : ℝ) * ((k.val : ℝ) / r)) ^ 2 -
        12 / 1000000 ≤ sineNeighborMass m r 1 k := by
  classical
  set β : ℝ := (k.val : ℝ) / r
  set c : ℝ := ((2 ^ m : ℕ) : ℝ) * β
  set σ : ℝ := c - round c
  have hσ := abs_le.mp (abs_sub_round c)
  have hcos_eq : Real.cos (Real.pi * ((2 ^ m : ℕ) : ℝ) * β) ^ 2 = Real.cos (Real.pi * |σ|) ^ 2 := by
    rw [mul_assoc]; exact cos_sq_eq_abs_round c
  have hstep :
      1 - 136 / 100000 - (900 / 100000 : ℝ) * Real.cos (Real.pi * ((2 ^ m : ℕ) : ℝ) * β) ^ 2 -
        12 / 1000000 ≤
      ∑ b ∈ range (2 ^ m),
        if phiR (2 ^ m) c b < 2 - σ ∨ phiL (2 ^ m) c b < 2 + σ
        then Complex.normSq (sinePhaseAmplitude m β b) else 0 := by
    by_cases hs : 0 ≤ σ
    · have hcirc := sine_circular_mass_two m hm β (2 - σ) (2 + σ) 15 14
        (by linarith) (by linarith) (by push_cast; linarith) (by push_cast; linarith)
        (by push_cast; linarith) (by push_cast; linarith)
      have hbox := right_box_bound σ hs hσ.2
      rw [hcos_eq, abs_of_nonneg hs] at hcirc ⊢
      change _ ≤ ∑ b ∈ range (2 ^ m),
        if phiR (2 ^ m) c b < 2 - σ ∨ phiL (2 ^ m) c b < 2 + σ
        then Complex.normSq (sinePhaseAmplitude m β b) else 0 at hcirc
      linarith
    · have hcirc := sine_circular_mass_two m hm β (2 - σ) (2 + σ) 14 15
        (by linarith) (by linarith) (by push_cast; linarith) (by push_cast; linarith)
        (by push_cast; linarith) (by push_cast; linarith)
      have hbox := right_box_bound (-σ) (by linarith) (by linarith)
      rw [hcos_eq, abs_of_neg (lt_of_not_ge hs)] at hcirc ⊢
      have he1 : 2 - -σ = 2 + σ := by ring
      have he2 : 2 + -σ = 2 - σ := by ring
      rw [he1, he2, add_comm (∑ j ∈ range 15, 1 / ((2 + σ + ↑j) ^ 2 - 1 / 4) ^ 2)] at hbox
      change _ ≤ ∑ b ∈ range (2 ^ m),
        if phiR (2 ^ m) c b < 2 - σ ∨ phiL (2 ^ m) c b < 2 + σ
        then Complex.normSq (sinePhaseAmplitude m β b) else 0 at hcirc
      linarith
  have hfin :
      ∑ b ∈ range (2 ^ m),
        (if phiR (2 ^ m) c b < 2 - σ ∨ phiL (2 ^ m) c b < 2 + σ
        then Complex.normSq (sinePhaseAmplitude m β b) else 0) =
      ∑ b : Fin (2 ^ m),
        if phiR (2 ^ m) c b.val < 2 - σ ∨ phiL (2 ^ m) c b.val < 2 + σ
        then Complex.normSq (sinePhaseAmplitude m β b.val) else 0 :=
    (Fin.sum_univ_eq_sum_range (fun b =>
      if phiR (2 ^ m) c b < 2 - σ ∨ phiL (2 ^ m) c b < 2 + σ
      then Complex.normSq (sinePhaseAmplitude m β b) else 0) (2 ^ m)).symm
  rw [hfin] at hstep
  refine hstep.trans (Finset.sum_le_sum (fun b _ => ?_))
  dsimp only [sineNeighborMass]
  split_ifs with hnear hgood
  · exact le_rfl
  · have hnear' : phiR (2 ^ m) c b.val < ((1 + 1 : ℕ) : ℝ) - σ ∨
        phiL (2 ^ m) c b.val < ((1 + 1 : ℕ) : ℝ) + σ := by
      rcases hnear with h | h
      · exact Or.inl (by push_cast; linarith)
      · exact Or.inr (by push_cast; linarith)
    exact (hgood (neighbor_coverage_gen m r 1 hr k b hnear')).elim
  · exact Complex.normSq_nonneg _
  · exact le_rfl

theorem box5_sum (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    (508 / 10000 : ℝ) *
      ((∑ k ∈ range 14, 1 / ((3 - t + k) ^ 2 - 1 / 4) ^ 2) +
       (∑ k ∈ range 13, 1 / ((3 + t + k) ^ 2 - 1 / 4) ^ 2)) + 68 / 1000000 ≤ 314 / 100000 := by
  have hA := smallSum_antitone 14 ((5 / 2 : ℚ) : ℝ) (3 - t) (by push_cast; norm_num) (by push_cast; linarith)
  have hB := smallSum_antitone 13 ((3 : ℚ) : ℝ) (3 + t) (by push_cast; norm_num) (by push_cast; linarith)
  rw [smallSum_cast] at hA hB
  have hcheck : (508 / 10000 : ℚ) * (smallSumQ 14 (5 / 2) + smallSumQ 13 3) + 68 / 1000000 ≤ 314 / 100000 := by
    norm_num [smallSumQ]
  have hR : (508 / 10000 : ℝ) * (((smallSumQ 14 (5 / 2) : ℚ) : ℝ) + ((smallSumQ 13 3 : ℚ) : ℝ)) +
      68 / 1000000 ≤ 314 / 100000 := by
    have h := Rat.cast_le (K := ℝ).mpr hcheck; push_cast at h; exact h
  linarith

theorem sine_neighbor_mass5_gen (m : ℕ) (hm : 204 ≤ m) (r : ℕ) (hr : 0 < r) (k : Fin r) :
    1 - (314 / 100000 : ℝ) * Real.cos (Real.pi * ((2 ^ m : ℕ) : ℝ) * ((k.val : ℝ) / r)) ^ 2 -
        12 / 1000000 ≤ sineNeighborMass m r 2 k := by
  classical
  set β : ℝ := (k.val : ℝ) / r
  set c : ℝ := ((2 ^ m : ℕ) : ℝ) * β
  set σ : ℝ := c - round c
  have hσ := abs_le.mp (abs_sub_round c)
  have hstep :
      1 - (314 / 100000 : ℝ) * Real.cos (Real.pi * ((2 ^ m : ℕ) : ℝ) * β) ^ 2 -
        12 / 1000000 ≤
      ∑ b ∈ range (2 ^ m),
        if phiR (2 ^ m) c b < 3 - σ ∨ phiL (2 ^ m) c b < 3 + σ
        then Complex.normSq (sinePhaseAmplitude m β b) else 0 := by
    by_cases hs : 0 ≤ σ
    · have hcirc := sine_circular_mass_two m hm β (3 - σ) (3 + σ) 14 13
        (by linarith) (by linarith) (by push_cast; linarith) (by push_cast; linarith)
        (by push_cast; linarith) (by push_cast; linarith)
      have hbox := box5_sum σ hs hσ.2
      have hm0 := mul_le_mul_of_nonneg_left hbox (sq_nonneg (Real.cos (Real.pi * ((2 ^ m : ℕ) : ℝ) * β)))
      change _ ≤ ∑ b ∈ range (2 ^ m),
        if phiR (2 ^ m) c b < 3 - σ ∨ phiL (2 ^ m) c b < 3 + σ
        then Complex.normSq (sinePhaseAmplitude m β b) else 0 at hcirc
      linarith
    · have hcirc := sine_circular_mass_two m hm β (3 - σ) (3 + σ) 13 14
        (by linarith) (by linarith) (by push_cast; linarith) (by push_cast; linarith)
        (by push_cast; linarith) (by push_cast; linarith)
      have hbox := box5_sum (-σ) (by linarith) (by linarith)
      have he1 : 3 - -σ = 3 + σ := by ring
      have he2 : 3 + -σ = 3 - σ := by ring
      rw [he1, he2, add_comm (∑ j ∈ range 14, 1 / ((3 + σ + ↑j) ^ 2 - 1 / 4) ^ 2)] at hbox
      have hm0 := mul_le_mul_of_nonneg_left hbox (sq_nonneg (Real.cos (Real.pi * ((2 ^ m : ℕ) : ℝ) * β)))
      change _ ≤ ∑ b ∈ range (2 ^ m),
        if phiR (2 ^ m) c b < 3 - σ ∨ phiL (2 ^ m) c b < 3 + σ
        then Complex.normSq (sinePhaseAmplitude m β b) else 0 at hcirc
      linarith
  have hfin :
      ∑ b ∈ range (2 ^ m),
        (if phiR (2 ^ m) c b < 3 - σ ∨ phiL (2 ^ m) c b < 3 + σ
        then Complex.normSq (sinePhaseAmplitude m β b) else 0) =
      ∑ b : Fin (2 ^ m),
        if phiR (2 ^ m) c b.val < 3 - σ ∨ phiL (2 ^ m) c b.val < 3 + σ
        then Complex.normSq (sinePhaseAmplitude m β b.val) else 0 :=
    (Fin.sum_univ_eq_sum_range (fun b =>
      if phiR (2 ^ m) c b < 3 - σ ∨ phiL (2 ^ m) c b < 3 + σ
      then Complex.normSq (sinePhaseAmplitude m β b) else 0) (2 ^ m)).symm
  rw [hfin] at hstep
  refine hstep.trans (Finset.sum_le_sum (fun b _ => ?_))
  dsimp only [sineNeighborMass]
  split_ifs with hnear hgood
  · exact le_rfl
  · have hnear' : phiR (2 ^ m) c b.val < ((2 + 1 : ℕ) : ℝ) - σ ∨
        phiL (2 ^ m) c b.val < ((2 + 1 : ℕ) : ℝ) + σ := by
      rcases hnear with h | h
      · exact Or.inl (by push_cast; linarith)
      · exact Or.inr (by push_cast; linarith)
    exact (hgood (neighbor_coverage_gen m r 2 hr k b hnear')).elim
  · exact Complex.normSq_nonneg _
  · exact le_rfl

/-- Elementary center-bin lower bound (`≥ 49 / 100`) whenever `|2^m β - (a + z * 2^m)| ≤ 1 / 2`. -/
theorem sinePhaseAmplitude_peak_lower (m : ℕ) (hm : 10 ≤ m) (β : ℝ) (a : ℕ) (z : ℤ)
    (hdist : |((2 ^ m : ℕ) : ℝ) * β - ((a : ℝ) + (z : ℝ) * ((2 ^ m : ℕ) : ℝ))| ≤ 1 / 2) :
    (49 / 100 : ℝ) ≤ Complex.normSq (sinePhaseAmplitude m β a) := by
  set N := 2 ^ m
  set B := 2 ^ (m - 10)
  have hNpos : 0 < N := pow_pos (by decide) m
  have hBpos : 0 < B := pow_pos (by decide) _
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hBR : (0 : ℝ) < B := by exact_mod_cast hBpos
  have hNB : N = 1024 * B := by
    have : 2 ^ m = 2 ^ 10 * 2 ^ (m - 10) := by rw [← pow_add, Nat.add_sub_cancel' hm]
    simpa [N, B] using this
  have hNBR : (N : ℝ) = 1024 * (B : ℝ) := by exact_mod_cast hNB
  set δ : ℝ := β - (a : ℝ) / N - (z : ℝ)
  have hNδ : |(N : ℝ) * δ| ≤ 1 / 2 := by
    have heq : (N : ℝ) * δ = (N : ℝ) * β - ((a : ℝ) + (z : ℝ) * (N : ℝ)) := by
      dsimp only [δ]; field_simp [hNR.ne']; ring
    rw [heq]; exact hdist
  have hω_eq : eigenvalue (β - (a : ℝ) / N) = eigenvalue δ := by
    have heq : β - (a : ℝ) / N = δ + (z : ℝ) := by dsimp only [δ]; ring
    rw [heq, eigenvalue_add_int]
  set u₀ : ℂ := (-Complex.I) * eigenvalue (-(N : ℝ) * δ / 2)
  have hu₀ : Complex.normSq u₀ = 1 := by
    simp only [u₀, Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_I, eigenvalue_normSq, mul_one]
  have hre_le : (u₀ * sinePhaseAmplitude m β a).re ^ 2 ≤ Complex.normSq (sinePhaseAmplitude m β a) := by
    have hns : Complex.normSq (u₀ * sinePhaseAmplitude m β a) = Complex.normSq (sinePhaseAmplitude m β a) := by
      rw [Complex.normSq_mul, hu₀, one_mul]
    rw [← hns, Complex.normSq_apply, ← sq]
    nlinarith [sq_nonneg (u₀ * sinePhaseAmplitude m β a).im]
  have hre_expr : (u₀ * sinePhaseAmplitude m β a).re =
      (N : ℝ)⁻¹ * ∑ x ∈ range N,
        Real.sqrt 2 * Real.sin (Real.pi * ((x / B : ℕ) : ℝ) / 1024) *
          Real.cos (2 * Real.pi * (δ * ((x : ℝ) - (N : ℝ) / 2))) := by
    have hmul : u₀ * sinePhaseAmplitude m β a =
        ((N : ℝ)⁻¹ : ℂ) * ∑ x ∈ range N,
          (((Real.sqrt 2 * Real.sin (Real.pi * ((x / B : ℕ) : ℝ) / 1024) : ℝ) : ℂ) *
            eigenvalue (δ * ((x : ℝ) - (N : ℝ) / 2))) := by
      unfold sinePhaseAmplitude
      change u₀ * (((N : ℕ) : ℂ)⁻¹ * ∑ x ∈ range N, sineWeight 10 (x / B) * eigenvalue (β - (a : ℝ) / N) ^ x) = _
      rw [← mul_assoc, mul_comm u₀ ((N : ℕ) : ℂ)⁻¹, mul_assoc, Finset.mul_sum]
      simp only [Complex.ofReal_inv, Complex.ofReal_natCast]
      congr 1
      apply Finset.sum_congr rfl; intro x _
      rw [hω_eq, sineWeight_eq_sin, eigenvalue_pow_eq_eigenvalue_mul]
      have harg10 : Real.pi * ((x / B : ℕ) : ℝ) / (2 : ℝ) ^ 10 = Real.pi * ((x / B : ℕ) : ℝ) / 1024 := by
        norm_num
      rw [harg10]
      have heig : eigenvalue (-(N : ℝ) * δ / 2) * eigenvalue ((x : ℝ) * δ) =
          eigenvalue (δ * ((x : ℝ) - (N : ℝ) / 2)) := by
        rw [← eigenvalue_add]; congr 1; ring
      dsimp only [u₀]
      have hI2 : (-Complex.I) * Complex.I = 1 := by simp [Complex.I_sq]
      calc (-Complex.I) * eigenvalue (-(N : ℝ) * δ / 2) *
            (((Real.sqrt 2 : ℝ) : ℂ) * Complex.I * ((Real.sin (Real.pi * ((x / B : ℕ) : ℝ) / 1024) : ℝ) : ℂ) *
              eigenvalue ((x : ℝ) * δ))
          = ((-Complex.I) * Complex.I) *
              (((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sin (Real.pi * ((x / B : ℕ) : ℝ) / 1024) : ℝ) : ℂ)) *
              (eigenvalue (-(N : ℝ) * δ / 2) * eigenvalue ((x : ℝ) * δ)) := by ring
        _ = (((Real.sqrt 2 * Real.sin (Real.pi * ((x / B : ℕ) : ℝ) / 1024) : ℝ) : ℂ) *
              eigenvalue (δ * ((x : ℝ) - (N : ℝ) / 2))) := by
            rw [hI2, one_mul, heig, Complex.ofReal_mul]
    rw [hmul, ← Complex.ofReal_inv, Complex.re_ofReal_mul, Complex.re_sum]
    congr 1
    apply Finset.sum_congr rfl; intro x _
    rw [Complex.re_ofReal_mul]
    congr 1
    unfold eigenvalue
    rw [show Complex.I * ((2 * Real.pi * (δ * ((x : ℝ) - (N : ℝ) / 2)) : ℝ) : ℂ) =
      ((2 * Real.pi * (δ * ((x : ℝ) - (N : ℝ) / 2)) : ℝ) : ℂ) * Complex.I by ring,
      Complex.exp_ofReal_mul_I_re]
  have hcos_lb (x : ℕ) (hx : x ∈ range N) :
      Real.sin (Real.pi * (x : ℝ) / N) ≤ Real.cos (2 * Real.pi * (δ * ((x : ℝ) - (N : ℝ) / 2))) := by
    have hxlt : (x : ℝ) < N := by exact_mod_cast (mem_range.mp hx)
    have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
    set α : ℝ := 2 * Real.pi * (δ * ((x : ℝ) - (N : ℝ) / 2))
    set γ : ℝ := Real.pi * |(x : ℝ) / N - 1 / 2|
    have hhalf : |(x : ℝ) / N - 1 / 2| ≤ 1 / 2 := by
      rw [abs_le]
      have h1 : 0 ≤ (x : ℝ) / N := by positivity
      have h2 : (x : ℝ) / N ≤ 1 := (div_le_one hNR).mpr hxlt.le
      constructor <;> linarith
    have hγ0 : 0 ≤ γ := mul_nonneg Real.pi_pos.le (abs_nonneg _)
    have hγpi : γ ≤ Real.pi / 2 := by dsimp only [γ]; nlinarith [Real.pi_pos]
    have hα_le : |α| ≤ γ := by
      have hα_eq : α = 2 * Real.pi * ((N : ℝ) * δ) * ((x : ℝ) / N - 1 / 2) := by
        dsimp only [α]; field_simp [hNR.ne']
      rw [hα_eq, abs_mul, abs_mul, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
      have h2 : 2 * Real.pi * |(N : ℝ) * δ| ≤ Real.pi := by nlinarith [Real.pi_pos]
      exact mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
    have hanti : Real.cos γ ≤ Real.cos |α| := by
      apply Real.strictAntiOn_cos.antitoneOn
      · exact ⟨abs_nonneg _, hα_le.trans (by linarith [Real.pi_pos])⟩
      · exact ⟨hγ0, by linarith [Real.pi_pos]⟩
      · exact hα_le
    rw [Real.cos_abs] at hanti
    have hcos_γ : Real.cos γ = Real.sin (Real.pi * (x : ℝ) / N) := by
      have h1 : Real.cos γ = Real.cos (Real.pi * ((x : ℝ) / N - 1 / 2)) := by
        have habs : γ = |Real.pi * ((x : ℝ) / N - 1 / 2)| := by
          dsimp only [γ]; rw [abs_mul, abs_of_pos Real.pi_pos]
        rw [habs, Real.cos_abs]
      rw [h1, show Real.pi * ((x : ℝ) / N - 1 / 2) = Real.pi * (x : ℝ) / N - Real.pi / 2 by ring,
        Real.cos_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]
      ring
    linarith
  have hre_ge : Real.sqrt 2 * (508 / 1024 : ℝ) ≤ (u₀ * sinePhaseAmplitude m β a).re := by
    have hreidx :
        (∑ x ∈ range N,
          Real.sqrt 2 * Real.sin (Real.pi * ((x / B : ℕ) : ℝ) / 1024) *
            Real.cos (2 * Real.pi * (δ * ((x : ℝ) - (N : ℝ) / 2)))) =
        ∑ u ∈ range 1024, ∑ j ∈ range B,
          Real.sqrt 2 * Real.sin (Real.pi * (((u * B + j) / B : ℕ) : ℝ) / 1024) *
            Real.cos (2 * Real.pi * (δ * (((u * B + j : ℕ) : ℝ) - (N : ℝ) / 2))) := by
      rw [congrArg range hNB]
      exact range_mul_sum 1024 B _
    rw [hre_expr, hreidx]
    have hinner (u : ℕ) (hu : u ∈ range 1024) :
        (B : ℝ) * (Real.sqrt 2 * Real.sin (Real.pi * (u : ℝ) / 1024) *
            (Real.sin (Real.pi * (u : ℝ) / 1024) - Real.pi / 1024)) ≤
          ∑ j ∈ range B,
            Real.sqrt 2 * Real.sin (Real.pi * (((u * B + j) / B : ℕ) : ℝ) / 1024) *
              Real.cos (2 * Real.pi * (δ * (((u * B + j : ℕ) : ℝ) - (N : ℝ) / 2))) := by
      have hult : u < 1024 := mem_range.mp hu
      have hsin_nn : 0 ≤ Real.sin (Real.pi * (u : ℝ) / 1024) := by
        apply Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
        have : (u : ℝ) ≤ 1024 := by exact_mod_cast hult.le
        nlinarith [Real.pi_pos]
      have hterm (j : ℕ) (hj : j ∈ range B) :
          Real.sqrt 2 * Real.sin (Real.pi * (u : ℝ) / 1024) *
              (Real.sin (Real.pi * (u : ℝ) / 1024) - Real.pi / 1024) ≤
            Real.sqrt 2 * Real.sin (Real.pi * (((u * B + j) / B : ℕ) : ℝ) / 1024) *
              Real.cos (2 * Real.pi * (δ * (((u * B + j : ℕ) : ℝ) - (N : ℝ) / 2))) := by
        have hjlt : j < B := mem_range.mp hj
        have hdiv : (u * B + j) / B = u := by
          rw [Nat.mul_comm u B, Nat.mul_add_div hBpos, Nat.div_eq_of_lt hjlt, Nat.add_zero]
        rw [hdiv]
        have hxmem : u * B + j ∈ range N := by
          rw [mem_range, hNB]
          have : u + 1 ≤ 1024 := hult
          nlinarith
        have hcos := hcos_lb (u * B + j) hxmem
        have hlip := Real.abs_sin_sub_sin_le (Real.pi * ((u * B + j : ℕ) : ℝ) / N) (Real.pi * (u : ℝ) / 1024)
        have hdiff : Real.pi * ((u * B + j : ℕ) : ℝ) / N - Real.pi * (u : ℝ) / 1024 =
            Real.pi * (j : ℝ) / (1024 * (B : ℝ)) := by
          rw [hNBR]; push_cast; field_simp [hBR.ne']; ring
        have hdiff_abs : |Real.pi * ((u * B + j : ℕ) : ℝ) / N - Real.pi * (u : ℝ) / 1024| =
            Real.pi * (j : ℝ) / (1024 * (B : ℝ)) := by
          rw [hdiff, abs_of_nonneg (by positivity)]
        have hdiff_le : Real.pi * (j : ℝ) / (1024 * (B : ℝ)) ≤ Real.pi / 1024 := by
          have hjB : (j : ℝ) ≤ B := by exact_mod_cast hjlt.le
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [Real.pi_pos]
        have hsin_lb : Real.sin (Real.pi * (u : ℝ) / 1024) - Real.pi / 1024 ≤
            Real.sin (Real.pi * ((u * B + j : ℕ) : ℝ) / N) := by
          rw [hdiff_abs] at hlip
          linarith [(abs_le.mp hlip).1]
        have hcoef_nn : 0 ≤ Real.sqrt 2 * Real.sin (Real.pi * (u : ℝ) / 1024) := by positivity
        exact mul_le_mul_of_nonneg_left (hsin_lb.trans hcos) hcoef_nn
      have hs := Finset.sum_le_sum hterm
      simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hs
    have hsum1 := Finset.sum_le_sum hinner
    rw [← Finset.mul_sum] at hsum1
    have hsin2 : ∑ u ∈ range 1024, Real.sin (Real.pi * (u : ℝ) / 1024) ^ 2 = 512 := by
      have h := sineWeight_sum_normSq
      have hterm : ∀ u ∈ range 1024, Complex.normSq (sineWeight 10 u) =
          2 * Real.sin (Real.pi * (u : ℝ) / 1024) ^ 2 := by
        intro u _; rw [sineWeight_normSq]; norm_num
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum] at h
      linarith
    have hsin1 : ∑ u ∈ range 1024, Real.sin (Real.pi * (u : ℝ) / 1024) ≤ 1024 := by
      calc ∑ u ∈ range 1024, Real.sin (Real.pi * (u : ℝ) / 1024)
          ≤ ∑ _u ∈ range 1024, (1 : ℝ) := Finset.sum_le_sum (fun u _ => Real.sin_le_one _)
        _ = 1024 := by simp
    have hpi4 : Real.pi < 4 := by linarith [Real.pi_lt_d6]
    have hsum_eval : ∑ u ∈ range 1024,
        Real.sqrt 2 * Real.sin (Real.pi * (u : ℝ) / 1024) *
          (Real.sin (Real.pi * (u : ℝ) / 1024) - Real.pi / 1024) =
        Real.sqrt 2 * ((∑ u ∈ range 1024, Real.sin (Real.pi * (u : ℝ) / 1024) ^ 2) -
          (Real.pi / 1024) * ∑ u ∈ range 1024, Real.sin (Real.pi * (u : ℝ) / 1024)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro u _; ring
    rw [hsum_eval, hsin2] at hsum1
    have hmid : Real.sqrt 2 * 508 ≤
        Real.sqrt 2 * (512 - Real.pi / 1024 * ∑ u ∈ range 1024, Real.sin (Real.pi * (u : ℝ) / 1024)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg 2)
      have h1 : Real.pi / 1024 * ∑ u ∈ range 1024, Real.sin (Real.pi * (u : ℝ) / 1024) ≤
          Real.pi / 1024 * 1024 := mul_le_mul_of_nonneg_left hsin1 (by positivity)
      linarith
    have hscale := mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left hmid hBR.le).trans hsum1) (inv_nonneg.mpr hNR.le)
    have hlhs : (N : ℝ)⁻¹ * ((B : ℝ) * (Real.sqrt 2 * 508)) = Real.sqrt 2 * (508 / 1024 : ℝ) := by
      rw [hNBR]; field_simp [hBR.ne']
    linarith
  have hsq : (Real.sqrt 2 * (508 / 1024 : ℝ)) ^ 2 ≤ (u₀ * sinePhaseAmplitude m β a).re ^ 2 :=
    pow_le_pow_left₀ (by positivity) hre_ge 2
  have hnum : (49 / 100 : ℝ) ≤ (Real.sqrt 2 * (508 / 1024 : ℝ)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]; norm_num
  linarith

theorem sine_neighbor_mass1_gen (m : ℕ) (hm : 10 ≤ m) (r : ℕ) (hr : 0 < r) (k : Fin r) :
    (49 / 100 : ℝ) ≤ sineNeighborMass m r 0 k := by
  classical
  set a : Fin (2 ^ m) := reducedPeak r m k
  have hgood_a : goodNeighbor m r 0 k a := by
    refine ⟨0, by omega, by omega, ?_⟩
    simp only [neighborWord, Int.cast_zero, add_zero, ← Int.natCast_mod, Int.toNat_natCast,
      Nat.mod_eq_of_lt a.isLt]
    rfl
  have hsingle : Complex.normSq (sinePhaseAmplitude m ((k.val : ℝ) / r) a.val) ≤ sineNeighborMass m r 0 k := by
    unfold sineNeighborMass
    have hmem : a ∈ (Finset.univ : Finset (Fin (2 ^ m))) := Finset.mem_univ a
    have hle := Finset.single_le_sum (f := fun x : Fin (2 ^ m) =>
        if goodNeighbor m r 0 k x then Complex.normSq (sinePhaseAmplitude m ((k.val : ℝ) / r) x.val) else 0)
      (fun x _ => by dsimp only; split_ifs; exact Complex.normSq_nonneg _; exact le_rfl) hmem
    simpa only [if_pos hgood_a] using hle
  set z : ℤ := ((reducedPeakRaw r m k / 2 ^ m : ℕ) : ℤ)
  have hdiv : reducedPeakRaw r m k = a.val + (reducedPeakRaw r m k / 2 ^ m) * 2 ^ m := by
    have h := (Nat.div_add_mod (reducedPeakRaw r m k) (2 ^ m)).symm
    dsimp only [a, reducedPeak]
    linarith [Nat.mul_comm (2 ^ m) (reducedPeakRaw r m k / 2 ^ m)]
  have hround : round (((2 ^ m : ℕ) : ℝ) * ((k.val : ℝ) / r)) = (reducedPeakRaw r m k : ℤ) := by
    have hc' : ((2 ^ m : ℕ) : ℝ) * ((k.val : ℝ) / r) = ((2 ^ m * k.val : ℕ) : ℝ) / r := by push_cast; ring
    rw [hc', ShorECDLP.Entrant.RoundedReadout.round_nat_ratio _ r hr]
    simp only [reducedPeakRaw, Nat.mul_assoc]
  have hdist : |((2 ^ m : ℕ) : ℝ) * ((k.val : ℝ) / r) - ((a.val : ℝ) + (z : ℝ) * ((2 ^ m : ℕ) : ℝ))| ≤ 1 / 2 := by
    have hcast : ((a.val : ℝ) + (z : ℝ) * ((2 ^ m : ℕ) : ℝ)) =
        (round (((2 ^ m : ℕ) : ℝ) * ((k.val : ℝ) / r)) : ℝ) := by
      rw [hround]
      have hR : ((reducedPeakRaw r m k : ℕ) : ℝ) =
          (a.val : ℝ) + ((reducedPeakRaw r m k / 2 ^ m : ℕ) : ℝ) * ((2 ^ m : ℕ) : ℝ) := by
        exact_mod_cast hdiv
      dsimp only [z]
      rw [Int.cast_natCast, Int.cast_natCast]
      linarith
    rw [hcast]
    exact abs_sub_round _
  exact (sinePhaseAmplitude_peak_lower m hm ((k.val : ℝ) / r) a.val z hdist).trans hsingle

theorem nearestNumerator_reducedPeak_256 (k : Fin order) :
    ShorECDLP.Challenge.nearestNumerator order 256 (reducedPeak order 256 k).val = k.val := by
  have hord_lt : order < 2 ^ 256 := by norm_num [order]
  have hord_pos : 0 < order := order_prime.pos
  have hk_lt : k.val < order := k.isLt
  have hraw_lt : reducedPeakRaw order 256 k < 2 ^ 256 := by
    unfold reducedPeakRaw
    apply (Nat.div_lt_iff_lt_mul (by omega)).mpr
    have : k.val + 1 ≤ order := hk_lt
    nlinarith
  have hval : (reducedPeak order 256 k).val = reducedPeakRaw order 256 k := by
    simp only [reducedPeak, Nat.mod_eq_of_lt hraw_lt]
  rw [hval]
  set m := reducedPeakRaw order 256 k
  have h1 : 2 * order * m ≤ 2 * 2 ^ 256 * k.val + order := by
    have h := Nat.div_mul_le_self (2 * 2 ^ 256 * k.val + order) (2 * order)
    dsimp only [m, reducedPeakRaw]
    linarith
  have h2 : 2 * 2 ^ 256 * k.val + order < 2 * order * (m + 1) := by
    have h := Nat.lt_mul_div_succ (2 * 2 ^ 256 * k.val + order) (by omega : 0 < 2 * order)
    dsimp only [m, reducedPeakRaw]
    linarith
  unfold ShorECDLP.Challenge.nearestNumerator
  have hNpos : 0 < 2 * 2 ^ 256 := by positivity
  have hlo : 2 * 2 ^ 256 * k.val ≤ 2 * order * m + 2 ^ 256 := by linarith
  have hhi : 2 * order * m + 2 ^ 256 < 2 * 2 ^ 256 * (k.val + 1) := by linarith
  have hd1 : k.val ≤ (2 * order * m + 2 ^ 256) / (2 * 2 ^ 256) :=
    (Nat.le_div_iff_mul_le hNpos).mpr (by linarith)
  have hd2 : (2 * order * m + 2 ^ 256) / (2 * 2 ^ 256) < k.val + 1 :=
    (Nat.div_lt_iff_lt_mul hNpos).mpr (by linarith)
  omega

def params256 : DecoderParams := ⟨256, 206, by decide, by decide, by decide, by decide⟩

def offsets13 : List (ℤ × ℤ) :=
  [(-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1),
   (-2, 0), (2, 0), (0, -2), (0, 2)]

theorem offsets13_length : offsets13.length = 13 := rfl

theorem offsets13_bounds : ∀ p ∈ offsets13, (-2 ≤ p.1 ∧ p.1 ≤ 2) ∧ (-2 ≤ p.2 ∧ p.2 ≤ 2) := by
  decide

def pairRecovered256 (d a b : ℕ) : Bool :=
  decide (∃ p ∈ offsets13, (d : ZMod order) ∈
    fixedCandidates params256 (neighborWord 256 a p.1) (neighborWord 206 b p.2))

theorem pairRecovered256_of_pair (d : ℕ) (k : Fin order) (hk : k.val ≠ 0)
    (a : Fin (2 ^ 256)) (b : Fin (2 ^ 206)) (i j : ℤ)
    (hp : (i, j) ∈ offsets13)
    (ha : neighborWord 256 a.val i = (reducedPeak order 256 k).val)
    (hb : neighborWord 206 b.val j = (reducedPeak order 206 ⟨d * k.val % order, Nat.mod_lt _ order_prime.pos⟩).val) :
    pairRecovered256 d a.val b.val = true := by
  classical
  haveI : Fact (Nat.Prime order) := ⟨order_prime⟩
  have hk0 : ((k.val : ℕ) : ZMod order) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    exact hk (Nat.eq_zero_of_dvd_of_lt h k.isLt)
  apply decide_eq_true
  refine ⟨(i, j), hp, ?_⟩
  unfold fixedCandidates
  apply Finset.mem_image.mpr
  refine ⟨d * k.val % order, ?_, ?_⟩
  · change d * k.val % order ∈ wrappedNumeratorCandidates order 206 (neighborWord 206 b.val j)
    rw [hb]
    exact reducedPeak_mem_candidates order 206 _
  · change ((d * k.val % order : ℕ) : ZMod order) *
        (ShorECDLP.Challenge.nearestNumerator order 256 (neighborWord 256 a.val i) : ZMod order)⁻¹ = d
    rw [ha, nearestNumerator_reducedPeak_256 k]
    simp only [ZMod.natCast_mod, Nat.cast_mul]
    field_simp

theorem cross13_lower (p1 p3 p5 q1 q3 q5 : ℝ)
    (hp1 : 49 / 100 ≤ p1) (hp3 : p3 ≤ p5) (hp5 : p3 ≤ 1)
    (hq1 : 49 / 100 ≤ q1) (hq3 : q3 ≤ q5) (hq5 : q3 ≤ 1) :
    1 - (51 / 100 : ℝ) * ((1 - p3) + (1 - q3)) - (49 / 100 : ℝ) * ((1 - p5) + (1 - q5)) ≤
      p3 * q3 + (p5 - p3) * q1 + p1 * (q5 - q3) := by
  nlinarith

/-- Main Wave 8B ideal recovery lower bound (`≥ 9924 / 10000`) for `(L = 256, R = 206, 13 trials)`. -/
theorem sine_pair_success_256_206 (Q : Point) (d : ℕ) (hn : Q ≠ 0) (hd : Q = d • G) :
    (9924 / 10000 : ℝ) ≤ ∑ a : Fin (2 ^ 256), ∑ b : Fin (2 ^ 206),
      if pairRecovered256 d a.val b.val then sinePairMass order 256 206 d (a, b) else 0 := by
  classical
  let r := order
  have hr : r.Prime := order_prime
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr.pos
  have hrinv : (0 : ℝ) ≤ (r : ℝ)⁻¹ := by positivity
  let kR : Fin r → Fin r := fun k => ⟨d * k.val % r, Nat.mod_lt _ hr.pos⟩
  let A : Fin r → Fin (2 ^ 256) → ℝ := fun k a =>
    Complex.normSq (sinePhaseAmplitude 256 ((k.val : ℝ) / r) a.val)
  let B : Fin r → Fin (2 ^ 206) → ℝ := fun k b =>
    Complex.normSq (sinePhaseAmplitude 206 (((kR k).val : ℝ) / r) b.val)
  let G1 : Fin r → Fin (2 ^ 256) → Fin (2 ^ 206) → Prop := fun k a b =>
    goodNeighbor 256 r 1 k a ∧ goodNeighbor 206 r 1 (kR k) b
  let G2 : Fin r → Fin (2 ^ 256) → Fin (2 ^ 206) → Prop := fun k a b =>
    (goodNeighbor 256 r 2 k a ∧ ¬ goodNeighbor 256 r 1 k a) ∧ goodNeighbor 206 r 0 (kR k) b
  let G3 : Fin r → Fin (2 ^ 256) → Fin (2 ^ 206) → Prop := fun k a b =>
    goodNeighbor 256 r 0 k a ∧ (goodNeighbor 206 r 2 (kR k) b ∧ ¬ goodNeighbor 206 r 1 (kR k) b)
  let good : Fin r → Fin (2 ^ 256) → Fin (2 ^ 206) → Prop := fun k a b =>
    k.val ≠ 0 ∧ (G1 k a b ∨ G2 k a b ∨ G3 k a b)
  let F : Fin r → Fin (2 ^ 256) → Fin (2 ^ 206) → ℝ := fun k a b =>
    if good k a b then A k a * B k b else 0
  let cL : Fin r → ℝ := fun k => Real.cos (Real.pi * ((2 ^ 256 : ℕ) : ℝ) * ((k.val : ℝ) / r)) ^ 2
  let cR : Fin r → ℝ := fun k => Real.cos (Real.pi * ((2 ^ 206 : ℕ) : ℝ) * (((kR k).val : ℝ) / r)) ^ 2
  have hrec : ∀ k a b, good k a b → pairRecovered256 d a.val b.val = true := by
    intro k a b ⟨hk, h⟩
    rcases h with ⟨⟨i, hi1, hi2, hi⟩, ⟨j, hj1, hj2, hj⟩⟩ |
      ⟨⟨⟨i, hi1, hi2, hi⟩, _⟩, ⟨j, hj1, hj2, hj⟩⟩ |
      ⟨⟨i, hi1, hi2, hi⟩, ⟨⟨j, hj1, hj2, hj⟩, _⟩⟩
    · have hp : (i, j) ∈ offsets13 := by
        have hi' : i = -1 ∨ i = 0 ∨ i = 1 := by omega
        have hj' : j = -1 ∨ j = 0 ∨ j = 1 := by omega
        rcases hi' with rfl | rfl | rfl <;> rcases hj' with rfl | rfl | rfl <;> decide
      exact pairRecovered256_of_pair d k hk a b i j hp hi hj
    · have hp : (i, j) ∈ offsets13 := by
        have hi' : i = -2 ∨ i = -1 ∨ i = 0 ∨ i = 1 ∨ i = 2 := by omega
        have hj' : j = 0 := by omega
        subst hj'
        rcases hi' with rfl | rfl | rfl | rfl | rfl <;> decide
      exact pairRecovered256_of_pair d k hk a b i j hp hi hj
    · have hp : (i, j) ∈ offsets13 := by
        have hi' : i = 0 := by omega
        have hj' : j = -2 ∨ j = -1 ∨ j = 0 ∨ j = 1 ∨ j = 2 := by omega
        subst hi'
        rcases hj' with rfl | rfl | rfl | rfl | rfl <;> decide
      exact pairRecovered256_of_pair d k hk a b i j hp hi hj
  have step1 :
      ∑ a : Fin (2 ^ 256), ∑ b : Fin (2 ^ 206), (r : ℝ)⁻¹ * ∑ k : Fin r, F k a b ≤
        ∑ a : Fin (2 ^ 256), ∑ b : Fin (2 ^ 206),
          if pairRecovered256 d a.val b.val then sinePairMass r 256 206 d (a, b) else 0 := by
    apply Finset.sum_le_sum; intro a _
    apply Finset.sum_le_sum; intro b _
    by_cases hp : pairRecovered256 d a.val b.val = true
    · rw [if_pos hp]
      unfold sinePairMass
      apply mul_le_mul_of_nonneg_left _ hrinv
      apply Finset.sum_le_sum; intro k _
      dsimp only [F, A, B, kR]
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
    · rw [if_neg hp]
      have hz : ∀ k, F k a b = 0 := by
        intro k; dsimp only [F]; rw [if_neg]
        intro hg; exact hp (hrec k a b hg)
      simp [hz]
  have step2 :
      (r : ℝ)⁻¹ * ∑ k : Fin r, ∑ a : Fin (2 ^ 256), ∑ b : Fin (2 ^ 206), F k a b =
        ∑ a : Fin (2 ^ 256), ∑ b : Fin (2 ^ 206), (r : ℝ)⁻¹ * ∑ k : Fin r, F k a b := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro a _
    rw [Finset.sum_comm]
  have step3 (k : Fin r) :
      (if k.val = 0 then (0 : ℝ) else (1 - 24 / 1000000 - 13872 / 10000000 : ℝ)) -
        cL k * (6129 / 1000000) - cR k * (6129 / 1000000) ≤
      ∑ a : Fin (2 ^ 256), ∑ b : Fin (2 ^ 206), F k a b := by
    have hcL0 : 0 ≤ cL k := sq_nonneg _
    have hcR0 : 0 ≤ cR k := sq_nonneg _
    by_cases hk : k.val = 0
    · rw [if_pos hk]
      have h0 : 0 ≤ ∑ a : Fin (2 ^ 256), ∑ b : Fin (2 ^ 206), F k a b :=
        Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => by
          dsimp only [F, A, B]; split_ifs
          · exact mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
          · exact le_rfl))
      linarith
    · rw [if_neg hk]
      have hsplit : ∀ a b, F k a b =
          (if G1 k a b then A k a * B k b else 0) +
          (if G2 k a b then A k a * B k b else 0) +
          (if G3 k a b then A k a * B k b else 0) := by
        intro a b
        dsimp only [F, good]
        by_cases h1 : G1 k a b
        · have hn2 : ¬ G2 k a b := fun h => h.1.2 h1.1
          have hn3 : ¬ G3 k a b := fun h => h.2.2 h1.2
          simp [hk, h1, hn2, hn3]
        · by_cases h2 : G2 k a b
          · have hn3 : ¬ G3 k a b := fun h => h2.1.2 (goodNeighbor_mono (by decide) h.1)
            simp [hk, h1, h2, hn3]
          · by_cases h3 : G3 k a b <;> simp [hk, h1, h2, h3]
      have hsum_eq : (∑ a : Fin (2 ^ 256), ∑ b : Fin (2 ^ 206), F k a b) =
          sineNeighborMass 256 r 1 k * sineNeighborMass 206 r 1 (kR k) +
          (sineNeighborMass 256 r 2 k - sineNeighborMass 256 r 1 k) * sineNeighborMass 206 r 0 (kR k) +
          sineNeighborMass 256 r 0 k * (sineNeighborMass 206 r 2 (kR k) - sineNeighborMass 206 r 1 (kR k)) := by
        simp_rw [hsplit, Finset.sum_add_distrib]
        have hS1 : (∑ a : Fin (2 ^ 256), ∑ b : Fin (2 ^ 206), if G1 k a b then A k a * B k b else 0) =
            sineNeighborMass 256 r 1 k * sineNeighborMass 206 r 1 (kR k) := by
          rw [sineNeighborMass, sineNeighborMass, Finset.sum_mul_sum]
          apply Finset.sum_congr rfl; intro a _
          apply Finset.sum_congr rfl; intro b _
          dsimp only [G1, A, B]; rw [ite_zero_mul_ite_zero]
        have hdiffL : (∑ a : Fin (2 ^ 256), if goodNeighbor 256 r 2 k a ∧ ¬ goodNeighbor 256 r 1 k a then A k a else 0) =
            sineNeighborMass 256 r 2 k - sineNeighborMass 256 r 1 k := by
          rw [sineNeighborMass, sineNeighborMass, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl; intro a _
          dsimp only [A]
          by_cases h1 : goodNeighbor 256 r 1 k a
          · have h2 := goodNeighbor_mono (by decide : 1 ≤ 2) h1
            simp [h1, h2]
          · by_cases h2 : goodNeighbor 256 r 2 k a <;> simp [h1, h2]
        have hdiffR : (∑ b : Fin (2 ^ 206), if goodNeighbor 206 r 2 (kR k) b ∧ ¬ goodNeighbor 206 r 1 (kR k) b then B k b else 0) =
            sineNeighborMass 206 r 2 (kR k) - sineNeighborMass 206 r 1 (kR k) := by
          rw [sineNeighborMass, sineNeighborMass, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl; intro b _
          dsimp only [B]
          by_cases h1 : goodNeighbor 206 r 1 (kR k) b
          · have h2 := goodNeighbor_mono (by decide : 1 ≤ 2) h1
            simp [h1, h2]
          · by_cases h2 : goodNeighbor 206 r 2 (kR k) b <;> simp [h1, h2]
        have hS2 : (∑ a : Fin (2 ^ 256), ∑ b : Fin (2 ^ 206), if G2 k a b then A k a * B k b else 0) =
            (sineNeighborMass 256 r 2 k - sineNeighborMass 256 r 1 k) * sineNeighborMass 206 r 0 (kR k) := by
          rw [← hdiffL, sineNeighborMass, Finset.sum_mul_sum]
          apply Finset.sum_congr rfl; intro a _
          apply Finset.sum_congr rfl; intro b _
          dsimp only [G2, A, B]; rw [ite_zero_mul_ite_zero]
        have hS3 : (∑ a : Fin (2 ^ 256), ∑ b : Fin (2 ^ 206), if G3 k a b then A k a * B k b else 0) =
            sineNeighborMass 256 r 0 k * (sineNeighborMass 206 r 2 (kR k) - sineNeighborMass 206 r 1 (kR k)) := by
          rw [← hdiffR, sineNeighborMass, Finset.sum_mul_sum]
          apply Finset.sum_congr rfl; intro a _
          apply Finset.sum_congr rfl; intro b _
          dsimp only [G3, A, B]; rw [ite_zero_mul_ite_zero]
        rw [hS1, hS2, hS3]
      rw [hsum_eq]
      have hp1 := sine_neighbor_mass1_gen 256 (by decide) r hr.pos k
      have hp3 := sine_neighbor_mass3_gen 256 (by decide) r hr.pos k
      have hp5 := sine_neighbor_mass5_gen 256 (by decide) r hr.pos k
      have hq1 := sine_neighbor_mass1_gen 206 (by decide) r hr.pos (kR k)
      have hq3 := sine_neighbor_mass3_gen 206 (by decide) r hr.pos (kR k)
      have hq5 := sine_neighbor_mass5_gen 206 (by decide) r hr.pos (kR k)
      have hcross := cross13_lower
        (sineNeighborMass 256 r 0 k) (sineNeighborMass 256 r 1 k) (sineNeighborMass 256 r 2 k)
        (sineNeighborMass 206 r 0 (kR k)) (sineNeighborMass 206 r 1 (kR k)) (sineNeighborMass 206 r 2 (kR k))
        hp1 (sineNeighborMass_mono 256 r 1 2 (by decide) k) (sineNeighborMass_le_one 256 (by decide) r 1 k)
        hq1 (sineNeighborMass_mono 206 r 1 2 (by decide) (kR k)) (sineNeighborMass_le_one 206 (by decide) r 1 (kR k))
      dsimp only [cL, cR] at *
      linarith
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => step3 k)
  have hcount : (∑ k : Fin r, if k.val = 0 then (0 : ℝ) else (1 - 24 / 1000000 - 13872 / 10000000 : ℝ)) =
      ((r : ℝ) - 1) * (1 - 24 / 1000000 - 13872 / 10000000) := by
    have hz : (∑ k : Fin r, if k.val = 0 then (1 : ℝ) else 0) = 1 := by
      rw [Fin.sum_univ_eq_sum_range (fun k => if k = 0 then (1 : ℝ) else 0)]
      simp [hr.pos]
    calc
      _ = ∑ k : Fin r, ((1 - 24 / 1000000 - 13872 / 10000000 : ℝ) -
            (1 - 24 / 1000000 - 13872 / 10000000) * (if k.val = 0 then 1 else 0)) := by
        apply Finset.sum_congr rfl; intro k _; split_ifs <;> ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hz]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        ring
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hcount, ← Finset.sum_mul, ← Finset.sum_mul] at hsum
  have hcL_sum : ∑ k : Fin r, cL k = (r : ℝ) / 2 := by
    have h := sum_cos_sq_eq r (2 ^ 256) hr.pos (order_not_dvd_pow2 256)
    simpa only [cL, mul_div_assoc] using h
  have hcR_sum : ∑ k : Fin r, cR k = (r : ℝ) / 2 := by
    have hndvd : ¬ r ∣ 2 ^ 206 * d := by
      intro h
      rcases hr.dvd_mul.mp h with h1 | h2
      · exact order_not_dvd_pow2 206 h1
      · exact order_not_dvd_of_ne_zero Q d hn hd h2
    have h := sum_cos_sq_eq r (2 ^ 206 * d) hr.pos hndvd
    rw [← h]
    apply Finset.sum_congr rfl; intro k _
    dsimp only [cR, kR]
    rw [← mul_div_assoc, cos_sq_mod r (2 ^ 206) (d * k.val) hr.pos]
    have harg : Real.pi * ((2 ^ 206 * d : ℕ) : ℝ) * (k.val : ℝ) / (r : ℝ) =
        Real.pi * ((2 ^ 206 : ℕ) : ℝ) * ((d * k.val : ℕ) : ℝ) / (r : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_mul]; ring
    rw [harg]
  rw [hcL_sum, hcR_sum] at hsum
  have hlower := mul_le_mul_of_nonneg_left hsum hrinv
  have heval : (r : ℝ)⁻¹ * (((r : ℝ) - 1) * (1 - 24 / 1000000 - 13872 / 10000000) -
      (r : ℝ) / 2 * (6129 / 1000000) - (r : ℝ) / 2 * (6129 / 1000000)) =
      (1 - 1 / (r : ℝ)) * (1 - 24 / 1000000 - 13872 / 10000000) - 6129 / 1000000 := by
    field_simp [hrR.ne']; ring
  rw [heval, step2] at hlower
  have hrbig_nat : 1000000 ≤ r := by dsimp only [r]; norm_num [order]
  have hrbig : (1000000 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hrbig_nat
  have hinv : 1 / (r : ℝ) ≤ (1 : ℝ) / 1000000 := one_div_le_one_div_of_le (by norm_num) hrbig
  have hnum : (9924 / 10000 : ℝ) ≤ (1 - 1 / (r : ℝ)) * (1 - 24 / 1000000 - 13872 / 10000000) -
      6129 / 1000000 := by linarith
  exact hnum.trans (hlower.trans step1)

theorem decoder_budget256 : 13 * (2 * (order / 2 ^ 206 + 2)) ≤ 56 * (2 ^ 49 + 2) := by
  norm_num [order]

end
end ShorECDLP.Entrant.SineBounds
end
