import ShorECDLP.Submission.«2607_13816».EEA.WordNat
import ShorECDLP.Submission.«2607_13816».Challenge.OuterResources
import ShorECDLP.Framework.Quantum.AdaptiveHadamard
import ShorECDLP.Submission.Entrant.Streaming.Semantics
import ShorECDLP.Submission.Entrant.Streaming.Resources
import ShorECDLP.Submission.«2607_13816».Window.SignedAddress
import ShorECDLP.Submission.«2607_13816».Challenge.Outer
import ShorECDLP.Submission.«2607_13816».Challenge.Reindex
import ShorECDLP.Challenge.Decoder
import ShorECDLP.Challenge.Resources


open ShorECDLP.Entrant.ZeroAdaptive

/-! Deterministic classical rounding encoded as ordinary recorded gates.
All gates are Clifford gates on two previously reset wires. -/
namespace ShorECDLP.Entrant.RoundedReadout
open ShorECDLP Quantum ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816.ChallengeMigration

/-- One full-adder step: record the next carry, then the sum bit.
Input and carry controls refer only to existing measurement records. -/
def addStep {n start : Nat} (carry bit : Fin start) : Straight n start (start + 2) :=
  .recordGate carry true (.X 0)
    (.recordGate bit true (.CX 0 1)
      (.gate (.literal (.H 1))
        (.measure 1
          (.recordGate carry.castSucc true (.X 0)
            (.recordGate bit.castSucc true (.X 1)
              (.recordGate carry.castSucc true (.X 1)
                (.gate (.literal (.H 1)) (.measure 1 .done))))))))

def liftTwo {start : Nat} (i : Fin start) : Fin (start + 2) :=
  ⟨i.val, by omega⟩

/-- Carry begins with the highest discarded Fourier bit. -/
def addWord {n : Nat} : (start : Nat) → Fin start → (bits : List (Fin start)) →
    Straight n start (start + 2 * bits.length)
  | start, carry, [] => .done
  | start, carry, bit :: bits => castFinish (by simp; omega)
      ((addStep carry bit).append
        (addWord (start + 2) ⟨start, by omega⟩ (bits.map liftTwo)))
termination_by _ _ bits => bits.length

def carryBits : Bool → List Bool → List Bool
  | _, [] => []
  | carry, bit :: bits => (carry && bit) :: (bit ^^ carry) :: carryBits (carry && bit) bits

def sumBits : Bool → List Bool → List Bool
  | _, [] => []
  | carry, bit :: bits => (bit ^^ carry) :: sumBits (carry && bit) bits

theorem addStep_wellFormed {n start : Nat} (carry bit : Fin start) :
    (addStep (n := n) carry bit).WellFormed := by
  simp [addStep, Straight.WellFormed, TemplateGate.WellFormed, Gate.WellFormed]

theorem addStep_slots {n start : Nat} (carry bit : Fin start) :
    (addStep (n := n) carry bit).gateSlots = 7 := rfl

theorem addStep_t {n start : Nat} (carry bit : Fin start)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((addStep carry bit).instantiate read history).tCount = 0 := by
  cases hc : history carry <;> cases hb : history bit <;>
    simp [addStep, Straight.instantiate, TemplateGate.instantiate, AdaptiveCircuit.tCount,
      ShorECDLP.tCount, tCost, hc, hb]

theorem addWord_wellFormed {n : Nat} : ∀ (start : Nat) (carry : Fin start) (bits : List (Fin start)),
    (addWord (n := n) start carry bits).WellFormed
  | _, _, [] => by simp [addWord, Straight.WellFormed]
  | start, carry, bit :: bits => by
      rw [addWord, castFinish_wellFormed]
      exact straight_append_wellFormed _ _ (addStep_wellFormed _ _)
        (addWord_wellFormed (start + 2) _ _)
termination_by _ _ bits => bits.length

theorem addWord_slots {n : Nat} : ∀ (start : Nat) (carry : Fin start) (bits : List (Fin start)),
    (addWord (n := n) start carry bits).gateSlots = 7 * bits.length
  | _, _, [] => by simp [addWord, Straight.gateSlots]
  | start, carry, bit :: bits => by
      rw [addWord, castFinish_gateSlots, Straight.gateSlots_append, addStep_slots,
        addWord_slots (start + 2)]
      simp
      omega
termination_by _ _ bits => bits.length

noncomputable section

/-- An H before the protected X reset records the computational-basis bit. -/
theorem zRecord_ket (w : Wire) (outcome : Bool) (s : BasisState) :
    xResetKraus w outcome (applyGate (.H w) (ket s)) =
      if outcome = s w then ket (s[w ↦ false]) else 0 := by
  have hh := applyGate_adjoint_applyGate (.H w) (by trivial) (ket s)
  change applyGate (.H w) (applyGate (.H w) (ket s)) = ket s at hh
  rw [xResetKraus, LinearMap.comp_apply, LinearMap.comp_apply, hh, projectZ_ket]
  by_cases he : outcome = s w
  · rw [if_pos he.symm, if_pos he]
    cases outcome with
    | false =>
      simp only [resetCircuit, Bool.false_eq_true, ↓reduceIte, Quantum.run, LinearMap.id_apply]
      congr 1
      funext i
      by_cases hi : i = w
      · subst i; simp [he.symm]
      · simp [upd, hi]
    | true => simp [resetCircuit, Quantum.run, onKet, he.symm]
  · rw [if_neg (Ne.symm he), if_neg he, map_zero]


theorem run_unitary_data (gs : Circuit) (p : AdaptiveCircuit) :
    (AdaptiveCircuit.unitary gs p).run = p.run.map (fun b =>
      (⟨b.history, b.kraus.comp (Quantum.run gs)⟩ : InstrumentBranch)) := rfl

theorem run_measure_data (w : Wire) (p q : AdaptiveCircuit) :
    (AdaptiveCircuit.xMeasureReset w p q).run =
      p.run.map (fun b => (⟨false :: b.history, b.kraus.comp (xResetKraus w false)⟩ : InstrumentBranch)) ++
      q.run.map (fun b => (⟨true :: b.history, b.kraus.comp (xResetKraus w true)⟩ : InstrumentBranch)) := rfl

theorem run_done_data : AdaptiveCircuit.done.run = [⟨[], LinearMap.id⟩] := rfl

theorem update_twice (s : BasisState) (w : Wire) (a b : Bool) :
    s[w ↦ a][w ↦ b] = s[w ↦ b] := by
  funext i
  by_cases h : i = w <;> simp [upd, h]

theorem updates_commute01 (s : BasisState) (a b : Bool) :
    s[0 ↦ a][1 ↦ b] = s[1 ↦ b][0 ↦ a] := by
  funext i
  by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;> simp [upd, h0, h1]

def andMap (carry bit out : Bool) : State →ₗ[ℂ] State :=
  (xResetKraus 1 out).comp ((applyGate (.H 1)).comp
    ((Quantum.run (if bit then [.CX 0 1] else [])).comp
      (Quantum.run (if carry then [.X 0] else []))))

def sumMap (carry bit out : Bool) : State →ₗ[ℂ] State :=
  (xResetKraus 1 out).comp ((applyGate (.H 1)).comp
    ((Quantum.run (if carry then [.X 1] else [])).comp
      ((Quantum.run (if bit then [.X 1] else [])).comp
        (Quantum.run (if carry then [.X 0] else [])))))

theorem run_singleton_map (g : Gate) : Quantum.run [g] = applyGate g := by
  ext ψ; rfl

theorem run_nil_map : Quantum.run [] = LinearMap.id := rfl

theorem branch_ext (a b : InstrumentBranch) (hh : a.history = b.history)
    (hk : ∀ ψ, a.kraus ψ = b.kraus ψ) : a = b := by
  cases a
  cases b
  cases hh
  congr 1
  exact LinearMap.ext hk

attribute [local irreducible] xResetKraus applyGate Quantum.run

@[irreducible] def stepTail (carry bit : Bool) : AdaptiveCircuit :=
  .unitary (if carry then [.X 0] else [])
    (.unitary (if bit then [.X 1] else [])
      (.unitary (if carry then [.X 1] else [])
        (.unitary [.H 1] (.xMeasureReset 1 .done .done))))

@[irreducible] def stepSource (carry bit : Bool) : AdaptiveCircuit :=
  .unitary (if carry then [.X 0] else [])
    (.unitary (if bit then [.CX 0 1] else [])
      (.unitary [.H 1] (.xMeasureReset 1 (stepTail carry bit) (stepTail carry bit))))

theorem addStep_instantiate {n start : Nat} (carry bit : Fin start)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    (addStep carry bit).instantiate read history = stepSource (history carry) (history bit) := by
  simp only [addStep, Straight.instantiate, Fin.lastCases_castSucc, TemplateGate.instantiate,
    stepSource, stepTail]

theorem two_record_run (w : Wire) (A B C D E F H : Circuit) :
    (AdaptiveCircuit.unitary A (.unitary B (.unitary C (.xMeasureReset w
      (.unitary D (.unitary E (.unitary F (.unitary H (.xMeasureReset w .done .done)))))
      (.unitary D (.unitary E (.unitary F (.unitary H (.xMeasureReset w .done .done))))))))).run =
    let first (x : Bool) := (xResetKraus w x).comp ((Quantum.run C).comp ((Quantum.run B).comp (Quantum.run A)))
    let last (y : Bool) := (xResetKraus w y).comp ((Quantum.run H).comp ((Quantum.run F).comp
      ((Quantum.run E).comp (Quantum.run D))))
    show Instrument from [⟨[false,false], (last false).comp (first false)⟩,
     ⟨[false,true], (last true).comp (first false)⟩,
     ⟨[true,false], (last false).comp (first true)⟩,
     ⟨[true,true], (last true).comp (first true)⟩] := by
  rfl

theorem stepSource_run (carry bit : Bool) :
    (stepSource carry bit).run =
      [⟨[false,false], (sumMap carry bit false).comp
        (andMap carry bit false)⟩,
       ⟨[false,true], (sumMap carry bit true).comp
        (andMap carry bit false)⟩,
       ⟨[true,false], (sumMap carry bit false).comp
        (andMap carry bit true)⟩,
       ⟨[true,true], (sumMap carry bit true).comp
        (andMap carry bit true)⟩] := by
  have h := two_record_run 1 (if carry then [.X 0] else [])
    (if bit then [.CX 0 1] else []) ([.H 1])
    (if carry then [.X 0] else []) (if bit then [.X 1] else [])
    (if carry then [.X 1] else []) ([.H 1])
  simpa only [stepSource, stepTail, andMap, sumMap, run_singleton_map] using h


theorem addStep_run {n start : Nat} (carry bit : Fin start)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((addStep carry bit).instantiate read history).run =
      [⟨[false,false], (sumMap (history carry) (history bit) false).comp
        (andMap (history carry) (history bit) false)⟩,
       ⟨[false,true], (sumMap (history carry) (history bit) true).comp
        (andMap (history carry) (history bit) false)⟩,
       ⟨[true,false], (sumMap (history carry) (history bit) false).comp
        (andMap (history carry) (history bit) true)⟩,
       ⟨[true,true], (sumMap (history carry) (history bit) true).comp
        (andMap (history carry) (history bit) true)⟩] := by
  rw [addStep_instantiate, stepSource_run]


theorem andMap_ket (carry bit out : Bool) (s : BasisState)
    (hs0 : s 0 = false) (hs1 : s 1 = false) :
    andMap carry bit out (ket s) =
      if out = (carry && bit) then ket (s[0 ↦ carry]) else 0 := by
  have h0 : s[0 ↦ false] = s := by funext i; by_cases h : i = 0 <;> simp [upd, h, hs0]
  have h1 : s[1 ↦ false] = s := by funext i; by_cases h : i = 1 <;> simp [upd, h, hs1]
  cases carry <;> cases bit <;> cases out <;>
    simp only [andMap, LinearMap.comp_apply, Bool.false_eq_true, Bool.true_eq_false,
      ↓reduceIte, run_nil, run_singleton, applyGate_X_ket, applyGate_CX_ket,
      zRecord_ket, hs0, hs1, h0, h1, upd_same, update_twice, updates_commute01,
      Bool.false_and, Bool.true_and, Bool.xor_false,
      Bool.xor_true, Bool.not_false,
      upd_other _ _ _ (by decide : (1 : Nat) ≠ 0)]

theorem sumMap_ket (carry bit out : Bool) (s : BasisState)
    (hs0 : s 0 = false) (hs1 : s 1 = false) :
    sumMap carry bit out (ket (s[0 ↦ carry])) =
      if out = (bit ^^ carry) then ket s else 0 := by
  have h0 : s[0 ↦ false] = s := by funext i; by_cases h : i = 0 <;> simp [upd, h, hs0]
  have h1 : s[1 ↦ false] = s := by funext i; by_cases h : i = 1 <;> simp [upd, h, hs1]
  cases carry <;> cases bit <;> cases out <;>
    simp only [sumMap, LinearMap.comp_apply, Bool.false_eq_true, Bool.true_eq_false,
      ↓reduceIte, run_nil, run_singleton, applyGate_X_ket, zRecord_ket,
      hs1, h0, h1, upd_same, update_twice, Bool.xor_false, Bool.xor_true,
      Bool.not_false, Bool.not_true]


def CleanReadout (s : BasisState) : Prop := s 0 = false ∧ s 1 = false

theorem stepMap_state (carry bit x y : Bool) (ψ : State) (hψ : SupportedOn CleanReadout ψ) :
    sumMap carry bit y (andMap carry bit x ψ) =
      if x = (carry && bit) ∧ y = (bit ^^ carry) then ψ else 0 := by
  let L := (sumMap carry bit y).comp (andMap carry bit x)
  let c : ℂ := if x = (carry && bit) ∧ y = (bit ^^ carry) then 1 else 0
  have h : BranchCoherentOn LinearMap.id CleanReadout (⟨[], L⟩ : InstrumentBranch) c := by
    intro s hs
    change sumMap carry bit y (andMap carry bit x (ket s)) = c • ket s
    rw [andMap_ket _ _ _ s hs.1 hs.2]
    by_cases hx : x = (carry && bit)
    · rw [if_pos hx, sumMap_ket _ _ _ s hs.1 hs.2]
      simp only [c, hx, true_and]
      split_ifs <;> simp
    · rw [if_neg hx, map_zero]
      simp [c, hx]
  have hs := h.on_supported hψ
  change sumMap carry bit y (andMap carry bit x ψ) = c • ψ at hs
  rw [hs]
  dsimp only [c]
  split_ifs <;> simp

theorem addStep_branch {n start : Nat} (carry bit : Fin start)
    (read : ConstantBit n → Bool) (history : Fin start → Bool)
    (ψ : State) (hψ : SupportedOn CleanReadout ψ) (b : InstrumentBranch)
    (hb : b ∈ ((addStep carry bit).instantiate read history).run)
    (hn : b.kraus ψ ≠ 0) :
    b.kraus ψ = ψ ∧ b.history = [history carry && history bit, history bit ^^ history carry] := by
  rw [addStep_run] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  all_goals
    simp only [LinearMap.comp_apply, stepMap_state _ _ _ _ ψ hψ] at hn ⊢
    split_ifs at hn with h
    · simp only [if_pos h]
      exact ⟨True.intro, by rw [← h.1, ← h.2]⟩
    · exact (hn rfl).elim


theorem addWord_branch {n : Nat} : ∀ (start : Nat) (carry : Fin start)
    (bits : List (Fin start)) (read : ConstantBit n → Bool) (history : Fin start → Bool)
    (ψ : State) (_hψ : SupportedOn CleanReadout ψ) (b : InstrumentBranch),
    b ∈ ((addWord start carry bits).instantiate read history).run → b.kraus ψ ≠ 0 →
    b.kraus ψ = ψ ∧ b.history = carryBits (history carry) (bits.map history)
  | _, _, [], _, _, _, _, b, hb, _ => by
      simp only [addWord, Straight.instantiate, run_done_data, List.mem_singleton] at hb
      subst b
      simp [carryBits]
  | start, carry, bit :: bits, read, history, ψ, hψ, b, hb, hn => by
      rw [addWord, castFinish_instantiate] at hb
      obtain ⟨mid, a, c, ha, hc, he, rfl⟩ := straight_append_branch _ _ read history b hb
      have han : a.kraus ψ ≠ 0 := by
        intro h
        apply hn
        simp only [InstrumentBranch.seq, LinearMap.comp_apply, h, map_zero]
      obtain ⟨hastate, hahist⟩ := addStep_branch carry bit read history ψ hψ a ha han
      have hcn : c.kraus ψ ≠ 0 := by
        simpa only [InstrumentBranch.seq, LinearMap.comp_apply, hastate] using hn
      have hi := addWord_branch (start + 2) ⟨start, by omega⟩ (bits.map liftTwo)
        read mid ψ hψ c hc hcn
      have hold (i : Fin start) : mid (liftTwo i) = history i := by
        have h := congrArg (fun xs : List Bool => xs[i.val]?) he
        dsimp only at h
        have hlt : i.val < start + 2 := by omega
        rw [List.getElem?_append_left (by simp)] at h
        simpa only [List.getElem?_ofFn, i.isLt, hlt, ↓reduceDIte,
          Option.some.injEq, liftTwo] using h
      have hcarry : mid ⟨start, by omega⟩ = (history carry && history bit) := by
        rw [hahist] at he
        have h := congrArg (fun xs : List Bool => xs[start]?) he
        dsimp only at h
        have hlt : start < start + 2 := by omega
        rw [List.getElem?_append_right (by simp)] at h
        simpa only [List.getElem?_ofFn, hlt, ↓reduceDIte, List.length_ofFn, Nat.sub_self,
          List.getElem?_cons_zero, Option.some.injEq] using h
      have hbits : (bits.map liftTwo).map mid = bits.map history := by
        rw [List.map_map]
        apply List.map_congr_left
        intro i _
        exact hold i
      constructor
      · simpa only [InstrumentBranch.seq, LinearMap.comp_apply, hastate] using hi.1
      · simp only [InstrumentBranch.seq, hahist, hi.2, hcarry, hbits,
          List.map_cons, carryBits, List.cons_append, List.nil_append]
termination_by _ _ bits => bits.length

theorem addWord_t {n : Nat} : ∀ (start : Nat) (carry : Fin start) (bits : List (Fin start))
    (read : ConstantBit n → Bool) (history : Fin start → Bool),
    ((addWord start carry bits).instantiate read history).tCount = 0
  | _, _, [], _, _ => by simp [addWord, Straight.instantiate, AdaptiveCircuit.tCount]
  | start, carry, bit :: bits, read, history => by
      rw [addWord, castFinish_instantiate]
      apply Nat.eq_zero_of_le_zero
      have h := outer_append_t_le (addStep carry bit) (addWord (start + 2) ⟨start, by omega⟩ (bits.map liftTwo))
        read history 0 (fun h => le_of_eq (addWord_t _ _ _ read h))
      simpa only [addStep_t, Nat.add_zero] using h
termination_by _ _ bits => bits.length

end
end ShorECDLP.Entrant.RoundedReadout
namespace ShorECDLP.Entrant.RoundedReadout
open ShorECDLP.Paper2607_13816

theorem sumBits_eq_increment (carry : Bool) (bits : List Bool) :
    sumBits carry bits = incrementBits carry bits := by
  induction bits generalizing carry with
  | nil => rfl
  | cons bit bits ih => simp only [sumBits, incrementBits, ih, Bool.and_comm]

theorem sumBits_length (carry : Bool) (bits : List Bool) :
    (sumBits carry bits).length = bits.length := by
  rw [sumBits_eq_increment, incrementBits_length]

theorem sumBits_value (carry : Bool) (bits : List Bool) :
    boolWordToNat (sumBits carry bits) = (carry.toNat + boolWordToNat bits) % 2^bits.length := by
  rw [sumBits_eq_increment, boolWordToNat_incrementBits]

theorem carryBits_length (carry : Bool) (bits : List Bool) :
    (carryBits carry bits).length = 2 * bits.length := by
  induction bits generalizing carry with
  | nil => rfl
  | cons bit bits ih => simp only [carryBits, List.length_cons, ih]; omega

theorem carryBits_odd (carry : Bool) (bits : List Bool) (i : Nat) :
    (carryBits carry bits)[2*i+1]? = (sumBits carry bits)[i]? := by
  induction bits generalizing carry i with
  | nil => simp [carryBits, sumBits]
  | cons bit bits ih =>
    cases i with
    | zero => simp [carryBits, sumBits]
    | succ i =>
      simp only [carryBits, sumBits]
      rw [show 2*(i+1)+1 = (2*i+1)+2 by omega]
      simpa only [List.getElem?_cons_succ, Nat.add_assoc] using ih (carry && bit) i

theorem word_drop (bits : List Bool) (k : Nat) :
    boolWordToNat (bits.drop k) = boolWordToNat bits / 2^k := by
  induction k generalizing bits with
  | zero => simp
  | succ k ih =>
    cases bits with
    | nil => simp [boolWordToNat_nil]
    | cons b bits =>
      rw [List.drop_succ_cons, ih, boolWordToNat_cons, pow_succ,
        Nat.mul_comm (2^k) 2, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by decide : 0 < 2)]
      have hsmall : b.toNat / 2 = 0 := by cases b <;> decide
      rw [hsmall, Nat.zero_add]


theorem rounded_word_value (bits : List Bool) (k : Nat) (hk : k < bits.length) :
    boolWordToNat (sumBits bits[k] (bits.drop (k+1))) =
      ((boolWordToNat bits + 2^k) / 2^(k+1)) % 2^(bits.length-(k+1)) := by
  rw [sumBits_value, List.length_drop]
  congr 1
  have hword := word_drop bits k
  rw [List.drop_eq_getElem_cons hk, boolWordToNat_cons] at hword
  rw [pow_succ, ← Nat.div_div_eq_div_mul, Nat.add_div_right _ (by positivity), ← hword]
  cases hb : bits[k] <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.zero_add]
  · omega
  · omega

end ShorECDLP.Entrant.RoundedReadout

namespace ShorECDLP.Entrant.RoundedReadout
open Quantum ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816.ChallengeMigration

theorem addStep_support {n start : Nat} (carry bit : Fin start)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((addStep carry bit).instantiate read history).wires ⊆ [0, 1] := by
  cases hc : history carry <;> cases hb : history bit <;>
    simp [addStep, Straight.instantiate, TemplateGate.instantiate, AdaptiveCircuit.wires,
      circuitWires, gateWires, hc, hb, List.subset_def]

theorem addWord_support {n : Nat} : ∀ (start : Nat) (carry : Fin start) (bits : List (Fin start))
    (read : ConstantBit n → Bool) (history : Fin start → Bool),
    ((addWord start carry bits).instantiate read history).wires ⊆ [0, 1]
  | _, _, [], _, _ => by simp [addWord, Straight.instantiate, AdaptiveCircuit.wires]
  | start, carry, bit :: bits, read, history => by
      rw [addWord, castFinish_instantiate]
      exact outer_append_support _ _ read history ([0, 1]) (addStep_support _ _ _ _)
        (fun h => addWord_support (start + 2) _ _ read h)
termination_by _ _ bits => bits.length
end ShorECDLP.Entrant.RoundedReadout


section
/-! Source part after CoordinateParts; requires Entrant Streaming Resources/Semantics imports. -/
namespace ShorECDLP.Entrant.BorrowFlag
open Quantum Classical ShorECDLP.Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
attribute [local irreducible] Paper2607_13816.ChallengeMigration.divisionProgram
  Paper2607_13816.ChallengeMigration.multiplicationProgram equalityProgram

private theorem fieldProgram_count_eq (n start : Nat) (arithmetic : FixedSegment n) :
    (fieldProgram n start arithmetic).1 =
      (let a := equalityProgram n start ZeroAdaptive.reg 0 837 ZeroAdaptive.scratch
       let b := arithmetic (start+a.1)
       appendCompiled a (prependCompiled ZeroAdaptive.cx (appendCompiled b
         (prependCompiled ZeroAdaptive.cx
           (equalityProgram n (start+a.1+b.1) ZeroAdaptive.reg 0 837 ZeroAdaptive.scratch))))).1 := by
  simp only [fieldProgram, coreSegments, prepareProgram, restoreProgram,
    sequenceProgram, surroundCompiled, appendCompiled, prependCompiled,
    relabelCompiled, Nat.add_zero]

theorem divisionProgram_count_eq (n start : Nat) :
    (divisionProgram n start).1 = (ZeroAdaptive.zDivisionProgram n start).1 :=
  fieldProgram_count_eq n start (Paper2607_13816.ChallengeMigration.divisionProgram n)

theorem multiplicationProgram_count_eq (n start : Nat) :
    (multiplicationProgram n start).1 = (ZeroAdaptive.zMultiplicationProgram n start).1 :=
  fieldProgram_count_eq n start (Paper2607_13816.ChallengeMigration.multiplicationProgram n)

private theorem sequence_count_eq {n : Nat} (ps qs : List (FixedSegment n))
    (h : List.Forall₂ (fun p q => ∀ start, (p start).1 = (q start).1) ps qs) (start : Nat) :
    (sequenceProgram n ps start).1 = (sequenceProgram n qs start).1 := by
  induction h generalizing start with
  | nil => rfl
  | @cons p q ps qs hp h ih =>
    simp only [sequenceProgram, appendCompiled]
    rw [hp start, ih]

theorem coordinateProgram_count_eq (start : Nat) :
    (ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateProgram start).1 = (ZeroAdaptive.adaptiveCoordinateProgram start).1 := by
  unfold ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateProgram ZeroAdaptive.adaptiveCoordinateProgram
  apply sequence_count_eq
  unfold ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateSegments ZeroAdaptive.adaptiveCoordinateSegments
  refine List.Forall₂.cons (fun _ => rfl) (List.Forall₂.cons (fun _ => rfl)
    (List.Forall₂.cons (divisionProgram_count_eq 32768) (List.Forall₂.cons (fun _ => rfl)
    (List.Forall₂.cons (fun _ => rfl) (List.Forall₂.cons (multiplicationProgram_count_eq 32768)
    (List.Forall₂.cons (fun _ => rfl) (List.Forall₂.cons (fun _ => rfl)
    (List.Forall₂.cons (fun _ => rfl) .nil))))))))

theorem coordinate_numeric_counts (x y : Nat → Nat) :
    (coordinateSource x y).tCount = 510196414 ∧
    (coordinateSource x y).measurementCount = 30273718 := by
  rw [coordinate_tCount, coordinate_measurements]
  exact Paper2607_13816.ChallengeMigration.coordinate_numeric_counts x y

private theorem cx_physical : CircuitWellFormed ZeroAdaptive.cx := by
  intro g hg
  have he := List.mem_singleton.mp hg
  subst g
  change (837 : Wire) ≠ 263
  decide

private theorem flip_physical : CircuitWellFormed flip := by
  intro g hg
  have he := List.mem_singleton.mp hg
  subst g
  trivial

theorem prepareProgram_wellFormed (n start : Nat) : (prepareProgram n start).2.WellFormed := by
  unfold prepareProgram
  apply appendCompiled_wellFormed
  · exact equalityProgram_wellFormed _ _ _ _ _ _
      (computeEqConstAdaptive_wellFormed _ _ _ _ ZeroAdaptive.layout)
  · exact literalProgram_wellFormed _ cx_physical

theorem restoreProgram_wellFormed (n start : Nat) : (restoreProgram n start).2.WellFormed := by
  unfold restoreProgram
  apply prependCompiled_wellFormed _ _ cx_physical
  exact equalityProgram_wellFormed _ _ _ _ _ _
    (computeEqConstAdaptive_wellFormed _ _ _ _ ZeroAdaptive.layout)

theorem fieldProgram_wellFormed (n start : Nat) (arithmetic : FixedSegment n)
    (ha : ∀ start, (arithmetic start).2.WellFormed) :
    (fieldProgram n start arithmetic).2.WellFormed := by
  unfold fieldProgram
  apply surroundCompiled_wellFormed _ _ _ flip_physical flip_physical
  apply sequenceProgram_wellFormed
  intro p hp cursor
  simp only [coreSegments, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact (relabelCompiled_wellFormed exchange _).mpr (prepareProgram_wellFormed n cursor)
  · exact ha cursor
  · exact (relabelCompiled_wellFormed exchange _).mpr (restoreProgram_wellFormed n cursor)

theorem divisionProgram_wellFormed (n start : Nat) : (divisionProgram n start).2.WellFormed :=
  fieldProgram_wellFormed n start _ (Paper2607_13816.ChallengeMigration.divisionProgram_wellFormed n)

theorem multiplicationProgram_wellFormed (n start : Nat) : (multiplicationProgram n start).2.WellFormed :=
  fieldProgram_wellFormed n start _ (Paper2607_13816.ChallengeMigration.multiplicationProgram_wellFormed n)

theorem prepareProgram_slots (n start : Nat) : (prepareProgram n start).2.gateSlots ≤ 1538 := by
  have h := equalityProgram_slots n start ZeroAdaptive.reg 0 837 ZeroAdaptive.scratch
  simp only [ZeroAdaptive.reg, List.length_cons, List.length_range'] at h
  simp only [prepareProgram, appendCompiled_slots, literalProgram_slots,
    ZeroAdaptive.cx, ZeroAdaptive.reg, List.length_singleton]
  omega

theorem restoreProgram_slots (n start : Nat) : (restoreProgram n start).2.gateSlots ≤ 1538 := by
  have h := equalityProgram_slots n start ZeroAdaptive.reg 0 837 ZeroAdaptive.scratch
  simp only [ZeroAdaptive.reg, List.length_cons, List.length_range'] at h
  simp only [restoreProgram, prependCompiled_slots, ZeroAdaptive.cx, ZeroAdaptive.reg, List.length_singleton]
  omega

theorem fieldProgram_slots (n start : Nat) (arithmetic : FixedSegment n)
    (ha : ∀ start, (arithmetic start).2.gateSlots ≤ 675000000) :
    (fieldProgram n start arithmetic).2.gateSlots ≤ 676000000 := by
  have h := sequenceProgram_slots_le n (coreSegments n arithmetic) ([1538,675000000,1538] : List Nat) (by
    unfold coreSegments
    refine List.Forall₂.cons ?_ (List.Forall₂.cons ha (List.Forall₂.cons ?_ .nil))
    · intro cursor
      rw [relabelCompiled_slots]
      exact prepareProgram_slots n cursor
    · intro cursor
      rw [relabelCompiled_slots]
      exact restoreProgram_slots n cursor) start
  simp only [List.sum_cons, List.sum_nil] at h
  simp only [fieldProgram, surroundCompiled_slots, flip, List.length_singleton]
  omega

theorem divisionProgram_slots (n start : Nat) : (divisionProgram n start).2.gateSlots ≤ 676000000 :=
  fieldProgram_slots n start _ (Paper2607_13816.ChallengeMigration.divisionProgram_slots n)

theorem multiplicationProgram_slots (n start : Nat) : (multiplicationProgram n start).2.gateSlots ≤ 676000000 :=
  fieldProgram_slots n start _ (Paper2607_13816.ChallengeMigration.multiplicationProgram_slots n)

attribute [local irreducible] divisionProgram multiplicationProgram
  fieldLookupAddProgram yNegateProgram pointSquareProgram signedFieldProgram xNegateProgram

theorem adaptiveCoordinateProgram_wellFormed (start : Nat) : (ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateProgram start).2.WellFormed := by
  exact sequenceProgram_wellFormed 32768 ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateSegments (by
    intro p hp cursor
    simp only [ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateSegments,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact fieldLookupXProgram_wellFormed _ _
    · exact signedFieldProgram_wellFormed _ _
    · exact divisionProgram_wellFormed _ _
    · exact pointSquareProgram_wellFormed _ _
    · exact fieldLookupXProgram_wellFormed _ _
    · exact multiplicationProgram_wellFormed _ _
    · exact xNegateProgram_wellFormed _ _
    · exact fieldLookupXProgram_wellFormed _ _
    · exact signedFieldProgram_wellFormed _ _) start

theorem adaptiveCoordinateProgram_slots (start : Nat) :
    (ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateProgram start).2.gateSlots≤1500000000 := by
  have h := sequenceProgram_slots_le 32768 ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateSegments
    ([17449459,17502203,676000000,15750663,17449459,676000000,26370,17449459,17502203] : List Nat) (by
      unfold ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateSegments
      refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil))))))))
      · intro s; exact fieldLookupAddProgram_slots _ _ s (by simp)
      · intro s; exact signedFieldProgram_slots _ s
      · intro s; exact divisionProgram_slots _ s
      · intro s; exact pointSquareProgram_slots _ s
      · intro s; exact fieldLookupAddProgram_slots _ _ s (by simp)
      · intro s; exact multiplicationProgram_slots _ s
      · intro s; exact xNegateProgram_slots _ s
      · intro s; exact fieldLookupAddProgram_slots _ _ s (by simp)
      · intro s; exact signedFieldProgram_slots _ s) start
  simp only [List.sum_cons,List.sum_nil] at h
  unfold ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateProgram
  omega


end ShorECDLP.Entrant.BorrowFlag

namespace ShorECDLP.Entrant.BorrowFlag
open Quantum Classical ShorECDLP.Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration

private theorem eq_layout_support (n start : Nat) :
    straightWires (equalityProgram n start ZeroAdaptive.reg 0 837 ZeroAdaptive.scratch).2 ⊆ zeroAllowedLayout := by
  apply equalityProgram_support
  · intro w hw
    simp [ZeroAdaptive.reg] at hw
    simp [zeroAllowedLayout]
    dsimp only [Wire] at *
    omega
  · simp [zeroAllowedLayout]
  · intro w hw
    simp [ZeroAdaptive.scratch] at hw
    simp [zeroAllowedLayout]
    dsimp only [Wire] at *
    omega

private theorem cx_layout_support : circuitWires ZeroAdaptive.cx ⊆ zeroAllowedLayout := by
  simp [ZeroAdaptive.cx, circuitWires, gateWires, zeroAllowedLayout]

private theorem exchanged_layout_in_base (w : Wire) (hw : w ∈ zeroAllowedLayout) :
    exchange w ∈ windowBaseSupport := by
  simp only [zeroAllowedLayout, List.mem_append, List.mem_range, List.mem_singleton] at hw
  rcases hw with hw | rfl
  · have ha : w ≠ (836 : Wire) := by dsimp only [Wire] at *; omega
    have hb : w ≠ (837 : Wire) := by dsimp only [Wire] at *; omega
    simp only [exchange, Equiv.swap_apply_def, if_neg ha, if_neg hb]
    simp only [windowBaseSupport, List.mem_append, List.mem_range, List.mem_singleton, List.mem_range'_1]
    left; left; omega
  · simp [exchange, windowBaseSupport]

private theorem prepare_support (n start : Nat) :
    straightWires (prepareProgram n start).2 ⊆ zeroAllowedLayout := by
  simp only [prepareProgram, appendCompiled_support, literalProgram_support, List.append_subset]
  exact ⟨eq_layout_support n start, cx_layout_support⟩

private theorem restore_support (n start : Nat) :
    straightWires (restoreProgram n start).2 ⊆ zeroAllowedLayout := by
  simp only [restoreProgram, prependCompiled_support, List.append_subset]
  exact ⟨cx_layout_support, eq_layout_support n start⟩

private theorem relabeled_support {n start : Nat}
    (p : (count : Nat) × Straight n start (start+count))
    (hp : straightWires p.2 ⊆ zeroAllowedLayout) :
    straightWires (relabelCompiled exchange p).2 ⊆ windowBaseSupport := by
  rw [relabelCompiled_support]
  intro w hw
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
  exact exchanged_layout_in_base v (hp hv)

private theorem flip_support : circuitWires flip ⊆ windowBaseSupport := by
  simp [flip, circuitWires, gateWires, windowBaseSupport]

theorem fieldProgram_support (n start : Nat) (arithmetic : FixedSegment n)
    (ha : ∀ start, straightWires (arithmetic start).2 ⊆ windowBaseSupport) :
    straightWires (fieldProgram n start arithmetic).2 ⊆ windowBaseSupport := by
  simp only [fieldProgram, surroundCompiled_support, List.append_subset]
  refine ⟨⟨flip_support, ?_⟩, flip_support⟩
  apply sequenceProgram_support
  intro seg hseg cursor
  simp only [coreSegments, List.mem_cons, List.not_mem_nil, or_false] at hseg
  rcases hseg with rfl | rfl | rfl
  · exact relabeled_support _ (prepare_support n cursor)
  · exact ha cursor
  · exact relabeled_support _ (restore_support n cursor)

theorem divisionProgram_support (n start : Nat) :
    straightWires (divisionProgram n start).2 ⊆ windowBaseSupport :=
  fieldProgram_support n start _ (Paper2607_13816.ChallengeMigration.divisionProgram_support_static n)

theorem multiplicationProgram_support (n start : Nat) :
    straightWires (multiplicationProgram n start).2 ⊆ windowBaseSupport :=
  fieldProgram_support n start _ (Paper2607_13816.ChallengeMigration.multiplicationProgram_support_static n)

theorem adaptiveCoordinateProgram_support (start : Nat) :
    straightWires (ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateProgram start).2 ⊆ windowBaseSupport := by
  have ha : List.range' 263 256 ⊆ windowBaseSupport := by
    intro w hw
    simp only [List.mem_range'_1] at hw
    simp only [windowBaseSupport, List.mem_append, List.mem_range, List.mem_singleton, List.mem_range'_1]
    left; left; omega
  have hf field cursor := fieldLookupAddProgram_support_static field _ ha (by simp) cursor
  have hs field cursor := signedFieldProgram_support_static field cursor
  unfold ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateProgram
  apply sequenceProgram_support
  intro seg hseg cursor
  simp only [ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateSegments, List.mem_cons, List.mem_nil_iff, or_false] at hseg
  rcases hseg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hf _ _
  · exact hs _ _
  · exact divisionProgram_support _ _
  · exact pointSquareProgram_support_static _ _
  · exact hf _ _
  · exact multiplicationProgram_support _ _
  · exact xNegateProgram_support_static _ _
  · exact hf _ _
  · exact hs _ _

end ShorECDLP.Entrant.BorrowFlag

end

section
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Classical Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1 ShorECDLP.Entrant.ZeroAdaptive
local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨p_prime⟩
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] fieldLookupAddProgram signedFieldProgram ShorECDLP.Entrant.BorrowFlag.divisionProgram pointSquareProgram ShorECDLP.Entrant.BorrowFlag.multiplicationProgram xNegateProgram yNegateProgram
theorem sequenceCircuit_three_tCount (a b c : AdaptiveCircuit) :
    (sequenceCircuit [a,b,c]).tCount = a.tCount+b.tCount+c.tCount := by
  simp only [sequenceCircuit,adaptive_tCount_seq,AdaptiveCircuit.tCount]
  omega

/-! ## The coordinate sequence without its final sign negation

The upstream window runs the nine-stage coordinate program, whose last stage is the signed `Y`
lookup `N; A; N` (`N` the sign-controlled negation `windowYNegate` of `Y`, `A` the table addition
of `-y`), and then `N` once more before the correction. These two negations are adjacent and `N`
is an involution on reduced words, so the window here runs the first eight stages, then `N; A`,
and goes straight to the correction. -/

/-- The first eight stages of the adaptive coordinate source. -/
noncomputable def coord8Circuit (x y : Nat → Nat) : AdaptiveCircuit :=
  (((((((fig14LookupX (fun a => (ShorECDLP.p-x a)%ShorECDLP.p)).seq
    (signedPointLookupY (fun a => (ShorECDLP.p-y a)%ShorECDLP.p))).seq
    ShorECDLP.Entrant.BorrowFlag.division).seq fig14SquareSubtract).seq
    (fig14LookupX (fun a => (3*x a)%ShorECDLP.p))).seq
    ShorECDLP.Entrant.BorrowFlag.multiplication).seq fig14Negate).seq
    (fig14LookupX (fun a => x a%ShorECDLP.p))

/-- The table addition `A` of the last signed `Y` lookup. -/
noncomputable def coordYAdd (y : Nat → Nat) : AdaptiveCircuit :=
  lookupModularAddProgram (fun a => (ShorECDLP.p-y a)%ShorECDLP.p) pointLookupAddress
    pointLookupPath (List.range' 7 256) (List.range' 580 256) secp256k1ReductionConstantBits
    ShorECDLP.p 836 559 560 561 558

/-- The coordinate sequence with its final sign negation removed. -/
noncomputable def tailCoordinateCircuit (x y : Nat → Nat) : AdaptiveCircuit :=
  ((coord8Circuit x y).seq windowYNegate).seq (coordYAdd y)

theorem adaptiveCoordinateSource_split (x y : Nat → Nat) :
    ShorECDLP.Entrant.BorrowFlag.coordinateSource x y =
      (coord8Circuit x y).seq (signedPointLookupY (fun a => (ShorECDLP.p-y a)%ShorECDLP.p)) := rfl

theorem signedPointLookupY_split (table : Nat → Nat) :
    signedPointLookupY table =
      (windowYNegate.seq (lookupModularAddProgram table pointLookupAddress pointLookupPath
        (List.range' 7 256) (List.range' 580 256) secp256k1ReductionConstantBits ShorECDLP.p
        836 559 560 561 558)).seq windowYNegate := by
  simp only [signedPointLookupY,signedLookupModularAddProgram,windowYNegate,List.length_range']

def tailCoordinateSegments : List (FixedSegment 32768) :=
  [fieldLookupAddProgram .negX (List.range' 263 256), signedFieldProgram .negY,
   ShorECDLP.Entrant.BorrowFlag.divisionProgram 32768, pointSquareProgram 32768,
   fieldLookupAddProgram .tripleX (List.range' 263 256), ShorECDLP.Entrant.BorrowFlag.multiplicationProgram 32768,
   xNegateProgram 32768, fieldLookupAddProgram .x (List.range' 263 256), yNegateProgram,
   fieldLookupAddProgram .negY (List.range' 580 256)]

def tailCoordinateProgram (start : Nat) : (count : Nat) × Straight 32768 start (start+count) :=
  sequenceProgram 32768 tailCoordinateSegments start

noncomputable def tailCoordinateSources (Q : Point) (w : OddWindow) : List AdaptiveCircuit :=
  [fig14LookupX (fun l => baseFieldValue (windowPoint Q w l) .negX),
   signedPointLookupY (fun l => baseFieldValue (windowPoint Q w l) .negY),
   ShorECDLP.Entrant.BorrowFlag.division, fig14SquareSubtract,
   fig14LookupX (fun l => baseFieldValue (windowPoint Q w l) .tripleX),
   ShorECDLP.Entrant.BorrowFlag.multiplication, fig14Negate,
   fig14LookupX (fun l => baseFieldValue (windowPoint Q w l) .x), windowYNegate,
   lookupModularAddProgram (fun l => fieldValue (windowPoint Q w l) .negY)
     pointLookupAddress pointLookupPath (List.range' 7 256) (List.range' 580 256)
     secp256k1ReductionConstantBits ShorECDLP.p 836 559 560 561 558]

theorem tailCoordinateSources_eq (Q : Point) (w : OddWindow) :
    sequenceCircuit (tailCoordinateSources Q w) =
      tailCoordinateCircuit (fun l => fieldValue (windowPoint Q w l) .x)
        (fun l => fieldValue (windowPoint Q w l) .y) := by
  have hx (P : Point) : baseFieldValue P .x = fieldValue P .x := rfl
  have hn (P : Point) : baseFieldValue P .negX = fieldValue P .negX := rfl
  have hy (P : Point) : baseFieldValue P .negY = fieldValue P .negY := rfl
  have ht (P : Point) : baseFieldValue P .tripleX = fieldValue P .tripleX := rfl
  simp only [tailCoordinateSources, hx, hn, hy, ht, sequenceCircuit, tailCoordinateCircuit,
    coord8Circuit, coordYAdd, adaptive_seq_assoc, adaptive_seq_done, field_negX, field_negY,
    field_tripleX, field_x_mod]

theorem tailCoordinateProgram_run (w : OddWindow) (start : Nat) (Q : Point) (hQ : order • Q = 0)
    (history : Fin start → Bool) :
    compiledRun (tailCoordinateProgram start) (readConstant (oddWindowCoefficients w) Q) history =
      (tailCoordinateCircuit (fun l => fieldValue (windowPoint Q w l) .x)
        (fun l => fieldValue (windowPoint Q w l) .y)).run := by
  unfold tailCoordinateProgram
  rw [← tailCoordinateSources_eq]
  apply sequenceProgram_run
  unfold tailCoordinateSegments tailCoordinateSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_
    (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_
    (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil)))))))))
  · intro cursor h; exact fig14LookupX_compiled w .negX cursor Q hQ h
  · intro cursor h; exact signedFieldProgram_run w .negY cursor Q hQ h
  · intro cursor h; exact ShorECDLP.Entrant.BorrowFlag.divisionProgram_run 32768 cursor _ h
  · intro cursor h; exact pointSquareProgram_run 32768 cursor _ h
  · intro cursor h; exact fig14LookupX_compiled w .tripleX cursor Q hQ h
  · intro cursor h; exact ShorECDLP.Entrant.BorrowFlag.multiplicationProgram_run 32768 cursor _ h
  · intro cursor h; exact xNegateProgram_run 32768 cursor _ h
  · intro cursor h; exact fig14LookupX_compiled w .x cursor Q hQ h
  · intro cursor h; exact yNegateProgram_run cursor _ h
  · intro cursor h; exact fieldLookupAddProgram_run w .negY _ cursor Q hQ (by simp) h

def sharedTailCoordinateProgram (w : OddWindow) (start : Nat) :
    (count : Nat) × Straight 983040 start (start+count) :=
  reindexCompiled (windowIndex w) (tailCoordinateProgram start)

theorem sharedTailCoordinateProgram_run (w : OddWindow) (start : Nat) (Q : Point)
    (hQ : order • Q = 0) (history : Fin start → Bool) :
    compiledRun (sharedTailCoordinateProgram w start) (readConstant coefficientAt Q) history =
      (tailCoordinateCircuit (fun l => fieldValue (windowPoint Q w l) .x)
        (fun l => fieldValue (windowPoint Q w l) .y)).run := by
  unfold sharedTailCoordinateProgram reindexCompiled compiledRun
  rw [reindexStraight_instantiate, readConstant_reindex _ _ _ Q (coefficientAt_window w)]
  exact tailCoordinateProgram_run w start Q hQ history

theorem tailCoordinateProgram_tCount (w : OddWindow) (start : Nat) (Q : Point)
    (hQ : order • Q = 0) (history : Fin start → Bool) :
    compiledTCount (tailCoordinateProgram start) (readConstant (oddWindowCoefficients w) Q) history =
      (tailCoordinateCircuit (fun l => fieldValue (windowPoint Q w l) .x)
        (fun l => fieldValue (windowPoint Q w l) .y)).tCount := by
  unfold tailCoordinateProgram
  rw [← tailCoordinateSources_eq]
  apply sequenceProgram_tCount
  unfold tailCoordinateSegments tailCoordinateSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_
    (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_
    (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil)))))))))
  · intro cursor h; exact fieldLookupAddProgram_tCount_source w .negX _ cursor Q hQ (by simp) h
  · intro cursor h; exact signedFieldProgram_tCount w .negY cursor Q hQ h
  · intro cursor h; exact ShorECDLP.Entrant.BorrowFlag.divisionProgram_tCount 32768 cursor _ h
  · intro cursor h; exact pointSquareProgram_tCount 32768 cursor _ h
  · intro cursor h; exact fieldLookupAddProgram_tCount_source w .tripleX _ cursor Q hQ (by simp) h
  · intro cursor h; exact ShorECDLP.Entrant.BorrowFlag.multiplicationProgram_tCount 32768 cursor _ h
  · intro cursor h; exact xNegateProgram_tCount 32768 cursor _ h
  · intro cursor h; exact fieldLookupAddProgram_tCount_source w .x _ cursor Q hQ (by simp) h
  · intro cursor h; exact yNegateProgram_tCount cursor _ h
  · intro cursor h; exact fieldLookupAddProgram_tCount_source w .negY _ cursor Q hQ (by simp) h

theorem sharedTailCoordinateProgram_tCount (w : OddWindow) (start : Nat) (Q : Point)
    (hQ : order • Q = 0) (history : Fin start → Bool) :
    compiledTCount (sharedTailCoordinateProgram w start) (readConstant coefficientAt Q) history =
      (tailCoordinateCircuit (fun l => fieldValue (windowPoint Q w l) .x)
        (fun l => fieldValue (windowPoint Q w l) .y)).tCount := by
  unfold sharedTailCoordinateProgram reindexCompiled compiledTCount
  rw [reindexStraight_instantiate, readConstant_reindex _ _ _ Q (coefficientAt_window w)]
  exact tailCoordinateProgram_tCount w start Q hQ history

theorem borrowed_coordinate_numeric_counts (x y : Nat → Nat) :
    (ShorECDLP.Entrant.BorrowFlag.coordinateSource x y).tCount = 510196414 ∧
    (ShorECDLP.Entrant.BorrowFlag.coordinateSource x y).measurementCount = 30273718 := by
  have h := old_coordinate_numeric_counts x y
  have hd := ShorECDLP.Entrant.BorrowFlag.division_counts
  have hm := ShorECDLP.Entrant.BorrowFlag.multiplication_counts
  have od := secp256k1ZeroAllowedDivision_resources
  have om := secp256k1ZeroAllowedMultiplication_resources
  simp only [ShorECDLP.Entrant.BorrowFlag.coordinateSource, signedLookupCoordinateProgram,
    adaptive_tCount_seq, modularMeasurements_seq] at h ⊢
  omega
private theorem tail_measurementCount_seq (first second : AdaptiveCircuit) :
    (first.seq second).measurementCount = first.measurementCount + second.measurementCount := by
  induction first with
  | done => simp [AdaptiveCircuit.seq, AdaptiveCircuit.measurementCount]
  | unitary circuit next ih =>
      simp [AdaptiveCircuit.seq, AdaptiveCircuit.measurementCount, ih]
  | xMeasureReset wire onFalse onTrue ihFalse ihTrue =>
      simp [AdaptiveCircuit.seq, AdaptiveCircuit.measurementCount,
        ihFalse, ihTrue, Nat.add_max_add_right, Nat.add_assoc]

/-- The coordinate tail is the coordinate program minus one sign negation. -/
theorem tail_numeric_counts (x y : Nat → Nat) :
    (tailCoordinateCircuit x y).tCount = 510174980 ∧
    (tailCoordinateCircuit x y).measurementCount = 30272696 := by
  obtain ⟨hc1,hc2⟩ := borrowed_coordinate_numeric_counts x y
  obtain ⟨hn1,hn2⟩ := windowYNegate_numeric_counts
  rw [adaptiveCoordinateSource_split,signedPointLookupY_split] at hc1 hc2
  unfold tailCoordinateCircuit coordYAdd
  simp only [adaptive_tCount_seq,tail_measurementCount_seq] at hc1 hc2 ⊢
  constructor <;> omega

theorem sharedTailCoordinateProgram_count (w : OddWindow) (start : Nat) :
    (sharedTailCoordinateProgram w start).1 = 30272696 := by
  have h := compiled_count_of_run (sharedTailCoordinateProgram w start)
    (readConstant coefficientAt (0 : Point)) (fun _ => false) _
    (sharedTailCoordinateProgram_run w start 0 (by simp) (fun _ => false))
  exact h.trans (tail_numeric_counts _ _).2

theorem tailCoordinateProgram_slots (start : Nat) :
    (tailCoordinateProgram start).2.gateSlots≤1500000000 := by
  have h := sequenceProgram_slots_le 32768 tailCoordinateSegments
    ([17449459,17502203,676000000,15750663,17449459,676000000,26370,17449459,26372,17449459] :
      List Nat) (by
      unfold tailCoordinateSegments
      refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_
        (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_
        (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil)))))))))
      · intro s; exact fieldLookupAddProgram_slots _ _ s (by simp)
      · intro s; exact signedFieldProgram_slots _ s
      · intro s; exact ShorECDLP.Entrant.BorrowFlag.divisionProgram_slots _ s
      · intro s; exact pointSquareProgram_slots _ s
      · intro s; exact fieldLookupAddProgram_slots _ _ s (by simp)
      · intro s; exact ShorECDLP.Entrant.BorrowFlag.multiplicationProgram_slots _ s
      · intro s; exact xNegateProgram_slots _ s
      · intro s; exact fieldLookupAddProgram_slots _ _ s (by simp)
      · intro s; exact yNegateProgram_slots_le s
      · intro s; exact fieldLookupAddProgram_slots _ _ s (by simp)) start
  simp only [List.sum_cons,List.sum_nil] at h
  unfold tailCoordinateProgram
  omega


theorem tailCoordinateProgram_wellFormed (start : Nat) :
    (tailCoordinateProgram start).2.WellFormed := by
  unfold tailCoordinateProgram
  apply sequenceProgram_wellFormed
  intro p hp cursor
  simp only [tailCoordinateSegments,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fieldLookupXProgram_wellFormed _ _
  · exact signedFieldProgram_wellFormed _ _
  · exact ShorECDLP.Entrant.BorrowFlag.divisionProgram_wellFormed _ _
  · exact pointSquareProgram_wellFormed _ _
  · exact fieldLookupXProgram_wellFormed _ _
  · exact ShorECDLP.Entrant.BorrowFlag.multiplicationProgram_wellFormed _ _
  · exact xNegateProgram_wellFormed _ _
  · exact fieldLookupXProgram_wellFormed _ _
  · exact yNegateProgram_wellFormed _
  · exact fieldLookupYProgram_wellFormed _ _
theorem tailCoordinateProgram_support_static (start : Nat) :
    straightWires (tailCoordinateProgram start).2 ⊆ windowBaseSupport := by
  have ha : List.range' 263 256 ⊆ windowBaseSupport := by
    intro w hw
    simp only [List.mem_range'_1] at hw
    simp only [windowBaseSupport,List.mem_append,List.mem_range,List.mem_singleton,List.mem_range'_1]
    omega
  have hy : List.range' 580 256 ⊆ windowBaseSupport := by
    intro w hw
    simp only [List.mem_range'_1] at hw
    simp only [windowBaseSupport,List.mem_append,List.mem_range,List.mem_singleton,List.mem_range'_1]
    omega
  have hf field cursor := (fieldLookupAddProgram_support_static field _ ha (by simp) cursor)
  have hs field cursor := (signedFieldProgram_support_static field cursor)
  unfold tailCoordinateProgram
  apply sequenceProgram_support
  intro seg hseg cursor
  simp only [tailCoordinateSegments,List.mem_cons,List.mem_nil_iff,or_false] at hseg
  rcases hseg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact hf _ _
  · exact hs _ _
  · exact ShorECDLP.Entrant.BorrowFlag.divisionProgram_support _ _
  · exact (pointSquareProgram_support_static _ _)
  · exact hf _ _
  · exact ShorECDLP.Entrant.BorrowFlag.multiplicationProgram_support _ _
  · exact (xNegateProgram_support_static _ _)
  · exact hf _ _
  · exact (yNegateProgram_support_static _)
  · exact (fieldLookupAddProgram_support_static _ _ hy (by simp) cursor)
private theorem restrictCoherent {a : AdaptiveCircuit} {v : State →ₗ[ℂ] State}
    {P R : BasisState → Prop} (h : CoherentlyImplementsOn a v R)
    (hp : ∀ s, P s → R s) : CoherentlyImplementsOn a v P := by
  obtain ⟨cs,hc,hm⟩ := h
  exact ⟨cs,hc.imp (fun _ _ hb s hs => hb s (hp s hs)),hm⟩

/-! ### The coordinate tail without its final negation

`tailCoordinateCircuit` runs the first eight coordinate stages, the negation `N` and the table
addition `A`. The upstream coordinate program runs `N` once more. Since `N` is an involution on
reduced words, the tail implements `N` after the upstream coordinate map. -/

private theorem tail_division_ready (s : BasisState) (hs : PointLookupValid s) :
    PointLookupValid (zeroAllowedDivisionOutputState s) := by
  refine ⟨fig14Division_ready s hs.1,?_⟩
  rw [zeroAllowedDivisionOutputState_frame s hs.1]
  simpa using hs.2
private theorem tail_multiplication_ready (s : BasisState) (hs : PointLookupValid s) :
    PointLookupValid (zeroAllowedMultiplicationOutputState s) := by
  refine ⟨fig14Multiplication_ready s hs.1,?_⟩
  rw [zeroAllowedMultiplicationOutputState_frame s hs.1]
  simpa using hs.2
private theorem tail_square_ready (s : BasisState) (hs : PointLookupValid s) :
    PointLookupValid (fig14SquareSubtractState s) :=
  ⟨fig14SquareSubtractState_ready s hs.1,
    ((fig14SquareSubtractState_correct s hs.1).2 836 (by decide +kernel)).trans hs.2⟩
private theorem tail_negate_ready (s : BasisState) (hs : PointLookupValid s) :
    PointLookupValid (fig14NegateState s) :=
  ⟨fig14NegateState_ready s hs.1,
    ((fig14NegateState_correct s hs.1).2 836 (by decide +kernel)).trans hs.2⟩
private theorem tail_yneg_ready (s : BasisState) (hs : PointLookupValid s) :
    PointLookupValid (windowYNegateState s) :=
  ⟨windowYNegateState_ready s hs.1,
    ((windowYNegateState_correct s hs.1).2 836 (by decide +kernel)).trans hs.2⟩

/-- The state after the first eight coordinate stages, as in `signedLookupCoordinateState`. -/
noncomputable def coord8State (x y : Nat → Nat) (s : BasisState) : BasisState :=
  let s1 := fig14LookupXState (fun a => (ShorECDLP.p-x a)%ShorECDLP.p) s
  let s2 := signedPointLookupYState (fun a => (ShorECDLP.p-y a)%ShorECDLP.p) s1
  let s3 := zeroAllowedDivisionOutputState s2
  let s4 := fig14SquareSubtractState s3
  let s5 := fig14LookupXState (fun a => (3*x a)%ShorECDLP.p) s4
  let s6 := zeroAllowedMultiplicationOutputState s5
  let s7 := fig14NegateState s6
  fig14LookupXState (fun a => x a%ShorECDLP.p) s7

noncomputable def coordYAddState (y : Nat → Nat) : BasisState → BasisState :=
  lookupModularAddState (fun a => (ShorECDLP.p-y a)%ShorECDLP.p) pointLookupAddress
    (List.range' 7 256) (List.range' 580 256) secp256k1ReductionConstantBits ShorECDLP.p 836 559 558

theorem coord8Circuit_coherent (x y : Nat → Nat) :
    CoherentlyImplementsOn (coord8Circuit x y) (Finsupp.lmapDomain ℂ ℂ (coord8State x y))
      PointLookupValid ∧ ∀ s, PointLookupValid s → PointLookupValid (coord8State x y s) := by
  have hk (k : Nat) : k%ShorECDLP.p<ShorECDLP.p := Nat.mod_lt _ ShorECDLP.Secp256k1.p_prime.pos
  have h1 := fig14LookupX_coherent (fun a => (ShorECDLP.p-x a)%ShorECDLP.p) (fun _ => hk _)
  have r1 := fig14LookupXState_ready (fun a => (ShorECDLP.p-x a)%ShorECDLP.p) (fun _ => hk _)
  have h2 := signedPointLookupY_coherent (fun a => (ShorECDLP.p-y a)%ShorECDLP.p) (fun _ => hk _)
  have r2 := signedPointLookupYState_ready (fun a => (ShorECDLP.p-y a)%ShorECDLP.p) (fun _ => hk _)
  have h3 : CoherentlyImplementsOn ShorECDLP.Entrant.BorrowFlag.division
      (Finsupp.lmapDomain ℂ ℂ zeroAllowedDivisionOutputState) PointLookupValid :=
    ShorECDLP.Entrant.BorrowFlag.division_coherent
  have h4 : CoherentlyImplementsOn fig14SquareSubtract
      (Finsupp.lmapDomain ℂ ℂ fig14SquareSubtractState) PointLookupValid :=
    restrictCoherent fig14SquareSubtract_coherent (fun s hs => hs.1)
  have h5 := fig14LookupX_coherent (fun a => (3*x a)%ShorECDLP.p) (fun _ => hk _)
  have r5 := fig14LookupXState_ready (fun a => (3*x a)%ShorECDLP.p) (fun _ => hk _)
  have h6 : CoherentlyImplementsOn ShorECDLP.Entrant.BorrowFlag.multiplication
      (Finsupp.lmapDomain ℂ ℂ zeroAllowedMultiplicationOutputState) PointLookupValid :=
    ShorECDLP.Entrant.BorrowFlag.multiplication_coherent
  have h7 : CoherentlyImplementsOn fig14Negate
      (Finsupp.lmapDomain ℂ ℂ fig14NegateState) PointLookupValid :=
    restrictCoherent fig14Negate_coherent (fun s hs => hs.1)
  have h8 := fig14LookupX_coherent (fun a => x a%ShorECDLP.p) (fun _ => hk _)
  have r8 := fig14LookupXState_ready (fun a => x a%ShorECDLP.p) (fun _ => hk _)
  have c2 := composeCoherent h1 h2 r1
  have v2 := fun s hs => r2 _ (r1 s hs)
  have c3 := composeCoherent c2 h3 v2
  have v3 := fun s hs => tail_division_ready _ (v2 s hs)
  have c4 := composeCoherent c3 h4 v3
  have v4 := fun s hs => tail_square_ready _ (v3 s hs)
  have c5 := composeCoherent c4 h5 v4
  have v5 := fun s hs => r5 _ (v4 s hs)
  have c6 := composeCoherent c5 h6 v5
  have v6 := fun s hs => tail_multiplication_ready _ (v5 s hs)
  have c7 := composeCoherent c6 h7 v6
  have v7 := fun s hs => tail_negate_ready _ (v6 s hs)
  have c8 := composeCoherent c7 h8 v7
  exact ⟨c8,fun s hs => r8 _ (v7 s hs)⟩

private theorem tail_input_disjoint :
    (836::pointLookupAddress++pointLookupPath).Disjoint (List.range' 7 256) := by
  apply List.disjoint_left.mpr
  intro w hw ht
  simp only [pointLookupAddress,pointLookupPath,List.mem_cons,List.mem_append,List.mem_range'] at hw ht
  rcases hw with (rfl | ⟨i,hi,hwi⟩) | ⟨i,hi,hwi⟩ <;> obtain ⟨j,hj,hwj⟩ := ht <;> omega

private theorem tail_path_disjoint : pointLookupPath.Disjoint (List.range' 580 256) := by
  apply List.disjoint_left.mpr
  intro w hw ht
  simp only [pointLookupPath,List.mem_range'] at hw ht
  omega

private theorem tail_address_disjoint : pointLookupAddress.Disjoint (List.range' 580 256) := by
  apply List.disjoint_left.mpr
  intro w hw ht
  simp only [pointLookupAddress,List.mem_range'] at hw ht
  omega

private theorem tail_add_layout :
    ([836,559,560,561,558] ++ List.range' 7 256 ++ List.range' 580 256 : List Wire).Nodup := by
  decide +kernel

private theorem tail_point_valid (s : BasisState) (hs : PointLookupValid s) :
    LookupModularValid pointLookupPath (List.range' 7 256) (List.range' 580 256)
      ShorECDLP.p 836 559 560 561 558 s := by
  refine ⟨?_,?_,hs.2,?_,?_,?_,?_,hs.1.2.2.2⟩
  · intro w hw
    apply hs.1.1 w
    simp [pointLookupPath] at hw ⊢
    omega
  · intro w hw
    apply hs.1.1 w
    simp at hw ⊢
    omega
  · exact hs.1.1 559 (by decide +kernel)
  · exact hs.1.1 560 (by decide +kernel)
  · exact hs.1.1 561 (by decide +kernel)
  · exact hs.1.1 558 (by decide +kernel)

theorem coordYAdd_coherent (y : Nat → Nat) :
    CoherentlyImplementsOn (coordYAdd y) (Finsupp.lmapDomain ℂ ℂ (coordYAddState y))
      PointLookupValid := by
  have hk (k : Nat) : k%ShorECDLP.p<ShorECDLP.p := Nat.mod_lt _ ShorECDLP.Secp256k1.p_prime.pos
  have h := lookupModularAddProgram_coherent (fun a => (ShorECDLP.p-y a)%ShorECDLP.p)
    pointLookupAddress pointLookupPath (List.range' 7 256) (List.range' 580 256)
    secp256k1ReductionConstantBits ShorECDLP.p 836 559 560 561 558
    (by decide +kernel) (by decide +kernel) tail_input_disjoint tail_path_disjoint
    (by simp) (by simp) (by simp [secp256k1ReductionConstantBits]) tail_add_layout
    ShorECDLP.Secp256k1.p_prime.pos (by decide +kernel)
    (by rw [secp256k1ReductionConstant_value]; decide +kernel) (fun _ => hk _)
  exact restrictCoherent h tail_point_valid

/-- The sign negation of `Y` is an involution on reduced words. -/
theorem windowYNegateState_twice (t : BasisState) (h558 : t 558 = false)
    (hy : boolWordToNat (wireValues (List.range' 580 256) t) < ShorECDLP.p) :
    windowYNegateState (windowYNegateState t) = t := by
  have hc (u : BasisState) (h5 : u 558 = false)
      (hu : boolWordToNat (wireValues (List.range' 580 256) u) < ShorECDLP.p) :
      boolWordToNat (wireValues (List.range' 580 256) (windowYNegateState u)) =
        (if u 854 then boolWordToNat (wireValues (List.range' 580 256) u)
          else (ShorECDLP.p-boolWordToNat (wireValues (List.range' 580 256) u))%ShorECDLP.p) ∧
      ∀ w, w ∉ List.range' 580 256 → windowYNegateState u w = u w :=
    negativeModularNegateState_correct _ _ ShorECDLP.p 854 558 u
      (by simp) (by simp) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) h5 (by simp; decide +kernel) hu
      (by rw [boolWordToNat_constantBits,Nat.mod_eq_of_lt (by decide +kernel)])
  have h1 := hc t h558 hy
  have h558' : windowYNegateState t 558 = false := (h1.2 558 (by decide +kernel)).trans h558
  have hy' : boolWordToNat (wireValues (List.range' 580 256) (windowYNegateState t)) <
      ShorECDLP.p := by
    rw [h1.1]
    split
    · exact hy
    · exact Nat.mod_lt _ ShorECDLP.Secp256k1.p_prime.pos
  have h2 := hc _ h558' hy'
  have hs : windowYNegateState t 854 = t 854 := h1.2 854 (by decide +kernel)
  have hv : boolWordToNat (wireValues (List.range' 580 256)
      (windowYNegateState (windowYNegateState t))) =
        boolWordToNat (wireValues (List.range' 580 256) t) := by
    rw [h2.1,hs,h1.1]
    generalize boolWordToNat (wireValues (List.range' 580 256) t) = v at hy ⊢
    cases t 854
    · simp only [Bool.false_eq_true,if_false]
      rcases Nat.eq_zero_or_pos v with rfl | hv0
      · simp
      · rw [Nat.mod_eq_of_lt (show ShorECDLP.p - v < ShorECDLP.p by omega),
          show ShorECDLP.p - (ShorECDLP.p - v) = v by omega, Nat.mod_eq_of_lt hy]
    · simp
  have he := boolWordToNat_injective_of_length (by simp [wireValues]) hv
  funext w
  by_cases hw : w ∈ List.range' 580 256
  · exact List.map_inj_left.mp he w hw
  · exact (h2.2 w hw).trans (h1.2 w hw)

theorem tailCoordinateState_eq (x y : Nat → Nat) (s : BasisState) (hs : PointLookupValid s) :
    coordYAddState y (windowYNegateState (coord8State x y s)) =
      windowYNegateState (signedLookupCoordinateState x y s) := by
  have hk (k : Nat) : k%ShorECDLP.p<ShorECDLP.p := Nat.mod_lt _ ShorECDLP.Secp256k1.p_prime.pos
  have ht := tail_yneg_ready _ ((coord8Circuit_coherent x y).2 s hs)
  have hv := tail_point_valid _ ht
  have hu := lookupModularAddState_correct (fun a => (ShorECDLP.p-y a)%ShorECDLP.p)
    pointLookupAddress pointLookupPath (List.range' 7 256) (List.range' 580 256)
    secp256k1ReductionConstantBits ShorECDLP.p 836 559 560 561 558
    tail_input_disjoint tail_address_disjoint (by simp) (by simp [secp256k1ReductionConstantBits])
    tail_add_layout (by decide +kernel) (by rw [secp256k1ReductionConstant_value]; decide +kernel)
    (fun _ => hk _) _ hv
  have hsplit : signedLookupCoordinateState x y s =
      windowYNegateState (coordYAddState y (windowYNegateState (coord8State x y s))) := by
    simp only [signedLookupCoordinateState,coord8State,coordYAddState,signedPointLookupYState,
      signedLookupModularAddState,windowYNegateState,List.length_range']
  rw [hsplit,windowYNegateState_twice]
  · exact (hu.2 558 (by decide +kernel)).trans hv.2.2.2.2.2.2.1
  · change boolWordToNat (wireValues (List.range' 580 256) (lookupModularAddState _ _ _ _ _ _ _ _ _ _)) < _
    rw [hu.1]
    exact Nat.mod_lt _ ShorECDLP.Secp256k1.p_prime.pos

theorem tailCoordinateCircuit_coherent (x y : Nat → Nat) :
    CoherentlyImplementsOn (tailCoordinateCircuit x y)
      (Finsupp.lmapDomain ℂ ℂ (fun s => windowYNegateState (signedLookupCoordinateState x y s)))
      PointLookupValid := by
  obtain ⟨c8,v8⟩ := coord8Circuit_coherent x y
  have hN : CoherentlyImplementsOn windowYNegate
      (Finsupp.lmapDomain ℂ ℂ windowYNegateState) PointLookupValid :=
    restrictCoherent windowYNegate_coherent (fun s hs => hs.1)
  have c9 := composeCoherent c8 hN v8
  have c10 := composeCoherent c9 (coordYAdd_coherent y) (fun s hs => tail_yneg_ready _ (v8 s hs))
  apply c10.congrIdeal
  intro s hs
  simp only [Finsupp.lmapDomain_apply,ket,Finsupp.mapDomain_single]
  rw [tailCoordinateState_eq x y s hs]


end ShorECDLP.Paper2607_13816.ChallengeMigration
end

/-! EDITABLE. Single-trial entrant: mixed-width circuit and resource proofs.
Concatenated in dependency order to bound parallel kernel replay memory.
Original provenance comments are retained beside each source part. -/

-- ==== part: Single/Coordinate ====

section
/-! Table-parametric instantiations of the Apache-2.0 licensed Streaming
compilation lemmas. Arithmetic circuits and their coherent proofs are reused.
Only the public coefficient read function is generalized here. -/

namespace ShorECDLP.Entrant.Single.Physical
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration ShorECDLP.Entrant.ZeroAdaptive

attribute [local irreducible] fieldLoadProgram modularAddProgram divisionProgram multiplicationProgram
  squareSubtractProgram modularNegateProgram secp256k1InPlaceDivision secp256k1InPlaceMultiplication

noncomputable def tablePoint (coeffs : Fin 32768 → PointCoeff) (Q : Point) (a : Nat) : Point :=
  constantPoint Q (coeffs ⟨a % 32768, Nat.mod_lt _ (by decide)⟩)

theorem fieldLoadOps_circuit (coeffs : Fin 32768 → PointCoeff) (field : PointField) (Q : Point) :
    lookupCircuit (readConstant coeffs Q) (fieldLoadOps field) =
    tableLookupProgram (fun l => tableWordMask (List.range' 7 256) (fieldValue (tablePoint coeffs Q l) field))
      pointLookupAddress 836 pointLookupPath := by
  rw [fieldLoadOps, unaryLookupOps_circuit]
  unfold tableLookupProgram tableLookup
  apply unaryAction_leaf_congr
  intro l hl q
  obtain ⟨i, hi, he⟩ := tableAddressTree_label _ 0 1 l hl
  have hlt : l < 32768 := by simpa [he, pointLookupAddress] using hi
  rw [fieldLeaf_instantiate]
  simp only [tablePoint, Nat.mod_eq_of_lt hlt]

theorem fieldLoadProgram_run (coeffs : Fin 32768 → PointCoeff) (field : PointField) (start : Nat)
    (Q : Point) (history : Fin start → Bool) :
    ((fieldLoadProgram field start).instantiate (readConstant coeffs Q) history).run =
      (tableLookupProgram (fun l => tableWordMask (List.range' 7 256) (fieldValue (tablePoint coeffs Q l) field))
        pointLookupAddress 836 pointLookupPath).run := by
  rw [fieldLoadProgram, castFinish_instantiate, lookupProgram_run, fieldLoadOps_circuit coeffs field Q]

theorem fieldLoadProgram_tCount (coeffs : Fin 32768 → PointCoeff) (field : PointField)
    (start : Nat) (Q : Point) (history : Fin start → Bool) :
    ((ShorECDLP.Paper2607_13816.ChallengeMigration.fieldLoadProgram field start).instantiate
      (readConstant coeffs Q) history).tCount = 229369 := by
  rw [ShorECDLP.Paper2607_13816.ChallengeMigration.fieldLoadProgram, castFinish_instantiate,
    lookupProgram_tCount, fieldLoadOps_circuit coeffs field Q,
    tableLookupProgram_tCount _ _ _ _ (by decide) (by decide)]
  rfl

theorem fieldLookupAddProgram_run (coeffs : Fin 32768 → PointCoeff) (field : PointField) (acc : List Wire)
    (start : Nat) (Q : Point) (hl : acc.length = 256)
    (history : Fin start → Bool) :
    compiledRun (fieldLookupAddProgram field acc start) (readConstant coeffs Q) history =
      (lookupModularAddProgram (fun l => fieldValue (tablePoint coeffs Q l) field)
        pointLookupAddress pointLookupPath (List.range' 7 256) acc secp256k1ReductionConstantBits
        ShorECDLP.p 836 559 560 561 558).run := by
  let read := readConstant coeffs Q
  let lookup := tableLookupProgram (fun l => tableWordMask (List.range' 7 256) (fieldValue (tablePoint coeffs Q l) field))
    pointLookupAddress 836 pointLookupPath
  let add := modularAddProgram 32768 (start+32767) (List.range' 7 256) acc
    secp256k1ReductionConstantBits ShorECDLP.p 836 559 560 561 558
  let target := controlledModularAdd (List.range' 7 256) acc secp256k1ReductionConstantBits
    ShorECDLP.p 836 559 560 561 558
  have addRun : ∀ h, (add.2.instantiate read h).run = target.run := by
    intro h
    exact modularAddProgram_run 32768 _ _ acc _ _ _ _ _ _ _
      (by simp [hl]) (by simp [secp256k1ReductionConstantBits, hl]) (by omega) read h
  have suffixRun : ∀ h, compiledRun
      (appendCompiled add ⟨32767, fieldLoadProgram field (start+32767+add.1)⟩) read h =
      (target.seq lookup).run := by
    intro h
    rw [appendCompiled_run add ⟨32767, fieldLoadProgram field (start+32767+add.1)⟩ read h lookup
      (fun h => fieldLoadProgram_run coeffs field _ Q h),
      AdaptiveCircuit.run_seq, addRun h, ← AdaptiveCircuit.run_seq]
  change compiledRun
    (appendCompiled ⟨32767, fieldLoadProgram field start⟩
      (appendCompiled add ⟨32767, fieldLoadProgram field (start+32767+add.1)⟩)) read history = _
  rw [appendCompiled_run _ _ _ _ (target.seq lookup) suffixRun,
    AdaptiveCircuit.run_seq, fieldLoadProgram_run coeffs field start Q history,
    ← AdaptiveCircuit.run_seq]
  rw [← adaptive_seq_assoc]
  rfl

theorem fieldLookupAddProgram_tCount (coeffs : Fin 32768 → PointCoeff) (field : PointField) (acc : List Wire)
    (start : Nat) (Q : Point) (hl : acc.length = 256)
    (history : Fin start → Bool) :
    compiledTCount (fieldLookupAddProgram field acc start) (readConstant coeffs Q) history =
      229369 + (controlledModularAdd (List.range' 7 256) acc secp256k1ReductionConstantBits
        ShorECDLP.p 836 559 560 561 558).tCount + 229369 := by
  let read := readConstant coeffs Q
  let add := modularAddProgram 32768 (start+32767) (List.range' 7 256) acc
    secp256k1ReductionConstantBits ShorECDLP.p 836 559 560 561 558
  let target := controlledModularAdd (List.range' 7 256) acc secp256k1ReductionConstantBits
    ShorECDLP.p 836 559 560 561 558
  have addT : ∀ h, (add.2.instantiate read h).tCount = target.tCount := by
    intro h
    exact modularAddProgram_tCount 32768 _ _ acc _ _ _ _ _ _ _
      (by simp [hl]) (by simp [secp256k1ReductionConstantBits, hl]) (by omega) read h
  have suffixT : ∀ h, compiledTCount
      (appendCompiled add ⟨32767, fieldLoadProgram field (start+32767+add.1)⟩) read h =
      target.tCount + 229369 := by
    intro h
    rw [appendCompiled_tCount add ⟨32767, fieldLoadProgram field (start+32767+add.1)⟩ read h 229369
      (fun h => fieldLoadProgram_tCount coeffs field _ Q h), addT h]
  change compiledTCount
    (appendCompiled ⟨32767, fieldLoadProgram field start⟩
      (appendCompiled add ⟨32767, fieldLoadProgram field (start+32767+add.1)⟩)) read history = _
  rw [appendCompiled_tCount _ _ _ _ (target.tCount+229369) suffixT,
    fieldLoadProgram_tCount coeffs field start Q history]
  exact (Nat.add_assoc _ _ _).symm

theorem fig14LookupX_compiled (coeffs : Fin 32768 → PointCoeff) (field : PointField) (start : Nat)
    (Q : Point) (history : Fin start → Bool) :
    compiledRun (fieldLookupAddProgram field (List.range' 263 256) start)
      (readConstant coeffs Q) history =
      (fig14LookupX (fun l => fieldValue (tablePoint coeffs Q l) field)).run := by
  exact fieldLookupAddProgram_run coeffs field _ start Q (by simp) history

theorem signedFieldProgram_run (coeffs : Fin 32768 → PointCoeff) (field : PointField) (start : Nat)
    (Q : Point) (history : Fin start → Bool) :
    compiledRun (signedFieldProgram field start) (readConstant coeffs Q) history =
      (signedPointLookupY (fun l => fieldValue (tablePoint coeffs Q l) field)).run := by
  unfold signedFieldProgram
  dsimp only
  unfold signedPointLookupY signedLookupModularAddProgram
  simp only [List.length_range']
  rw [adaptive_seq_assoc]
  apply appendCompiled_run_eq
  · exact yNegateProgram_run start _ history
  · intro h
    apply appendCompiled_run_eq
    · exact fieldLookupAddProgram_run coeffs field _ _ Q (by simp) h
    · intro h
      exact yNegateProgram_run _ _ h

theorem fieldLookupAddProgram_tCount_source (coeffs : Fin 32768 → PointCoeff) (field : PointField) (acc : List Wire)
    (start : Nat) (Q : Point) (hl : acc.length = 256)
    (history : Fin start → Bool) :
    compiledTCount (fieldLookupAddProgram field acc start) (readConstant coeffs Q) history =
      (lookupModularAddProgram (fun l => fieldValue (tablePoint coeffs Q l) field)
        pointLookupAddress pointLookupPath (List.range' 7 256) acc secp256k1ReductionConstantBits
        ShorECDLP.p 836 559 560 561 558).tCount := by
  rw [fieldLookupAddProgram_tCount coeffs field acc start Q hl history]
  simp only [lookupModularAddProgram, adaptive_tCount_seq]
  rw [tableLookupProgram_tCount _ _ _ _ (by decide) (by decide)]
  rfl

theorem yNegateProgram_tCount (start : Nat) (read : ConstantBit 32768 → Bool) (history : Fin start → Bool) :
    compiledTCount (yNegateProgram start) read history =
      (negativeControlledModularNegate (List.range' 580 256) (List.range' 7 256)
        (constantBits 256 ShorECDLP.p) 854 559 560 561 558).tCount := by
  exact negativeNegateProgram_tCount 32768 start _ _ _ _ _ _ _ _
    (by simp) (by rw [constantBits_length, List.length_range']) (by simp) read history

theorem signedFieldProgram_tCount (coeffs : Fin 32768 → PointCoeff) (field : PointField) (start : Nat)
    (Q : Point) (history : Fin start → Bool) :
    compiledTCount (signedFieldProgram field start) (readConstant coeffs Q) history =
      (signedPointLookupY (fun l => fieldValue (tablePoint coeffs Q l) field)).tCount := by
  unfold signedFieldProgram
  dsimp only
  unfold signedPointLookupY signedLookupModularAddProgram
  simp only [List.length_range']
  rw [adaptive_seq_assoc]
  apply appendCompiled_tCount_eq
  · exact yNegateProgram_tCount start _ history
  · intro h
    apply appendCompiled_tCount_eq
    · exact fieldLookupAddProgram_tCount_source coeffs field _ _ Q (by simp) h
    · intro h
      exact yNegateProgram_tCount _ _ h

noncomputable def tailCoordinateCircuits (Q : Point) (coeffs : Fin 32768 → PointCoeff) : List AdaptiveCircuit :=
  [fig14LookupX (fun l => baseFieldValue (tablePoint coeffs Q l) .negX),
   signedPointLookupY (fun l => baseFieldValue (tablePoint coeffs Q l) .negY),
   ShorECDLP.Entrant.BorrowFlag.division, fig14SquareSubtract,
   fig14LookupX (fun l => baseFieldValue (tablePoint coeffs Q l) .tripleX),
   ShorECDLP.Entrant.BorrowFlag.multiplication, fig14Negate,
   fig14LookupX (fun l => baseFieldValue (tablePoint coeffs Q l) .x),
   windowYNegate,
   lookupModularAddProgram (fun l => fieldValue (tablePoint coeffs Q l) .negY)
     pointLookupAddress pointLookupPath (List.range' 7 256) (List.range' 580 256)
     secp256k1ReductionConstantBits ShorECDLP.p 836 559 560 561 558]

theorem tailCoordinateCircuits_eq (Q : Point) (coeffs : Fin 32768 → PointCoeff) :
    sequenceCircuit (tailCoordinateCircuits Q coeffs) =
      tailCoordinateCircuit (fun l => fieldValue (tablePoint coeffs Q l) .x)
        (fun l => fieldValue (tablePoint coeffs Q l) .y) := by
  have hx (P : Point) : baseFieldValue P .x = fieldValue P .x := rfl
  have hn (P : Point) : baseFieldValue P .negX = fieldValue P .negX := rfl
  have hy (P : Point) : baseFieldValue P .negY = fieldValue P .negY := rfl
  have ht (P : Point) : baseFieldValue P .tripleX = fieldValue P .tripleX := rfl
  simp only [tailCoordinateCircuits, hx, hn, hy, ht, sequenceCircuit, tailCoordinateCircuit, coord8Circuit, coordYAdd,
    adaptive_seq_assoc, adaptive_seq_done, field_negX, field_negY, field_tripleX, field_x_mod]

theorem tailCoordinateProgram_run (coeffs : Fin 32768 → PointCoeff) (start : Nat) (Q : Point)
    (history : Fin start → Bool) :
    compiledRun (tailCoordinateProgram start) (readConstant coeffs Q) history =
      (tailCoordinateCircuit (fun l => fieldValue (tablePoint coeffs Q l) .x)
        (fun l => fieldValue (tablePoint coeffs Q l) .y)).run := by
  unfold tailCoordinateProgram
  rw [← tailCoordinateCircuits_eq]
  apply sequenceProgram_run
  unfold tailCoordinateSegments tailCoordinateCircuits
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil))))))))))
  · intro cursor h
    exact fig14LookupX_compiled coeffs .negX cursor Q h
  · intro cursor h
    exact signedFieldProgram_run coeffs .negY cursor Q h
  · intro cursor h
    exact ShorECDLP.Entrant.BorrowFlag.divisionProgram_run 32768 cursor _ h
  · intro cursor h
    exact pointSquareProgram_run 32768 cursor _ h
  · intro cursor h
    exact fig14LookupX_compiled coeffs .tripleX cursor Q h
  · intro cursor h
    exact ShorECDLP.Entrant.BorrowFlag.multiplicationProgram_run 32768 cursor _ h
  · intro cursor h
    exact xNegateProgram_run 32768 cursor _ h
  · intro cursor h
    exact fig14LookupX_compiled coeffs .x cursor Q h
  · intro cursor h
    exact yNegateProgram_run cursor _ h
  · intro cursor h
    exact fieldLookupAddProgram_run coeffs .negY _ cursor Q (by simp) h

theorem tailCoordinateProgram_tCount (coeffs : Fin 32768 → PointCoeff) (start : Nat) (Q : Point)
    (history : Fin start → Bool) :
    compiledTCount (tailCoordinateProgram start) (readConstant coeffs Q) history =
      (tailCoordinateCircuit (fun l => fieldValue (tablePoint coeffs Q l) .x)
        (fun l => fieldValue (tablePoint coeffs Q l) .y)).tCount := by
  unfold tailCoordinateProgram
  rw [← tailCoordinateCircuits_eq]
  apply sequenceProgram_tCount
  unfold tailCoordinateSegments tailCoordinateCircuits
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil))))))))))
  · intro cursor h
    exact fieldLookupAddProgram_tCount_source coeffs .negX _ cursor Q (by simp) h
  · intro cursor h
    exact signedFieldProgram_tCount coeffs .negY cursor Q h
  · intro cursor h
    exact ShorECDLP.Entrant.BorrowFlag.divisionProgram_tCount 32768 cursor _ h
  · intro cursor h
    exact pointSquareProgram_tCount 32768 cursor _ h
  · intro cursor h
    exact fieldLookupAddProgram_tCount_source coeffs .tripleX _ cursor Q (by simp) h
  · intro cursor h
    exact ShorECDLP.Entrant.BorrowFlag.multiplicationProgram_tCount 32768 cursor _ h
  · intro cursor h
    exact xNegateProgram_tCount 32768 cursor _ h
  · intro cursor h
    exact fieldLookupAddProgram_tCount_source coeffs .x _ cursor Q (by simp) h
  · intro cursor h
    unfold windowYNegate
    exact yNegateProgram_tCount cursor _ h
  · intro cursor h
    exact fieldLookupAddProgram_tCount_source coeffs .negY _ cursor Q (by simp) h

end ShorECDLP.Entrant.Single.Physical

end

-- ==== part: Single/Batch ====

section
/-! Table-parametric in-place exceptional correction. The correction and
its semantic proof adapt the Streaming construction (VerifiedQC PR #551,
Apache-2.0) to the mixed-width coefficient table. -/

namespace ShorECDLP.Entrant.Single.Physical
open ShorECDLP Classical Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

def tableRows (label : Nat) : Fin 32768 := ⟨label % 32768, Nat.mod_lt _ (by decide)⟩

noncomputable def placedBatchSource (coeffs : Fin 32768 → PointCoeff) (Q : Point) : AdaptiveCircuit :=
  ipxSourceOps (readConstant coeffs Q) tableRows batchWindowTree pointLookupPath ipxSchedule

noncomputable def placedBatchState (coeffs : Fin 32768 → PointCoeff) (Q : Point) (st : BasisState) : BasisState :=
  Classical.run (ipxUnitaryOps (readConstant coeffs Q) tableRows batchWindowTree pointLookupPath ipxSchedule) st

attribute [local irreducible] ipxUnitaryOps ipxSourceOps

theorem placedBatchSource_state (coeffs : Fin 32768 → PointCoeff) (Q : Point) :
    CoherentlyImplementsOn (placedBatchSource coeffs Q) (Finsupp.lmapDomain ℂ ℂ (placedBatchState coeffs Q))
      (IpxInv pointLookupPath) := by
  have h := ipxSourceOps_coherent coeffs Q tableRows batchWindowTree pointLookupPath
    ipxGeometry_window ipxSchedule
  apply h.congrIdeal
  intro st _
  rw [run_ket_agrees_classical _ st (ipxUnitaryOps_HPFree _ _ _ _ _)]
  simp only [placedBatchState,ket,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]

theorem placedBatchState_frame (coeffs : Fin 32768 → PointCoeff) (Q : Point) (s : BasisState)
    (hs : IpxInv pointLookupPath s) (w : Wire) (hw : w ∉ pointLogicalWires)
    (hf : ∀ k, w ≠ ipxFlag k) : placedBatchState coeffs Q s w = s w :=
  (ipxUnitary_model coeffs Q tableRows batchWindowTree pointLookupPath
    ipxGeometry_window ipxSchedule s hs).2.2 w hw hf

theorem placedBatchState_pointWrite (coeffs : Fin 32768 → PointCoeff) (Q : Point) (st : BasisState)
    (hv : Secp256k1ZeroAllowedInputValid st) (hq : st 836 = true)
    {x y : Fp} (hC : curve.toAffine.Nonsingular x y)
    (hr : constantPoint Q (coeffs (tableRows (batchWindowTree.routeLabel st))) = .some hC)
    (hord : order • (.some hC : Point) = 0)
    (P : Point) (hdata : pointStateCoordinates st = fig14EncodedEquiv x y (fig14PointEncoding P)) :
    placedBatchState coeffs Q st = pointWrite (P + .some hC) st := by
  have hinv := ipxInv_of_valid st hv hq
  have hm := ipxUnitary_model coeffs Q tableRows batchWindowTree pointLookupPath
    ipxGeometry_window ipxSchedule st hinv
  have hA : st ∘ accumulatorPort = coordinateWordBits (fig14EncodedEquiv x y (fig14PointEncoding P)) :=
    (accumulatorPort_coordinates st hv).trans (congrArg coordinateWordBits hdata)
  have hF : (fun k => st (ipxFlag k)) = fun _ => false := funext (ipxFlags_clean st hv)
  have hres := hm.1
  rw [hA,hF] at hres
  change _ = ipxModel _ _ at hres
  rw [ipxModel_point coeffs Q _ hC hr hord P] at hres
  have hacc := congrArg Prod.fst hres
  have hfl := congrArg Prod.snd hres
  dsimp only at hacc hfl
  apply ShorECDLP.Paper2607_13816.ChallengeMigration.accumulator_word_frame_ext
  · exact (accumulatorPort_encoding_iff _ _).mp hacc
  · intro v hv'
    by_cases hk : ∃ k, v = ipxFlag k
    · obtain ⟨k,rfl⟩ := hk
      exact (congrFun hfl k).trans (ipxFlags_clean st hv k).symm
    · push_neg at hk
      exact hm.2.2 v hv' hk

theorem tablePoint_order (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q = 0) (a : Nat) :
    order • tablePoint coeffs Q a = 0 := by
  unfold tablePoint constantPoint
  rw [nsmul_add, smul_comm order, smul_comm order, generator_nsmul_eq_zero, hQ, nsmul_zero, nsmul_zero, add_zero]

end ShorECDLP.Entrant.Single.Physical

end

-- ==== part: Single/State ====

section
/-! Table-parametric boundary composition adapted from the Apache-2.0
licensed Streaming `BatchedWindowState` module. Point arithmetic and its
exceptional cases are supplied by the existing coordinate and batch results. -/

namespace ShorECDLP.Entrant.Single.Physical
open ShorECDLP Classical Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨p_prime⟩

noncomputable def signedBatchState (coeffs : Fin 32768 → PointCoeff) (Q : Point) (s : BasisState) : BasisState :=
  windowYNegateState (placedBatchState coeffs Q (windowYNegateState s))

theorem pointWrite_frame_eq (P : Point) (s t : BasisState)
    (h : ∀ w, w ∉ pointLogicalWires → s w=t w) : pointWrite P s=pointWrite P t := by
  funext w
  by_cases hw : w ∈ pointLogicalWires
  · simp only [pointWrite,if_pos hw]
  · simp only [pointWrite,if_neg hw,h w hw]

theorem signedBatchState_pointWrite (coeffs : Fin 32768 → PointCoeff) (Q : Point) (s : BasisState)
    (hs : Secp256k1ZeroAllowedInputValid s) (hq : s 836 = true)
    {x y : Fp} (hC : curve.toAffine.Nonsingular x y)
    (hr : constantPoint Q (coeffs (tableRows
      (batchWindowTree.routeLabel (windowYNegateState s)))) = .some hC)
    (hord : order • (.some hC : Point) = 0)
    (P : Point)
    (hdata : pointStateCoordinates s =
      fig14EncodedEquiv x (if s 854 then y else -y) (fig14PointEncoding P)) :
    signedBatchState coeffs Q s = pointWrite (P + if s 854 then .some hC else -(.some hC)) s := by
  let P' : Point := if s 854 then P else -P
  have ht := windowYNegateState_ready s hs
  have htq : windowYNegateState s 836 = true :=
    ((windowYNegateState_correct s hs).2 836 (by decide)).trans hq
  have hd : pointStateCoordinates (windowYNegateState s) = fig14EncodedEquiv x y (fig14PointEncoding P') := by
    rw [windowYNegateState_coordinates s hs,hdata]
    cases hsg : s 854
    · simpa only [hsg,Bool.false_eq_true,ite_false,P',fig14PointEncoding_neg,encodedNegY] using
        fig14EncodedEquiv_negY x y (fig14PointEncoding P)
    · simp only [hsg,ite_true,P']
  have he := placedBatchState_pointWrite coeffs Q _ ht htq hC hr hord P' hd
  have hsign : placedBatchState coeffs Q (windowYNegateState s) 854 = s 854 :=
    (placedBatchState_frame coeffs Q _ (ipxInv_of_valid _ ht htq) 854 (by decide +kernel)
      (ipxFlag_ne_of_ge 854 (by decide))).trans
      ((windowYNegateState_correct s hs).2 854 (by decide +kernel))
  have hv : Secp256k1ZeroAllowedInputValid (placedBatchState coeffs Q (windowYNegateState s)) := by
    rw [he]; exact pointWrite_valid _ _ ht
  have hc : pointStateCoordinates (placedBatchState coeffs Q (windowYNegateState s)) =
      fig14PointEncoding (P' + .some hC) := by
    rw [he]; exact pointWrite_coordinates _ _
  unfold signedBatchState
  rw [windowYNegateState_pointWrite (P' + .some hC) _ hv hc,hsign,he,pointWrite_overwrite]
  have hpoint : (if s 854 then P' + .some hC else -(P' + .some hC)) =
      P + if s 854 then .some hC else -(.some hC) := by
    cases hsg : s 854 <;> simp [P',hsg,add_comm]
  rw [hpoint]
  apply pointWrite_frame_eq
  intro v hv
  apply (windowYNegateState_correct s hs).2 v
  intro hy
  exact hv (List.mem_append_right _ (List.mem_append_left _ hy))
noncomputable def batchedWindowState (coeffs : Fin 32768 → PointCoeff) (Q : Point) (s : BasisState) : BasisState :=
  signedBatchState coeffs Q (signedLookupCoordinateState
    (fun a => fieldValue (tablePoint coeffs Q a) .x) (fun a => fieldValue (tablePoint coeffs Q a) .y) s)

theorem batchedWindowState_finite (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q = 0)
    (s : BasisState) (hs : BatchedPointReady s) {x y : Fp}
    (hC : curve.toAffine.Nonsingular x y)
    (hr : tablePoint coeffs Q (tableAddressValue pointLookupAddress s)=.some hC)
    (P : Point) (hP : pointStateCoordinates s=fig14PointEncoding P) :
    batchedWindowState coeffs Q s = pointWrite (P + if s 854 then .some hC else -(.some hC)) s := by
  let xs := fun a => fieldValue (tablePoint coeffs Q a) .x
  let ys := fun a => fieldValue (tablePoint coeffs Q a) .y
  let t := signedLookupCoordinateState xs ys s
  have ht : BatchedPointReady t := signedLookupCoordinateState_batchedReady xs ys s hs
  have ha : tableAddressValue pointLookupAddress t=tableAddressValue pointLookupAddress s := by
    apply tableAddressValue_congr
    intro v hv
    apply signedLookupCoordinateState_frame xs ys s hs.1 v
    · simp only [pointLookupAddress,List.mem_range'_1] at hv
      simp only [List.mem_range'_1]
      omega
    · simp only [pointLookupAddress,List.mem_range'_1] at hv
      simp only [List.mem_range'_1]
      omega
  have hz : t 854=s 854 := signedLookupCoordinateState_sign xs ys s hs.1
  have hr' : constantPoint Q (coeffs (tableRows
      (batchWindowTree.routeLabel (windowYNegateState t)))) = .some hC := by
    rw [batchWindowTree_route,windowYNegateState_address t ht.1.1,ha]
    exact hr
  have hx : xs (tableAddressValue pointLookupAddress s)=x.val := by simp [xs,hr,fieldValue,pointCoordinates]
  have hy : ys (tableAddressValue pointLookupAddress s)=y.val := by simp [ys,hr,fieldValue,pointCoordinates]
  have hyv : signedPointTableValue ys s=(if s 854 then y else -y).val := by
    unfold signedPointTableValue
    rw [hy]
    cases s 854 <;> simp [ZMod.neg_val']
  have hd : pointStateCoordinates t=fig14EncodedEquiv x (if t 854 then y else -y) (fig14PointEncoding P) := by
    rw [hz]
    dsimp only [t]
    rw [signedLookupCoordinateState_eq xs ys s hs.1,hx,hyv]
    rw [fig14CoordinateState_encoded x (if s 854 then y else -y) s hs.1.1 hs.1.2,hP]
  have he := signedBatchState_pointWrite coeffs Q t ht.1.1 ht.1.2 hC hr'
    (hr ▸ tablePoint_order coeffs Q hQ _) P hd
  change signedBatchState coeffs Q t= _
  rw [he,hz]
  apply pointWrite_frame_eq
  intro v hv
  exact signedLookupCoordinateState_frame xs ys s hs.1 v
    (fun hx => hv (List.mem_append_left _ hx))
    (fun hy => hv (List.mem_append_right _ (List.mem_append_left _ hy)))
theorem batchedWindowState_correct (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q = 0)
    (hn : ∀ a, tablePoint coeffs Q a ≠ 0)
    (s : BasisState) (hs : BatchedPointReady s)
    (P : Point) (hP : pointStateCoordinates s=fig14PointEncoding P) :
    batchedWindowState coeffs Q s = pointWrite
      (P + if s 854 then tablePoint coeffs Q (tableAddressValue pointLookupAddress s)
        else -tablePoint coeffs Q (tableAddressValue pointLookupAddress s)) s := by
  cases he : tablePoint coeffs Q (tableAddressValue pointLookupAddress s) with
  | zero => exact False.elim (hn _ he)
  | some hC => exact batchedWindowState_finite coeffs Q hQ s hs hC he P hP

theorem signedBatchState_middle_ready (coeffs : Fin 32768 → PointCoeff) (Q : Point) (s : BasisState)
    (hs : Secp256k1ZeroAllowedInputValid s) (hq : s 836 = true)
    {x y : Fp} (hC : curve.toAffine.Nonsingular x y)
    (hr : constantPoint Q (coeffs (tableRows
      (batchWindowTree.routeLabel (windowYNegateState s)))) = .some hC)
    (hord : order • (.some hC : Point) = 0)
    (P : Point)
    (hdata : pointStateCoordinates s =
      fig14EncodedEquiv x (if s 854 then y else -y) (fig14PointEncoding P)) :
    Secp256k1ZeroAllowedInputValid (placedBatchState coeffs Q (windowYNegateState s)) := by
  let P' : Point := if s 854 then P else -P
  have ht := windowYNegateState_ready s hs
  have htq : windowYNegateState s 836 = true :=
    ((windowYNegateState_correct s hs).2 836 (by decide)).trans hq
  have hd : pointStateCoordinates (windowYNegateState s) = fig14EncodedEquiv x y (fig14PointEncoding P') := by
    rw [windowYNegateState_coordinates s hs,hdata]
    cases hsg : s 854
    · simpa only [hsg,Bool.false_eq_true,ite_false,P',fig14PointEncoding_neg,encodedNegY] using
        fig14EncodedEquiv_negY x y (fig14PointEncoding P)
    · simp only [hsg,ite_true,P']
  rw [placedBatchState_pointWrite coeffs Q _ ht htq hC hr hord P' hd]
  exact pointWrite_valid _ _ ht

def SignedBatchReady (coeffs : Fin 32768 → PointCoeff) (Q : Point) (s : BasisState) : Prop :=
  BatchedPointReady s ∧ ∃ (x y : Fp) (hC : curve.toAffine.Nonsingular x y),
    constantPoint Q (coeffs (tableRows
      (batchWindowTree.routeLabel (windowYNegateState s)))) = .some hC ∧
    order • (.some hC : Point) = 0 ∧
    ∃ P : Point, pointStateCoordinates s =
      fig14EncodedEquiv x (if s 854 then y else -y) (fig14PointEncoding P)

end ShorECDLP.Entrant.Single.Physical

end

-- ==== part: Single/Body ====

section
/-! The existing full-size corrected physical body, with table rows supplied
by the caller. Adapted from the Apache-2.0 licensed Streaming WindowBody. -/

namespace ShorECDLP.Entrant.Single.Physical
open ShorECDLP Classical Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration ShorECDLP.Entrant.ZeroAdaptive

attribute [local irreducible] batchWindowTree
attribute [local irreducible] tailCoordinateProgram yNegateProgram
  ipxProgramOf sequenceProgram surroundCompiled relabelCompiled

theorem correction_count (start : Nat) :
    (ipxProgramOf tableRows batchWindowTree pointLookupPath start).1 = 432091 := by
  simp only [ipxProgramOf]
  rw [ipxOps_measurements _ _ _ ipxTree_layout, ipxSchedule_queries, batchWindowTree_nodes]
  norm_num [ipxSchedule_tests]

@[irreducible] def placedProgram (start : Nat) : (count : Nat) × Straight 32768 start (start+count) :=
  ipxProgramOf tableRows batchWindowTree pointLookupPath start

theorem placedProgram_run (coeffs : Fin 32768 → PointCoeff) (start : Nat) (Q : Point)
    (history : Fin start → Bool) :
    compiledRun (placedProgram start) (readConstant coeffs Q) history =
      (placedBatchSource coeffs Q).run := by
  unfold placedProgram compiledRun
  simp only [ipxProgramOf, lookupProgram_run, ipxOps_source, placedBatchSource]

def segments : List (FixedSegment 32768) :=
  [tailCoordinateProgram, placedProgram, yNegateProgram]

@[irreducible] noncomputable def sources (coeffs : Fin 32768 → PointCoeff) (Q : Point) : List AdaptiveCircuit :=
  [tailCoordinateCircuit (fun l => fieldValue (tablePoint coeffs Q l) .x)
    (fun l => fieldValue (tablePoint coeffs Q l) .y),
    placedBatchSource coeffs Q, windowYNegate]

@[irreducible] def core (start : Nat) : (count : Nat) × Straight 32768 start (start+count) :=
  sequenceProgram 32768 segments start

theorem core_run (coeffs : Fin 32768 → PointCoeff) (start : Nat) (Q : Point)
    (history : Fin start → Bool) :
    compiledRun (core start) (readConstant coeffs Q) history =
      (sequenceCircuit (sources coeffs Q)).run := by
  unfold core
  apply sequenceProgram_run
  unfold segments sources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ .nil))
  · intro cursor h; exact tailCoordinateProgram_run coeffs cursor Q h
  · intro cursor h; exact placedProgram_run coeffs cursor Q h
  · intro cursor h; exact yNegateProgram_run cursor _ h

@[irreducible] def prepared (start : Nat) : (count : Nat) × Straight 32768 start (start+count) :=
  surroundCompiled (signedAddressCircuit 836 854 pointLookupAddress)
    (signedAddressCircuit 836 854 pointLookupAddress) (core start)

@[irreducible] noncomputable def preparedSource (coeffs : Fin 32768 → PointCoeff) (Q : Point) : AdaptiveCircuit :=
  (AdaptiveCircuit.unitary (signedAddressCircuit 836 854 pointLookupAddress) .done).seq
    ((sequenceCircuit (sources coeffs Q)).seq
      (AdaptiveCircuit.unitary (signedAddressCircuit 836 854 pointLookupAddress) .done))

theorem prepared_run (coeffs : Fin 32768 → PointCoeff) (start : Nat) (Q : Point)
    (history : Fin start → Bool) :
    compiledRun (prepared start) (readConstant coeffs Q) history =
      (preparedSource coeffs Q).run := by
  unfold prepared preparedSource
  exact surroundCompiled_run _ _ _ _ _ _ (core_run coeffs start Q history)

theorem coordinate_count (start : Nat) : (tailCoordinateProgram start).1 = 30272696 := by
  have h := sharedTailCoordinateProgram_count (.right ⟨0, by decide⟩) start
  simpa only [sharedTailCoordinateProgram, reindexCompiled] using h

theorem negate_count (start : Nat) : (yNegateProgram start).1 = 1022 := by
  have h := sharedYNegateProgram_count (.right ⟨0, by decide⟩) start
  simpa only [sharedYNegateProgram, reindexCompiled] using h

theorem placed_count (start : Nat) : (placedProgram start).1 = 432091 := by
  unfold placedProgram
  exact correction_count start

private theorem sequence_count (n : Nat) (ps : List (FixedSegment n)) (counts : List Nat)
    (h : List.Forall₂ (fun p count => ∀ start, (p start).1 = count) ps counts) (start : Nat) :
    (sequenceProgram n ps start).1 = counts.sum := by
  induction h generalizing start with
  | nil => simp only [sequenceProgram, List.sum_nil]
  | cons hp _ ih =>
    simp only [sequenceProgram, appendCompiled, List.sum_cons]
    rw [hp, ih]

theorem core_count (start : Nat) : (core start).1 = 30705809 := by
  have h := sequence_count 32768 segments ([30272696, 432091, 1022] : List Nat) (by
    unfold segments
    exact List.Forall₂.cons coordinate_count
      (List.Forall₂.cons placed_count (List.Forall₂.cons negate_count .nil))) start
  unfold core
  exact h

theorem prepared_count (start : Nat) : (prepared start).1 = 30705809 := by
  unfold prepared
  rw [surroundCompiled_count, core_count]

@[irreducible] def actual : OuterWindow 32768 :=
  closedWindow (castFinish (by rw [prepared_count])
    (relabelStraight (windowAddressPerm 855 (by decide)) (prepared 0).2))

theorem actual_run (coeffs : Fin 32768 → PointCoeff) (start : Nat) (Q : Point)
    (history : Fin start → Bool) :
    ((actual.program start).instantiate (readConstant coeffs Q) history).run =
      ((preparedSource coeffs Q).relabel (windowAddressPerm 855 (by decide))).run := by
  unfold actual
  simp only [closedWindow_run, castFinish_instantiate, relabelStraight_instantiate, AdaptiveCircuit.run_relabel]
  have h := prepared_run coeffs 0 Q Fin.elim0
  unfold compiledRun at h
  exact congrArg (List.map (InstrumentBranch.relabel (windowAddressPerm 855 (by decide)))) h

end ShorECDLP.Entrant.Single.Physical

end

-- ==== part: Single/Coherent ====

section
/-! Coherent composition of the full-size physical windows for arbitrary
public row values. Adapted from the Apache-2.0 licensed Streaming boundary
and address-placement proofs. The library supplies all arithmetic coherence. -/

namespace ShorECDLP.Entrant.Single.Physical
open ShorECDLP Classical Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration ShorECDLP.Entrant.ZeroAdaptive
local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨p_prime⟩

private theorem restrictCoherent {a : AdaptiveCircuit} {v : State →ₗ[ℂ] State}
    {P R : BasisState → Prop} (h : CoherentlyImplementsOn a v R)
    (hp : ∀ s, P s → R s) : CoherentlyImplementsOn a v P := by
  obtain ⟨cs,hc,hm⟩ := h
  exact ⟨cs,hc.imp (fun _ _ hb s hs => hb s (hp s hs)),hm⟩

noncomputable def signedBatchSource (coeffs : Fin 32768 → PointCoeff) (Q : Point) : AdaptiveCircuit :=
  (windowYNegate.seq (placedBatchSource coeffs Q)).seq windowYNegate

theorem signedBatchSource_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Point) :
    CoherentlyImplementsOn (signedBatchSource coeffs Q)
      (Finsupp.lmapDomain ℂ ℂ (signedBatchState coeffs Q)) (SignedBatchReady coeffs Q) := by
  have hneg : CoherentlyImplementsOn windowYNegate (Finsupp.lmapDomain ℂ ℂ windowYNegateState)
      (SignedBatchReady coeffs Q) := restrictCoherent windowYNegate_coherent (fun s hs => hs.1.1.1)
  have hfirst := composeCoherent hneg (placedBatchSource_state coeffs Q) (fun s hs => by
    have hn := windowYNegateState_batchedReady s hs.1
    exact ipxInv_of_valid _ hn.1.1 hn.1.2)
  have hlast := composeCoherent hfirst windowYNegate_coherent (by
    intro s hs
    obtain ⟨hr,x,y,hC,hrow,hord,P,hdata⟩ := hs
    exact signedBatchState_middle_ready coeffs Q s hr.1.1 hr.1.2 hC hrow hord P hdata)
  exact hlast
theorem batchedWindow_coordinate_ready (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q = 0)
    (s : BasisState) (hs : BatchedPointReady s) {x y : Fp}
    (hC : curve.toAffine.Nonsingular x y)
    (hr : tablePoint coeffs Q (tableAddressValue pointLookupAddress s)=.some hC)
    (P : Point) (hP : pointStateCoordinates s=fig14PointEncoding P) :
    SignedBatchReady coeffs Q (signedLookupCoordinateState
      (fun a => fieldValue (tablePoint coeffs Q a) .x) (fun a => fieldValue (tablePoint coeffs Q a) .y) s) := by
  let xs := fun a => fieldValue (tablePoint coeffs Q a) .x
  let ys := fun a => fieldValue (tablePoint coeffs Q a) .y
  let t := signedLookupCoordinateState xs ys s
  have ht : BatchedPointReady t := signedLookupCoordinateState_batchedReady xs ys s hs
  have ha : tableAddressValue pointLookupAddress t=tableAddressValue pointLookupAddress s := by
    apply tableAddressValue_congr
    intro v hv
    apply signedLookupCoordinateState_frame xs ys s hs.1 v
    · simp only [pointLookupAddress,List.mem_range'_1] at hv
      simp only [List.mem_range'_1]
      omega
    · simp only [pointLookupAddress,List.mem_range'_1] at hv
      simp only [List.mem_range'_1]
      omega
  have hz : t 854=s 854 := signedLookupCoordinateState_sign xs ys s hs.1
  have hr' : constantPoint Q (coeffs (tableRows
      (batchWindowTree.routeLabel (windowYNegateState t)))) = .some hC := by
    rw [batchWindowTree_route,windowYNegateState_address t ht.1.1,ha]
    exact hr
  have hx : xs (tableAddressValue pointLookupAddress s)=x.val := by simp [xs,hr,fieldValue,pointCoordinates]
  have hy : ys (tableAddressValue pointLookupAddress s)=y.val := by simp [ys,hr,fieldValue,pointCoordinates]
  have hyv : signedPointTableValue ys s=(if s 854 then y else -y).val := by
    unfold signedPointTableValue
    rw [hy]
    cases s 854 <;> simp [ZMod.neg_val']
  have hd : pointStateCoordinates t=fig14EncodedEquiv x (if t 854 then y else -y) (fig14PointEncoding P) := by
    rw [hz]
    dsimp only [t]
    rw [signedLookupCoordinateState_eq xs ys s hs.1,hx,hyv]
    rw [fig14CoordinateState_encoded x (if s 854 then y else -y) s hs.1.1 hs.1.2,hP]
  exact ⟨ht,x,y,hC,hr',hr ▸ tablePoint_order coeffs Q hQ _,P,hd⟩

theorem batchedWindowSources_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q = 0)
    (hn : ∀ a, tablePoint coeffs Q a ≠ 0) :
    CoherentlyImplementsOn (sequenceCircuit (sources coeffs Q))
      (Finsupp.lmapDomain ℂ ℂ (batchedWindowState coeffs Q)) BatchedWindowValid := by
  let xs := fun a => fieldValue (tablePoint coeffs Q a) .x
  let ys := fun a => fieldValue (tablePoint coeffs Q a) .y
  have hfirst : CoherentlyImplementsOn (tailCoordinateCircuit xs ys)
      (Finsupp.lmapDomain ℂ ℂ (fun s => windowYNegateState (signedLookupCoordinateState xs ys s)))
      BatchedWindowValid :=
    restrictCoherent (tailCoordinateCircuit_coherent xs ys) (fun s hs => hs.1.1)
  have hready (s : BasisState) (hs : BatchedWindowValid s) :
      SignedBatchReady coeffs Q (signedLookupCoordinateState xs ys s) := by
    obtain ⟨hs,P,hP⟩ := hs
    cases he : tablePoint coeffs Q (tableAddressValue pointLookupAddress s) with
    | zero => exact False.elim (hn _ he)
    | some hC => exact batchedWindow_coordinate_ready coeffs Q hQ s hs hC he P hP
  have hmid := composeCoherent hfirst (placedBatchSource_state coeffs Q) (fun s hs => by
    have hb := windowYNegateState_batchedReady _ (hready s hs).1
    exact ipxInv_of_valid _ hb.1.1 hb.1.2)
  have hlast := composeCoherent hmid windowYNegate_coherent (fun s hs => by
    obtain ⟨hr,x,y,hC,hrow,hord,P,hdata⟩ := hready s hs
    exact signedBatchState_middle_ready coeffs Q _ hr.1.1 hr.1.2 hC hrow hord P hdata)
  simpa only [sources,sequenceCircuit,adaptive_seq_assoc,adaptive_seq_done,
    batchedWindowState,signedBatchState,xs,ys] using hlast
theorem batchedWindowState_valid (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q = 0)
    (hn : ∀ a, tablePoint coeffs Q a ≠ 0)
    (s : BasisState) (hs : BatchedWindowValid s) : BatchedWindowValid (batchedWindowState coeffs Q s) := by
  obtain ⟨hs,P,hP⟩ := hs
  rw [batchedWindowState_correct coeffs Q hQ hn s hs P hP]
  exact ⟨pointWrite_batchedReady _ s hs,_,pointWrite_coordinates _ s⟩

noncomputable def preparedBatchState (coeffs : Fin 32768 → PointCoeff) (Q : Point) (s : BasisState) : BasisState :=
  batchPrepareState (batchedWindowState coeffs Q (batchPrepareState s))

theorem preparedBatchState_correct (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q = 0)
    (hn : ∀ a, tablePoint coeffs Q a ≠ 0)
    (s : BasisState) (hs : BatchedPointReady s) (P : Point) (hP : pointStateCoordinates s=fig14PointEncoding P) :
    preparedBatchState coeffs Q s = pointWrite
      (P + if s 854 then tablePoint coeffs Q (tableAddressValue pointLookupAddress (batchPrepareState s))
        else -tablePoint coeffs Q (tableAddressValue pointLookupAddress (batchPrepareState s))) s := by
  unfold preparedBatchState
  rw [batchedWindowState_correct coeffs Q hQ hn _ (batchPrepareState_ready s hs) P
    ((batchPrepareState_coordinates s).trans hP),batchPrepareState_pointWrite,
    batchPrepareState_involution,batchPrepareState_frame s 854 (by decide)]

theorem batchPrepare_coherent : CoherentlyImplementsOn
    (.unitary (signedAddressCircuit 836 854 pointLookupAddress) .done)
    (Finsupp.lmapDomain ℂ ℂ batchPrepareState) BatchedWindowValid := by
  have h := CoherentlyImplementsOn.unitary (signedAddressCircuit 836 854 pointLookupAddress) BatchedWindowValid
  apply h.congrIdeal
  intro s hs
  simpa only [Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,ket,batchPrepareState] using
    signedAddressCircuit_ket 836 854 pointLookupAddress (by decide) (by decide) (by decide) s

attribute [local irreducible] batchPrepareState batchedWindowState

theorem preparedSource_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q = 0)
    (hn : ∀ a, tablePoint coeffs Q a ≠ 0) :
    CoherentlyImplementsOn (preparedSource coeffs Q)
      (Finsupp.lmapDomain ℂ ℂ (preparedBatchState coeffs Q)) BatchedWindowValid := by
  have hc := composeCoherent (batchedWindowSources_coherent coeffs Q hQ hn) batchPrepare_coherent
    (batchedWindowState_valid coeffs Q hQ hn)
  have h := composeCoherent (f := batchPrepareState)
    (g := fun s => batchPrepareState (batchedWindowState coeffs Q s))
    batchPrepare_coherent hc batchPrepareState_valid
  unfold preparedSource
  exact h

private theorem parkedWindow_valid (start : Nat) (hs : 855≤start) (s : BasisState)
    (hv : PointLookupValid s) : PointLookupValid (relabelBasis (windowAddressPerm start hs).symm s) := by
  have he (w : Wire) (hw : w<839) : relabelBasis (windowAddressPerm start hs).symm s w=s w := by
    simp only [relabelBasis,Equiv.symm_symm,windowAddressPerm_core start hs w hw]
  refine ⟨⟨?_,?_,?_,?_⟩,?_⟩
  · intro w hw
    have hb : w<839 := by simp only [List.mem_append,List.mem_range'_1] at hw; (try dsimp only [Wire] at *); omega
    rw [he w hb]
    exact hv.1.1 w hw
  · rw [he 837 (by decide)]; exact hv.1.2.1
  · have hh : wireValues (List.range' 263 256) (relabelBasis (windowAddressPerm start hs).symm s)=wireValues (List.range' 263 256) s := by
      apply List.map_congr_left
      intro w hw
      apply he w
      simp only [List.mem_range'_1] at hw
      (try dsimp only [Wire] at *); omega
    rw [hh]; exact hv.1.2.2.1
  · have hh : wireValues (List.range' 580 256) (relabelBasis (windowAddressPerm start hs).symm s)=wireValues (List.range' 580 256) s := by
      apply List.map_congr_left
      intro w hw
      apply he w
      simp only [List.mem_range'_1] at hw
      (try dsimp only [Wire] at *); omega
    rw [hh]; exact hv.1.2.2.2
  · rw [he 836 (by decide)]; exact hv.2

private theorem point_bank_bound (w : Wire) (hw : w∈pointLogicalWires) : w<839 := by
  simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1] at hw
  dsimp only [Wire] at *
  omega
private theorem relabel_pointWrite (start : Nat) (hs : 855≤start)
    (P : ShorECDLP.Secp256k1.Point) (s : BasisState) :
    relabelBasis (windowAddressPerm start hs)
      (pointWrite P (relabelBasis (windowAddressPerm start hs).symm s))=pointWrite P s := by
  have hsym : (windowAddressPerm start hs).symm=windowAddressPerm start hs := rfl
  funext w
  by_cases hw : w∈pointLogicalWires
  · have he := windowAddressPerm_core start hs w (point_bank_bound w hw)
    simp [relabelBasis,hsym,he,pointWrite,hw]
  · have hn : (windowAddressPerm start hs).symm w∉pointLogicalWires := by
      intro h
      have he := windowAddressPerm_core start hs _ (point_bank_bound _ h)
      rw [Equiv.apply_symm_apply] at he
      exact hw (he ▸ h)
    simp [relabelBasis,pointWrite,hw,hn]

private theorem relabel_coordinates (start : Nat) (hs : 855≤start) (s : BasisState) :
    pointStateCoordinates (relabelBasis (windowAddressPerm start hs).symm s)=pointStateCoordinates s := by
  have he (bits : List Wire) (hb : ∀ w∈bits,w<839) :
      wireValues bits (relabelBasis (windowAddressPerm start hs).symm s)=wireValues bits s := by
    apply List.map_congr_left
    intro w hw
    simp only [relabelBasis,Equiv.symm_symm,windowAddressPerm_core start hs w (hb w hw)]
  have hx := he (List.range' 263 256) (by intro w hw; simp only [List.mem_range'_1] at hw; dsimp only [Wire] at *; omega)
  have hy := he (List.range' 580 256) (by intro w hw; simp only [List.mem_range'_1] at hw; dsimp only [Wire] at *; omega)
  simp only [pointStateCoordinates,hx,hy,relabelBasis,Equiv.symm_symm,windowAddressPerm_core start hs 838 (by decide)]


theorem windowAddressPerm_workspace (w : Wire) (hw : w ∈ batchWorkspace) :
    windowAddressPerm 855 (by decide) w=w := by
  simp [batchWorkspace] at hw

theorem actualWindow_pullback_ready (s : BasisState) (hs : BatchedPointReady s) :
    BatchedPointReady (relabelBasis (windowAddressPerm 855 (by decide)).symm s) := by
  refine ⟨parkedWindow_valid 855 (by decide) s hs.1,?_⟩
  intro w hw
  change s (windowAddressPerm 855 (by decide) w)=false
  rw [windowAddressPerm_workspace w hw]
  exact hs.2 w hw

theorem actualWindow_pullback_valid (s : BasisState) (hs : BatchedWindowValid s) :
    BatchedWindowValid (relabelBasis (windowAddressPerm 855 (by decide)).symm s) := by
  obtain ⟨hs,P,hP⟩ := hs
  exact ⟨actualWindow_pullback_ready s hs,P,(relabel_coordinates 855 (by decide) s).trans hP⟩

noncomputable def actualBatchedWindowState (coeffs : Fin 32768 → PointCoeff) (Q : Point) (s : BasisState) : BasisState :=
  relabelBasis (windowAddressPerm 855 (by decide))
    (preparedBatchState coeffs Q (relabelBasis (windowAddressPerm 855 (by decide)).symm s))

theorem actualBatchedWindow_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q = 0)
    (hn : ∀ a, tablePoint coeffs Q a ≠ 0)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((actual.program start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (actualBatchedWindowState coeffs Q)) BatchedWindowValid := by
  have h := (preparedSource_coherent coeffs Q hQ hn).relabel (windowAddressPerm 855 (by decide))
  have hr : CoherentlyImplementsOn ((preparedSource coeffs Q).relabel (windowAddressPerm 855 (by decide)))
      ((relabelState (windowAddressPerm 855 (by decide))).comp
        ((Finsupp.lmapDomain ℂ ℂ (preparedBatchState coeffs Q)).comp
          (relabelState (windowAddressPerm 855 (by decide)).symm))) BatchedWindowValid := by
    obtain ⟨cs,hc,hm⟩ := h
    exact ⟨cs,hc.imp (fun _ _ hb s hs => hb s (actualWindow_pullback_valid s hs)),hm⟩
  have he : CoherentlyImplementsOn ((preparedSource coeffs Q).relabel (windowAddressPerm 855 (by decide)))
      (Finsupp.lmapDomain ℂ ℂ (actualBatchedWindowState coeffs Q)) BatchedWindowValid := by
    apply hr.congrIdeal
    intro s hs
    simp [actualBatchedWindowState,LinearMap.comp_apply,relabelState,ket]
  unfold CoherentlyImplementsOn at he ⊢
  rw [actual_run coeffs start Q history]
  exact he

theorem actualBatchedWindowState_correct (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q = 0)
    (hn : ∀ a, tablePoint coeffs Q a ≠ 0)
    (s : BasisState) (hs : BatchedPointReady s) (P : Point) (hP : pointStateCoordinates s=fig14PointEncoding P) :
    actualBatchedWindowState coeffs Q s = pointWrite
      (P + if s 870 then tablePoint coeffs Q (tableAddressValue pointLookupAddress
          (batchPrepareState (relabelBasis (windowAddressPerm 855 (by decide)).symm s)))
        else -tablePoint coeffs Q (tableAddressValue pointLookupAddress
          (batchPrepareState (relabelBasis (windowAddressPerm 855 (by decide)).symm s)))) s := by
  unfold actualBatchedWindowState
  rw [preparedBatchState_correct coeffs Q hQ hn _ (actualWindow_pullback_ready s hs) P
    ((relabel_coordinates 855 (by decide) s).trans hP),relabel_pointWrite]
  have he : relabelBasis (windowAddressPerm 855 (by decide)).symm s 854=s 870 := by
    simp only [relabelBasis,Equiv.symm_symm]
    exact congrArg s (windowAddressPerm_address 855 (by decide) 15 (by decide))
  rw [he]

private theorem address_word_eq (bits : List Wire) (s : BasisState) :
    tableAddressValue bits s=boolWordToNat (wireValues bits s) := by
  induction bits with
  | nil => rfl
  | cons w ws ih => simpa only [tableAddressValue,wireValues,List.map_cons,boolWordToNat] using congrArg (fun n => (s w).toNat+2*n) ih

theorem actualWindow_selected_address (s : BasisState) (hs : BatchedPointReady s) :
    tableAddressValue pointLookupAddress
      (batchPrepareState (relabelBasis (windowAddressPerm 855 (by decide)).symm s))=
      signedTableAddress 32768 (windowRawDigit 0 s) := by
  have hq : relabelBasis (windowAddressPerm 855 (by decide)).symm s 836=true :=
    (actualWindow_pullback_ready s hs).1.2
  rw [address_word_eq,batchPrepareState,signedAddressState_value _ _ _ _ hq]
  have ha := parkedWindow_address 855 (by decide) s
  rw [address_word_eq,address_word_eq] at ha
  have hz : relabelBasis (windowAddressPerm 855 (by decide)).symm s 854=s 870 := by
    exact congrArg s (windowAddressPerm_address 855 (by decide) 15 (by decide))
  rw [ha,hz]
  rfl


theorem actualBatchedWindowState_selected (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q = 0)
    (hn : ∀ a, tablePoint coeffs Q a ≠ 0)
    (s : BasisState) (hs : BatchedPointReady s) (P : Point) (hP : pointStateCoordinates s=fig14PointEncoding P) :
    actualBatchedWindowState coeffs Q s = pointWrite
      (P + if s 870 then tablePoint coeffs Q (signedTableAddress 32768 (windowRawDigit 0 s))
        else -tablePoint coeffs Q (signedTableAddress 32768 (windowRawDigit 0 s))) s := by
  rw [actualBatchedWindowState_correct coeffs Q hQ hn s hs P hP,actualWindow_selected_address s hs]

theorem actualBatchedWindowState_valid (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q = 0)
    (hn : ∀ a, tablePoint coeffs Q a ≠ 0)
    (s : BasisState) (hs : BatchedWindowValid s) : BatchedWindowValid (actualBatchedWindowState coeffs Q s) := by
  obtain ⟨hs,P,hP⟩ := hs
  rw [actualBatchedWindowState_selected coeffs Q hQ hn s hs P hP]
  exact ⟨pointWrite_batchedReady _ s hs,_,pointWrite_coordinates _ s⟩

theorem actualBatchedWindowState_frame (coeffs : Fin 32768 → PointCoeff) (Q : Point) (hQ : order • Q = 0)
    (hn : ∀ a, tablePoint coeffs Q a ≠ 0)
    (s : BasisState) (hs : BatchedWindowValid s) (v : Wire) (hv : v∉pointLogicalWires) :
    actualBatchedWindowState coeffs Q s v=s v := by
  obtain ⟨hs,P,hP⟩ := hs
  rw [actualBatchedWindowState_selected coeffs Q hQ hn s hs P hP]
  simp [pointWrite,hv]

end ShorECDLP.Entrant.Single.Physical

end

-- ==== part: Single/Schedule ====

section
/-! A 263-bit axis uses eight 16-bit windows followed by nine 15-bit windows.
The address definition below reuses the signed-address convention of the
Apache-2.0 licensed 2607_13816 submission. -/

namespace ShorECDLP.Entrant.Single

open ShorECDLP.Paper2607_13816

@[irreducible] def widths : List Nat :=
  [16, 16, 16, 16, 16, 16, 16, 16, 15, 15, 15, 15, 15, 15, 15, 15, 15]

@[irreducible] def exponents : List Nat :=
  [247, 231, 215, 199, 183, 167, 151, 135, 120, 105, 90, 75, 60, 45, 30, 15, 0]

@[irreducible] def rightWidths : List Nat := List.replicate 14 16

@[irreducible] def rightExponents : List Nat :=
  [208, 192, 176, 160, 144, 128, 112, 96, 80, 64, 48, 32, 16, 0]

theorem rightWidths_sum : rightWidths.sum = 224 := by simp [rightWidths]

theorem widths_length : widths.length = 17 := by
  simp [widths]

theorem widths_sum : widths.sum = 263 := by
  simp [widths]

theorem exponents_length : exponents.length = 17 := by
  simp [exponents]

/-- The zero padding bit is between the low magnitude bits and the sign. -/
def paddedValue (low : Nat) (sign : Bool) : Nat := low + 32768 * sign.toNat

def logicalValue (low : Nat) (sign : Bool) : Nat := low + 16384 * sign.toNat

/-- Aliasing the two physical address halves preserves the logical address. -/
theorem padded_address (low : Nat) (sign : Bool) (hlow : low < 16384) :
    signedTableAddress 32768 (paddedValue low sign) % 16384 =
      signedTableAddress 16384 (logicalValue low sign) := by
  cases sign with
  | false =>
    have hbig : low < 32768 := by omega
    have hsub : 32767 - low = 16384 + (16383 - low) := by omega
    have hrem : 16383 - low < 16384 := by omega
    simp only [paddedValue, logicalValue, Bool.toNat_false, Nat.mul_zero, Nat.add_zero,
      signedTableAddress, if_pos hbig, if_pos hlow]
    rw [hsub, Nat.add_mod]
    simp [Nat.mod_eq_of_lt hrem]
  | true =>
    have hbig : ¬ low + 32768 < 32768 := by omega
    have hsmall : ¬ low + 16384 < 16384 := by omega
    simp only [paddedValue, logicalValue, Bool.toNat_true, Nat.mul_one,
      signedTableAddress, if_neg hbig, if_neg hsmall]
    have h1 : low + 32768 - 32768 = low := by omega
    have h2 : low + 16384 - 16384 = low := by omega
    rw [h1, h2, Nat.mod_eq_of_lt hlow]

/-- Static positions for variable-width windows with fixed body record counts. -/
def positions : List (Nat × Nat) → Nat → List Nat
  | [], _ => []
  | (count, width) :: ws, start =>
      List.range' (start + count) width ++ positions ws (start + count + width)

def recordCount : List (Nat × Nat) → Nat
  | [] => 0
  | (count, width) :: ws => count + width + recordCount ws

theorem positions_length (ws : List (Nat × Nat)) (start : Nat) :
    (positions ws start).length = (ws.map Prod.snd).sum := by
  induction ws generalizing start with
  | nil => simp [positions]
  | cons w ws ih =>
    rcases w with ⟨count, width⟩
    simp [positions, ih]

theorem positions_bounds (ws : List (Nat × Nat)) (start i : Nat)
    (hi : i ∈ positions ws start) : start ≤ i ∧ i < start + recordCount ws := by
  induction ws generalizing start with
  | nil => simp [positions] at hi
  | cons w ws ih =>
    rcases w with ⟨count, width⟩
    simp only [positions, List.mem_append] at hi
    rcases hi with hi | hi
    · have h := List.mem_range'.mp hi
      simp only [recordCount]
      omega
    · have h := ih _ hi
      simp only [recordCount]
      omega

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/Outer ====

section
/-! Variable-width outer-axis skeleton adapted from the Apache-2.0 licensed
2607_13816 challenge migration. The caller must establish each window's
coherent semantics and bank cleanliness. -/

namespace ShorECDLP.Entrant.Single

open Quantum ShorECDLP.Challenge ShorECDLP.Paper2607_13816
open ShorECDLP.Paper2607_13816.ChallengeMigration

structure Window (n : Nat) where
  wires : List Wire
  count : Nat
  program : (start : Nat) → Straight n start (start + count)

def axisCount {n : Nat} : List (Window n) → Nat
  | [] => 0
  | w :: ws => w.count + w.wires.length + axisCount ws

def nextPrior {start : Nat} (count width : Nat) (prior : List (Fin start)) :
    List (Fin (start + count + width)) :=
  (List.ofFn (fun i : Fin width =>
    (⟨start + count + i.val, by omega⟩ : Fin (start + count + width)))).reverse ++
    prior.map (fun i => ⟨i.val, by omega⟩)

/-- Within an axis, feedback tracks only preceding Fourier outputs. -/
def axis {n : Nat} :
    (ws : List (Window n)) → (start : Nat) → List (Fin start) →
      Straight n start (start + axisCount ws)
  | [], _, _ => .done
  | w :: ws, start, prior =>
    let fourier : Straight n (start+w.count) (start+w.count+w.wires.length) :=
      castFinish (by simp) (fourierProgram n .inverse w.wires (start+w.count) (bankPrior w.count prior))
    castFinish (by simp only [axisCount]; omega)
      ((prepareOuterBank w.wires.reverse (w.program start)).append (fourier.append
        (axis ws (start+w.count+w.wires.length) (nextPrior w.count w.wires.length prior))))

def axisPositions {n : Nat} (ws : List (Window n)) (start : Nat) : List Nat :=
  positions (ws.map (fun w => (w.count, w.wires.length))) start

theorem axisPositions_length {n : Nat} (ws : List (Window n)) (start : Nat) :
    (axisPositions ws start).length = (ws.map (fun w => w.wires.length)).sum := by
  simp only [axisPositions, positions_length, List.map_map, Function.comp_def]

theorem recordCount_eq_axisCount {n : Nat} (ws : List (Window n)) :
    recordCount (ws.map (fun w => (w.count, w.wires.length))) = axisCount ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [recordCount, axisCount, ih]

theorem axisPositions_bounds {n : Nat} (ws : List (Window n)) (start i : Nat)
    (hi : i ∈ axisPositions ws start) : start ≤ i ∧ i < start + axisCount ws := by
  have h := positions_bounds (ws.map (fun w => (w.count, w.wires.length))) start i
    (show i ∈ positions (ws.map (fun w => (w.count, w.wires.length))) start from hi)
  simpa only [recordCount_eq_axisCount] using h

/-- Evidence that a selected position was produced by a Fourier bank. -/
def FourierRecord {n : Nat} (read : ConstantBit n → Bool)
    (whole : List Bool) (i : Nat) : Prop :=
  ∃ (wires : List Wire) (bankStart : Nat) (prior : List (Fin bankStart))
      (h : Fin bankStart → Bool) (f : InstrumentBranch) (bit : Fin wires.length),
      f ∈ ((fourierProgram n .inverse wires bankStart prior).instantiate read h).run ∧
      i = bankStart + bit.val ∧ whole[i]? = f.history[bit.val]? ∧
      List.ofFn h = whole.take bankStart

theorem axis_records {n : Nat} (ws : List (Window n))
    (start : Nat) (prior : List (Fin start)) (read : ConstantBit n → Bool)
    (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((axis ws start prior).instantiate read history).run) :
    ∀ i ∈ axisPositions ws start, FourierRecord read (List.ofFn history ++ b.history) i := by
  induction ws generalizing start b with
  | nil => intro i hi; simp [axisPositions, positions] at hi
  | cons w ws ih =>
    simp only [axis, castFinish_instantiate] at hb
    obtain ⟨h₁, a, rest, ha, hr, he₁, rfl⟩ := straight_append_branch _ _ read history b hb
    obtain ⟨h₂, f, c, hf, hc, he₂, rfl⟩ := straight_append_branch _ _ read h₁ rest hr
    simp only [castFinish_instantiate] at hf
    have hfull : List.ofFn history ++ (a.seq (f.seq c)).history =
        List.ofFn h₁ ++ f.history ++ c.history := by
      simp only [InstrumentBranch.seq, he₁, List.append_assoc]
    have htail : List.ofFn h₂ ++ c.history =
        List.ofFn history ++ (a.seq (f.seq c)).history := by
      rw [he₂, ← hfull]
    intro i hi
    change i ∈ List.range' (start+w.count) w.wires.length ++
      axisPositions ws (start+w.count+w.wires.length) at hi
    rcases List.mem_append.mp hi with hi | hi
    · have hi' := List.mem_range'.mp hi
      let bit : Fin w.wires.length := ⟨i - (start+w.count), by omega⟩
      have hbit : i = start+w.count+bit.val := by dsimp [bit]; omega
      refine ⟨w.wires, start+w.count, bankPrior w.count prior, h₁, f, bit, hf, hbit, ?_, ?_⟩
      · rw [hfull, hbit]
        exact fourierProgram_record_at n .inverse w.wires _ _ read h₁ f hf
          (List.ofFn h₁) c.history (by simp) bit
      · rw [hfull, List.append_assoc]
        have hlen : (List.ofFn h₁).length = start+w.count := by simp
        simpa only [hlen] using (show (List.ofFn h₁ ++ (f.history ++ c.history)).take
          (List.ofFn h₁).length = List.ofFn h₁ from List.take_left).symm
    · have ht := ih _ _ h₂ c hc i hi
      simpa only [htail] using ht

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/Plan ====

section
namespace ShorECDLP.Entrant.Single

/-- Exponents of successive most-significant-first mixed-radix digits. -/
def suffixExponents : List Nat → List Nat
  | [] => []
  | _ :: rest => rest.sum :: suffixExponents rest

theorem exponents_match_widths : suffixExponents widths = exponents := by
  simp [widths, exponents, suffixExponents]

@[irreducible] def leftMetadata : List (Nat × Nat) :=
  (65535, 16) :: List.replicate 7 (30705809, 16) ++ List.replicate 9 (30705809, 15)

@[irreducible] def rightMetadata : List (Nat × Nat) :=
  List.replicate 14 (30705809, 16)

theorem left_widths : leftMetadata.map Prod.snd = widths := by
  simp [leftMetadata, widths]

theorem right_widths : rightMetadata.map Prod.snd = rightWidths := by
  simp [rightMetadata, rightWidths]

theorem left_record_count : recordCount leftMetadata = 491358742 := by
  norm_num [leftMetadata, recordCount, List.replicate]

theorem right_record_count : recordCount rightMetadata = 429881550 := by
  norm_num [rightMetadata, recordCount, List.replicate]

theorem left_positions_length (start : Nat) : (positions leftMetadata start).length = 263 := by
  rw [positions_length, left_widths, widths_sum]

theorem right_positions_length (start : Nat) : (positions rightMetadata start).length = 224 := by
  rw [positions_length, right_widths, rightWidths_sum]

theorem projected_rows : 65536 + 21 * 32768 + 9 * 16384 = 901120 := by norm_num

theorem projected_records : 491358742 + 429881550 + 854 = 921241146 := by norm_num

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/Rows ====

section
namespace ShorECDLP.Entrant.Single

open ShorECDLP.Challenge ShorECDLP.Paper2607_13816.ChallengeMigration

/-- Chronological signed windows after the direct first load. -/
inductive SignedWindow where
  | left16 (index : Fin 7)
  | left15 (index : Fin 9)
  | right16 (index : Fin 14)

def firstRow (a : Fin 65536) : Fin 901120 := ⟨a.val, by omega⟩

/-- Each width-15 window aliases the two physical address halves. -/
def signedRow : SignedWindow → Fin 32768 → Fin 901120
  | .left16 j, a => ⟨65536 + j.val * 32768 + a.val, by omega⟩
  | .left15 j, a => ⟨294912 + j.val * 16384 + a.val % 16384, by
      have h := Nat.mod_lt a.val (by omega : 0 < 16384)
      omega⟩
  | .right16 j, a => ⟨442368 + j.val * 32768 + a.val, by omega⟩

theorem left15_alias (j : Fin 9) (a : Fin 32768) :
    signedRow (.left15 j) a = signedRow (.left15 j) ⟨a.val % 16384, by
      have h := Nat.mod_lt a.val (by omega : 0 < 16384)
      omega⟩ := by
  apply Fin.ext
  simp [signedRow]

/-- The reindexing preserves the behavior under the corresponding table read. -/
theorem signed_reindex_instantiate {s e : Nat} (w : SignedWindow)
    (p : Straight 32768 s e) (read : ConstantBit 901120 → Bool) (history : Fin s → Bool) :
    (reindexStraight (signedRow w) p).instantiate read history =
      p.instantiate (read ∘ reindexBit (signedRow w)) history :=
  reindexStraight_instantiate (signedRow w) p read history

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/Interface ====

section
/-! The mixed-width window contract. Distribution proofs may take `WindowLaw`
as a hypothesis; the concrete implementation supplies this same contract.
The physical arithmetic and its exceptional cases are inherited from the
Apache-2.0 licensed Streaming construction. -/

namespace ShorECDLP.Entrant.Single

open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

@[irreducible] def leftSigned : List SignedWindow :=
  List.ofFn (fun j : Fin 7 => SignedWindow.left16 j) ++
    List.ofFn (fun j : Fin 9 => SignedWindow.left15 j)

@[irreducible] def rightSigned : List SignedWindow :=
  List.ofFn (fun j : Fin 14 => SignedWindow.right16 j)

def SignedWindow.width : SignedWindow → Nat
  | .left16 _ | .right16 _ => 16
  | .left15 _ => 15

def SignedWindow.exponent : SignedWindow → Nat
  | .left16 j => 231 - 16 * j.val
  | .right16 j => 208 - 16 * j.val
  | .left15 j => 120 - 15 * j.val

def SignedWindow.base (Q : Point) : SignedWindow → Point
  | .left16 _ | .left15 _ => G
  | .right16 _ => Q

def bank (width : Nat) : List Wire :=
  if width = 15 then List.range' 855 14 ++ [870] else List.range' 855 16

def digit (width : Nat) (s : BasisState) : Nat := tableAddressValue (bank width) s

def halfOrder : Nat := (order + 1) / 2

def offsetScalar (width exponent : Nat) : Nat :=
  (2^(width-1) + order - halfOrder) * 2^exponent

@[irreducible] def leftOffset : Nat := ((widths.zip exponents).drop 1).foldr
  (fun p acc => offsetScalar p.1 p.2 + acc) 0

@[irreducible] def rightOffset : Nat := (rightWidths.zip rightExponents).foldr
  (fun p acc => offsetScalar p.1 p.2 + acc) 0

@[irreducible] noncomputable def initialPoint (Q : Point) (v : Nat) : Point :=
  (v * 2^247 + leftOffset) • G + rightOffset • Q

noncomputable def increment (Q : Point) (w : SignedWindow) (v : Nat) : Point :=
  ((2 * (v : Int) - (2 : Int)^w.width + 1) : Int) •
    ((halfOrder * 2^w.exponent) • w.base Q)

noncomputable def firstUpdate (Q : Point) (s : BasisState) : BasisState :=
  pointWrite (initialPoint Q (digit 16 s)) s

/-- A graph form avoids choosing a point from arbitrary invalid coordinates. -/
def WindowLaw {n : Nat} (coeffs : Fin n → PointCoeff)
    (physical : Window n) (update : Point → BasisState → BasisState)
    (valid : BasisState → Prop) : Prop :=
  ∀ (Q : Point), order • Q = 0 → Q ≠ 0 → ∀ start history,
    CoherentlyImplementsOn ((physical.program start).instantiate
      (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (update Q)) valid

def WindowValid (w : SignedWindow) (s : BasisState) : Prop :=
  BatchedWindowValid s ∧ (w.width = 15 → s 869 = false)

/-- The signed law names its ideal state map and fixes that map on every valid
point encoding. Its branch coefficients are uniform across input basis states. -/
structure SignedWindowLaw {n : Nat} (coeffs : Fin n → PointCoeff)
    (physical : SignedWindow → Window n) where
  update : Point → SignedWindow → BasisState → BasisState
  correct : ∀ Q w s, order • Q = 0 → Q ≠ 0 → WindowValid w s → ∀ P,
    pointStateCoordinates s = fig14PointEncoding P →
    update Q w s = pointWrite (P + increment Q w (digit w.width s)) s
  coherent : ∀ w, WindowLaw coeffs (physical w) (fun Q => update Q w) (WindowValid w)

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/Coefficients ====

section
/-! Mixed-width public coefficients. The coefficient encoding and torsion
identities reuse the Apache-2.0 licensed Streaming construction. -/

namespace ShorECDLP.Entrant.Single

open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

/-- The first lookup directly loads the accumulator, including infinity. -/
@[irreducible] def initialCoefficients (v : Nat) : PointCoeff :=
  coefficients (v * 2^247 + leftOffset) rightOffset

@[irreducible] def oddScalar (exponent address : Nat) : Nat :=
  (2 * address + 1) * 2^exponent * halfOrder

@[irreducible] def signedCoefficients (w : SignedWindow) (address : Nat) : PointCoeff :=
  match w with
  | .left16 _ | .left15 _ => coefficients (oddScalar w.exponent address) 0
  | .right16 _ => coefficients 0 (oddScalar w.exponent address)

@[irreducible] def mixedCoefficientAt (i : Fin 901120) : PointCoeff :=
  if i.val < 65536 then initialCoefficients i.val
  else if i.val < 294912 then
    coefficients (oddScalar (231 - 16 * ((i.val - 65536) / 32768)) ((i.val - 65536) % 32768)) 0
  else if i.val < 442368 then
    coefficients (oddScalar (120 - 15 * ((i.val - 294912) / 16384)) ((i.val - 294912) % 16384)) 0
  else coefficients 0 (oddScalar (208 - 16 * ((i.val - 442368) / 32768)) ((i.val - 442368) % 32768))

@[irreducible] def mixedCoefficientTable : List PointCoeff := List.ofFn mixedCoefficientAt

theorem mixedCoefficientTable_length : mixedCoefficientTable.length = 901120 := by
  unfold mixedCoefficientTable
  exact List.length_ofFn

theorem mixedCoefficientAt_first (a : Fin 65536) :
    mixedCoefficientAt (firstRow a) = initialCoefficients a.val := by
  simp [mixedCoefficientAt, firstRow, a.isLt]

theorem mixedCoefficientAt_signed (w : SignedWindow) (a : Fin 32768) :
    mixedCoefficientAt (signedRow w a) =
      signedCoefficients w (a.val % 2^(w.width-1)) := by
  cases w with
  | left16 j =>
    have h1 : ¬ (signedRow (.left16 j) a).val < 65536 := by simp [signedRow]; omega
    have h2 : (signedRow (.left16 j) a).val < 294912 := by simp [signedRow]; omega
    have hj : ((signedRow (.left16 j) a).val - 65536) / 32768 = j.val := by simp [signedRow]; omega
    have ha : ((signedRow (.left16 j) a).val - 65536) % 32768 = a.val := by simp [signedRow]; omega
    simp [mixedCoefficientAt, h1, h2, hj, ha, signedCoefficients, SignedWindow.width,
      SignedWindow.exponent, Nat.mod_eq_of_lt a.isLt]
  | left15 j =>
    have hb : a.val % 16384 < 16384 := Nat.mod_lt _ (by decide)
    have h1 : ¬ (signedRow (.left15 j) a).val < 65536 := by simp [signedRow]; omega
    have h2 : ¬ (signedRow (.left15 j) a).val < 294912 := by simp [signedRow]; omega
    have h3 : (signedRow (.left15 j) a).val < 442368 := by simp [signedRow]; omega
    have hj : ((signedRow (.left15 j) a).val - 294912) / 16384 = j.val := by simp [signedRow]; omega
    have ha : ((signedRow (.left15 j) a).val - 294912) % 16384 = a.val % 16384 := by simp [signedRow]; omega
    simp [mixedCoefficientAt, h1, h2, h3, hj, ha, signedCoefficients,
      SignedWindow.width, SignedWindow.exponent]
  | right16 j =>
    have h1 : ¬ (signedRow (.right16 j) a).val < 65536 := by simp [signedRow]; omega
    have h2 : ¬ (signedRow (.right16 j) a).val < 294912 := by simp [signedRow]; omega
    have h3 : ¬ (signedRow (.right16 j) a).val < 442368 := by simp [signedRow]; omega
    have hj : ((signedRow (.right16 j) a).val - 442368) / 32768 = j.val := by simp [signedRow]; omega
    have ha : ((signedRow (.right16 j) a).val - 442368) % 32768 = a.val := by simp [signedRow]; omega
    simp [mixedCoefficientAt, h1, h2, h3, hj, ha, signedCoefficients,
      SignedWindow.width, SignedWindow.exponent, Nat.mod_eq_of_lt a.isLt]


theorem initialCoefficients_point (Q : Point) (hQ : order • Q = 0) (v : Nat) :
    constantPoint Q (initialCoefficients v) = initialPoint Q v :=
by
  unfold initialCoefficients initialPoint
  exact coefficients_point _ _ Q hQ

noncomputable def positivePoint (Q : Point) (w : SignedWindow) (address : Nat) : Point :=
  oddScalar w.exponent (address % 2^(w.width-1)) • w.base Q

theorem signedCoefficients_point (Q : Point) (hQ : order • Q = 0)
    (w : SignedWindow) (address : Nat) :
    constantPoint Q (signedCoefficients w (address % 2^(w.width-1))) =
      positivePoint Q w address := by
  cases w <;> simp [signedCoefficients, coefficients_point _ _ Q hQ,
    positivePoint, SignedWindow.base]

theorem positivePoint_ne_zero (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : SignedWindow) (address : Nat) : positivePoint Q w address ≠ 0 := by
  let P := w.base Q
  have hp : P ≠ 0 := by
    cases w with
    | left16 _ | left15 _ => exact G_ne_zero
    | right16 _ => exact hn
  have hr : order • P = 0 := by
    cases w with
    | left16 _ | left15 _ => exact generator_nsmul_eq_zero
    | right16 _ => exact hQ
  letI : Fact (Nat.Prime order) := ⟨order_prime⟩
  have ho : addOrderOf P = order := addOrderOf_eq_prime hr hp
  have hw : 2^(w.width-1) ≤ 32768 := by cases w <;> norm_num [SignedWindow.width]
  have hm : 0 < 2^(w.width-1) := pow_pos (by decide) _
  have hb := Nat.mod_lt address hm
  have hl : 65535 < order := by norm_num [order]
  have hs : 0 < 2*(address % 2^(w.width-1))+1 ∧
      2*(address % 2^(w.width-1))+1 < order := by omega
  have hh : 0 < halfOrder ∧ halfOrder < order := by dsimp [halfOrder]; omega
  have hodd : ¬ order ∣ 2*(address % 2^(w.width-1))+1 :=
    fun h => (Nat.le_of_dvd hs.1 h).not_gt hs.2
  have hhalf : ¬ order ∣ halfOrder := fun h => (Nat.le_of_dvd hh.1 h).not_gt hh.2
  have htwo : ¬ order ∣ 2 := fun h => (Nat.le_of_dvd (by decide : 0 < 2) h).not_gt (by omega)
  intro hz
  have he : ((2*(address % 2^(w.width-1))+1)*2^w.exponent*halfOrder) • P = 0 := by simpa only [positivePoint, oddScalar] using hz
  have hd := addOrderOf_dvd_iff_nsmul_eq_zero.mpr he
  rw [ho] at hd
  rcases order_prime.dvd_mul.mp hd with hd | hd
  · rcases order_prime.dvd_mul.mp hd with hd | hd
    · exact hodd hd
    · exact htwo (order_prime.dvd_of_dvd_pow hd)
  · exact hhalf hd

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/Padding ====

section
namespace ShorECDLP.Entrant.Single
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

theorem address_append (xs ys : List Wire) (s : BasisState) :
    tableAddressValue (xs ++ ys) s =
      tableAddressValue xs s + 2^xs.length * tableAddressValue ys s := by
  induction xs with
  | nil => simp [tableAddressValue]
  | cons x xs ih =>
    simp only [List.cons_append, tableAddressValue, List.length_cons, ih, pow_succ]
    ring

theorem bank_length (width : Nat) (hw : width = 15 ∨ width = 16) :
    (bank width).length = width := by
  rcases hw with rfl | rfl <;> simp [bank]

theorem window_width (w : SignedWindow) : w.width = 15 ∨ w.width = 16 := by
  cases w <;> simp [SignedWindow.width]

theorem digit15_low (s : BasisState) :
    digit 15 s = logicalValue (tableAddressValue (List.range' 855 14) s) (s 870) := by
  simp [digit, bank, address_append, tableAddressValue, logicalValue]

theorem digit16_physical (s : BasisState) : digit 16 s = windowRawDigit 0 s := by
  simp [digit, bank, windowRawDigit, windowAddressBits, windowBankStart,
    tableAddressValue, List.range', wireValues, boolWordToNat]
  omega

theorem physical_padding (s : BasisState) (hs : s 869 = false) :
    windowRawDigit 0 s = paddedValue (tableAddressValue (List.range' 855 14) s) (s 870) := by
  simp [windowRawDigit, windowAddressBits, windowBankStart, paddedValue,
    tableAddressValue, List.range', wireValues, boolWordToNat, hs]

theorem digit_bound (w : SignedWindow) (s : BasisState) : digit w.width s < 2^w.width := by
  have h := tableAddressValue_lt (bank w.width) s
  rw [bank_length _ (window_width w)] at h
  exact h

theorem digit_low_sign (w : SignedWindow) (s : BasisState) :
    digit w.width s < 2^(w.width-1) ↔ s 870 = false := by
  rcases window_width w with hw | hw
  · rw [hw, digit15_low]
    have hb := tableAddressValue_lt (List.range' 855 14) s
    simp only [List.length_range'] at hb
    cases h : s 870 <;> simp_all [logicalValue]
  · rw [hw, digit16_physical]
    exact reused_window_digit_low s

/-- Both physical address halves select the same logical signed row. -/
theorem selected_address_alias (w : SignedWindow) (s : BasisState)
    (hz : w.width = 15 → s 869 = false) :
    signedTableAddress 32768 (windowRawDigit 0 s) % 2^(w.width-1) =
      signedTableAddress (2^(w.width-1)) (digit w.width s) := by
  rcases window_width w with hw | hw
  · rw [hw, physical_padding s (hz hw), digit15_low]
    exact padded_address _ _ (by simpa using tableAddressValue_lt (List.range' 855 14) s)
  · rw [hw, digit16_physical]
    exact Nat.mod_eq_of_lt (signedTableAddress_bound 32768 _ (windowRawDigit_bound 0 s))

/-- Table signs implement the intended centered odd logical digit. -/
theorem selected_increment (Q : Point) (w : SignedWindow) (s : BasisState)
    (hz : w.width = 15 → s 869 = false) :
    (if s 870 then positivePoint Q w (signedTableAddress 32768 (windowRawDigit 0 s))
      else -positivePoint Q w (signedTableAddress 32768 (windowRawDigit 0 s))) =
      increment Q w (digit w.width s) := by
  have hpow : (2 : Int)^w.width = 2 * (2^(w.width-1) : Nat) := by
    rcases window_width w with hw | hw <;> rw [hw] <;> norm_num
  have hs : (if s 870 then positivePoint Q w (signedTableAddress 32768 (windowRawDigit 0 s))
      else -positivePoint Q w (signedTableAddress 32768 (windowRawDigit 0 s))) =
      signedTableOdd (2^(w.width-1)) (digit w.width s) •
        ((halfOrder * 2^w.exponent) • w.base Q) := by
    simp only [positivePoint, selected_address_alias w s hz, oddScalar, mul_smul]
    rw [smul_comm halfOrder (2^w.exponent)]
    cases h : s 870
    · rw [if_neg (by decide), signedTableOdd, if_pos ((digit_low_sign w s).mpr h)]
      simp only [neg_zsmul, natCast_zsmul]
    · rw [if_pos rfl, signedTableOdd, if_neg (by
        intro hh
        have he := (digit_low_sign w s).mp hh
        simp [h] at he)]
      simp only [natCast_zsmul]
  rw [hs, signedTableOdd_value]
  unfold increment
  rw [hpow]

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/First ====

section
/-! Direct loading with the mixed-width offsets. Adapted from the Apache-2.0
licensed Streaming PointTable; the physical theorem permits infinity. -/

namespace ShorECDLP.Entrant.Single
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

@[irreducible] def firstWindow : Window 901120 :=
  ⟨(bank 16).reverse, 65535, fun start => reindexStraight firstRow (firstLookupProgram start)⟩

theorem initialLookup_circuit (Q : Point) (hQ : order • Q = 0) :
    lookupCircuit (readConstant (fun i : Fin 65536 => initialCoefficients i.val) Q) firstLookupOps =
      physicalPointLookup (initialPoint Q) := by
  rw [firstLookupOps, unaryLookupOps_circuit]
  unfold physicalPointLookup directPointLookup tableLookupProgram tableLookup
  apply unaryAction_leaf_congr
  intro l hl q
  obtain ⟨i, hi, he⟩ := tableAddressTree_label _ 0 1 l hl
  have hlt : l < 65536 := by simpa [he] using hi
  rw [pointLeaf_instantiate]
  simp only [Nat.mod_eq_of_lt hlt, initialCoefficients_point Q hQ, pointTableMask]

theorem firstWindow_run (Q : Point) (hQ : order • Q = 0) (start : Nat)
    (history : Fin start → Bool) :
    ((firstWindow.program start).instantiate (readConstant mixedCoefficientAt Q) history).run =
      (physicalPointLookup (initialPoint Q)).run := by
  unfold firstWindow
  rw [reindexStraight_instantiate,
    readConstant_reindex firstRow _ _ Q mixedCoefficientAt_first]
  rw [firstLookupProgram, castFinish_instantiate, lookupProgram_run, initialLookup_circuit Q hQ]

theorem firstWindow_coherent (Q : Point) (hQ : order • Q = 0) (start : Nat)
    (history : Fin start → Bool) :
    CoherentlyImplementsOn ((firstWindow.program start).instantiate
      (readConstant mixedCoefficientAt Q) history)
      (Finsupp.lmapDomain ℂ ℂ (firstUpdate Q))
      (DirectPointLookupValid (List.range' 519 16) 836) := by
  unfold CoherentlyImplementsOn
  rw [firstWindow_run Q hQ start history]
  exact physicalPointLookup_coherent (initialPoint Q)

theorem firstWindow_t (Q : Point) (hQ : order • Q = 0) (start : Nat)
    (history : Fin start → Bool) :
    ((firstWindow.program start).instantiate (readConstant mixedCoefficientAt Q) history).tCount = 458745 := by
  unfold firstWindow
  rw [reindexStraight_instantiate,
    readConstant_reindex firstRow _ _ Q mixedCoefficientAt_first]
  rw [firstLookupProgram, castFinish_instantiate, lookupProgram_tCount, initialLookup_circuit Q hQ]
  exact (physicalPointLookup_resources _).1

theorem firstUpdate_valid (Q : Point) (s : BasisState) (hs : FirstWindowInput s) :
    BatchedWindowValid (firstUpdate Q s) := firstWindowInput_pointWrite s hs _

theorem firstUpdate_frame (Q : Point) (s : BasisState) (v : Wire)
    (hv : v ∉ pointLogicalWires) : firstUpdate Q s v = s v := pointWrite_frame _ _ v hv

/- The following uniform cost argument is adapted from the Apache-2.0
licensed Streaming UniformT module. -/
private theorem leaf_t_zero {n : Nat} (q : Wire) (ports : List (ConstantBit n × Wire))
    (read : ConstantBit n → Bool) :
    ShorECDLP.tCount ((lookupLeafGates q ports).flatMap (TemplateGate.instantiate read)) = 0 := by
  rw [lookupLeafGates_instantiate]
  induction ports.filter (fun p => read p.1) with
  | nil => rfl
  | cons p ps ih => simpa [ShorECDLP.tCount, tCost] using ih
private theorem unary_t_congr (tree : UnaryActionTree) (f g : Nat → Wire → Circuit)
    (h : ∀ l w, ShorECDLP.tCount (f l w) = ShorECDLP.tCount (g l w))
    (q : Wire) (anc : List Wire) :
    (unaryAction .inc f tree q anc).tCount = (unaryAction .inc g tree q anc).tCount := by
  induction tree generalizing q anc with
  | leaf l => simp [unaryAction,AdaptiveCircuit.tCount,h]
  | node b z o ihz iho => cases anc <;>
      simp only [unaryAction,AdaptiveCircuit.tCount,adaptive_tCount_seq,ihz,iho]
private theorem first_load_uniform (start : Nat)
    (read : ConstantBit 65536 → Bool) (history : Fin start → Bool) :
    ((firstLookupProgram start).instantiate read history).tCount = 458745 := by
  have he : ((firstLookupProgram start).instantiate read history).tCount =
      ((firstLookupProgram start).instantiate (readConstant (fun i : Fin 65536 => firstWindowCoefficients i.val) 0) history).tCount := by
    simp only [firstLookupProgram,castFinish_instantiate,lookupProgram_tCount,firstLookupOps,unaryLookupOps_circuit]
    apply unary_t_congr
    intro l w
    simp only [pointLeaf,leaf_t_zero]
  exact he.trans (firstLookupProgram_tCount start 0 (by simp) history)
theorem firstWindow_t_uniform (Q : Point) (start : Nat) (history : Fin start → Bool) :
    ((firstWindow.program start).instantiate (readConstant mixedCoefficientAt Q) history).tCount = 458745 := by
  unfold firstWindow
  rw [reindexStraight_instantiate]
  exact first_load_uniform start _ history

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/Windows ====

section
namespace ShorECDLP.Entrant.Single
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

@[irreducible] def signedWindow (w : SignedWindow) : Window 901120 :=
  ⟨(bank w.width).reverse, Physical.actual.count,
    fun start => reindexStraight (signedRow w) (Physical.actual.program start)⟩

def windowCoefficients (w : SignedWindow) : Fin 32768 → PointCoeff :=
  fun a => mixedCoefficientAt (signedRow w a)

theorem window_table_point (Q : Point) (hQ : order • Q = 0) (w : SignedWindow) (a : Nat) :
    Physical.tablePoint (windowCoefficients w) Q a = positivePoint Q w a := by
  unfold Physical.tablePoint windowCoefficients
  rw [mixedCoefficientAt_signed, signedCoefficients_point Q hQ]
  have ha : a % 32768 % 2^(w.width-1) = a % 2^(w.width-1) := by
    cases w <;> norm_num [SignedWindow.width]
  simp only [positivePoint, ha]

noncomputable def windowUpdate (Q : Point) (w : SignedWindow) : BasisState → BasisState :=
  Physical.actualBatchedWindowState (windowCoefficients w) Q

theorem windowUpdate_correct (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : SignedWindow) (s : BasisState) (hs : WindowValid w s) (P : Point)
    (hP : pointStateCoordinates s = fig14PointEncoding P) :
    windowUpdate Q w s = pointWrite (P + increment Q w (digit w.width s)) s := by
  unfold windowUpdate
  rw [Physical.actualBatchedWindowState_selected _ Q hQ
    (fun a => (window_table_point Q hQ w a).symm ▸ positivePoint_ne_zero Q hQ hn w a)
    s hs.1.1 P hP, window_table_point Q hQ, selected_increment Q w s hs.2]

private theorem reindex_coherent {n m s e : Nat} (f : Fin n → Fin m)
    (p : Straight n s e) (read : ConstantBit m → Bool) (read' : ConstantBit n → Bool)
    (history : Fin s → Bool) (hread : read ∘ reindexBit f = read')
    (ideal : State →ₗ[ℂ] State) (valid : BasisState → Prop)
    (h : CoherentlyImplementsOn (p.instantiate read' history) ideal valid) :
    CoherentlyImplementsOn ((reindexStraight f p).instantiate read history) ideal valid := by
  rw [reindexStraight_instantiate, hread]
  exact h

private theorem restrict_coherent {a : AdaptiveCircuit} {ideal : State →ₗ[ℂ] State}
    {P R : BasisState → Prop} (h : CoherentlyImplementsOn a ideal P)
    (hr : ∀ s, R s → P s) : CoherentlyImplementsOn a ideal R := by
  obtain ⟨cs, hc, hm⟩ := h
  exact ⟨cs, hc.imp (fun _ _ hb s hs => hb s (hr s hs)), hm⟩

theorem signedWindow_coherent (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : SignedWindow) (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((signedWindow w).program start |>.instantiate
      (readConstant mixedCoefficientAt Q) history)
      (Finsupp.lmapDomain ℂ ℂ (windowUpdate Q w)) (WindowValid w) := by
  have h := Physical.actualBatchedWindow_coherent (windowCoefficients w) Q hQ
    (fun a => (window_table_point Q hQ w a).symm ▸ positivePoint_ne_zero Q hQ hn w a)
    start history
  have ht := reindex_coherent (signedRow w) (Physical.actual.program start)
    (readConstant mixedCoefficientAt Q) (readConstant (windowCoefficients w) Q) history
    (readConstant_reindex (signedRow w) (windowCoefficients w) mixedCoefficientAt Q (fun _ => rfl))
    _ _ h
  unfold signedWindow windowUpdate
  exact restrict_coherent ht (fun _ hs => hs.1)

noncomputable def concreteSignedWindowLaw : SignedWindowLaw mixedCoefficientAt signedWindow where
  update := windowUpdate
  correct := fun Q w s hQ hn hs P hP => windowUpdate_correct Q hQ hn w s hs P hP
  coherent := fun w Q hQ hn start history => signedWindow_coherent Q hQ hn w start history

theorem windowUpdate_frame (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : SignedWindow) (s : BasisState) (hs : WindowValid w s) (v : Wire)
    (hv : v ∉ pointLogicalWires) : windowUpdate Q w s v = s v := by
  obtain ⟨P, hP⟩ := hs.1.2
  rw [windowUpdate_correct Q hQ hn w s hs P hP]
  exact pointWrite_frame _ _ v hv

/-- The unused magnitude wire is restored, for both signs and all transcripts
through the coherent implementation. -/
theorem windowUpdate_padding (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : SignedWindow) (s : BasisState) (hs : WindowValid w s) :
    w.width = 15 → windowUpdate Q w s 869 = false := by
  intro hw
  rw [windowUpdate_frame Q hQ hn w s hs 869 (by decide +kernel)]
  exact hs.2 hw

theorem windowUpdate_valid (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : SignedWindow) (s : BasisState) (hs : WindowValid w s) :
    WindowValid w (windowUpdate Q w s) := by
  obtain ⟨P, hP⟩ := hs.1.2
  rw [windowUpdate_correct Q hQ hn w s hs P hP]
  exact ⟨⟨pointWrite_batchedReady _ s hs.1.1, _, pointWrite_coordinates _ s⟩,
    fun hw => (pointWrite_frame _ s 869 (by decide +kernel)).trans (hs.2 hw)⟩

theorem signedWindow_wires (w : SignedWindow) : (signedWindow w).wires = (bank w.width).reverse := by
  unfold signedWindow
  rfl

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/BodyCounts ====

section
namespace ShorECDLP.Entrant.Single.Physical
open ShorECDLP Classical Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration ShorECDLP.Entrant.ZeroAdaptive
attribute [local irreducible] batchWindowTree
attribute [local irreducible] tailCoordinateProgram yNegateProgram
  tailCoordinateCircuit placedBatchSource windowYNegate ipxProgramOf
  sequenceProgram surroundCompiled relabelCompiled

theorem actual_count : actual.count = 30705809 := by
  unfold actual closedWindow
  rfl

theorem placed_t (coeffs : Fin 32768 → PointCoeff) (start : Nat) (Q : Point)
    (history : Fin start → Bool) :
    compiledTCount (placedProgram start) (readConstant coeffs Q) history =
      (placedBatchSource coeffs Q).tCount := by
  unfold placedProgram compiledTCount
  simp only [ipxProgramOf, lookupProgram_tCount, ipxOps_source, placedBatchSource]

theorem batch_t (coeffs : Fin 32768 → PointCoeff) (Q : Point) :
    (placedBatchSource coeffs Q).tCount = 3024805 := by
  rw [placedBatchSource, ipxSourceOps_tCount _ _ _ _ ipxTree_layout, ipxSchedule_cost, batchWindowTree_nodes]

theorem sources_t (coeffs : Fin 32768 → PointCoeff) (Q : Point) :
    (sequenceCircuit (sources coeffs Q)).tCount = 513221219 := by
  unfold sources
  rw [sequenceCircuit_three_tCount, (tail_numeric_counts _ _).1,
    windowYNegate_numeric_counts.1, batch_t]

theorem core_t (coeffs : Fin 32768 → PointCoeff) (start : Nat) (Q : Point)
    (history : Fin start → Bool) :
    compiledTCount (core start) (readConstant coeffs Q) history =
      (sequenceCircuit (sources coeffs Q)).tCount := by
  unfold core
  apply sequenceProgram_tCount
  unfold segments sources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ .nil))
  · intro cursor h; exact tailCoordinateProgram_tCount coeffs cursor Q h
  · intro cursor h; exact placed_t coeffs cursor Q h
  · intro cursor h; unfold windowYNegate; exact yNegateProgram_tCount cursor _ h

theorem actual_t (coeffs : Fin 32768 → PointCoeff) (start : Nat) (Q : Point)
    (history : Fin start → Bool) :
    ((actual.program start).instantiate (readConstant coeffs Q) history).tCount = 513221219 := by
  have h := surroundCompiled_tCount (signedAddressCircuit 836 854 pointLookupAddress)
    (signedAddressCircuit 836 854 pointLookupAddress) (core 0)
    (sequenceCircuit (sources coeffs Q)) (readConstant coeffs Q) Fin.elim0
    (core_t coeffs 0 Q Fin.elim0)
  simp only [AdaptiveCircuit.tCount, adaptive_tCount_seq, signedAddressCircuit_tCount,
    Nat.zero_add, Nat.add_zero, sources_t] at h
  unfold actual
  simp only [closedWindow_run, castFinish_instantiate, relabelStraight_instantiate, AdaptiveCircuit.relabel_tCount]
  change compiledTCount (prepared 0) (readConstant coeffs Q) Fin.elim0 = _
  unfold prepared
  exact h

end ShorECDLP.Entrant.Single.Physical

end

-- ==== part: Single/WindowCounts ====

section
namespace ShorECDLP.Entrant.Single
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

theorem signedWindow_count (w : SignedWindow) : (signedWindow w).count = 30705809 := by
  unfold signedWindow
  exact Physical.actual_count

theorem signedWindow_t (Q : Point) (w : SignedWindow) (start : Nat)
    (history : Fin start → Bool) :
    (((signedWindow w).program start).instantiate (readConstant mixedCoefficientAt Q) history).tCount = 513221219 := by
  unfold signedWindow
  rw [reindexStraight_instantiate, readConstant_reindex (signedRow w)
    (windowCoefficients w) mixedCoefficientAt Q (fun _ => rfl)]
  exact Physical.actual_t (windowCoefficients w) start Q history

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/Layout ====

section
namespace ShorECDLP.Entrant.Single

open ShorECDLP.Challenge

def params : DecoderParams := ⟨263, 224, by omega, by omega, by omega, by omega⟩

/-- The first right bank follows the complete left-axis transcript. -/
def trialPositions : TrialPositions params where
  left := ⟨(positions leftMetadata 0).toArray, by
    simpa only [List.size_toArray, params] using left_positions_length 0⟩
  right := ⟨(positions rightMetadata 491358742).toArray, by
    simpa only [List.size_toArray, params] using right_positions_length 491358742⟩

def layout : DecodeLayout := ⟨.nearestPair, params, [trialPositions], by simp⟩

theorem left_position_bound (i : Nat) (hi : i ∈ trialPositions.left.toList) :
    i < 491358742 := by
  have h := positions_bounds leftMetadata 0 i
    (show i ∈ positions leftMetadata 0 from by simpa [trialPositions] using hi)
  rw [left_record_count] at h
  omega

theorem right_position_bound (i : Nat) (hi : i ∈ trialPositions.right.toList) :
    491358742 ≤ i ∧ i < 921240292 := by
  have h := positions_bounds rightMetadata 491358742 i
    (show i ∈ positions rightMetadata 491358742 from by simpa [trialPositions] using hi)
  rw [right_record_count] at h
  omega

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/OuterProperties ====

section
namespace ShorECDLP.Entrant.Single
open Quantum ShorECDLP.Challenge ShorECDLP.Paper2607_13816
open ShorECDLP.Paper2607_13816.ChallengeMigration

def bodyT (count : Nat) : Nat := if count = 65535 then 458745 else 513221219

def metadataT : List (Nat × Nat) → Nat → Nat
  | [], _ => 0
  | (count, width) :: ws, prior =>
      bodyT count + fourierSlots width prior + metadataT ws (prior + width)

def metadataSlots (slots : Nat) : List (Nat × Nat) → Nat → Nat
  | [], _ => 0
  | (_, width) :: ws, prior =>
      slots + width + fourierSlots width prior + metadataSlots slots ws (prior + width)

theorem nextPrior_length {start : Nat} (count width : Nat) (prior : List (Fin start)) :
    (nextPrior count width prior).length = prior.length + width := by
  simp [nextPrior, Nat.add_comm]

theorem axis_wellFormed {n : Nat} (ws : List (Window n))
    (hw : ∀ w ∈ ws, ∀ start, (w.program start).WellFormed) (start : Nat)
    (prior : List (Fin start)) : (axis ws start prior).WellFormed := by
  induction ws generalizing start with
  | nil => trivial
  | cons w ws ih =>
    simp only [axis, castFinish_wellFormed]
    apply straight_append_wellFormed _ _ (prepareOuterBank_wellFormed _ _ (hw w (by simp) start))
    apply straight_append_wellFormed
    · simpa only [castFinish_wellFormed] using fourierProgram_wellFormed n .inverse w.wires _ _
    · exact ih (fun v hv => hw v (List.mem_cons_of_mem w hv)) _ _

theorem axis_slots {n : Nat} (ws : List (Window n)) (slots : Nat)
    (hw : ∀ w ∈ ws, ∀ start, (w.program start).gateSlots ≤ slots)
    (start : Nat) (prior : List (Fin start)) :
    (axis ws start prior).gateSlots ≤
      metadataSlots slots (ws.map (fun w => (w.count, w.wires.length))) prior.length := by
  induction ws generalizing start with
  | nil => simp [axis, metadataSlots, Straight.gateSlots]
  | cons w ws ih =>
    simp only [axis, castFinish_gateSlots, Straight.gateSlots_append,
      prepareOuterBank_slots, List.length_reverse, fourierProgram_slots, bankPrior_length]
    have h := ih (fun v hv => hw v (List.mem_cons_of_mem w hv))
      (start+w.count+w.wires.length) (nextPrior w.count w.wires.length prior)
    have hg := hw w (by simp) start
    simp only [nextPrior_length] at h
    simp only [List.map_cons, metadataSlots]
    omega

theorem axis_t {n : Nat} (ws : List (Window n)) (read : ConstantBit n → Bool)
    (hw : ∀ w ∈ ws, ∀ start h,
      ((w.program start).instantiate read h).tCount ≤ bodyT w.count)
    (start : Nat) (prior : List (Fin start)) (history : Fin start → Bool) :
    ((axis ws start prior).instantiate read history).tCount ≤
      metadataT (ws.map (fun w => (w.count, w.wires.length))) prior.length := by
  induction ws generalizing start with
  | nil => simp [axis, metadataT, Straight.instantiate, AdaptiveCircuit.tCount]
  | cons w ws ih =>
    simp only [axis, castFinish_instantiate]
    apply (outer_append_t_le _ _ read history
      (fourierSlots w.wires.length prior.length +
        metadataT (ws.map (fun w => (w.count, w.wires.length))) (prior.length+w.wires.length)) ?_).trans
    · simp only [prepareOuterBank_t, List.map_cons, metadataT]
      have h := hw w (by simp) start history
      omega
    · intro h
      apply (outer_append_t_le _ _ read h
        (metadataT (ws.map (fun w => (w.count, w.wires.length))) (prior.length+w.wires.length)) ?_).trans
      · have hf := fourierProgram_t_le n .inverse w.wires (start+w.count)
          (bankPrior w.count prior) read h
        simp only [bankPrior_length] at hf
        simp only [castFinish_instantiate]
        omega
      · intro h₂
        simpa only [nextPrior_length] using
          ih (fun v hv => hw v (List.mem_cons_of_mem w hv)) _
            (nextPrior w.count w.wires.length prior) h₂

theorem axis_support {n : Nat} (ws : List (Window n)) (support : List Wire)
    (hb : ∀ w ∈ ws, w.wires ⊆ support)
    (hp : ∀ w ∈ ws, ∀ start read history,
      ((w.program start).instantiate read history).wires ⊆ support)
    (start : Nat) (prior : List (Fin start)) (read : ConstantBit n → Bool)
    (history : Fin start → Bool) :
    ((axis ws start prior).instantiate read history).wires ⊆ support := by
  induction ws generalizing start with
  | nil => exact List.nil_subset _
  | cons w ws ih =>
    simp only [axis, castFinish_instantiate]
    apply outer_append_support
    · apply prepareOuterBank_support
      · intro v hv; exact hb w (by simp) (List.mem_reverse.mp hv)
      · exact hp w (by simp) start read history
    · intro h
      apply outer_append_support
      · simp only [castFinish_instantiate]
        exact fourierProgram_support n .inverse w.wires _ _ read h support (hb w (by simp))
      · intro h₂
        exact ih (fun v hv => hb v (List.mem_cons_of_mem w hv))
          (fun v hv => hp v (List.mem_cons_of_mem w hv)) _ _ h₂

/-- Newest-first feedback contains exactly the earlier selected axis outputs. -/
theorem nextPrior_values {start : Nat} (count width : Nat) (prior : List (Fin start)) :
    (nextPrior count width prior).map Fin.val =
      (List.range' (start + count) width).reverse ++ prior.map Fin.val := by
  simp only [nextPrior, List.map_append, List.map_reverse, List.map_ofFn, List.map_map,
    Function.comp_def]
  congr 1
  apply congrArg List.reverse
  apply List.ext_getElem
  · simp
  · intro i hi hj; simp

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/Framing ====

section
namespace ShorECDLP.Entrant.Single
open Quantum ShorECDLP.Challenge ShorECDLP.Paper2607_13816
open ShorECDLP.Paper2607_13816.ChallengeMigration

/-- A fixed query flag surrounds two axes and a reset. -/
@[irreducible] def framed {n s m k e f : Nat} (p : Straight n s m) (q : Straight n m k)
    (r : Straight n k e) (h : e = f) : Straight n s f :=
  .gate (.literal (.X 836)) (castFinish h (p.append (q.append (.gate (.literal (.X 836)) r))))

theorem framed_wellFormed {n s m k e f : Nat} (p : Straight n s m) (q : Straight n m k)
    (r : Straight n k e) (h : e = f) (hp : p.WellFormed) (hq : q.WellFormed) (hr : r.WellFormed) :
    (framed p q r h).WellFormed := by
  unfold framed
  refine ⟨trivial, ?_⟩
  rw [castFinish_wellFormed]
  exact straight_append_wellFormed _ _ hp (straight_append_wellFormed _ _ hq ⟨trivial, hr⟩)

theorem framed_slots {n s m k e f : Nat} (p : Straight n s m) (q : Straight n m k)
    (r : Straight n k e) (h : e = f) :
    (framed p q r h).gateSlots = p.gateSlots + q.gateSlots + r.gateSlots + 2 := by
  unfold framed
  simp only [Straight.gateSlots, castFinish_gateSlots, Straight.gateSlots_append]
  omega

theorem framed_t_le {n s m k e f : Nat} (p : Straight n s m) (q : Straight n m k)
    (r : Straight n k e) (h : e = f) (read : ConstantBit n → Bool) (history : Fin s → Bool)
    (a b : Nat) (hp : (p.instantiate read history).tCount ≤ a)
    (hq : ∀ history, (q.instantiate read history).tCount ≤ b)
    (hr : ∀ history, (r.instantiate read history).tCount = 0) :
    ((framed p q r h).instantiate read history).tCount ≤ a + b := by
  unfold framed
  simp only [Straight.instantiate, TemplateGate.instantiate, AdaptiveCircuit.tCount,
    ShorECDLP.tCount, tCost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.zero_add, castFinish_instantiate]
  apply (outer_append_t_le _ _ read history b ?_).trans (Nat.add_le_add_right hp b)
  intro hq'
  apply (outer_append_t_le _ _ read hq' 0 ?_).trans
  · simpa only [Nat.add_zero] using hq hq'
  · intro hr'
    simp only [Straight.instantiate, TemplateGate.instantiate, AdaptiveCircuit.tCount,
      ShorECDLP.tCount, tCost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.zero_add, hr hr']
    exact Nat.le_refl 0

theorem framed_support {n s m k e f : Nat} (p : Straight n s m) (q : Straight n m k)
    (r : Straight n k e) (h : e = f) (read : ConstantBit n → Bool) (history : Fin s → Bool)
    (support : List Wire) (hx : (836 : Wire) ∈ support)
    (hp : (p.instantiate read history).wires ⊆ support)
    (hq : ∀ history, (q.instantiate read history).wires ⊆ support)
    (hr : ∀ history, (r.instantiate read history).wires ⊆ support) :
    ((framed p q r h).instantiate read history).wires ⊆ support := by
  have x_support {a b : Nat} (p : Straight n a b) (history : Fin a → Bool)
      (hp : (p.instantiate read history).wires ⊆ support) :
      ((Straight.gate (.literal (.X 836)) p).instantiate read history).wires ⊆ support := by
    intro v hv
    change v ∈ circuitWires [.X 836] ++ _ at hv
    rcases List.mem_append.mp hv with hv | hv
    · have he : v = 836 := by simpa [circuitWires, gateWires] using hv
      exact he ▸ hx
    · exact hp hv
  unfold framed
  apply x_support
  rw [castFinish_instantiate]
  apply outer_append_support _ _ read history support hp
  intro hq'
  exact outer_append_support _ _ read hq' support (hq hq') (fun hr' => x_support r hr' (hr hr'))

theorem framed_run {n s m k e f : Nat} (p : Straight n s m) (q : Straight n m k)
    (r : Straight n k e) (h : e = f) (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    ((framed p q r h).instantiate read history).run =
      (AdaptiveCircuit.unitary [.X 836]
        ((p.append (q.append (.gate (.literal (.X 836)) r))).instantiate read history)).run := by
  unfold framed
  simp only [Straight.instantiate, TemplateGate.instantiate, castFinish_instantiate]

theorem framed_branch {n s m k e f : Nat} (p : Straight n s m) (q : Straight n m k)
    (r : Straight n k e) (h : e = f) (read : ConstantBit n → Bool) (history : Fin s → Bool)
    (b : InstrumentBranch) (hb : b ∈ ((framed p q r h).instantiate read history).run) :
    ∃ c ∈ ((p.append (q.append (.gate (.literal (.X 836)) r))).instantiate read history).run,
      b = ⟨c.history, c.kraus.comp (Quantum.run [.X 836])⟩ := by
  simp only [framed, castFinish_instantiate, Straight.instantiate, TemplateGate.instantiate,
    AdaptiveCircuit.run] at hb
  obtain ⟨c, hc, he⟩ := List.mem_map.mp hb
  exact ⟨c, hc, he.symm⟩

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/Program ====

section
namespace ShorECDLP.Entrant.Single
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

attribute [local irreducible] resetProgram

@[irreducible] def leftWindows : List (Window 901120) :=
  firstWindow :: leftSigned.map signedWindow

@[irreducible] def rightWindows : List (Window 901120) := rightSigned.map signedWindow

theorem left_metadata : leftWindows.map (fun w => (w.count, w.wires.length)) = leftMetadata := by
  simp [leftWindows, leftSigned, signedWindow_count, signedWindow_wires,
    SignedWindow.width, bank, firstWindow, leftMetadata]

theorem right_metadata : rightWindows.map (fun w => (w.count, w.wires.length)) = rightMetadata := by
  simp [rightWindows, rightSigned, signedWindow_count, signedWindow_wires,
    SignedWindow.width, bank, rightMetadata]

theorem left_count : axisCount leftWindows = 491358742 := by
  rw [← recordCount_eq_axisCount, left_metadata, left_record_count]

theorem right_count : axisCount rightWindows = 429881550 := by
  rw [← recordCount_eq_axisCount, right_metadata, right_record_count]

theorem left_positions (start : Nat) : axisPositions leftWindows start = positions leftMetadata start := by
  rw [axisPositions, left_metadata]

theorem right_positions (start : Nat) : axisPositions rightWindows start = positions rightMetadata start := by
  rw [axisPositions, right_metadata]

@[irreducible] def resetBody (start : Nat) : Straight 901120 start (start + 854) :=
  castFinish (by rw [resetWires_length]) (resetProgram 901120 start resetWires)

theorem resetBody_run (start : Nat) (read : ConstantBit 901120 → Bool) (history : Fin start → Bool) :
    ((resetBody start).instantiate read history).run =
      (measureResetWithCorrection resetWires (fun _ => [])).run := by
  unfold resetBody
  rw [castFinish_instantiate, resetProgram_run]

theorem resetBody_t (start : Nat) (read : ConstantBit 901120 → Bool) (history : Fin start → Bool) :
    ((resetBody start).instantiate read history).tCount = 0 := by
  unfold resetBody
  rw [castFinish_instantiate, resetProgram_t]

theorem resetBody_slots (start : Nat) : (resetBody start).gateSlots = 0 := by
  unfold resetBody
  rw [castFinish_gateSlots, resetProgram_gateSlots]

theorem resetBody_wellFormed (start : Nat) : (resetBody start).WellFormed := by
  unfold resetBody
  rw [castFinish_wellFormed]
  exact resetProgram_wellFormed _ _ _

theorem resetBody_support (start : Nat) (read : ConstantBit 901120 → Bool) (history : Fin start → Bool) :
    ((resetBody start).instantiate read history).wires ⊆ resetWires := by
  unfold resetBody
  rw [castFinish_instantiate]
  exact resetProgram_support _ _ _ _ read history (List.Subset.refl _)

def trialCount : Nat := axisCount leftWindows + axisCount rightWindows + 854

theorem trialCount_eq : trialCount = 921241146 := by
  rw [trialCount, left_count, right_count]

/-- One trial, with independent same-axis feedback histories and a final reset. -/
@[irreducible] def trial (start : Nat) : Straight 901120 start (start + trialCount) :=
  framed (axis leftWindows start List.nil)
    (axis rightWindows (start + axisCount leftWindows) List.nil)
    (resetBody (start + axisCount leftWindows + axisCount rightWindows))
    (by unfold trialCount; omega)

@[irreducible] def program : Straight 901120 0 921241146 :=
  castFinish (by rw [trialCount_eq]) (trial 0)

theorem left_output_records (start : Nat) (prior : List (Fin start))
    (read : ConstantBit 901120 → Bool) (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((axis leftWindows start prior).instantiate read history).run) :
    ∀ i ∈ positions leftMetadata start, FourierRecord read (List.ofFn history ++ b.history) i := by
  rw [← left_positions]
  exact axis_records leftWindows start prior read history b hb

theorem right_output_records (start : Nat) (prior : List (Fin start))
    (read : ConstantBit 901120 → Bool) (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((axis rightWindows start prior).instantiate read history).run) :
    ∀ i ∈ positions rightMetadata start, FourierRecord read (List.ofFn history ++ b.history) i := by
  rw [← right_positions]
  exact axis_records rightWindows start prior read history b hb

theorem layout_left_positions : trialPositions.left.toList = axisPositions leftWindows 0 := by
  rw [left_positions]
  simp only [trialPositions, Vector.toList, List.toList_toArray]

theorem layout_right_positions : trialPositions.right.toList =
    axisPositions rightWindows (axisCount leftWindows) := by
  rw [right_positions, left_count]
  simp only [trialPositions, Vector.toList, List.toList_toArray]

/-- The protected decoder reads the actual Fourier position vectors in their
stored little-endian order. -/
theorem layout_read_left (history : List Bool) :
    readWord history trialPositions.left.toList = readWord history (axisPositions leftWindows 0) := by
  rw [layout_left_positions]

theorem layout_read_right (history : List Bool) :
    readWord history trialPositions.right.toList =
      readWord history (axisPositions rightWindows (axisCount leftWindows)) := by
  rw [layout_right_positions]

theorem program_history_length (read : ConstantBit 901120 → Bool) (b : InstrumentBranch)
    (hb : b ∈ (program.instantiate read Fin.elim0).run) : b.history.length = 921241146 := by
  exact straight_history_length program read Fin.elim0 b hb

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/BodyPhysical ====

section
namespace ShorECDLP.Entrant.Single.Physical
open ShorECDLP Quantum ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
attribute [local irreducible] batchWindowTree
attribute [local irreducible] tailCoordinateProgram yNegateProgram ipxProgramOf

private theorem old_in_complete : resetWires ⊆ resetWires := List.Subset.refl _

theorem placed_wellFormed (start : Nat) : (placedProgram start).2.WellFormed := by
  unfold placedProgram
  exact ipxProgramOf_wellFormed _ _ _ ipxTree_layout ipxPaths_outside start

theorem core_wellFormed (start : Nat) : (core start).2.WellFormed := by
  unfold core
  apply sequenceProgram_wellFormed
  intro p hp cursor
  simp only [segments, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact tailCoordinateProgram_wellFormed cursor
  · exact placed_wellFormed cursor
  · exact yNegateProgram_wellFormed cursor

theorem prepared_wellFormed (start : Nat) : (prepared start).2.WellFormed := by
  unfold prepared
  exact surroundCompiled_wellFormed _ _ _
    (signedAddressCircuit_wellFormed _ _ _ (by decide) (by decide))
    (signedAddressCircuit_wellFormed _ _ _ (by decide) (by decide)) (core_wellFormed start)

theorem actual_wellFormed (start : Nat) : (actual.program start).WellFormed := by
  unfold actual closedWindow
  apply shiftStraight_wellFormed
  rw [castFinish_wellFormed]
  exact (relabelStraight_wellFormed _ _).mpr (prepared_wellFormed 0)

private theorem closed_relabel_support {n e f : Nat} (h : e = f) (perm : Wire ≃ Wire)
    (p : Straight n 0 e) (start : Nat) :
    straightWires ((closedWindow (castFinish h (relabelStraight perm p))).program start) =
      (straightWires p).map perm := by
  simp only [closedWindow, straightWires_shift, straightWires_castFinish, straightWires_relabel]

theorem placed_slots (start : Nat) : (placedProgram start).2.gateSlots ≤ 1183842436 := by
  unfold placedProgram
  simp only [ipxProgramOf, lookupProgram_slots]
  have h := ipxOps_slots_le tableRows batchWindowTree pointLookupPath ipxSchedule
  rw [ipxSlotBound_schedule, batchWindowTree_nodes] at h
  omega

theorem core_slots (start : Nat) : (core start).2.gateSlots ≤ 2683868808 := by
  have h := sequenceProgram_slots_le 32768 segments
    ([1500000000, 1183842436, 26372] : List Nat) (by
      unfold segments
      refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ .nil))
      · intro s; exact tailCoordinateProgram_slots s
      · intro s; exact placed_slots s
      · intro s; exact yNegateProgram_slots_le s) start
  unfold core
  simpa only [List.sum_cons, List.sum_nil] using h

theorem prepared_slots (start : Nat) : (prepared start).2.gateSlots ≤ 3000000000 := by
  have h := core_slots start
  unfold prepared
  simp only [surroundCompiled_slots, signedAddressCircuit_length,
    pointLookupAddress, List.length_range']
  omega

theorem actual_slots (start : Nat) : (actual.program start).gateSlots ≤ 3000000000 := by
  unfold actual closedWindow
  simp only [shiftStraight_gateSlots, castFinish_gateSlots, relabelStraight_slots]
  exact prepared_slots 0

theorem coordinate_support (start : Nat) :
    (straightWires (tailCoordinateProgram start).2).map (windowAddressPerm 855 (by decide)) ⊆
      resetWires := by
  intro z hz
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hz
  exact windowBaseSupport_relocated v
    (tailCoordinateProgram_support_static start hv)

theorem negate_support (start : Nat) :
    (straightWires (yNegateProgram start).2).map (windowAddressPerm 855 (by decide)) ⊆
      resetWires := by
  have h := (sharedYNegateProgram_support_static (.right ⟨0, by decide⟩) start).trans old_in_complete
  simpa only [sharedYNegateProgram, reindexCompiled_support] using h

theorem placed_support (start : Nat) :
    (straightWires (placedProgram start).2).map (windowAddressPerm 855 (by decide)) ⊆
      resetWires := by
  have hraw : straightWires (ipxProgramOf tableRows batchWindowTree pointLookupPath start).2 ⊆ ipxRawSupport := by
    apply ipxProgramOf_support
    · intro c
      have hc := ipxControl_lt c
      apply ipxRawSupport_mem _ <;> (try dsimp only [Wire] at *) <;> omega
    · intro z hz
      simp only [pointLookupPath,List.mem_range'_1] at hz
      apply ipxRawSupport_mem _ <;> (try dsimp only [Wire] at *) <;> omega
    · intro z hz
      unfold batchWindowTree at hz
      have h := (tableAddressTree_mem_index pointLookupAddress 0 1 z).mp hz
      simp only [pointLookupAddress,List.mem_range'_1] at h
      apply ipxRawSupport_mem _ <;> (try dsimp only [Wire] at *) <;> omega
  unfold placedProgram
  intro z hz
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hz
  exact old_in_complete (ipxRawSupport_placed v (hraw hv))

theorem core_support (cursor : Nat) : (straightWires (core cursor).2).map
    (windowAddressPerm 855 (by decide)) ⊆ resetWires := by
  unfold core
  apply sequenceProgram_mapped_support
  simp only [segments, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
  exact ⟨coordinate_support, placed_support, negate_support⟩

theorem prepared_support (start : Nat) : (straightWires (prepared start).2).map
    (windowAddressPerm 855 (by decide)) ⊆ resetWires := by
  unfold prepared
  simp only [surroundCompiled_support, List.map_append, List.append_subset]
  exact ⟨⟨signedAddressCircuit_support_static.trans old_in_complete, core_support start⟩,
    signedAddressCircuit_support_static.trans old_in_complete⟩

theorem actual_support (start : Nat) :
    straightWires (actual.program start) ⊆ resetWires := by
  unfold actual
  rw [closed_relabel_support]
  exact prepared_support 0

end ShorECDLP.Entrant.Single.Physical

end

-- ==== part: Single/WindowProperties ====

section
namespace ShorECDLP.Entrant.Single
open Quantum ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

attribute [local irreducible] firstLookupProgram

private theorem reset_in_complete : resetWires ⊆ resetWires := List.Subset.refl _

theorem firstWindow_wellFormed (start : Nat) : (firstWindow.program start).WellFormed := by
  unfold firstWindow
  exact (reindexStraight_wellFormed firstRow (firstLookupProgram start)).mpr (firstLookupProgram_wellFormed start)

theorem firstWindow_slots (start : Nat) : (firstWindow.program start).gateSlots ≤ 3000000000 := by
  have h := actualFirstWindow_slots start
  simp only [actualFirstWindow, reindexStraight_gateSlots] at h
  unfold firstWindow
  rw [reindexStraight_gateSlots]
  exact h.trans (by norm_num)

theorem firstWindow_support (start : Nat) :
    straightWires (firstWindow.program start) ⊆ resetWires := by
  have h := (actualFirstWindow_support_static start).trans reset_in_complete
  simp only [actualFirstWindow, straightWires_reindex] at h
  unfold firstWindow
  rw [straightWires_reindex]
  exact h

theorem signedWindow_wellFormed (w : SignedWindow) (start : Nat) :
    ((signedWindow w).program start).WellFormed := by
  unfold signedWindow
  exact (reindexStraight_wellFormed (signedRow w) (Physical.actual.program start)).mpr (Physical.actual_wellFormed start)

theorem signedWindow_slots (w : SignedWindow) (start : Nat) :
    ((signedWindow w).program start).gateSlots ≤ 3000000000 := by
  unfold signedWindow
  rw [reindexStraight_gateSlots]
  exact Physical.actual_slots start

theorem signedWindow_support (w : SignedWindow) (start : Nat) :
    straightWires ((signedWindow w).program start) ⊆ resetWires := by
  unfold signedWindow
  rw [straightWires_reindex]
  exact Physical.actual_support start

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/Validity ====

section
namespace ShorECDLP.Entrant.Single
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

theorem windowBank_subset (w : SignedWindow) : bank w.width ⊆ streamAddress := by
  intro v hv
  rcases window_width w with hw | hw
  · rw [hw] at hv
    simp only [bank, if_true, List.mem_append, List.mem_range'_1, List.mem_singleton] at hv
    simp only [streamAddress, List.mem_range'_1]
    dsimp only [Wire] at *
    omega
  · rw [hw] at hv
    simpa only [bank, show (16 : Nat) ≠ 15 by decide, if_false, streamAddress] using hv

theorem bank_padding_excluded (w : SignedWindow) (hw : w.width = 15) : 869 ∉ bank w.width := by
  rw [hw]
  simp [bank, List.mem_range'_1]

theorem bank_outside_point (w : SignedWindow) (v : Wire) (hv : v ∈ bank w.width) :
    v ∉ pointLogicalWires := by
  have hb := windowBank_subset w hv
  simp only [streamAddress, List.mem_range'_1] at hb
  simp only [pointLogicalWires, pointCorrectionX, pointCorrectionYInf, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1]
  dsimp only [Wire] at *
  omega

theorem windowValid_update (w : SignedWindow) (s : BasisState) (hs : WindowValid w s)
    (v : Wire) (hv : v ∈ bank w.width) (b : Bool) : WindowValid w (s[v ↦ b]) := by
  refine ⟨batchedWindowValid_address_update s hs.1 v (windowBank_subset w hv) b, ?_⟩
  intro hw
  have hne : (869 : Wire) ≠ v := by intro he; subst v; exact bank_padding_excluded w hw hv
  simpa only [upd, if_neg hne] using hs.2 hw

private theorem supported_smul {V : BasisState → Prop} {ψ : State} (c : ℂ)
    (hψ : SupportedOn V ψ) : SupportedOn V (c • ψ) := by
  intro s hs
  apply hψ s
  intro h
  exact hs (by simp [h])

private theorem supported_add {V : BasisState → Prop} {ψ φ : State}
    (hψ : SupportedOn V ψ) (hφ : SupportedOn V φ) : SupportedOn V (ψ + φ) := by
  intro s hs
  by_cases h : ψ s = 0
  · exact hφ s (by simpa [h] using hs)
  · exact hψ s h

theorem supported_transform (V W : BasisState → Prop) (L : State →ₗ[ℂ] State)
    (hL : ∀ s, V s → SupportedOn W (L (ket s))) (ψ : State)
    (hψ : SupportedOn V ψ) : SupportedOn W (L ψ) := by
  classical
  induction ψ using Finsupp.induction with
  | zero => simp
  | single_add s c ψ hs hc ih =>
    have hz : ψ s = 0 := by simpa using hs
    have hvs : V s := hψ s (by simp [hz, hc])
    have hvψ : SupportedOn V ψ := by
      intro u hu
      apply hψ u
      by_cases he : u = s
      · subst u; exact (hu hz).elim
      · simpa [he] using hu
    have he : Finsupp.single s c = c • ket s := by ext u; simp [ket]
    rw [map_add, he, map_smul]
    exact supported_add (supported_smul c (hL s hvs)) (ih hvψ)

theorem supported_linear (V : BasisState → Prop) (L : State →ₗ[ℂ] State)
    (hL : ∀ s, V s → SupportedOn V (L (ket s))) (ψ : State)
    (hψ : SupportedOn V ψ) : SupportedOn V (L ψ) :=
  supported_transform V V L hL ψ hψ

theorem windowValid_prepare (w : SignedWindow) (ws : List Wire)
    (hws : ws ⊆ bank w.width) (ψ : State) (hψ : SupportedOn (WindowValid w) ψ) :
    SupportedOn (WindowValid w) (Quantum.run (ws.map Gate.H) ψ) := by
  induction ws generalizing ψ with
  | nil => exact hψ
  | cons v vs ih =>
    apply ih (fun z hz => hws (List.mem_cons_of_mem v hz))
    apply supported_linear (WindowValid w) (applyGate (.H v)) ?_ ψ hψ
    intro s hs
    rw [applyGate_ket]
    exact supported_add
      (supported_smul _ (supportedOn_ket _ _ (windowValid_update w s hs v (hws (by simp)) false)))
      (supported_smul _ (supportedOn_ket _ _ (windowValid_update w s hs v (hws (by simp)) true)))

theorem windowValid_clear (w : SignedWindow) (ws : List Wire)
    (hws : ws ⊆ bank w.width) (s : BasisState) (hs : WindowValid w s) :
    WindowValid w (fourierClear ws s) := by
  induction ws generalizing s with
  | nil => exact hs
  | cons v vs ih =>
    exact ih (fun z hz => hws (List.mem_cons_of_mem v hz)) _
      (windowValid_update w s hs v (hws (by simp)) false)

theorem windowValid_fourier (w : SignedWindow) (dir : PhaseDir) (ws : List Wire)
    (hws : ws ⊆ bank w.width) (prior bs : List Bool) (ψ : State)
    (hψ : SupportedOn (WindowValid w) ψ) :
    SupportedOn (WindowValid w) (fourierBranch dir ws prior bs ψ) := by
  apply supported_linear _ _ ?_ ψ hψ
  intro s hs
  rw [fourierBranch_ket]
  exact supported_smul _ (supportedOn_ket _ _ (windowValid_clear w ws hws s hs))

/-- Clearing the Fourier bank commutes with writing the point accumulator. -/
theorem clear_pointWrite (w : SignedWindow) (P : Point) (s : BasisState) :
    fourierClear (bank w.width) (pointWrite P s) =
      pointWrite P (fourierClear (bank w.width) s) := by
  funext v
  rw [fourierClear_apply]
  by_cases hv : v ∈ bank w.width
  · simp only [hv, if_true, pointWrite_frame P _ v (bank_outside_point w v hv), fourierClear_apply]
  · rw [if_neg hv]
    unfold pointWrite
    split_ifs <;> simp [fourierClear_apply, hv]

theorem windowUpdate_cleared (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : SignedWindow) (s : BasisState) (hs : WindowValid w s) (P : Point)
    (hP : pointStateCoordinates s = fig14PointEncoding P) :
    fourierClear (bank w.width) (windowUpdate Q w s) =
      pointWrite (P + increment Q w (digit w.width s)) (fourierClear (bank w.width) s) := by
  rw [windowUpdate_correct Q hQ hn w s hs P hP, clear_pointWrite]

def TrialReady (s : BasisState) : Prop := BatchedWindowValid s ∧ Clean streamAddress s

def Prepared (w : SignedWindow) (s : BasisState) : Prop :=
  BatchedWindowValid s ∧ ∀ v ∈ streamAddress, v ∉ bank w.width → s v = false

theorem prepared_valid (w : SignedWindow) (s : BasisState) (hs : Prepared w s) : WindowValid w s := by
  refine ⟨hs.1, ?_⟩
  intro hw
  exact hs.2 869 (by simp [streamAddress]) (bank_padding_excluded w hw)

theorem ready_prepared (w : SignedWindow) (s : BasisState) (hs : TrialReady s) : Prepared w s :=
  ⟨hs.1, fun v hv _ => hs.2 v hv⟩

theorem prepared_update (w : SignedWindow) (s : BasisState) (hs : Prepared w s)
    (v : Wire) (hv : v ∈ bank w.width) (b : Bool) : Prepared w (s[v ↦ b]) := by
  refine ⟨batchedWindowValid_address_update s hs.1 v (windowBank_subset w hv) b, ?_⟩
  intro z hz hn
  have hne : z ≠ v := by intro h; subst z; exact hn hv
  simpa only [upd, if_neg hne] using hs.2 z hz hn

theorem prepared_prepare (w : SignedWindow) (ws : List Wire) (hws : ws ⊆ bank w.width)
    (ψ : State) (hψ : SupportedOn (Prepared w) ψ) :
    SupportedOn (Prepared w) (Quantum.run (ws.map Gate.H) ψ) := by
  induction ws generalizing ψ with
  | nil => exact hψ
  | cons v vs ih =>
    apply ih (fun z hz => hws (List.mem_cons_of_mem v hz))
    apply supported_linear (Prepared w) (applyGate (.H v)) ?_ ψ hψ
    intro s hs
    rw [applyGate_ket]
    exact supported_add
      (supported_smul _ (supportedOn_ket _ _ (prepared_update w s hs v (hws (by simp)) false)))
      (supported_smul _ (supportedOn_ket _ _ (prepared_update w s hs v (hws (by simp)) true)))

theorem stream_outside_point (v : Wire) (hv : v ∈ streamAddress) : v ∉ pointLogicalWires := by
  simp only [streamAddress, List.mem_range'_1] at hv
  simp only [pointLogicalWires, pointCorrectionX, pointCorrectionYInf, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1]
  dsimp only [Wire] at *
  omega

theorem prepared_windowUpdate (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : SignedWindow) (s : BasisState) (hs : Prepared w s) : Prepared w (windowUpdate Q w s) := by
  refine ⟨(windowUpdate_valid Q hQ hn w s (prepared_valid w s hs)).1, ?_⟩
  intro v hv ha
  rw [windowUpdate_frame Q hQ hn w s (prepared_valid w s hs) v (stream_outside_point v hv)]
  exact hs.2 v hv ha

theorem prepared_clear_ready (w : SignedWindow) (s : BasisState) (hs : Prepared w s) :
    TrialReady (fourierClear (bank w.width).reverse s) := by
  refine ⟨batchedWindowValid_fourierClear _ (fun _ h => windowBank_subset w (List.mem_reverse.mp h)) s hs.1, ?_⟩
  intro v hv
  rw [fourierClear_apply]
  split_ifs with h
  · rfl
  · exact hs.2 v hv (fun hmem => h (List.mem_reverse.mpr hmem))

theorem ready_prepare (w : SignedWindow) (ψ : State) (hψ : SupportedOn TrialReady ψ) :
    SupportedOn (Prepared w) (Quantum.run ((bank w.width).map Gate.H) ψ) :=
  prepared_prepare w _ (List.Subset.refl _) ψ (fun s hs => ready_prepared w s (hψ s hs))

theorem signed_branch_prepared (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : SignedWindow) (start : Nat) (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ (((signedWindow w).program start).instantiate (readConstant mixedCoefficientAt Q) history).run)
    (ψ : State) (hψ : SupportedOn (Prepared w) ψ) : SupportedOn (Prepared w) (b.kraus ψ) := by
  obtain ⟨c, hc⟩ := (signedWindow_coherent Q hQ hn w start history).branch_coefficient b hb
  rw [hc.on_supported (fun s hs => prepared_valid w s (hψ s hs))]
  apply supported_smul
  apply supported_linear (Prepared w) _ ?_ ψ hψ
  intro s hs
  simpa only [ket, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single] using
    supportedOn_ket (Prepared w) _ (prepared_windowUpdate Q hQ hn w s hs)

theorem prepared_fourier_ready (w : SignedWindow) (prior bs : List Bool)
    (ψ : State) (hψ : SupportedOn (Prepared w) ψ) :
    SupportedOn TrialReady (fourierBranch .inverse (bank w.width).reverse prior bs ψ) := by
  apply supported_transform (Prepared w) TrialReady _ ?_ ψ hψ
  intro s hs
  rw [fourierBranch_ket]
  exact supported_smul _ (supportedOn_ket _ _ (prepared_clear_ready w s hs))

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/ResourceArithmetic ====

section
namespace ShorECDLP.Entrant.Single
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

theorem windows_cases (w : Window 901120) (hw : w ∈ leftWindows ++ rightWindows) :
    w = firstWindow ∨ ∃ s, w = signedWindow s := by
  simp only [leftWindows, rightWindows, List.mem_append, List.mem_cons, List.mem_map] at hw
  rcases hw with (h | ⟨s, _, h⟩) | ⟨s, _, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨s, h.symm⟩
  · exact Or.inr ⟨s, h.symm⟩

theorem windows_wellFormed (w : Window 901120) (hw : w ∈ leftWindows ++ rightWindows) (start : Nat) :
    (w.program start).WellFormed := by
  rcases windows_cases w hw with rfl | ⟨s, rfl⟩
  · exact firstWindow_wellFormed start
  · exact signedWindow_wellFormed s start

theorem windows_slots (w : Window 901120) (hw : w ∈ leftWindows ++ rightWindows) (start : Nat) :
    (w.program start).gateSlots ≤ 3000000000 := by
  rcases windows_cases w hw with rfl | ⟨s, rfl⟩
  · exact firstWindow_slots start
  · exact signedWindow_slots s start

theorem windows_t (Q : Point) (w : Window 901120)
    (hw : w ∈ leftWindows ++ rightWindows) (start : Nat) (history : Fin start → Bool) :
    ((w.program start).instantiate (readConstant mixedCoefficientAt Q) history).tCount ≤ bodyT w.count := by
  rcases windows_cases w hw with rfl | ⟨s, rfl⟩
  · rw [firstWindow_t_uniform Q start history]
    simp [firstWindow, bodyT]
  · rw [signedWindow_t Q s start history, signedWindow_count]
    simp [bodyT]

theorem left_t_budget : metadataT leftMetadata 0 = 8212032702 := by
  norm_num [leftMetadata, metadataT, bodyT, List.replicate, fourierSlots]

theorem right_t_budget : metadataT rightMetadata 0 = 7185122042 := by
  norm_num [rightMetadata, metadataT, bodyT, List.replicate, fourierSlots]

theorem slots_budget : metadataSlots 3000000000 leftMetadata 0 +
    metadataSlots 3000000000 rightMetadata 0 + 2 = 93000059918 := by
  norm_num [leftMetadata, rightMetadata, metadataSlots, List.replicate, fourierSlots]

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/TrialValidity ====

section
namespace ShorECDLP.Entrant.Single
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

theorem trial_wellFormed (start : Nat) : (trial start).WellFormed := by
  unfold trial
  apply framed_wellFormed
  · exact axis_wellFormed leftWindows (fun w hw => windows_wellFormed w (List.mem_append_left _ hw)) _ _
  · exact axis_wellFormed rightWindows (fun w hw => windows_wellFormed w (List.mem_append_right _ hw)) _ _
  · exact resetBody_wellFormed _

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/ProgramShape ====

section
namespace ShorECDLP.Entrant.Single
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

theorem trial_slots (start : Nat) : (trial start).gateSlots ≤ 93000059918 := by
  have hl := axis_slots leftWindows 3000000000
    (fun w hw => windows_slots w (List.mem_append_left _ hw)) start List.nil
  have hr := axis_slots rightWindows 3000000000
    (fun w hw => windows_slots w (List.mem_append_right _ hw)) (start + axisCount leftWindows) List.nil
  rw [left_metadata] at hl
  rw [right_metadata] at hr
  simp only [List.length_nil] at hl hr
  unfold trial
  rw [framed_slots, resetBody_slots]
  have h := slots_budget
  omega

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/Resources ====

section
namespace ShorECDLP.Entrant.Single
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

theorem left_axis_t (Q : Point) (start : Nat) (history : Fin start → Bool) :
    ((axis leftWindows start List.nil).instantiate (readConstant mixedCoefficientAt Q) history).tCount ≤ 8212032702 := by
  have h := axis_t leftWindows (readConstant mixedCoefficientAt Q)
    (fun w hw => windows_t Q w (List.mem_append_left _ hw)) start List.nil history
  rwa [left_metadata, List.length_nil, left_t_budget] at h

theorem right_axis_t (Q : Point) (start : Nat) (history : Fin start → Bool) :
    ((axis rightWindows start List.nil).instantiate (readConstant mixedCoefficientAt Q) history).tCount ≤ 7185122042 := by
  have h := axis_t rightWindows (readConstant mixedCoefficientAt Q)
    (fun w hw => windows_t Q w (List.mem_append_right _ hw)) start List.nil history
  rwa [right_metadata, List.length_nil, right_t_budget] at h

theorem trial_t (Q : Point) (start : Nat) (history : Fin start → Bool) :
    ((trial start).instantiate (readConstant mixedCoefficientAt Q) history).tCount ≤ 15397154744 := by
  unfold trial
  exact framed_t_le _ _ _ _ _ history 8212032702 7185122042
    (left_axis_t Q start history) (fun h => right_axis_t Q _ h) (fun h => resetBody_t _ _ h)

theorem program_wellFormed : program.WellFormed := by
  unfold program
  rw [castFinish_wellFormed]
  exact trial_wellFormed 0

theorem program_slots : program.gateSlots ≤ 93000059918 := by
  unfold program
  rw [castFinish_gateSlots]
  exact trial_slots 0

theorem program_t (Q : Point) :
    (program.instantiate (readConstant mixedCoefficientAt Q) Fin.elim0).tCount ≤ 15397154744 := by
  unfold program
  rw [castFinish_instantiate]
  exact trial_t Q 0 Fin.elim0

theorem program_measurements (read : ConstantBit 901120 → Bool) :
    (program.instantiate read Fin.elim0).measurementCount = 921241146 := by
  exact program.measurementCount read Fin.elim0

theorem stream_support : streamAddress ⊆ resetWires := by
  intro v hv
  exact List.mem_append_right _ hv

theorem windows_bank_support (w : Window 901120) (hw : w ∈ leftWindows ++ rightWindows) :
    w.wires ⊆ resetWires := by
  rcases windows_cases w hw with rfl | ⟨s, rfl⟩
  · unfold firstWindow
    intro v hv
    apply stream_support
    simpa only [List.mem_reverse, bank, show (16 : Nat) ≠ 15 by decide, if_false, streamAddress] using hv
  · rw [signedWindow_wires]
    intro v hv
    exact stream_support (windowBank_subset s (List.mem_reverse.mp hv))

theorem windows_support (w : Window 901120) (hw : w ∈ leftWindows ++ rightWindows)
    (start : Nat) (read : ConstantBit 901120 → Bool) (history : Fin start → Bool) :
    ((w.program start).instantiate read history).wires ⊆ resetWires := by
  apply (straight_instantiate_support _ read history).trans
  rcases windows_cases w hw with rfl | ⟨s, rfl⟩
  · exact firstWindow_support start
  · exact signedWindow_support s start

private theorem flag_support : (836 : Wire) ∈ resetWires := by
  simp [resetWires]

theorem left_axis_support (start : Nat) (read : ConstantBit 901120 → Bool) (history : Fin start → Bool) :
    ((axis leftWindows start List.nil).instantiate read history).wires ⊆ resetWires :=
  axis_support leftWindows resetWires
    (fun w hw => windows_bank_support w (List.mem_append_left _ hw))
    (fun w hw => windows_support w (List.mem_append_left _ hw)) start List.nil read history

theorem right_axis_support (start : Nat) (read : ConstantBit 901120 → Bool) (history : Fin start → Bool) :
    ((axis rightWindows start List.nil).instantiate read history).wires ⊆ resetWires :=
  axis_support rightWindows resetWires
    (fun w hw => windows_bank_support w (List.mem_append_right _ hw))
    (fun w hw => windows_support w (List.mem_append_right _ hw)) start List.nil read history

theorem trial_support (start : Nat) (read : ConstantBit 901120 → Bool) (history : Fin start → Bool) :
    ((trial start).instantiate read history).wires ⊆ resetWires := by
  unfold trial
  exact framed_support _ _ _ _ read history resetWires flag_support
    (left_axis_support start read history) (fun h => right_axis_support _ read h)
    (fun h => resetBody_support _ read h)

theorem program_support (read : ConstantBit 901120 → Bool) :
    (program.instantiate read Fin.elim0).wires ⊆ resetWires := by
  unfold program
  rw [castFinish_instantiate]
  exact trial_support 0 read Fin.elim0

theorem program_qubits (read : ConstantBit 901120 → Bool) :
    (program.instantiate read Fin.elim0).qubitCount ≤ 854 := by
  have hs : (program.instantiate read Fin.elim0).wires.dedup.toFinset ⊆
      resetWires.toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (program_support read (by simpa using hw))
  have hc := (Finset.card_le_card hs).trans (List.toFinset_card_le _)
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
  simpa only [AdaptiveCircuit.qubitCount, resetWires_length] using hc

theorem program_resource_facts (Q : Point) :
    (resources (program.instantiate (readConstant mixedCoefficientAt Q) Fin.elim0)).qubits ≤ 854 ∧
    (resources (program.instantiate (readConstant mixedCoefficientAt Q) Fin.elim0)).tModel ≤ 15397154744 ∧
    (resources (program.instantiate (readConstant mixedCoefficientAt Q) Fin.elim0)).measurements = 921241146 :=
  ⟨program_qubits _, program_t Q, program_measurements _⟩

theorem table_rows_limit : mixedCoefficientTable.length ≤ 983040 := by
  rw [mixedCoefficientTable_length]
  norm_num

theorem one_candidate_check : layout.trials.length * decoderCandidateLimit layout.kind layout.params = 1 := by
  simp [layout, decoderCandidateLimit]

theorem resource_product : 854 * 15397154744 = 13149170151376 := by norm_num

end ShorECDLP.Entrant.Single

end
