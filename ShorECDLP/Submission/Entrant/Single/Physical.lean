import ShorECDLP.Submission.«2607_13816».Window.TableLookup
import ShorECDLP.Submission.«2607_13816».Challenge.SignedWindow
import ShorECDLP.Submission.«2607_13816».EEA.MeasuredAnd
import ShorECDLP.Challenge.StraightLine
import ShorECDLP.Framework.Quantum.AdaptiveFrame
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import ShorECDLP.Challenge.Contract
import ShorECDLP.Submission.«2607_13816».Challenge.Records
import ShorECDLP.Submission.«2607_13816».EEA.BlockAPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».Challenge.Coordinate
import ShorECDLP.Submission.«2607_13816».Challenge.CursorShift
import ShorECDLP.Submission.«2607_13816».EEA.MeasuredWrapperCounts
import ShorECDLP.Framework.Quantum.AdaptiveDisjoint
import ShorECDLP.Submission.«2607_13816».Challenge.Support
import ShorECDLP.Challenge.Official
import ShorECDLP.Submission.«2607_13816».EEA.LengthPrimitiveCounts
import ShorECDLP.Framework.Quantum.InnerProduct
import ShorECDLP.Submission.«2607_13816».EEA.Preprocess
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
attribute [local irreducible] ShorECDLP.Entrant.MeasuredQuotient.Reverse.divisionProgram
  ShorECDLP.Entrant.MeasuredQuotient.Reverse.multiplicationProgram equalityProgram

private theorem field_count_generic (n start : Nat) (guard arithmetic : FixedSegment n)
     (exchange : Wire ≃ Wire) (flip cx : Circuit) :
     (surroundCompiled flip flip (sequenceProgram n
       (List.cons (fun s => relabelCompiled exchange (appendCompiled (guard s) ⟨0,literalProgram cx⟩))
         (List.cons arithmetic (List.cons (fun s => relabelCompiled exchange (prependCompiled cx (guard s))) List.nil))) start)).1 =
     (let a := guard start
      let b := arithmetic (start+a.1)
      appendCompiled a (prependCompiled cx (appendCompiled b
        (prependCompiled cx (guard (start+a.1+b.1)))))).1 := by
   simp only [sequenceProgram, surroundCompiled, appendCompiled, prependCompiled,
     relabelCompiled, Nat.add_zero]

private theorem fieldProgram_count_eq (n start : Nat) (arithmetic : FixedSegment n) :
    (fieldProgram n start arithmetic).1 =
      (let a := equalityProgram n start ZeroAdaptive.reg 0 837 ZeroAdaptive.scratch
       let b := arithmetic (start+a.1)
       appendCompiled a (prependCompiled ZeroAdaptive.cx (appendCompiled b
         (prependCompiled ZeroAdaptive.cx
           (equalityProgram n (start+a.1+b.1) ZeroAdaptive.reg 0 837 ZeroAdaptive.scratch))))).1 :=
   field_count_generic n start (fun s => equalityProgram n s ZeroAdaptive.reg 0 837 ZeroAdaptive.scratch)
      arithmetic exchange flip ZeroAdaptive.cx
theorem divisionProgram_count_eq (n start : Nat) :
    (divisionProgram n start).1 = (ZeroAdaptive.zDivisionProgram n start).1 :=
  fieldProgram_count_eq n start (ShorECDLP.Entrant.MeasuredQuotient.Reverse.divisionProgram n)

theorem multiplicationProgram_count_eq (n start : Nat) :
    (multiplicationProgram n start).1 = (ZeroAdaptive.zMultiplicationProgram n start).1 :=
  fieldProgram_count_eq n start (ShorECDLP.Entrant.MeasuredQuotient.Reverse.multiplicationProgram n)

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
    (coordinateSource x y).tCount = 498372875 ∧
    (coordinateSource x y).measurementCount = 31239854 := by
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
  fieldProgram_wellFormed n start _ (ShorECDLP.Entrant.MeasuredQuotient.Reverse.divisionProgram_wellFormed n)

theorem multiplicationProgram_wellFormed (n start : Nat) : (multiplicationProgram n start).2.WellFormed :=
  fieldProgram_wellFormed n start _ (ShorECDLP.Entrant.MeasuredQuotient.Reverse.multiplicationProgram_wellFormed n)

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
  fieldProgram_slots n start _ (ShorECDLP.Entrant.MeasuredQuotient.Reverse.divisionProgram_slots n)

theorem multiplicationProgram_slots (n start : Nat) : (multiplicationProgram n start).2.gateSlots ≤ 676000000 :=
  fieldProgram_slots n start _ (ShorECDLP.Entrant.MeasuredQuotient.Reverse.multiplicationProgram_slots n)

attribute [local irreducible] divisionProgram multiplicationProgram
  fieldLookupAddProgram yNegateProgram pointSquareProgram signedFieldProgram xNegateProgram
  ShorECDLP.Entrant.SquareInPlace.paddedSquareProgram

theorem adaptiveCoordinateProgram_wellFormed (start : Nat) : (ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateProgram start).2.WellFormed := by
  exact sequenceProgram_wellFormed 32768 ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateSegments (by
    intro p hp cursor
    simp only [ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateSegments,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact fieldLookupXProgram_wellFormed _ _
    · exact signedFieldProgram_wellFormed _ _
    · exact divisionProgram_wellFormed _ _
    · exact paddedSquareProgram_wellFormed _ _
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
      · intro s; exact paddedSquareProgram_slots _ s
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
  fieldProgram_support n start _ (ShorECDLP.Entrant.MeasuredQuotient.Reverse.divisionProgram_support_static n)

theorem multiplicationProgram_support (n start : Nat) :
    straightWires (multiplicationProgram n start).2 ⊆ windowBaseSupport :=
  fieldProgram_support n start _ (ShorECDLP.Entrant.MeasuredQuotient.Reverse.multiplicationProgram_support_static n)

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
  · exact paddedSquareProgram_support_static _ _
  · exact hf _ _
  · exact multiplicationProgram_support _ _
  · exact xNegateProgram_support_static _ _
  · exact hf _ _
  · exact hs _ _

end ShorECDLP.Entrant.BorrowFlag

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
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

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

noncomputable def adaptiveCoordinateSources (Q : Point) (coeffs : Fin 32768 → PointCoeff) : List AdaptiveCircuit :=
  [fig14LookupX (fun l => baseFieldValue (tablePoint coeffs Q l) .negX),
   signedPointLookupY (fun l => baseFieldValue (tablePoint coeffs Q l) .negY),
   ShorECDLP.Entrant.BorrowFlag.division, ShorECDLP.Entrant.SquareInPlace.paddedSquare,
   fig14LookupX (fun l => baseFieldValue (tablePoint coeffs Q l) .tripleX),
   ShorECDLP.Entrant.BorrowFlag.multiplication, fig14Negate,
   fig14LookupX (fun l => baseFieldValue (tablePoint coeffs Q l) .x),
   signedPointLookupY (fun l => baseFieldValue (tablePoint coeffs Q l) .negY)]

theorem adaptiveCoordinateSources_eq (Q : Point) (coeffs : Fin 32768 → PointCoeff) :
    sequenceCircuit (adaptiveCoordinateSources Q coeffs) =
      ShorECDLP.Entrant.BorrowFlag.coordinateSource (fun l => fieldValue (tablePoint coeffs Q l) .x)
        (fun l => fieldValue (tablePoint coeffs Q l) .y) := by
  have hx (P : Point) : baseFieldValue P .x = fieldValue P .x := rfl
  have hn (P : Point) : baseFieldValue P .negX = fieldValue P .negX := rfl
  have hy (P : Point) : baseFieldValue P .negY = fieldValue P .negY := rfl
  have ht (P : Point) : baseFieldValue P .tripleX = fieldValue P .tripleX := rfl
  simp only [adaptiveCoordinateSources, hx, hn, hy, ht, sequenceCircuit, ShorECDLP.Entrant.BorrowFlag.coordinateSource,
    adaptive_seq_assoc, adaptive_seq_done, field_negX, field_negY, field_tripleX, field_x_mod]

theorem adaptiveCoordinateProgram_run (coeffs : Fin 32768 → PointCoeff) (start : Nat) (Q : Point)
    (history : Fin start → Bool) :
    compiledRun (ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateProgram start) (readConstant coeffs Q) history =
      (ShorECDLP.Entrant.BorrowFlag.coordinateSource (fun l => fieldValue (tablePoint coeffs Q l) .x)
        (fun l => fieldValue (tablePoint coeffs Q l) .y)).run := by
  unfold ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateProgram
  rw [← adaptiveCoordinateSources_eq]
  apply sequenceProgram_run
  unfold ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateSegments adaptiveCoordinateSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))))))
  · intro cursor h
    exact fig14LookupX_compiled coeffs .negX cursor Q h
  · intro cursor h
    exact signedFieldProgram_run coeffs .negY cursor Q h
  · intro cursor h
    exact ShorECDLP.Entrant.BorrowFlag.divisionProgram_run 32768 cursor _ h
  · intro cursor h
    exact ShorECDLP.Entrant.SquareInPlace.paddedSquareProgram_run 32768 cursor _ h
  · intro cursor h
    exact fig14LookupX_compiled coeffs .tripleX cursor Q h
  · intro cursor h
    exact ShorECDLP.Entrant.BorrowFlag.multiplicationProgram_run 32768 cursor _ h
  · intro cursor h
    exact xNegateProgram_run 32768 cursor _ h
  · intro cursor h
    exact fig14LookupX_compiled coeffs .x cursor Q h
  · intro cursor h
    exact signedFieldProgram_run coeffs .negY cursor Q h

theorem adaptiveCoordinateProgram_tCount (coeffs : Fin 32768 → PointCoeff) (start : Nat) (Q : Point)
    (history : Fin start → Bool) :
    compiledTCount (ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateProgram start) (readConstant coeffs Q) history =
      (ShorECDLP.Entrant.BorrowFlag.coordinateSource (fun l => fieldValue (tablePoint coeffs Q l) .x)
        (fun l => fieldValue (tablePoint coeffs Q l) .y)).tCount := by
  unfold ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateProgram
  rw [← adaptiveCoordinateSources_eq]
  apply sequenceProgram_tCount
  unfold ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateSegments adaptiveCoordinateSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))))))
  · intro cursor h
    exact fieldLookupAddProgram_tCount_source coeffs .negX _ cursor Q (by simp) h
  · intro cursor h
    exact signedFieldProgram_tCount coeffs .negY cursor Q h
  · intro cursor h
    exact ShorECDLP.Entrant.BorrowFlag.divisionProgram_tCount 32768 cursor _ h
  · intro cursor h
    exact ShorECDLP.Entrant.SquareInPlace.paddedSquareProgram_tCount 32768 cursor _ h
  · intro cursor h
    exact fieldLookupAddProgram_tCount_source coeffs .tripleX _ cursor Q (by simp) h
  · intro cursor h
    exact ShorECDLP.Entrant.BorrowFlag.multiplicationProgram_tCount 32768 cursor _ h
  · intro cursor h
    exact xNegateProgram_tCount 32768 cursor _ h
  · intro cursor h
    exact fieldLookupAddProgram_tCount_source coeffs .x _ cursor Q (by simp) h
  · intro cursor h
    exact signedFieldProgram_tCount coeffs .negY cursor Q h

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
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

attribute [local irreducible] batchWindowTree
attribute [local irreducible] ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateProgram yNegateProgram
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
  [ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateProgram, yNegateProgram, placedProgram, yNegateProgram]

@[irreducible] noncomputable def sources (coeffs : Fin 32768 → PointCoeff) (Q : Point) : List AdaptiveCircuit :=
  [ShorECDLP.Entrant.BorrowFlag.coordinateSource (fun l => fieldValue (tablePoint coeffs Q l) .x)
    (fun l => fieldValue (tablePoint coeffs Q l) .y), windowYNegate,
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
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ .nil)))
  · intro cursor h; exact adaptiveCoordinateProgram_run coeffs cursor Q h
  · intro cursor h; exact yNegateProgram_run cursor _ h
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

theorem coordinate_count (start : Nat) : (ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateProgram start).1 = 31239854 := by
  have h := sharedAdaptiveCoordinateProgram_count (.right ⟨0, by decide⟩) start
  apply (ShorECDLP.Entrant.BorrowFlag.coordinateProgram_count_eq start).trans
  simpa only [sharedAdaptiveCoordinateProgram, reindexCompiled] using h

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

theorem core_count (start : Nat) : (core start).1 = 31673989 := by
  have h := sequence_count 32768 segments ([31239854, 1022, 432091, 1022] : List Nat) (by
    unfold segments
    exact List.Forall₂.cons coordinate_count (List.Forall₂.cons negate_count
      (List.Forall₂.cons placed_count (List.Forall₂.cons negate_count .nil)))) start
  unfold core
  exact h

theorem prepared_count (start : Nat) : (prepared start).1 = 31673989 := by
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
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
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
  have hfirst : CoherentlyImplementsOn (ShorECDLP.Entrant.BorrowFlag.coordinateSource xs ys)
      (Finsupp.lmapDomain ℂ ℂ (signedLookupCoordinateState xs ys)) BatchedWindowValid :=
    restrictCoherent (ShorECDLP.Entrant.BorrowFlag.coordinateSource_coherent xs ys) (fun s hs => hs.1.1)
  have h := composeCoherent hfirst (signedBatchSource_coherent coeffs Q) (by
    intro s hs
    obtain ⟨hs,P,hP⟩ := hs
    cases he : tablePoint coeffs Q (tableAddressValue pointLookupAddress s) with
    | zero => exact False.elim (hn _ he)
    | some hC => exact batchedWindow_coordinate_ready coeffs Q hQ s hs hC he P hP)
  simpa only [sources,sequenceCircuit,signedBatchSource,adaptive_seq_assoc,adaptive_seq_done,
    batchedWindowState,xs,ys] using h
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

/- The 17-bit initial lookup and its input/Fourier coherence adaptation are from public submission a7a1c745-4abb-4da4-8e60-64ade932fb49 by spariev (GPT 6.1 Sol, Codex), built on the Apache-2.0 ShorECDLP development. -/
section
namespace ShorECDLP.Entrant.First17
open Classical Quantum Challenge Secp256k1 Paper2607_13816 Paper2607_13816.ChallengeMigration
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def bits : List Wire := List.range' 855 16 ++ [536]
def paths : List Wire := List.range' 519 17

def ops : List (LookupOp 131072) :=
  unaryLookupOps (fun l q => pointLeaf ⟨l%131072,Nat.mod_lt _ (by decide)⟩ q)
    (tableAddressTree bits 0 1) 836 paths

theorem ops_measurements : lookupMeasurements ops = 131071 := by
  rw [ops,unaryLookupOps_measurements _ _ _ _
    (tableAddressTree_layout _ _ _ _ _ (by decide) (by decide))]
  have h := tableAddressTree_nodes bits 0 1
  change (tableAddressTree bits 0 1).internalNodes+1 = 131072 at h
  omega

def program (start : Nat) : Straight 131072 start (start+131071) :=
  castFinish (by rw [ops_measurements]) (lookupProgram 131072 ops start)

noncomputable def tablePoint (coeffs : Fin 131072 → PointCoeff) (Q : Point) (a : Nat) : Point :=
  constantPoint Q (coeffs ⟨a%131072,Nat.mod_lt _ (by decide)⟩)

noncomputable def source (table : Nat → Point) : AdaptiveCircuit :=
  directPointLookup table bits paths 836

theorem ops_circuit (coeffs : Fin 131072 → PointCoeff) (Q : Point) :
    lookupCircuit (readConstant coeffs Q) ops = source (tablePoint coeffs Q) := by
  rw [ops,unaryLookupOps_circuit]
  unfold source directPointLookup tableLookupProgram tableLookup
  apply unaryAction_leaf_congr
  intro l hl q
  rw [pointLeaf_instantiate]
  rfl

theorem program_run (coeffs : Fin 131072 → PointCoeff) (Q : Point) (start : Nat)
    (history : Fin start → Bool) :
    ((program start).instantiate (readConstant coeffs Q) history).run =
      (source (tablePoint coeffs Q)).run := by
  rw [program,castFinish_instantiate,lookupProgram_run,ops_circuit]

theorem source_coherent (table : Nat → Point) :
    CoherentlyImplementsOn (source table)
      (Finsupp.lmapDomain ℂ ℂ (fun s => pointWrite (table (tableAddressValue bits s)) s))
      (DirectPointLookupValid paths 836) := by
  apply directPointLookup_coherent table bits paths 836 (by decide) (by decide)
  apply List.disjoint_left.mpr
  intro w hw hp
  simp only [bits,paths,List.mem_cons,List.mem_append,List.not_mem_nil,or_false,List.mem_range'_1] at hw
  simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1] at hp
  dsimp only [Wire] at *
  omega

theorem program_coherent (coeffs : Fin 131072 → PointCoeff) (Q : Point) (start : Nat)
    (history : Fin start → Bool) :
    CoherentlyImplementsOn ((program start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (fun s => pointWrite (tablePoint coeffs Q (tableAddressValue bits s)) s))
      (DirectPointLookupValid paths 836) := by
  unfold CoherentlyImplementsOn
  rw [program_run]
  exact source_coherent _

theorem source_tCount (table : Nat → Point) : (source table).tCount = 917497 := by
  unfold source
  rw [directPointLookup_tCount _ _ _ _ (by decide) (by decide)]
  rfl

theorem program_tCount (coeffs : Fin 131072 → PointCoeff) (Q : Point) (start : Nat)
    (history : Fin start → Bool) :
    ((program start).instantiate (readConstant coeffs Q) history).tCount = 917497 := by
  rw [program,castFinish_instantiate,lookupProgram_tCount,ops_circuit,source_tCount]

theorem ops_physical : ∀ op ∈ ops, op.Physical := by
  apply unaryLookupOps_physical
  · exact tableAddressTree_layout _ _ _ _ _ (by decide) (by decide)
  · intro label control hc g hg
    simp only [pointLeaf,lookupLeafGates,List.mem_map] at hg
    obtain ⟨⟨ref,target⟩,hm,rfl⟩ := hg
    have ht := (List.of_mem_zip hm).2
    change control ≠ target
    have hn : ∀ c ∈ 836::paths, c ∉ pointLogicalWires := by
      intro c hc ht
      simp only [paths,List.mem_cons,List.mem_range'_1] at hc
      simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,
        List.mem_range'_1,List.mem_singleton] at ht
      dsimp only [Wire] at *
      omega
    exact fun he => hn control hc (he ▸ ht)

theorem program_wellFormed (start : Nat) : (program start).WellFormed := by
  unfold program
  rw [castFinish_wellFormed]
  exact lookupProgram_wellFormed _ ops_physical _

theorem program_slots (start : Nat) : (program start).gateSlots ≤ 68550646 := by
  have h := unaryLookupOps_slots_le
    (fun l q => pointLeaf ⟨l%131072,Nat.mod_lt _ (by decide)⟩ q)
    513 (fun _ q => pointLeaf_slots _ q) (tableAddressTree bits 0 1) 836 paths
  have hn := tableAddressTree_nodes bits 0 1
  change (tableAddressTree bits 0 1).internalNodes+1 = 131072 at hn
  simpa only [program,castFinish_gateSlots,lookupProgram_slots,ops] using
    (show lookupSlots (unaryLookupOps (fun l q => pointLeaf ⟨l%131072,Nat.mod_lt _ (by decide)⟩ q)
      (tableAddressTree bits 0 1) 836 paths) ≤ 68550646 by omega)


def support : List Wire := 836 :: bits ++ paths ++ pointLogicalWires

theorem program_support (start : Nat) : straightWires (program start) ⊆ support := by
  have hl : ∀ op ∈ ops, lookupOpWires op ⊆ support := by
    apply unaryLookupOps_support
    · simp [support]
    · intro w hw
      simp [support,hw]
    · intro w hw
      have hb := (tableAddressTree_mem_index bits 0 1 w).mp hw
      simp [support,hb]
    · intro label q hq
      apply lookupLeafGates_support _ _ _ hq
      intro port hp
      have ht := (List.of_mem_zip hp).2
      simp [support,ht]
  simp only [program,straightWires_castFinish,lookupProgram_support]
  intro w hw
  obtain ⟨op,hop,hw⟩ := List.mem_flatMap.mp hw
  exact hl op hop hw

end ShorECDLP.Entrant.First17
end

section
namespace ShorECDLP.Entrant.First17
open Classical Quantum Challenge Secp256k1 Paper2607_13816 Paper2607_13816.ChallengeMigration

def Input (s : BasisState) : Prop := s 836=true ∧ ∀ v,v≠836 → v∉bits → s v=false

theorem input_of_strong (s : BasisState) (hs : FirstWindowInput s) : Input s := by
  refine ⟨hs.1,?_⟩
  intro v hv ha
  apply hs.2 v hv
  intro hh
  apply ha
  simp only [streamAddress] at hh
  exact List.mem_append_left _ hh

theorem input_lookup (s : BasisState) (hs : Input s) : DirectPointLookupValid paths 836 s := by
  refine ⟨?_,?_,hs.1⟩
  · intro v hv
    have mem : 519≤v ∧ v<536 := by simpa [paths,List.mem_range'_1] using hv
    apply hs.2 v (by dsimp only [Wire] at *; omega)
    simp only [bits,List.mem_append,List.mem_singleton,List.mem_range'_1]
    dsimp only [Wire] at *
    omega
  · intro v hv
    have mem : 263≤v ∧ v<519 ∨ 580≤v ∧ v<836 ∨ v=838 := by
      simpa [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_range'_1,or_assoc] using hv
    apply hs.2 v (by dsimp only [Wire] at *; omega)
    simp only [bits,List.mem_append,List.mem_singleton,List.mem_range'_1]
    dsimp only [Wire] at *
    omega

theorem input_update (s : BasisState) (hs : Input s) (w : Wire) (hw : w∈bits) (b : Bool) :
    Input (s[w↦b]) := by
  have ne : (836:Wire)≠w := by
    simp only [bits,List.mem_append,List.mem_range'_1,List.mem_singleton] at hw
    dsimp only [Wire] at *
    omega
  refine ⟨by simpa only [upd,if_neg ne] using hs.1,?_⟩
  intro v hv ha
  have nvw : v≠w := by intro e; exact ha (e ▸ hw)
  simpa only [upd,if_neg nvw] using hs.2 v hv ha

theorem input_clear536 (s : BasisState) (hs : Input s) (clear : s 536=false) : FirstWindowInput s := by
  refine ⟨hs.1,?_⟩
  intro v hv ha
  by_cases e : v=536
  · simpa [e] using clear
  · apply hs.2 v hv
    simpa only [bits,List.mem_append,List.mem_singleton,not_or,e,or_false] using
      (show v∉List.range' 855 16 from ha)

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
private theorem support_linear (V : BasisState → Prop) (L : State →ₗ[ℂ] State)
    (hL : ∀ s, V s → SupportedOn V (L (ket s))) (ψ : State)
    (hψ : SupportedOn V ψ) : SupportedOn V (L ψ) := by
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
end ShorECDLP.Entrant.First17
end

-- ==== part: Single/Schedule ====

section
/-! The left axis uses a 17-bit first load, six 16-bit signed windows and ten 15-bit signed windows.
The right axis uses one 15-bit window followed by twelve 16-bit windows.
The address definition below reuses the signed-address convention of the
Apache-2.0 licensed 2607_13816 submission. -/

namespace ShorECDLP.Entrant.Single

open ShorECDLP.Paper2607_13816

@[irreducible] def widths : List Nat :=
  [17, 16, 16, 16, 16, 16, 16, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15]

@[irreducible] def exponents : List Nat :=
  [246, 230, 214, 198, 182, 166, 150, 135, 120, 105, 90, 75, 60, 45, 30, 15, 0]

@[irreducible] def rightWidths : List Nat := 15 :: List.replicate 12 16

@[irreducible] def rightExponents : List Nat :=
  [192, 176, 160, 144, 128, 112, 96, 80, 64, 48, 32, 16, 0]

theorem rightWidths_sum : rightWidths.sum = 207 := by simp [rightWidths]

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
  (131071, 17) :: List.replicate 6 (31673989, 16) ++ List.replicate 10 (31673989, 15)

@[irreducible] def rightMetadata : List (Nat × Nat) :=
  (31673989, 15) :: List.replicate 12 (31673989, 16)

theorem left_widths : leftMetadata.map Prod.snd = widths := by
  simp [leftMetadata, widths]

theorem right_widths : rightMetadata.map Prod.snd = rightWidths := by
  simp [rightMetadata, rightWidths]

theorem left_record_count : recordCount leftMetadata = 506915158 := by
  norm_num [leftMetadata, recordCount, List.replicate]

theorem right_record_count : recordCount rightMetadata = 411762064 := by
  norm_num [rightMetadata, recordCount, List.replicate]

theorem left_positions_length (start : Nat) : (positions leftMetadata start).length = 263 := by
  rw [positions_length, left_widths, widths_sum]

theorem right_positions_length (start : Nat) : (positions rightMetadata start).length = 207 := by
  rw [positions_length, right_widths, rightWidths_sum]

theorem projected_rows : 131072 + 18 * 32768 + 11 * 16384 = 901120 := by norm_num

theorem projected_records : 506915158 + 411762064 + 854 = 918678076 := by norm_num

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/Rows ====

section
namespace ShorECDLP.Entrant.Single

open ShorECDLP.Challenge ShorECDLP.Paper2607_13816.ChallengeMigration

/-- Chronological signed windows after the direct first load. -/
inductive SignedWindow where
  | left16 (index : Fin 6)
  | left15 (index : Fin 10)
  | right15 (index : Fin 1)
  | right16 (index : Fin 12)

def firstRow (a : Fin 131072) : Fin 901120 := ⟨a.val, by omega⟩

/-- Each width-15 window aliases the two physical address halves. -/
def signedRow : SignedWindow → Fin 32768 → Fin 901120
  | .left16 j, a => ⟨131072 + j.val * 32768 + a.val, by omega⟩
  | .left15 j, a => ⟨327680 + j.val * 16384 + a.val % 16384, by
      have h := Nat.mod_lt a.val (by omega : 0 < 16384)
      omega⟩
  | .right15 _, a => ⟨491520 + a.val % 16384, by
      have h := Nat.mod_lt a.val (by omega : 0 < 16384)
      omega⟩
  | .right16 j, a => ⟨507904 + j.val * 32768 + a.val, by omega⟩

theorem left15_alias (j : Fin 10) (a : Fin 32768) :
    signedRow (.left15 j) a = signedRow (.left15 j) ⟨a.val % 16384, by
      have h := Nat.mod_lt a.val (by omega : 0 < 16384)
      omega⟩ := by
  apply Fin.ext
  simp [signedRow]

theorem right15_alias (j : Fin 1) (a : Fin 32768) :
    signedRow (.right15 j) a = signedRow (.right15 j) ⟨a.val % 16384, by
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
  List.ofFn (fun j : Fin 6 => SignedWindow.left16 j) ++
    List.ofFn (fun j : Fin 10 => SignedWindow.left15 j)

@[irreducible] def rightSigned : List SignedWindow :=
  [SignedWindow.right15 ⟨0, by decide⟩] ++
    List.ofFn (fun j : Fin 12 => SignedWindow.right16 j)

def SignedWindow.width : SignedWindow → Nat
  | .left16 _ | .right16 _ => 16
  | .left15 _ | .right15 _ => 15

def SignedWindow.exponent : SignedWindow → Nat
  | .left16 j => 230 - 16 * j.val
  | .right15 _ => 192
  | .right16 j => 176 - 16 * j.val
  | .left15 j => 135 - 15 * j.val

def SignedWindow.base (Q : Point) : SignedWindow → Point
  | .left16 _ | .left15 _ => G
  | .right15 _ | .right16 _ => Q

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
  (v * 2^246 + leftOffset) • G + rightOffset • Q

noncomputable def increment (Q : Point) (w : SignedWindow) (v : Nat) : Point :=
  ((2 * (v : Int) - (2 : Int)^w.width + 1) : Int) •
    ((halfOrder * 2^w.exponent) • w.base Q)

noncomputable def firstUpdate (Q : Point) (s : BasisState) : BasisState :=
  pointWrite (initialPoint Q (tableAddressValue First17.bits s)) s

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
  coefficients (v * 2^246 + leftOffset) rightOffset

@[irreducible] def oddScalar (exponent address : Nat) : Nat :=
  (2 * address + 1) * 2^exponent * halfOrder

@[irreducible] def signedCoefficients (w : SignedWindow) (address : Nat) : PointCoeff :=
  match w with
  | .left16 _ | .left15 _ => coefficients (oddScalar w.exponent address) 0
  | .right15 _ | .right16 _ => coefficients 0 (oddScalar w.exponent address)

@[irreducible] def mixedCoefficientAt (i : Fin 901120) : PointCoeff :=
  if i.val < 131072 then initialCoefficients i.val
  else if i.val < 327680 then
    coefficients (oddScalar (230 - 16 * ((i.val - 131072) / 32768)) ((i.val - 131072) % 32768)) 0
  else if i.val < 491520 then
    coefficients (oddScalar (135 - 15 * ((i.val - 327680) / 16384)) ((i.val - 327680) % 16384)) 0
  else if i.val < 507904 then
    coefficients 0 (oddScalar 192 ((i.val - 491520) % 16384))
  else coefficients 0 (oddScalar (176 - 16 * ((i.val - 507904) / 32768)) ((i.val - 507904) % 32768))

@[irreducible] def mixedCoefficientTable : List PointCoeff := List.ofFn mixedCoefficientAt

theorem mixedCoefficientTable_length : mixedCoefficientTable.length = 901120 := by
  unfold mixedCoefficientTable
  exact List.length_ofFn

theorem mixedCoefficientAt_first (a : Fin 131072) :
    mixedCoefficientAt (firstRow a) = initialCoefficients a.val := by
  simp [mixedCoefficientAt, firstRow, a.isLt]

theorem mixedCoefficientAt_signed (w : SignedWindow) (a : Fin 32768) :
    mixedCoefficientAt (signedRow w a) =
      signedCoefficients w (a.val % 2^(w.width-1)) := by
  cases w with
  | left16 j =>
    have h1 : ¬ (signedRow (.left16 j) a).val < 131072 := by simp [signedRow]; omega
    have h2 : (signedRow (.left16 j) a).val < 327680 := by simp [signedRow]; omega
    have hj : ((signedRow (.left16 j) a).val - 131072) / 32768 = j.val := by simp [signedRow]; omega
    have ha : ((signedRow (.left16 j) a).val - 131072) % 32768 = a.val := by simp [signedRow]; omega
    simp [mixedCoefficientAt, h1, h2, hj, ha, signedCoefficients, SignedWindow.width,
      SignedWindow.exponent, Nat.mod_eq_of_lt a.isLt]
  | left15 j =>
    have hb : a.val % 16384 < 16384 := Nat.mod_lt _ (by decide)
    have h1 : ¬ (signedRow (.left15 j) a).val < 131072 := by simp [signedRow]; omega
    have h2 : ¬ (signedRow (.left15 j) a).val < 327680 := by simp [signedRow]; omega
    have h3 : (signedRow (.left15 j) a).val < 491520 := by simp [signedRow]; omega
    have hj : ((signedRow (.left15 j) a).val - 327680) / 16384 = j.val := by simp [signedRow]; omega
    have ha : ((signedRow (.left15 j) a).val - 327680) % 16384 = a.val % 16384 := by simp [signedRow]; omega
    simp [mixedCoefficientAt, h1, h2, h3, hj, ha, signedCoefficients,
      SignedWindow.width, SignedWindow.exponent]
  | right15 j =>
    have hb : a.val % 16384 < 16384 := Nat.mod_lt _ (by decide)
    have h1 : ¬ (signedRow (.right15 j) a).val < 131072 := by simp [signedRow]; omega
    have h2 : ¬ (signedRow (.right15 j) a).val < 327680 := by simp [signedRow]; omega
    have h3 : ¬ (signedRow (.right15 j) a).val < 491520 := by simp [signedRow]
    have h4 : (signedRow (.right15 j) a).val < 507904 := by simp [signedRow]; omega
    have ha : ((signedRow (.right15 j) a).val - 491520) % 16384 = a.val % 16384 := by simp [signedRow]
    simp [mixedCoefficientAt, h1, h2, h3, h4, ha, signedCoefficients,
      SignedWindow.width, SignedWindow.exponent]
  | right16 j =>
    have h1 : ¬ (signedRow (.right16 j) a).val < 131072 := by simp [signedRow]; omega
    have h2 : ¬ (signedRow (.right16 j) a).val < 327680 := by simp [signedRow]; omega
    have h3 : ¬ (signedRow (.right16 j) a).val < 491520 := by simp [signedRow]; omega
    have h4 : ¬ (signedRow (.right16 j) a).val < 507904 := by simp [signedRow]; omega
    have hj : ((signedRow (.right16 j) a).val - 507904) / 32768 = j.val := by simp [signedRow]; omega
    have ha : ((signedRow (.right16 j) a).val - 507904) % 32768 = a.val := by simp [signedRow]; omega
    simp [mixedCoefficientAt, h1, h2, h3, h4, hj, ha, signedCoefficients,
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
    | right15 _ | right16 _ => exact hn
  have hr : order • P = 0 := by
    cases w with
    | left16 _ | left15 _ => exact generator_nsmul_eq_zero
    | right15 _ | right16 _ => exact hQ
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
  ⟨First17.bits.reverse, 131071, fun start => reindexStraight firstRow (First17.program start)⟩

theorem initialLookup_circuit (Q : Point) (hQ : order • Q = 0) :
    lookupCircuit (readConstant (fun i : Fin 131072 => initialCoefficients i.val) Q) First17.ops =
      First17.source (initialPoint Q) := by
  rw [First17.ops, unaryLookupOps_circuit]
  unfold First17.source directPointLookup tableLookupProgram tableLookup
  apply unaryAction_leaf_congr
  intro l hl q
  obtain ⟨i, hi, he⟩ := tableAddressTree_label _ 0 1 l hl
  have hlt : l < 131072 := by simpa [he] using hi
  rw [pointLeaf_instantiate]
  simp only [Nat.mod_eq_of_lt hlt, initialCoefficients_point Q hQ, pointTableMask]

theorem firstWindow_run (Q : Point) (hQ : order • Q = 0) (start : Nat)
    (history : Fin start → Bool) :
    ((firstWindow.program start).instantiate (readConstant mixedCoefficientAt Q) history).run =
      (First17.source (initialPoint Q)).run := by
  unfold firstWindow
  rw [reindexStraight_instantiate,
    readConstant_reindex firstRow _ _ Q mixedCoefficientAt_first]
  rw [First17.program, castFinish_instantiate, lookupProgram_run, initialLookup_circuit Q hQ]

theorem firstWindow_coherent (Q : Point) (hQ : order • Q = 0) (start : Nat)
    (history : Fin start → Bool) :
    CoherentlyImplementsOn ((firstWindow.program start).instantiate
      (readConstant mixedCoefficientAt Q) history)
      (Finsupp.lmapDomain ℂ ℂ (firstUpdate Q))
      (DirectPointLookupValid First17.paths 836) := by
  unfold CoherentlyImplementsOn
  rw [firstWindow_run Q hQ start history]
  exact First17.source_coherent (initialPoint Q)

theorem firstWindow_t (Q : Point) (hQ : order • Q = 0) (start : Nat)
    (history : Fin start → Bool) :
    ((firstWindow.program start).instantiate (readConstant mixedCoefficientAt Q) history).tCount = 917497 := by
  unfold firstWindow
  rw [reindexStraight_instantiate,
    readConstant_reindex firstRow _ _ Q mixedCoefficientAt_first]
  rw [First17.program, castFinish_instantiate, lookupProgram_tCount, initialLookup_circuit Q hQ]
  exact First17.source_tCount _

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
    (read : ConstantBit 131072 → Bool) (history : Fin start → Bool) :
    ((First17.program start).instantiate read history).tCount = 917497 := by
  have he : ((First17.program start).instantiate read history).tCount =
      ((First17.program start).instantiate (readConstant (fun i : Fin 131072 => initialCoefficients i.val) 0) history).tCount := by
    simp only [First17.program,castFinish_instantiate,lookupProgram_tCount,First17.ops,unaryLookupOps_circuit]
    apply unary_t_congr
    intro l w
    simp only [pointLeaf,leaf_t_zero]
  exact he.trans (First17.program_tCount (fun i : Fin 131072 => initialCoefficients i.val) 0 start history)
theorem firstWindow_t_uniform (Q : Point) (start : Nat) (history : Fin start → Bool) :
    ((firstWindow.program start).instantiate (readConstant mixedCoefficientAt Q) history).tCount = 917497 := by
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
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
attribute [local irreducible] batchWindowTree
attribute [local irreducible] ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateProgram yNegateProgram
  ShorECDLP.Entrant.BorrowFlag.coordinateSource placedBatchSource windowYNegate ipxProgramOf
  sequenceProgram surroundCompiled relabelCompiled

theorem actual_count : actual.count = 31673989 := by
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
    (sequenceCircuit (sources coeffs Q)).tCount = 501440548 := by
  unfold sources
  rw [sequenceCircuit_four_tCount, (ShorECDLP.Entrant.BorrowFlag.coordinate_numeric_counts _ _).1,
    windowYNegate_numeric_counts.1, batch_t]

theorem core_t (coeffs : Fin 32768 → PointCoeff) (start : Nat) (Q : Point)
    (history : Fin start → Bool) :
    compiledTCount (core start) (readConstant coeffs Q) history =
      (sequenceCircuit (sources coeffs Q)).tCount := by
  unfold core
  apply sequenceProgram_tCount
  unfold segments sources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ .nil)))
  · intro cursor h; exact adaptiveCoordinateProgram_tCount coeffs cursor Q h
  · intro cursor h; unfold windowYNegate; exact yNegateProgram_tCount cursor _ h
  · intro cursor h; exact placed_t coeffs cursor Q h
  · intro cursor h; unfold windowYNegate; exact yNegateProgram_tCount cursor _ h

theorem actual_t (coeffs : Fin 32768 → PointCoeff) (start : Nat) (Q : Point)
    (history : Fin start → Bool) :
    ((actual.program start).instantiate (readConstant coeffs Q) history).tCount = 501440548 := by
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

theorem signedWindow_count (w : SignedWindow) : (signedWindow w).count = 31673989 := by
  unfold signedWindow
  exact Physical.actual_count

theorem signedWindow_t (Q : Point) (w : SignedWindow) (start : Nat)
    (history : Fin start → Bool) :
    (((signedWindow w).program start).instantiate (readConstant mixedCoefficientAt Q) history).tCount = 501440548 := by
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

def params : DecoderParams := ⟨263, 207, by omega, by omega, by omega, by omega⟩

/-- The first right bank follows the complete left-axis transcript. -/
def trialPositions : TrialPositions params where
  left := ⟨(positions leftMetadata 0).toArray, by
    simpa only [List.size_toArray, params] using left_positions_length 0⟩
  right := ⟨(positions rightMetadata 506915158).toArray, by
    simpa only [List.size_toArray, params] using right_positions_length 506915158⟩

def layout : DecodeLayout := ⟨.nearestPair, params, [trialPositions], by simp⟩

theorem left_position_bound (i : Nat) (hi : i ∈ trialPositions.left.toList) :
    i < 506915158 := by
  have h := positions_bounds leftMetadata 0 i
    (show i ∈ positions leftMetadata 0 from by simpa [trialPositions] using hi)
  rw [left_record_count] at h
  omega

theorem right_position_bound (i : Nat) (hi : i ∈ trialPositions.right.toList) :
    506915158 ≤ i ∧ i < 918677222 := by
  have h := positions_bounds rightMetadata 506915158 i
    (show i ∈ positions rightMetadata 506915158 from by simpa [trialPositions] using hi)
  rw [right_record_count] at h
  omega

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/OuterProperties ====

section
namespace ShorECDLP.Entrant.Single
open Quantum ShorECDLP.Challenge ShorECDLP.Paper2607_13816
open ShorECDLP.Paper2607_13816.ChallengeMigration

def bodyT (count : Nat) : Nat := if count = 131071 then 917497 else 501440548

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
    SignedWindow.width, bank, First17.bits, firstWindow, leftMetadata]

theorem right_metadata : rightWindows.map (fun w => (w.count, w.wires.length)) = rightMetadata := by
  simp [rightWindows, rightSigned, signedWindow_count, signedWindow_wires,
    SignedWindow.width, bank, rightMetadata]

theorem left_count : axisCount leftWindows = 506915158 := by
  rw [← recordCount_eq_axisCount, left_metadata, left_record_count]

theorem right_count : axisCount rightWindows = 411762064 := by
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

theorem trialCount_eq : trialCount = 918678076 := by
  rw [trialCount, left_count, right_count]

/-- One trial, with independent same-axis feedback histories and a final reset. -/
@[irreducible] def trial (start : Nat) : Straight 901120 start (start + trialCount) :=
  framed (axis leftWindows start List.nil)
    (axis rightWindows (start + axisCount leftWindows) List.nil)
    (resetBody (start + axisCount leftWindows + axisCount rightWindows))
    (by unfold trialCount; omega)

@[irreducible] def program : Straight 901120 0 918678076 :=
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
    (hb : b ∈ (program.instantiate read Fin.elim0).run) : b.history.length = 918678076 := by
  exact straight_history_length program read Fin.elim0 b hb

end ShorECDLP.Entrant.Single

end

-- ==== part: Single/BodyPhysical ====

section
namespace ShorECDLP.Entrant.Single.Physical
open ShorECDLP Quantum ShorECDLP.Challenge
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
attribute [local irreducible] batchWindowTree
attribute [local irreducible] ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateProgram yNegateProgram ipxProgramOf

private theorem old_in_complete : resetWires ⊆ resetWires := List.Subset.refl _

theorem placed_wellFormed (start : Nat) : (placedProgram start).2.WellFormed := by
  unfold placedProgram
  exact ipxProgramOf_wellFormed _ _ _ ipxTree_layout ipxPaths_outside start

theorem core_wellFormed (start : Nat) : (core start).2.WellFormed := by
  unfold core
  apply sequenceProgram_wellFormed
  intro p hp cursor
  simp only [segments, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateProgram_wellFormed cursor
  · exact yNegateProgram_wellFormed cursor
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

theorem core_slots (start : Nat) : (core start).2.gateSlots ≤ 2683895180 := by
  have h := sequenceProgram_slots_le 32768 segments
    ([1500000000, 26372, 1183842436, 26372] : List Nat) (by
      unfold segments
      refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ .nil)))
      · intro s; exact ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateProgram_slots s
      · intro s; exact yNegateProgram_slots_le s
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
    (straightWires (ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateProgram start).2).map (windowAddressPerm 855 (by decide)) ⊆
      resetWires := by
  intro z hz
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hz
  exact windowBaseSupport_relocated v
    (ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateProgram_support start hv)

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
  exact ⟨coordinate_support, negate_support, placed_support, negate_support⟩

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

attribute [local irreducible] First17.program

private theorem reset_in_complete : resetWires ⊆ resetWires := List.Subset.refl _

theorem firstWindow_wellFormed (start : Nat) : (firstWindow.program start).WellFormed := by
  unfold firstWindow
  exact (reindexStraight_wellFormed firstRow (First17.program start)).mpr (First17.program_wellFormed start)

theorem firstWindow_slots (start : Nat) : (firstWindow.program start).gateSlots ≤ 3000000000 := by
  unfold firstWindow
  rw [reindexStraight_gateSlots]
  exact (First17.program_slots start).trans (by norm_num)

theorem firstWindow_support (start : Nat) :
    straightWires (firstWindow.program start) ⊆ resetWires := by
  unfold firstWindow
  rw [straightWires_reindex]
  apply (First17.program_support start).trans
  intro w hw
  simp only [First17.support, First17.bits, First17.paths, pointLogicalWires,
    pointCorrectionX, pointCorrectionYInf, List.mem_append, List.mem_cons,
    List.not_mem_nil, List.mem_range'_1, or_false] at hw
  simp only [resetWires, List.mem_append, List.mem_cons, List.not_mem_nil,
    List.mem_range, List.mem_range'_1, or_false]
  dsimp only [Wire] at *
  omega

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

theorem left_t_budget : metadataT leftMetadata 0 = 8024000718 := by
  norm_num [leftMetadata, metadataT, bodyT, List.replicate, fourierSlots]

theorem right_t_budget : metadataT rightMetadata 0 = 6518748445 := by
  norm_num [rightMetadata, metadataT, bodyT, List.replicate, fourierSlots]

theorem slots_budget : metadataSlots 3000000000 leftMetadata 0 +
    metadataSlots 3000000000 rightMetadata 0 + 2 = 90000056246 := by
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

theorem trial_slots (start : Nat) : (trial start).gateSlots ≤ 90000056246 := by
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
    ((axis leftWindows start List.nil).instantiate (readConstant mixedCoefficientAt Q) history).tCount ≤ 8024000718 := by
  have h := axis_t leftWindows (readConstant mixedCoefficientAt Q)
    (fun w hw => windows_t Q w (List.mem_append_left _ hw)) start List.nil history
  rwa [left_metadata, List.length_nil, left_t_budget] at h

theorem right_axis_t (Q : Point) (start : Nat) (history : Fin start → Bool) :
    ((axis rightWindows start List.nil).instantiate (readConstant mixedCoefficientAt Q) history).tCount ≤ 6518748445 := by
  have h := axis_t rightWindows (readConstant mixedCoefficientAt Q)
    (fun w hw => windows_t Q w (List.mem_append_right _ hw)) start List.nil history
  rwa [right_metadata, List.length_nil, right_t_budget] at h

theorem trial_t (Q : Point) (start : Nat) (history : Fin start → Bool) :
    ((trial start).instantiate (readConstant mixedCoefficientAt Q) history).tCount ≤ 14542749163 := by
  unfold trial
  exact framed_t_le _ _ _ _ _ history 8024000718 6518748445
    (left_axis_t Q start history) (fun h => right_axis_t Q _ h) (fun h => resetBody_t _ _ h)

theorem program_wellFormed : program.WellFormed := by
  unfold program
  rw [castFinish_wellFormed]
  exact trial_wellFormed 0

theorem program_slots : program.gateSlots ≤ 90000056246 := by
  unfold program
  rw [castFinish_gateSlots]
  exact trial_slots 0

theorem program_t (Q : Point) :
    (program.instantiate (readConstant mixedCoefficientAt Q) Fin.elim0).tCount ≤ 14542749163 := by
  unfold program
  rw [castFinish_instantiate]
  exact trial_t Q 0 Fin.elim0

theorem program_measurements (read : ConstantBit 901120 → Bool) :
    (program.instantiate read Fin.elim0).measurementCount = 918678076 := by
  exact program.measurementCount read Fin.elim0

theorem stream_support : streamAddress ⊆ resetWires := by
  intro v hv
  exact List.mem_append_right _ hv

theorem windows_bank_support (w : Window 901120) (hw : w ∈ leftWindows ++ rightWindows) :
    w.wires ⊆ resetWires := by
  rcases windows_cases w hw with rfl | ⟨s, rfl⟩
  · unfold firstWindow
    exact (show First17.bits.reverse ⊆ resetWires by decide +kernel)
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
    (resources (program.instantiate (readConstant mixedCoefficientAt Q) Fin.elim0)).tModel ≤ 14542749163 ∧
    (resources (program.instantiate (readConstant mixedCoefficientAt Q) Fin.elim0)).measurements = 918678076 :=
  ⟨program_qubits _, program_t Q, program_measurements _⟩

theorem table_rows_limit : mixedCoefficientTable.length ≤ 983040 := by
  rw [mixedCoefficientTable_length]
  norm_num

theorem one_candidate_check : layout.trials.length * decoderCandidateLimit layout.kind layout.params = 1 := by
  simp [layout, decoderCandidateLimit]

theorem resource_product : 854 * 14542749163 = 12419507785202 := by norm_num

end ShorECDLP.Entrant.Single

end

/-! Generic measured phase compilation and source cost certificates. -/

section

section

/-! Measurement-assisted Toffoli synthesis using a reusable clean ancillary wire.
The temporary AND follows Gidney, Quantum 2, 74 (2018). Its four T rotations and
one S rotation cost five in the challenge's P-count model. -/
namespace ShorECDLP.Entrant.AndGadget
open Quantum ShorECDLP.Paper2607_13816
noncomputable section
set_option maxHeartbeats 200000

attribute [local irreducible] Quantum.applyGate Quantum.run Quantum.ket
set_option linter.unusedSimpArgs false


private theorem upd_twice (s : BasisState) (q : Wire) (a b : Bool) :
    s[q ↦ a][q ↦ b] = s[q ↦ b] := by
  funext w
  by_cases h : w = q <;> simp [upd, h]
private theorem upd_self (s : BasisState) (q : Wire) : s[q ↦ s q] = s := by
  funext w
  by_cases h : w = q <;> simp [upd, h]

private theorem phase_square (dir : PhaseDir) (k : Nat) :
    phaseCoeff dir (k+1)^2 = phaseCoeff dir k := by
  rw [phaseCoeff, ← Complex.exp_nat_mul, phaseCoeff]
  congr 1
  cases dir <;> simp only [phaseAngle, pow_succ] <;> push_cast <;> field_simp

private theorem phase_two : phaseCoeff .forward 2 = Complex.I := by
  simp only [phaseCoeff, phaseAngle]
  convert Complex.exp_pi_div_two_mul_I using 1
  congr 1
  push_cast
  ring

private theorem phase_two_inverse : phaseCoeff .inverse 2 = -Complex.I := by
  simp only [phaseCoeff, phaseAngle]
  convert Complex.exp_neg_pi_div_two_mul_I using 1
  congr 1
  push_cast
  ring

/-- Diagonal phase on the XOR of a control and target. -/
def xorPhase (dir : PhaseDir) (a q : Wire) : Circuit :=
  [.CX a q, .P dir 3 q, .CX a q]

private theorem xorPhase_ket (dir : PhaseDir) (a q : Wire) (ha : a ≠ q)
    (s : BasisState) :
    Quantum.run (xorPhase dir a q) (ket s) =
      (if s q ^^ s a then phaseCoeff dir 3 else 1) • ket s := by
  simp only [xorPhase, Quantum.run_cons, Quantum.run_nil, applyGate_CX_ket,
    applyGate_P_ket, map_smul, upd_same, upd_other _ _ _ ha,
    upd_twice, Bool.xor_assoc, Bool.xor_self, Bool.xor_false, upd_self]

/-- Four diagonal parity phases; additional Clifford CNOTs keep the proof modular. -/
def parityPhase (a b q : Wire) : Circuit :=
  [.P .forward 3 q] ++ xorPhase .inverse a q ++
    [.CX a q] ++ xorPhase .forward b q ++ [.CX a q] ++ xorPhase .inverse b q

private theorem parityPhase_ket (a b q : Wire) (ha : a ≠ q) (hb : b ≠ q)
    (s : BasisState) :
    Quantum.run (parityPhase a b q) (ket s) =
      (if s a && s b then (if s q then Complex.I else -Complex.I) else 1) • ket s := by
  have hmul := phaseCoeff_mul_adjoint .forward 3
  have himul := phaseCoeff_adjoint_mul .forward 3
  have hsq := phase_square .forward 2
  have hisq := phase_square .inverse 2
  rw [phase_two] at hsq
  rw [phase_two_inverse] at hisq
  change phaseCoeff .forward 3 * phaseCoeff .inverse 3 = 1 at hmul
  change phaseCoeff .inverse 3 * phaseCoeff .forward 3 = 1 at himul
  simp only [parityPhase, Quantum.run_append, Quantum.run_singleton,
    applyGate_P_ket, applyGate_CX_ket, map_smul, xorPhase_ket _ a q ha,
    xorPhase_ket _ b q hb, upd_same, upd_other _ _ _ ha, upd_other _ _ _ hb,
    upd_twice, Bool.xor_assoc, Bool.xor_self, Bool.xor_false, upd_self, smul_smul]
  cases ha' : s a <;> cases hb' : s b <;> cases hq : s q <;>
    simp only [ha', hb', hq, Bool.false_and, Bool.true_and,
      Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, mul_one, one_mul,
      ← pow_two, hsq, hisq, mul_assoc, hmul, himul, one_pow]

/-- Exact temporary AND on a clean target; S is counted as one P rotation. -/
def andCompute (a b q : Wire) : Circuit :=
  [.H q] ++ parityPhase a b q ++ [.H q, .P .forward 2 q]

private theorem invSqrtTwo_square :
    (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = (1/2 : ℂ) := by
  have h : Real.sqrt 2 ≠ 0 := by positivity
  have hr : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1/2 : ℝ) := by
    field_simp
    nlinarith [Real.mul_self_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
  have hc := congrArg (fun x : ℝ => (x : ℂ)) hr
  simpa using hc

/-- No data-dependent phase remains on the clean-target subspace. -/
theorem andCompute_ket (a b q : Wire) (ha : a ≠ q) (hb : b ≠ q)
    (s : BasisState) (hq : s q = false) :
    Quantum.run (andCompute a b q) (ket s) = ket (s[q ↦ s a && s b]) := by
  have hs : s[q ↦ false] = s := by simpa only [hq] using upd_self s q
  have hsq : ((↑(Real.sqrt 2) : ℂ)⁻¹)^2 = (1/2 : ℂ) := by
    simpa [pow_two] using invSqrtTwo_square
  simp only [andCompute, Quantum.run_append, Quantum.run_cons, Quantum.run_nil,
    LinearMap.id_coe, id_eq, applyGate_H_ket, map_add, map_smul,
    parityPhase_ket a b q ha hb, upd_other _ _ _ ha, upd_other _ _ _ hb,
    upd_same, hq, Bool.false_eq_true, if_false, if_true, mul_one,
    applyGate_P_ket, phase_two, upd_twice]
  cases ha' : s a <;> cases hb' : s b <;>
    simp [ha', hb', hs, hq, smul_add, smul_smul, mul_add, add_mul,
      invSqrtTwo_square, Complex.I_mul_I]
  all_goals match_scalars <;> ring_nf
  all_goals norm_num [hsq, Complex.I_sq]

/-- One branch of AND-compute, target update, and corrected X erasure. -/
def toffoliBranch (a b t q : Wire) (outcome : Bool) : State →ₗ[ℂ] State :=
  (Quantum.run (if outcome then controlledZ a b else [])).comp
    ((xResetKraus q outcome).comp (Quantum.run (andCompute a b q ++ [.CX q t])))

private theorem reset_after_update (s : BasisState) (q t : Wire) (hqt : q ≠ t)
    (hq : s q = false) (v z : Bool) :
    s[q ↦ v][t ↦ z][q ↦ false] = s[t ↦ z] := by
  funext w
  by_cases hwq : w = q <;> by_cases hwt : w = t <;> simp_all [upd]

/-- Both outcomes have the same data-independent amplitude, with no residual phase. -/
theorem toffoliBranch_ket (a b t q : Wire) (outcome : Bool)
    (hab : a ≠ b) (haq : a ≠ q) (hbq : b ≠ q)
    (hat : a ≠ t) (hbt : b ≠ t) (hqt : q ≠ t)
    (s : BasisState) (hq : s q = false) :
    toffoliBranch a b t q outcome (ket s) =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • applyGate (.CCX a b t) (ket s) := by
  simp only [toffoliBranch, LinearMap.comp_apply, Quantum.run_append,
    andCompute_ket a b q haq hbq s hq, Quantum.run_singleton, applyGate_CX_ket,
    upd_same, upd_other _ _ _ (Ne.symm hqt), xResetKraus_ket,
    upd_other _ _ _ hqt, reset_after_update s q t hqt hq, map_smul,
    applyGate_CCX_ket, xResetCoeff]
  cases outcome <;> simp only [Bool.false_eq_true, if_false, if_true,
    Quantum.run_nil, run_controlledZ_ket a b _ hab,
    upd_other _ _ _ hat, upd_other _ _ _ hbt]
  all_goals cases ha : s a <;> cases hb : s b <;>
    simp [ha, hb, smul_smul]

/-- The primitive also holds on arbitrary supported superpositions. -/
theorem toffoliBranch_supported (a b t q : Wire) (outcome : Bool)
    (hab : a ≠ b) (haq : a ≠ q) (hbq : b ≠ q)
    (hat : a ≠ t) (hbt : b ≠ t) (hqt : q ≠ t)
    (psi : State) (hpsi : SupportedOn (fun s => s q = false) psi) :
    toffoliBranch a b t q outcome psi =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • applyGate (.CCX a b t) psi := by
  have h : BranchCoherentOn (applyGate (.CCX a b t)) (fun s => s q = false)
      ⟨[], toffoliBranch a b t q outcome⟩ (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) :=
    fun s hs => toffoliBranch_ket a b t q outcome hab haq hbq hat hbt hqt s hs
  exact h.on_supported hpsi

/-- Every rotation, including S, is charged. -/
theorem andCompute_tCount (a b q : Wire) : ShorECDLP.tCount (andCompute a b q) = 5 := by
  rfl

theorem andCompute_wellFormed (a b q : Wire) (ha : a ≠ q) (hb : b ≠ q) :
    CircuitWellFormed (andCompute a b q) := by
  simp [andCompute, parityPhase, xorPhase, CircuitWellFormed, Gate.WellFormed, ha, hb]

end
end ShorECDLP.Entrant.AndGadget
end

section

/-! A static record-preserving compiler for measurement-assisted Toffoli gates. -/
namespace ShorECDLP.Entrant.AndGadget
open Quantum ShorECDLP.Challenge

/-- The compiler records the location of every original measurement. -/
structure Lowered (n oldFinish start : Nat) where
  finish : Nat
  program : Straight n start finish
  records : Fin oldFinish → Fin finish

/-- Execute a fixed literal prefix. -/
def literals {n s e : Nat} (gs : Circuit) (next : Straight n s e) : Straight n s e :=
  gs.foldr (fun g tail => .gate (.literal g) tail) next

/-- The selected phase correction uses Clifford gates only. -/
def toffoliPrefix {n s e : Nat} (a b target scratch : Wire)
    (next : Straight n (s+1) e) : Straight n s e :=
  literals (andCompute a b scratch ++ [.CX scratch target])
    (.measure scratch
      (.recordGate (Fin.last s) true (.H b)
        (.recordGate (Fin.last s) true (.CX a b)
          (.recordGate (Fin.last s) true (.H b) next))))

/-- Only unconditional literal Toffolis are replaced. Original conditional gates
and their record references remain exactly represented. -/
def lower {n oldStart oldFinish : Nat} (scratch : Wire)
    (p : Straight n oldStart oldFinish) (start : Nat)
    (records : Fin oldStart → Fin start) : Lowered n oldFinish start :=
  match p with
  | .done => ⟨start, .done, records⟩
  | .gate (.literal (.CCX a b t)) next =>
      let r := lower scratch next (start+1) (fun i => (records i).castSucc)
      ⟨r.finish, toffoliPrefix a b t scratch r.program, r.records⟩
  | .gate g next =>
      let r := lower scratch next start records
      ⟨r.finish, .gate g r.program, r.records⟩
  | .recordGate i v g next =>
      let r := lower scratch next start records
      ⟨r.finish, .recordGate (records i) v g r.program, r.records⟩
  | .measure w next =>
      let r := lower scratch next (start+1)
        (Fin.lastCases (Fin.last start) (fun i => (records i).castSucc))
      ⟨r.finish, .measure w r.program, r.records⟩

/-- Number of new records, independent of all constant values and outcomes. -/
def added {n s e : Nat} : Straight n s e → Nat
  | .done => 0
  | .gate (.literal (.CCX _ _ _)) next => 1 + added next
  | .gate _ next => added next
  | .recordGate _ _ _ next => added next
  | .measure _ next => added next

end ShorECDLP.Entrant.AndGadget

namespace ShorECDLP.Entrant.AndGadget
open Quantum ShorECDLP.Challenge
noncomputable section

/-- Backward evaluation against a predicate on the complete record. -/
def expectation {n s e : Nat} (read : ConstantBit n → Bool)
    (p : Straight n s e) (history : Fin s → Bool) (psi : State)
    (accept : (Fin e → Bool) → Bool) : ℝ :=
  match p with
  | .done => if accept history then normSq psi else 0
  | .gate g next => expectation read next history (Quantum.run (g.instantiate read) psi) accept
  | .recordGate i v g next => expectation read next history
      (Quantum.run (if history i = v then [g] else []) psi) accept
  | .measure w next =>
      expectation read next (Fin.lastCases false history) (xResetKraus w false psi) accept +
      expectation read next (Fin.lastCases true history) (xResetKraus w true psi) accept

/-- The static record cost of an appended program is additive. -/
theorem added_append {n s m e : Nat} (p : Straight n s m) (q : Straight n m e) :
    added (p.append q) = added p + added q := by
  induction p with
  | done => simp [Straight.append, added]
  | gate g p ih =>
      cases g with
      | literal g => cases g <;> simp [Straight.append, added, ih, Nat.add_assoc]
      | whenBit r v g => simp [Straight.append, added, ih]
  | recordGate i v g p ih => exact ih q
  | measure w p ih => exact ih q

end
end ShorECDLP.Entrant.AndGadget

namespace ShorECDLP.Entrant.AndGadget
open Quantum ShorECDLP.Challenge

/-- The new cursor is the old remaining record count plus one per lowered gate. -/
theorem lower_finish {n s e : Nat} (scratch : Wire) (p : Straight n s e)
    (start : Nat) (records : Fin s → Fin start) :
    (lower scratch p start records).finish + s = start + e + added p := by
  induction p generalizing start with
  | done => simp [lower, added, Nat.add_comm]
  | gate g p ih =>
      cases g with
      | literal g =>
          cases g <;> simp only [lower, added]
          all_goals have h := ih (start := start) records
          all_goals try omega
          exact (by have h := ih (start := start+1) (fun i => (records i).castSucc); omega)
      | whenBit r v g => exact ih start records
  | recordGate i v g p ih => exact ih start records
  | measure w p ih =>
      simp only [lower, added]
      have h := ih (start := start+1)
        (Fin.lastCases (Fin.last start) (fun i => (records i).castSucc))
      omega

/-- Old references into the initial prefix keep their values. -/
theorem lower_initial {n s e : Nat} (scratch : Wire) (p : Straight n s e)
    (start : Nat) (records : Fin s → Fin start) (i : Fin s) :
    ((lower scratch p start records).records (i.castLE p.cursor_mono)).val = (records i).val := by
  induction p generalizing start with
  | done => rfl
  | gate g p ih =>
      cases g with
      | literal g =>
          cases g <;> simp only [lower]
          all_goals apply ih
      | whenBit r v g => exact ih start records i
  | recordGate j v g p ih => exact ih start records i
  | measure w p ih =>
      simp only [lower]
      have h := ih (start := start+1)
        (Fin.lastCases (Fin.last start) (fun i => (records i).castSucc)) i.castSucc
      simpa only [Fin.castLE, Fin.val_castSucc, Fin.lastCases_castSucc] using h

end ShorECDLP.Entrant.AndGadget

namespace ShorECDLP.Entrant.AndGadget
open Quantum ShorECDLP.Challenge ShorECDLP.Paper2607_13816
noncomputable section
attribute [local irreducible] Quantum.run Quantum.applyGate Quantum.ket

private theorem state_normSq_smul (c : ℂ) (psi : State) :
    normSq (c • psi) = Complex.normSq c * normSq psi := by
  unfold normSq
  rw [inner_smul_smul, ← Complex.normSq_eq_conj_mul_self]
  simp

theorem expectation_smul {n s e : Nat} (read : ConstantBit n → Bool)
    (p : Straight n s e) (history : Fin s → Bool) (psi : State)
    (accept : (Fin e → Bool) → Bool) (c : ℂ) :
    expectation read p history (c • psi) accept =
      Complex.normSq c * expectation read p history psi accept := by
  induction p generalizing psi with
  | done => simp only [expectation]; split <;> simp [state_normSq_smul]
  | gate g p ih => simp only [expectation, map_smul, ih]
  | recordGate i v g p ih => simp only [expectation, map_smul, ih]
  | measure w p ih => simp only [expectation, map_smul, ih, mul_add]

theorem expectation_literals {n s e : Nat} (read : ConstantBit n → Bool)
    (gs : Circuit) (p : Straight n s e) (history : Fin s → Bool) (psi : State)
    (accept : (Fin e → Bool) → Bool) :
    expectation read (literals gs p) history psi accept =
      expectation read p history (Quantum.run gs psi) accept := by
  induction gs generalizing psi with
  | nil => simp [literals, Quantum.run_nil]
  | cons g gs ih =>
      simp only [literals, List.foldr_cons, expectation, TemplateGate.instantiate,
        Quantum.run_nil, Quantum.run_cons]
      exact ih (applyGate g psi)

theorem expectation_toffoliPrefix {n s e : Nat} (read : ConstantBit n → Bool)
    (a b t q : Wire) (p : Straight n (s+1) e) (history : Fin s → Bool)
    (psi : State) (accept : (Fin e → Bool) → Bool) :
    expectation read (toffoliPrefix a b t q p) history psi accept =
      expectation read p (Fin.lastCases false history) (toffoliBranch a b t q false psi) accept +
      expectation read p (Fin.lastCases true history) (toffoliBranch a b t q true psi) accept := by
  simp only [toffoliPrefix, expectation_literals, expectation, Fin.lastCases_last,
    Bool.false_eq_true, if_false, if_true, Quantum.run_nil,
    toffoliBranch, LinearMap.comp_apply, controlledZ,
    Quantum.run_cons, Quantum.run_nil]

/-- The source never accesses the new ancillary wire. -/
def Fresh {n s e : Nat} (q : Wire) : Straight n s e → Prop
  | .done => True
  | .gate (.literal g) p => q ∉ gateWires g ∧ Fresh q p
  | .gate (.whenBit _ _ g) p => q ∉ gateWires g ∧ Fresh q p
  | .recordGate _ _ g p => q ∉ gateWires g ∧ Fresh q p
  | .measure w p => q ≠ w ∧ Fresh q p

private theorem gate_frame (q : Wire) (gs : Circuit) (hq : q ∉ circuitWires gs)
    (psi : State) (hpsi : SupportedOn (fun s => s q = false) psi) :
    SupportedOn (fun s => s q = false) (Quantum.run gs psi) := by
  have h := AdaptiveCircuit.branch_frame (.unitary gs .done) q false
    (by simpa [AdaptiveCircuit.wires] using hq)
    ⟨[], Quantum.run gs⟩ (by simp only [AdaptiveCircuit.run, List.map_singleton, List.mem_singleton]; rfl) psi hpsi
  exact h

end
end ShorECDLP.Entrant.AndGadget

namespace ShorECDLP.Entrant.AndGadget
open Quantum ShorECDLP.Challenge ShorECDLP.Paper2607_13816
noncomputable section
attribute [local irreducible] Quantum.run Quantum.applyGate Quantum.ket

private theorem reset_frame (q w : Wire) (hq : q ≠ w) (outcome : Bool)
    (psi : State) (hpsi : SupportedOn (fun s => s q = false) psi) :
    SupportedOn (fun s => s q = false) (xResetKraus w outcome psi) := by
  apply AdaptiveCircuit.branch_frame (.xMeasureReset w .done .done) q false
    (by simpa [AdaptiveCircuit.wires] using hq)
    ⟨[outcome], xResetKraus w outcome⟩ ?_ psi hpsi
  cases outcome <;>
    simp only [AdaptiveCircuit.run, List.map_singleton, List.mem_append, List.mem_singleton]
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem half_amplitude :
    Complex.normSq (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = (1/2 : ℝ) := by
  simp only [Complex.normSq_ofReal]
  have h : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  nlinarith [Real.mul_self_sqrt (show (0:ℝ) ≤ 2 by norm_num)]

/-- Compilation preserves every predicate on the original measurement record. -/
theorem lower_expectation {n s e : Nat} (q : Wire) (p : Straight n s e)
    (start : Nat) (records : Fin s → Fin start)
    (read : ConstantBit n → Bool) (history : Fin s → Bool)
    (newHistory : Fin start → Bool) (psi : State)
    (accept : (Fin e → Bool) → Bool)
    (hmap : newHistory ∘ records = history) (hf : Fresh q p) (hwf : p.WellFormed)
    (hpsi : SupportedOn (fun s => s q = false) psi) :
    expectation read (lower q p start records).program newHistory psi
        (fun h => accept (h ∘ (lower q p start records).records)) =
      expectation read p history psi accept := by
  induction p generalizing start psi with
  | done => simp only [lower, expectation, hmap]
  | gate g p ih =>
      cases g with
      | literal g =>
          cases g with
          | CCX a b t =>
              obtain ⟨hf, htail⟩ := hf
              have hqs : q ≠ a ∧ q ≠ b ∧ q ≠ t := by simpa [gateWires] using hf
              have hw : a ≠ b ∧ a ≠ t ∧ b ≠ t := hwf.1
              have hp : SupportedOn (fun s => s q = false) (applyGate (.CCX a b t) psi) := by
                simpa only [Quantum.run_singleton] using gate_frame q ([.CCX a b t] : Circuit)
                  (by simpa [circuitWires] using hf) psi hpsi
              simp only [lower, expectation_toffoliPrefix]
              rw [toffoliBranch_supported a b t q false hw.1 hqs.1.symm hqs.2.1.symm
                    hw.2.1 hw.2.2 hqs.2.2 psi hpsi,
                  toffoliBranch_supported a b t q true hw.1 hqs.1.symm hqs.2.1.symm
                    hw.2.1 hw.2.2 hqs.2.2 psi hpsi,
                  expectation_smul, expectation_smul]
              have hm (outcome : Bool) :
                  (Fin.lastCases outcome newHistory) ∘ (fun i => (records i).castSucc) = history := by
                simpa only [Function.comp_def, Fin.lastCases_castSucc] using hmap
              rw [ih (start+1) (fun i => (records i).castSucc) history
                    (Fin.lastCases false newHistory) _ accept (hm false) htail hwf.2 hp,
                  ih (start+1) (fun i => (records i).castSucc) history
                    (Fin.lastCases true newHistory) _ accept (hm true) htail hwf.2 hp]
              simp only [expectation, TemplateGate.instantiate, Quantum.run_singleton, half_amplitude]
              ring
          | X t | H t | CX a t | P dir k t =>
              simp only [lower, expectation]
              apply ih start records history newHistory _ accept hmap hf.2 hwf.2
              apply gate_frame q _ ?_ psi hpsi
              simpa [TemplateGate.instantiate, circuitWires] using hf.1
      | whenBit r v g =>
          simp only [lower, expectation]
          apply ih start records history newHistory _ accept hmap hf.2 hwf.2
          apply gate_frame q _ ?_ psi hpsi
          simp only [TemplateGate.instantiate]
          split
          · simpa [circuitWires] using hf.1
          · simp [circuitWires]
  | recordGate i v g p ih =>
      have hm : newHistory (records i) = history i := congrFun hmap i
      simp only [lower, expectation, hm]
      apply ih start records history newHistory _ accept hmap hf.2 hwf.2
      apply gate_frame q _ ?_ psi hpsi
      split
      · simpa [circuitWires] using hf.1
      · simp [circuitWires]
  | measure w p ih =>
      simp only [lower, expectation]
      congr 1
      all_goals
        apply ih (start+1)
          (Fin.lastCases (Fin.last start) (fun i => (records i).castSucc)) _ _ _ accept ?_ hf.2 hwf
          (reset_frame q w hf.1 _ psi hpsi)
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        all_goals simp [Function.comp_def, ← hmap]

end
end ShorECDLP.Entrant.AndGadget

namespace ShorECDLP.Entrant.AndGadget
open Quantum ShorECDLP.Challenge
set_option linter.unusedSimpArgs false

theorem literals_slots {n s e : Nat} (gs : Circuit) (p : Straight n s e) :
    (literals gs p).gateSlots = gs.length + p.gateSlots := by
  induction gs with
  | nil => simp [literals]
  | cons g gs ih =>
      change 1 + (literals gs p).gateSlots = (gs.length+1) + p.gateSlots
      rw [ih]
      omega

theorem toffoliPrefix_slots {n s e : Nat} (a b t q : Wire) (p : Straight n (s+1) e) :
    (toffoliPrefix a b t q p).gateSlots = 19 + p.gateSlots := by
  simp [toffoliPrefix, literals_slots, andCompute, parityPhase, xorPhase, Straight.gateSlots]
  omega

theorem lower_slots {n s e : Nat} (q : Wire) (p : Straight n s e)
    (start : Nat) (records : Fin s → Fin start) :
    (lower q p start records).program.gateSlots = p.gateSlots + 18 * added p := by
  induction p generalizing start with
  | done => simp [lower, added, Straight.gateSlots]
  | gate g p ih =>
      cases g with
      | literal g => cases g <;>
          simp [lower, added, Straight.gateSlots, toffoliPrefix_slots, ih] <;> omega
      | whenBit r v g => simp [lower, added, Straight.gateSlots, ih, Nat.add_assoc]
  | recordGate i v g p ih => simp [lower, added, Straight.gateSlots, ih, Nat.add_assoc]
  | measure w p ih => exact ih _ _

theorem literals_wellFormed {n s e : Nat} (gs : Circuit) (p : Straight n s e)
    (hg : CircuitWellFormed gs) (hp : p.WellFormed) : (literals gs p).WellFormed := by
  induction gs with
  | nil => exact hp
  | cons g gs ih => exact ⟨hg g (by simp), ih (fun k hk => hg k (by simp [hk]))⟩

theorem lower_wellFormed {n s e : Nat} (q : Wire) (p : Straight n s e)
    (start : Nat) (records : Fin s → Fin start) (hf : Fresh q p) (hp : p.WellFormed) :
    (lower q p start records).program.WellFormed := by
  induction p generalizing start with
  | done => trivial
  | gate g p ih =>
      cases g with
      | literal g =>
          cases g with
          | CCX a b t =>
              have hq : q ≠ a ∧ q ≠ b ∧ q ≠ t := by simpa [gateWires] using hf.1
              have hw : a ≠ b ∧ a ≠ t ∧ b ≠ t := hp.1
              apply literals_wellFormed
              · exact (circuitWellFormed_append _ _).mpr
                  ⟨andCompute_wellFormed a b q hq.1.symm hq.2.1.symm,
                    by simpa [CircuitWellFormed, Gate.WellFormed] using hq.2.2⟩
              · exact ⟨trivial, hw.1, trivial, ih _ _ hf.2 hp.2⟩
          | X t | H t | CX a t | P dir k t => exact ⟨hp.1, ih _ _ hf.2 hp.2⟩
      | whenBit r v g => exact ⟨hp.1, ih _ _ hf.2 hp.2⟩
  | recordGate i v g p ih => exact ⟨hp.1, ih _ _ hf.2 hp.2⟩
  | measure w p ih => exact ih _ _ hf.2 hp

theorem literals_t {n s e : Nat} (read : ConstantBit n → Bool)
    (gs : Circuit) (p : Straight n s e) (history : Fin s → Bool) :
    ((literals gs p).instantiate read history).tCount =
      ShorECDLP.tCount gs + (p.instantiate read history).tCount := by
  induction gs with
  | nil => simp [literals, ShorECDLP.tCount]
  | cons g gs ih =>
      change ShorECDLP.tCount [g] + ((literals gs p).instantiate read history).tCount = _
      rw [ih]
      simp [ShorECDLP.tCount, Nat.add_assoc]

theorem toffoliPrefix_t {n s e : Nat} (read : ConstantBit n → Bool)
    (a b t q : Wire) (p : Straight n (s+1) e) (history : Fin s → Bool) :
    ((toffoliPrefix a b t q p).instantiate read history).tCount =
      5 + max (p.instantiate read (Fin.lastCases false history)).tCount
        (p.instantiate read (Fin.lastCases true history)).tCount := by
  simp [toffoliPrefix, literals_t, andCompute, parityPhase, xorPhase,
    Straight.instantiate, AdaptiveCircuit.tCount, ShorECDLP.tCount, tCost]

/-- Exact T reduction, including arbitrary original record-controlled gates. -/
theorem lower_t {n s e : Nat} (q : Wire) (p : Straight n s e)
    (start : Nat) (records : Fin s → Fin start) (read : ConstantBit n → Bool)
    (history : Fin s → Bool) (newHistory : Fin start → Bool)
    (hmap : newHistory ∘ records = history) :
    ((lower q p start records).program.instantiate read newHistory).tCount + 2 * added p =
      (p.instantiate read history).tCount := by
  induction p generalizing start with
  | done => rfl
  | gate g p ih =>
      cases g with
      | literal g =>
          cases g with
          | CCX a b t =>
              have hm (outcome : Bool) :
                  (Fin.lastCases outcome newHistory) ∘ (fun i => (records i).castSucc) = history := by
                simpa only [Function.comp_def, Fin.lastCases_castSucc] using hmap
              have h0 := ih (start+1) (fun i => (records i).castSucc) history
                (Fin.lastCases false newHistory) (hm false)
              have h1 := ih (start+1) (fun i => (records i).castSucc) history
                (Fin.lastCases true newHistory) (hm true)
              simp only [lower, toffoliPrefix_t, added, Straight.instantiate,
                TemplateGate.instantiate, AdaptiveCircuit.tCount, ShorECDLP.tCount,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, tCost] at *
              omega
          | X t | H t | CX a t | P dir k t =>
              have h := ih start records history newHistory hmap
              simp only [lower, added, Straight.instantiate, TemplateGate.instantiate,
                AdaptiveCircuit.tCount] at *
              omega
      | whenBit r v g =>
          have h := ih start records history newHistory hmap
          simp only [lower, added, Straight.instantiate, AdaptiveCircuit.tCount] at *
          omega
  | recordGate i v g p ih =>
      have h := ih start records history newHistory hmap
      have hm : newHistory (records i) = history i := congrFun hmap i
      simp only [lower, added, Straight.instantiate, AdaptiveCircuit.tCount, hm] at *
      omega
  | measure w p ih =>
      have hm (outcome : Bool) : (Fin.lastCases outcome newHistory) ∘
          (Fin.lastCases (Fin.last start) (fun i => (records i).castSucc)) =
          Fin.lastCases outcome history := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        all_goals simp [Function.comp_def, ← hmap]
      have h0 := ih (start+1) _ (Fin.lastCases false history) (Fin.lastCases false newHistory) (hm false)
      have h1 := ih (start+1) _ (Fin.lastCases true history) (Fin.lastCases true newHistory) (hm true)
      simp only [lower, added, Straight.instantiate, AdaptiveCircuit.tCount] at *
      omega

end ShorECDLP.Entrant.AndGadget

namespace ShorECDLP.Entrant.AndGadget
open Quantum ShorECDLP.Challenge
noncomputable section
attribute [local irreducible] Quantum.run Quantum.applyGate Quantum.ket

private def prependBranch (outcome : Option Bool) (before : State →ₗ[ℂ] State)
    (branch : InstrumentBranch) : InstrumentBranch :=
  ⟨outcome.toList ++ branch.history, branch.kraus.comp before⟩
private theorem run_unitary (gs : Circuit) (tail : AdaptiveCircuit) :
    (AdaptiveCircuit.unitary gs tail).run = tail.run.map (prependBranch none (Quantum.run gs)) := rfl
private theorem run_measure (q : Wire) (a b : AdaptiveCircuit) :
    (AdaptiveCircuit.xMeasureReset q a b).run =
      a.run.map (prependBranch (some false) (xResetKraus q false)) ++
      b.run.map (prependBranch (some true) (xResetKraus q true)) := rfl

/-- Sum probability mass selected by an arbitrary transcript predicate. -/
def selectedMass (I : Instrument) (psi : State) (accept : List Bool → Bool) : ℝ :=
  (I.map (fun b => if accept b.history then normSq (b.kraus psi) else 0)).sum

theorem selectedMass_filter (I : Instrument) (psi : State) (accept : List Bool → Bool) :
    selectedMass I psi accept = Instrument.bornMass (I.filter (fun b => accept b.history)) psi := by
  induction I with
  | nil => rfl
  | cons b I ih =>
      cases hb : accept b.history <;> simp [selectedMass, Instrument.bornMass, hb] at * <;> exact ih

private theorem selectedMass_prefix (I : Instrument) (outcome : Option Bool)
    (before : State →ₗ[ℂ] State) (psi : State) (accept : List Bool → Bool) :
    selectedMass (I.map (prependBranch outcome before)) psi accept =
      selectedMass I (before psi) (fun xs => accept (outcome.toList ++ xs)) := by
  simp [selectedMass, prependBranch, List.map_map, Function.comp_def, LinearMap.comp_apply]

/-- Read the initial prefix followed by the newly emitted record. -/
def fullHistory {s : Nat} (e : Nat) (history : Fin s → Bool) (tail : List Bool) : Fin e → Bool :=
  fun i => (List.ofFn history ++ tail).getD i.val false

private theorem fullHistory_nil {s : Nat} (history : Fin s → Bool) :
    fullHistory s history List.nil = history := by
  funext i
  simp [fullHistory, i.isLt]

private theorem fullHistory_cons {s e : Nat} (history : Fin s → Bool) (b : Bool) (tail : List Bool) :
    fullHistory e history (b :: tail) = fullHistory e (Fin.lastCases b history) tail := by
  unfold fullHistory
  rw [List.ofFn_succ']
  simp only [Fin.lastCases_castSucc, Fin.lastCases_last, List.concat_eq_append,
    List.append_assoc, List.singleton_append]

/-- The recursive expectation is precisely the protected instrument Born mass. -/
theorem expectation_selectedMass {n s e : Nat} (read : ConstantBit n → Bool)
    (p : Straight n s e) (history : Fin s → Bool) (psi : State)
    (accept : (Fin e → Bool) → Bool) :
    expectation read p history psi accept =
      selectedMass (p.instantiate read history).run psi (fun xs => accept (fullHistory e history xs)) := by
  induction p generalizing psi with
  | done => simp [expectation, Straight.instantiate, AdaptiveCircuit.run,
      selectedMass, fullHistory_nil]
  | gate g p ih =>
      simp only [expectation, Straight.instantiate, run_unitary, selectedMass_prefix,
        Option.toList_none, List.nil_append]
      exact ih history _ accept
  | recordGate i v g p ih =>
      simp only [expectation, Straight.instantiate, run_unitary, selectedMass_prefix,
        Option.toList_none, List.nil_append]
      exact ih history _ accept
  | measure w p ih =>
      simp only [expectation, Straight.instantiate, run_measure]
      rw [show ∀ a b : Instrument, selectedMass (a ++ b) psi
          (fun xs => accept (fullHistory _ history xs)) =
          selectedMass a psi (fun xs => accept (fullHistory _ history xs)) +
          selectedMass b psi (fun xs => accept (fullHistory _ history xs)) by
        intros; simp [selectedMass]]
      simp only [selectedMass_prefix, Option.toList_some, List.singleton_append, fullHistory_cons]
      rw [ih, ih]

end
end ShorECDLP.Entrant.AndGadget

namespace ShorECDLP.Entrant.AndGadget
open Quantum ShorECDLP.Challenge ShorECDLP.Paper2607_13816.ChallengeMigration
noncomputable section

/-- Invalid old positions remain invalid after record remapping. -/
def redirect {e f : Nat} (records : Fin e → Fin f) (i : Nat) : Nat :=
  if h : i < e then (records ⟨i,h⟩).val else f

def redirectedLayout {e f : Nat} (records : Fin e → Fin f) (layout : DecodeLayout) : DecodeLayout where
  kind := layout.kind
  params := layout.params
  trials := layout.trials.map (fun t => ⟨t.left.map (redirect records), t.right.map (redirect records)⟩)
  trials_le := by simpa using layout.trials_le

private theorem redirect_get {e f : Nat} (records : Fin e → Fin f)
    (xs : List Bool) (hlen : xs.length = f) (i : Nat) :
    xs[redirect records i]? =
      (List.ofFn (fun j : Fin e => xs.getD (records j).val false))[i]? := by
  by_cases hi : i < e
  · have hr : (records ⟨i,hi⟩).val < xs.length := by simp [hlen]
    simp [redirect, hi, List.getElem?_eq_getElem hr]
  · have he : e ≤ i := by omega
    simp [redirect, hi, List.getElem?_eq_none (by omega : xs.length ≤ f)]

theorem readWord_redirect {e f : Nat} (records : Fin e → Fin f)
    (xs : List Bool) (hlen : xs.length = f) (positions : List Nat) :
    readWord xs (positions.map (redirect records)) =
      readWord (List.ofFn (fun j : Fin e => xs.getD (records j).val false)) positions := by
  induction positions with
  | nil => rfl
  | cons i positions ih => simp only [List.map_cons, readWord, redirect_get records xs hlen, ih]

theorem candidates_redirect {e f : Nat} (records : Fin e → Fin f) (layout : DecodeLayout)
    (xs : List Bool) (hlen : xs.length = f) :
    candidates (redirectedLayout records layout) xs =
      candidates layout (List.ofFn (fun j : Fin e => xs.getD (records j).val false)) := by
  simp only [candidates, redirectedLayout, List.flatMap_map]
  apply List.flatMap_congr
  intro t ht
  cases layout.kind <;>
    simp [decodeTrial, trialCandidates, Vector.toList_map, readWord_redirect records xs hlen]

theorem verified_redirect {e f : Nat} (records : Fin e → Fin f) (layout : DecodeLayout)
    (Q : Secp256k1.Point) (xs : List Bool) (hlen : xs.length = f) :
    verifiedCandidate (redirectedLayout records layout) Q xs =
      verifiedCandidate layout Q (List.ofFn (fun j : Fin e => xs.getD (records j).val false)) := by
  unfold verifiedCandidate
  rw [candidates_redirect records layout xs hlen]

private theorem ofFn_fullHistory {e : Nat} (xs : List Bool) (hlen : xs.length = e) :
    List.ofFn (fullHistory e Fin.elim0 xs) = xs := by
  subst e
  change List.ofFn (fun i : Fin xs.length => xs.getD i.val false) = xs
  simpa only [List.getD_eq_getElem xs false (Fin.isLt _)] using List.ofFn_getElem xs

/-- Bridge the finite-record predicate to the protected decoder and Born sum. -/
theorem expectation_verified {n e : Nat} (read : ConstantBit n → Bool)
    (p : Straight n 0 e) (layout : DecodeLayout) (Q : Secp256k1.Point) (psi : State) :
    expectation read p Fin.elim0 psi
      (fun h => (verifiedCandidate layout Q (List.ofFn h)).isSome) =
      Instrument.bornMass ((p.instantiate read Fin.elim0).run.filter
        (fun b => (verifiedCandidate layout Q b.history).isSome)) psi := by
  rw [expectation_selectedMass, ← selectedMass_filter (p.instantiate read Fin.elim0).run psi
    (fun xs => (verifiedCandidate layout Q xs).isSome)]
  unfold selectedMass
  congr 1
  apply List.map_congr_left
  intro b hb
  have hl : b.history.length = e := by
    simpa using straight_history_length p read Fin.elim0 b hb
  change (if (verifiedCandidate layout Q (List.ofFn (fullHistory e Fin.elim0 b.history))).isSome then _ else _) = _
  rw [ofFn_fullHistory b.history hl]

/-- The remapped protected decoder has exactly the original success probability. -/
theorem lower_verified {n e : Nat} (q : Wire) (p : Straight n 0 e)
    (read : ConstantBit n → Bool) (layout : DecodeLayout) (Q : Secp256k1.Point)
    (psi : State) (hf : Fresh q p) (hwf : p.WellFormed)
    (hpsi : SupportedOn (fun s => s q = false) psi) :
    Instrument.bornMass
      (((lower q p 0 Fin.elim0).program.instantiate read Fin.elim0).run.filter
        (fun b => (verifiedCandidate (redirectedLayout (lower q p 0 Fin.elim0).records layout)
          Q b.history).isSome)) psi =
    Instrument.bornMass ((p.instantiate read Fin.elim0).run.filter
      (fun b => (verifiedCandidate layout Q b.history).isSome)) psi := by
  rw [← expectation_verified, ← expectation_verified]
  have he : (fun h => (verifiedCandidate (redirectedLayout (lower q p 0 Fin.elim0).records layout)
        Q (List.ofFn h)).isSome) =
      (fun h => (verifiedCandidate layout Q (List.ofFn (h ∘ (lower q p 0 Fin.elim0).records))).isSome) := by
    funext h
    rw [verified_redirect _ _ _ _ List.length_ofFn]
    simp [Function.comp_def]
  rw [he]
  exact lower_expectation q p 0 Fin.elim0 read Fin.elim0 Fin.elim0 psi (fun h => (verifiedCandidate layout Q (List.ofFn h)).isSome)
    (by funext i; exact Fin.elim0 i) hf hwf hpsi

end
end ShorECDLP.Entrant.AndGadget

namespace ShorECDLP.Entrant.AndGadget
open Quantum ShorECDLP.Challenge

/-- Static support, including every optional gate slot. -/
def Within {n s e : Nat} (ws : List Wire) : Straight n s e → Prop
  | .done => True
  | .gate (.literal g) p => gateWires g ⊆ ws ∧ Within ws p
  | .gate (.whenBit _ _ g) p => gateWires g ⊆ ws ∧ Within ws p
  | .recordGate _ _ g p => gateWires g ⊆ ws ∧ Within ws p
  | .measure w p => w ∈ ws ∧ Within ws p

theorem Within.fresh {n s e : Nat} {ws : List Wire} {p : Straight n s e}
    (h : Within ws p) (q : Wire) (hq : q ∉ ws) : Fresh q p := by
  induction p with
  | done => trivial
  | gate g p ih =>
      cases g <;> exact ⟨fun hq' => hq (h.1 hq'), ih h.2⟩
  | recordGate i v g p ih => exact ⟨fun hq' => hq (h.1 hq'), ih h.2⟩
  | measure w p ih => exact ⟨fun he => hq (he ▸ h.1), ih h.2⟩

theorem Within.mono {n s e : Nat} {ws vs : List Wire} {p : Straight n s e}
    (h : Within ws p) (hs : ws ⊆ vs) : Within vs p := by
  induction p with
  | done => trivial
  | gate g p ih => cases g <;> exact ⟨h.1.trans hs, ih h.2⟩
  | recordGate i v g p ih => exact ⟨h.1.trans hs, ih h.2⟩
  | measure w p ih => exact ⟨hs h.1, ih h.2⟩

theorem Within.instantiate {n s e : Nat} {ws : List Wire} {p : Straight n s e}
    (h : Within ws p) (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    (p.instantiate read history).wires ⊆ ws := by
  induction p with
  | done => simp [Straight.instantiate, AdaptiveCircuit.wires]
  | gate g p ih =>
      cases g with
      | literal g => simpa [Straight.instantiate, TemplateGate.instantiate,
          AdaptiveCircuit.wires, circuitWires] using List.append_subset.mpr ⟨h.1, ih h.2 history⟩
      | whenBit r v g =>
          simp only [Straight.instantiate, TemplateGate.instantiate, AdaptiveCircuit.wires]
          split
          · simpa [circuitWires] using List.append_subset.mpr ⟨h.1, ih h.2 history⟩
          · simpa [circuitWires] using ih h.2 history
  | recordGate i v g p ih =>
      simp only [Straight.instantiate, AdaptiveCircuit.wires]
      split
      · simpa [circuitWires] using List.append_subset.mpr ⟨h.1, ih h.2 history⟩
      · simpa [circuitWires] using ih h.2 history
  | measure w p ih =>
      exact List.cons_subset.mpr ⟨h.1, List.append_subset.mpr ⟨ih h.2 _, ih h.2 _⟩⟩

theorem within_of_instantiate {n s e : Nat} (p : Straight n s e) (ws : List Wire)
    (h : ∀ read history, (p.instantiate read history).wires ⊆ ws) : Within ws p := by
  induction p with
  | done => trivial
  | gate g p ih =>
      cases g with
      | literal g =>
          constructor
          · intro w hw
            exact h (fun _ => false) (fun _ => false)
              (by simp [Straight.instantiate, TemplateGate.instantiate, AdaptiveCircuit.wires, circuitWires, hw])
          · apply ih
            intro read history w hw
            exact h read history (List.mem_append_right _ hw)
      | whenBit r v g =>
          constructor
          · intro w hw
            exact h (fun _ => v) (fun _ => false)
              (by simp [Straight.instantiate, TemplateGate.instantiate, AdaptiveCircuit.wires, circuitWires, hw])
          · apply ih
            intro read history w hw
            exact h read history (List.mem_append_right _ hw)
  | recordGate i v g p ih =>
      constructor
      · intro w hw
        exact h (fun _ => false) (fun _ => v)
          (by simp [Straight.instantiate, AdaptiveCircuit.wires, circuitWires, hw])
      · apply ih
        intro read history w hw
        exact h read history (List.mem_append_right _ hw)
  | @measure s e w p ih =>
      constructor
      · exact h (fun _ => false) (fun _ => false) (List.mem_cons_self)
      · apply ih
        intro read history v hv
        let before : Fin s → Bool := fun i => history i.castSucc
        have he : Fin.lastCases (history (Fin.last s)) before = history := by
          funext i
          refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [before]
        rw [← he] at hv
        apply h read before
        cases hb : history (Fin.last s) <;>
          simp only [hb] at hv <;>
          simp only [Straight.instantiate, AdaptiveCircuit.wires, List.mem_cons, List.mem_append]
        · exact Or.inr (Or.inl hv)
        · exact Or.inr (Or.inr hv)

theorem within_literals {n s e : Nat} (ws : List Wire) (gs : Circuit) (p : Straight n s e)
    (hg : circuitWires gs ⊆ ws) (hp : Within ws p) : Within ws (literals gs p) := by
  induction gs with
  | nil => exact hp
  | cons g gs ih =>
      have hh : gateWires g ⊆ ws ∧ circuitWires gs ⊆ ws := by
        simpa only [circuitWires, List.flatMap_cons, List.append_subset] using hg
      exact ⟨hh.1, ih hh.2⟩

theorem lower_within {n s e : Nat} (q : Wire) (p : Straight n s e) (ws : List Wire)
    (hp : Within ws p) (start : Nat) (records : Fin s → Fin start) :
    Within (q :: ws) (lower q p start records).program := by
  induction p generalizing start with
  | done => trivial
  | gate g p ih =>
      cases g with
      | literal g =>
          cases g with
          | CCX a b t =>
              have hs : a ∈ ws ∧ b ∈ ws ∧ t ∈ ws := by simpa [gateWires] using hp.1
              apply within_literals
              · simp [andCompute, parityPhase, xorPhase, circuitWires, gateWires,
                  List.cons_subset, hs.1, hs.2.1, hs.2.2]
              · exact ⟨by simp, by simp [gateWires, hs.2.1],
                  by simp [gateWires, hs.1, hs.2.1], by simp [gateWires, hs.2.1], ih hp.2 _ _⟩
          | X t | H t | CX a t | P dir k t =>
              exact ⟨hp.1.trans (by simp), ih hp.2 _ _⟩
      | whenBit r v g => exact ⟨hp.1.trans (by simp), ih hp.2 _ _⟩
  | recordGate i v g p ih => exact ⟨hp.1.trans (by simp), ih hp.2 _ _⟩
  | measure w p ih => exact ⟨List.mem_cons_of_mem _ hp.1, ih hp.2 _ _⟩

end ShorECDLP.Entrant.AndGadget

namespace ShorECDLP.Entrant.AndGadget
open Quantum ShorECDLP.Challenge
noncomputable section

/-- Package the transformed straight program with unchanged public coefficients. -/
def lowerEntry (q : Wire) (entry : StraightEntry) : StraightEntry where
  coefficients := entry.coefficients
  finalCursor := (lower q entry.program 0 Fin.elim0).finish
  program := (lower q entry.program 0 Fin.elim0).program

def lowerLayout (q : Wire) (entry : StraightEntry) (layout : DecodeLayout) : DecodeLayout :=
  redirectedLayout (lower q entry.program 0 Fin.elim0).records layout

/-- Certificate transport uses only a proved count of eligible literal Toffolis. -/
theorem lower_certificate (limits : Limits) (layout : DecodeLayout) (entry : StraightEntry)
    (bounds newBounds : Bounds) (q : Wire) (ws : List Wire)
    (cert : Certificate limits layout entry bounds)
    (hs : Within ws entry.program) (hq : q ∉ ws)
    (hslots : entry.program.gateSlots + 18 * added entry.program ≤ limits.gateSlots)
    (hrecords : entry.finalCursor + added entry.program ≤ limits.measurements)
    (hqubits : ws.length + 1 ≤ newBounds.qubits)
    (ht : bounds.tModel ≤ newBounds.tModel + 2 * added entry.program)
    (hm : entry.finalCursor + added entry.program ≤ newBounds.measurements) :
    Certificate limits (lowerLayout q entry layout) (lowerEntry q entry) newBounds where
  gateBudget := by simpa only [lowerEntry, lower_slots] using hslots
  recordBudget := by
    have h := lower_finish q entry.program 0 Fin.elim0
    simp only [Nat.add_zero, Nat.zero_add] at h
    simpa only [lowerEntry] using h.le.trans hrecords
  tableBudget := cert.tableBudget
  candidateBudget := by simpa [lowerLayout, redirectedLayout] using cert.candidateBudget
  wellFormed := lower_wellFormed q entry.program 0 Fin.elim0 (hs.fresh q hq) cert.wellFormed
  resources := by
    intro Q
    have hsup := (lower_within q entry.program ws hs 0 Fin.elim0).instantiate
      (readConstant entry.coefficients.get Q) Fin.elim0
    have hc : (((lowerEntry q entry).instantiate Q).wires.dedup.toFinset).card ≤ (q :: ws).length := by
      apply (Finset.card_le_card ?_).trans (List.toFinset_card_le (q :: ws))
      intro w hw
      apply List.mem_toFinset.mpr
      apply hsup
      simpa only [List.mem_toFinset, List.mem_dedup] using hw
    have hqc : ((lowerEntry q entry).instantiate Q).qubitCount ≤ newBounds.qubits := by
      rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
      exact hc.trans hqubits
    have htc := lower_t q entry.program 0 Fin.elim0 (readConstant entry.coefficients.get Q)
      Fin.elim0 Fin.elim0 (by funext i; exact Fin.elim0 i)
    have hto := (cert.resources Q).2.1
    have hmc := (lower q entry.program 0 Fin.elim0).program.measurementCount
      (readConstant entry.coefficients.get Q) Fin.elim0
    have hfinish := lower_finish q entry.program 0 Fin.elim0
    refine ⟨hqc, ?_, ?_⟩
    · change ((lower q entry.program 0 Fin.elim0).program.instantiate
        (readConstant entry.coefficients.get Q) Fin.elim0).tCount ≤ newBounds.tModel
      change (entry.program.instantiate (readConstant entry.coefficients.get Q) Fin.elim0).tCount ≤ bounds.tModel at hto
      omega
    · change ((lower q entry.program 0 Fin.elim0).program.instantiate
        (readConstant entry.coefficients.get Q) Fin.elim0).measurementCount ≤ newBounds.measurements
      omega
  success := by
    intro Q d hn hd
    change 99 / 100 ≤ Instrument.bornMass
      (((lower q entry.program 0 Fin.elim0).program.instantiate
        (readConstant entry.coefficients.get Q) Fin.elim0).run.filter
        (fun b => (verifiedCandidate (redirectedLayout (lower q entry.program 0 Fin.elim0).records layout)
          Q b.history).isSome)) (ket zeroBasisState)
    rw [lower_verified q entry.program _ layout Q _ (hs.fresh q hq) cert.wellFormed
      (supportedOn_ket _ _ rfl)]
    exact cert.success Q d hn hd

end
end ShorECDLP.Entrant.AndGadget
end

section
namespace ShorECDLP.Entrant.AndGadget
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

theorem added_cast {n s e f} (p : Straight n s e) (h : e=f) :
    added (ChallengeMigration.castFinish h p) = added p := by subst f; rfl

theorem added_relabel {n s e} (p : Straight n s e) (f : Wire ≃ Wire) :
    added (relabelStraight f p) = added p := by
  induction p with
  | done => rfl
  | gate g p ih => cases g with
    | literal g => cases g <;> simp_all [relabelStraight, relabelTemplateGate, Gate.relabel, added]
    | whenBit r v g => simp_all [relabelStraight, relabelTemplateGate, added]
  | recordGate => simp_all [relabelStraight, added]
  | measure => simp_all [relabelStraight, added]

theorem added_reindex {n m s e} (p : Straight n s e) (f : Fin n → Fin m) :
    added (reindexStraight f p) = added p := by
  induction p with
  | done => rfl
  | gate g p ih => cases g with
    | literal g => cases g <;> simp_all [reindexStraight, reindexGate, added]
    | whenBit r v g => simp_all [reindexStraight, reindexGate, added]
  | recordGate => simp_all [reindexStraight, added]
  | measure => simp_all [reindexStraight, added]

theorem added_shift {n s e} (p : Straight n s e) (offset : Nat) :
    added (shiftStraight offset p) = added p := by
  induction p with
  | done => rfl
  | gate g p ih => cases g with
    | literal g => cases g <;> simp_all [shiftStraight, added]
    | whenBit r v g => simp_all [shiftStraight, added]
  | recordGate => simp_all [shiftStraight, added]
  | measure => simp_all [shiftStraight, added, added_cast]

def ccxCount : Circuit → Nat
  | [] => 0
  | .CCX _ _ _ :: gs => Nat.succ (ccxCount gs)
  | _ :: gs => ccxCount gs

theorem added_literal {n s} (gs : Circuit) :
    added (literalProgram gs : Straight n s s) = ccxCount gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => cases g <;> simp_all [literalProgram, gateProgram, added, ccxCount, Nat.add_comm]

def AtLeast {n s e} (p : Straight n s e) (count : Nat) : Prop := count ≤ added p
namespace AtLeast
 theorem zero {n s e} (p : Straight n s e) : AtLeast p 0 := Nat.zero_le _
 theorem castCount {n s e d f} {p : Straight n s e} (hp : AtLeast p d) (h : d=f) : AtLeast p f := h ▸ hp
 theorem castFinish {n s e f d} {p : Straight n s e} (hp : AtLeast p d) (h : e=f) :
     AtLeast (ChallengeMigration.castFinish h p) d := by simpa only [AtLeast, added_cast] using hp
 theorem append {n s m e d f} {p : Straight n s m} {q : Straight n m e}
     (hp : AtLeast p d) (hq : AtLeast q f) : AtLeast (p.append q) (d+f) := by
   unfold AtLeast at *; rw [added_append]; omega
 theorem appendCompiled {n start d f}
     (p : (count : Nat) × Straight n start (start+count))
     (q : (count : Nat) × Straight n (start+p.1) (start+p.1+count))
     (hp : AtLeast p.2 d) (hq : AtLeast q.2 f) :
     AtLeast (ChallengeMigration.appendCompiled p q).2 (d+f) := by
   unfold ChallengeMigration.appendCompiled
   exact (hp.append hq).castFinish _
 theorem appendLiteral {n start d}
     (p : (count : Nat) × Straight n start (start+count)) (gs : Circuit)
     (hp : AtLeast p.2 d) : AtLeast (ChallengeMigration.appendLiteral p gs).2 d :=
   (appendCompiled p ⟨0,literalProgram gs⟩ hp (zero _)).castCount (Nat.add_zero d)
 theorem sequenceCons {n start d f} (p : FixedSegment n) (ps : List (FixedSegment n))
     (hp : AtLeast (p start).2 d)
     (hq : AtLeast (sequenceProgram n ps (start+(p start).1)).2 f) :
     AtLeast (sequenceProgram n (p::ps) start).2 (d+f) := appendCompiled (p start) (sequenceProgram n ps (start+(p start).1)) hp hq
 theorem surroundCompiled {n start d} (before after : Circuit)
     (p : (count : Nat) × Straight n start (start+count)) (hp : AtLeast p.2 d) :
     AtLeast (ChallengeMigration.surroundCompiled before after p).2 d := by
   unfold ChallengeMigration.surroundCompiled ChallengeMigration.prependCompiled
   exact ((zero (literalProgram before)).append
     ((appendCompiled p ⟨0,literalProgram after⟩ hp (zero _)).castCount (Nat.add_zero d))).castCount (Nat.zero_add d)
 theorem relabel {n s e d} {p : Straight n s e} (hp : AtLeast p d) (f : Wire ≃ Wire) :
     AtLeast (relabelStraight f p) d := by simpa [AtLeast, added_relabel] using hp
 theorem reindex {n m s e d} {p : Straight n s e} (hp : AtLeast p d) (f : Fin n → Fin m) :
     AtLeast (reindexStraight f p) d := by simpa [AtLeast, added_reindex] using hp
 theorem shift {n s e d} {p : Straight n s e} (hp : AtLeast p d) (offset : Nat) :
     AtLeast (shiftStraight offset p) d := by simpa [AtLeast, added_shift] using hp
end AtLeast

attribute [local irreducible] sequenceProgram appendCompiled literalProgram
 remainderBlockProgram coefficientBlockProgram phaseProgram hProgram intervalProgram coefficientProgram
 preprocessProgram productionParityProgram measuredStepProgram measuredScheduleProgram
 measuredEEAForwardProgram measuredForwardWrapperProgram multiplyWorkProgram divisionAfterResetProgram
 divisionProgram zeroDivisionProgram fieldLookupAddProgram signedFieldProgram pointSquareProgram
 zeroMultiplicationProgram xNegateProgram coordinateProgram


theorem ccxCount_primitive (gs : Circuit) :
    ccxCount gs = (primitiveResources (.unitary gs .done)).toffoli := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    cases g <;> simp_all [ccxCount, primitiveResources, gidneyToffoliCount, gidneyGateCount, Nat.add_comm]

theorem aCount (n s : Nat) : AtLeast (literalProgram (blockAForward indexedStepProductionRegisters) : Straight n s s) 906 := by
  rw [AtLeast, added_literal, ccxCount_primitive]
  rw [blockAForward259_primitive _ indexedStepProduction_layout.terminalPadding
    indexedStepProduction_layout.preShift indexedStepProduction_layout.work2_length
    (by decide) (by decide) (by decide)]

theorem fCount (n s : Nat) : AtLeast (literalProgram (blockFForward indexedStepProductionRegisters) : Straight n s s) 566 := by
  rw [AtLeast, added_literal, ccxCount_primitive]
  unfold blockFForward
  rw [postShiftUnitary259_primitive _ indexedStepProduction_layout.postShift
    indexedStepProduction_layout.work2_length (by decide)]

theorem stepCount (n start T : Nat) :
    AtLeast (measuredStepProgram n start indexedStepProductionRegisters 256 T).2 1472 := by
  unfold measuredStepProgram measuredStepSegments
  refine (AtLeast.sequenceCons (d := 906) (f := 566) _ _ (aCount n _) ?_)
  refine (AtLeast.sequenceCons (d := 0) (f := 566) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 0) (f := 566) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 0) (f := 566) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  exact (AtLeast.sequenceCons (d := 566) (f := 0) _ _ (fCount n _) (AtLeast.zero _)).castCount (by omega)

theorem scheduleCount (n : Nat) (count first start : Nat) :
    AtLeast (measuredScheduleProgram n indexedStepProductionRegisters 256 count first start).2 (count*1472) := by
  induction count generalizing first start with
  | zero => exact AtLeast.zero _
  | succ count ih =>
    simp only [measuredScheduleProgram]
    exact (AtLeast.appendCompiled _ _ (stepCount n start first) (ih (first+1) _)).castCount (by omega)

theorem wrapperCount (n start : Nat) :
    AtLeast (measuredForwardWrapperProgram n start).2 2384640 := by
  unfold measuredForwardWrapperProgram measuredForwardWrapperSegments
  refine (AtLeast.sequenceCons (d := 0) (f := 2384640) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  exact (AtLeast.sequenceCons (d := 2384640) (f := 0) _ _ (show AtLeast (measuredEEAForwardProgram n _ indexedStepProductionRegisters).2 2384640 from by unfold measuredEEAForwardProgram; exact scheduleCount n 1620 1 _) (AtLeast.zero _)).castCount (by omega)

theorem divisionCount (n start : Nat) : AtLeast (divisionProgram n start).2 2384640 := by
  unfold divisionProgram
  refine (AtLeast.appendCompiled (d := 2384640) (f := 0) _ _ ?_ (AtLeast.zero _)).castCount (by omega)
  exact (AtLeast.appendCompiled _ _ (wrapperCount n start) (AtLeast.zero _)).castCount (by omega)

theorem zeroDivisionCount (n start : Nat) : AtLeast (zeroDivisionProgram n start).2 2384640 := by
  unfold zeroDivisionProgram
  exact AtLeast.surroundCompiled _ _ _ (divisionCount n start)

theorem coordinateCount (start : Nat) : AtLeast (coordinateProgram start).2 2384640 := by
  unfold coordinateProgram coordinateSegments
  refine (AtLeast.sequenceCons (d := 0) (f := 2384640) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 0) (f := 2384640) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  exact (AtLeast.sequenceCons _ _ (zeroDivisionCount 32768 _) (AtLeast.zero _)).castCount (by omega)
end
end ShorECDLP.Entrant.AndGadget
end

section
namespace ShorECDLP.Entrant.AndGadget
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 3000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

def residue {n s e : Nat} : Straight n s e → Nat
  | .done => 0
  | .gate (.literal g) p => primitivePhaseCost g + residue p
  | .gate (.whenBit _ _ g) p => tCost g + residue p
  | .recordGate _ _ g p => tCost g + residue p
  | .measure _ p => residue p

@[simp] theorem residue_done {n s : Nat} : residue (Straight.done : Straight n s s) = 0 := rfl

theorem residue_t {n s e} (p : Straight n s e) (read : ConstantBit n → Bool)
    (history : Fin s → Bool) :
    (p.instantiate read history).tCount ≤ 7 * added p + residue p := by
  induction p with
  | done => simp [Straight.instantiate, AdaptiveCircuit.tCount, added, residue]
  | gate g p ih =>
    have h := ih history
    cases g with
    | literal g => cases g <;>
        simp only [Straight.instantiate, TemplateGate.instantiate, AdaptiveCircuit.tCount,
          tCount, tCost, primitivePhaseCost, added, residue, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at * <;> omega
    | whenBit r v g =>
        simp only [Straight.instantiate, TemplateGate.instantiate, AdaptiveCircuit.tCount, added, residue]
        split <;> simp only [tCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] <;> omega
  | recordGate i v g p ih =>
      have h := ih history
      simp only [Straight.instantiate, AdaptiveCircuit.tCount, added, residue]
      split <;> simp only [tCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] <;> omega
  | measure w p ih =>
      have hf := ih (Fin.lastCases false history)
      have ht := ih (Fin.lastCases true history)
      simp only [Straight.instantiate, AdaptiveCircuit.tCount, added, residue]
      omega

theorem residue_append {n s m e} (p : Straight n s m) (q : Straight n m e) :
    residue (p.append q) = residue p + residue q := by
  induction p with
  | done => simp [Straight.append, residue]
  | gate g p ih => cases g <;> simp [Straight.append, residue, ih, Nat.add_assoc]
  | recordGate => simp_all [Straight.append, residue, Nat.add_assoc]
  | measure => simp_all [Straight.append, residue]

theorem residue_cast {n s e f} (p : Straight n s e) (h : e=f) :
    residue (castFinish h p) = residue p := by subst f; rfl

theorem residue_literal {n s} (gs : Circuit) :
    residue (literalProgram gs : Straight n s s) = (gs.map primitivePhaseCost).sum := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp_all [literalProgram, gateProgram, residue]

theorem residue_literal_HPFree {n s} (gs : Circuit) (h : Classical.HPFree gs) :
    residue (literalProgram gs : Straight n s s) = 0 := by
  rw [residue_literal, primitivePhaseCost_of_HPFree gs h]

theorem residue_recordGates {n s e} (i : Fin s) (gs : Circuit) (p : Straight n s e) :
    residue (recordGates i gs p) = tCount gs + residue p := by
  induction gs with
  | nil => simp [recordGates, tCount]
  | cons g gs ih => simp [recordGates, residue, tCount, ih, Nat.add_assoc]

@[simp] theorem residue_andErase (n s a b t : Nat) :
    residue (andEraseProgram n s a b t) = 0 := by
  simp [andEraseProgram, residue, residue_recordGates, controlledZ, tCount, tCost]

@[simp] theorem residue_compiled {n start}
    (p : (count : Nat) × Straight n start (start+count))
    (q : (count : Nat) × Straight n (start+p.1) (start+p.1+count)) :
    residue (appendCompiled p q).2 = residue p.2 + residue q.2 := by
  simp only [appendCompiled, residue_cast, residue_append]

@[simp] theorem residue_prepend {n start} (gs : Circuit)
    (p : (count : Nat) × Straight n start (start+count)) :
    residue (prependCompiled gs p).2 = (gs.map primitivePhaseCost).sum + residue p.2 := by
  simp only [prependCompiled, residue_append, residue_literal]

@[simp] theorem residue_surround {n start} (gs hs : Circuit)
    (p : (count : Nat) × Straight n start (start+count)) :
    residue (surroundCompiled gs hs p).2 =
      (gs.map primitivePhaseCost).sum + residue p.2 + (hs.map primitivePhaseCost).sum := by
  simp [surroundCompiled, residue_literal, Nat.add_assoc]

@[simp] theorem residue_vchainTail (n : Nat) (controls : List Wire) (acc target : Wire)
    (scratch : List Wire) (start : Nat) :
    residue (vchainTailProgram n controls acc target scratch start).2 = 0 := by
  induction controls generalizing acc scratch start with
  | nil => rfl
  | cons control controls ih =>
    cases controls with
    | nil => simp [vchainTailProgram, residue_literal, primitivePhaseCost]
    | cons next controls =>
      cases scratch with
      | nil => rfl
      | cons work scratch => simp only [vchainTailProgram, residue_prepend, residue_compiled,
          ih, residue_andErase]; rfl

@[simp] theorem residue_vchain (n start : Nat) (controls : List Wire) (target : Wire) (scratch : List Wire) :
    residue (vchainProgram n start controls target scratch).2 = 0 := by
  unfold vchainProgram
  split <;> simp_all [residue, residue_literal, primitivePhaseCost]

@[simp] theorem residue_rippleMaj (n start control target addend carry scratch : Nat) :
    residue (rippleMajProgram n start control target addend carry scratch).2 = 0 := by
  simp [rippleMajProgram, residue_literal, primitivePhaseCost]

@[simp] theorem residue_rippleUma (n start control target addend carry scratch : Nat) :
    residue (rippleUmaProgram n start control target addend carry scratch).2 = 0 := by
  simp [rippleUmaProgram, residue_literal, primitivePhaseCost]

@[simp] theorem residue_rippleMajInv (n start control target addend carry scratch : Nat) :
    residue (rippleMajInvProgram n start control target addend carry scratch).2 = 0 := by
  simp [rippleMajInvProgram, residue_literal, primitivePhaseCost]

@[simp] theorem residue_rippleUmaInv (n start control target addend carry scratch : Nat) :
    residue (rippleUmaInvProgram n start control target addend carry scratch).2 = 0 := by
  simp [rippleUmaInvProgram, residue_literal, primitivePhaseCost]

@[simp] theorem residue_rippleFirst (n start : Nat) (mode : RippleMode) (control target addend carry scratch : Wire) :
    residue (rippleFirstProgram n start mode control target addend carry scratch).2 = 0 := by
  cases mode <;> simp [rippleFirstProgram]

@[simp] theorem residue_rippleSecond (n start : Nat) (mode : RippleMode) (control target addend carry scratch : Wire) :
    residue (rippleSecondProgram n start mode control target addend carry scratch).2 = 0 := by
  cases mode <;> simp [rippleSecondProgram]

@[simp] theorem residue_zeroErase (n start a b w : Nat) :
    residue (zeroEraseProgram n start a b w).2 = 0 := by
  simp [zeroEraseProgram, residue_literal, primitivePhaseCost]

@[simp] theorem residue_dualErase (n start a i x b j y : Nat) :
    residue (dualEraseProgram n start a i x b j y).2 = 0 := by
  simp [dualEraseProgram]

def compiledResidue {n start} (p : (count : Nat) × Straight n start (start+count)) : Nat := residue p.2

@[simp] theorem residue_ite {n start} (c : Prop) [Decidable c]
    (p q : (count : Nat) × Straight n start (start+count)) :
    residue (if c then p else q).2 = if c then residue p.2 else residue q.2 := by
  change compiledResidue (if c then p else q) = _
  split <;> rfl


theorem residue_unary (n : Nat) (order : UnaryOrder)
    (leaf : (label : Nat) → (control : Wire) → (start : Nat) →
      (count : Nat) × Straight n start (start+count))
    (hl : ∀ label control start, residue (leaf label control start).2 = 0)
    (tree : UnaryActionTree) (q : Wire) (path : List Wire) (start : Nat) :
    residue (unaryProgram n order leaf tree q path start).2 = 0 := by
  change compiledResidue (unaryProgram n order leaf tree q path start) = 0
  induction tree generalizing q path start with
  | leaf label => rw [unaryProgram.eq_1]; exact hl label q start
  | node bit zero one ihz iho =>
    cases path with
    | nil => rw [unaryProgram.eq_3]; rfl
    | cons p ps =>
      rw [unaryProgram.eq_2]
      simp only [compiledResidue] at ihz iho
      cases order <;>
        simp [compiledResidue, ihz, iho, computeZeroAnd, primitivePhaseCost]

theorem residue_dual (n : Nat) (order : UnaryOrder)
    (leaf : (label : Nat) → (a b : Wire) → (start : Nat) →
      (count : Nat) × Straight n start (start+count))
    (hl : ∀ label a b start, residue (leaf label a b start).2 = 0)
    (tree : DualUnaryActionTree) (a b : Wire) (xs ys : List Wire) (start : Nat) :
    residue (dualProgram n order leaf tree a b xs ys start).2 = 0 := by
  change compiledResidue (dualProgram n order leaf tree a b xs ys start) = 0
  induction tree generalizing a b xs ys start with
  | leaf label => rw [dualProgram.eq_1]; exact hl label a b start
  | node i j zero one ihz iho =>
    cases xs with
    | nil => rw [dualProgram.eq_3] <;> simp [compiledResidue, residue]
    | cons x xs => cases ys with
      | nil => rw [dualProgram.eq_3] <;> simp [compiledResidue, residue]
      | cons y ys =>
        rw [dualProgram.eq_2]
        simp only [compiledResidue] at ihz iho
        cases order <;>
          simp [compiledResidue, ihz, iho, computeZeroAnd, primitivePhaseCost]

@[simp] theorem phaseCost_zeroMask (ws : List Wire) (v : Nat) :
    ((zeroMask ws v).map primitivePhaseCost).sum = 0 :=
  primitivePhaseCost_of_HPFree _ (zeroMask_HPFree ws v)

@[simp] theorem phaseCost_endpointLeafToggle (top : Bool) (label : Nat) (a b c : Wire) :
    ((endpointLeafToggle top label a b c).map primitivePhaseCost).sum = 0 :=
  primitivePhaseCost_of_HPFree _ (endpointLeafToggle_HPFree top label a b c)

@[simp] theorem residue_equality (n start : Nat) (register : List Wire) (value : Nat) (flag : Wire)
    (scratch : List Wire) : residue (equalityProgram n start register value flag scratch).2 = 0 := by
  simp [equalityProgram, residue_literal]

@[simp] theorem residue_toggleEquality (n start : Nat) (root : Wire) (register : List Wire) (value : Nat)
    (acc flag : Wire) (scratch : List Wire) :
    residue (toggleEqualityProgram n start root register value acc flag scratch).2 = 0 := by
  simp [toggleEqualityProgram, primitivePhaseCost]

@[simp] theorem residue_intervalFirst (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc target addend carry scratch : Wire) (label : Nat)
    (rightControl leftControl : Wire) :
    residue (intervalFirstProgram n start mode topSpecial rightTop leftTop acc target addend carry scratch label rightControl leftControl).2 = 0 := by
  simp [intervalFirstProgram, residue_literal]

@[simp] theorem residue_topFirst (n start : Nat) (mode : RippleMode) (value : Nat)
    (rightRegister leftRegister : List Wire) (acc target addend carry work flag : Wire)
    (scratch : List Wire) (rightRoot leftRoot : Wire) :
    residue (topFirstProgram n start mode value rightRegister leftRegister acc target addend carry work flag scratch rightRoot leftRoot).2 = 0 := by
  simp [topFirstProgram]

@[simp] theorem residue_traversalFirst (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc carry scratch : Wire) (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire) (rightPaths leftPaths : List Wire) :
    residue (traversalFirstProgram n start mode topSpecial rightTop leftTop acc carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).2 = 0 := by
  unfold traversalFirstProgram
  apply residue_dual
  intros
  apply residue_intervalFirst

@[simp] theorem residue_coefficientFirst (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (label : Nat) (control : Wire) :
    residue (coefficientFirstProgram n start r k K mode target label control).2 = 0 := by
  simp [coefficientFirstProgram, residue_literal, primitivePhaseCost]

@[simp] theorem residue_intervalSecond (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc target addend carry scratch : Wire) (label : Nat)
    (rightControl leftControl : Wire) :
    residue (intervalSecondProgram n start mode topSpecial rightTop leftTop acc target addend carry scratch label rightControl leftControl).2 = 0 := by
  simp [intervalSecondProgram, residue_literal]

@[simp] theorem residue_topSecond (n start : Nat) (mode : RippleMode) (value : Nat)
    (rightRegister leftRegister : List Wire) (acc target addend carry work flag : Wire)
    (scratch : List Wire) (rightRoot leftRoot : Wire) :
    residue (topSecondProgram n start mode value rightRegister leftRegister acc target addend carry work flag scratch rightRoot leftRoot).2 = 0 := by
  simp [topSecondProgram]

@[simp] theorem residue_traversalSecond (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc carry scratch : Wire) (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire) (rightPaths leftPaths : List Wire) :
    residue (traversalSecondProgram n start mode topSpecial rightTop leftTop acc carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).2 = 0 := by
  unfold traversalSecondProgram
  apply residue_dual
  intros
  apply residue_intervalSecond

@[simp] theorem residue_coefficientSecond (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (label : Nat) (control : Wire) :
    residue (coefficientSecondProgram n start r k K mode target label control).2 = 0 := by
  simp [coefficientSecondProgram, residue_literal, primitivePhaseCost]

@[simp] theorem residue_coefficient (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget) :
    residue (coefficientProgram n start r k K mode signUpdate target).2 = 0 := by
  have hl : ∀ label control start, residue (coefficientFirstProgram n start r k K mode target label control).2 = 0 := by simp
  have hr : ∀ label control start, residue (coefficientSecondProgram n start r k K mode target label control).2 = 0 := by simp
  cases signUpdate <;> simp [coefficientProgram, residue_unary _ _ _ hl, residue_unary _ _ _ hr,
    residue_literal, coefficientPrefixSignCircuit, primitivePhaseCost]

@[simp] theorem residue_coefficientInverse (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget) :
    residue (coefficientInverseProgram n start r k K mode signUpdate target).2 = 0 := by
  simp [coefficientInverseProgram]

attribute [local simp] primitivePhaseCost_of_HPFree

@[simp] theorem residue_intervalTopFirst (n start : Nat) (r : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (target : IntervalTarget) :
    residue (intervalTopFirstProgram n start r k K mode target).2 = 0 := by
  change compiledResidue (intervalTopFirstProgram n start r k K mode target) = 0
  unfold intervalTopFirstProgram
  split <;> simp [compiledResidue, residue_literal]
@[simp] theorem residue_intervalTopSecond (n start : Nat) (r : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (target : IntervalTarget) :
    residue (intervalTopSecondProgram n start r k K mode target).2 = 0 := by
  change compiledResidue (intervalTopSecondProgram n start r k K mode target) = 0
  unfold intervalTopSecondProgram
  split <;> simp [compiledResidue, residue_literal]

@[simp] theorem residue_interval (n start : Nat) (r : IntervalRegisters) (width k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget) :
    residue (intervalProgram n start r width k K mode signUpdate target).2 = 0 := by
  cases signUpdate <;> simp [intervalProgram, residue_literal, intervalSignUpdate, primitivePhaseCost]

@[simp] theorem residue_intervalInverse (n start : Nat) (r : IntervalRegisters) (width k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget) :
    residue (intervalInverseProgram n start r width k K mode signUpdate target).2 = 0 := by
  simp [intervalInverseProgram]

theorem residue_sequence (n : Nat) (ps : List (FixedSegment n))
    (hp : ∀ p ∈ ps, ∀ start, residue (p start).2 = 0) (start : Nat) :
    residue (sequenceProgram n ps start).2 = 0 := by
  induction ps generalizing start with
  | nil => rfl
  | cons p ps ih =>
    simp only [sequenceProgram, residue_compiled]
    rw [hp p (by simp), ih (by intro q hq; exact hp q (by simp [hq]))]

theorem residue_phaseSegments (n start : Nat) (r : PhaseUpdateRegisters) (shift : Wire)
    (core : Circuit) (hc : (core.map primitivePhaseCost).sum = 0) :
    residue (sequenceProgram n (phaseSegments n r shift core) start).2 = 0 := by
  apply residue_sequence
  intro p hp s
  simp only [phaseSegments, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h | h | h | h | h | h | h | h | h | h | h <;>
    subst p <;> simp [residue_literal, primitivePhaseCost, hc]

@[simp] theorem residue_phase (n start : Nat) (r : PhaseUpdateRegisters) (shift : Wire) :
    residue (phaseProgram n start r shift).2 = 0 := by
  unfold phaseProgram
  apply residue_phaseSegments
  simp [phaseCoreGates, primitivePhaseCost]

@[simp] theorem residue_phaseInverse (n start : Nat) (r : PhaseUpdateRegisters) (shift : Wire) :
    residue (phaseInverseProgram n start r shift).2 = 0 := by
  unfold phaseInverseProgram
  apply residue_phaseSegments
  simp [phaseInverseCoreGates, primitivePhaseCost]

private theorem blockB2_classical (r : IndexedStepRegisters) : Classical.HPFree (blockB2 r) := by
  have h := indexedStepUnitary_HPFree r 256 1
  simp only [indexedStepUnitary, Classical.hpFree_append] at h
  have hb : Classical.HPFree (blockBForward r 256 (certifiedActiveWindows 256 1).remainder) := by tauto
  simp only [blockBForward, Classical.hpFree_append] at hb
  tauto

@[simp] theorem residue_remainderBlock (n start : Nat) (r : IndexedStepRegisters)
    (width : Nat) (w : ActiveWindow) :
    residue (remainderBlockProgram n start r width w).2 = 0 := by
  unfold remainderBlockProgram remainderBlockSegments
  simp [sequenceProgram, residue_literal, primitivePhaseCost, blockB2_classical]

@[simp] theorem residue_coefficientBlock (n start : Nat) (r : IndexedStepRegisters)
    (width : Nat) (w : ActiveWindow) :
    residue (coefficientBlockProgram n start r width w).2 = 0 := by
  unfold coefficientBlockProgram coefficientBlockSegments
  simp [sequenceProgram, residue_literal, primitivePhaseCost]

@[simp] theorem residue_zeroCell (n start : Nat) (base : Bool) (r bit guard target temporary : Wire) :
    residue (zeroCellProgram n start base r bit guard target temporary).2 = 0 := by
  cases base <;> simp [zeroCellProgram, measuredZeroPrefix, primitivePhaseCost]

@[simp] theorem residue_upperForwardLeaf (n start k K : Nat) (control temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire) :
    residue (upperForwardLeafProgram n start k K control temporary bitAt dirtyAt label r).2 = 0 := by
  by_cases h : k ≤ label ∧ label ≤ K
  · by_cases he : label = K <;> simp [upperForwardLeafProgram, h, he]
  · simp [upperForwardLeafProgram, h]

@[simp] theorem residue_upperReverseLeaf (n start k K : Nat) (temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire) :
    residue (upperReverseLeafProgram n start k K temporary bitAt dirtyAt label r).2 = 0 := by
  by_cases h : k ≤ label ∧ label < K <;> simp [upperReverseLeafProgram, h]

@[simp] theorem residue_lowerForwardLeaf (n start k K : Nat) (control temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire) :
    residue (lowerForwardLeafProgram n start k K control temporary bitAt dirtyAt label r).2 = 0 := by
  by_cases h : k ≤ label ∧ label ≤ K
  · by_cases he : label = k <;> simp [lowerForwardLeafProgram, h, he]
  · simp [lowerForwardLeafProgram, h]

@[simp] theorem residue_lowerReverseLeaf (n start k K : Nat) (temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire) :
    residue (lowerReverseLeafProgram n start k K temporary bitAt dirtyAt label r).2 = 0 := by
  by_cases h : k < label ∧ label ≤ K <;> simp [lowerReverseLeafProgram, h]

@[simp] theorem residue_rangeLeaf (n : Nat) (after : Bool) (r : Wire)
    (leaf : Nat → Wire → FixedSegment n)
    (hl : ∀ label control start, residue (leaf label control start).2 = 0)
    (label : Nat) (dynamic : Wire) (start : Nat) :
    residue (rangeLeafProgram n after r leaf label dynamic start).2 = 0 := by
  cases after <;> simp [rangeLeafProgram, hl, residue_literal, primitivePhaseCost]

@[simp] theorem residue_rangeScan (n : Nat) (after : Bool) (order : UnaryOrder)
    (tree : UnaryActionTree) (control r : Wire) (path : List Wire)
    (leaf : Nat → Wire → FixedSegment n) (start : Nat)
    (hl : ∀ label control start, residue (leaf label control start).2 = 0) :
    residue (rangeScanProgram n after order tree control r path leaf start).2 = 0 := by
  have hr (after : Bool) : ∀ label control start,
      residue (rangeLeafProgram n after r leaf label control start).2 = 0 := by simp [hl]
  cases after <;> simp [rangeScanProgram, residue_unary _ _ _ (hr _), residue_literal, primitivePhaseCost]

@[simp] theorem residue_upperMap (n k K : Nat) (tree : UnaryActionTree) (control r t : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire) (start : Nat) :
    residue (upperMapProgram n k K tree control r t path bitAt dirtyAt start).2 = 0 := by
  simp [upperMapProgram]

@[simp] theorem residue_lowerMap (n k K : Nat) (tree : UnaryActionTree) (control r t : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire) (start : Nat) :
    residue (lowerMapProgram n k K tree control r t path bitAt dirtyAt start).2 = 0 := by
  simp [lowerMapProgram]

@[simp] theorem phaseCost_highestWrites (k K : Nat) (targets : List Wire) (dirtyAt : Nat → Wire) :
    ((highestPositionDirtyWrites k K targets dirtyAt).map primitivePhaseCost).sum = 0 :=
  primitivePhaseCost_of_HPFree _ (by simp [highestPositionDirtyWrites])
@[simp] theorem phaseCost_rightWrites (width k K : Nat) (targets : List Wire) (dirtyAt : Nat → Wire) :
    ((rightLengthDirtyWrites width k K targets dirtyAt).map primitivePhaseCost).sum = 0 :=
  primitivePhaseCost_of_HPFree _ (by simp [rightLengthDirtyWrites])

@[simp] theorem residue_upperWriter (n k K : Nat) (tree : UnaryActionTree) (control r t : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire) (targets : List Wire) (start : Nat) :
    residue (upperWriterProgram n k K tree control r t path bitAt dirtyAt targets start).2 = 0 := by
  simp [upperWriterProgram]

@[simp] theorem residue_lowerWriter (n width k K : Nat) (tree : UnaryActionTree) (control r t : Wire)
    (path : List Wire) (bitAt dirtyAt : Nat → Wire) (targets : List Wire) (start : Nat) :
    residue (lowerWriterProgram n width k K tree control r t path bitAt dirtyAt targets start).2 = 0 := by
  simp [lowerWriterProgram]

@[simp] theorem residue_ltUpdate (n width k K : Nat) (tree : UnaryActionTree) (control r t carry : Wire)
    (path : List Wire) (work1At work2At : Nat → Wire) (lengthT lengthRP constants : List Wire) (start : Nat) :
    residue (ltUpdateProgram n width k K tree control r t carry path work1At work2At lengthT lengthRP constants start).2 = 0 := by
  simp [ltUpdateProgram]
@[simp] theorem residue_lrpUpdate (n width k K : Nat) (tree : UnaryActionTree) (control r t carry : Wire)
    (path : List Wire) (work1At work2At : Nat → Wire) (lengthT lengthRP constants : List Wire) (start : Nat) :
    residue (lrpUpdateProgram n width k K tree control r t carry path work1At work2At lengthT lengthRP constants start).2 = 0 := by
  simp [lrpUpdateProgram]

@[simp] theorem residue_upperEnd (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows) :
    residue (upperEndProgram n start r width w).2 = 0 := by
  simp [upperEndProgram, residue_literal]

@[simp] theorem residue_lowerEnd (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows) :
    residue (lowerEndProgram n start r width w).2 = 0 := by
  simp [lowerEndProgram, residue_literal]

@[simp] theorem residue_end (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows) :
    residue (endProgram n start r width w).2 = 0 := by
  simp [endProgram, residue_literal]

@[simp] theorem residue_endInverse (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows) :
    residue (endInverseProgram n start r width w).2 = 0 := by
  simp [endInverseProgram, residue_literal]

@[simp] private theorem blockHPrefix_classical (r : IndexedStepRegisters) : Classical.HPFree (blockHPrefix r) := by
  simp [blockHPrefix]
@[simp] private theorem blockHSuffix_classical (r : IndexedStepRegisters) : Classical.HPFree (blockHSuffix r) := by
  simp [blockHSuffix]

@[simp] theorem residue_h (n start : Nat) (r : IndexedStepRegisters) (width T : Nat) :
    residue (hProgram n start r width T).2 = 0 := by
  simp [hProgram, residue_literal, primitivePhaseCost]
@[simp] theorem residue_hInverse (n start : Nat) (r : IndexedStepRegisters) (width T : Nat) :
    residue (hInverseProgram n start r width T).2 = 0 := by
  simp [hInverseProgram, residue_literal, primitivePhaseCost]

@[simp] private theorem blockAForward_classical (r : IndexedStepRegisters) : Classical.HPFree (blockAForward r) := by
  have h := indexedStepUnitary_HPFree r 256 1
  simp only [indexedStepUnitary, Classical.hpFree_append] at h
  tauto

@[simp] private theorem blockCForward_classical (r : IndexedStepRegisters) : Classical.HPFree (blockCForward r) := by
  have h := indexedStepUnitary_HPFree r 256 1
  simp only [indexedStepUnitary, Classical.hpFree_append] at h
  tauto

@[simp] private theorem blockFForward_classical (r : IndexedStepRegisters) : Classical.HPFree (blockFForward r) := by
  have h := indexedStepUnitary_HPFree r 256 1
  simp only [indexedStepUnitary, Classical.hpFree_append] at h
  tauto

@[simp] private theorem blockAInverse_classical (r : IndexedStepRegisters) : Classical.HPFree (blockAInverse r) := by
  have h := indexedStepInverseUnitary_HPFree r 256 1
  simp only [indexedStepInverseUnitary, Classical.hpFree_append] at h
  tauto

@[simp] private theorem blockCInverse_classical (r : IndexedStepRegisters) : Classical.HPFree (blockCInverse r) := by
  have h := indexedStepInverseUnitary_HPFree r 256 1
  simp only [indexedStepInverseUnitary, Classical.hpFree_append] at h
  tauto

@[simp] private theorem blockDForward_classical (r : IndexedStepRegisters) (width T : Nat) :
    Classical.HPFree (blockDForward r (certifiedActiveWindows width T).quotientSwap) := by
  have h := indexedStepUnitary_HPFree r width T
  simp only [indexedStepUnitary, Classical.hpFree_append] at h
  tauto

@[simp] private theorem blockDInverse_classical (r : IndexedStepRegisters) (width T : Nat) :
    Classical.HPFree (blockDInverse r (certifiedActiveWindows width T).quotientSwap) := by
  have h := indexedStepInverseUnitary_HPFree r width T
  simp only [indexedStepInverseUnitary, Classical.hpFree_append] at h
  tauto

@[simp] theorem residue_measuredStep (n start : Nat) (r : IndexedStepRegisters) (width T : Nat) :
    residue (measuredStepProgram n start r width T).2 = 0 := by
  simp [measuredStepProgram, measuredStepSegments, sequenceProgram, residue_literal, primitivePhaseCost]

@[simp] theorem phaseCost_adjoint (gs : Circuit) :
    ((gs.adjoint).map primitivePhaseCost).sum = (gs.map primitivePhaseCost).sum := by
  have h := congrArg PrimitiveResources.phase (primitiveResources_unitary_adjoint gs .done)
  simpa [primitiveResources, gidneyGateCount] using h

@[simp] theorem residue_measuredInverseStep (n start : Nat) (r : IndexedStepRegisters) (T : Nat) :
    residue (measuredInverseStepProgram n start r T).2 = 0 := by
  simp [measuredInverseStepProgram, measuredInverseStepSegments, sequenceProgram,
    residue_literal, primitivePhaseCost, blockB2_classical]

@[simp] theorem residue_measuredSchedule (n : Nat) (r : IndexedStepRegisters)
    (width count first start : Nat) :
    residue (measuredScheduleProgram n r width count first start).2 = 0 := by
  induction count generalizing first start with
  | zero => rfl
  | succ count ih => simp only [measuredScheduleProgram, residue_compiled, residue_measuredStep, ih, Nat.zero_add]

@[simp] theorem residue_measuredInverseSchedule (n : Nat) (r : IndexedStepRegisters)
    (count first start : Nat) :
    residue (measuredInverseScheduleProgram n r count first start).2 = 0 := by
  induction count generalizing first start with
  | zero => rfl
  | succ count ih => simp only [measuredInverseScheduleProgram, residue_compiled, residue_measuredInverseStep, ih, Nat.zero_add]

end
end ShorECDLP.Entrant.AndGadget
end

section
namespace ShorECDLP.Entrant.AndGadget
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 3000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

theorem ccx_cost_le (gs : Circuit) : 7 * ccxCount gs ≤ tCount gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => cases g <;>
      simp only [ccxCount, tCount, List.map_cons, List.sum_cons, tCost] at * <;> omega

theorem adaptive_ccx_cost_le (p : AdaptiveCircuit) : 7 * (primitiveResources p).toffoli ≤ p.tCount := by
  induction p with
  | done => rfl
  | unitary gs p ih =>
      have hg := ccx_cost_le gs
      rw [ccxCount_primitive] at hg
      simp only [primitiveResources, gidneyToffoliCount, gidneyGateCount, AdaptiveCircuit.tCount] at *
      omega
  | xMeasureReset w f t ihf iht =>
      simp only [primitiveResources, gidneyToffoliCount, gidneyGateCount, AdaptiveCircuit.tCount] at *
      omega

attribute [local irreducible] measuredEEAForwardProgram measuredEEAReverseProgram
 secp256k1MeasuredEEAForward secp256k1MeasuredEEAReverse added residue
 primitiveResources AdaptiveCircuit.tCount

theorem forwardCoreFullCount (n start : Nat) :
    AtLeast (measuredEEAForwardProgram n start indexedStepProductionRegisters).2 15772489 := by
  have hs := secp256k1MeasuredEEAForward_toffoli indexedStepProductionRegisters
    secp256k1ScheduleLayout_production (by decide)
  rw [secp256k1EEAForwardPrimitive_certificate] at hs
  have hl := adaptive_ccx_cost_le (secp256k1MeasuredEEAForward indexedStepProductionRegisters)
  have ht := measuredEEAForwardProgram_tCount n start indexedStepProductionRegisters
    (fun _ => false) (fun _ => false)
  have hr := residue_t (measuredEEAForwardProgram n start indexedStepProductionRegisters).2
    (fun _ => false) (fun _ => false)
  have hz : residue (measuredEEAForwardProgram n start indexedStepProductionRegisters).2 = 0 := by
    unfold measuredEEAForwardProgram
    exact residue_measuredSchedule _ _ _ _ _ _
  unfold AtLeast
  unfold compiledTCount at ht
  change (primitiveResources (secp256k1MeasuredEEAForward indexedStepProductionRegisters)).toffoli + 1681736 = 17454225 at hs
  omega

theorem reverseCoreFullCount (n start : Nat) :
    AtLeast (measuredEEAReverseProgram n start indexedStepProductionRegisters).2 15772489 := by
  have hs := secp256k1MeasuredEEAReverse_toffoli indexedStepProductionRegisters
    secp256k1ScheduleLayout_production (by decide)
  rw [secp256k1EEAReversePrimitive_certificate] at hs
  have hl := adaptive_ccx_cost_le (secp256k1MeasuredEEAReverse indexedStepProductionRegisters)
  have ht := measuredEEAReverseProgram_tCount n start indexedStepProductionRegisters
    (fun _ => false) (fun _ => false)
  have hr := residue_t (measuredEEAReverseProgram n start indexedStepProductionRegisters).2
    (fun _ => false) (fun _ => false)
  have hz : residue (measuredEEAReverseProgram n start indexedStepProductionRegisters).2 = 0 := by
    unfold measuredEEAReverseProgram
    exact residue_measuredInverseSchedule _ _ _ _ _
  unfold AtLeast
  unfold compiledTCount at ht
  change (primitiveResources (secp256k1MeasuredEEAReverse indexedStepProductionRegisters)).toffoli + 1681736 = 17454225 at hs
  omega
attribute [local irreducible] sequenceProgram appendCompiled literalProgram
 measuredForwardWrapperProgram measuredReverseWrapperProgram

theorem forwardWrapperFullCount (n start : Nat) :
    AtLeast (measuredForwardWrapperProgram n start).2 15772489 := by
  unfold measuredForwardWrapperProgram measuredForwardWrapperSegments
  refine (AtLeast.sequenceCons (d := 0) (f := 15772489) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  exact (AtLeast.sequenceCons (d := 15772489) (f := 0) _ _
    (forwardCoreFullCount n _) (AtLeast.zero _)).castCount (by omega)

theorem reverseWrapperFullCount (n start : Nat) :
    AtLeast (measuredReverseWrapperProgram n start).2 15772489 := by
  unfold measuredReverseWrapperProgram measuredReverseWrapperSegments
  refine (AtLeast.sequenceCons (d := 0) (f := 15772489) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 0) (f := 15772489) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 0) (f := 15772489) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  exact (AtLeast.sequenceCons (d := 15772489) (f := 0) _ _
    (reverseCoreFullCount n _) (AtLeast.zero _)).castCount (by omega)

theorem AtLeast.relabelCompiled {n start d} (p : (count : Nat) × Straight n start (start+count))
    (hp : AtLeast p.2 d) (f : Wire ≃ Wire) : AtLeast (ChallengeMigration.relabelCompiled f p).2 d := hp.relabel f
def CompiledAtLeast {n start} (p : (count : Nat) × Straight n start (start+count)) (d : Nat) : Prop := AtLeast p.2 d

theorem AtLeast.measure {n s e d} (w : Wire) {p : Straight n (s+1) e} (hp : AtLeast p d) :
    AtLeast (.measure w p) d := by simpa only [AtLeast, added] using hp

theorem AtLeast.collect {n d}
    (next : (cursor : Nat) → List (Fin cursor) → (count : Nat) × Straight n cursor (cursor+count))
    (hn : ∀ cursor prior, AtLeast (next cursor prior).2 d)
    (ws : List Wire) (start : Nat) (prior : List (Fin start)) :
    AtLeast (collectProgram n next ws start prior).2 d := by
  change CompiledAtLeast (collectProgram n next ws start prior) d
  induction ws generalizing start with
  | nil => exact hn start prior
  | cons w ws ih =>
    rw [collectProgram]
    dsimp only [CompiledAtLeast]
    apply AtLeast.castFinish
    apply AtLeast.measure
    exact ih (start+1) _

theorem forwardBankCount (n start : Nat) :
    AtLeast (measuredForwardDataBankProgram n start).2 15772489 :=
  AtLeast.relabelCompiled _ (forwardWrapperFullCount n start) eeaWorkspaceExchange

theorem reverseBankCount (n start : Nat) :
    AtLeast (measuredReverseDataBankProgram n start).2 15772489 :=
  AtLeast.relabelCompiled _ (reverseWrapperFullCount n start) eeaWorkspaceExchange

attribute [local irreducible] measuredForwardDataBankProgram measuredReverseDataBankProgram
 multiplyDataProgram multiplyWorkProgram unmultiplyDataProgram divisionAfterResetProgram divisionProgram
 multiplicationAfterResetProgram multiplicationCleanupProgram multiplicationCorrectionProgram
 multiplicationProgram coordinateProgram zeroDivisionProgram zeroMultiplicationProgram

theorem divisionAfterCount (n start : Nat) (prior : List (Fin start)) :
    AtLeast (divisionAfterResetProgram n start prior).2 15772489 := by
  unfold divisionAfterResetProgram appendRetaining
  refine (AtLeast.appendCompiled (d := 15772489) (f := 0) _ _ ?_ (AtLeast.zero _)).castCount (by omega)
  exact (AtLeast.appendCompiled _ _ (reverseBankCount n start) (AtLeast.zero _)).castCount (by omega)

theorem divisionBothCount (n start : Nat) : AtLeast (divisionProgram n start).2 31544978 := by
  unfold divisionProgram
  refine AtLeast.appendCompiled (d := 15772489) (f := 15772489) _ _ ?_ ?_
  · exact (AtLeast.appendCompiled _ _ (forwardWrapperFullCount n start) (AtLeast.zero _)).castCount (by omega)
  · exact AtLeast.collect (divisionAfterResetProgram n) (divisionAfterCount n) _ _ _

theorem multiplicationCleanupCount (n start : Nat) :
    AtLeast (multiplicationCleanupProgram n start).2 15772489 := by
  unfold multiplicationCleanupProgram
  exact (AtLeast.appendCompiled (d := 0) (f := 15772489) _ _ (AtLeast.zero _)
    (AtLeast.appendLiteral _ _ (reverseBankCount n _))).castCount (Nat.zero_add _)

theorem multiplicationCorrectionCount (n start : Nat) (prior : List (Fin start)) :
    AtLeast (multiplicationCorrectionProgram n start prior).2 15772489 := by
  unfold multiplicationCorrectionProgram
  exact (AtLeast.appendCompiled _ _ (AtLeast.zero _) (multiplicationCleanupCount n _)).castCount (by omega)

theorem multiplicationAfterCount (n start : Nat) (prior : List (Fin start)) :
    AtLeast (multiplicationAfterResetProgram n start prior).2 31544978 := by
  unfold multiplicationAfterResetProgram appendRetaining
  refine AtLeast.appendCompiled (d := 15772489) (f := 15772489) _ _ ?_ (multiplicationCorrectionCount n _ _)
  exact (AtLeast.appendCompiled _ _ (forwardBankCount n start) (AtLeast.zero _)).castCount (by omega)

theorem multiplicationBothCount (n start : Nat) : AtLeast (multiplicationProgram n start).2 31544978 := by
  unfold multiplicationProgram
  refine (AtLeast.appendCompiled (d := 0) (f := 31544978) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  exact AtLeast.collect (multiplicationAfterResetProgram n) (multiplicationAfterCount n) _ _ _

theorem coordinateAllCount (start : Nat) : AtLeast (coordinateProgram start).2 63089956 := by
  unfold coordinateProgram coordinateSegments
  refine (AtLeast.sequenceCons (d := 0) (f := 63089956) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 0) (f := 63089956) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  refine AtLeast.sequenceCons (d := 31544978) (f := 31544978) _ _ ?_ ?_
  · unfold zeroDivisionProgram
    exact AtLeast.surroundCompiled _ _ _ (divisionBothCount _ _)
  · refine (AtLeast.sequenceCons (d := 0) (f := 31544978) _ _ (AtLeast.zero _) ?_).castCount (by omega)
    refine (AtLeast.sequenceCons (d := 0) (f := 31544978) _ _ (AtLeast.zero _) ?_).castCount (by omega)
    refine (AtLeast.sequenceCons (d := 31544978) (f := 0) _ _ ?_ (AtLeast.zero _)).castCount (by omega)
    unfold zeroMultiplicationProgram
    exact AtLeast.surroundCompiled _ _ _ (multiplicationBothCount _ _)

end
end ShorECDLP.Entrant.AndGadget
end
end

section
section
set_option Elab.async false
namespace ShorECDLP.Entrant.Catalyst
open Quantum Paper2607_13816
noncomputable section
attribute [local irreducible] Quantum.run Quantum.applyGate Quantum.ket
set_option linter.unusedSimpArgs false

def prepare (q : Wire) : Circuit := [.H q, .P .forward 2 q]
def kick (t q : Wire) : Circuit := [.CX t q] ++ controlledZ t q
private theorem phase_two : phaseCoeff .forward 2 = Complex.I := by
  simp only [phaseCoeff, phaseAngle]
  convert Complex.exp_pi_div_two_mul_I using 1
  congr 1
  push_cast
  ring
private theorem upd_twice (s : BasisState) (q : Wire) (a b : Bool) :
    s[q ↦ a][q ↦ b] = s[q ↦ b] := by
  funext w
  by_cases h : w = q <;> simp [upd, h]

theorem kick_ket (t q : Wire) (ht : t ≠ q) (s : BasisState) (hq : s q = false) :
    Quantum.run (kick t q) (Quantum.run (prepare q) (ket s)) =
      Quantum.run (prepare q) (applyGate (.P .forward 2 t) (ket s)) := by
  simp only [kick, prepare, Quantum.run_append, Quantum.run_cons, Quantum.run_nil,
    LinearMap.id_coe, id_eq, applyGate_H_ket, applyGate_P_ket, map_add, map_smul,
    applyGate_CX_ket, run_controlledZ_ket t q _ ht, upd_same, upd_other _ _ _ ht,
    upd_twice, phase_two, hq, Bool.false_eq_true, if_false, if_true, mul_one]
  cases hs : s t <;> simp [hs, smul_add, smul_smul, Complex.I_mul_I]
  all_goals match_scalars <;> ring_nf
  all_goals norm_num [Complex.I_sq]

theorem linear_on_supported (A B : State →ₗ[ℂ] State) (V : BasisState → Prop)
    (h : ∀ s, V s → A (ket s) = B (ket s)) (psi : State) (hp : SupportedOn V psi) :
    A psi = B psi := by
  have hb : BranchCoherentOn B V ⟨[],A⟩ 1 := by
    intro s hs
    simpa only [one_smul] using h s hs
  simpa only [one_smul] using hb.on_supported hp

theorem linear_comp_supported (A B C D : State →ₗ[ℂ] State) (V : BasisState → Prop)
    (h : ∀ s, V s → A (B (ket s)) = C (D (ket s))) (psi : State) (hp : SupportedOn V psi) :
    A (B psi) = C (D psi) := linear_on_supported (A.comp B) (C.comp D) V h psi hp

theorem kick_supported (t q : Wire) (ht : t ≠ q) (psi : State)
    (hp : SupportedOn (fun s => s q = false) psi) :
    Quantum.run (kick t q) (Quantum.run (prepare q) psi) =
      Quantum.run (prepare q) (applyGate (.P .forward 2 t) psi) :=
  linear_comp_supported (Quantum.run (kick t q)) (Quantum.run (prepare q))
    (Quantum.run (prepare q)) (applyGate (.P .forward 2 t)) _
    (kick_ket t q ht) psi hp

theorem prepare_gate (q : Wire) (g : Gate) (hq : q ∉ gateWires g) (psi : State) :
    applyGate g (Quantum.run (prepare q) psi) = Quantum.run (prepare q) (applyGate g psi) := by
  simp only [prepare, Quantum.run_cons, Quantum.run_nil, LinearMap.id_coe, id_eq]
  rw [applyGate_P_commute g q .forward 2 hq, applyGate_H_commute g q hq]

theorem prepare_reset (q w : Wire) (hq : q ≠ w) (b : Bool) (psi : State) :
    xResetKraus w b (Quantum.run (prepare q) psi) = Quantum.run (prepare q) (xResetKraus w b psi) := by
  simp only [prepare, Quantum.run_cons, Quantum.run_nil, LinearMap.id_coe, id_eq]
  rw [xReset_P_commute w q b .forward 2 hq,
    ← applyGate_reset_commute (.H q) w b (by simpa [gateWires, ne_comm] using hq)]
open Challenge AndGadget

def replacement (q : Wire) : Gate → Circuit
  | .P .forward 2 t => kick t q
  | g => [g]

def savedGate : Gate → Nat
  | .P .forward 2 _ => 1
  | _ => 0

def compile {n s e} (q : Wire) : Straight n s e → Straight n s e
  | .done => .done
  | .gate (.literal g) next => literals (replacement q g) (compile q next)
  | .gate (.whenBit r v g) next => .gate (.whenBit r v g) (compile q next)
  | .recordGate i v g next => .recordGate i v g (compile q next)
  | .measure w next => .measure w (compile q next)

def saved {n s e} : Straight n s e → Nat
  | .done => 0
  | .gate (.literal g) next => savedGate g + saved next
  | .gate _ next => saved next
  | .recordGate _ _ _ next => saved next
  | .measure _ next => saved next

theorem replacement_correct (q : Wire) (g : Gate) (hq : q ∉ gateWires g)
    (psi : State) (hp : SupportedOn (fun s => s q = false) psi) :
    Quantum.run (replacement q g) (Quantum.run (prepare q) psi) =
      Quantum.run (prepare q) (applyGate g psi) := by
  unfold replacement
  split
  · rename_i t
    exact kick_supported t q (by simpa [gateWires, ne_comm] using hq) psi hp
  · simpa only [Quantum.run_singleton] using prepare_gate q g hq psi

private theorem gate_frame (q : Wire) (gs : Circuit) (hq : q ∉ circuitWires gs)
    (psi : State) (hpsi : SupportedOn (fun s => s q = false) psi) :
    SupportedOn (fun s => s q = false) (Quantum.run gs psi) := by
  have h := AdaptiveCircuit.branch_frame (.unitary gs .done) q false
    (by simpa [AdaptiveCircuit.wires] using hq)
    ⟨[], Quantum.run gs⟩ (by simp only [AdaptiveCircuit.run, List.map_singleton, List.mem_singleton]; rfl) psi hpsi
  exact h

private theorem reset_frame (q w : Wire) (hq : q ≠ w) (outcome : Bool)
    (psi : State) (hpsi : SupportedOn (fun s => s q = false) psi) :
    SupportedOn (fun s => s q = false) (xResetKraus w outcome psi) := by
  apply AdaptiveCircuit.branch_frame (.xMeasureReset w .done .done) q false
    (by simpa [AdaptiveCircuit.wires] using hq)
    ⟨[outcome], xResetKraus w outcome⟩ ?_ psi hpsi
  cases outcome <;>
    simp only [AdaptiveCircuit.run, List.map_singleton, List.mem_append, List.mem_singleton]
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem compile_expectation {n s e} (q : Wire) (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) (psi : State)
    (accept : (Fin e → Bool) → Bool) (hf : Fresh q p)
    (hp : SupportedOn (fun s => s q = false) psi) :
    expectation read (compile q p) history (Quantum.run (prepare q) psi) accept =
      expectation read p history psi accept := by
  induction p generalizing psi with
  | done =>
    simp only [compile, expectation, normSq_run (prepare q) (by simp [prepare, CircuitWellFormed, Gate.WellFormed])]
  | gate g p ih =>
    cases g with
    | literal g =>
      simp only [compile, expectation_literals, replacement_correct q g hf.1 psi hp,
        expectation, TemplateGate.instantiate, Quantum.run_singleton]
      exact ih history _ accept hf.2 (by simpa only [Quantum.run_singleton] using gate_frame q ([g] : Circuit) (by simpa [circuitWires] using hf.1) psi hp)
    | whenBit r v g =>
      simp only [compile, expectation, TemplateGate.instantiate]
      split
      · simp only [Quantum.run_singleton, prepare_gate q g hf.1]
        exact ih history _ accept hf.2 (by simpa only [Quantum.run_singleton] using gate_frame q ([g] : Circuit) (by simpa [circuitWires] using hf.1) psi hp)
      · simpa only [Quantum.run_nil, LinearMap.id_coe, id_eq] using ih history psi accept hf.2 hp
  | recordGate i v g p ih =>
    simp only [compile, expectation]
    split
    · simp only [Quantum.run_singleton, prepare_gate q g hf.1]
      exact ih history _ accept hf.2 (by simpa only [Quantum.run_singleton] using gate_frame q ([g] : Circuit) (by simpa [circuitWires] using hf.1) psi hp)
    · simpa only [Quantum.run_nil, LinearMap.id_coe, id_eq] using ih history psi accept hf.2 hp
  | measure w p ih =>
    simp only [compile, expectation, prepare_reset q w hf.1]
    rw [ih _ _ accept hf.2 (reset_frame q w hf.1 false psi hp), ih _ _ accept hf.2 (reset_frame q w hf.1 true psi hp)]

theorem replacement_t (q : Wire) (g : Gate) :
    ShorECDLP.tCount (replacement q g) + savedGate g = tCost g := by
  unfold replacement savedGate
  split
  · rfl
  · rename_i g h
    cases g <;> simp_all [tCount, tCost]

theorem literals_t {n s e} (gs : Circuit) (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    ((literals gs p).instantiate read history).tCount =
      ShorECDLP.tCount gs + (p.instantiate read history).tCount := AndGadget.literals_t read gs p history

theorem compile_t {n s e} (q : Wire) (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    ((compile q p).instantiate read history).tCount + saved p =
      (p.instantiate read history).tCount := by
  induction p with
  | done => rfl
  | gate g p ih =>
    cases g with
    | literal g =>
      simp only [compile, literals_t, saved, Straight.instantiate, TemplateGate.instantiate,
        AdaptiveCircuit.tCount, tCount, List.sum_cons, List.map_cons, List.map_nil, List.sum_nil]
      have h := replacement_t q g
      simp only [ShorECDLP.tCount] at h
      have hi := ih history
      omega
    | whenBit r v g =>
      simp only [compile, saved, Straight.instantiate, TemplateGate.instantiate, AdaptiveCircuit.tCount]
      have hi := ih history
      omega
  | recordGate i v g p ih =>
    simp only [compile, saved, Straight.instantiate, AdaptiveCircuit.tCount]
    have hi := ih history
    omega
  | measure w p ih =>
    simp only [compile, saved, Straight.instantiate, AdaptiveCircuit.tCount]
    have h0 := ih (Fin.lastCases false history)
    have h1 := ih (Fin.lastCases true history)
    omega

theorem replacement_wellFormed (q : Wire) (g : Gate) (hq : q ∉ gateWires g)
    (hg : Gate.WellFormed g) : CircuitWellFormed (replacement q g) := by
  unfold replacement
  split
  · rename_i t
    have ht : t ≠ q := by simpa [gateWires, ne_comm] using hq
    simp [kick, controlledZ, CircuitWellFormed, Gate.WellFormed, ht]
  · simpa [CircuitWellFormed] using hg

theorem literals_wellFormed {n s e} (gs : Circuit) (p : Straight n s e)
    (hg : CircuitWellFormed gs) (hp : p.WellFormed) : (literals gs p).WellFormed := by
  induction gs with
  | nil => exact hp
  | cons g gs ih =>
    exact ⟨hg g (by simp), ih (by intro a ha; exact hg a (by simp [ha]))⟩

theorem compile_wellFormed {n s e} (q : Wire) (p : Straight n s e)
    (hf : Fresh q p) (hp : p.WellFormed) : (compile q p).WellFormed := by
  induction p with
  | done => trivial
  | gate g p ih =>
    cases g with
    | literal g => exact literals_wellFormed _ _ (replacement_wellFormed q g hf.1 hp.1) (ih hf.2 hp.2)
    | whenBit => exact ⟨hp.1, ih hf.2 hp.2⟩
  | recordGate => exact ⟨hp.1, by apply_assumption; exact hf.2; exact hp.2⟩
  | measure w p ih => exact ih hf.2 hp

theorem replacement_wires (q : Wire) (g : Gate) :
    circuitWires (replacement q g) ⊆ q :: gateWires g := by
  unfold replacement
  split
  · simp [kick, controlledZ, circuitWires, gateWires, List.subset_def]
  · simp [circuitWires]

theorem literals_within {n s e} (ws : List Wire) (gs : Circuit) (p : Straight n s e)
    (hg : circuitWires gs ⊆ ws) (hp : Within ws p) : Within ws (literals gs p) := by
  induction gs with
  | nil => exact hp
  | cons g gs ih =>
    have h : gateWires g ⊆ ws ∧ circuitWires gs ⊆ ws := by simpa [circuitWires] using hg
    exact ⟨h.1, ih h.2⟩

theorem compile_within {n s e} (q : Wire) (p : Straight n s e) (ws : List Wire)
    (hp : Within ws p) : Within (q::ws) (compile q p) := by
  induction p with
  | done => trivial
  | gate g p ih =>
    cases g with
    | literal g =>
      apply literals_within
      · exact (replacement_wires q g).trans (List.cons_subset_cons q hp.1)
      · exact ih hp.2
    | whenBit => exact ⟨fun _ h => List.mem_cons_of_mem q (hp.1 h), ih hp.2⟩
  | recordGate => exact ⟨fun _ h => List.mem_cons_of_mem q (hp.1 h), by apply_assumption; exact hp.2⟩
  | measure => exact ⟨List.mem_cons_of_mem q hp.1, by apply_assumption; exact hp.2⟩

theorem replacement_length (q : Wire) (g : Gate) :
    (replacement q g).length = 1 + 3 * savedGate g := by
  unfold replacement savedGate
  split <;> rfl

theorem compile_slots {n s e} (q : Wire) (p : Straight n s e) :
    (compile q p).gateSlots = p.gateSlots + 3 * saved p := by
  induction p with
  | done => rfl
  | gate g p ih => cases g <;> simp [compile, saved, literals_slots, replacement_length, Straight.gateSlots, ih] <;> omega
  | recordGate => simp_all [compile, saved, Straight.gateSlots]; omega
  | measure => exact (by apply_assumption)

theorem saved_le_slots {n s e} (p : Straight n s e) : saved p ≤ p.gateSlots := by
  induction p with
  | done => rfl
  | gate g p ih =>
    cases g with
    | literal g =>
      have hg : savedGate g ≤ 1 := by unfold savedGate; split <;> omega
      simp only [saved, Straight.gateSlots]
      omega
    | whenBit => simp only [saved, Straight.gateSlots]; omega
  | recordGate => simp only [saved, Straight.gateSlots]; omega
  | measure => exact (by apply_assumption)

theorem saved_literals {n s e} (gs : Circuit) (p : Straight n s e) :
    saved (literals gs p) = (gs.map savedGate).sum + saved p := by
  induction gs with
  | nil => simp [literals]
  | cons g gs ih =>
    change savedGate g + saved (literals gs p) = _
    rw [ih]
    simp [Nat.add_assoc]

theorem saved_toffoliPrefix {n s e} (a b t q : Wire) (p : Straight n (s+1) e) :
    saved (toffoliPrefix a b t q p) = 1 + saved p := by
  simp [toffoliPrefix, saved_literals, andCompute, parityPhase, xorPhase, saved, savedGate]

theorem saved_lower {n s e} (q : Wire) (p : Straight n s e) (start : Nat)
    (records : Fin s → Fin start) :
    saved (lower q p start records).program = added p + saved p := by
  induction p generalizing start with
  | done => rfl
  | gate g p ih =>
    cases g with
    | literal g => cases g <;> simp [lower, added, saved, saved_toffoliPrefix, ih, savedGate] <;> omega
    | whenBit => exact ih _ _
  | recordGate => exact (by apply_assumption)
  | measure => exact (by apply_assumption)

def compileEntry (q : Wire) (entry : StraightEntry) : StraightEntry where
  coefficients := entry.coefficients
  finalCursor := entry.finalCursor
  program := literals (prepare q) (compile q entry.program)

theorem compile_verified {n e} (q : Wire) (p : Straight n 0 e)
    (read : ConstantBit n → Bool) (layout : DecodeLayout) (Q : Secp256k1.Point)
    (psi : State) (hf : Fresh q p) (hp : SupportedOn (fun s => s q = false) psi) :
    Instrument.bornMass (((literals (prepare q) (compile q p)).instantiate read Fin.elim0).run.filter
      (fun b => (verifiedCandidate layout Q b.history).isSome)) psi =
    Instrument.bornMass ((p.instantiate read Fin.elim0).run.filter
      (fun b => (verifiedCandidate layout Q b.history).isSome)) psi := by
  rw [← expectation_verified, ← expectation_verified, expectation_literals]
  exact compile_expectation q p read Fin.elim0 psi _ hf hp

theorem compileEntry_within (q : Wire) (entry : StraightEntry) (ws : List Wire)
    (hp : Within ws entry.program) : Within (q::ws) (compileEntry q entry).program := by
  apply literals_within
  · simp [prepare, circuitWires, gateWires, List.subset_def]
  · exact compile_within q entry.program ws hp

theorem compile_certificate (limits : Limits) (layout : DecodeLayout) (entry : StraightEntry)
    (bounds newBounds : Bounds) (q : Wire) (ws : List Wire)
    (cert : Certificate limits layout entry bounds)
    (hs : Within ws entry.program) (hq : q ∉ ws)
    (hslots : entry.program.gateSlots + 3 * saved entry.program + 2 ≤ limits.gateSlots)
    (hqubits : ws.length + 1 ≤ newBounds.qubits)
    (ht : bounds.tModel + 1 ≤ newBounds.tModel + saved entry.program)
    (hm : entry.finalCursor ≤ newBounds.measurements) :
    Certificate limits layout (compileEntry q entry) newBounds where
  gateBudget := by simpa [compileEntry, literals_slots, compile_slots, prepare, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hslots
  recordBudget := cert.recordBudget
  tableBudget := cert.tableBudget
  candidateBudget := cert.candidateBudget
  wellFormed := literals_wellFormed _ _ (by simp [prepare, CircuitWellFormed, Gate.WellFormed])
    (compile_wellFormed q entry.program (hs.fresh q hq) cert.wellFormed)
  resources := by
    intro Q
    have hsup := (compileEntry_within q entry ws hs).instantiate
      (readConstant entry.coefficients.get Q) Fin.elim0
    have hc : (((compileEntry q entry).instantiate Q).wires.dedup.toFinset).card ≤ (q :: ws).length := by
      apply (Finset.card_le_card ?_).trans (List.toFinset_card_le (q :: ws))
      intro w hw
      apply List.mem_toFinset.mpr
      apply hsup
      simpa only [List.mem_toFinset, List.mem_dedup] using hw
    have hqc : ((compileEntry q entry).instantiate Q).qubitCount ≤ newBounds.qubits := by
      rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
      exact hc.trans hqubits
    have htc := compile_t q entry.program (readConstant entry.coefficients.get Q) Fin.elim0
    have hto := (cert.resources Q).2.1
    have hmc := (compileEntry q entry).program.measurementCount
      (readConstant entry.coefficients.get Q) Fin.elim0
    refine ⟨hqc, ?_, ?_⟩
    · change ((literals (prepare q) (compile q entry.program)).instantiate
        (readConstant entry.coefficients.get Q) Fin.elim0).tCount ≤ newBounds.tModel
      rw [literals_t]
      change 1 + ((compile q entry.program).instantiate (readConstant entry.coefficients.get Q) Fin.elim0).tCount ≤ newBounds.tModel
      change (entry.program.instantiate (readConstant entry.coefficients.get Q) Fin.elim0).tCount ≤ bounds.tModel at hto
      omega
    · change ((compileEntry q entry).program.instantiate (readConstant entry.coefficients.get Q) Fin.elim0).measurementCount ≤ newBounds.measurements
      have he : ((compileEntry q entry).program.instantiate (readConstant entry.coefficients.get Q) Fin.elim0).measurementCount = entry.finalCursor := by
        simpa only [Nat.add_zero] using hmc
      exact he.le.trans hm
  success := by
    intro Q d hn hd
    change 99 / 100 ≤ Instrument.bornMass
      (((literals (prepare q) (compile q entry.program)).instantiate
        (readConstant entry.coefficients.get Q) Fin.elim0).run.filter
        (fun b => (verifiedCandidate layout Q b.history).isSome)) (ket zeroBasisState)
    rw [compile_verified q entry.program _ layout Q _ (hs.fresh q hq)
      (supportedOn_ket _ _ rfl)]
    exact cert.success Q d hn hd

end
end ShorECDLP.Entrant.Catalyst
end
end

section

/-! EDITABLE. Zero residue for the arithmetic outside the EEA cores.

The Toffoli lowering saves two T-model units for every unconditional literal CCX.  Its credited
count used only the measured EEA cores.  Here the same residue argument (`residue = 0`, i.e. no
phase gates and no constant- or record-controlled non-Clifford gates) is proved for the Gidney
adders and comparators, the modular arithmetic built from them and the Horner multipliers, so
their Toffoli gates are credited as well. -/

section
namespace ShorECDLP.Entrant.FullCredit
open Quantum Challenge AndGadget Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 3000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

/-! ## Generic residue facts -/

/-- A circuit with no phase instruction. -/
def PhaseFree (gs : Circuit) : Prop := (gs.map primitivePhaseCost).sum = 0

theorem phaseFree_of_HPFree {gs : Circuit} (h : Classical.HPFree gs) : PhaseFree gs :=
  primitivePhaseCost_of_HPFree gs h

theorem phaseFree_nil : PhaseFree [] := rfl

theorem phaseFree_append {a b : Circuit} (ha : PhaseFree a) (hb : PhaseFree b) :
    PhaseFree (a ++ b) := by
  unfold PhaseFree at *; simp [List.map_append, List.sum_append, ha, hb]

theorem phaseFree_cons {g : Gate} {gs : Circuit} (hg : primitivePhaseCost g = 0)
    (hs : PhaseFree gs) : PhaseFree (g :: gs) := by
  unfold PhaseFree at *; simp [hg, hs]

theorem phaseFree_adjoint {gs : Circuit} (h : PhaseFree gs) : PhaseFree gs.adjoint := by
  unfold PhaseFree at *
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.sum_cons] at h
    have hg : primitivePhaseCost g = 0 := by omega
    have hs : (gs.map primitivePhaseCost).sum = 0 := by omega
    simp only [Circuit.adjoint, List.map_reverse, List.map_cons, List.reverse_cons,
      List.map_append, List.sum_append] at ih ⊢
    have := ih hs
    cases g <;> simp_all [Gate.adjoint, primitivePhaseCost]

theorem residue_literal_pf {n s} {gs : Circuit} (h : PhaseFree gs) :
    residue (literalProgram gs : Straight n s s) = 0 := by
  rw [residue_literal]; exact h

def templateResidue {n : Nat} : TemplateGate n → Nat
  | .literal g => primitivePhaseCost g
  | .whenBit _ _ g => tCost g

theorem residue_gateProgram {n s} (gs : List (TemplateGate n)) :
    residue (gateProgram gs : Straight n s s) = (gs.map templateResidue).sum := by
  induction gs with
  | nil => rfl
  | cons g gs ih => cases g <;> simp [gateProgram, residue, templateResidue, ih]

theorem residue_relabel {n s e} (p : Straight n s e) (f : Wire ≃ Wire) :
    residue (relabelStraight f p) = residue p := by
  have hp (g : Gate) : primitivePhaseCost (g.relabel f) = primitivePhaseCost g := by
    cases g <;> rfl
  have ht (g : Gate) : tCost (g.relabel f) = tCost g := by cases g <;> rfl
  induction p with
  | done => rfl
  | gate g p ih =>
    cases g <;> simp [relabelStraight, relabelTemplateGate, residue, ih, hp, ht]
  | recordGate i v g p ih => simp [relabelStraight, residue, ih, ht]
  | measure w p ih => simp [relabelStraight, residue, ih]

theorem residue_reindex {n m s e} (p : Straight n s e) (f : Fin n → Fin m) :
    residue (reindexStraight f p) = residue p := by
  induction p with
  | done => rfl
  | gate g p ih => cases g <;> simp [reindexStraight, reindexGate, residue, ih]
  | recordGate i v g p ih => simp [reindexStraight, residue, ih]
  | measure w p ih => simp [reindexStraight, residue, ih]

theorem residue_shift {n s e} (p : Straight n s e) (offset : Nat) :
    residue (shiftStraight offset p) = residue p := by
  induction p with
  | done => rfl
  | gate g p ih => cases g <;> simp [shiftStraight, residue, ih]
  | recordGate i v g p ih => simp [shiftStraight, residue, ih]
  | measure w p ih => simp [shiftStraight, residue, ih]

theorem residue_constantStraight {n s e} (q : Wire) (p : Straight n s e) :
    residue (constantStraight q p) ≤ residue p := by
  have hp (g : Gate) : primitivePhaseCost (constantControlGate q g) = primitivePhaseCost g := by
    cases g <;> simp [constantControlGate] <;> split <;> rfl
  have ht (g : Gate) : tCost (constantControlGate q g) ≤ tCost g := by
    cases g <;> simp [constantControlGate] <;> split <;> simp [tCost]
  induction p with
  | done => exact Nat.le_refl _
  | gate g p ih =>
    cases g with
    | literal g => simp only [constantStraight, constantTemplateGate, residue, hp]; omega
    | whenBit i v g =>
      simp only [constantStraight, constantTemplateGate, residue]; have := ht g; omega
  | recordGate i v g p ih =>
    simp only [constantStraight, residue]; have := ht g; omega
  | measure w p ih => simp [constantStraight, residue, ih]

theorem residue_registerCorrection {n s e} (ws : List Wire) (is : List (Fin s))
    (next : Straight n s e) :
    residue (registerCorrectionProgram ws is next) = residue next := by
  induction ws generalizing is with
  | nil => cases is <;> rfl
  | cons w ws ih =>
    cases is with
    | nil => rfl
    | cons i is =>
      simp [registerCorrectionProgram, residue_recordGates, pauliZ, tCount, tCost, ih]

theorem residue_deferred (n : Nat) (targets : List Wire) (cleanup : Circuit)
    (hc : PhaseFree cleanup) :
    ∀ (cells : List (Circuit × Wire)), (∀ c ∈ cells, PhaseFree c.1) →
      ∀ (start : Nat) (prior : List (Fin start)),
        residue (deferredCorrectionProgram n targets cleanup cells start prior) = 0 := by
  intro cells
  induction cells with
  | nil =>
    intro _ start prior
    simp only [deferredCorrectionProgram, residue_registerCorrection, residue_append,
      residue_literal_pf hc, residue_done]
  | cons c cells ih =>
    intro hcells start prior
    obtain ⟨gs, w⟩ := c
    simp only [deferredCorrectionProgram, residue_cast, residue_append,
      residue_literal_pf (hcells _ (List.mem_cons_self ..))]
    simp only [residue, Nat.zero_add]
    exact ih (fun c hc => hcells c (List.mem_cons_of_mem _ hc)) _ _

def lookupOpResidue {n : Nat} : LookupOp n → Nat
  | .gates gs => (gs.map templateResidue).sum
  | .erase _ _ _ => 0

theorem residue_lookup (n : Nat) :
    ∀ (ops : List (LookupOp n)) (start : Nat),
      residue (lookupProgram n ops start) = (ops.map lookupOpResidue).sum := by
  intro ops
  induction ops with
  | nil => intro _; rfl
  | cons op ops ih =>
    intro start
    cases op with
    | gates gs => simp [lookupProgram, residue_append, residue_gateProgram, ih, lookupOpResidue]
    | erase a b t => simp [lookupProgram, residue_cast, residue_append, ih, lookupOpResidue]

theorem residue_collect {n : Nat}
    (next : (cursor : Nat) → List (Fin cursor) → (count : Nat) × Straight n cursor (cursor+count))
    (hn : ∀ cursor prior, residue (next cursor prior).2 = 0) :
    ∀ (ws : List Wire) (start : Nat) (prior : List (Fin start)),
      residue (collectProgram n next ws start prior).2 = 0 := by
  intro ws
  induction ws with
  | nil => intro start prior; exact hn start prior
  | cons w ws ih =>
    intro start prior
    simp only [collectProgram, residue_cast, residue]
    exact ih _ _

/-! ## Phase-free literal leaves -/

@[simp] theorem sum_controlledAddCarry (bs as : List Wire) (q c f : Wire) :
    ((controlledAddCarry bs as q c f).map primitivePhaseCost).sum = 0 :=
  primitivePhaseCost_of_HPFree _ (controlledAddCarry_HPFree bs as q c f)

@[simp] theorem sum_controlledSubCarry (bs as : List Wire) (q c f : Wire) :
    ((controlledSubCarry bs as q c f).map primitivePhaseCost).sum = 0 :=
  primitivePhaseCost_of_HPFree _ (controlledSubCarry_HPFree bs as q c f)

@[simp] theorem sum_controlledCompareLT (l r : List Wire) (q c f : Wire) :
    ((controlledCompareLT l r q c f).map primitivePhaseCost).sum = 0 :=
  primitivePhaseCost_of_HPFree _ (controlledCompareLT_HPFree l r q c f)

@[simp] theorem sum_doublingShift (acc : List Wire) (f : Wire) :
    ((doublingShift acc f).map primitivePhaseCost).sum = 0 :=
  primitivePhaseCost_of_HPFree _ (doublingShift_HPFree acc f)

@[simp] theorem sum_doublingShift_adjoint (acc : List Wire) (f : Wire) :
    (((doublingShift acc f).adjoint).map primitivePhaseCost).sum = 0 :=
  phaseFree_adjoint (sum_doublingShift acc f)

@[simp] theorem sum_controlledComplement (input : List Wire) (q : Wire) :
    ((controlledComplement input q).map primitivePhaseCost).sum = 0 := by
  unfold controlledComplement
  induction input with
  | nil => rfl
  | cons w ws ih => simpa [primitivePhaseCost] using ih

@[simp] theorem sum_workRegistersPrepare : (workRegistersPrepare.map primitivePhaseCost).sum = 0 :=
  primitivePhaseCost_of_HPFree _ workRegistersPrepare_resources.2.1

@[simp] theorem sum_workRegistersRestore : (workRegistersRestore.map primitivePhaseCost).sum = 0 :=
  primitivePhaseCost_of_HPFree _ workRegistersRestore_resources.2.1

@[simp] theorem sum_eeaLengthSetup : (eeaLengthSetup.map primitivePhaseCost).sum = 0 := by
  apply primitivePhaseCost_of_HPFree
  simp only [eeaLengthSetup, Classical.hpFree_append]
  exact ⟨⟨xorConstant_HPFree _ _, xorConstant_HPFree _ _⟩, lengthInitialize_HPFree _ _ _ _ _⟩

@[simp] theorem sum_eeaLengthUndo : (eeaLengthUndo.map primitivePhaseCost).sum = 0 := by
  apply primitivePhaseCost_of_HPFree
  simp only [eeaLengthUndo, Classical.hpFree_append]
  exact ⟨⟨lengthInitialize_HPFree _ _ _ _ _, xorConstant_HPFree _ _⟩, xorConstant_HPFree _ _⟩

@[simp] theorem sum_terminalEpochCompression :
    (terminalEpochCompression.map primitivePhaseCost).sum = 0 := by
  apply primitivePhaseCost_of_HPFree
  simp [terminalEpochCompression, mcxVChain_HPFree]

@[simp] theorem sum_terminalWork1Clear : (terminalWork1Clear.map primitivePhaseCost).sum = 0 :=
  primitivePhaseCost_of_HPFree _ (xorConstant_HPFree _ _)

@[simp] theorem sum_canonicalWork2Rotation :
    (canonicalWork2Rotation.map primitivePhaseCost).sum = 0 :=
  primitivePhaseCost_of_HPFree _ canonicalWork2Rotation_HPFree

@[simp] theorem sum_canonicalWork2InverseRotation :
    (canonicalWork2InverseRotation.map primitivePhaseCost).sum = 0 :=
  primitivePhaseCost_of_HPFree _ canonicalWork2InverseRotation_HPFree

@[simp] theorem sum_fig15SwapOutput : (fig15SwapOutput.map primitivePhaseCost).sum = 0 := by
  apply primitivePhaseCost_of_HPFree
  intro g hg
  simp only [fig15SwapOutput, List.mem_flatMap] at hg
  obtain ⟨i, hi, hg⟩ := hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> trivial

@[simp] theorem sum_fig15ZeroPrepare : (fig15ZeroPrepare.map primitivePhaseCost).sum = 0 := by
  apply primitivePhaseCost_of_HPFree
  rw [fig15ZeroPrepare, nonzeroInputPrepare, Classical.hpFree_append]
  exact ⟨computeEqConst_HPFree _ _ _ _, by simp [Classical.HPFree]⟩

@[simp] theorem sum_fig15ZeroRestore : (fig15ZeroRestore.map primitivePhaseCost).sum = 0 := by
  apply primitivePhaseCost_of_HPFree
  rw [fig15ZeroRestore, nonzeroInputRestore, Classical.hpFree_append]
  exact ⟨by simp [Classical.HPFree], computeEqConst_HPFree _ _ _ _⟩

@[simp] theorem sum_signedAddressCircuit (q sign : Wire) (bits : List Wire) :
    ((signedAddressCircuit q sign bits).map primitivePhaseCost).sum = 0 :=
  primitivePhaseCost_of_HPFree _ (signedAddressCircuit_HPFree q sign bits)

@[simp] theorem sum_zeroMask (register : List Wire) (value : Nat) :
    ((zeroMask register value).map primitivePhaseCost).sum = 0 :=
  primitivePhaseCost_of_HPFree _ (zeroMask_HPFree register value)

/-! ## Gidney adders and comparators -/

theorem pf_flipWord (ws : List Wire) : PhaseFree (gidneyFlipWord ws) := by
  unfold PhaseFree gidneyFlipWord
  induction ws with
  | nil => rfl
  | cons w ws ih => simpa [primitivePhaseCost] using ih

theorem pf_constCarryXor (input dirty : List Wire) (constant : List Bool) (q c : Wire) :
    PhaseFree (controlledConstCarryXor input dirty constant q c) :=
  controlledConstCarryXor_cost_zero primitivePhaseCost (fun _ _ => rfl) (fun _ _ _ => rfl)
    input dirty constant q c

theorem pf_addCleanup (input dirty : List Wire) (constant : List Bool) (q c : Wire) :
    PhaseFree (gidneyAddCleanup input dirty constant q c) := by
  unfold gidneyAddCleanup
  exact phaseFree_append (phaseFree_append (pf_flipWord _) (pf_constCarryXor _ _ _ _ _))
    (pf_flipWord _)

theorem pf_addCarryCell (q c s a i d : Wire) (k : Bool) :
    PhaseFree (gidneyAddCarryCell q c s a i d k) := by
  unfold PhaseFree gidneyAddCarryCell; cases k <;> simp [primitivePhaseCost]

theorem pf_compareCarryCell (q c s a i d f : Wire) (k last : Bool) :
    PhaseFree (gidneyCompareCarryCell q c s a i d f k last) := by
  unfold PhaseFree gidneyCompareCarryCell; cases k <;> cases last <;> simp [primitivePhaseCost]

theorem pf_gidneyCells (q : Wire) :
    ∀ (as ds : List Wire) (ks : List Bool) (cur sp anc : Wire),
      ∀ c ∈ gidneyCarryCells q cur sp anc as ds ks, PhaseFree c.1 := by
  intro as
  induction as with
  | nil => intro ds ks cur sp anc c hc; simp [gidneyCarryCells] at hc
  | cons a as ih =>
    intro ds ks cur sp anc c hc
    cases ds with
    | nil =>
      cases as with
      | nil =>
        cases ks with
        | nil => simp [gidneyCarryCells] at hc
        | cons k ks =>
          cases ks with
          | nil =>
            simp only [gidneyCarryCells, List.mem_singleton] at hc; subst hc
            unfold PhaseFree; cases k <;> simp [primitivePhaseCost]
          | cons k' ks => simp [gidneyCarryCells] at hc
      | cons b bs => cases ks <;> simp [gidneyCarryCells] at hc
    | cons d ds =>
      cases ks with
      | nil => cases as <;> simp [gidneyCarryCells] at hc
      | cons k ks =>
        have hc' : c = (gidneyAddCarryCell q cur sp anc a d k, cur) ∨
            c ∈ gidneyCarryCells q sp cur anc as ds ks := by
          cases as <;> simpa [gidneyCarryCells] using hc
        rcases hc' with rfl | hc'
        · exact pf_addCarryCell _ _ _ _ _ _ _
        · exact ih ds ks sp cur anc c hc'

theorem pf_compareCells (q f : Wire) :
    ∀ (as ds : List Wire) (ks : List Bool) (cur sp anc : Wire),
      ∀ c ∈ compareCarryCells q cur sp anc f as ds ks, PhaseFree c.1 := by
  intro as
  induction as with
  | nil =>
    intro ds ks cur sp anc c hc
    cases ds <;> cases ks <;> simp [compareCarryCells] at hc
    subst hc; exact phaseFree_nil
  | cons a as ih =>
    intro ds ks cur sp anc c hc
    cases ds with
    | nil => cases ks <;> simp [compareCarryCells] at hc
    | cons d ds =>
      cases ks with
      | nil => simp [compareCarryCells] at hc
      | cons k ks =>
        simp only [compareCarryCells, List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact pf_compareCarryCell _ _ _ _ _ _ _ _ _
        · exact ih ds ks sp cur anc c hc

@[simp] theorem residue_gidney (n start : Nat) (input dirty : List Wire) (constant : List Bool)
    (q carry spare ancilla : Wire) :
    residue (gidneyProgram n start input dirty constant q carry spare ancilla).2 = 0 := by
  change compiledResidue (gidneyProgram n start input dirty constant q carry spare ancilla) = 0
  unfold gidneyProgram
  split
  · rfl
  · split
    · exact residue_literal_pf (by unfold PhaseFree; split <;> simp [primitivePhaseCost])
    · show residue (gidneyNontrivialProgram _ _ _ _ _ _ _ _ _ _ _ _) = 0
      unfold gidneyNontrivialProgram
      rw [residue_append, residue_literal_pf (pf_addCarryCell _ _ _ _ _ _ _), Nat.zero_add]
      exact residue_deferred n _ _ (pf_addCleanup _ _ _ _ _) _ (pf_gidneyCells q _ _ _ _ _ _) _ _
    · rfl

@[simp] theorem residue_compareCore (n start : Nat) (input dirty : List Wire) (constant : List Bool)
    (q carry spare ancilla flag : Wire) :
    residue (compareCoreProgram n start input dirty constant q carry spare ancilla flag).2 = 0 := by
  change compiledResidue (compareCoreProgram n start input dirty constant q carry spare ancilla flag) = 0
  unfold compareCoreProgram
  split
  · show residue (compareCarryProgram _ _ _ _ _ _ _ _ _ _ _ _ _) = 0
    unfold compareCarryProgram
    rw [residue_append, residue_literal_pf (pf_compareCarryCell _ _ _ _ _ _ _ _ _), Nat.zero_add]
    exact residue_deferred n _ _ (pf_constCarryXor _ _ _ _ _) _ (pf_compareCells q flag _ _ _ _ _ _) _ _
  · rfl

@[simp] theorem residue_compareGE (n start : Nat) (input dirty : List Wire) (threshold : Nat)
    (q carry spare ancilla flag : Wire) :
    residue (compareGEProgram n start input dirty threshold q carry spare ancilla flag).2 = 0 := by
  change compiledResidue (compareGEProgram n start input dirty threshold q carry spare ancilla flag) = 0
  unfold compareGEProgram
  split
  · exact residue_literal_pf (by unfold PhaseFree; simp [primitivePhaseCost])
  · split
    · rfl
    · exact residue_compareCore n start input dirty _ q carry spare ancilla flag

@[simp] theorem residue_uncontrolledCompare (n start : Nat) (input dirty : List Wire) (threshold : Nat)
    (carry spare ancilla flag : Wire) :
    residue (uncontrolledCompareProgram n start input dirty threshold carry spare ancilla flag).2 = 0 := by
  unfold uncontrolledCompareProgram
  have h := residue_constantStraight (gidneyCompareVirtualControl input dirty carry spare ancilla flag)
    (compareGEProgram n start input dirty threshold
      (gidneyCompareVirtualControl input dirty carry spare ancilla flag) carry spare ancilla flag).2
  rw [residue_compareGE] at h
  exact Nat.le_zero.mp h

/-! ## Modular arithmetic -/

@[simp] theorem residue_modularAdd (n start : Nat) (input acc : List Wire) (correction : List Bool)
    (modulus : Nat) (q carry spare ancilla flag : Wire) :
    residue (modularAddProgram n start input acc correction modulus q carry spare ancilla flag).2 = 0 := by
  simp [modularAddProgram, residue_append, residue_literal]

@[simp] theorem residue_modularNegate (n start : Nat) (target dirty : List Wire) (modulus : List Bool)
    (q c r t f : Wire) :
    residue (modularNegateProgram n start target dirty modulus q c r t f).2 = 0 := by
  simp [modularNegateProgram]

@[simp] theorem residue_negativeNegate (n start : Nat) (target dirty : List Wire) (modulus : List Bool)
    (q c r t f : Wire) :
    residue (negativeNegateProgram n start target dirty modulus q c r t f).2 = 0 := by
  simp [negativeNegateProgram, residue_literal, primitivePhaseCost]

@[simp] theorem residue_modularSub (n start : Nat) (input acc : List Wire) (modulus : List Bool)
    (p : Nat) (q c r t f : Wire) :
    residue (modularSubProgram n start input acc modulus p q c r t f).2 = 0 := by
  simp [modularSubProgram, residue_literal]

@[simp] theorem residue_modularDouble (n start : Nat) (acc dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) :
    residue (modularDoubleProgram n start acc dirty bits p c r t f).2 = 0 := by
  cases acc with
  | nil => rfl
  | cons a rest => simp [modularDoubleProgram, residue_literal, primitivePhaseCost]

@[simp] theorem residue_modularHalve (n start : Nat) (acc dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) :
    residue (modularHalveProgram n start acc dirty bits p c r t f).2 = 0 := by
  cases acc with
  | nil => rfl
  | cons a rest => simp [modularHalveProgram, residue_literal, primitivePhaseCost]

@[simp] theorem residue_horner (n : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (start : Nat) :
    residue (hornerProgram n start controls input acc bits p c r t f).2 = 0 := by
  induction controls generalizing start with
  | nil => rfl
  | cons q qs ih => simp [hornerProgram, ih]

@[simp] theorem residue_hornerInverse (n : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (start : Nat) :
    residue (hornerInverseProgram n start controls input acc bits p c r t f).2 = 0 := by
  induction controls generalizing start with
  | nil => rfl
  | cons q qs ih => simp [hornerInverseProgram, ih]

@[simp] theorem residue_squareAdd (n start : Nat) (input acc : List Wire) (bits : List Bool)
    (p : Nat) (q copied c r t f : Wire) :
    residue (squareAddProgram n start input acc bits p q copied c r t f).2 = 0 := by
  simp [squareAddProgram, residue_literal, primitivePhaseCost]

@[simp] theorem residue_squareSub (n start : Nat) (input acc : List Wire) (bits : List Bool)
    (p : Nat) (q copied c r t f : Wire) :
    residue (squareSubProgram n start input acc bits p q copied c r t f).2 = 0 := by
  simp [squareSubProgram, residue_literal, primitivePhaseCost]

@[simp] theorem residue_square (n : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (copied c r t f : Wire) (start : Nat) :
    residue (squareProgram n start controls input acc bits p copied c r t f).2 = 0 := by
  induction controls generalizing start with
  | nil => rfl
  | cons q qs ih => simp [squareProgram, ih]

@[simp] theorem residue_squareInverse (n : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (copied c r t f : Wire) (start : Nat) :
    residue (squareInverseProgram n start controls input acc bits p copied c r t f).2 = 0 := by
  induction controls generalizing start with
  | nil => rfl
  | cons q qs ih => simp [squareInverseProgram, ih]

@[simp] theorem residue_squareSubtract (n start : Nat) (x y acc : List Wire)
    (correction modulus : List Bool) (p : Nat) (q copied c r t f : Wire) :
    residue (squareSubtractProgram n start x y acc correction modulus p q copied c r t f).2 = 0 := by
  simp [squareSubtractProgram]

@[simp] theorem residue_doublesProgram (n k start : Nat) (acc dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) :
    residue (ShorECDLP.Entrant.SquareInPlace.doublesProgram n k start acc dirty bits p c r t f).2 = 0 := by
  induction k generalizing start with
  | zero => simp only [ShorECDLP.Entrant.SquareInPlace.doublesProgram, residue_done]
  | succ k ih => simp [ShorECDLP.Entrant.SquareInPlace.doublesProgram, residue_compiled, ih]

@[simp] theorem residue_padsProgram (n k start : Nat) (w : Wire) :
    residue (ShorECDLP.Entrant.SquareInPlace.padsProgram n k start w).2 = 0 := by
  induction k generalizing start with
  | zero => simp only [ShorECDLP.Entrant.SquareInPlace.padsProgram, residue_done]
  | succ k ih => simp [ShorECDLP.Entrant.SquareInPlace.padsProgram, residue_compiled, residue, ih]

@[simp] theorem residue_paddedSquare (n start : Nat) :
    residue (ShorECDLP.Entrant.SquareInPlace.paddedSquareProgram n start).2 = 0 := by
  unfold ShorECDLP.Entrant.SquareInPlace.paddedSquareProgram ShorECDLP.Entrant.SquareInPlace.inPlaceSquareProgram
  simp only [residue_compiled, residue_squareInverse, residue_doublesProgram, residue_padsProgram]

attribute [local irreducible] ShorECDLP.Entrant.SquareInPlace.paddedSquareProgram in
theorem paddedSquareCount (n start : Nat) :
    AtLeast (ShorECDLP.Entrant.SquareInPlace.paddedSquareProgram n start).2 1500938 := by
  have hr := residue_t (ShorECDLP.Entrant.SquareInPlace.paddedSquareProgram n start).2 (fun _ => false) (fun _ => false)
  have ht := ShorECDLP.Entrant.SquareInPlace.paddedSquareProgram_tCount n start (fun _ => false) (fun _ => false)
  rw [ShorECDLP.Entrant.SquareInPlace.paddedSquare_counts.1] at ht
  have hz := residue_paddedSquare n start
  unfold AtLeast compiledTCount at *
  omega


/-! ## EEA wrappers -/

@[simp] theorem residue_constMinus (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (q c r t : Wire) :
    residue (constMinusProgram n start input dirty bits q c r t).2 = 0 := by
  simp [constMinusProgram]

@[simp] theorem residue_eeaCenter (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t iter : Wire) :
    residue (eeaCenterProgram n start input dirty bits p c r t iter).2 = 0 := by
  simp [eeaCenterProgram]

@[simp] theorem residue_eeaUncenter (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t iter : Wire) :
    residue (eeaUncenterProgram n start input dirty bits p c r t iter).2 = 0 := by
  simp [eeaUncenterProgram]

@[simp] theorem residue_eeaParity (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (c r t iter : Wire) :
    residue (eeaParityProgram n start input dirty bits c r t iter).2 = 0 := by
  simp [eeaParityProgram, residue_literal, primitivePhaseCost]

theorem residue_preprocess (n start : Nat) : residue (preprocessProgram n start).2 = 0 := by
  unfold preprocessProgram
  rw [residue_surround, residue_eeaCenter, sum_workRegistersPrepare, sum_eeaLengthSetup]

theorem residue_unpreprocess (n start : Nat) : residue (unpreprocessProgram n start).2 = 0 := by
  unfold unpreprocessProgram
  rw [residue_surround, residue_eeaUncenter, sum_eeaLengthUndo, sum_workRegistersRestore]

theorem residue_productionParity (n start : Nat) :
    residue (productionParityProgram n start).2 = 0 := by
  unfold productionParityProgram
  exact residue_eeaParity _ _ _ _ _ _ _ _ _

attribute [local irreducible] terminalWork1Clear

theorem residue_measuredForwardWrapper (n start : Nat) :
    residue (measuredForwardWrapperProgram n start).2 = 0 := by
  unfold measuredForwardWrapperProgram
  apply residue_sequence
  intro p hp s
  simp only [measuredForwardWrapperSegments, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h | h | h | h | h <;> subst p
  · exact residue_preprocess n s
  · exact residue_measuredSchedule _ _ _ _ _ _
  · show residue (literalProgram _) = 0
    rw [residue_literal, List.map_append, List.sum_append, sum_canonicalWork2Rotation,
      sum_terminalEpochCompression]
  · exact residue_productionParity n s
  · exact (residue_literal _).trans sum_terminalWork1Clear

theorem residue_measuredReverseWrapper (n start : Nat) :
    residue (measuredReverseWrapperProgram n start).2 = 0 := by
  unfold measuredReverseWrapperProgram
  apply residue_sequence
  intro p hp s
  simp only [measuredReverseWrapperSegments, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h | h | h | h | h <;> subst p
  · exact (residue_literal _).trans sum_terminalWork1Clear
  · exact residue_productionParity n s
  · show residue (literalProgram _) = 0
    rw [residue_literal, List.map_append, List.sum_append, sum_terminalEpochCompression,
      sum_canonicalWork2InverseRotation]
  · exact residue_measuredInverseSchedule _ _ _ _ _
  · exact residue_unpreprocess n s

theorem residue_measuredForwardDataBank (n start : Nat) :
    residue (measuredForwardDataBankProgram n start).2 = 0 := by
  unfold measuredForwardDataBankProgram relabelCompiled
  rw [residue_relabel]
  exact residue_measuredForwardWrapper n start

theorem residue_measuredReverseDataBank (n start : Nat) :
    residue (measuredReverseDataBankProgram n start).2 = 0 := by
  unfold measuredReverseDataBankProgram relabelCompiled
  rw [residue_relabel]
  exact residue_measuredReverseWrapper n start

/-! ## In-place division and multiplication -/

theorem residue_multiplyWork (n start : Nat) : residue (multiplyWorkProgram n start).2 = 0 := by
  unfold multiplyWorkProgram; apply residue_horner

theorem residue_multiplyData (n start : Nat) : residue (multiplyDataProgram n start).2 = 0 := by
  unfold multiplyDataProgram; apply residue_horner

theorem residue_unmultiplyData (n start : Nat) :
    residue (unmultiplyDataProgram n start).2 = 0 := by
  unfold unmultiplyDataProgram; apply residue_hornerInverse

attribute [local irreducible] measuredForwardWrapperProgram measuredReverseWrapperProgram
  measuredForwardDataBankProgram measuredReverseDataBankProgram multiplyDataProgram
  multiplyWorkProgram unmultiplyDataProgram

theorem residue_correctionCompiled (n start : Nat) (ws : List Wire) (prior : List (Fin start)) :
    residue (correctionCompiled n start ws prior).2 = 0 := by
  unfold correctionCompiled
  exact (residue_registerCorrection ws prior _).trans rfl

theorem residue_app {n start : Nat} (p : (count : Nat) × Straight n start (start+count))
    (q : (count : Nat) × Straight n (start+p.1) (start+p.1+count))
    (hp : residue p.2 = 0) (hq : residue q.2 = 0) : residue (appendCompiled p q).2 = 0 := by
  rw [residue_compiled, hp, hq]

 theorem residue_appendLiteral {n start}
     (p : (count : Nat) × Straight n start (start+count)) (gs : Circuit)
     (hp : residue p.2 = 0) (hg : (gs.map primitivePhaseCost).sum = 0) :
     residue (ChallengeMigration.appendLiteral p gs).2 = 0 :=
   residue_app p ⟨0,literalProgram gs⟩ hp (residue_literal_pf hg)

theorem residue_divisionCleanup (n start : Nat) :
    residue (divisionCleanupProgram n start).2 = 0 := by
  unfold divisionCleanupProgram appendLiteral
  exact residue_app _ _ (residue_unmultiplyData _ _) (residue_literal_pf sum_fig15SwapOutput)

theorem residue_divisionCorrection (n start : Nat) (prior : List (Fin start)) :
    residue (divisionCorrectionProgram n start prior).2 = 0 := by
  unfold divisionCorrectionProgram
  exact residue_app _ _ (residue_correctionCompiled _ _ _ _) (residue_divisionCleanup _ _)

theorem residue_divisionAfterReset (n start : Nat) (prior : List (Fin start)) :
    residue (divisionAfterResetProgram n start prior).2 = 0 := by
  unfold divisionAfterResetProgram appendRetaining
  exact residue_app _ _
    (residue_app _ _ (residue_measuredReverseDataBank _ _) (residue_multiplyData _ _))
    (residue_divisionCorrection _ _ _)

attribute [local irreducible] divisionAfterResetProgram

theorem residue_division (n start : Nat) : residue (divisionProgram n start).2 = 0 := by
  unfold divisionProgram
  exact residue_app _ _
    (residue_app _ _ (residue_measuredForwardWrapper _ _) (residue_multiplyWork _ _))
    (residue_collect _ (residue_divisionAfterReset n) _ _ _)

theorem residue_multiplicationCleanup (n start : Nat) :
    residue (multiplicationCleanupProgram n start).2 = 0 := by
  unfold multiplicationCleanupProgram
  exact residue_app _ _ (FullCredit.residue_unmultiplyData _ _)
    (residue_appendLiteral _ _ (residue_measuredReverseDataBank _ _) sum_fig15SwapOutput)

theorem residue_multiplicationCorrection (n start : Nat) (prior : List (Fin start)) :
    residue (multiplicationCorrectionProgram n start prior).2 = 0 := by
  unfold multiplicationCorrectionProgram
  exact residue_app _ _ (residue_correctionCompiled _ _ _ _) (residue_multiplicationCleanup _ _)

theorem residue_multiplicationAfterReset (n start : Nat) (prior : List (Fin start)) :
    residue (multiplicationAfterResetProgram n start prior).2 = 0 := by
  unfold multiplicationAfterResetProgram appendRetaining
  exact residue_app _ _
    (residue_app _ _ (residue_measuredForwardDataBank _ _) (residue_multiplyData _ _))
    (residue_multiplicationCorrection _ _ _)

attribute [local irreducible] multiplicationAfterResetProgram

theorem residue_multiplication (n start : Nat) :
    residue (multiplicationProgram n start).2 = 0 := by
  unfold multiplicationProgram
  exact residue_app _ _ (residue_multiplyWork _ _)
    (residue_collect _ (residue_multiplicationAfterReset n) _ _ _)

/-! ## Lookups -/

@[simp] theorem lookupOpResidue_gates {n : Nat} (gs : List (TemplateGate n)) :
    lookupOpResidue (.gates gs) = (gs.map templateResidue).sum := rfl

@[simp] theorem lookupOpResidue_erase {n : Nat} (a b t : Wire) :
    lookupOpResidue (n := n) (.erase a b t) = 0 := rfl

@[simp] theorem lookupOpResidue_ordinary {n : Nat} (gs : Circuit) :
    lookupOpResidue (ordinaryOp (n := n) gs) = (gs.map primitivePhaseCost).sum := by
  unfold ordinaryOp lookupOpResidue
  induction gs with
  | nil => rfl
  | cons g gs ih => simp only [List.map_cons, List.sum_cons, templateResidue] at ih ⊢; rw [ih]

theorem tres_lookupLeaf {n : Nat} (q : Wire) (ports : List (ConstantBit n × Wire)) :
    ((lookupLeafGates q ports).map templateResidue).sum = 0 := by
  unfold lookupLeafGates
  induction ports with
  | nil => rfl
  | cons p ps ih => simpa [templateResidue, tCost] using ih

theorem opsResidue_unary {n : Nat} (leaf : Nat → Wire → List (TemplateGate n))
    (hl : ∀ l q, ((leaf l q).map templateResidue).sum = 0) :
    ∀ (tree : UnaryActionTree) (q : Wire) (path : List Wire),
      ((unaryLookupOps leaf tree q path).map lookupOpResidue).sum = 0 := by
  intro tree
  induction tree with
  | leaf l => intro q path; simp [unaryLookupOps, hl]
  | node bit zero one ihz iho =>
    intro q path
    cases path with
    | nil => simp [unaryLookupOps]
    | cons p ps =>
      simp [unaryLookupOps, ihz, iho, computeZeroAnd, primitivePhaseCost]

theorem residue_fieldLoad (field : PointField) (start : Nat) :
    residue (fieldLoadProgram field start) = 0 := by
  rw [fieldLoadProgram, residue_cast, residue_lookup, fieldLoadOps]
  exact opsResidue_unary _ (fun l q => tres_lookupLeaf _ _) _ _ _

theorem residue_fieldLookupAdd (field : PointField) (acc : List Wire) (start : Nat) :
    residue (fieldLookupAddProgram field acc start).2 = 0 := by
  unfold fieldLookupAddProgram
  simp only [residue_compiled, residue_fieldLoad, residue_modularAdd]

theorem residue_firstLookup (start : Nat) : residue (firstLookupProgram start) = 0 := by
  rw [firstLookupProgram, residue_cast, residue_lookup, firstLookupOps]
  exact opsResidue_unary _ (fun l q => tres_lookupLeaf _ _) _ _ _


theorem residue_first17Lookup (start : Nat) : residue (First17.program start) = 0 := by
  rw [First17.program, residue_cast, residue_lookup, First17.ops]
  exact opsResidue_unary _ (fun l q => tres_lookupLeaf _ _) _ _ _

/-! ## Window coordinates -/

theorem residue_yNegate (start : Nat) : residue (yNegateProgram start).2 = 0 := by
  unfold yNegateProgram; apply residue_negativeNegate

theorem residue_signedField (field : PointField) (start : Nat) :
    residue (signedFieldProgram field start).2 = 0 := by
  unfold signedFieldProgram
  simp only [residue_compiled, residue_yNegate, residue_fieldLookupAdd]

theorem residue_xNegate (n start : Nat) : residue (xNegateProgram n start).2 = 0 := by
  unfold xNegateProgram; apply residue_modularNegate

theorem residue_pointSquare (n start : Nat) : residue (pointSquareProgram n start).2 = 0 := by
  unfold pointSquareProgram; apply residue_squareSubtract

end
end ShorECDLP.Entrant.FullCredit
end
end

section

/-! EDITABLE. Zero residue for complete signed windows.

The window bodies add lookups, the zero-allowed field guards and the endpoint correction block
around the arithmetic of `Credit`.  With every block free of phase instructions and of
constant- or record-controlled non-Clifford gates, each window's exact T-count is carried by
its literal Toffoli gates alone, which credits all of them to the lowering. -/

section
namespace ShorECDLP.Entrant.FullCredit
open Quantum Challenge AndGadget Paper2607_13816 Paper2607_13816.ChallengeMigration ShorECDLP.Secp256k1
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

@[simp] theorem opsResidue_measuredTail {n : Nat} (a : Wire) (cs : List Wire) (t : Wire) (ws : List Wire) :
    ((measuredTailOps (n := n) a cs t ws).map lookupOpResidue).sum = 0 := by
  induction cs generalizing a ws with
  | nil => rfl
  | cons c cs ih => cases cs with
    | nil => simp [measuredTailOps, primitivePhaseCost]
    | cons d cs => cases ws <;> simp [measuredTailOps, ih, primitivePhaseCost]

@[simp] theorem opsResidue_measuredChain {n : Nat} (cs : List Wire) (t : Wire) (ws : List Wire) :
    ((measuredChainOps (n := n) cs t ws).map lookupOpResidue).sum = 0 := by
  cases cs with
  | nil => simp [measuredChainOps, primitivePhaseCost]
  | cons a cs => cases cs <;> simp [measuredChainOps, primitivePhaseCost]

@[simp] theorem opsResidue_measuredEquality {n : Nat} (r : List Wire) (v : Nat) (t : Wire) (ws : List Wire) :
    ((measuredEqualityOps (n := n) r v t ws).map lookupOpResidue).sum = 0 := by
  simp [measuredEqualityOps]

@[simp] theorem opsResidue_measuredTest {n : Nat} (k : Fin 4) :
    ((ipxMeasuredTestOps (n := n) k).map lookupOpResidue).sum = 0 := by
  simp [ipxMeasuredTestOps]

@[simp] theorem residue_equality (n start : Nat) (r : List Wire) (v : Nat) (t : Wire) (ws : List Wire) :
    residue (equalityProgram n start r v t ws).2 = 0 := by
  simp [equalityProgram, residue_literal]

@[simp] theorem residue_borrowPrepare (n start : Nat) :
    residue (BorrowFlag.prepareProgram n start).2 = 0 := by
  simp [BorrowFlag.prepareProgram, residue_literal, ZeroAdaptive.cx, primitivePhaseCost]

@[simp] theorem residue_borrowRestore (n start : Nat) :
    residue (BorrowFlag.restoreProgram n start).2 = 0 := by
  simp [BorrowFlag.restoreProgram, ZeroAdaptive.cx, primitivePhaseCost]

theorem residue_borrowField (n start : Nat) (arithmetic : FixedSegment n)
    (ha : ∀ cursor, residue (arithmetic cursor).2 = 0) :
    residue (BorrowFlag.fieldProgram n start arithmetic).2 = 0 := by
  unfold BorrowFlag.fieldProgram
  simp only [residue_surround, BorrowFlag.flip, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, primitivePhaseCost, Nat.zero_add, Nat.add_zero]
  apply residue_sequence
  intro p hp s
  simp only [BorrowFlag.coreSegments,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with h | h | h <;> subst p
  · simp [relabelCompiled, residue_relabel]
  · exact ha s
  · simp [relabelCompiled, residue_relabel]

namespace MeasuredCredit
open MeasuredQuotient

private theorem leaf_classical (r : QuotientSwapRegisters) (k l : Nat) (c : Wire) :
    Classical.HPFree (quotientSwapLeaf r k l c) :=
  controlledSwap_HPFree c r.sign (r.workAt k l)

@[simp] theorem residue_program (n start : Nat) (r : QuotientSwapRegisters) (k K : Nat) :
    residue (MeasuredQuotient.program n start r k K).2 = 0 := by
  unfold MeasuredQuotient.program
  rw [residue_surround]
  have hl : residue (unaryProgram n .inc
      (fun label control _ => ⟨0,literalProgram (quotientSwapLeaf r k label control)⟩)
      (quotientSwapTree r k K) r.control (r.path k K) start).2 = 0 :=
    residue_unary n .inc _ (fun l c s => residue_literal_HPFree _ (leaf_classical r k l c)) _ _ _ _
  rw [hl]
  simp [primitivePhaseCost_of_HPFree,Classical.hpFree_append,
    cuccaroAdd_HPFree,cuccaroSub_HPFree,addConstant_HPFree,subConstant_HPFree]

@[simp] theorem residue_d2Program (n start : Nat) (r : IndexedStepRegisters) (w : ActiveWindow) :
    residue (MeasuredQuotient.d2Program n start r w).2 = 0 := by
  simp [MeasuredQuotient.d2Program,residue_surround,MeasuredQuotient.before,
    MeasuredQuotient.after,primitivePhaseCost]

private theorem d1_classical (r : IndexedStepRegisters) : Classical.HPFree (blockD1Forward r) := by
  have h := indexedStepUnitary_HPFree r 256 0
  simp only [indexedStepUnitary,blockDForward,Classical.hpFree_append] at h
  tauto
private theorem d3_classical (r : IndexedStepRegisters) : Classical.HPFree (blockD3Forward r) := by
  have h := indexedStepUnitary_HPFree r 256 0
  simp only [indexedStepUnitary,blockDForward,Classical.hpFree_append] at h
  tauto

@[simp] theorem residue_dProgram (n start : Nat) (r : IndexedStepRegisters) (w : ActiveWindow) :
    residue (MeasuredQuotient.dProgram n start r w).2 = 0 := by
  simp [MeasuredQuotient.dProgram,residue_surround,primitivePhaseCost_of_HPFree,
    d1_classical,d3_classical]

private theorem blockA_classical (r : IndexedStepRegisters) : Classical.HPFree (blockAForward r) := by
  have h := indexedStepUnitary_HPFree r 256 1
  simp only [indexedStepUnitary, Classical.hpFree_append] at h
  tauto

private theorem blockC_classical (r : IndexedStepRegisters) : Classical.HPFree (blockCForward r) := by
  have h := indexedStepUnitary_HPFree r 256 1
  simp only [indexedStepUnitary, Classical.hpFree_append] at h
  tauto

private theorem blockF_classical (r : IndexedStepRegisters) : Classical.HPFree (blockFForward r) := by
  have h := indexedStepUnitary_HPFree r 256 1
  simp only [indexedStepUnitary, Classical.hpFree_append] at h
  tauto

@[simp] theorem residue_cdProgram (n start : Nat) (r : IndexedStepRegisters) (width T : Nat) :
    residue (MeasuredQuotient.cdProgram n start r width T).2 = 0 := by
  simp [MeasuredQuotient.cdProgram,residue_prepend,primitivePhaseCost_of_HPFree,blockC_classical]

@[simp] theorem residue_stepProgram (n start : Nat) (r : IndexedStepRegisters) (width T : Nat) :
    residue (MeasuredQuotient.stepProgram n start r width T).2 = 0 := by
  simp [MeasuredQuotient.stepProgram,MeasuredQuotient.stepSegments,sequenceProgram,residue_literal,primitivePhaseCost,primitivePhaseCost_of_HPFree,blockA_classical,blockF_classical]

@[simp] theorem residue_scheduleProgram (n : Nat) (r : IndexedStepRegisters)
    (width count first start : Nat) :
    residue (MeasuredQuotient.scheduleProgram n r width count first start).2 = 0 := by
  induction count generalizing first start with
  | zero => simp [MeasuredQuotient.scheduleProgram,residue_literal]
  | succ count ih => simp only [MeasuredQuotient.scheduleProgram,residue_compiled,
      residue_stepProgram,ih,Nat.zero_add]

attribute [local irreducible] MeasuredQuotient.scheduleProgram
private theorem forward_program_view (n start : Nat) (r : IndexedStepRegisters) :
    MeasuredQuotient.forwardProgram n start r =
      MeasuredQuotient.scheduleProgram n r 256 1620 1 start := rfl

theorem residue_forwardProgram (n start : Nat) (r : IndexedStepRegisters) :
    residue (MeasuredQuotient.forwardProgram n start r).2 = 0 := by
  rw [forward_program_view]
  exact residue_scheduleProgram n r 256 1620 1 start

attribute [local irreducible] preprocessProgram productionParityProgram terminalWork1Clear

theorem residue_wrapperProgram (n start : Nat) : residue (MeasuredQuotient.wrapperProgram n start).2 = 0 := by
  unfold MeasuredQuotient.wrapperProgram
  apply residue_sequence
  intro p hp s
  simp only [MeasuredQuotient.wrapperSegments,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact residue_preprocess n s
  · exact residue_forwardProgram n s indexedStepProductionRegisters
  · rw [residue_literal,List.map_append,List.sum_append,sum_canonicalWork2Rotation,sum_terminalEpochCompression]
  · exact residue_productionParity n s
  · exact (residue_literal _).trans sum_terminalWork1Clear

attribute [local irreducible] MeasuredQuotient.wrapperProgram multiplyWorkProgram divisionAfterResetProgram collectProgram

theorem residue_divisionProgram (n start : Nat) : residue (MeasuredQuotient.divisionProgram n start).2 = 0 := by
  unfold MeasuredQuotient.divisionProgram
  exact residue_app _ _
    (residue_app _ _ (residue_wrapperProgram _ _) (residue_multiplyWork _ _))
    (residue_collect _ (residue_divisionAfterReset n) _ _ _)

theorem divisionCount (n start : Nat) : AtLeast (MeasuredQuotient.divisionProgram n start).2 34910095 := by
  have ht := MeasuredQuotient.divisionProgram_tCount n start (fun _ => false) (fun _ => false)
  rw [MeasuredQuotient.division_T] at ht
  have hr := residue_t (MeasuredQuotient.divisionProgram n start).2 (fun _ => false) (fun _ => false)
  have hz := residue_divisionProgram n start
  unfold AtLeast compiledTCount at *
  omega
end MeasuredCredit

namespace MeasuredCredit
attribute [local irreducible] MeasuredQuotient.wrapperProgram
  multiplicationCorrectionProgram multiplyWorkProgram multiplyDataProgram collectProgram

theorem residue_bankWrapperProgram (n start : Nat) :
    residue (MeasuredQuotient.bankWrapperProgram n start).2 = 0 := by
  unfold MeasuredQuotient.bankWrapperProgram relabelCompiled
  rw [residue_relabel]
  exact residue_wrapperProgram n start

theorem residue_multiplicationAfterResetProgram (n start : Nat) (prior : List (Fin start)) :
    residue (MeasuredQuotient.multiplicationAfterResetProgram n start prior).2 = 0 := by
  unfold MeasuredQuotient.multiplicationAfterResetProgram appendRetaining
  exact residue_app _ _
    (residue_app _ _ (residue_bankWrapperProgram _ _) (residue_multiplyData _ _))
    (residue_multiplicationCorrection _ _ _)

attribute [local irreducible] MeasuredQuotient.multiplicationAfterResetProgram

theorem residue_multiplicationProgram (n start : Nat) :
    residue (MeasuredQuotient.multiplicationProgram n start).2 = 0 := by
  unfold MeasuredQuotient.multiplicationProgram
  exact residue_app _ _ (residue_multiplyWork _ _)
    (residue_collect _ (residue_multiplicationAfterResetProgram n) _ _ _)

theorem multiplicationCount (n start : Nat) :
    AtLeast (MeasuredQuotient.multiplicationProgram n start).2 34910095 := by
  have ht := MeasuredQuotient.multiplicationProgram_tCount n start (fun _ => false) (fun _ => false)
  rw [MeasuredQuotient.multiplication_T] at ht
  have hr := residue_t (MeasuredQuotient.multiplicationProgram n start).2 (fun _ => false) (fun _ => false)
  have hz := residue_multiplicationProgram n start
  unfold AtLeast compiledTCount at *
  omega
end MeasuredCredit

namespace ReverseMeasuredCredit
open MeasuredQuotient.Reverse

@[simp] theorem residue_program (n start : Nat) (r : IndexedStepRegisters) (w : ActiveWindow) :
    residue (MeasuredQuotient.Reverse.program n start r w).2 = 0 := by
  simp [MeasuredQuotient.Reverse.program,residue_surround,primitivePhaseCost_of_HPFree,
    first_HPFree,last_HPFree,MeasuredCredit.residue_d2Program]

private theorem blockB2_classical (r : IndexedStepRegisters) : Classical.HPFree (blockB2 r) := by
  have h := indexedStepUnitary_HPFree r 256 1
  simp only [indexedStepUnitary,blockBForward,Classical.hpFree_append] at h
  tauto

@[simp] theorem residue_stepProgram (n start : Nat) (r : IndexedStepRegisters) (T : Nat) :
    residue (MeasuredQuotient.Reverse.stepProgram n start r T).2 = 0 := by
  simp [MeasuredQuotient.Reverse.stepProgram,MeasuredQuotient.Reverse.stepSegments,sequenceProgram,
    residue_literal,primitivePhaseCost,primitivePhaseCost_of_HPFree,
    entryBefore_HPFree,entryAfter_HPFree,blockB2_classical]

@[simp] theorem residue_scheduleProgram (n : Nat) (r : IndexedStepRegisters)
    (count first start : Nat) :
    residue (MeasuredQuotient.Reverse.scheduleProgram n r count first start).2 = 0 := by
  induction count generalizing first start with
  | zero => rfl
  | succ count ih => simp only [MeasuredQuotient.Reverse.scheduleProgram,residue_compiled,
      residue_stepProgram,ih,Nat.zero_add]

attribute [local irreducible] MeasuredQuotient.Reverse.scheduleProgram
private theorem reverse_program_view (n start : Nat) (r : IndexedStepRegisters) :
    MeasuredQuotient.Reverse.reverseProgram n start r =
      MeasuredQuotient.Reverse.scheduleProgram n r 1620 1 start := rfl

theorem residue_reverseProgram (n start : Nat) (r : IndexedStepRegisters) :
    residue (MeasuredQuotient.Reverse.reverseProgram n start r).2 = 0 := by
  rw [reverse_program_view]
  exact residue_scheduleProgram n r 1620 1 start

attribute [local irreducible] unpreprocessProgram productionParityProgram terminalWork1Clear

theorem residue_wrapperProgram (n start : Nat) : residue (MeasuredQuotient.Reverse.wrapperProgram n start).2 = 0 := by
  unfold MeasuredQuotient.Reverse.wrapperProgram
  apply residue_sequence
  intro p hp s
  simp only [MeasuredQuotient.Reverse.wrapperSegments,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact (residue_literal _).trans sum_terminalWork1Clear
  · exact residue_productionParity n s
  · rw [residue_literal,List.map_append,List.sum_append,sum_terminalEpochCompression,sum_canonicalWork2InverseRotation]
  · exact residue_reverseProgram n s indexedStepProductionRegisters
  · exact residue_unpreprocess n s

attribute [local irreducible] MeasuredQuotient.Reverse.wrapperProgram
  divisionCorrectionProgram multiplyWorkProgram multiplyDataProgram collectProgram

theorem residue_bankWrapperProgram (n start : Nat) :
    residue (MeasuredQuotient.Reverse.bankWrapperProgram n start).2 = 0 := by
  unfold MeasuredQuotient.Reverse.bankWrapperProgram relabelCompiled
  rw [residue_relabel]
  exact residue_wrapperProgram n start

theorem residue_divisionAfterResetProgram (n start : Nat) (prior : List (Fin start)) :
    residue (MeasuredQuotient.Reverse.divisionAfterResetProgram n start prior).2 = 0 := by
  unfold MeasuredQuotient.Reverse.divisionAfterResetProgram appendRetaining
  exact residue_app _ _
    (residue_app _ _ (residue_bankWrapperProgram _ _) (residue_multiplyData _ _))
    (residue_divisionCorrection _ _ _)

attribute [local irreducible] MeasuredQuotient.Reverse.divisionAfterResetProgram MeasuredQuotient.wrapperProgram

theorem residue_divisionProgram (n start : Nat) : residue (MeasuredQuotient.Reverse.divisionProgram n start).2 = 0 := by
  unfold MeasuredQuotient.Reverse.divisionProgram
  exact residue_app _ _
    (residue_app _ _ (MeasuredCredit.residue_wrapperProgram _ _) (residue_multiplyWork _ _))
    (residue_collect _ (residue_divisionAfterResetProgram n) _ _ _)

theorem divisionCount (n start : Nat) : AtLeast (MeasuredQuotient.Reverse.divisionProgram n start).2 34668561 := by
  have ht := MeasuredQuotient.Reverse.divisionProgram_tCount n start (fun _ => false) (fun _ => false)
  rw [MeasuredQuotient.Reverse.division_T] at ht
  have hr := residue_t (MeasuredQuotient.Reverse.divisionProgram n start).2 (fun _ => false) (fun _ => false)
  have hz := residue_divisionProgram n start
  unfold AtLeast compiledTCount at *
  omega
end ReverseMeasuredCredit

namespace ReverseMeasuredCredit
attribute [local irreducible] MeasuredQuotient.Reverse.bankWrapperProgram MeasuredQuotient.bankWrapperProgram
theorem residue_multiplicationCleanup (n start : Nat) :
    residue (MeasuredQuotient.Reverse.multiplicationCleanupProgram n start).2 = 0 := by
  unfold MeasuredQuotient.Reverse.multiplicationCleanupProgram
  exact residue_app _ _ (residue_unmultiplyData _ _)
    (residue_appendLiteral _ _ (residue_bankWrapperProgram _ _) sum_fig15SwapOutput)

theorem residue_multiplicationCorrection (n start : Nat) (prior : List (Fin start)) :
    residue (MeasuredQuotient.Reverse.multiplicationCorrectionProgram n start prior).2 = 0 := by
  unfold MeasuredQuotient.Reverse.multiplicationCorrectionProgram
  exact residue_app _ _ (residue_correctionCompiled _ _ _ _) (residue_multiplicationCleanup _ _)

theorem residue_multiplicationAfterResetProgram (n start : Nat) (prior : List (Fin start)) :
    residue (MeasuredQuotient.Reverse.multiplicationAfterResetProgram n start prior).2 = 0 := by
  unfold MeasuredQuotient.Reverse.multiplicationAfterResetProgram appendRetaining
  exact residue_app _ _
    (residue_app _ _ (MeasuredCredit.residue_bankWrapperProgram _ _) (residue_multiplyData _ _))
    (residue_multiplicationCorrection _ _ _)

attribute [local irreducible] MeasuredQuotient.Reverse.multiplicationAfterResetProgram

theorem residue_multiplicationProgram (n start : Nat) :
    residue (MeasuredQuotient.Reverse.multiplicationProgram n start).2 = 0 := by
  unfold MeasuredQuotient.Reverse.multiplicationProgram
  exact residue_app _ _ (residue_multiplyWork _ _)
    (residue_collect _ (residue_multiplicationAfterResetProgram n) _ _ _)

theorem multiplicationCount (n start : Nat) :
    AtLeast (MeasuredQuotient.Reverse.multiplicationProgram n start).2 34668561 := by
  have ht := MeasuredQuotient.Reverse.multiplicationProgram_tCount n start (fun _ => false) (fun _ => false)
  rw [MeasuredQuotient.Reverse.multiplication_T] at ht
  have hr := residue_t (MeasuredQuotient.Reverse.multiplicationProgram n start).2 (fun _ => false) (fun _ => false)
  have hz := residue_multiplicationProgram n start
  unfold AtLeast compiledTCount at *
  omega
end ReverseMeasuredCredit

theorem residue_borrowCoordinate (start : Nat) :
    residue (BorrowFlag.adaptiveCoordinateProgram start).2 = 0 := by
  unfold BorrowFlag.adaptiveCoordinateProgram
  apply residue_sequence
  intro p hp s
  simp only [BorrowFlag.adaptiveCoordinateSegments,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with h | h | h | h | h | h | h | h | h <;> subst p
  · exact residue_fieldLookupAdd _ _ s
  · exact residue_signedField _ s
  · unfold BorrowFlag.divisionProgram
    exact residue_borrowField _ _ _ (ReverseMeasuredCredit.residue_divisionProgram _)
  · exact residue_paddedSquare _ s
  · exact residue_fieldLookupAdd _ _ s
  · unfold BorrowFlag.multiplicationProgram
    exact residue_borrowField _ _ _ (ReverseMeasuredCredit.residue_multiplicationProgram _)
  · exact residue_xNegate _ s
  · exact residue_fieldLookupAdd _ _ s
  · exact residue_signedField _ s

/-! ## Endpoint correction lookups -/

theorem tres_endpointSelectGate {n : Nat} (q : Wire) (port : Wire × EndpointBit n) :
    ((endpointSelectGate q port).map templateResidue).sum = 0 := by
  obtain ⟨w, b⟩ := port
  rcases b with b | r
  · cases b <;> rfl
  · rfl

theorem tres_endpointSelectGates {n : Nat} (q : Wire) (ports : List (Wire × EndpointBit n)) :
    ((endpointSelectGates q ports).map templateResidue).sum = 0 := by
  unfold endpointSelectGates
  induction ports with
  | nil => rfl
  | cons p ps ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, tres_endpointSelectGate, ih]

@[simp] theorem sum_ipxTest (k : Fin 4) : ((ipxTest k).map primitivePhaseCost).sum = 0 := by
  apply primitivePhaseCost_of_HPFree
  rw [ipxTest, Classical.hpFree_append, Classical.hpFree_append]
  exact ⟨⟨computeEqConst_HPFree _ _ _ _, computeEqConst_HPFree _ _ _ _⟩,
    computeEqConst_HPFree _ _ _ _⟩

theorem opsResidue_ipx {n : Nat} (rows : Nat → Fin n) (tree : UnaryActionTree) (paths : List Wire) :
    ∀ ops : List IpxOp, ((ipxOps rows tree paths ops).map lookupOpResidue).sum = 0
  | [] => rfl
  | .query c u v :: ops => by
    rw [ipxOps, List.map_append, List.sum_append, opsResidue_ipx rows tree paths ops,
      opsResidue_unary _ (fun l q => by
        rw [ipxLeaf, List.map_append, List.sum_append, tres_endpointSelectGates,
          tres_endpointSelectGates])]
  | .test k :: ops => by
    rw [ipxOps, List.map_append, List.sum_append, opsResidue_ipx rows tree paths ops,
      opsResidue_measuredTest]

/-! ## Window bodies -/

theorem residue_zeroDivision (n start : Nat) : residue (zeroDivisionProgram n start).2 = 0 := by
  unfold zeroDivisionProgram
  rw [residue_surround, residue_division, sum_fig15ZeroPrepare, sum_fig15ZeroRestore]

theorem residue_zeroMultiplication (n start : Nat) :
    residue (zeroMultiplicationProgram n start).2 = 0 := by
  unfold zeroMultiplicationProgram
  rw [residue_surround, residue_multiplication, sum_fig15ZeroPrepare, sum_fig15ZeroRestore]

theorem residue_coordinate (start : Nat) : residue (coordinateProgram start).2 = 0 := by
  unfold coordinateProgram
  apply residue_sequence
  intro p hp s
  simp only [coordinateSegments, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h | h | h | h | h | h | h | h | h <;> subst p
  · exact residue_fieldLookupAdd _ _ s
  · exact residue_signedField _ s
  · exact residue_zeroDivision _ s
  · exact residue_pointSquare _ s
  · exact residue_fieldLookupAdd _ _ s
  · exact residue_zeroMultiplication _ s
  · exact residue_xNegate _ s
  · exact residue_fieldLookupAdd _ _ s
  · exact residue_signedField _ s

theorem residue_placed (start : Nat) : residue (Single.Physical.placedProgram start).2 = 0 := by
  unfold Single.Physical.placedProgram ipxProgramOf
  exact (residue_lookup _ _ _).trans (opsResidue_ipx _ _ _ _)

theorem residue_core (start : Nat) : residue (Single.Physical.core start).2 = 0 := by
  unfold Single.Physical.core
  apply residue_sequence
  intro p hp s
  simp only [Single.Physical.segments, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h | h | h | h <;> subst p
  · exact residue_borrowCoordinate s
  · exact residue_yNegate s
  · exact residue_placed s
  · exact residue_yNegate s

theorem residue_prepared (start : Nat) : residue (Single.Physical.prepared start).2 = 0 := by
  unfold Single.Physical.prepared
  rw [residue_surround, residue_core, sum_signedAddressCircuit]

theorem residue_actual (start : Nat) : residue (Single.Physical.actual.program start) = 0 := by
  unfold Single.Physical.actual closedWindow
  exact ((residue_shift _ _).trans (residue_cast _ _)).trans
    ((residue_relabel _ _).trans (residue_prepared 0))

theorem residue_signedWindow (w : Single.SignedWindow) (start : Nat) :
    residue ((Single.signedWindow w).program start) = 0 := by
  unfold Single.signedWindow
  exact (residue_reindex _ _).trans (residue_actual start)

theorem residue_firstWindow (start : Nat) : residue (Single.firstWindow.program start) = 0 := by
  unfold Single.firstWindow
  dsimp only
  rw [residue_reindex]
  exact residue_first17Lookup start

/-! ## Window credits -/

/-- Every T gate of a signed window comes from an unconditional literal Toffoli. -/
theorem signedFullCount (w : Single.SignedWindow) (start : Nat) :
    AtLeast ((Single.signedWindow w).program start) 71634364 := by
  have ht := Single.signedWindow_t 0 w start (fun _ => false)
  have hr := residue_t ((Single.signedWindow w).program start)
    (readConstant Single.mixedCoefficientAt 0) (fun _ => false)
  rw [ht, residue_signedWindow] at hr
  unfold AtLeast
  omega

/-- The first window is a bare lookup, credited the same way. -/
theorem firstFullCount (start : Nat) : AtLeast (Single.firstWindow.program start) 131071 := by
  have ht := Single.firstWindow_t_uniform 0 start (fun _ => false)
  have hr := residue_t (Single.firstWindow.program start)
    (readConstant Single.mixedCoefficientAt 0) (fun _ => false)
  rw [ht, residue_firstWindow] at hr
  unfold AtLeast
  omega

end
end ShorECDLP.Entrant.FullCredit
end
end
