import ShorECDLP.Submission.Naive.Arithmetic.Secp256k1Instance
import ShorECDLP.Submission.Naive.Challenge.NumericLengths

/-! EDITABLE. Low-space field inversion engine (two-level checkpoint pebbling).

The engine works on 257-wire blocks `reg i` of `Secp256k1Instance`.  Its blocks are the
base `0` and `2 … nb-1`; block `1` (an unused port) is never touched.  A multiplier is
supplied abstractly as a `MulSpec`: a placed out-of-place modular multiplier for every
triple of distinct engine blocks, sharing one work-wire list disjoint from the blocks.

A valuation `σ : Nat → Option Nat` records, for every engine block, either the exponent
`e` of the value `x ^ e mod p` it holds or that it is clean.  `Moves σ σ' c` says that `c`
maps every state described by `σ` to one described by `σ'` and leaves every wire outside
the engine alone.

Each chain step `c := a²` or `c := a · r` is one placed multiplication.  A segment of steps
is evaluated by the recursive Bennett scheme (compute the first step, recurse, uncompute the
first step); the whole chain is the same scheme one level up, over segments whose results
are kept in checkpoint blocks.  `lowProgram` instantiates this with the libsecp256k1
addition chain for `x ^ (p - 2)` cut into twenty segments, and `lowProgram_contract` packages
it as a clean out-of-place inversion with an untouched exponent port. -/

namespace ShorECDLP.Entrant.LowInv

open ShorECDLP Arithmetic
open ShorECDLP.Secp256k1Instance (reg regBlock Block)
open scoped ArithmeticNotation

/-! ## Geometry -/

/-- Engine blocks: the base `0` and the blocks `2 … nb-1`. -/
def ids (nb : Nat) : List Nat := 0 :: List.range' 2 (nb - 2)

theorem mem_ids {nb i : Nat} : i ∈ ids nb ↔ i = 0 ∨ (2 ≤ i ∧ i < nb) := by
  simp only [ids, List.mem_cons, List.mem_range'_1]
  omega

theorem mem_reg {i : Nat} {w : Nat} : w ∈ (reg i).wires ↔ 257 * i ≤ w ∧ w < 257 * i + 257 := by
  simp only [Secp256k1Instance.reg_wires, Block.wires, regBlock, Secp256k1Instance.fieldWidth,
    List.mem_range'_1]

theorem reg_eq_of_mem {i j : Nat} {w : Nat} (hi : w ∈ (reg i).wires) (hj : w ∈ (reg j).wires) :
    i = j := by
  obtain ⟨h1, h2⟩ := mem_reg.mp hi
  obtain ⟨h3, h4⟩ := mem_reg.mp hj
  have : (w : Nat) < 257 * i + 257 := h2
  have : (w : Nat) < 257 * j + 257 := h4
  omega

/-- A placed multiplier for every triple of distinct engine blocks. -/
structure MulSpec (nb : Nat) where
  work : List Wire
  prog : Nat → Nat → Nat → Circuit
  cost : Nat
  len : Nat
  prog_length : ∀ a b c, (prog a b c).length ≤ len
  work_disjoint : ∀ i ∈ ids nb, ∀ w ∈ (reg i).wires, w ∉ work
  work_disjoint_one : ∀ w ∈ (reg 1).wires, w ∉ work
  work_nodup : work.Nodup
  contract : ∀ a b c, a ∈ ids nb → b ∈ ids nb → c ∈ ids nb → a ≠ b → a ≠ c → b ≠ c →
    ModMulContract (prog a b c)
      { lhs := (reg a).wires, rhs := (reg b).wires, out := (reg c).wires, work := work } p cost

variable {nb : Nat} (ms : MulSpec nb)

/-- The register layout of the multiplier placed on blocks `a`, `b`, `c`. -/
def mulLayout (a b c : Nat) : RegisterLayout :=
  { lhs := (reg a).wires, rhs := (reg b).wires, out := (reg c).wires, work := ms.work }

theorem mulLayout_allWires (a b c : Nat) :
    (mulLayout ms a b c).allWires = (reg a).wires ++ (reg b).wires ++ (reg c).wires ++ ms.work :=
  rfl

def engW : List Wire := (ids nb).flatMap (fun i => (reg i).wires) ++ ms.work

theorem mem_engW {w : Wire} :
    w ∈ engW ms ↔ (∃ i ∈ ids nb, w ∈ (reg i).wires) ∨ w ∈ ms.work := by
  simp only [engW, List.mem_append, List.mem_flatMap]

theorem reg_sub_engW {i : Nat} (hi : i ∈ ids nb) {w : Wire} (hw : w ∈ (reg i).wires) :
    w ∈ engW ms :=
  (mem_engW ms).mpr (Or.inl ⟨i, hi, hw⟩)

/-! ## Valuations -/

abbrev Val := Nat → Option Nat

def upd (σ : Val) (d : Nat) (v : Option Nat) : Val := fun i => if i = d then v else σ i

@[simp] theorem upd_same (σ : Val) (d : Nat) (v : Option Nat) : upd σ d v d = v := by
  simp [upd]

theorem upd_ne (σ : Val) {d i : Nat} (v : Option Nat) (h : i ≠ d) : upd σ d v i = σ i := by
  simp [upd, h]

theorem upd_comm (σ : Val) {a b : Nat} (u v : Option Nat) (h : a ≠ b) :
    upd (upd σ a u) b v = upd (upd σ b v) a u := by
  funext i
  simp only [upd]
  by_cases ha : i = a
  · subst ha
    simp [h]
  · simp [ha]

def RegOK (x : Nat) (st : BasisState) (i : Nat) : Option Nat → Prop
  | some e => regValue (reg i).wires st = x ^ e % p
  | none => Clean (reg i).wires st

def Inv (x : Nat) (σ : Val) (st : BasisState) : Prop :=
  (∀ i ∈ ids nb, RegOK x st i (σ i)) ∧ Clean ms.work st

def Moves (x : Nat) (σ σ' : Val) (c : Circuit) : Prop :=
  ∀ st, Inv ms x σ st →
    Inv ms x σ' (Classical.run c st) ∧ ∀ w, w ∉ engW ms → Classical.run c st w = st w

variable {ms}

theorem Moves.append {x : Nat} {σ₁ σ₂ σ₃ : Val} {c d : Circuit}
    (hc : Moves ms x σ₁ σ₂ c) (hd : Moves ms x σ₂ σ₃ d) : Moves ms x σ₁ σ₃ (c ++ d) := by
  intro st hst
  obtain ⟨h₁, f₁⟩ := hc st hst
  obtain ⟨h₂, f₂⟩ := hd _ h₁
  refine ⟨?_, ?_⟩
  · rw [Classical.run_append]; exact h₂
  · intro w hw
    rw [Classical.run_append, f₂ w hw, f₁ w hw]

/-- Equal register values force equal wires. -/
theorem wires_eq_of_regValue_eq :
    ∀ (ws : List Wire) (s₁ s₂ : BasisState), regValue ws s₁ = regValue ws s₂ →
      ∀ w ∈ ws, s₁ w = s₂ w
  | [], _, _, _, w, hw => absurd hw List.not_mem_nil
  | a :: ws, s₁, s₂, h, w, hw => by
      rw [regValue_cons, regValue_cons] at h
      have ha : s₁ a = s₂ a := by
        cases h₁ : s₁ a <;> cases h₂ : s₂ a <;> rw [h₁, h₂] at h <;> simp at h <;> omega
      have ht : regValue ws s₁ = regValue ws s₂ := by
        rw [ha] at h
        omega
      rcases List.mem_cons.mp hw with rfl | hw
      · exact ha
      · exact wires_eq_of_regValue_eq ws s₁ s₂ ht w hw

/-- A valuation determines every engine wire. -/
theorem Inv.determines {x : Nat} {σ : Val} {s₁ s₂ : BasisState}
    (h₁ : Inv ms x σ s₁) (h₂ : Inv ms x σ s₂) (hout : ∀ w, w ∉ engW ms → s₁ w = s₂ w) :
    s₁ = s₂ := by
  funext w
  by_cases hw : w ∈ engW ms
  · rcases (mem_engW ms).mp hw with ⟨i, hi, hwi⟩ | hb
    · have r₁ := h₁.1 i hi
      have r₂ := h₂.1 i hi
      cases hσ : σ i with
      | some e =>
          rw [hσ] at r₁ r₂
          change regValue _ s₁ = x ^ e % p at r₁
          change regValue _ s₂ = x ^ e % p at r₂
          exact wires_eq_of_regValue_eq _ s₁ s₂ (r₁.trans r₂.symm) w hwi
      | none =>
          rw [hσ] at r₁ r₂
          rw [r₁ w hwi, r₂ w hwi]
    · rw [h₁.2 w hb, h₂.2 w hb]
  · exact hout w hw

/-- Clear every block that `σ` declares clean. -/
def clearNone (nb : Nat) (σ : Val) (st : BasisState) : BasisState :=
  fun w => if ∃ i ∈ ids nb, σ i = none ∧ w ∈ (reg i).wires then false else st w

theorem clearNone_inv {x : Nat} {σ σ' : Val} {st : BasisState}
    (hext : ∀ i e, σ i = some e → σ' i = some e) (hst : Inv ms x σ' st) :
    Inv ms x σ (clearNone nb σ st) := by
  classical
  refine ⟨?_, ?_⟩
  · intro i hi
    cases hσ : σ i with
    | some e =>
        have hv := hst.1 i hi
        rw [hext i e hσ] at hv
        change regValue _ st = x ^ e % p at hv
        change regValue _ (clearNone nb σ st) = x ^ e % p
        rw [← hv]
        apply regValue_congr
        intro w hw
        simp only [clearNone]
        rw [if_neg]
        rintro ⟨j, _, hj, hwj⟩
        have := reg_eq_of_mem hw hwj
        subst this
        rw [hσ] at hj
        cases hj
    | none =>
        intro w hw
        simp only [clearNone]
        rw [if_pos ⟨i, hi, hσ, hw⟩]
  · intro w hw
    simp only [clearNone]
    split
    · rfl
    · exact hst.2 w hw

theorem clearNone_outside (σ : Val) (st : BasisState) {w : Wire} (hw : w ∉ engW ms) :
    clearNone nb σ st w = st w := by
  classical
  simp only [clearNone]
  rw [if_neg]
  rintro ⟨i, hi, _, hwi⟩
  exact hw (reg_sub_engW ms hi hwi)

/-- Uncomputation: a clean circuit run backwards undoes its valuation change. -/
theorem Moves.reverse {x : Nat} {σ σ' : Val} {c : Circuit} (h : Moves ms x σ σ' c)
    (hext : ∀ i e, σ i = some e → σ' i = some e)
    (hhp : Classical.HPFree c) (hwf : CircuitWellFormed c) :
    Moves ms x σ' σ c.reverse := by
  intro st hst
  have h₀ : Inv ms x σ (clearNone nb σ st) := clearNone_inv hext hst
  obtain ⟨h₁, f₁⟩ := h _ h₀
  have heq : Classical.run c (clearNone nb σ st) = st :=
    Inv.determines h₁ hst (fun w hw => (f₁ w hw).trans (clearNone_outside σ st hw))
  have hback : Classical.run c.reverse st = clearNone nb σ st := by
    have h := run_reverse_cancel c (clearNone nb σ st) hhp hwf
    rwa [heq] at h
  rw [hback]
  exact ⟨h₀, fun w hw => clearNone_outside σ st hw⟩


/-! ## Packaged circuit facts -/

/-- Everything the composition needs about one engine circuit. -/
structure Good (ms : MulSpec nb) (x : Nat) (σ σ' : Val) (c : Circuit) (t l : Nat) : Prop where
  moves : Moves ms x σ σ' c
  hp : Classical.HPFree c
  wf : CircuitWellFormed c
  uses : CircuitUsesOnly (engW ms) c
  tc : tCount c = t
  len : c.length ≤ l

theorem Good.append {x : Nat} {σ₁ σ₂ σ₃ : Val} {c d : Circuit} {t₁ t₂ l₁ l₂ : Nat}
    (hc : Good ms x σ₁ σ₂ c t₁ l₁) (hd : Good ms x σ₂ σ₃ d t₂ l₂) :
    Good ms x σ₁ σ₃ (c ++ d) (t₁ + t₂) (l₁ + l₂) where
  moves := hc.moves.append hd.moves
  hp := (Classical.hpFree_append _ _).mpr ⟨hc.hp, hd.hp⟩
  wf := (circuitWellFormed_append _ _).mpr ⟨hc.wf, hd.wf⟩
  uses := usesOnly_append hc.uses hd.uses
  tc := by rw [tCount_append, hc.tc, hd.tc]
  len := by rw [List.length_append]; exact Nat.add_le_add hc.len hd.len

theorem Good.reverse {x : Nat} {σ σ' : Val} {c : Circuit} {t l : Nat}
    (h : Good ms x σ σ' c t l) (hext : ∀ i e, σ i = some e → σ' i = some e) :
    Good ms x σ' σ c.reverse t l where
  moves := h.moves.reverse hext h.hp h.wf
  hp := Arithmetic.hpFree_reverse h.hp
  wf := Arithmetic.wellFormed_reverse h.wf
  uses := usesOnly_reverse h.uses
  tc := by rw [tCount_reverse, h.tc]
  len := by rw [List.length_reverse]; exact h.len

theorem RegOK.congr {x : Nat} {s s' : BasisState} {i : Nat} {o : Option Nat}
    (h : RegOK x s i o) (hs : ∀ w ∈ (reg i).wires, s' w = s w) : RegOK x s' i o := by
  cases o with
  | some e =>
      change regValue _ s' = x ^ e % p
      rw [regValue_congr _ s' s hs]
      exact h
  | none =>
      intro w hw
      rw [hs w hw]
      exact h w hw

theorem pow_mod_mul (x a b : Nat) : x ^ a % p * (x ^ b % p) % p = x ^ (a + b) % p := by
  rw [pow_add, Nat.mul_mod (x ^ a)]

theorem regValue_lt_p {x : Nat} {st : BasisState} {i e : Nat}
    (h : RegOK x st i (some e)) : regValue (reg i).wires st < p := by
  change regValue _ st = x ^ e % p at h
  rw [h]
  exact Nat.mod_lt _ Secp256k1Instance.p_pos

/-- Distinct blocks give disjoint, duplicate-free wire lists. -/
theorem regs_nodup {a b : Nat} (h : a ≠ b) : ((reg a).wires ++ (reg b).wires).Nodup :=
  List.nodup_append.mpr ⟨(regBlock a).wires_nodup, (regBlock b).wires_nodup,
    fun _ hw _ hv e => h (reg_eq_of_mem hw (e ▸ hv))⟩

theorem mul_layout_valid {a b c : Nat} (ha : a ∈ ids nb) (hb : b ∈ ids nb) (hc : c ∈ ids nb)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (mulLayout ms a b c).Valid := by
  refine ⟨(reg a).length_eq.trans (reg b).length_eq.symm,
    (reg a).length_eq.trans (reg c).length_eq.symm, ?_⟩
  rw [mulLayout_allWires]
  refine List.nodup_append.mpr ⟨?_, ms.work_nodup, ?_⟩
  · refine List.nodup_append.mpr ⟨regs_nodup hab, (regBlock c).wires_nodup, ?_⟩
    intro w hw _ hv e
    subst e
    rcases List.mem_append.mp hw with hw | hw
    · exact hac (reg_eq_of_mem hw hv)
    · exact hbc (reg_eq_of_mem hw hv)
  · intro w hw v hv e
    subst e
    rcases List.mem_append.mp hw with hw | hw
    · rcases List.mem_append.mp hw with hw | hw
      · exact ms.work_disjoint a ha w hw hv
      · exact ms.work_disjoint b hb w hw hv
    · exact ms.work_disjoint c hc w hw hv

/-! ## Primitive steps -/

theorem mul_good {x : Nat} {σ : Val} {a b c ea eb : Nat}
    (ha : a ∈ ids nb) (hb : b ∈ ids nb) (hc : c ∈ ids nb)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hσa : σ a = some ea) (hσb : σ b = some eb) (hσc : σ c = none) :
    Good ms x σ (upd σ c (some (ea + eb))) (ms.prog a b c) ms.cost ms.len := by
  have hk : ModMulContract (ms.prog a b c) (mulLayout ms a b c) p ms.cost :=
    ms.contract a b c ha hb hc hab hac hbc
  have hvalid := mul_layout_valid (ms := ms) ha hb hc hab hac hbc
  have hsub : ∀ i ∈ ids nb, ∀ w ∈ (reg i).wires, i ≠ a → i ≠ b → i ≠ c →
      w ∉ (mulLayout ms a b c).allWires := by
    intro i hi w hw hia hib hic hmem
    simp only [mulLayout_allWires, List.mem_append] at hmem
    rcases hmem with ((h | h) | h) | h
    · exact hia (reg_eq_of_mem hw h)
    · exact hib (reg_eq_of_mem hw h)
    · exact hic (reg_eq_of_mem hw h)
    · exact ms.work_disjoint i hi w hw h
  have hall : ∀ w ∈ (mulLayout ms a b c).allWires, w ∈ engW ms := by
    intro w hw
    simp only [mulLayout_allWires, List.mem_append] at hw
    rcases hw with ((h | h) | h) | h
    · exact reg_sub_engW ms ha h
    · exact reg_sub_engW ms hb h
    · exact reg_sub_engW ms hc h
    · exact (mem_engW ms).mpr (Or.inr h)
  refine ⟨?_, hk.hpFree, hk.wellFormed hvalid, usesOnly_mono hk.usesOnly hall,
    hk.counted, ms.prog_length a b c⟩
  intro st hst
  have hra := hst.1 a ha
  have hrb := hst.1 b hb
  have hrc := hst.1 c hc
  rw [hσa] at hra
  rw [hσb] at hrb
  rw [hσc] at hrc
  have hclean : Clean ((reg c).wires ++ ms.work) st := by
    intro w hw
    rcases List.mem_append.mp hw with h | h
    · exact hrc w h
    · exact hst.2 w h
  obtain ⟨hA, hB, hC, hW⟩ := hk.correct st hvalid (regValue_lt_p hra) (regValue_lt_p hrb) hclean
  have hpres := hk.usesOnly.preservesOutside
  refine ⟨⟨?_, hW⟩, fun w hw => hpres st w (fun h => hw (hall w h))⟩
  intro i hi
  by_cases hic : i = c
  · subst hic
    rw [upd_same]
    change regValue (reg i).wires _ = _
    change regValue (reg i).wires _ = regValue (reg a).wires st * regValue (reg b).wires st % p at hC
    change regValue _ st = x ^ ea % p at hra
    change regValue _ st = x ^ eb % p at hrb
    rw [hC, hra, hrb, pow_mod_mul]
  · rw [upd_ne _ _ hic]
    by_cases hia : i = a
    · subst hia
      rw [hσa]
      exact RegOK.congr hra hA
    · by_cases hib : i = b
      · subst hib
        rw [hσb]
        exact RegOK.congr hrb hB
      · exact RegOK.congr (hst.1 i hi)
          (fun w hw => hpres st w (hsub i hi w hw hia hib hic))

theorem copy_good {x : Nat} {σ : Val} {a d ea : Nat}
    (ha : a ∈ ids nb) (hd : d ∈ ids nb) (had : a ≠ d)
    (hσa : σ a = some ea) (hσd : σ d = none) :
    Good ms x σ (upd σ d (some ea)) (copyReg (reg a).wires (reg d).wires) 0 257 := by
  have hnd := regs_nodup had
  refine ⟨?_, copyReg_HPFree _ _, copyReg_wellFormed _ _ hnd,
    copyReg_usesOnly _ _ _ (fun w hw => reg_sub_engW ms ha hw)
      (fun w hw => reg_sub_engW ms hd hw), copyReg_tCount _ _, ?_⟩
  · intro st hst
    have hra := hst.1 a ha
    have hrd := hst.1 d hd
    rw [hσa] at hra
    rw [hσd] at hrd
    have hval := copyReg_correct (reg a).wires (reg d).wires st
      ((reg d).length_eq.trans (reg a).length_eq.symm) hnd hrd
    have hother : ∀ w, w ∉ (reg d).wires →
        Classical.run (copyReg (reg a).wires (reg d).wires) st w = st w :=
      fun w hw => copyReg_other w _ _ st hw
    refine ⟨⟨?_, fun w hw => (hother w (fun h => ms.work_disjoint d hd w h hw)).trans
      (hst.2 w hw)⟩, fun w hw => hother w (fun h => hw (reg_sub_engW ms hd h))⟩
    intro i hi
    by_cases hid : i = d
    · subst hid
      rw [upd_same]
      change regValue _ _ = _
      rw [hval]
      exact hra
    · rw [upd_ne _ _ hid]
      exact RegOK.congr (hst.1 i hi) (fun w hw => hother w (fun h' => hid (reg_eq_of_mem hw h')))
  · have h := NaiveChallenge.copyReg_length_le (reg a).wires (reg d).wires
    rw [(reg a).length_eq] at h
    exact h


theorem Good.cast {x : Nat} {σ σ' : Val} {c : Circuit} {t l t' l' : Nat}
    (h : Good ms x σ σ' c t l) (ht : t = t') (hl : l ≤ l') : Good ms x σ σ' c t' l' :=
  ⟨h.moves, h.hp, h.wf, h.uses, ht ▸ h.tc, h.len.trans hl⟩

theorem Good.congr {x : Nat} {σ σ' τ : Val} {c : Circuit} {t l : Nat}
    (h : Good ms x σ σ' c t l) (he : σ' = τ) : Good ms x σ τ c t l := he ▸ h

/-! ## Chain steps -/

/-- One out-of-place chain step: square, or multiply by the register `r` holding `x ^ er`. -/
inductive Op where
  | sq
  | mul (r er : Nat)

def opExp : Op → Nat → Nat
  | .sq, e => e + e
  | .mul _ er, e => e + er

def stepCirc (ms : MulSpec nb) (D : Nat) : Op → Nat → Nat → Circuit
  | .sq, a, c =>
      copyReg (reg a).wires (reg D).wires ++ ms.prog a D c ++
        (copyReg (reg a).wires (reg D).wires).reverse
  | .mul r _, a, c => ms.prog a r c

def stepLen (ms : MulSpec nb) : Op → Nat
  | .sq => 257 + ms.len + 257
  | .mul _ _ => ms.len

/-- Static and valuation side conditions of one step `c := op(a)`. -/
def ready1 (nb D : Nat) : Op → Nat → Nat → Val → Nat → Bool
  | .sq, a, c, σ, e =>
      decide (a ∈ ids nb) && decide (c ∈ ids nb) && decide (a ≠ c) && decide (σ a = some e) &&
        decide (σ c = none) && decide (D ∈ ids nb) && decide (D ≠ a) && decide (D ≠ c) &&
        decide (σ D = none)
  | .mul r er, a, c, σ, e =>
      decide (a ∈ ids nb) && decide (c ∈ ids nb) && decide (a ≠ c) && decide (σ a = some e) &&
        decide (σ c = none) && decide (r ∈ ids nb) && decide (r ≠ a) && decide (r ≠ c) &&
        decide (σ r = some er)

theorem step_good {x D : Nat} (op : Op) (a c : Nat) (σ : Val) (e : Nat)
    (h : ready1 nb D op a c σ e = true) :
    Good ms x σ (upd σ c (some (opExp op e))) (stepCirc ms D op a c) ms.cost (stepLen ms op) ∧
      σ c = none := by
  cases op with
  | sq =>
      simp only [ready1, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨ha, hc⟩, hac⟩, hσa⟩, hσc⟩, hD⟩, hDa⟩, hDc⟩, hσD⟩ := h
      refine ⟨?_, hσc⟩
      have g1 := copy_good (ms := ms) (x := x) ha hD (Ne.symm hDa) hσa hσD
      have g2 := mul_good (ms := ms) (x := x) (σ := upd σ D (some e)) (ea := e) (eb := e)
        ha hD hc (Ne.symm hDa) hac hDc (by rw [upd_ne _ _ (Ne.symm hDa)]; exact hσa)
        (upd_same _ _ _) (by rw [upd_ne _ _ (Ne.symm hDc)]; exact hσc)
      have g3 := copy_good (ms := ms) (x := x) (σ := upd σ c (some (e + e))) ha hD
        (Ne.symm hDa) (by rw [upd_ne _ _ hac]; exact hσa)
        (by rw [upd_ne _ _ hDc]; exact hσD)
      have g3r := g3.reverse (fun i e' hi => by
        by_cases hiD : i = D
        · subst hiD
          rw [upd_ne _ _ hDc, hσD] at hi
          cases hi
        · rw [upd_ne _ _ hiD]
          exact hi)
      have hcomm : upd (upd σ D (some e)) c (some (e + e)) =
          upd (upd σ c (some (e + e))) D (some e) := upd_comm _ _ _ hDc
      have g := (g1.append (g2.congr hcomm)).append g3r
      exact g.cast (by simp) (by simp [stepLen])
  | mul r er =>
      simp only [ready1, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨ha, hc⟩, hac⟩, hσa⟩, hσc⟩, hr⟩, hra⟩, hrc⟩, hσr⟩ := h
      exact ⟨(mul_good (ms := ms) (x := x) ha hr hc (Ne.symm hra) hac hrc hσa hσr hσc).cast
        rfl (by simp [stepLen]), hσc⟩

/-! ## Bennett composition -/

def bennett {α : Type} (step : α → Nat → Nat → Circuit) :
    Nat → Nat → List α → List Nat → Circuit
  | src, dst, [a], _ => step a src dst
  | src, dst, a :: b :: as, s :: ss =>
      step a src s ++ bennett step s dst (b :: as) ss ++ (step a src s).reverse
  | _, _, _, _ => []

def foldE {α : Type} (f : α → Nat → Nat) : List α → Nat → Nat
  | [], e => e
  | a :: as, e => foldE f as (f a e)

def bcost {α : Type} (T : α → Nat) : List α → Nat
  | [] => 0
  | [a] => T a
  | a :: b :: as => 2 * T a + bcost T (b :: as)

def chainOK {α : Type} (R : α → Nat → Nat → Val → Nat → Bool) (f : α → Nat → Nat) :
    Nat → Nat → List α → List Nat → Val → Nat → Bool
  | src, dst, [a], _, σ, e => R a src dst σ e
  | src, dst, a :: b :: as, s :: ss, σ, e =>
      R a src s σ e && R a src s (upd σ dst (some (foldE f (a :: b :: as) e))) e &&
        decide (s ≠ dst) && chainOK R f s dst (b :: as) ss (upd σ s (some (f a e))) (f a e)
  | _, _, _, _, _, _ => false

theorem bennett_good {α : Type} {step : α → Nat → Nat → Circuit} {f : α → Nat → Nat}
    {R : α → Nat → Nat → Val → Nat → Bool} {T L : α → Nat} {x : Nat}
    (hstep : ∀ a src dst σ e, R a src dst σ e = true →
      Good ms x σ (upd σ dst (some (f a e))) (step a src dst) (T a) (L a) ∧ σ dst = none) :
    ∀ (items : List α) (src dst : Nat) (scratch : List Nat) (σ : Val) (e : Nat),
      chainOK R f src dst items scratch σ e = true →
      Good ms x σ (upd σ dst (some (foldE f items e))) (bennett step src dst items scratch)
        (bcost T items) (bcost L items)
  | [], _, _, _, _, _, h => by simp [chainOK] at h
  | [a], src, dst, scratch, σ, e, h => by
      simp only [chainOK] at h
      simpa [bennett, foldE, bcost] using (hstep a src dst σ e h).1
  | _ :: _ :: _, _, _, [], _, _, h => by simp [chainOK] at h
  | a :: b :: as, src, dst, s :: ss, σ, e, h => by
      simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨h1, h2⟩, hsd⟩, h4⟩ := h
      have g1 := (hstep a src s σ e h1).1
      have g2 := bennett_good hstep (b :: as) s dst ss _ _ h4
      have g3 := hstep a src s _ e h2
      have g3r := g3.1.reverse (fun i e' hi => by
        by_cases his : i = s
        · subst his
          rw [g3.2] at hi
          cases hi
        · rw [upd_ne _ _ his]
          exact hi)
      have hcomm : upd (upd σ s (some (f a e))) dst (some (foldE f (b :: as) (f a e))) =
          upd (upd σ dst (some (foldE f (a :: b :: as) e))) s (some (f a e)) := by
        rw [upd_comm _ _ _ hsd]
        rfl
      have g := (g1.append (g2.congr hcomm)).append g3r
      refine (g.congr rfl).cast ?_ ?_
      · simp only [bcost]
        omega
      · simp only [bcost]
        omega


/-! ## Two-level pebbling -/

/-- A segment of chain steps from `src` into `dst`, through the scratch blocks `scr`. -/
def segStep (ms : MulSpec nb) (D : Nat) (scr : List Nat) (seg : List Op) (src dst : Nat) :
    Circuit :=
  bennett (stepCirc ms D) src dst seg scr

def segExp (seg : List Op) (e : Nat) : Nat := foldE opExp seg e

def ready2 (nb D : Nat) (scr : List Nat) (seg : List Op) (src dst : Nat) (σ : Val) (e : Nat) :
    Bool :=
  chainOK (ready1 nb D) opExp src dst seg scr σ e && decide (σ dst = none)

theorem seg_good {x D : Nat} (scr : List Nat) (seg : List Op) (src dst : Nat) (σ : Val) (e : Nat)
    (h : ready2 nb D scr seg src dst σ e = true) :
    Good ms x σ (upd σ dst (some (segExp seg e))) (segStep ms D scr seg src dst)
      (bcost (fun _ => ms.cost) seg) (bcost (stepLen ms) seg) ∧ σ dst = none := by
  simp only [ready2, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨bennett_good (fun op a c σ e h => step_good op a c σ e h) seg src dst scr σ e h.1, h.2⟩

/-- The whole engine: segments from the base (block 0) through checkpoints into block 2. -/
def engProg (ms : MulSpec nb) (D : Nat) (scr : List Nat) (segs : List (List Op))
    (ckpts : List Nat) : Circuit :=
  bennett (segStep ms D scr) 0 2 segs ckpts

def σ₀ : Val := upd (fun _ => none) 0 (some 1)

theorem engProg_good {x D : Nat} (scr : List Nat) (segs : List (List Op)) (ckpts : List Nat)
    (h : chainOK (ready2 nb D scr) segExp 0 2 segs ckpts σ₀ 1 = true) :
    Good ms x σ₀ (upd σ₀ 2 (some (foldE segExp segs 1))) (engProg ms D scr segs ckpts)
      (bcost (fun seg => bcost (fun _ => ms.cost) seg) segs)
      (bcost (fun seg => bcost (stepLen ms) seg) segs) :=
  bennett_good (fun seg a c σ e h => seg_good scr seg a c σ e h) segs 0 2 ckpts σ₀ 1 h


/-! ## The Naive low-space multiplier as a `MulSpec` -/

/-- The Naive low-space multiplier, with its workspace in blocks `38 … 42`. -/
def msE : MulSpec 38 where
  work := Secp256k1Instance.mulWork 38 39
  prog a b c := Secp256k1Instance.mulProgram a b c 38 39
  cost := Secp256k1Instance.mulCost
  len := 4037213
  prog_length a b c := NaiveChallenge.secpMulProgram_length_le a b c 38 39
  work_disjoint i hi w hw := by
    rw [mem_ids] at hi
    rw [Secp256k1Instance.mulWork_eq_blocksWires]
    apply Secp256k1Instance.not_mem_blocksWires_of_source (regBlock i) _ w hw
    rw [Secp256k1Instance.mulWorkBlocks_ids]
    simp only [Secp256k1Instance.regBlock_id, List.mem_cons, List.not_mem_nil, or_false]
    omega
  work_disjoint_one w hw := by
    rw [Secp256k1Instance.mulWork_eq_blocksWires]
    apply Secp256k1Instance.not_mem_blocksWires_of_source (regBlock 1) _ w hw
    rw [Secp256k1Instance.mulWorkBlocks_ids]
    decide
  work_nodup := by
    rw [Secp256k1Instance.mulWork_eq_blocksWires]
    apply Secp256k1Instance.blocksWires_nodup
    rw [Secp256k1Instance.mulWorkBlocks_ids]
    decide
  contract a b c ha hb hc hab _ _ := by
    rw [mem_ids] at ha hb
    exact Secp256k1Instance.mul_contract a b c 38 39 (by omega) (by omega) (by omega)
      hab (by omega) (by omega)

/-! ## The concrete engine

The libsecp256k1 addition chain (255 squarings, 15 multiplications) is cut into twenty
segments.  Checkpoints live in blocks `4 … 22`, the segment scratch in blocks `23 … 37`,
the squaring duplicate in block `3`, and the multiplier workspace above block `37`. -/

def nbE : Nat := 38
def dupE : Nat := 3
def ckptsE : List Nat := List.range' 4 19
def scrE : List Nat := List.range' 23 15

def plan : List (List Op) :=
  [[.sq, .mul 0 1],
   [.sq, .mul 0 1],
   [.sq, .sq, .sq, .mul 5 7, .sq, .sq, .sq, .mul 5 7, .sq, .sq, .mul 4 3],
   [.sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .mul 6 2047],
   [.sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq],
   [.sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .mul 7 4194303],
   [.sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq],
   [.sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq],
   [.sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .mul 9 17592186044415],
   [.sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq],
   [.sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq],
   [.sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq],
   [.sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq],
   [.sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq],
   [.sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .mul 12 309485009821345068724781055, .sq, .sq, .sq, .sq, .sq, .sq],
   [.sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq],
   [.sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq],
   [.sq, .sq, .sq, .sq, .sq, .sq, .mul 9 17592186044415, .sq, .sq, .sq, .mul 5 7, .sq, .sq, .sq, .sq, .sq],
   [.sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq, .sq],
   [.sq, .sq, .mul 7 4194303, .sq, .sq, .sq, .sq, .sq, .mul 0 1, .sq, .sq, .sq, .mul 4 3, .sq, .sq, .mul 0 1]]

def lowProgram : Circuit := engProg msE dupE scrE plan ckptsE

/-- Number of placed multiplications in `lowProgram`. -/
def lowMults : Nat := 1009

def lowCost : Nat := lowMults * Secp256k1Instance.mulCost

set_option maxRecDepth 100000 in
theorem plan_ok : chainOK (ready2 nbE dupE scrE) segExp 0 2 plan ckptsE σ₀ 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem plan_exp : foldE segExp plan 1 = p - 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem plan_cost :
    bcost (fun seg => bcost (fun _ => Secp256k1Instance.mulCost) seg) plan = lowCost := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem plan_len :
    bcost (fun seg => bcost (stepLen msE) seg) plan ≤ 4075000000 := by
  decide +kernel

theorem lowProgram_good (x : Nat) :
    Good msE x σ₀ (upd σ₀ 2 (some (p - 2))) lowProgram lowCost 4075000000 := by
  have h := engProg_good (ms := msE) (x := x) (D := dupE) scrE plan ckptsE plan_ok
  rw [plan_exp] at h
  exact h.cast plan_cost plan_len


/-! ## Contract packaging -/

/-- Base in block 0, untouched port in block 1, result in block 2; everything else is work. -/
def lowLayout : RegisterLayout :=
  { lhs := (reg 0).wires, rhs := (reg 1).wires, out := (reg 2).wires,
    work := (List.range' 3 35).flatMap (fun i => (reg i).wires) ++ msE.work }

theorem mem_lowWork_regs {w : Nat} :
    w ∈ (List.range' 3 35).flatMap (fun i => (reg i).wires) ↔ ∃ i, 3 ≤ i ∧ i < 38 ∧ w ∈ (reg i).wires := by
  simp only [List.mem_flatMap, List.mem_range'_1]
  constructor
  · rintro ⟨i, ⟨h1, h2⟩, hw⟩
    exact ⟨i, h1, by omega, hw⟩
  · rintro ⟨i, h1, h2, hw⟩
    exact ⟨i, ⟨h1, by omega⟩, hw⟩

theorem engW_sub_allWires : ∀ w ∈ engW msE, w ∈ lowLayout.allWires := by
  intro w hw
  simp only [lowLayout, RegisterLayout.allWires, List.mem_append]
  rcases (mem_engW msE).mp hw with ⟨i, hi, hwi⟩ | hwk
  · rw [mem_ids] at hi
    rcases hi with rfl | ⟨h1, h2⟩
    · exact Or.inl (Or.inl (Or.inl hwi))
    · by_cases h2' : i = 2
      · subst h2'
        exact Or.inl (Or.inr hwi)
      · exact Or.inr (Or.inl (mem_lowWork_regs.mpr ⟨i, by omega, h2, hwi⟩))
  · exact Or.inr (Or.inr hwk)

theorem lowProgram_contract :
    CleanBinaryContract lowProgram lowLayout p (fun a _ => a ^ (p - 2)) lowCost where
  correct := by
    intro st _ hlhs _ hclean
    change regValue (reg 0).wires st < p at hlhs
    let x := regValue (reg 0).wires st
    have hx : x % p = x := Nat.mod_eq_of_lt hlhs
    have hg := lowProgram_good x
    have hinv : Inv msE x σ₀ st := by
      refine ⟨fun i hi => ?_, fun w hw => hclean w (List.mem_append_right _
        (List.mem_append_right _ hw))⟩
      rw [mem_ids] at hi
      rcases hi with rfl | ⟨h1, h2⟩
      · change regValue _ st = x ^ 1 % p
        rw [pow_one, hx]
      · have hσ : σ₀ i = none := by
          simp only [σ₀, upd]
          rw [if_neg (by omega)]
        rw [hσ]
        intro w hw
        by_cases h2' : i = 2
        · subst h2'
          exact hclean w (List.mem_append_left _ hw)
        · exact hclean w (List.mem_append_right _ (List.mem_append_left _
            (mem_lowWork_regs.mpr ⟨i, by omega, h2, hw⟩)))
    obtain ⟨hinv', hframe⟩ := hg.moves st hinv
    have h0 := hinv'.1 0 (mem_ids.mpr (Or.inl rfl))
    rw [upd_ne _ _ (by decide : (0 : Nat) ≠ 2)] at h0
    change regValue _ _ = x ^ 1 % p at h0
    rw [pow_one, hx] at h0
    have h2 := hinv'.1 2 (mem_ids.mpr (Or.inr ⟨le_refl _, by decide⟩))
    rw [upd_same] at h2
    refine ⟨?_, ?_, h2, ?_⟩
    · intro w hw
      exact wires_eq_of_regValue_eq _ _ _ h0 w hw
    · intro w hw
      apply hframe w
      intro hmem
      rcases (mem_engW msE).mp hmem with ⟨i, hi, hwi⟩ | hwk
      · have := reg_eq_of_mem hwi hw
        subst this
        rw [mem_ids] at hi
        omega
      · exact msE.work_disjoint_one w hw hwk
    · intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · obtain ⟨i, h1, h2', hwi⟩ := mem_lowWork_regs.mp hw
        have hi := hinv'.1 i (mem_ids.mpr (Or.inr ⟨by omega, h2'⟩))
        have hσ : upd σ₀ 2 (some (p - 2)) i = none := by
          rw [upd_ne _ _ (by omega : i ≠ 2)]
          simp only [σ₀, upd]
          rw [if_neg (by omega)]
        rw [hσ] at hi
        exact hi w hwi
      · exact hinv'.2 w hw
  usesOnly := usesOnly_mono (lowProgram_good 0).uses engW_sub_allWires
  counted := (lowProgram_good 0).tc
  hpFree := (lowProgram_good 0).hp
  wellFormed := fun _ => (lowProgram_good 0).wf

def lowBlocks : List Block :=
  [regBlock 0, regBlock 1, regBlock 2] ++ (List.range' 3 35).map regBlock ++
    Secp256k1Instance.mulWorkBlocks 38 39

theorem lowLayout_allWires_eq : lowLayout.allWires = Secp256k1Instance.blocksWires lowBlocks := by
  simp only [lowLayout, RegisterLayout.allWires, lowBlocks, msE,
    Secp256k1Instance.mulWork_eq_blocksWires, Secp256k1Instance.blocksWires,
    List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.append_assoc, Secp256k1Instance.reg_wires, List.flatMap_map]

theorem lowBlocks_ids : lowBlocks.map Block.id = [0, 1, 2] ++ List.range' 3 35 ++
    [41, 38, 39, 40, 42] := by
  simp [lowBlocks, Secp256k1Instance.mulWorkBlocks_ids, List.map_map, Function.comp_def]

theorem lowLayout_valid : lowLayout.Valid := by
  refine ⟨(reg 0).length_eq.trans (reg 1).length_eq.symm,
    (reg 0).length_eq.trans (reg 2).length_eq.symm, ?_⟩
  rw [lowLayout_allWires_eq]
  apply Secp256k1Instance.blocksWires_nodup
  rw [lowBlocks_ids]
  decide

theorem lowLayout_allWires_lt : ∀ w ∈ lowLayout.allWires, w < 257 * 43 := by
  intro w hw
  rw [lowLayout_allWires_eq, Secp256k1Instance.blocksWires, List.mem_flatMap] at hw
  obtain ⟨b, hb, hwb⟩ := hw
  have hid : b.id < 43 := by
    have hmem : b.id ∈ lowBlocks.map Block.id := List.mem_map_of_mem hb
    rw [lowBlocks_ids] at hmem
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, List.mem_range'_1,
      or_false] at hmem
    omega
  have hbound := (Secp256k1Instance.Block.mem_bounds hwb).2
  have hle : Secp256k1Instance.fieldWidth * (b.id + 1) ≤ 257 * 43 := by
    simp only [Secp256k1Instance.fieldWidth]
    omega
  exact Nat.lt_of_lt_of_le hbound hle

theorem lowProgram_length_le : lowProgram.length ≤ 4075000000 := (lowProgram_good 0).len

theorem lowCost_eq : lowCost = 10263089914 := by
  simp [lowCost, lowMults, Secp256k1Instance.mulCost, Secp256k1Instance.fieldWidth]

end ShorECDLP.Entrant.LowInv
