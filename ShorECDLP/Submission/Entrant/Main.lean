import ShorECDLP.Submission.Entrant.Streaming.Correction
import ShorECDLP.Submission.Entrant.Compiler
import ShorECDLP.Submission.«2607_13816».EEA.LengthPrimitiveCounts
import ShorECDLP.Framework.Quantum.InnerProduct
import ShorECDLP.Submission.«2607_13816».EEA.Preprocess
import ShorECDLP.Submission.«2607_13816».EEA.BlockAPrimitiveCounts
import ShorECDLP.Challenge.Contract
import ShorECDLP.Submission.«2607_13816».Challenge.OuterResources
import ShorECDLP.Submission.«2607_13816».Challenge.CursorShift
import ShorECDLP.Submission.Entrant.Streaming.Certificate

section

section


/-! Exact cancellation of reversible gates across commuting classical operations.
The rewrite preserves the full quantum operator, including on nonzero workspace. -/
namespace ShorECDLP.Entrant.Cancellation
open Quantum
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000

def controls : Gate → List Wire
  | .CX a _ => [a]
  | .CCX a b _ => [a,b]
  | _ => []

def target : Gate → Wire
  | .X t | .H t | .CX _ t | .CCX _ _ t | .P _ _ t => t

def classicalGate : Gate → Bool
  | .X _ | .CX _ _ | .CCX _ _ _ => true
  | _ => false

def commutes (a b : Gate) : Bool :=
  classicalGate a && classicalGate b &&
    !(controls a).contains (target b) && !(controls b).contains (target a)

private theorem classical_commute (a b : Gate) (hc : commutes a b = true)
    (s : BasisState) :
    Classical.applyGate a (Classical.applyGate b s) =
      Classical.applyGate b (Classical.applyGate a s) := by
  cases a <;> cases b <;>
    simp_all [commutes, classicalGate, controls, target]
  all_goals
    funext w
    simp only [Classical.applyGate, upd]
    split_ifs <;> subst_vars <;> try contradiction
  all_goals simp only [eq_self, not_true_eq_false, false_and, and_false] at *
  all_goals try simp only [Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm, Bool.xor_not]

private theorem quantum_commute (a b : Gate) (hc : commutes a b = true)
    (ψ : State) :
    Quantum.applyGate a (Quantum.applyGate b ψ) =
      Quantum.applyGate b (Quantum.applyGate a ψ) := by
  have ha : Classical.IsClassicalGate a := by
    cases a <;> simp_all [commutes, classicalGate, Classical.IsClassicalGate]
  have hb : Classical.IsClassicalGate b := by
    cases b <;> simp_all [commutes, classicalGate, Classical.IsClassicalGate]
  have hk (s : BasisState) :
      Quantum.applyGate a (Quantum.applyGate b (ket s)) =
        Quantum.applyGate b (Quantum.applyGate a (ket s)) := by
    simp only [applyGate_ket_agrees_classical _ _ ha,
      applyGate_ket_agrees_classical _ _ hb, classical_commute a b hc]
  induction ψ using Finsupp.induction with
  | zero => simp only [map_zero]
  | @single_add s c ψ hs hc ih =>
    have he : Finsupp.single s c = c • ket s := by simp [ket]
    simp only [map_add, he, map_smul, ih, hk]

/-- Search only through commuting gates. Failure leaves the input untouched. -/
def erase (g : Gate) : Circuit → Option Circuit
  | [] => none
  | h :: hs =>
    if g = h ∧ g.adjoint = g then some hs
    else if commutes g h then (erase g hs).map (List.cons h)
    else none

/-- Append one gate to a reverse-order accumulation, cancelling when possible. -/
def push (g : Gate) (gs : Circuit) : Circuit :=
  match erase g gs with
  | some rest => rest
  | none => g :: gs

/-- The list is processed from right to left. -/
def optimize : Circuit → Circuit
  | [] => []
  | g :: gs => push g (optimize gs)

theorem erase_sublist (g : Gate) (xs ys : Circuit) (h : erase g xs = some ys) :
    ys.Sublist xs := by
  induction xs generalizing ys with
  | nil => simp [erase] at h
  | cons a xs ih =>
    simp only [erase] at h
    split at h
    · cases h
      exact List.Sublist.cons _ (List.Sublist.refl _)
    · split at h
      · cases he : erase g xs with
        | none => simp [he] at h
        | some zs =>
          simp only [he, Option.map_some, Option.some.injEq] at h
          subst ys
          exact List.Sublist.cons₂ _ (ih zs he)
      · simp at h

theorem push_sublist (g : Gate) (xs : Circuit) : (push g xs).Sublist (g :: xs) := by
  unfold push
  cases h : erase g xs with
  | none => exact List.Sublist.refl _
  | some ys => exact List.Sublist.cons _ (erase_sublist g xs ys h)

theorem optimize_sublist (xs : Circuit) : (optimize xs).Sublist xs := by
  induction xs with
  | nil => exact List.Sublist.refl _
  | cons g xs ih =>
    exact (push_sublist g (optimize xs)).trans (List.Sublist.cons₂ g ih)

private theorem erase_mem (g : Gate) (xs ys : Circuit) (h : erase g xs = some ys) :
    ∀ a ∈ ys, a ∈ xs := by
  induction xs generalizing ys with
  | nil => simp [erase] at h
  | cons a xs ih =>
    simp only [erase] at h
    split at h
    · cases h
      exact fun b hb => List.mem_cons_of_mem _ hb
    · split at h
      · cases he : erase g xs with
        | none => simp [he] at h
        | some zs =>
          simp only [he, Option.map_some, Option.some.injEq] at h
          subst ys
          intro b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih zs he b hb)
      · simp at h

theorem push_mem (g : Gate) (xs : Circuit) :
    ∀ a ∈ push g xs, a ∈ g :: xs := by
  unfold push
  cases h : erase g xs with
  | none => exact fun _ ha => ha
  | some ys => exact fun a ha => List.mem_cons_of_mem _ (erase_mem g xs ys h a ha)

theorem optimize_mem (xs : Circuit) : ∀ a ∈ optimize xs, a ∈ xs := by
  induction xs with
  | nil => simp [optimize]
  | cons g xs ih =>
    intro a ha
    rcases List.mem_cons.mp (push_mem g (optimize xs) a ha) with rfl | hh
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih a hh)

theorem optimize_wellFormed (xs : Circuit) (h : CircuitWellFormed xs) :
    CircuitWellFormed (optimize xs) :=
  fun a ha => h a (optimize_mem xs a ha)

private theorem erase_run (g : Gate) (xs ys : Circuit)
    (hg : g.WellFormed) (h : erase g xs = some ys) (ψ : State) :
    Quantum.run (g :: xs) ψ = Quantum.run ys ψ := by
  induction xs generalizing ys ψ with
  | nil => simp [erase] at h
  | cons a xs ih =>
    simp only [erase] at h
    split at h
    · rename_i he
      rcases he with ⟨rfl, hadj⟩
      cases h
      simp only [Quantum.run_cons]
      have hi := applyGate_adjoint_applyGate g hg ψ
      rw [hadj] at hi
      rw [hi]
    · split at h
      · rename_i hc
        cases he : erase g xs with
        | none => simp [he] at h
        | some zs =>
          simp only [he, Option.map_some, Option.some.injEq] at h
          subst ys
          simp only [Quantum.run_cons]
          rw [← quantum_commute g a hc]
          exact ih zs he (Quantum.applyGate a ψ)
      · simp at h

theorem push_run (g : Gate) (xs : Circuit) (hg : g.WellFormed) (ψ : State) :
    Quantum.run (push g xs) ψ = Quantum.run (g :: xs) ψ := by
  unfold push
  cases h : erase g xs with
  | none => rfl
  | some ys => exact (erase_run g xs ys hg h ψ).symm

theorem optimize_run (xs : Circuit) (h : CircuitWellFormed xs) :
    Quantum.run (optimize xs) = Quantum.run xs := by
  induction xs with
  | nil => rfl
  | cons g xs ih =>
    have hg := h g (by simp)
    have ht : CircuitWellFormed xs := fun a ha => h a (by simp [ha])
    apply LinearMap.ext
    intro ψ
    rw [optimize, push_run _ _ hg, Quantum.run_cons, ih ht, Quantum.run_cons]

end ShorECDLP.Entrant.Cancellation

namespace ShorECDLP.Entrant.Cancellation
open Paper2607_13816

/-- The terminal-epoch restore has two redundant traversals of its predicate v-chain. -/
def epochSource : Circuit := blockCForward indexedStepProductionRegisters

def reducedEpoch : Circuit := optimize epochSource

private instance gateWellFormedDecidable (g : Gate) : Decidable g.WellFormed := by
  cases g <;> unfold Gate.WellFormed <;> infer_instance

theorem epochSource_wellFormed : CircuitWellFormed epochSource := by
  unfold CircuitWellFormed
  decide +kernel

theorem reducedEpoch_run : Quantum.run reducedEpoch = Quantum.run epochSource :=
  optimize_run epochSource epochSource_wellFormed

theorem reducedEpoch_sublist : reducedEpoch.Sublist epochSource := optimize_sublist epochSource

theorem reducedEpoch_counts : ShorECDLP.tCount epochSource = 245 ∧
    ShorECDLP.tCount reducedEpoch = 133 ∧ reducedEpoch.length = 24 := by
  decide +kernel

end ShorECDLP.Entrant.Cancellation


namespace ShorECDLP.Entrant.Optimization
open Quantum Challenge Paper2607_13816.ChallengeMigration

/-- A syntactic subsequence retaining every measurement and classical control. -/
inductive Drops {n : Nat} : {s e : Nat} → Straight n s e → Straight n s e → Nat → Prop
  | refl {s e} (p : Straight n s e) : Drops p p 0
  | skip {s e} (g : Gate) {p q : Straight n s e} {d : Nat} :
      Drops p q d → Drops (.gate (.literal g) p) q (tCost g + d)
  | gate {s e} (g : TemplateGate n) {p q : Straight n s e} {d : Nat} :
      Drops p q d → Drops (.gate g p) (.gate g q) d
  | record {s e} (i : Fin s) (v : Bool) (g : Gate) {p q : Straight n s e} {d : Nat} :
      Drops p q d → Drops (.recordGate i v g p) (.recordGate i v g q) d
  | measure {s e} (w : Wire) {p q : Straight n (s+1) e} {d : Nat} :
      Drops p q d → Drops (.measure w p) (.measure w q) d

theorem Drops.wellFormed {n s e d} {p q : Straight n s e}
    (h : Drops p q d) (hp : p.WellFormed) : q.WellFormed := by
  induction h with
  | refl => exact hp
  | skip g h ih => exact ih hp.2
  | gate g h ih => exact ⟨hp.1, ih hp.2⟩
  | record i v g h ih => exact ⟨hp.1, ih hp.2⟩
  | measure w h ih => exact ih hp

theorem Drops.slots {n s e d} {p q : Straight n s e}
    (h : Drops p q d) : q.gateSlots ≤ p.gateSlots := by
  induction h <;> simp_all [Straight.gateSlots]; omega

theorem Drops.tCount {n s e d} {p q : Straight n s e}
    (h : Drops p q d) (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    (q.instantiate read history).tCount + d = (p.instantiate read history).tCount := by
  induction h with
  | refl => omega
  | skip g h ih =>
    simp only [Straight.instantiate, TemplateGate.instantiate, AdaptiveCircuit.tCount,
      ShorECDLP.tCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    have hh := ih history
    omega
  | gate g h ih =>
    simp only [Straight.instantiate, AdaptiveCircuit.tCount]
    have hh := ih history
    omega
  | record i v g h ih =>
    simp only [Straight.instantiate, AdaptiveCircuit.tCount]
    have hh := ih history
    omega
  | measure w h ih =>
    simp only [Straight.instantiate, AdaptiveCircuit.tCount]
    have hf := ih (Fin.lastCases false history)
    have ht := ih (Fin.lastCases true history)
    omega

theorem Drops.wires {n s e d} {p q : Straight n s e}
    (h : Drops p q d) (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    ∀ w ∈ (q.instantiate read history).wires, w ∈ (p.instantiate read history).wires := by
  induction h with
  | refl => exact fun _ hw => hw
  | skip g h ih =>
    intro w hw
    exact List.mem_append_right _ (ih history w hw)
  | gate g h ih =>
    intro w hw
    simp only [Straight.instantiate, AdaptiveCircuit.wires, List.mem_append] at hw ⊢
    exact hw.imp id (ih history w)
  | record i v g h ih =>
    intro w hw
    simp only [Straight.instantiate, AdaptiveCircuit.wires, List.mem_append] at hw ⊢
    exact hw.imp id (ih history w)
  | measure v h ih =>
    intro w hw
    simp only [Straight.instantiate, AdaptiveCircuit.wires, List.mem_cons, List.mem_append] at hw ⊢
    rcases hw with he | hf | ht
    · exact Or.inl he
    · exact Or.inr (Or.inl (ih (Fin.lastCases false history) w hf))
    · exact Or.inr (Or.inr (ih (Fin.lastCases true history) w ht))

private theorem Drops.append_right {n a b c d} (p : Straight n a b)
    {q q' : Straight n b c} (h : Drops q q' d) : Drops (p.append q) (p.append q') d := by
  induction p with
  | done => exact h
  | gate g p ih => exact Drops.gate g (ih h)
  | recordGate i v g p ih => exact Drops.record i v g (ih h)
  | measure w p ih => exact Drops.measure w (ih h)

theorem Drops.append {n a b c d f} {p p' : Straight n a b} {q q' : Straight n b c}
    (hp : Drops p p' d) (hq : Drops q q' f) :
    Drops (p.append q) (p'.append q') (d+f) := by
  induction hp with
  | refl p => simpa using Drops.append_right p hq
  | skip g h ih => simpa [Nat.add_assoc] using Drops.skip g (ih hq)
  | gate g h ih => exact Drops.gate g (ih hq)
  | record i v g h ih => exact Drops.record i v g (ih hq)
  | measure w h ih => exact Drops.measure w (ih hq)

private theorem tCount_le_of_sublist {xs ys : Circuit} (h : xs.Sublist ys) :
    ShorECDLP.tCount xs ≤ ShorECDLP.tCount ys := by
  induction h <;> simp_all [ShorECDLP.tCount]; omega

theorem Drops.literal {n s} {xs ys : Circuit} (h : ys.Sublist xs) :
    Drops (literalProgram xs : Straight n s s) (literalProgram ys)
      (ShorECDLP.tCount xs - ShorECDLP.tCount ys) := by
  induction h with
  | slnil => exact Drops.refl _
  | cons a h ih =>
    have ht := tCount_le_of_sublist h
    simpa [literalProgram, gateProgram, ShorECDLP.tCount_cons, Nat.add_sub_assoc ht]
      using Drops.skip a ih
  | cons₂ a h ih =>
    simpa [literalProgram, gateProgram, ShorECDLP.tCount_cons, Nat.add_sub_add_left] using Drops.gate (.literal a) ih

/-- Structural circuit rewrites, with exact operator equality at unitary leaves. -/
inductive Rewrites {n : Nat} : {s e : Nat} → Straight n s e → Straight n s e → Prop
  | refl {s e} (p : Straight n s e) : Rewrites p p
  | literal {s} (xs ys : Circuit) : Quantum.run xs = Quantum.run ys →
      Rewrites (literalProgram xs : Straight n s s) (literalProgram ys)
  | gate {s e} (g : TemplateGate n) {p q : Straight n s e} :
      Rewrites p q → Rewrites (.gate g p) (.gate g q)
  | record {s e} (i : Fin s) (v : Bool) (g : Gate) {p q : Straight n s e} :
      Rewrites p q → Rewrites (.recordGate i v g p) (.recordGate i v g q)
  | measure {s e} (w : Wire) {p q : Straight n (s+1) e} :
      Rewrites p q → Rewrites (.measure w p) (.measure w q)
  | append {a b c} {p p' : Straight n a b} {q q' : Straight n b c} :
      Rewrites p p' → Rewrites q q' → Rewrites (p.append q) (p'.append q')

private noncomputable def branchPrefix (history : List Bool) (u : State →ₗ[ℂ] State)
    (branches : Instrument) : Instrument :=
  branches.map fun b => ⟨history ++ b.history, b.kraus.comp u⟩

private theorem prefix_prefix (a b : List Bool) (u v : State →ₗ[ℂ] State) (bs : Instrument) :
    branchPrefix a u (branchPrefix b v bs) = branchPrefix (a++b) (v.comp u) bs := by
  simp only [branchPrefix, List.map_map]
  congr 1
  funext branch
  simp only [Function.comp_apply, List.append_assoc, LinearMap.comp_assoc]

/-- Continuation evaluator used only to prove context closure, never as submitted data. -/
private noncomputable def evaluate {n s e} (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool)
    (tail : (Fin e → Bool) → Instrument) : Instrument :=
  match p with
  | .done => tail history
  | .gate g p => branchPrefix [] (Quantum.run (g.instantiate read)) (evaluate p read history tail)
  | .recordGate i v g p => branchPrefix [] (Quantum.run (if history i=v then [g] else []))
      (evaluate p read history tail)
  | .measure w p =>
      branchPrefix [false] (xResetKraus w false) (evaluate p read (Fin.lastCases false history) tail) ++
      branchPrefix [true] (xResetKraus w true) (evaluate p read (Fin.lastCases true history) tail)

private theorem evaluate_append {n a b c} (p : Straight n a b) (q : Straight n b c)
    (read : ConstantBit n → Bool) (history : Fin a → Bool)
    (tail : (Fin c → Bool) → Instrument) :
    evaluate (p.append q) read history tail =
      evaluate p read history (fun h => evaluate q read h tail) := by
  induction p with
  | done => rfl
  | gate g p ih => simp only [Straight.append, evaluate, ih]
  | recordGate i v g p ih => simp only [Straight.append, evaluate, ih]
  | measure w p ih => simp only [Straight.append, evaluate, ih]

private theorem evaluate_literal {n s} (xs : Circuit) (read : ConstantBit n → Bool)
    (history : Fin s → Bool) (tail : (Fin s → Bool) → Instrument) :
    evaluate (literalProgram xs) read history tail = branchPrefix [] (Quantum.run xs) (tail history) := by
  induction xs with
  | nil => simp [literalProgram, gateProgram, evaluate, branchPrefix, Quantum.run]
  | cons g xs ih =>
    simp only [literalProgram, List.map_cons, gateProgram, evaluate, TemplateGate.instantiate] at ⊢
    change branchPrefix [] (Quantum.run [g]) (evaluate (literalProgram xs) read history tail) = _
    rw [ih, prefix_prefix]
    simp [Quantum.run]

private theorem Rewrites.eval_eq {n s e} {p q : Straight n s e} (h : Rewrites p q)
    (read : ConstantBit n → Bool) (history : Fin s → Bool)
    (tail : (Fin e → Bool) → Instrument) : evaluate p read history tail = evaluate q read history tail := by
  induction h with
  | refl => rfl
  | literal xs ys he => simp only [evaluate_literal, he]
  | gate g h ih =>
    simp only [evaluate, ih]
  | record i v g h ih =>
    simp only [evaluate, ih]
  | measure w h ih =>
    simp only [evaluate, ih]
  | append hp hq ip iq =>
    simp only [evaluate_append]
    rw [ip]
    congr 1
    funext hist
    exact iq hist tail

private theorem evaluate_run {n s e} (p : Straight n s e) (read : ConstantBit n → Bool)
    (history : Fin s → Bool) :
    evaluate p read history (fun _ => [{history := [], kraus := LinearMap.id}]) =
      (p.instantiate read history).run := by
  induction p with
  | done => rfl
  | gate g p ih => simp only [evaluate, Straight.instantiate, AdaptiveCircuit.run, ih]; rfl
  | recordGate i v g p ih => simp only [evaluate, Straight.instantiate, AdaptiveCircuit.run, ih]; rfl
  | measure w p ih => simp only [evaluate, Straight.instantiate, AdaptiveCircuit.run, ih]; rfl

theorem Rewrites.run {n s e} {p q : Straight n s e} (h : Rewrites p q)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    (p.instantiate read history).run = (q.instantiate read history).run := by
  rw [← evaluate_run, ← evaluate_run]
  exact h.eval_eq read history _

private theorem reindex_append {n m a b c} (f : Fin n → Fin m)
    (p : Straight n a b) (q : Straight n b c) :
    reindexStraight f (p.append q) = (reindexStraight f p).append (reindexStraight f q) := by
  induction p <;> simp_all [reindexStraight, Straight.append]

private theorem reindex_literal {n m s} (f : Fin n → Fin m) (xs : Circuit) :
    reindexStraight f (literalProgram xs : Straight n s s) = literalProgram xs := by
  induction xs <;> simp_all [literalProgram, gateProgram, reindexStraight, reindexGate]

theorem Rewrites.reindex {n m s e} {p q : Straight n s e} (h : Rewrites p q)
    (f : Fin n → Fin m) : Rewrites (reindexStraight f p) (reindexStraight f q) := by
  induction h with
  | refl => exact Rewrites.refl _
  | literal xs ys he => simpa only [reindex_literal] using Rewrites.literal (n := m) xs ys he
  | gate g h ih => exact Rewrites.gate _ ih
  | record i v g h ih => exact Rewrites.record _ _ _ ih
  | measure w h ih => exact Rewrites.measure _ ih
  | append hp hq ip iq => simpa only [reindex_append] using Rewrites.append ip iq

theorem Drops.reindex {n m s e d} {p q : Straight n s e} (h : Drops p q d)
    (f : Fin n → Fin m) : Drops (reindexStraight f p) (reindexStraight f q) d := by
  induction h with
  | refl => exact Drops.refl _
  | skip g h ih => exact Drops.skip _ ih
  | gate g h ih => exact Drops.gate _ ih
  | record i v g h ih => exact Drops.record _ _ _ ih
  | measure w h ih => exact Drops.measure _ ih

private theorem relabel_append {n a b c} (f : Wire ≃ Wire)
    (p : Straight n a b) (q : Straight n b c) :
    relabelStraight f (p.append q) = (relabelStraight f p).append (relabelStraight f q) := by
  induction p <;> simp_all [relabelStraight, Straight.append]

private theorem relabel_literal {n s} (f : Wire ≃ Wire) (xs : Circuit) :
    relabelStraight f (literalProgram xs : Straight n s s) = literalProgram (xs.map (Gate.relabel f)) := by
  induction xs <;> simp_all [literalProgram, gateProgram, relabelStraight, relabelTemplateGate]

private theorem relabel_run_eq (f : Wire ≃ Wire) (xs ys : Circuit)
    (h : Quantum.run xs = Quantum.run ys) :
    Quantum.run (xs.map (Gate.relabel f)) = Quantum.run (ys.map (Gate.relabel f)) := by
  apply LinearMap.ext
  intro ψ
  have hx := Quantum.run_relabel f xs (relabelState f.symm ψ)
  have hy := Quantum.run_relabel f ys (relabelState f.symm ψ)
  simp only [relabelState_symm_right] at hx hy
  rw [hx, hy, h]

theorem Rewrites.relabel {n s e} {p q : Straight n s e} (h : Rewrites p q)
    (f : Wire ≃ Wire) : Rewrites (relabelStraight f p) (relabelStraight f q) := by
  induction h with
  | refl => exact Rewrites.refl _
  | literal xs ys he =>
    simpa only [relabel_literal] using Rewrites.literal (n := n)
      (xs.map (Gate.relabel f)) (ys.map (Gate.relabel f)) (relabel_run_eq f xs ys he)
  | gate g h ih => exact Rewrites.gate _ ih
  | record i v g h ih => exact Rewrites.record _ _ _ ih
  | measure w h ih => exact Rewrites.measure _ ih
  | append hp hq ip iq => simpa only [relabel_append] using Rewrites.append ip iq

theorem Drops.relabel {n s e d} {p q : Straight n s e} (h : Drops p q d)
    (f : Wire ≃ Wire) : Drops (relabelStraight f p) (relabelStraight f q) d := by
  induction h with
  | refl => exact Drops.refl _
  | skip g h ih =>
    have he : tCost (g.relabel f) = tCost g := by cases g <;> rfl
    simpa only [he] using Drops.skip (g.relabel f) ih
  | gate g h ih => exact Drops.gate _ ih
  | record i v g h ih => exact Drops.record _ _ _ ih
  | measure w h ih => exact Drops.measure _ ih

private theorem shift_append {n a b c} (offset : Nat)
    (p : Straight n a b) (q : Straight n b c) :
    shiftStraight offset (p.append q) = (shiftStraight offset p).append (shiftStraight offset q) := by
  induction p <;> simp_all [shiftStraight, Straight.append]

private theorem shift_literal {n s} (offset : Nat) (xs : Circuit) :
    shiftStraight offset (literalProgram xs : Straight n s s) = literalProgram xs := by
  induction xs <;> simp_all [literalProgram, gateProgram, shiftStraight]

theorem Rewrites.shift {n s e} {p q : Straight n s e} (h : Rewrites p q)
    (offset : Nat) : Rewrites (shiftStraight offset p) (shiftStraight offset q) := by
  induction h with
  | refl => exact Rewrites.refl _
  | literal xs ys he => simpa only [shift_literal] using Rewrites.literal (n := n) xs ys he
  | gate g h ih => exact Rewrites.gate _ ih
  | record i v g h ih => exact Rewrites.record _ _ _ ih
  | measure w h ih => exact Rewrites.measure _ ih
  | append hp hq ip iq => simpa only [shift_append] using Rewrites.append ip iq

theorem Drops.shift {n s e d} {p q : Straight n s e} (h : Drops p q d)
    (offset : Nat) : Drops (shiftStraight offset p) (shiftStraight offset q) d := by
  induction h with
  | refl => exact Drops.refl _
  | skip g h ih => exact Drops.skip _ ih
  | gate g h ih => exact Drops.gate _ ih
  | record i v g h ih => exact Drops.record _ _ _ ih
  | measure w h ih => exact Drops.measure _ ih

theorem Rewrites.castFinish {n s e f} {p q : Straight n s e} (h : Rewrites p q)
    (he : e=f) : Rewrites (castFinish he p) (castFinish he q) := by
  subst f
  exact h

theorem Drops.castFinish {n s e f d} {p q : Straight n s e} (h : Drops p q d)
    (he : e=f) : Drops (castFinish he p) (castFinish he q) d := by
  subst f
  exact h

private theorem qubitCount_mono (a b : AdaptiveCircuit)
    (h : ∀ w ∈ a.wires, w ∈ b.wires) : a.qubitCount ≤ b.qubitCount := by
  have hh : a.wires.toFinset ⊆ b.wires.toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (h w (List.mem_toFinset.mp hw))
  simpa only [AdaptiveCircuit.qubitCount, List.card_toFinset] using Finset.card_le_card hh

/-- Retain the exact table and decoder cursor while substituting an equivalent program. -/
def replaceEntry (e : StraightEntry) (p : Straight e.coefficients.length 0 e.finalCursor) : StraightEntry :=
  ⟨e.coefficients,e.finalCursor,p⟩

/-- Transport the protected certificate along a verified gate deletion with exact T savings. -/
theorem replacement_certificate {limits : Limits} {layout : DecodeLayout}
    {entry : StraightEntry} {bounds : Bounds} (original : Certificate limits layout entry bounds)
    {p : Straight entry.coefficients.length 0 entry.finalCursor} {saving : Nat}
    (hd : Drops entry.program p saving) (he : Rewrites entry.program p) :
    Certificate limits layout (replaceEntry entry p)
      ⟨bounds.qubits,bounds.tModel-saving,bounds.measurements⟩ := by
  refine ⟨hd.slots.trans original.gateBudget, original.recordBudget, original.tableBudget,
    original.candidateBudget, hd.wellFormed original.wellFormed, ?_, ?_⟩
  · intro Q
    have ho := original.resources Q
    have hq := qubitCount_mono (p.instantiate (readConstant entry.coefficients.get Q) Fin.elim0)
      (entry.instantiate Q) (hd.wires _ _)
    have ht := hd.tCount (readConstant entry.coefficients.get Q) Fin.elim0
    have hm := Straight.measurementCount p (readConstant entry.coefficients.get Q) Fin.elim0
    have hm' := Straight.measurementCount entry.program (readConstant entry.coefficients.get Q) Fin.elim0
    change (entry.instantiate Q).qubitCount ≤ bounds.qubits ∧
      (entry.instantiate Q).tCount ≤ bounds.tModel ∧
      (entry.instantiate Q).measurementCount ≤ bounds.measurements at ho
    change (p.instantiate (readConstant entry.coefficients.get Q) Fin.elim0).qubitCount ≤ bounds.qubits ∧
      (p.instantiate (readConstant entry.coefficients.get Q) Fin.elim0).tCount ≤ bounds.tModel-saving ∧
      (p.instantiate (readConstant entry.coefficients.get Q) Fin.elim0).measurementCount ≤ bounds.measurements
    exact ⟨hq.trans ho.1, by dsimp only [StraightEntry.instantiate] at ho; omega,
      by dsimp only [StraightEntry.instantiate] at ho; omega⟩
  · intro Q d hQ hdQ
    have hh := he.run (readConstant entry.coefficients.get Q) Fin.elim0
    change (99 : ℝ)/100 ≤ Instrument.bornMass
      (((p.instantiate (readConstant entry.coefficients.get Q) Fin.elim0).run).filter _) (ket zeroBasisState)
    rw [← hh]
    exact original.success Q d hQ hdQ

/-- A program together with the exact proof needed to replace a fixed source context. -/
structure Patch {n s e : Nat} (source : Straight n s e) (saving : Nat) where
  program : Straight n s e
  drops : Drops source program saving
  rewrites : Rewrites source program

namespace Patch
noncomputable section

def refl {n s e} (p : Straight n s e) : Patch p 0 := ⟨p, Drops.refl p, Rewrites.refl p⟩

def castSaving {n s e a b} {p : Straight n s e} (h : Patch p a) (he : a=b) : Patch p b := he ▸ h

def literal {n s d} (xs ys : Circuit) (hs : ys.Sublist xs)
    (hr : Quantum.run xs = Quantum.run ys)
    (ht : ShorECDLP.tCount ys + d = ShorECDLP.tCount xs) :
    Patch (literalProgram xs : Straight n s s) d := by
  refine ⟨literalProgram ys, ?_, Rewrites.literal xs ys hr⟩
  have hd : ShorECDLP.tCount xs - ShorECDLP.tCount ys = d := by omega
  simpa only [hd] using Drops.literal (n := n) (s := s) hs

def append {n a b c d f} {p : Straight n a b} {q : Straight n b c}
    (hp : Patch p d) (hq : Patch q f) : Patch (p.append q) (d+f) :=
  ⟨hp.program.append hq.program, hp.drops.append hq.drops, hp.rewrites.append hq.rewrites⟩

def castFinish {n s e f d} {p : Straight n s e} (hp : Patch p d) (he : e=f) :
    Patch (Paper2607_13816.ChallengeMigration.castFinish he p) d :=
  ⟨Paper2607_13816.ChallengeMigration.castFinish he hp.program, hp.drops.castFinish he, hp.rewrites.castFinish he⟩

def appendCompiled {n start d f}
    (p : (count : Nat) × Straight n start (start+count))
    (q : (count : Nat) × Straight n (start+p.1) (start+p.1+count))
    (hp : Patch p.2 d) (hq : Patch q.2 f) :
    Patch (Paper2607_13816.ChallengeMigration.appendCompiled p q).2 (d+f) :=
  (hp.append hq).castFinish (Nat.add_assoc start p.1 q.1)

def sequenceCons {n start d f} (head : FixedSegment n) (tail : List (FixedSegment n))
    (hp : Patch (head start).2 d)
    (hq : Patch (sequenceProgram n tail (start+(head start).1)).2 f) :
    Patch (sequenceProgram n (head::tail) start).2 (d+f) :=
  appendCompiled (head start) (sequenceProgram n tail (start+(head start).1)) hp hq

def gate {n s e d} (g : TemplateGate n) {p : Straight n s e} (hp : Patch p d) :
    Patch (.gate g p) d := ⟨.gate g hp.program, Drops.gate g hp.drops, Rewrites.gate g hp.rewrites⟩

def record {n s e d} (i : Fin s) (v : Bool) (g : Gate) {p : Straight n s e}
    (hp : Patch p d) : Patch (.recordGate i v g p) d :=
  ⟨.recordGate i v g hp.program, Drops.record i v g hp.drops, Rewrites.record i v g hp.rewrites⟩

def measure {n s e d} (w : Wire) {p : Straight n (s+1) e} (hp : Patch p d) :
    Patch (.measure w p) d :=
  ⟨.measure w hp.program, Drops.measure w hp.drops, Rewrites.measure w hp.rewrites⟩

def reindex {n m s e d} {p : Straight n s e} (hp : Patch p d) (f : Fin n → Fin m) :
    Patch (reindexStraight f p) d :=
  ⟨reindexStraight f hp.program, hp.drops.reindex f, hp.rewrites.reindex f⟩

def relabel {n s e d} {p : Straight n s e} (hp : Patch p d) (f : Wire ≃ Wire) :
    Patch (relabelStraight f p) d :=
  ⟨relabelStraight f hp.program, hp.drops.relabel f, hp.rewrites.relabel f⟩

def shift {n s e d} {p : Straight n s e} (hp : Patch p d) (offset : Nat) :
    Patch (shiftStraight offset p) d :=
  ⟨shiftStraight offset hp.program, hp.drops.shift offset, hp.rewrites.shift offset⟩

end
end Patch

end ShorECDLP.Entrant.Optimization


namespace ShorECDLP.Entrant.Optimization
open Quantum Challenge Paper2607_13816.ChallengeMigration
open Paper2607_13816
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 200000
set_option Elab.async false
attribute [local irreducible] sequenceProgram appendCompiled literalProgram
  remainderBlockProgram coefficientBlockProgram phaseProgram hProgram intervalProgram coefficientProgram
  preprocessProgram productionParityProgram measuredStepProgram measuredScheduleProgram
  measuredEEAForwardProgram measuredForwardWrapperProgram multiplyWorkProgram divisionAfterResetProgram
  divisionProgram zeroDivisionProgram fieldLookupAddProgram signedFieldProgram pointSquareProgram
  zeroMultiplicationProgram xNegateProgram coordinateProgram


def Patch.prependCompiled {n start d} (gs : Circuit)
    (p : (count : Nat) × Straight n start (start+count)) (hp : Patch p.2 d) :
    Patch (Paper2607_13816.ChallengeMigration.prependCompiled gs p).2 d := by
  unfold Paper2607_13816.ChallengeMigration.prependCompiled
  exact ((Patch.refl (literalProgram gs)).append hp).castSaving (Nat.zero_add d)

def Patch.surroundCompiled {n start d} (before after : Circuit)
    (p : (count : Nat) × Straight n start (start+count)) (hp : Patch p.2 d) :
    Patch (Paper2607_13816.ChallengeMigration.surroundCompiled before after p).2 d := by
  unfold Paper2607_13816.ChallengeMigration.surroundCompiled Paper2607_13816.ChallengeMigration.prependCompiled
  exact ((Patch.refl (literalProgram before)).append
    ((Patch.appendCompiled p ⟨0, literalProgram after⟩ hp (Patch.refl _)).castSaving (Nat.add_zero d))).castSaving (Nat.zero_add d)

/-- Rewrite one terminal-epoch restore inside an otherwise untouched literal segment. -/
def epochPatch (n s : Nat) (tail : Circuit) :
    Patch (literalProgram (Cancellation.epochSource ++ tail) : Straight n s s) 112 := by
  apply Patch.literal _ (Cancellation.reducedEpoch ++ tail)
  · exact Cancellation.reducedEpoch_sublist.append (List.Sublist.refl _)
  · simp only [Quantum.run_append_map, Cancellation.reducedEpoch_run]
  · have h := Cancellation.reducedEpoch_counts
    simp only [ShorECDLP.tCount_append, h.1, h.2.1]
    omega



set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def aSource : Circuit := blockAForward indexedStepProductionRegisters
def aMiddle : Circuit := (aSource.drop 837).take 33
def aReduced : Circuit := aSource.take 837 ++ Cancellation.optimize aMiddle ++ aSource.drop 870

private theorem split_three (xs : Circuit) (a b : Nat) :
    xs = xs.take a ++ (xs.drop a).take b ++ xs.drop (a+b) := by
  rw [List.append_assoc, ← List.drop_drop]
  rw [List.take_append_drop, List.take_append_drop]

private theorem aSplit : aSource = aSource.take 837 ++ aMiddle ++ aSource.drop 870 :=
  split_three aSource 837 33

private theorem aMiddle_wellFormed : CircuitWellFormed aMiddle := by
  unfold CircuitWellFormed
  decide +kernel

private theorem aMiddle_counts : ShorECDLP.tCount aMiddle = 105 ∧
    ShorECDLP.tCount (Cancellation.optimize aMiddle) = 7 := by
  decide +kernel

def aPatch (n start : Nat) : Patch (literalProgram aSource : Straight n start start) 98 := by
  apply Patch.literal _ aReduced
  · conv_rhs => rw [aSplit]
    exact ((List.Sublist.refl _).append (Cancellation.optimize_sublist aMiddle)).append (List.Sublist.refl _)
  · have h := Cancellation.optimize_run aMiddle aMiddle_wellFormed
    conv_lhs => rw [aSplit]
    simp only [aReduced, Quantum.run_append_map, h]
  · conv_rhs => rw [aSplit]
    have h := aMiddle_counts
    simp only [aReduced, ShorECDLP.tCount_append, h.1, h.2]
    omega


set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def b2Source : Circuit := blockB2 indexedStepProductionRegisters
private theorem b2_wellFormed : CircuitWellFormed b2Source := by
  unfold CircuitWellFormed
  decide +kernel
private theorem b2_counts : ShorECDLP.tCount b2Source = 462 ∧
    ShorECDLP.tCount (Cancellation.optimize b2Source) = 238 := by
  decide +kernel

def b2Patch (n start : Nat) : Patch (literalProgram b2Source : Straight n start start) 224 := by
  apply Patch.literal _ (Cancellation.optimize b2Source)
  · exact Cancellation.optimize_sublist b2Source
  · exact (Cancellation.optimize_run b2Source b2_wellFormed).symm
  · have h := b2_counts
    omega

def remainderPatch (n start width : Nat) (w : ActiveWindow) :
    Patch (remainderBlockProgram n start indexedStepProductionRegisters width w).2 224 := by
  unfold remainderBlockProgram remainderBlockSegments
  refine (Patch.sequenceCons (d := 0) (f := 224) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 224) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 224) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := 224) (f := 0) _ _ (b2Patch n _) (Patch.refl _)).castSaving (by omega)

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def b1Source : Circuit :=
  let r := indexedStepProductionRegisters
  rControlNonterminal [r.phase1] 0 r.control r.lengthRPrime r.terminal r.blockScratch
private theorem b1_wellFormed : CircuitWellFormed b1Source := by
  unfold CircuitWellFormed
  decide +kernel
private theorem b1_counts : ShorECDLP.tCount b1Source = 217 ∧
    ShorECDLP.tCount (Cancellation.optimize b1Source) = 119 := by decide +kernel

def b1Patch (n start : Nat) : Patch (literalProgram b1Source : Straight n start start) 98 := by
  apply Patch.literal _ (Cancellation.optimize b1Source)
  · exact Cancellation.optimize_sublist b1Source
  · exact (Cancellation.optimize_run b1Source b1_wellFormed).symm
  · have h := b1_counts; omega

def remainderPatchAll (n start width : Nat) (w : ActiveWindow) :
    Patch (remainderBlockProgram n start indexedStepProductionRegisters width w).2 420 := by
  unfold remainderBlockProgram remainderBlockSegments
  refine (Patch.sequenceCons (d := 98) (f := 322) _ _ (b1Patch n _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 322) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 98) (f := 224) _ _ (b1Patch n _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := 224) (f := 0) _ _ (b2Patch n _) (Patch.refl _)).castSaving (by omega)

def ePrepSource : Circuit :=
  let r := indexedStepProductionRegisters
  ((computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++
    computeControl [r.phase1,r.terminal] 1 r.control r.blockScratch) ++
    computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch) ++ prepareLatestPaperTBoundary r.tBoundary 256

def eCleanSource : Circuit :=
  let r := indexedStepProductionRegisters
  computeControl [r.phase1] 1 r.control r.blockScratch ++ restoreLatestPaperTBoundary r.tBoundary 256

private theorem ePrep_wellFormed : CircuitWellFormed ePrepSource := by
  unfold CircuitWellFormed
  decide +kernel
private theorem eClean_wellFormed : CircuitWellFormed eCleanSource := by
  unfold CircuitWellFormed
  decide +kernel
private theorem ePrep_counts : ShorECDLP.tCount ePrepSource = 560 ∧
    ShorECDLP.tCount (Cancellation.optimize ePrepSource) = 518 := by decide +kernel
private theorem eClean_counts : ShorECDLP.tCount eCleanSource = 539 ∧
    ShorECDLP.tCount (Cancellation.optimize eCleanSource) = 497 := by decide +kernel

def ePrepPatch (n start : Nat) : Patch (literalProgram ePrepSource : Straight n start start) 42 := by
  apply Patch.literal _ (Cancellation.optimize ePrepSource)
  · exact Cancellation.optimize_sublist ePrepSource
  · exact (Cancellation.optimize_run ePrepSource ePrep_wellFormed).symm
  · have h := ePrep_counts; omega

def eCleanPatch (n start : Nat) : Patch (literalProgram eCleanSource : Straight n start start) 42 := by
  apply Patch.literal _ (Cancellation.optimize eCleanSource)
  · exact Cancellation.optimize_sublist eCleanSource
  · exact (Cancellation.optimize_run eCleanSource eClean_wellFormed).symm
  · have h := eClean_counts; omega

def coefficientPatch (n start : Nat) (w : ActiveWindow) :
    Patch (coefficientBlockProgram n start indexedStepProductionRegisters 256 w).2 84 := by
  unfold coefficientBlockProgram coefficientBlockSegments
  refine (Patch.sequenceCons (d := 42) (f := 42) _ _ (ePrepPatch n _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 42) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 42) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 42) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := 42) (f := 0) _ _ (eCleanPatch n _) (Patch.refl _)).castSaving (by omega)

def candidateStepPatch (n start T : Nat) :
    Patch (measuredStepProgram n start indexedStepProductionRegisters 256 T).2 714 := by
  unfold measuredStepProgram measuredStepSegments
  refine (Patch.sequenceCons (d := 98) (f := 616) _ _ (aPatch n _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 420) (f := 196) _ _ (remainderPatchAll n _ 256 _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 112) (f := 84) _ _ (epochPatch n _ _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := 84) (f := 0) _ _ (coefficientPatch n _ _) (Patch.refl _)).castSaving (by omega)

/-- Optimize the fixed A, remainder-control, epoch and coefficient-boundary literals. -/
def stepPatch (n start T : Nat) :
    Patch (measuredStepProgram n start indexedStepProductionRegisters 256 T).2 714 :=
  candidateStepPatch n start T

/-- Exact per-step savings accumulate through the fixed 1,620-step schedule. -/

def schedulePatch (n : Nat) : (count first start : Nat) →
    Patch (measuredScheduleProgram n indexedStepProductionRegisters 256 count first start).2 (count*714)
  | 0, _, _ => Patch.refl _
  | count+1, first, start => by
    simp only [measuredScheduleProgram]
    exact (Patch.appendCompiled _ _ (stepPatch n start first)
      (schedulePatch n count (first+1) _)).castSaving (by omega)


def eeaForwardPatch (n start : Nat) :
    Patch (measuredEEAForwardProgram n start indexedStepProductionRegisters).2 1156680 := by
  unfold measuredEEAForwardProgram
  exact schedulePatch n 1620 1 start


def wrapperPatch (n start : Nat) :
    Patch (measuredForwardWrapperProgram n start).2 1156680 := by
  unfold measuredForwardWrapperProgram measuredForwardWrapperSegments
  refine (Patch.sequenceCons (d := 0) (f := 1156680) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := 1156680) (f := 0) _ _ (eeaForwardPatch n _) (Patch.refl _)).castSaving (by omega)


def divisionPatch (n start : Nat) : Patch (divisionProgram n start).2 1156680 := by
  unfold divisionProgram
  refine (Patch.appendCompiled (d := 1156680) (f := 0) _ _ ?_ (Patch.refl _)).castSaving (by omega)
  exact (Patch.appendCompiled _ _ (wrapperPatch n start) (Patch.refl _)).castSaving (by omega)



end
end ShorECDLP.Entrant.Optimization
namespace ShorECDLP.Entrant.Optimization
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] sequenceProgram appendCompiled literalProgram coordinateProgram zeroDivisionProgram
  Single.axis Single.entry

def zeroDivisionPatch (n start : Nat) : Patch (zeroDivisionProgram n start).2 1156680 := by
  unfold zeroDivisionProgram
  exact Patch.surroundCompiled _ _ _ (divisionPatch n start)

def coordinatePatch (start : Nat) : Patch (coordinateProgram start).2 1156680 := by
  unfold coordinateProgram coordinateSegments
  refine (Patch.sequenceCons (d := 0) (f := 1156680) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 1156680) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons _ _ (zeroDivisionPatch 32768 _) (Patch.refl _)).castSaving (by omega)

def corePatch (start : Nat) : Patch (Single.Physical.core start).2 1156680 := by
  unfold Single.Physical.core Single.Physical.segments
  exact (Patch.sequenceCons (d := 1156680) (f := 0) _ _ (coordinatePatch start) (Patch.refl _)).castSaving (by omega)

def preparedPatch (start : Nat) : Patch (Single.Physical.prepared start).2 1156680 := by
  unfold Single.Physical.prepared
  exact Patch.surroundCompiled _ _ _ (corePatch start)

def actualPatch (start : Nat) : Patch (Single.Physical.actual.program start) 1156680 := by
  unfold Single.Physical.actual closedWindow
  exact (((preparedPatch 0).relabel (windowAddressPerm 855 (by decide))).castFinish _).shift start

def signedPatch (w : Single.SignedWindow) (start : Nat) :
    Patch ((Single.signedWindow w).program start) 1156680 := by
  unfold Single.signedWindow
  exact (actualPatch start).reindex (Single.signedRow w)

def preparePatch {n s e d} (ws : List Wire) {p : Straight n s e} (hp : Patch p d) :
    Patch (prepareOuterBank ws p) d := by
  induction ws with
  | nil => exact hp
  | cons w ws ih => exact Patch.gate (.literal (.H w)) ih

structure PatchedWindow (n : Nat) where
  source : Single.Window n
  saving : Nat
  patch : ∀ start, Patch (source.program start) saving

def leftPatches : List (PatchedWindow 851968) :=
  ⟨Single.firstWindow,0,fun _ => Patch.refl _⟩ ::
    Single.leftSigned.map (fun w => ⟨Single.signedWindow w,1156680,signedPatch w⟩)
def rightPatches : List (PatchedWindow 851968) :=
  Single.rightSigned.map (fun w => ⟨Single.signedWindow w,1156680,signedPatch w⟩)
private theorem leftPatches_source : leftPatches.map PatchedWindow.source = Single.leftWindows := by
  simp [leftPatches, Single.leftWindows]
private theorem rightPatches_source : rightPatches.map PatchedWindow.source = Single.rightWindows := by
  simp [rightPatches, Single.rightWindows]
private theorem leftPatches_saving : (leftPatches.map PatchedWindow.saving).sum = 18506880 := by
  simp [leftPatches, Single.leftSigned]
private theorem rightPatches_saving : (rightPatches.map PatchedWindow.saving).sum = 19663560 := by
  simp [rightPatches, Single.rightSigned]

def axisPatch {n} : (ps : List (PatchedWindow n)) → (start : Nat) → (prior : List (Fin start)) →
    Patch (Single.axis (ps.map PatchedWindow.source) start prior) ((ps.map PatchedWindow.saving).sum)
  | [], _, _ => Patch.refl _
  | p::ps, start, prior => by
    simp only [List.map_cons, List.sum_cons, Single.axis]
    refine Patch.castFinish ?_ _
    refine Patch.castSaving (Patch.append (f := (ps.map PatchedWindow.saving).sum) (preparePatch _ (p.patch start)) ?_) (by omega)
    exact (Patch.append (Patch.refl _) (axisPatch ps _ (Single.nextPrior p.source.count p.source.wires.length prior))).castSaving (by omega)

def axisPatchFor {n} (ps : List (PatchedWindow n)) (ws : List (Single.Window n))
    (he : ps.map PatchedWindow.source = ws) (start : Nat) (prior : List (Fin start)) :
    Patch (Single.axis ws start prior) ((ps.map PatchedWindow.saving).sum) := by
  subst ws
  exact axisPatch ps start prior

def Patch.framed {n s m k e f dl dr} (p : Straight n s m) (q : Straight n m k)
    (r : Straight n k e) (h : e=f) (hp : Patch p dl) (hq : Patch q dr) :
    Patch (Single.framed p q r h) (dl+dr) := by
  unfold Single.framed
  exact Patch.gate _ ((Patch.append hp ((Patch.append hq (Patch.gate _ (Patch.refl _))).castSaving (Nat.add_zero dr))).castFinish h)

def trialPatch (start : Nat) : Patch (Single.trial start) 38170440 := by
  have hl := (axisPatchFor leftPatches Single.leftWindows leftPatches_source start List.nil).castSaving leftPatches_saving
  have hr := (axisPatchFor rightPatches Single.rightWindows rightPatches_source
    (start+Single.axisCount Single.leftWindows) List.nil).castSaving rightPatches_saving
  unfold Single.trial
  exact (Patch.framed _ _ _ _ hl hr).castSaving (by decide)

def programPatch : Patch Single.program 38170440 := by
  unfold Single.program
  exact (trialPatch 0).castFinish _

def Patch.fixedEntry {n e d} (f : Fin n → PointCoeff) (p : Straight n 0 e) (hp : Patch p d) :
    Patch (Single.fixedEntry f p).program d := by
  unfold Single.fixedEntry
  exact hp.reindex _

def entryPatch : Patch Single.entry.program 38170440 := by
  unfold Single.entry
  exact Patch.fixedEntry Single.mixedCoefficientAt _ programPatch
end
end ShorECDLP.Entrant.Optimization

namespace ShorECDLP.Entrant.Parent
open Challenge
noncomputable def entry : StraightEntry := Optimization.replaceEntry Single.entry Optimization.entryPatch.program
def layout : DecodeLayout := Single.layout
def bounds : Bounds := ⟨Single.bounds.qubits, Single.bounds.tModel - 38170440, Single.bounds.measurements⟩
theorem certificate : Certificate officialLimits layout entry bounds :=
  Optimization.replacement_certificate Single.certificate Optimization.entryPatch.drops Optimization.entryPatch.rewrites
end ShorECDLP.Entrant.Parent
end
end

section
namespace ShorECDLP.Entrant.AndGadget
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unnecessarySeqFocus false
set_option Elab.async false
attribute [local irreducible] sequenceProgram appendCompiled literalProgram coordinateProgram zeroDivisionProgram
 Single.axis Single.entry

theorem AtLeast.gate {n s e d} (g : TemplateGate n) {p : Straight n s e} (hp : AtLeast p d) :
    AtLeast (.gate g p) d := by
  cases g with
  | literal g => cases g <;> simp_all [AtLeast, added] <;> omega
  | whenBit => exact hp

theorem coreCount (start : Nat) : AtLeast (Single.Physical.core start).2 63089956 := by
  unfold Single.Physical.core Single.Physical.segments
  exact (AtLeast.sequenceCons (d := 63089956) (f := 0) _ _ (coordinateAllCount start) (AtLeast.zero _)).castCount (by omega)

theorem preparedCount (start : Nat) : AtLeast (Single.Physical.prepared start).2 63089956 := by
  unfold Single.Physical.prepared
  exact AtLeast.surroundCompiled _ _ _ (coreCount start)

theorem actualCount (start : Nat) : AtLeast (Single.Physical.actual.program start) 63089956 := by
  unfold Single.Physical.actual closedWindow
  exact (((preparedCount 0).relabel (windowAddressPerm 855 (by decide))).castFinish _).shift start

theorem signedCount (w : Single.SignedWindow) (start : Nat) :
    AtLeast ((Single.signedWindow w).program start) 63089956 := by
  unfold Single.signedWindow
  exact (actualCount start).reindex (Single.signedRow w)

theorem prepareCount {n s e d} (ws : List Wire) {p : Straight n s e} (hp : AtLeast p d) :
    AtLeast (prepareOuterBank ws p) d := by
  induction ws with
  | nil => exact hp
  | cons w ws ih => exact AtLeast.gate (.literal (.H w)) ih

structure CountedWindow (n : Nat) where
  source : Single.Window n
  saving : Nat
  countProof : ∀ start, AtLeast (source.program start) saving

def leftCountes : List (CountedWindow 851968) :=
  ⟨Single.firstWindow,0,fun _ => AtLeast.zero _⟩ ::
    Single.leftSigned.map (fun w => ⟨Single.signedWindow w,63089956,signedCount w⟩)
def rightCountes : List (CountedWindow 851968) :=
  Single.rightSigned.map (fun w => ⟨Single.signedWindow w,63089956,signedCount w⟩)
private theorem leftCountes_source : leftCountes.map CountedWindow.source = Single.leftWindows := by
  simp [leftCountes, Single.leftWindows]
private theorem rightCountes_source : rightCountes.map CountedWindow.source = Single.rightWindows := by
  simp [rightCountes, Single.rightWindows]
private theorem leftCountes_saving : (leftCountes.map CountedWindow.saving).sum = 1009439296 := by
  simp [leftCountes, Single.leftSigned]
private theorem rightCountes_saving : (rightCountes.map CountedWindow.saving).sum = 1072529252 := by
  simp [rightCountes, Single.rightSigned]

theorem axisCountProof {n} : (ps : List (CountedWindow n)) → (start : Nat) → (prior : List (Fin start)) →
    AtLeast (Single.axis (ps.map CountedWindow.source) start prior) ((ps.map CountedWindow.saving).sum)
  | [], _, _ => AtLeast.zero _
  | p::ps, start, prior => by
    simp only [List.map_cons, List.sum_cons, Single.axis]
    refine AtLeast.castFinish ?_ _
    refine AtLeast.castCount (AtLeast.append (f := (ps.map CountedWindow.saving).sum) (prepareCount _ (p.countProof start)) ?_) (by omega)
    exact (AtLeast.append (AtLeast.zero _) (axisCountProof ps _ (Single.nextPrior p.source.count p.source.wires.length prior))).castCount (by omega)

theorem axisCountFor {n} (ps : List (CountedWindow n)) (ws : List (Single.Window n))
    (he : ps.map CountedWindow.source = ws) (start : Nat) (prior : List (Fin start)) :
    AtLeast (Single.axis ws start prior) ((ps.map CountedWindow.saving).sum) := by
  subst ws
  exact axisCountProof ps start prior

theorem AtLeast.framed {n s m k e f dl dr} (p : Straight n s m) (q : Straight n m k)
    (r : Straight n k e) (h : e=f) (hp : AtLeast p dl) (hq : AtLeast q dr) :
    AtLeast (Single.framed p q r h) (dl+dr) := by
  unfold Single.framed
  exact AtLeast.gate _ ((AtLeast.append hp ((AtLeast.append hq (AtLeast.gate _ (AtLeast.zero _))).castCount (Nat.add_zero dr))).castFinish h)

theorem trialCount (start : Nat) : AtLeast (Single.trial start) 2081968548 := by
  have hl := (axisCountFor leftCountes Single.leftWindows leftCountes_source start List.nil).castCount leftCountes_saving
  have hr := (axisCountFor rightCountes Single.rightWindows rightCountes_source
    (start+Single.axisCount Single.leftWindows) List.nil).castCount rightCountes_saving
  unfold Single.trial
  exact (AtLeast.framed _ _ _ _ hl hr).castCount (by decide)

theorem programCount : AtLeast Single.program 2081968548 := by
  unfold Single.program
  exact (trialCount 0).castFinish _

theorem AtLeast.fixedEntry {n e d} (f : Fin n → PointCoeff) (p : Straight n 0 e) (hp : AtLeast p d) :
    AtLeast (Single.fixedEntry f p).program d := by
  unfold Single.fixedEntry
  exact hp.reindex _

theorem entryCount : AtLeast Single.entry.program 2081968548 := by
  unfold Single.entry
  exact AtLeast.fixedEntry Single.mixedCoefficientAt _ programCount

theorem dropped_added {n s e d} {p q : Straight n s e} (h : Optimization.Drops p q d) :
    7 * added p ≤ 7 * added q + d := by
  induction h with
  | refl => omega
  | skip g h ih => cases g <;> simp_all [added, tCost] <;> omega
  | gate g h ih =>
    cases g with
    | literal g => cases g <;> simp_all [added] <;> omega
    | whenBit => exact ih
  | record => assumption
  | measure => assumption

attribute [local irreducible] added lower lowerEntry lowerLayout Optimization.entryPatch


theorem parent_added_lower : 2076515628 ≤ added Parent.entry.program := by
  have h := dropped_added Optimization.entryPatch.drops
  have hc := entryCount
  change 2081968548 ≤ added Single.entry.program at hc
  unfold Parent.entry Optimization.replaceEntry
  change 2076515628 ≤ added Optimization.entryPatch.program
  omega


theorem within_reindex {n m s e} (p : Straight n s e) (f : Fin n → Fin m) (ws : List Wire)
    (hp : Within ws p) : Within ws (reindexStraight f p) := by
  induction p with
  | done => trivial
  | gate g p ih => cases g <;> exact ⟨hp.1, ih hp.2⟩
  | recordGate => exact ⟨hp.1, by apply_assumption; exact hp.2⟩
  | measure => exact ⟨hp.1, by apply_assumption; exact hp.2⟩


theorem within_drops {n s e d} {p q : Straight n s e} (h : Optimization.Drops p q d)
    (ws : List Wire) (hp : Within ws p) : Within ws q := by
  induction h with
  | refl => exact hp
  | skip g h ih => exact ih hp.2
  | gate g h ih => cases g <;> exact ⟨hp.1, ih hp.2⟩
  | record i v g h ih => exact ⟨hp.1, ih hp.2⟩
  | measure w h ih => exact ⟨hp.1, ih hp.2⟩


theorem fixedEntry_within {n e} (f : Fin n → PointCoeff) (p : Straight n 0 e)
    (ws : List Wire) (hp : Within ws p) : Within ws (Single.fixedEntry f p).program :=
  within_reindex p _ ws hp


attribute [local irreducible] Within

theorem parent_within : Within completeBatchedSupport Parent.entry.program := by
  unfold Parent.entry Optimization.replaceEntry
  apply within_drops Optimization.entryPatch.drops
  unfold Single.entry
  apply fixedEntry_within
  apply within_of_instantiate
  intro read history
  have he : history = Fin.elim0 := by funext i; exact Fin.elim0 i
  subst history
  exact Single.program_support read


set_option maxRecDepth 2000

theorem parent_added_upper : added Parent.entry.program ≤ 8450153389 := by
  have h := lower_t 1024 Parent.entry.program 0 Fin.elim0
    (readConstant Parent.entry.coefficients.get 0) Fin.elim0 Fin.elim0
    (by funext i; exact Fin.elim0 i)
  have ht := (Parent.certificate.resources 0).2.1
  change (Parent.entry.program.instantiate (readConstant Parent.entry.coefficients.get 0) Fin.elim0).tCount ≤ 16900306778 at ht
  omega


theorem parent_slots : Parent.entry.program.gateSlots ≤ 102000069434 := by
  have hs := Optimization.entryPatch.drops.slots
  have ho : Single.entry.program.gateSlots ≤ 102000069434 := by
    rw [Single.entry, Single.fixedEntry_slots]
    exact Single.program_slots
  unfold Parent.entry Optimization.replaceEntry
  exact hs.trans ho

end
end ShorECDLP.Entrant.AndGadget

namespace ShorECDLP.Entrant
open Challenge AndGadget Paper2607_13816.ChallengeMigration
attribute [local irreducible] Within
set_option maxRecDepth 10000
attribute [local irreducible] added lower lowerEntry lowerLayout Optimization.entryPatch
noncomputable def entry : StraightEntry := lowerEntry 1024 Parent.entry
noncomputable def layout : DecodeLayout := lowerLayout 1024 Parent.entry Parent.layout
def bounds : Bounds := ⟨856, 12747275522, 9463545925⟩

private theorem resourceArithmetic (a slots cursor oldT newT maxSlots maxRecords newRecords : Nat)
    (ha : a ≤ 8450153389) (hl : 2076515628 ≤ a) (hs : slots ≤ 102000069434)
    (hc : cursor ≤ 1013392536) (ho : oldT ≤ 16900306778) (hn : 12747275522 ≤ newT)
    (hls : 4000000000000000 ≤ maxSlots) (hlm : 47471340504 ≤ maxRecords)
    (hnm : 9463545925 ≤ newRecords) :
    slots + 18*a ≤ maxSlots ∧ cursor+a ≤ maxRecords ∧ oldT ≤ newT + 2*a ∧
    cursor+a ≤ newRecords := by omega

theorem certificate : Certificate officialLimits layout entry bounds := by
  have h := resourceArithmetic (added Parent.entry.program) Parent.entry.program.gateSlots
    Parent.entry.finalCursor Parent.bounds.tModel bounds.tModel officialLimits.gateSlots
    officialLimits.measurements bounds.measurements
    parent_added_upper parent_added_lower parent_slots (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  apply lower_certificate officialLimits Parent.layout Parent.entry Parent.bounds bounds
    1024 completeBatchedSupport Parent.certificate parent_within
  · simp [completeBatchedSupport, resetWires]
  · exact h.1
  · exact h.2.1
  · change completeBatchedSupport.length + 1 ≤ 856
    rw [completeBatchedSupport_length]
  · exact h.2.2.1
  · exact h.2.2.2
end ShorECDLP.Entrant
end
