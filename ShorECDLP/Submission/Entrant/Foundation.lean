import ShorECDLP.Submission.«2607_13816».Challenge.Support
import ShorECDLP.Challenge.Official
import ShorECDLP.Submission.«2607_13816».EEA.LengthPrimitiveCounts
import ShorECDLP.Framework.Quantum.InnerProduct
import ShorECDLP.Submission.«2607_13816».EEA.Preprocess
import ShorECDLP.Submission.«2607_13816».EEA.BlockAPrimitiveCounts
import ShorECDLP.Challenge.Contract
import ShorECDLP.Submission.«2607_13816».Challenge.OuterResources
import ShorECDLP.Submission.«2607_13816».Challenge.CursorShift
import ShorECDLP.Framework.Quantum.AdaptiveDisjoint

namespace ShorECDLP.Entrant.FoundationCancellation
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

end ShorECDLP.Entrant.FoundationCancellation

namespace ShorECDLP.Entrant.FoundationCancellation
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

end ShorECDLP.Entrant.FoundationCancellation



namespace ShorECDLP.Entrant.Transport
open Quantum
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def source (a b t u : Wire) : Circuit := [.CCX a b t,.CX t u,.CCX a b t]
def reduced (a b t u : Wire) : Circuit := [.CX t u,.CCX a b u]

theorem classical_identity (a b t u : Wire)
    (hat : a≠t) (hbt : b≠t) (hau : a≠u) (hbu : b≠u) (htu : t≠u)
    (s : BasisState) : Classical.run (source a b t u) s=Classical.run (reduced a b t u) s := by
  funext w
  simp only [source,reduced,Classical.run,List.foldl_cons,List.foldl_nil,Classical.applyGate]
  by_cases hwu : w=u
  · subst w
    simp [upd,Ne.symm hat,Ne.symm hbt,Ne.symm hau,Ne.symm hbu,htu,Ne.symm htu,
      hat,hbt,hau,hbu,Bool.xor_assoc,Bool.xor_left_comm,Bool.xor_comm]
  · by_cases hwt : w=t
    · subst w
      simp [upd,Ne.symm hat,Ne.symm hbt,Ne.symm hau,Ne.symm hbu,htu,Ne.symm htu,
        hat,hbt,hau,hbu,Bool.xor_assoc]
    · simp [upd,hwu,hwt]

theorem run_identity (a b t u : Wire)
    (hat : a≠t) (hbt : b≠t) (hau : a≠u) (hbu : b≠u) (htu : t≠u) :
    Quantum.run (source a b t u)=Quantum.run (reduced a b t u) := by
  have hk (s : BasisState) : Quantum.run (source a b t u) (ket s)=
      Quantum.run (reduced a b t u) (ket s) := by
    rw [run_ket_agrees_classical _ _ (by simp [source,Classical.HPFree,Classical.IsClassicalGate]),
      run_ket_agrees_classical _ _ (by simp [reduced,Classical.HPFree,Classical.IsClassicalGate]),
      classical_identity a b t u hat hbt hau hbu htu]
  apply LinearMap.ext
  intro ψ
  induction ψ using Finsupp.induction with
  | zero=>simp only [map_zero]
  | @single_add s c ψ hs hc ih=>
    have he : Finsupp.single s c=c•ket s := by simp [ket]
    simp only [map_add,he,map_smul,ih,hk]

/-- Only adjacent exact conjugations are compressed; no clean-workspace premise. -/
def optimize : Circuit→Circuit
  | .CCX a b t :: .CX v u :: .CCX c d z :: rest=>
    if a=c ∧ b=d ∧ t=v ∧ t=z ∧ a≠u ∧ b≠u ∧ t≠u ∧ a≠t ∧ b≠t then
      .CX t u :: .CCX a b u :: optimize rest
    else .CCX a b t :: optimize (.CX v u :: .CCX c d z :: rest)
  | g::rest=>g::optimize rest
  | []=>[]

end ShorECDLP.Entrant.Transport
namespace ShorECDLP.Entrant.Transport
open Quantum
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

inductive Reduction : Circuit→Circuit→Prop where
  | nil : Reduction List.nil List.nil
  | keep (g : Gate) {xs ys : Circuit} : Reduction xs ys→Reduction (g::xs) (g::ys)
  | fuse (a b t u : Wire) (hat : a≠t) (hbt : b≠t) (hau : a≠u) (hbu : b≠u) (htu : t≠u)
      {xs ys : Circuit} : Reduction xs ys→
      Reduction (.CCX a b t :: .CX t u :: .CCX a b t :: xs) (.CX t u :: .CCX a b u :: ys)

theorem optimize_rel (xs : Circuit) : Reduction xs (optimize xs) := by
  induction xs using optimize.induct with
  | case1 a b t v u c d z rest h ih=>
    rw [optimize,if_pos h]
    rcases h with ⟨rfl,rfl,rfl,rfl,hau,hbu,htu,hat,hbt⟩
    exact Reduction.fuse _ _ _ _ hat hbt hau hbu htu ih
  | case2 a b t v u c d z rest h ih=>
    rw [optimize,if_neg h]
    exact Reduction.keep _ ih
  | case3 g rest h ih=>
    rw [optimize.eq_2 g rest h]
    exact Reduction.keep _ ih
  | case4=>exact Reduction.nil

theorem Reduction.run {xs ys : Circuit} (h : Reduction xs ys) : Quantum.run xs=Quantum.run ys := by
  induction h with
  | nil=>rfl
  | keep g h ih=>
    apply LinearMap.ext
    intro ψ
    simp only [Quantum.run_cons,ih]
  | fuse a b t u hat hbt hau hbu htu h ih=>
    have he:=run_identity a b t u hat hbt hau hbu htu
    apply LinearMap.ext
    intro ψ
    have hh:=congrArg (fun m : State→ₗ[ℂ]State=>m ψ) he
    simp only [source,reduced,Quantum.run_cons,Quantum.run_nil] at hh
    simpa only [Quantum.run_cons,ih] using congrArg (Quantum.run _) hh

end ShorECDLP.Entrant.Transport

namespace ShorECDLP.Entrant.ControlTransport
open Quantum
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def source (a b t : Wire) : Circuit := [.CCX a b t,.CX a b,.CCX a b t]
def reduced (a b t : Wire) : Circuit := [.CX a b,.CX a t]

theorem classical_identity (a b t : Wire) (hab : a≠b) (hat : a≠t) (hbt : b≠t)
    (s : BasisState) : Classical.run (source a b t) s=Classical.run (reduced a b t) s := by
  funext w
  simp only [source,reduced,Classical.run,List.foldl_cons,List.foldl_nil,Classical.applyGate]
  by_cases hwt : w=t
  · subst w
    cases ha:s a <;> cases hb:s b <;> cases ht:s t <;>
      simp_all [upd,Ne.symm hab,Ne.symm hat,Ne.symm hbt]
  · by_cases hwb : w=b
    · subst w
      simp [upd,Ne.symm hab,Ne.symm hat,Ne.symm hbt,hab,hat,hbt]
    · simp [upd,hwt,hwb]

theorem run_identity (a b t : Wire) (hab : a≠b) (hat : a≠t) (hbt : b≠t) :
    Quantum.run (source a b t)=Quantum.run (reduced a b t) := by
  have hk (s : BasisState) : Quantum.run (source a b t) (ket s)=
      Quantum.run (reduced a b t) (ket s) := by
    rw [run_ket_agrees_classical _ _ (by simp [source,Classical.HPFree,Classical.IsClassicalGate]),
      run_ket_agrees_classical _ _ (by simp [reduced,Classical.HPFree,Classical.IsClassicalGate]),
      classical_identity a b t hab hat hbt]
  apply LinearMap.ext
  intro ψ
  induction ψ using Finsupp.induction with
  | zero=>simp only [map_zero]
  | @single_add s c ψ hs hc ih=>
    have he : Finsupp.single s c=c•ket s := by simp [ket]
    simp only [map_add,he,map_smul,ih,hk]

set_option linter.unnecessarySeqFocus false
/-- Compress the adjacent control-fanout conjugation on arbitrary input states. -/
def optimize : Circuit→Circuit
  | .CCX a b t :: .CX v u :: .CCX c d z :: rest=>
    if a=c ∧ b=d ∧ t=z ∧ a=v ∧ b=u ∧ a≠b ∧ a≠t ∧ b≠t then
      .CX a b :: .CX a t :: optimize rest
    else .CCX a b t :: optimize (.CX v u :: .CCX c d z :: rest)
  | g::rest=>g::optimize rest
  | []=>[]

inductive Reduction : Circuit→Circuit→Prop where
  | nil : Reduction List.nil List.nil
  | keep (g : Gate) {xs ys : Circuit} : Reduction xs ys→Reduction (g::xs) (g::ys)
  | fuse (a b t : Wire) (hab : a≠b) (hat : a≠t) (hbt : b≠t)
      {xs ys : Circuit} : Reduction xs ys→
      Reduction (.CCX a b t :: .CX a b :: .CCX a b t :: xs) (.CX a b :: .CX a t :: ys)

theorem optimize_rel (xs : Circuit) : Reduction xs (optimize xs) := by
  induction xs using optimize.induct with
  | case1 a b t v u c d z rest h ih=>
    rw [optimize,if_pos h]
    rcases h with ⟨rfl,rfl,rfl,rfl,rfl,hab,hat,hbt⟩
    exact Reduction.fuse _ _ _ hab hat hbt ih
  | case2 a b t v u c d z rest h ih=>
    rw [optimize,if_neg h]
    exact Reduction.keep _ ih
  | case3 g rest h ih=>
    rw [optimize.eq_2 g rest h]
    exact Reduction.keep _ ih
  | case4=>exact Reduction.nil

theorem Reduction.run {xs ys : Circuit} (h : Reduction xs ys) : Quantum.run xs=Quantum.run ys := by
  induction h with
  | nil=>rfl
  | keep g h ih=>
    apply LinearMap.ext
    intro ψ
    simp only [Quantum.run_cons,ih]
  | fuse a b t hab hat hbt h ih=>
    have he:=run_identity a b t hab hat hbt
    apply LinearMap.ext
    intro ψ
    have hh:=congrArg (fun m : State→ₗ[ℂ]State=>m ψ) he
    simp only [source,reduced,Quantum.run_cons,Quantum.run_nil] at hh
    simpa only [Quantum.run_cons,ih] using congrArg (Quantum.run _) hh

theorem Reduction.tle {xs ys : Circuit} (h : Reduction xs ys) :
    ShorECDLP.tCount ys≤ShorECDLP.tCount xs := by
  induction h <;> simp_all [ShorECDLP.tCount_cons,tCost] <;> omega
end ShorECDLP.Entrant.ControlTransport

namespace ShorECDLP.Entrant.TransportOptimization
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
  | transport {s e} (a b t u : Wire)
      (hh : a≠t ∧ b≠t ∧ a≠u ∧ b≠u ∧ t≠u)
      {p q : Straight n s e} {d : Nat} : Drops p q d→
      Drops (.gate (.literal (.CCX a b t)) (.gate (.literal (.CX t u))
        (.gate (.literal (.CCX a b t)) p)))
        (.gate (.literal (.CX t u)) (.gate (.literal (.CCX a b u)) q)) (7+d)
  | control {s e} (a b t : Wire) (hh : a≠b ∧ a≠t ∧ b≠t)
      {p q : Straight n s e} {d : Nat} : Drops p q d→
      Drops (.gate (.literal (.CCX a b t)) (.gate (.literal (.CX a b))
        (.gate (.literal (.CCX a b t)) p)))
        (.gate (.literal (.CX a b)) (.gate (.literal (.CX a t)) q)) (14+d)
  | swap {s e} (g k : Gate) {p q : Straight n s e} {d : Nat} : Drops p q d →
      Drops (.gate (.literal g) (.gate (.literal k) p))
        (.gate (.literal k) (.gate (.literal g) q)) d
  | trans {s e} {p q r : Straight n s e} {d f : Nat} :
      Drops p q d → Drops q r f → Drops p r (d+f)

theorem Drops.wellFormed {n s e d} {p q : Straight n s e}
    (h : Drops p q d) (hp : p.WellFormed) : q.WellFormed := by
  induction h with
  | refl => exact hp
  | skip g h ih => exact ih hp.2
  | gate g h ih => exact ⟨hp.1, ih hp.2⟩
  | record i v g h ih => exact ⟨hp.1, ih hp.2⟩
  | measure w h ih => exact ih hp

  | swap g k h ih => exact ⟨hp.2.1,hp.1,ih hp.2.2⟩
  | transport a b t u hh h ih=>
    simp only [Straight.WellFormed,TemplateGate.WellFormed,Gate.WellFormed] at hp ⊢
    exact ⟨hp.2.1,⟨⟨hp.1.1,hh.2.2.1,hh.2.2.2.1⟩,ih hp.2.2.2⟩⟩
  | control a b t hh h ih=>
    simp only [Straight.WellFormed,TemplateGate.WellFormed,Gate.WellFormed] at hp ⊢
    exact ⟨hp.2.1,⟨hp.1.2.1,ih hp.2.2.2⟩⟩

  | trans h k ih ik=>exact ik (ih hp)
theorem Drops.slots {n s e d} {p q : Straight n s e}
    (h : Drops p q d) : q.gateSlots ≤ p.gateSlots := by
  induction h <;> (try simp_all [Straight.gateSlots]) <;> omega

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

  | swap g k h ih =>
    have hi := ih history
    simp only [Straight.instantiate,TemplateGate.instantiate,AdaptiveCircuit.tCount]
    omega
  | transport a b t u hh h ih=>
    have hi:=ih history
    simp only [Straight.instantiate,TemplateGate.instantiate,AdaptiveCircuit.tCount,
      ShorECDLP.tCount,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,tCost]
    omega
  | control a b t hh h ih=>
    have hi:=ih history
    simp only [Straight.instantiate,TemplateGate.instantiate,AdaptiveCircuit.tCount,
      ShorECDLP.tCount,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,tCost]
    omega
  | trans h k ih ik=>have hi:=ih history; have hk:=ik history; omega
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

  | swap g k h ih =>
    intro w hw
    have hi := ih history w
    simp only [Straight.instantiate,TemplateGate.instantiate,AdaptiveCircuit.wires,List.mem_append] at hw ⊢
    tauto
  | transport a b t u hh h ih=>
    intro w hw
    have hi:=ih history w
    simp only [Straight.instantiate,TemplateGate.instantiate,AdaptiveCircuit.wires,
      circuitWires,gateWires,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw ⊢
    tauto
  | control a b t hh h ih=>
    intro w hw
    have hi:=ih history w
    simp only [Straight.instantiate,TemplateGate.instantiate,AdaptiveCircuit.wires,
      circuitWires,gateWires,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw ⊢
    tauto
  | trans h k ih ik=>exact fun w hw=>ih history w (ik history w hw)
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
  induction hp generalizing f with
  | refl p => simpa using Drops.append_right p hq
  | skip g h ih => simpa [Nat.add_assoc] using Drops.skip g (ih hq)
  | gate g h ih => exact Drops.gate g (ih hq)
  | record i v g h ih => exact Drops.record i v g (ih hq)
  | measure w h ih => exact Drops.measure w (ih hq)

  | swap g k h ih => exact Drops.swap g k (ih hq)
  | transport a b t u hh h ih=>
    simpa only [Straight.append,Nat.add_assoc] using Drops.transport a b t u hh (ih hq)
  | control a b t hh h ih=>
    simpa only [Straight.append,Nat.add_assoc] using Drops.control a b t hh (ih hq)

  | trans h k ih ik=>
    have hl:=ih (Drops.refl q)
    have hr:=ik hq
    simpa only [Nat.add_zero,Nat.add_assoc] using Drops.trans hl hr
theorem tCount_le_of_sublist {xs ys : Circuit} (h : xs.Sublist ys) :
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

  | swap g k h ih => exact Drops.swap g k ih
  | transport a b t u hh h ih=>exact Drops.transport a b t u hh ih
  | control a b t hh h ih=>exact Drops.control a b t hh ih

  | trans h k ih ik=>exact Drops.trans ih ik
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

  | swap g k h ih => exact Drops.swap (g.relabel f) (k.relabel f) ih
  | transport a b t u hh h ih=>
    have hf : f a≠f t ∧ f b≠f t ∧ f a≠f u ∧ f b≠f u ∧ f t≠f u :=
      ⟨fun h=>hh.1 (f.injective h),fun h=>hh.2.1 (f.injective h),
       fun h=>hh.2.2.1 (f.injective h),fun h=>hh.2.2.2.1 (f.injective h),
       fun h=>hh.2.2.2.2 (f.injective h)⟩
    exact Drops.transport (f a) (f b) (f t) (f u) hf ih
  | control a b t hh h ih=>
    have hf : f a≠f b ∧ f a≠f t ∧ f b≠f t :=
      ⟨fun h=>hh.1 (f.injective h),fun h=>hh.2.1 (f.injective h),
       fun h=>hh.2.2 (f.injective h)⟩
    exact Drops.control (f a) (f b) (f t) hf ih

  | trans h k ih ik=>exact Drops.trans ih ik
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

  | swap g k h ih => exact Drops.swap g k ih
  | transport a b t u hh h ih=>exact Drops.transport a b t u hh ih
  | control a b t hh h ih=>exact Drops.control a b t hh ih

  | trans h k ih ik=>exact Drops.trans ih ik
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

end ShorECDLP.Entrant.TransportOptimization




namespace ShorECDLP.Entrant.Transport
open Quantum
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

theorem Reduction.tle {xs ys : Circuit} (h : Reduction xs ys) :
    ShorECDLP.tCount ys≤ShorECDLP.tCount xs := by
  induction h <;> simp_all [ShorECDLP.tCount_cons,tCost] <;> omega

end ShorECDLP.Entrant.Transport
namespace ShorECDLP.Entrant.TransportOptimization
open Quantum Challenge Paper2607_13816.ChallengeMigration
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

theorem transport_drops {xs ys : Circuit} (hr : Transport.Reduction xs ys) (n start : Nat) :
    Drops (literalProgram xs : Straight n start start) (literalProgram ys)
      (ShorECDLP.tCount xs-ShorECDLP.tCount ys) := by
  induction hr with
  | nil=>exact Drops.refl _
  | @keep g xs ys h ih=>
    simpa only [literalProgram,gateProgram,List.map_cons,ShorECDLP.tCount_cons,
      Nat.add_sub_add_left] using Drops.gate (.literal g) ih
  | @fuse a b t u hat hbt hau hbu htu xs ys h ih=>
    have ht:=h.tle
    have hh:=Drops.transport a b t u ⟨hat,hbt,hau,hbu,htu⟩ ih
    have hd : ShorECDLP.tCount (.CCX a b t :: .CX t u :: .CCX a b t :: xs)-
        ShorECDLP.tCount (.CX t u :: .CCX a b u :: ys)=
        7+(ShorECDLP.tCount xs-ShorECDLP.tCount ys) := by
      simp only [ShorECDLP.tCount_cons,tCost]
      omega
    rw [hd]
    exact hh

noncomputable def transportPatch (n start d : Nat) (xs : Circuit)
    (ht : ShorECDLP.tCount (Transport.optimize xs)+d=ShorECDLP.tCount xs) :
    Patch (literalProgram xs : Straight n start start) d := by
  refine ⟨literalProgram (Transport.optimize xs),?_,
    Rewrites.literal xs (Transport.optimize xs) (Transport.optimize_rel xs).run⟩
  have hd : ShorECDLP.tCount xs-ShorECDLP.tCount (Transport.optimize xs)=d := by omega
  simpa only [hd] using transport_drops (Transport.optimize_rel xs) n start

end ShorECDLP.Entrant.TransportOptimization

namespace ShorECDLP.Entrant.Initializer
open Quantum Paper2607_13816
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def prefixTail (acc : Wire) : List Wire → List Wire → Circuit
  | [], _ => []
  | [_], _ => []
  | c :: d :: cs, s :: ss => .CCX c acc s :: prefixTail s (d :: cs) ss
  | _ :: _ :: _, [] => []

def leafTail (acc : Wire) : List Wire → Wire → List Wire → Circuit
  | [], _, _ => []
  | [c], t, _ => [.CCX c acc t]
  | _ :: d :: cs, t, s :: ss => leafTail s (d :: cs) t ss
  | _ :: _ :: _, _, [] => []

def chainPrefix : List Wire → List Wire → Circuit
  | a :: b :: cs, ss => prefixTail b (a :: cs) ss
  | _, _ => []

def leaf : List Wire → Wire → List Wire → Circuit
  | [], t, _ => [.X t]
  | [a], t, _ => [.CX a t]
  | a :: b :: cs, t, ss => leafTail b (a :: cs) t ss

theorem tail_factor (acc : Wire) (cs : List Wire) (t : Wire) (ss : List Wire) :
    mcxVChainTail acc cs t ss = prefixTail acc cs ss ++ leafTail acc cs t ss ++ (prefixTail acc cs ss).adjoint := by
  induction cs generalizing acc ss with
  | nil => rfl
  | cons c cs ih =>
    cases cs with
    | nil => rfl
    | cons d cs =>
      cases ss with
      | nil => rfl
      | cons s ss =>
        simp only [mcxVChainTail, prefixTail, leafTail, ih, circuit_adjoint_cons,
          Gate.adjoint, List.cons_append, List.append_assoc, List.nil_append]

theorem factor (cs : List Wire) (t : Wire) (ss : List Wire) :
    mcxVChain cs t ss = chainPrefix cs ss ++ leaf cs t ss ++ (chainPrefix cs ss).adjoint := by
  cases cs with
  | nil => rfl
  | cons a cs =>
    cases cs with
    | nil => rfl
    | cons b cs => exact tail_factor b (a::cs) t ss

def before (cs : List Wire) (pat : Nat) (ss : List Wire) (v : Nat) : Circuit :=
  zeroMask cs pat ++ xorConstant ss v ++ chainPrefix cs ss

def after (cs : List Wire) (pat : Nat) (ss : List Wire) (v : Nat) : Circuit :=
  (chainPrefix cs ss).adjoint ++ xorConstant ss v ++ (zeroMask cs pat).adjoint

theorem known_factor (cs : List Wire) (pat : Nat) (t : Wire) (ss : List Wire) (v : Nat) :
    knownScratchControl cs pat t ss v = before cs pat ss v ++ leaf cs t ss ++ after cs pat ss v := by
  simp only [knownScratchControl,knownScratchMCX,factor,before,after,List.append_assoc]

def pairwiseCommutes (a b : Circuit) : Bool :=
  a.all fun x => b.all fun y => FoundationCancellation.commutes x y

theorem gate_circuit_commute (g : Gate) (c : Circuit)
    (h : ∀ a ∈ c, FoundationCancellation.commutes g a = true) (ψ : State) :
    applyGate g (Quantum.run c ψ) = Quantum.run c (applyGate g ψ) := by
  induction c generalizing ψ with
  | nil => rfl
  | cons a c ih =>
    simp only [Quantum.run_cons]
    rw [ih (fun b hb => h b (by simp [hb])), FoundationCancellation.quantum_commute g a (h a (by simp))]

theorem circuit_commute (a b : Circuit) (h : pairwiseCommutes a b = true) (ψ : State) :
    Quantum.run a (Quantum.run b ψ) = Quantum.run b (Quantum.run a ψ) := by
  induction a generalizing ψ with
  | nil => rfl
  | cons g a ih =>
    have hh : (∀ x ∈ b, FoundationCancellation.commutes g x = true) ∧ pairwiseCommutes a b = true := by
      simpa only [pairwiseCommutes,List.all_cons,Bool.and_eq_true,List.all_eq_true] using h
    simp only [Quantum.run_cons]
    rw [gate_circuit_commute g b hh.1, ih hh.2]

theorem xor_twice (ss : List Wire) (v : Nat) (hn : ss.Nodup) (ψ : State) :
    Quantum.run (xorConstant ss v) (Quantum.run (xorConstant ss v) ψ) = ψ := by
  induction ψ using Finsupp.induction with
  | zero => simp only [map_zero]
  | @single_add s c ψ hs hc ih =>
    have he : Finsupp.single s c = c • ket s := by simp [ket]
    simp only [map_add,he,map_smul,run_ket_agrees_classical _ _ (xorConstant_HPFree ss v),run_xorConstant_twice ss v s hn,ih]

theorem before_after (cs : List Wire) (pat : Nat) (ss : List Wire) (v : Nat)
    (hn : ss.Nodup) (hp : CircuitWellFormed (chainPrefix cs ss)) (ψ : State) :
    Quantum.run (before cs pat ss v) (Quantum.run (after cs pat ss v) ψ) = ψ := by
  simp only [before,after,Quantum.run_append]
  rw [Quantum.run_run_adjoint _ (zeroMask_wellFormed cs pat),xor_twice ss v hn,
    Quantum.run_run_adjoint _ hp]

def reducedCase (cs : List Wire) (pat : Nat) (ts : List Wire) (encoded : Nat)
    (flag : Wire) (ss : List Wire) (v : Nat) : Circuit :=
  before cs pat ss v ++ leaf cs flag ss ++ controlledXorConstant flag ts encoded ++
    leaf cs flag ss ++ after cs pat ss v

theorem reducedCase_run (cs : List Wire) (pat : Nat) (ts : List Wire) (encoded : Nat)
    (flag : Wire) (ss : List Wire) (v : Nat)
    (hn : ss.Nodup) (hp : CircuitWellFormed (chainPrefix cs ss))
    (hc : pairwiseCommutes (after cs pat ss v) (controlledXorConstant flag ts encoded) = true) :
    Quantum.run (lengthInitializeCase cs pat ts encoded flag ss v) =
      Quantum.run (reducedCase cs pat ts encoded flag ss v) := by
  apply LinearMap.ext
  intro ψ
  simp only [lengthInitializeCase,known_factor,reducedCase,Quantum.run_append]
  rw [← circuit_commute _ _ hc, before_after cs pat ss v hn hp]

theorem reducedCase_sublist (cs : List Wire) (pat : Nat) (ts : List Wire) (encoded : Nat)
    (flag : Wire) (ss : List Wire) (v : Nat) :
    (reducedCase cs pat ts encoded flag ss v).Sublist (lengthInitializeCase cs pat ts encoded flag ss v) := by
  simp only [lengthInitializeCase,known_factor,reducedCase,List.append_assoc]
  apply List.Sublist.append_left
  apply List.Sublist.append_left
  apply List.Sublist.trans _ (List.sublist_append_right (after cs pat ss v) _)
  apply List.Sublist.append_left
  exact List.sublist_append_right (before cs pat ss v) _
end ShorECDLP.Entrant.Initializer
namespace ShorECDLP.Entrant.Initializer
open Quantum Paper2607_13816
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem reducedCase_t (cs : List Wire) (pat : Nat) (ts : List Wire) (encoded : Nat)
    (flag : Wire) (ss : List Wire) (v : Nat) :
    ShorECDLP.tCount (reducedCase cs pat ts encoded flag ss v) +
      2 * ShorECDLP.tCount (chainPrefix cs ss) =
      ShorECDLP.tCount (lengthInitializeCase cs pat ts encoded flag ss v) := by
  simp only [lengthInitializeCase,known_factor,reducedCase,before,after,
    ShorECDLP.tCount_append,ShorECDLP.tCount_adjoint,zeroMask_tCount,xorConstant_tCount]
  omega

def rows := lengthInitializeCases (List.range' 266 256) 9
def targets := List.range' 549 9
def scratch := (List.range' 7 256).reverse.take 254
def modulus := 2^256-2^32-977

def scan : List (List Wire × Nat × Nat) → Circuit
  | [] => []
  | (cs,pat,encoded)::rs => reducedCase cs pat targets encoded 558 scratch modulus ++ scan rs

def saving : List (List Wire × Nat × Nat) → Nat
  | [] => 0
  | (cs,_,_)::rs => 2 * ShorECDLP.tCount (chainPrefix cs scratch) + saving rs

def Good (row : List Wire × Nat × Nat) : Prop :=
  CircuitWellFormed (chainPrefix row.1 scratch) ∧
  pairwiseCommutes (after row.1 row.2.1 scratch modulus)
    (controlledXorConstant 558 targets row.2.2) = true

private theorem scratch_nodup : scratch.Nodup := by decide +kernel

theorem scan_run (rs : List (List Wire × Nat × Nat)) (h : ∀ row ∈ rs, Good row) :
    Quantum.run (lengthInitializeScan targets 558 scratch modulus rs) = Quantum.run (scan rs) := by
  induction rs with
  | nil => rfl
  | cons row rs ih =>
    obtain ⟨cs,pat,encoded⟩ := row
    simp only [lengthInitializeScan,scan,Quantum.run_append_map]
    rw [reducedCase_run cs pat targets encoded 558 scratch modulus scratch_nodup
      (h (cs,pat,encoded) (by simp)).1 (h (cs,pat,encoded) (by simp)).2,ih (fun row hr => h row (by simp [hr]))]

theorem scan_sublist (rs : List (List Wire × Nat × Nat)) :
    (scan rs).Sublist (lengthInitializeScan targets 558 scratch modulus rs) := by
  induction rs with
  | nil => exact List.Sublist.refl _
  | cons row rs ih => exact (reducedCase_sublist _ _ _ _ _ _ _).append ih

theorem scan_t (rs : List (List Wire × Nat × Nat)) :
    ShorECDLP.tCount (scan rs) + saving rs =
      ShorECDLP.tCount (lengthInitializeScan targets 558 scratch modulus rs) := by
  induction rs with
  | nil => rfl
  | cons row rs ih =>
    obtain ⟨cs,pat,encoded⟩ := row
    simp only [scan,saving,lengthInitializeScan,ShorECDLP.tCount_append]
    have hr := reducedCase_t cs pat targets encoded 558 scratch modulus
    omega

private instance gateWFDecidable (g : Gate) : Decidable g.WellFormed := by
  cases g <;> unfold Gate.WellFormed <;> infer_instance

end ShorECDLP.Entrant.Initializer
namespace ShorECDLP.Entrant.Initializer
open Quantum Paper2607_13816 Classical
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem prefix_sublist (cs : List Wire) (t : Wire) (ss : List Wire) :
    (chainPrefix cs ss).Sublist (mcxVChain cs t ss) := by
  rw [factor]
  exact (List.sublist_append_left _ _).trans (List.sublist_append_left _ _)

theorem prefix_support (cs ss : List Wire) : PaperCircuitUsesOnly (cs ++ ss) (chainPrefix cs ss) := by
  intro g hg w hw
  have h0 := mcxVChain_usesOnly cs 0 ss g ((prefix_sublist cs 0 ss).subset hg) w hw
  have h1 := mcxVChain_usesOnly cs 1 ss g ((prefix_sublist cs 1 ss).subset hg) w hw
  simp only [List.mem_append,List.mem_cons] at *
  aesop

theorem after_support (cs : List Wire) (pat : Nat) (ss : List Wire) (v : Nat) :
    PaperCircuitUsesOnly (cs ++ ss) (after cs pat ss v) := by
  unfold after
  exact (prefix_support cs ss).adjoint.append ((xorConstant_usesOnly ss v).mono
    (fun w hw => List.mem_append_right _ hw)) |>.append
      ((zeroMask_usesOnly cs pat).adjoint.mono (fun w hw => List.mem_append_left _ hw))

theorem after_classical (cs : List Wire) (pat : Nat) (ss : List Wire) (v : Nat) :
    HPFree (after cs pat ss v) := by
  have h := knownScratchControl_HPFree cs pat 0 ss v
  rw [known_factor] at h
  intro g hg
  exact h g (by simp [hg])

theorem disjoint_commutes (a b : Circuit) (xs ys : List Wire)
    (ha : HPFree a) (hb : HPFree b) (hsa : PaperCircuitUsesOnly xs a)
    (hsb : PaperCircuitUsesOnly ys b) (hd : List.Disjoint xs ys) :
    pairwiseCommutes a b = true := by
  simp only [pairwiseCommutes,List.all_eq_true]
  intro g hg k hk
  have hga := ha g hg
  have hkb := hb k hk
  have hdis : ∀ w ∈ gateWires g, w ∉ gateWires k := by
    intro w hw hn
    exact List.disjoint_left.mp hd (hsa g hg w hw) (hsb k hk w hn)
  cases g <;> cases k <;>
    simp_all [IsClassicalGate,FoundationCancellation.commutes,FoundationCancellation.classicalGate,
      FoundationCancellation.controls,FoundationCancellation.target,gateWires]
  all_goals aesop

private theorem full_layout : ((List.range' 266 256) ++ 558 :: scratch).Nodup := by decide +kernel

theorem good_for (cs : List Wire) (pat enc : Nat) (hcs : cs.Sublist (List.range' 266 256)) :
    Good (cs,pat,enc) := by
  have hlen := hcs.length_le
  have hcap : cs.length-2 ≤ scratch.length := by
    have hs : scratch.length=254 := by decide
    simp only [List.length_range'] at hlen
    omega
  have hlay : McxVChainLayout cs 558 scratch :=
    (hcs.append (List.Sublist.refl _)).nodup full_layout
  constructor
  · intro g hg
    exact mcxVChain_wellFormed cs 558 scratch hcap hlay g ((prefix_sublist cs 558 scratch).subset hg)
  · apply disjoint_commutes _ _ (cs++scratch) (558::targets)
      (after_classical _ _ _ _) (controlledXorConstant_HPFree _ _ _)
      (after_support _ _ _ _) (controlledXorConstant_usesOnly _ _ _)
    apply List.disjoint_left.mpr
    intro w hw hn
    have hlo : w < 549 := by
      rcases List.mem_append.mp hw with hw | hw
      · have hh := hcs.subset hw
        simp only [List.mem_range',Nat.one_mul] at hh
        rcases hh with ⟨i, hi, rfl⟩
        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi _) (by decide)
      · have hh := List.mem_of_mem_take (show w ∈ (List.range' 7 256).reverse.take 254 from hw)
        simp only [List.mem_reverse,List.mem_range',Nat.one_mul] at hh
        rcases hh with ⟨i, hi, rfl⟩
        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi _) (by decide)
    simp only [List.mem_cons,targets,List.mem_range',Nat.one_mul] at hn
    rcases hn with rfl | ⟨i, hi, rfl⟩
    · exact (by decide : ¬ (558:Nat) < 549) hlo
    · exact Nat.not_lt_of_ge (Nat.le_add_right 549 i) hlo

theorem rows_good : ∀ row ∈ rows, Good row := by
  intro row hr
  simp only [rows,lengthInitializeCases,List.mem_append,List.mem_map,List.mem_range,
    List.mem_singleton] at hr
  rcases hr with ⟨i,hi,rfl⟩ | rfl
  · exact good_for _ _ _ (List.take_sublist _ _)
  · exact good_for _ _ _ (List.Sublist.refl _)

private theorem rows_saving : saving rows = 456946 := by decide +kernel

theorem initializer_run : Quantum.run (lengthInitialize (List.range' 266 256) targets 558 scratch modulus) =
    Quantum.run (scan rows) := scan_run rows rows_good

theorem initializer_sublist : (scan rows).Sublist (lengthInitialize (List.range' 266 256) targets 558 scratch modulus) := scan_sublist rows

theorem initializer_t : ShorECDLP.tCount (scan rows) + 456946 =
    ShorECDLP.tCount (lengthInitialize (List.range' 266 256) targets 558 scratch modulus) := by
  have h := scan_t rows
  rw [rows_saving] at h
  exact h
end ShorECDLP.Entrant.Initializer
namespace ShorECDLP.Entrant.Initializer
open Quantum Paper2607_13816
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

abbrev Row := List Wire × Nat × Nat

def mid (r : Row) : Circuit := leaf r.1 558 scratch ++
  controlledXorConstant 558 targets r.2.2 ++ leaf r.1 558 scratch

def extension (a b : Row) : Circuit :=
  (chainPrefix b.1 scratch).drop (chainPrefix a.1 scratch).length

def transition (a b : Row) : Circuit := [.X (a.1.getLastD 0)] ++ extension a b

def Compatible (a b : Row) : Prop :=
  zeroMask b.1 b.2.1 = zeroMask a.1 a.2.1 ++ [.X (a.1.getLastD 0)] ∧
  chainPrefix b.1 scratch = chainPrefix a.1 scratch ++ extension a b ∧
  pairwiseCommutes [.X (a.1.getLastD 0)] (chainPrefix a.1 scratch) = true ∧
  pairwiseCommutes [.X (a.1.getLastD 0)] (xorConstant scratch modulus) = true

instance compatibleDecidable (a b : Row) : Decidable (Compatible a b) := by
  unfold Compatible
  infer_instance

theorem boundary_run (a b : Row) (hg : Good a) (h : Compatible a b) (ψ : State) :
    Quantum.run (after a.1 a.2.1 scratch modulus ++ before b.1 b.2.1 scratch modulus) ψ =
      Quantum.run (transition a b) ψ := by
  rcases h with ⟨hm,hp,hcp,hcx⟩
  simp only [after,before,transition,hm,hp,Quantum.run_append]
  rw [Quantum.run_run_adjoint _ (zeroMask_wellFormed _ _)]
  rw [← circuit_commute _ _ hcx]
  rw [xor_twice scratch modulus (by decide +kernel)]
  rw [← circuit_commute _ _ hcp]
  rw [Quantum.run_run_adjoint _ hg.1]

theorem boundary_sublist (a b : Row) (h : Compatible a b) :
    (transition a b).Sublist (after a.1 a.2.1 scratch modulus ++ before b.1 b.2.1 scratch modulus) := by
  rcases h with ⟨hm,hp,_,_⟩
  apply List.Sublist.trans _ (List.sublist_append_right _ _)
  simp only [transition,before,hm,hp,List.append_assoc]
  apply List.Sublist.trans _ (List.sublist_append_right _ _)
  exact (List.Sublist.refl _).append
    ((List.sublist_append_right _ _).trans (List.sublist_append_right _ _))

theorem boundary_t (a b : Row) (h : Compatible a b) :
    ShorECDLP.tCount (transition a b) + 2 * ShorECDLP.tCount (chainPrefix a.1 scratch) =
      ShorECDLP.tCount (after a.1 a.2.1 scratch modulus ++ before b.1 b.2.1 scratch modulus) := by
  rcases h with ⟨_,hp,_,_⟩
  simp only [transition,after,before,hp,ShorECDLP.tCount_append,
    ShorECDLP.tCount_adjoint,zeroMask_tCount,xorConstant_tCount]
  simp only [ShorECDLP.tCount,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,ShorECDLP.tCost]
  omega

/-- Emit the current row's middle, sharing adjacent chain prefixes. -/
def sharedTail (a : Row) : List Row → Circuit
  | [] => mid a ++ after a.1 a.2.1 scratch modulus
  | b::rs => mid a ++ transition a b ++ sharedTail b rs

def shared : List Row → Circuit
  | [] => []
  | a::rs => before a.1 a.2.1 scratch modulus ++ sharedTail a rs

def sharingSaving (a : Row) : List Row → Nat
  | [] => 0
  | b::rs => 2 * ShorECDLP.tCount (chainPrefix a.1 scratch) + sharingSaving b rs


theorem sharedTail_run (a : Row) (rs : List Row)
    (hg : ∀ r ∈ a::rs, Good r) (hc : (a::rs).IsChain Compatible) (ψ : State) :
    Quantum.run (sharedTail a rs) ψ =
      Quantum.run (mid a ++ after a.1 a.2.1 scratch modulus ++ scan rs) ψ := by
  induction rs generalizing a ψ with
  | nil => simp only [sharedTail,scan,List.append_nil]
  | cons b rs ih =>
    have hh := List.isChain_cons_cons.mp hc
    have hb : ∀ r ∈ b::rs, Good r := fun r hr => hg r (List.mem_cons_of_mem _ hr)
    simp only [sharedTail,Quantum.run_append]
    rw [ih b hb hh.2]
    simp only [scan,reducedCase,mid,Quantum.run_append]
    have he := boundary_run a b (hg a (by simp)) hh.1
    simp only [Quantum.run_append] at he
    rw [← he]

theorem sharedTail_sublist (a : Row) (rs : List Row)
    (hc : (a::rs).IsChain Compatible) :
    (sharedTail a rs).Sublist (mid a ++ after a.1 a.2.1 scratch modulus ++ scan rs) := by
  induction rs generalizing a with
  | nil => simp only [sharedTail,scan,List.append_nil];exact List.Sublist.refl _
  | cons b rs ih =>
    have hh := List.isChain_cons_cons.mp hc
    have hs := (List.Sublist.refl (mid a)).append
      ((boundary_sublist a b hh.1).append (ih b hh.2))
    simpa only [sharedTail,scan,reducedCase,mid,List.append_assoc] using hs

theorem scan_cons_t (r : Row) (rs : List Row) :
    ShorECDLP.tCount (scan (r::rs)) = ShorECDLP.tCount (before r.1 r.2.1 scratch modulus) +
      ShorECDLP.tCount (mid r) + ShorECDLP.tCount (after r.1 r.2.1 scratch modulus) + ShorECDLP.tCount (scan rs) := by
  obtain ⟨cs,pat,enc⟩ := r
  simp only [scan,reducedCase,mid,ShorECDLP.tCount_append]
  omega

theorem sharedTail_t (a : Row) (rs : List Row)
    (hc : (a::rs).IsChain Compatible) :
    ShorECDLP.tCount (sharedTail a rs) + sharingSaving a rs =
      ShorECDLP.tCount (mid a ++ after a.1 a.2.1 scratch modulus ++ scan rs) := by
  induction rs generalizing a with
  | nil => simp only [sharedTail,sharingSaving,scan,List.append_nil,Nat.add_zero]
  | cons b rs ih =>
    have hh := List.isChain_cons_cons.mp hc
    have ht := boundary_t a b hh.1
    have hi := ih b hh.2
    simp only [ShorECDLP.tCount_append] at ht hi
    simp only [sharedTail,sharingSaving,ShorECDLP.tCount_append,scan_cons_t]
    omega


def sharedSaving : List Row → Nat
  | [] => 0
  | a::rs => sharingSaving a rs

theorem shared_run (rs : List Row) (hg : ∀ r ∈ rs, Good r) (hc : rs.IsChain Compatible) :
    Quantum.run (shared rs) = Quantum.run (scan rs) := by
  apply LinearMap.ext
  intro ψ
  cases rs with
  | nil => rfl
  | cons a rs =>
    simp only [shared,Quantum.run_append]
    rw [sharedTail_run a rs hg hc]
    simp only [scan,reducedCase,mid,Quantum.run_append]

theorem shared_sublist (rs : List Row) (hc : rs.IsChain Compatible) :
    (shared rs).Sublist (scan rs) := by
  cases rs with
  | nil => exact List.Sublist.refl _
  | cons a rs =>
    have h := (List.Sublist.refl (before a.1 a.2.1 scratch modulus)).append (sharedTail_sublist a rs hc)
    simpa only [shared,scan,reducedCase,mid,List.append_assoc] using h

theorem shared_t (rs : List Row) (hc : rs.IsChain Compatible) :
    ShorECDLP.tCount (shared rs) + sharedSaving rs = ShorECDLP.tCount (scan rs) := by
  cases rs with
  | nil => rfl
  | cons a rs =>
    have h := sharedTail_t a rs hc
    simp only [ShorECDLP.tCount_append] at h
    simp only [shared,sharedSaving,ShorECDLP.tCount_append,scan_cons_t]
    omega

end ShorECDLP.Entrant.Initializer
namespace ShorECDLP.Entrant.Initializer
open Quantum Paper2607_13816
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-- A Boolean equality certificate for the X/CCX fragment used in chain boundaries. -/
def sameGate : Gate → Gate → Bool
  | .X a, .X b => a == b
  | .CCX a b c, .CCX d e f => (a == d) && (b == e) && (c == f)
  | _, _ => false

def sameCircuit : Circuit → Circuit → Bool
  | [], [] => true
  | a::as, b::bs => sameGate a b && sameCircuit as bs
  | _, _ => false

theorem sameGate_eq (a b : Gate) (h : sameGate a b = true) : a = b := by
  cases a <;> cases b <;> simp_all [sameGate,Bool.and_eq_true]

theorem sameCircuit_eq (a b : Circuit) (h : sameCircuit a b = true) : a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [sameCircuit]
  | cons a as ih =>
    cases b with
    | nil => simp [sameCircuit] at h
    | cons b bs =>
      simp only [sameCircuit,Bool.and_eq_true] at h
      rw [sameGate_eq a b h.1,ih bs h.2]

def compatibleCheck (a b : Row) : Bool :=
  sameCircuit (zeroMask b.1 b.2.1) (zeroMask a.1 a.2.1 ++ [.X (a.1.getLastD 0)]) &&
  sameCircuit (chainPrefix b.1 scratch) (chainPrefix a.1 scratch ++ extension a b) &&
  pairwiseCommutes [.X (a.1.getLastD 0)] (chainPrefix a.1 scratch) &&
  pairwiseCommutes [.X (a.1.getLastD 0)] (xorConstant scratch modulus)

theorem compatibleCheck_sound (a b : Row) (h : compatibleCheck a b = true) : Compatible a b := by
  simp only [compatibleCheck,Bool.and_eq_true] at h
  exact ⟨sameCircuit_eq _ _ h.1.1.1,sameCircuit_eq _ _ h.1.1.2,h.1.2,h.2⟩

def chainCheck : List Row → Bool
  | [] => true
  | [_] => true
  | a::b::rs => compatibleCheck a b && chainCheck (b::rs)

theorem chainCheck_sound (rs : List Row) (h : chainCheck rs = true) : rs.IsChain Compatible := by
  induction rs with
  | nil => exact List.isChain_nil
  | cons a rs ih =>
    cases rs with
    | nil => exact List.isChain_singleton _
    | cons b rs =>
      simp only [chainCheck,Bool.and_eq_true] at h
      exact List.isChain_cons_cons.mpr ⟨compatibleCheck_sound a b h.1,ih h.2⟩

private theorem rows_check : chainCheck rows = true := by decide +kernel

theorem rows_compatible_fast : rows.IsChain Compatible := chainCheck_sound rows rows_check
end ShorECDLP.Entrant.Initializer
namespace ShorECDLP.Entrant.Initializer
open Quantum Paper2607_13816
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

private theorem rows_compatible : rows.IsChain Compatible := rows_compatible_fast
private theorem rows_sharedSaving : sharedSaving rows = 453390 := by decide +kernel

theorem initializer_shared_run :
    Quantum.run (lengthInitialize (List.range' 266 256) targets 558 scratch modulus) =
      Quantum.run (shared rows) := initializer_run.trans (shared_run rows rows_good rows_compatible).symm

theorem initializer_shared_sublist : (shared rows).Sublist
    (lengthInitialize (List.range' 266 256) targets 558 scratch modulus) :=
  (shared_sublist rows rows_compatible).trans initializer_sublist

theorem initializer_shared_t : ShorECDLP.tCount (shared rows) + 910336 =
    ShorECDLP.tCount (lengthInitialize (List.range' 266 256) targets 558 scratch modulus) := by
  have h := shared_t rows rows_compatible
  rw [rows_sharedSaving] at h
  have ht := initializer_t
  omega

end ShorECDLP.Entrant.Initializer
namespace ShorECDLP.Entrant.Initializer
open Quantum Paper2607_13816
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

private theorem count_sublist {a b : Circuit} (h : a.Sublist b) : ShorECDLP.tCount a ≤ ShorECDLP.tCount b := by
  induction h with
  | slnil => exact Nat.le_refl _
  | cons a h ih => simpa only [ShorECDLP.tCount,List.map_cons,List.sum_cons] using Nat.le_trans ih (Nat.le_add_left _ _)
  | cons₂ a h ih => simpa only [ShorECDLP.tCount,List.map_cons,List.sum_cons] using Nat.add_le_add_left ih (ShorECDLP.tCost a)

def tightMid (a : Row) : Circuit := FoundationCancellation.optimize (mid a)
def midSaving (a : Row) : Nat := ShorECDLP.tCount (mid a) - ShorECDLP.tCount (tightMid a)

def tightTail (a : Row) : List Row → Circuit
  | [] => tightMid a ++ after a.1 a.2.1 scratch modulus
  | b::rs => tightMid a ++ transition a b ++ tightTail b rs

def tight : List Row → Circuit
  | [] => []
  | a::rs => before a.1 a.2.1 scratch modulus ++ tightTail a rs

theorem mid_t (a : Row) : ShorECDLP.tCount (tightMid a) + midSaving a = ShorECDLP.tCount (mid a) :=
  Nat.add_sub_of_le (count_sublist (FoundationCancellation.optimize_sublist _))

theorem tail_run (a : Row) (rs : List Row) (h : ∀ r ∈ a::rs, CircuitWellFormed (mid r)) (ψ : State) :
    Quantum.run (tightTail a rs) ψ = Quantum.run (sharedTail a rs) ψ := by
  induction rs generalizing a ψ with
  | nil =>
    simp only [tightTail,sharedTail,Quantum.run_append,tightMid,FoundationCancellation.optimize_run _ (h a (by simp))]
  | cons b rs ih =>
    simp only [tightTail,sharedTail,Quantum.run_append,tightMid,FoundationCancellation.optimize_run _ (h a (by simp))]
    exact ih b (fun r hr => h r (List.mem_cons_of_mem _ hr)) _

theorem tail_sublist (a : Row) (rs : List Row) : (tightTail a rs).Sublist (sharedTail a rs) := by
  induction rs generalizing a with
  | nil => exact (FoundationCancellation.optimize_sublist _).append (List.Sublist.refl _)
  | cons b rs ih => exact ((FoundationCancellation.optimize_sublist _).append (List.Sublist.refl _)).append (ih b)

theorem tail_t (a : Row) (rs : List Row) :
    ShorECDLP.tCount (tightTail a rs) + ((a::rs).map midSaving).sum = ShorECDLP.tCount (sharedTail a rs) := by
  induction rs generalizing a with
  | nil =>
    have h := mid_t a
    simp only [tightTail,sharedTail,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,ShorECDLP.tCount_append]
    omega
  | cons b rs ih =>
    have h := mid_t a
    have hb := ih b
    simp only [tightTail,sharedTail,List.map_cons,List.sum_cons,ShorECDLP.tCount_append] at hb ⊢
    omega

private theorem source_wellFormed : CircuitWellFormed
    (lengthInitialize (List.range' 266 256) targets 558 scratch modulus) := by
  apply lengthInitialize_wellFormed
  · unfold ComputeControlLayout McxVChainLayout
    decide +kernel
  · decide +kernel

private theorem source_scan_mid (a : Row) (rs : List Row) (ha : a ∈ rs) :
    (mid a).Sublist (scan rs) := by
  induction rs with
  | nil => simp at ha
  | cons b rs ih =>
    rcases List.mem_cons.mp ha with rfl | ht
    · have h0 : (mid a).Sublist (before a.1 a.2.1 scratch modulus ++ mid a) := List.sublist_append_right _ _
      have h1 := h0.trans (List.sublist_append_left _ (after a.1 a.2.1 scratch modulus))
      have h2 := h1.trans (List.sublist_append_left _ (scan rs))
      simpa only [scan,reducedCase,mid,List.append_assoc] using h2
    · exact (ih ht).trans (List.sublist_append_right _ _)

private theorem rows_mid_wellFormed : ∀ r ∈ rows, CircuitWellFormed (mid r) := by
  intro r hr g hg
  exact source_wellFormed g (initializer_sublist.subset ((source_scan_mid r rows hr).subset hg))

theorem tight_run : Quantum.run (tight rows) = Quantum.run (shared rows) := by
  apply LinearMap.ext
  intro ψ
  cases he : rows with
  | nil => rfl
  | cons a rs =>
    simp only [tight,shared,Quantum.run_append]
    exact tail_run a rs (by simpa only [he] using rows_mid_wellFormed) _

theorem tight_sublist : (tight rows).Sublist (shared rows) := by
  cases rows with
  | nil => exact List.Sublist.refl _
  | cons a rs => exact (List.Sublist.refl _).append (tail_sublist a rs)

private theorem mids_saving : (rows.map midSaving).sum = 14 := by decide +kernel

theorem tight_extra : ShorECDLP.tCount (tight rows) + 14 = ShorECDLP.tCount (shared rows) := by
  rw [← mids_saving]
  cases rows with
  | nil => rfl
  | cons a rs =>
    have h := tail_t a rs
    simp only [tight,shared,ShorECDLP.tCount_append]
    omega

theorem initializer_tight_run :
    Quantum.run (lengthInitialize (List.range' 266 256) targets 558 scratch modulus) =
      Quantum.run (tight rows) := initializer_shared_run.trans tight_run.symm

theorem initializer_tight_sublist : (tight rows).Sublist
    (lengthInitialize (List.range' 266 256) targets 558 scratch modulus) :=
  tight_sublist.trans initializer_shared_sublist

theorem initializer_tight_t : ShorECDLP.tCount (tight rows) + 910350 =
    ShorECDLP.tCount (lengthInitialize (List.range' 266 256) targets 558 scratch modulus) := by
  have h := tight_extra
  have ht := initializer_shared_t
  omega
end ShorECDLP.Entrant.Initializer
namespace ShorECDLP.Entrant.Initializer
open Paper2607_13816 ShorECDLP.Classical
/-- On the classical gate fragment, the protected cost is seven per Toffoli. -/
theorem classical_toffoli_cost (c : Circuit) (hf : HPFree c) :
    ShorECDLP.tCount c = 7 * eeaToffoliCount c := by
  induction c with
  | nil => rfl
  | cons g c ih =>
    have hg : IsClassicalGate g := hf g (by simp)
    have ht : HPFree c := fun k hk => hf k (by simp [hk])
    cases g <;> simp_all [ShorECDLP.tCount,ShorECDLP.tCost,eeaToffoliCount]
    omega


/-- Exact physical Toffoli saving for the complete shared initializer. -/
theorem initializer_tight_ccx : eeaToffoliCount (tight rows) + 130050 =
    eeaToffoliCount (lengthInitialize (List.range' 266 256) targets 558 scratch modulus) := by
  have hf := lengthInitialize_HPFree (List.range' 266 256) targets 558 scratch modulus
  have hs : HPFree (tight rows) := fun g hg => hf g (initializer_tight_sublist.subset hg)
  have h := initializer_tight_t
  rw [classical_toffoli_cost _ hs,classical_toffoli_cost _ hf] at h
  omega
end ShorECDLP.Entrant.Initializer


namespace ShorECDLP.Entrant.AcrossLeft
open Quantum
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

def source (a b t u : Wire) (h : Gate) : Circuit := [.CCX a b t,h,.CX t u,.CCX a b t]
def reduced (a b t u : Wire) (h : Gate) : Circuit := [h,.CX t u,.CCX a b u]

theorem run_identity (a b t u : Wire) (h : Gate)
    (hat : a≠t) (hbt : b≠t) (hau : a≠u) (hbu : b≠u) (htu : t≠u)
    (hc : FoundationCancellation.commutes (.CCX a b t) h = true) :
    Quantum.run (source a b t u h)=Quantum.run (reduced a b t u h) := by
  have he := Transport.run_identity a b t u hat hbt hau hbu htu
  have hc' (ϕ : State) : applyGate (.CCX a b t) (applyGate h ϕ) = applyGate h (applyGate (.CCX a b t) ϕ) := by
    simpa only [Quantum.run_cons,Quantum.run_nil] using
      Initializer.gate_circuit_commute (.CCX a b t) (h :: List.nil) (by
        intro k hk
        have heq : k=h := by simpa only [List.mem_singleton] using hk
        rw [heq]
        exact hc) ϕ
  apply LinearMap.ext
  intro ψ
  simp only [source,reduced,Quantum.run_cons,Quantum.run_nil]
  have hh := congrArg (fun m : State →ₗ[ℂ]State => m (applyGate h ψ)) he
  simp only [Transport.source,Transport.reduced,Quantum.run_cons,Quantum.run_nil] at hh
  rw [hc'] at hh
  exact hh

def optimize : Circuit → Circuit
  | .CCX a b t :: h :: .CX v u :: .CCX c d z :: rest =>
    if a=c ∧ b=d ∧ t=v ∧ t=z ∧ a≠u ∧ b≠u ∧ t≠u ∧ a≠t ∧ b≠t ∧
        FoundationCancellation.commutes (.CCX a b t) h = true then
      h :: .CX t u :: .CCX a b u :: optimize rest
    else .CCX a b t :: optimize (h :: .CX v u :: .CCX c d z :: rest)
  | g::rest => g::optimize rest
  | [] => []

inductive Reduction : Circuit → Circuit → Prop where
  | nil : Reduction List.nil List.nil
  | keep (g : Gate) {xs ys : Circuit} : Reduction xs ys → Reduction (g::xs) (g::ys)
  | fuse (a b t u : Wire) (h : Gate)
      (hat : a≠t) (hbt : b≠t) (hau : a≠u) (hbu : b≠u) (htu : t≠u)
      (hc : FoundationCancellation.commutes (.CCX a b t) h = true)
      {xs ys : Circuit} : Reduction xs ys →
      Reduction (.CCX a b t :: h :: .CX t u :: .CCX a b t :: xs) (h :: .CX t u :: .CCX a b u :: ys)

theorem optimize_rel (xs : Circuit) : Reduction xs (optimize xs) := by
  induction xs using optimize.induct with
  | case1 a b t h v u c d z rest hc ih =>
    rw [optimize,if_pos hc]
    rcases hc with ⟨rfl,rfl,rfl,rfl,hau,hbu,htu,hat,hbt,hcomm⟩
    exact Reduction.fuse _ _ _ _ _ hat hbt hau hbu htu hcomm ih
  | case2 a b t h v u c d z rest hc ih =>
    rw [optimize,if_neg hc]
    exact Reduction.keep _ ih
  | case3 g rest hc ih =>
    rw [optimize.eq_2 g rest hc]
    exact Reduction.keep _ ih
  | case4 => exact Reduction.nil

theorem Reduction.run {xs ys : Circuit} (h : Reduction xs ys) : Quantum.run xs=Quantum.run ys := by
  induction h with
  | nil => rfl
  | keep g h ih =>
    apply LinearMap.ext
    intro ψ
    simp only [Quantum.run_cons,ih]
  | fuse a b t u g hat hbt hau hbu htu hc h ih =>
    have he := run_identity a b t u g hat hbt hau hbu htu hc
    apply LinearMap.ext
    intro ψ
    have hh := congrArg (fun m : State→ₗ[ℂ]State => m ψ) he
    simp only [source,reduced,Quantum.run_cons,Quantum.run_nil] at hh
    simpa only [Quantum.run_cons,ih] using congrArg (Quantum.run _) hh

end ShorECDLP.Entrant.AcrossLeft

namespace ShorECDLP.Entrant.AcrossRight
open Quantum
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

def source (a b t u : Wire) (h : Gate) : Circuit := [.CCX a b t,.CX t u,h,.CCX a b t]
def reduced (a b t u : Wire) (h : Gate) : Circuit := [.CX t u,.CCX a b u,h]

theorem run_identity (a b t u : Wire) (h : Gate)
    (hat : a≠t) (hbt : b≠t) (hau : a≠u) (hbu : b≠u) (htu : t≠u)
    (hc : FoundationCancellation.commutes (.CCX a b t) h = true) :
    Quantum.run (source a b t u h)=Quantum.run (reduced a b t u h) := by
  have he := Transport.run_identity a b t u hat hbt hau hbu htu
  have hc' (ϕ : State) : applyGate (.CCX a b t) (applyGate h ϕ) = applyGate h (applyGate (.CCX a b t) ϕ) := by
    simpa only [Quantum.run_cons,Quantum.run_nil] using
      Initializer.gate_circuit_commute (.CCX a b t) (h :: List.nil) (by
        intro k hk
        have heq : k=h := by simpa only [List.mem_singleton] using hk
        rw [heq]
        exact hc) ϕ
  apply LinearMap.ext
  intro ψ
  simp only [source,reduced,Quantum.run_cons,Quantum.run_nil]
  have hh := congrArg (fun v : State => applyGate h v)
      (congrArg (fun m : State →ₗ[ℂ]State => m ψ) he)
  simp only [Transport.source,Transport.reduced,Quantum.run_cons,Quantum.run_nil] at hh
  rw [←hc'] at hh
  exact hh

def optimize : Circuit → Circuit
  | .CCX a b t :: .CX v u :: h :: .CCX c d z :: rest =>
    if a=c ∧ b=d ∧ t=v ∧ t=z ∧ a≠u ∧ b≠u ∧ t≠u ∧ a≠t ∧ b≠t ∧
        FoundationCancellation.commutes (.CCX a b t) h = true then
      .CX t u :: .CCX a b u :: h :: optimize rest
    else .CCX a b t :: optimize (.CX v u :: h :: .CCX c d z :: rest)
  | g::rest => g::optimize rest
  | [] => []

inductive Reduction : Circuit → Circuit → Prop where
  | nil : Reduction List.nil List.nil
  | keep (g : Gate) {xs ys : Circuit} : Reduction xs ys → Reduction (g::xs) (g::ys)
  | fuse (a b t u : Wire) (h : Gate)
      (hat : a≠t) (hbt : b≠t) (hau : a≠u) (hbu : b≠u) (htu : t≠u)
      (hc : FoundationCancellation.commutes (.CCX a b t) h = true)
      {xs ys : Circuit} : Reduction xs ys →
      Reduction (.CCX a b t :: .CX t u :: h :: .CCX a b t :: xs) (.CX t u :: .CCX a b u :: h :: ys)

theorem optimize_rel (xs : Circuit) : Reduction xs (optimize xs) := by
  induction xs using optimize.induct with
  | case1 a b t v u h c d z rest hc ih =>
    rw [optimize,if_pos hc]
    rcases hc with ⟨rfl,rfl,rfl,rfl,hau,hbu,htu,hat,hbt,hcomm⟩
    exact Reduction.fuse _ _ _ _ _ hat hbt hau hbu htu hcomm ih
  | case2 a b t v u h c d z rest hc ih =>
    rw [optimize,if_neg hc]
    exact Reduction.keep _ ih
  | case3 g rest hc ih =>
    rw [optimize.eq_2 g rest hc]
    exact Reduction.keep _ ih
  | case4 => exact Reduction.nil

theorem Reduction.run {xs ys : Circuit} (h : Reduction xs ys) : Quantum.run xs=Quantum.run ys := by
  induction h with
  | nil => rfl
  | keep g h ih =>
    apply LinearMap.ext
    intro ψ
    simp only [Quantum.run_cons,ih]
  | fuse a b t u g hat hbt hau hbu htu hc h ih =>
    have he := run_identity a b t u g hat hbt hau hbu htu hc
    apply LinearMap.ext
    intro ψ
    have hh := congrArg (fun m : State→ₗ[ℂ]State => m ψ) he
    simp only [source,reduced,Quantum.run_cons,Quantum.run_nil] at hh
    simpa only [Quantum.run_cons,ih] using congrArg (Quantum.run _) hh

end ShorECDLP.Entrant.AcrossRight

set_option linter.unnecessarySeqFocus false
namespace ShorECDLP.Entrant.AcrossLeft
open Quantum

theorem Reduction.tle {xs ys : Circuit} (h : Reduction xs ys) :
    ShorECDLP.tCount ys ≤ ShorECDLP.tCount xs := by
  induction h <;> simp_all [ShorECDLP.tCount_cons,tCost] <;> omega
end ShorECDLP.Entrant.AcrossLeft
namespace ShorECDLP.Entrant.AcrossRight
open Quantum

theorem Reduction.tle {xs ys : Circuit} (h : Reduction xs ys) :
    ShorECDLP.tCount ys ≤ ShorECDLP.tCount xs := by
  induction h <;> simp_all [ShorECDLP.tCount_cons,tCost] <;> omega
end ShorECDLP.Entrant.AcrossRight

namespace ShorECDLP.Entrant.TransportOptimization
open Quantum Challenge Paper2607_13816.ChallengeMigration
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

theorem acrossLeft_drops {xs ys : Circuit} (h : AcrossLeft.Reduction xs ys) (n start : Nat) :
    Drops (literalProgram xs : Straight n start start) (literalProgram ys)
      (ShorECDLP.tCount xs-ShorECDLP.tCount ys) := by
  induction h with
  | nil => exact Drops.refl _
  | @keep g xs ys h ih =>
    have hd : ShorECDLP.tCount (g::xs)-ShorECDLP.tCount (g::ys)=
        ShorECDLP.tCount xs-ShorECDLP.tCount ys := by simp only [ShorECDLP.tCount_cons]; omega
    rw [hd]
    simpa only [literalProgram,gateProgram,List.map_cons] using Drops.gate (.literal g) ih
  | @fuse a b t u g hat hbt hau hbu htu hc xs ys h ih =>
    have hs := Drops.swap (.CCX a b t) g
      (Drops.refl (.gate (.literal (.CX t u)) (.gate (.literal (.CCX a b t))
        (literalProgram xs : Straight n start start))))
    have ht := Drops.gate (.literal g) (Drops.transport a b t u ⟨hat,hbt,hau,hbu,htu⟩ ih)
    have hj := Drops.trans hs ht
    have hle := h.tle
    have hd : ShorECDLP.tCount (.CCX a b t :: g :: .CX t u :: .CCX a b t :: xs)-
        ShorECDLP.tCount (g :: .CX t u :: .CCX a b u :: ys)=
        7+(ShorECDLP.tCount xs-ShorECDLP.tCount ys) := by
      simp only [ShorECDLP.tCount_cons,tCost]
      omega
    rw [hd]
    simpa only [literalProgram,gateProgram,List.map_cons,Nat.zero_add] using hj

theorem acrossRight_drops {xs ys : Circuit} (h : AcrossRight.Reduction xs ys) (n start : Nat) :
    Drops (literalProgram xs : Straight n start start) (literalProgram ys)
      (ShorECDLP.tCount xs-ShorECDLP.tCount ys) := by
  induction h with
  | nil => exact Drops.refl _
  | @keep g xs ys h ih =>
    have hd : ShorECDLP.tCount (g::xs)-ShorECDLP.tCount (g::ys)=
        ShorECDLP.tCount xs-ShorECDLP.tCount ys := by simp only [ShorECDLP.tCount_cons]; omega
    rw [hd]
    simpa only [literalProgram,gateProgram,List.map_cons] using Drops.gate (.literal g) ih
  | @fuse a b t u g hat hbt hau hbu htu hc xs ys h ih =>
    have hs := Drops.gate (.literal (.CCX a b t)) (Drops.gate (.literal (.CX t u))
      (Drops.swap g (.CCX a b t) (Drops.refl (literalProgram xs : Straight n start start))))
    have ht := Drops.transport a b t u ⟨hat,hbt,hau,hbu,htu⟩ (Drops.gate (.literal g) ih)
    have hj := Drops.trans hs ht
    have hle := h.tle
    have hd : ShorECDLP.tCount (.CCX a b t :: .CX t u :: g :: .CCX a b t :: xs)-
        ShorECDLP.tCount (.CX t u :: .CCX a b u :: g :: ys)=
        7+(ShorECDLP.tCount xs-ShorECDLP.tCount ys) := by
      simp only [ShorECDLP.tCount_cons,tCost]
      omega
    rw [hd]
    simpa only [literalProgram,gateProgram,List.map_cons,Nat.zero_add] using hj
end ShorECDLP.Entrant.TransportOptimization
