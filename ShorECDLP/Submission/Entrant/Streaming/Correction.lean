import ShorECDLP.Submission.«2607_13816».Challenge.BatchState
import ShorECDLP.Submission.«2607_13816».Challenge.EndpointEncoding
import ShorECDLP.Submission.«2607_13816».Challenge.AccumulatorEncoding
import ShorECDLP.Submission.«2607_13816».Challenge.BatchTemplate
import ShorECDLP.Submission.«2607_13816».Challenge.GidneyAdd
import ShorECDLP.Submission.«2607_13816».Challenge.WindowBody

import ShorECDLP.Submission.«2607_13816».Challenge.LookupPhysical
import ShorECDLP.Submission.«2607_13816».Challenge.Interval

/-! Measured equality schedules: entrant improvement using protected measurement-uncomputation semantics. -/
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
set_option linter.unusedSimpArgs false

/-- A flat compiler schedule for the library's measured clean v-chain. -/
def measuredTailOps {n : Nat} (a : Wire) :
    List Wire → Wire → List Wire → List (LookupOp n)
  | [], _, _ => []
  | [c], t, _ => [ordinaryOp [.CCX c a t]]
  | c :: d :: cs, t, w :: ws =>
      [ordinaryOp [.CCX c a w]] ++ measuredTailOps w (d :: cs) t ws ++ [.erase c a w]
  | _ :: _ :: _, _, [] => []

def measuredChainOps {n : Nat} : List Wire → Wire → List Wire → List (LookupOp n)
  | [], t, _ => [ordinaryOp [.X t]]
  | [c], t, _ => [ordinaryOp [.CX c t]]
  | a :: b :: cs, t, ws => measuredTailOps b (a :: cs) t ws

def measuredEqualityOps {n : Nat} (r : List Wire) (v : Nat) (t : Wire) (ws : List Wire) :
    List (LookupOp n) :=
  [ordinaryOp (zeroMask r v)] ++ measuredChainOps r t ws ++ [ordinaryOp (zeroMask r v)]

theorem measuredTailOps_source {n : Nat} (read : ConstantBit n → Bool)
    (a : Wire) (cs : List Wire) (t : Wire) (ws : List Wire) :
    lookupCircuit read (measuredTailOps a cs t ws) = mcxVChainTailAdaptive a cs t ws := by
  induction cs generalizing a ws with
  | nil => rfl
  | cons c cs ih =>
    cases cs with
    | nil => simp [measuredTailOps,lookupCircuit,ordinaryOp,literal_gates,TemplateGate.instantiate,mcxVChainTailAdaptive]
    | cons d ds =>
      cases ws with
      | nil => rfl
      | cons w ws =>
        simp [measuredTailOps,lookupCircuit_append,lookupCircuit,ordinaryOp,literal_gates,
          TemplateGate.instantiate,ih,mcxVChainTailAdaptive,AdaptiveCircuit.seq,adaptive_seq_done]

theorem measuredChainOps_source {n : Nat} (read : ConstantBit n → Bool)
    (cs : List Wire) (t : Wire) (ws : List Wire) :
    lookupCircuit read (measuredChainOps cs t ws) = mcxVChainAdaptive cs t ws := by
  cases cs with
  | nil => simp [measuredChainOps,lookupCircuit,ordinaryOp,literal_gates,TemplateGate.instantiate,mcxVChainAdaptive]
  | cons a cs =>
    cases cs with
    | nil => simp [measuredChainOps,lookupCircuit,ordinaryOp,literal_gates,TemplateGate.instantiate,mcxVChainAdaptive]
    | cons b cs => exact measuredTailOps_source read b (a :: cs) t ws

theorem measuredEqualityOps_source {n : Nat} (read : ConstantBit n → Bool)
    (r : List Wire) (v : Nat) (t : Wire) (ws : List Wire) :
    lookupCircuit read (measuredEqualityOps r v t ws) = computeEqConstAdaptive r v t ws := by
  simp [measuredEqualityOps,lookupCircuit_append,lookupCircuit,ordinaryOp,literal_gates,
    measuredChainOps_source,computeEqConstAdaptive,AdaptiveCircuit.seq]

theorem measuredTailOps_measurements {n : Nat} (a : Wire) (cs : List Wire) (t : Wire)
    (ws : List Wire) (h : cs.length - 1 ≤ ws.length) :
    lookupMeasurements (@measuredTailOps n a cs t ws) = cs.length - 1 := by
  induction cs generalizing a ws with
  | nil => rfl
  | cons c cs ih =>
    cases cs with
    | nil => rfl
    | cons d ds =>
      cases ws with
      | nil => simp at h
      | cons w ws =>
        simp only [measuredTailOps,lookupMeasurements_append,lookupMeasurements,ordinaryOp]
        rw [ih w ws (by simpa using h)]
        simp

theorem measuredEqualityOps_measurements {n : Nat} (r : List Wire) (v : Nat)
    (t : Wire) (ws : List Wire) (h : r.length - 2 ≤ ws.length) :
    lookupMeasurements (@measuredEqualityOps n r v t ws) = r.length - 2 := by
  simp only [measuredEqualityOps,lookupMeasurements_append,lookupMeasurements,ordinaryOp,
    Nat.zero_add,Nat.add_zero]
  cases r with
  | nil => rfl
  | cons a r =>
    cases r with
    | nil => rfl
    | cons b r => exact measuredTailOps_measurements b (a :: r) t ws h

theorem measuredTailOps_physical {n : Nat} (a : Wire) (cs : List Wire) (t : Wire)
    (ws : List Wire) (h : CircuitWellFormed (mcxVChainTail a cs t ws)) :
    ∀ op ∈ @measuredTailOps n a cs t ws, op.Physical := by
  induction cs generalizing a ws with
  | nil => simp [measuredTailOps]
  | cons c cs ih =>
    cases cs with
    | nil =>
      simp only [measuredTailOps,List.forall_mem_singleton]
      exact ordinaryOp_physical _ h
    | cons d ds =>
      cases ws with
      | nil => simp [measuredTailOps]
      | cons w ws =>
        have hf : CircuitWellFormed [.CCX c a w] :=
          ((circuitWellFormed_append _ _).mp ((circuitWellFormed_append _ _).mp h).1).1
        have hm := ((circuitWellFormed_append _ _).mp
          ((circuitWellFormed_append _ _).mp h).1).2
        have hca : c ≠ a := (hf (.CCX c a w) (by simp)).1
        simp only [measuredTailOps,List.forall_mem_append,List.forall_mem_singleton]
        exact ⟨⟨ordinaryOp_physical _ hf,ih w ws hm⟩,hca⟩

theorem measuredChainOps_physical {n : Nat} (r : List Wire) (t : Wire) (ws : List Wire)
    (h : CircuitWellFormed (mcxVChain r t ws)) :
    ∀ op ∈ @measuredChainOps n r t ws, op.Physical := by
  cases r with
  | nil =>
    simp only [measuredChainOps,List.forall_mem_singleton]
    exact ordinaryOp_physical _ h
  | cons a r =>
    cases r with
    | nil =>
      simp only [measuredChainOps,List.forall_mem_singleton]
      exact ordinaryOp_physical _ h
    | cons b r => exact measuredTailOps_physical b (a :: r) t ws h

theorem measuredEqualityOps_physical {n : Nat} (r : List Wire) (v : Nat) (t : Wire)
    (ws : List Wire) (h : EqConstLayout r t ws) :
    ∀ op ∈ @measuredEqualityOps n r v t ws, op.Physical := by
  simp only [measuredEqualityOps,List.forall_mem_append,List.forall_mem_singleton]
  exact ⟨⟨ordinaryOp_physical _ (zeroMask_wellFormed r v),
    measuredChainOps_physical r t ws (mcxVChain_wellFormed r t ws h.1 h.2)⟩,
    ordinaryOp_physical _ (zeroMask_wellFormed r v)⟩

theorem equality_preserves_clean (r : List Wire) (v : Nat) (t : Wire) (ws : List Wire)
    (h : EqConstLayout r t ws) (s : BasisState) (hs : Clean ws s) :
    Clean ws (Classical.run (computeEqConst r v t ws) s) := by
  have ht : t ∉ ws := (List.nodup_cons.mp (List.nodup_append.mp h.2).2.1).1
  rw [run_computeEqConst r v t ws s h hs]
  intro w hw
  rw [upd_other _ _ _ (by intro he; exact ht (he ▸ hw))]
  exact hs w hw

/-- Structural reference used only to bound gate slots and touched wires. -/
def equalityTemplateGate {n : Nat} : TemplateGate n → Gate
  | .literal g => g
  | .whenBit _ _ g => g

def equalityOpSkeleton {n : Nat} : LookupOp n → Circuit
  | .gates gs => gs.map equalityTemplateGate
  | .erase a b t => [.CCX a b t]

def equalitySkeleton {n : Nat} (ops : List (LookupOp n)) : Circuit :=
  ops.flatMap equalityOpSkeleton

theorem equalitySkeleton_append {n : Nat} (a b : List (LookupOp n)) :
    equalitySkeleton (a ++ b) = equalitySkeleton a ++ equalitySkeleton b :=
  List.flatMap_append

theorem equalitySkeleton_ordinary {n : Nat} (gs : Circuit) :
    equalitySkeleton [@ordinaryOp n gs] = gs := by
  simp [equalitySkeleton,equalityOpSkeleton,ordinaryOp,List.map_map,equalityTemplateGate,
    Function.comp_def]

theorem measuredTailOps_skeleton {n : Nat} (a : Wire) (cs : List Wire) (t : Wire)
    (ws : List Wire) :
    equalitySkeleton (@measuredTailOps n a cs t ws) = mcxVChainTail a cs t ws := by
  induction cs generalizing a ws with
  | nil => rfl
  | cons c cs ih =>
    cases cs with
    | nil => exact equalitySkeleton_ordinary _
    | cons d ds =>
      cases ws with
      | nil => rfl
      | cons w ws =>
        rw [measuredTailOps,equalitySkeleton_append,equalitySkeleton_append,
          equalitySkeleton_ordinary,ih]
        rfl

theorem measuredEqualityOps_skeleton {n : Nat} (r : List Wire) (v : Nat) (t : Wire)
    (ws : List Wire) :
    equalitySkeleton (@measuredEqualityOps n r v t ws) = computeEqConst r v t ws := by
  have hc : equalitySkeleton (@measuredChainOps n r t ws) = mcxVChain r t ws := by
    cases r with
    | nil => exact equalitySkeleton_ordinary _
    | cons a r =>
      cases r with
      | nil => exact equalitySkeleton_ordinary _
      | cons b r => exact measuredTailOps_skeleton b (a :: r) t ws
  simp only [measuredEqualityOps,equalitySkeleton_append,equalitySkeleton_ordinary,hc,computeEqConst]

end ShorECDLP.Paper2607_13816.ChallengeMigration

/-! EDITABLE. Streaming entrant, module `Correction`: the in-place XOR exceptional-point correction (word model, circuit, semantics, window).

This module concatenates the former per-file modules `IpxModel`, `IpxCircuit`, `IpxSemantics`,
`IpxWindow` (in this order). Each former file is one `namespace` block below, marked `-- ====
part: <Name> ====`, with its provenance note. Only the import lines changed.

Why few modules: the kernel replay loads the complete import closure (about 4.3 GB) once per
Entrant module, in parallel across its worker threads, so its peak memory grows with the number
of Entrant modules. -/

-- ==== part: IpxModel ====

/-! # In-place XOR correction: the word-level model

The streaming window addition writes `F(enc P)` into the 513-bit accumulator, where `F` is the
coordinate permutation of the affine formula for the window point `C`. It equals
`enc (P + C)` except on the four exceptional inputs `P_k ∈ [0, C, -C, -(C+C)]`.

This module replaces the five-word transposition network of the upstream certificate by an
in-place correction that keeps no endpoint word resident. With `a_k = W(F(enc P_k))` and
`b_k = W(enc (P_k + C))` (the eight endpoint words of the selected table row), it

1. computes four one-hot flags `f_k = [acc = a_k]` by XOR-ing the endpoint words into the
   accumulator and zero-testing it,
2. applies `acc ^= f_k · (a_k ^ b_k)` under each flag, and
3. clears every flag with `f_k ^= [acc = b_k]`.

Here the schedule is modelled on the accumulator word and the four flags. The circuit-level
semantics is in `IpxSemantics`. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Classical ShorECDLP.Secp256k1 ShorECDLP.Challenge

/-- One step of the correction schedule: a table query XOR-ing endpoint word `u` (and `v`, if
present) into the accumulator, enabled by the window control or by flag `k`, or the zero test
of the accumulator into flag `k`. -/
inductive IpxOp where
  | query (control : Option (Fin 4)) (u : Fin 8) (v : Option (Fin 8))
  | test (k : Fin 4)

/-- Flags `f_k = [acc = a_k]`; afterwards the accumulator holds `acc ^ a_3`. -/
def ipxPhase1 : List IpxOp :=
  [.query none 0 none, .test 0, .query none 0 (some 1), .test 1,
   .query none 1 (some 2), .test 2, .query none 2 (some 3), .test 3]

/-- Flag-controlled updates `acc ^= f_k · (a_k ^ b_k)`. -/
def ipxPhase2 : List IpxOp :=
  [.query (some 0) 0 (some 4), .query (some 1) 1 (some 5),
   .query (some 2) 2 (some 6), .query (some 3) 3 (some 7)]

/-- Flag clearing `f_k ^= [acc = b_k]`; the final query restores the accumulator. -/
def ipxPhase3 : List IpxOp :=
  [.query none 3 (some 4), .test 0, .query none 4 (some 5), .test 1,
   .query none 5 (some 6), .test 2, .query none 6 (some 7), .test 3, .query none 7 none]

/-- Thirteen table queries and eight zero tests per correction block. -/
def ipxSchedule : List IpxOp := ipxPhase1 ++ ipxPhase2 ++ ipxPhase3

/-- Source word `a_k` and target word `b_k` among the eight endpoint words. -/
def ipxA (k : Fin 4) : Fin 8 := ⟨k.val, by omega⟩
def ipxB (k : Fin 4) : Fin 8 := ⟨k.val+4, by omega⟩

noncomputable section

def ipxOptWord (e : Fin 8 → BatchWord) : Option (Fin 8) → BatchWord
  | none => fun _ => false
  | some j => e j

def ipxActive (F : Fin 4 → Bool) : Option (Fin 4) → Bool
  | none => true
  | some k => F k

def ipxModelStep (e : Fin 8 → BatchWord) (st : BatchWord × (Fin 4 → Bool)) :
    IpxOp → BatchWord × (Fin 4 → Bool)
  | .query c u v =>
    (if ipxActive st.2 c then wordXor st.1 (wordXor (e u) (ipxOptWord e v)) else st.1, st.2)
  | .test k => (st.1, Function.update st.2 k (xor (st.2 k) (decide (st.1 = fun _ => false))))

def ipxModel (e : Fin 8 → BatchWord) (st : BatchWord × (Fin 4 → Bool)) :
    BatchWord × (Fin 4 → Bool) :=
  ipxSchedule.foldl (ipxModelStep e) st

@[simp] theorem wordXor_shift (a b c : BatchWord) :
    wordXor (wordXor a b) (wordXor b c) = wordXor a c := by
  funext i; simp only [wordXor]; cases a i <;> cases b i <;> cases c i <;> rfl

@[simp] theorem wordXor_cancel_right (a b : BatchWord) : wordXor (wordXor a b) b = a := by
  funext i; simp only [wordXor]; cases a i <;> cases b i <;> rfl

theorem wordXor_swap_out (a b c : BatchWord) :
    wordXor (wordXor a b) (wordXor a c) = wordXor c b := by
  funext i; simp only [wordXor]; cases a i <;> cases b i <;> cases c i <;> rfl

@[simp] theorem wordXor_eq_zero_iff (a b : BatchWord) :
    wordXor a b = (fun _ => false) ↔ a = b := by
  constructor
  · intro h
    funext i
    have hi := congrFun h i
    simp only [wordXor] at hi
    cases ha : a i <;> cases hb : b i <;> simp_all
  · rintro rfl
    exact wordXor_self a

theorem ipx_phase1 (e : Fin 8 → BatchWord) (A : BatchWord) (F : Fin 4 → Bool) :
    ipxPhase1.foldl (ipxModelStep e) (A,F) =
      (wordXor A (e 3), fun k => xor (F k) (decide (A = e (ipxA k)))) := by
  simp only [ipxPhase1,List.foldl_cons,List.foldl_nil,ipxModelStep,ipxActive,ipxOptWord,ite_true,
    wordXor_zero,wordXor_shift,wordXor_eq_zero_iff]
  refine Prod.ext rfl ?_
  funext k
  fin_cases k <;> simp [ipxA]

theorem ipx_phase2_zero (e : Fin 8 → BatchWord) (A : BatchWord) :
    ipxPhase2.foldl (ipxModelStep e) (A,fun _ => false) = (A,fun _ => false) := by
  simp [ipxPhase2,ipxModelStep,ipxActive]

theorem ipx_phase2_one (e : Fin 8 → BatchWord) (A : BatchWord) (j : Fin 4) :
    ipxPhase2.foldl (ipxModelStep e) (A,fun k => decide (j = k)) =
      (wordXor A (wordXor (e (ipxA j)) (e (ipxB j))),fun k => decide (j = k)) := by
  fin_cases j <;> simp [ipxPhase2,ipxModelStep,ipxActive,ipxOptWord,ipxA,ipxB]

theorem ipx_phase3 (e : Fin 8 → BatchWord) (A : BatchWord) (F : Fin 4 → Bool) :
    ipxPhase3.foldl (ipxModelStep e) (wordXor A (e 3),F) =
      (A, fun k => xor (F k) (decide (A = e (ipxB k)))) := by
  simp only [ipxPhase3,List.foldl_cons,List.foldl_nil,ipxModelStep,ipxActive,ipxOptWord,ite_true,
    wordXor_zero,wordXor_shift,wordXor_eq_zero_iff,wordXor_cancel_right]
  refine Prod.ext rfl ?_
  funext k
  fin_cases k <;> simp [ipxB]

theorem ipxModel_split (e : Fin 8 → BatchWord) (st : BatchWord × (Fin 4 → Bool)) :
    ipxModel e st = ipxPhase3.foldl (ipxModelStep e)
      (ipxPhase2.foldl (ipxModelStep e) (ipxPhase1.foldl (ipxModelStep e) st)) := by
  simp only [ipxModel,ipxSchedule,List.foldl_append]

/-- An accumulator value that is no endpoint word passes through unchanged. -/
theorem ipxModel_generic (e : Fin 8 → BatchWord) (A : BatchWord)
    (ha : ∀ k, A ≠ e (ipxA k)) (hb : ∀ k, A ≠ e (ipxB k)) :
    ipxModel e (A,fun _ => false) = (A,fun _ => false) := by
  have h1 : (fun k => xor ((fun _ => false) k) (decide (A = e (ipxA k)))) = fun _ => false := by
    funext k; simp [ha k]
  have h3 : (fun k => xor ((fun _ => false) k) (decide (A = e (ipxB k)))) = fun _ => false := by
    funext k; simp [hb k]
  rw [ipxModel_split,ipx_phase1,h1,ipx_phase2_zero,ipx_phase3,h3]

/-- One-hot correction: with pairwise distinct source words and pairwise distinct target words,
the source word `a_j` becomes `b_j` and every flag is cleared. -/
theorem ipxModel_exceptional (e : Fin 8 → BatchWord)
    (ha : ∀ j k, e (ipxA j) = e (ipxA k) → j = k) (hb : ∀ j k, e (ipxB j) = e (ipxB k) → j = k)
    (j : Fin 4) :
    ipxModel e (e (ipxA j),fun _ => false) = (e (ipxB j),fun _ => false) := by
  have h1 : (fun k => xor ((fun _ => false) k) (decide (e (ipxA j) = e (ipxA k)))) =
      fun k => decide (j = k) := by
    funext k
    by_cases hjk : j = k
    · subst hjk; simp
    · have hne : e (ipxA j) ≠ e (ipxA k) := fun h => hjk (ha j k h)
      simp [hjk,hne]
  have h3 : (fun k => xor (decide (j = k)) (decide (e (ipxB j) = e (ipxB k)))) = fun _ => false := by
    funext k
    by_cases hjk : j = k
    · subst hjk; simp
    · have hne : e (ipxB j) ≠ e (ipxB k) := fun h => hjk (hb j k h)
      simp [hjk,hne]
  rw [ipxModel_split,ipx_phase1,h1,ipx_phase2_one,wordXor_swap_out,ipx_phase3,h3]

local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨p_prime⟩

/-- The four exceptional inputs, in the order of the protected endpoint pairs. -/
def ipxInput (C : Point) : Fin 4 → Point := ![0, C, -C, -(C+C)]

theorem ipxInput_injective (C : Point) (h1 : C ≠ 0) (h2 : C + C ≠ 0) (h3 : C + C + C ≠ 0) :
    Function.Injective (ipxInput C) := by
  have e2 : ∀ D : Point, D = -D → D + D = 0 := fun D h => by
    calc D + D = D + -D := by rw [← h]
      _ = 0 := add_neg_cancel D
  intro j k h
  fin_cases j <;> fin_cases k <;> try rfl
  all_goals exfalso
  · have h' : (0 : Point) = C := h
    exact h1 h'.symm
  · have h' : (0 : Point) = -C := h
    exact h1 (neg_eq_zero.mp h'.symm)
  · have h' : (0 : Point) = -(C+C) := h
    exact h2 (neg_eq_zero.mp h'.symm)
  · have h' : C = 0 := h
    exact h1 h'
  · have h' : C = -C := h
    exact h2 (e2 C h')
  · have h' : C = -(C+C) := h
    apply h3
    calc C + C + C = -(C+C) + (C+C) := by rw [← h']; abel
      _ = 0 := neg_add_cancel _
  · have h' : -C = 0 := h
    exact h1 (neg_eq_zero.mp h')
  · have h' : -C = C := h
    exact h2 (e2 C (neg_eq_iff_eq_neg.mp h'))
  · have h' : -C = -(C+C) := h
    apply h1
    have h'' : C = C + C := neg_injective h'
    calc C = C + C - C := by abel
      _ = C - C := by rw [← h'']
      _ = 0 := sub_self C
  · have h' : -(C+C) = 0 := h
    exact h2 (neg_eq_zero.mp h')
  · have h' : -(C+C) = C := h
    apply h3
    have h'' : C + C = -C := neg_eq_iff_eq_neg.mp h'
    calc C + C + C = -C + C := by rw [h'']
      _ = 0 := neg_add_cancel C
  · have h' : -(C+C) = -C := h
    apply h1
    have h'' : C + C = C := neg_injective h'
    calc C = C + C - C := by abel
      _ = C - C := by rw [h'']
      _ = 0 := sub_self C

/-- Every non-zero multiple of a point of prime order `order` keeps the exceptional inputs apart. -/
theorem ipxInput_injective_of_order (C : Point) (hC : C ≠ 0) (hord : order • C = 0) :
    Function.Injective (ipxInput C) := by
  letI : Fact (Nat.Prime order) := ⟨order_prime⟩
  have ho : addOrderOf C = order := addOrderOf_eq_prime hord hC
  have hbig : 3 < order := by norm_num [order]
  have hnot (m : Nat) (hm0 : 0 < m) (hm : m < order) : m • C ≠ 0 := by
    intro hz
    have hd := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hz
    rw [ho] at hd
    exact (Nat.le_of_dvd hm0 hd).not_gt hm
  apply ipxInput_injective C hC
  · simpa [two_nsmul] using hnot 2 (by decide) (by omega)
  · have h := hnot 3 (by decide) (by omega)
    rwa [show (3 : Nat) = 2 + 1 from rfl, succ_nsmul, two_nsmul] at h

theorem ipxWords_eq {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point) (row : Fin n)
    {x y : Fp} (hC : curve.toAffine.Nonsingular x y)
    (hrow : constantPoint Q (coeffs row) = .some hC) (k : Fin 4) :
    readEndpointWords coeffs Q row (ipxA k) =
        coordinateWordBits (fig14EncodedEquiv x y (fig14PointEncoding (ipxInput (.some hC) k))) ∧
      readEndpointWords coeffs Q row (ipxB k) =
        coordinateWordBits (fig14PointEncoding (ipxInput (.some hC) k + .some hC)) := by
  have h := readEndpointWords_pairs coeffs Q row
  rw [hrow,protectedExceptionPairs_eq hC] at h
  simp only [fixedExceptionPairs,fixedExceptionInputs,List.map_cons,List.map_nil,
    List.cons.injEq,Prod.mk.injEq] at h
  obtain ⟨⟨h0,h4⟩,⟨h1,h5⟩,⟨h2,h6⟩,⟨h3,h7⟩,-⟩ := h
  fin_cases k
  · exact ⟨h0,h4⟩
  · exact ⟨h1,h5⟩
  · exact ⟨h2,h6⟩
  · exact ⟨h3,h7⟩

/-- The correction model applied to the formula output `F(enc P)` of any point `P` gives
`enc (P + C)` and clears every flag, for every table row holding a finite point of prime order. -/
theorem ipxModel_point {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point) (row : Fin n)
    {x y : Fp} (hC : curve.toAffine.Nonsingular x y)
    (hrow : constantPoint Q (coeffs row) = .some hC) (hord : order • (.some hC : Point) = 0)
    (P : Point) :
    ipxModel (readEndpointWords coeffs Q row)
        (coordinateWordBits (fig14EncodedEquiv x y (fig14PointEncoding P)),fun _ => false) =
      (coordinateWordBits (fig14PointEncoding (P + .some hC)),fun _ => false) := by
  have hw := ipxWords_eq coeffs Q row hC hrow
  have hf : Function.Injective
      (fun R : Point => coordinateWordBits (fig14EncodedEquiv x y (fig14PointEncoding R))) :=
    coordinateWordBits_injective.comp ((fig14EncodedEquiv x y).injective.comp fig14PointEncoding_injective)
  have hg : Function.Injective
      (fun R : Point => coordinateWordBits (fig14PointEncoding (R + .some hC))) :=
    coordinateWordBits_injective.comp (fig14PointEncoding_injective.comp (add_left_injective _))
  have hinj := ipxInput_injective_of_order (.some hC) (by simp) hord
  have ha : ∀ j k, readEndpointWords coeffs Q row (ipxA j) = readEndpointWords coeffs Q row (ipxA k) →
      j = k := by
    intro j k h
    rw [(hw j).1,(hw k).1] at h
    exact hinj (hf h)
  have hb : ∀ j k, readEndpointWords coeffs Q row (ipxB j) = readEndpointWords coeffs Q row (ipxB k) →
      j = k := by
    intro j k h
    rw [(hw j).2,(hw k).2] at h
    exact hinj (hg h)
  by_cases hP : ∃ j, P = ipxInput (.some hC) j
  · obtain ⟨j,rfl⟩ := hP
    rw [← (hw j).1,ipxModel_exceptional _ ha hb j,(hw j).2]
  · push_neg at hP
    have hout : P ∉ fig14ExceptionalPoints (.some hC) := by
      have h0 : P ≠ 0 := hP 0
      have h1 : P ≠ .some hC := hP 1
      have h2 : P ≠ -(.some hC) := hP 2
      have h3 : P ≠ -((.some hC) + (.some hC)) := hP 3
      simp only [fig14ExceptionalPoints,Finset.mem_insert,Finset.mem_singleton,not_or]
      exact ⟨h0,h1,h2,h3⟩
    have hn := fig14EncodedEquiv_nonexceptional hC P hout
    have ha' : ∀ k, coordinateWordBits (fig14EncodedEquiv x y (fig14PointEncoding P)) ≠
        readEndpointWords coeffs Q row (ipxA k) := by
      intro k h
      rw [(hw k).1] at h
      exact hP k (hf h)
    have hb' : ∀ k, coordinateWordBits (fig14EncodedEquiv x y (fig14PointEncoding P)) ≠
        readEndpointWords coeffs Q row (ipxB k) := by
      intro k h
      rw [hn,(hw k).2] at h
      exact hP k (hg h)
    rw [ipxModel_generic _ _ ha' hb',hn]

end

end ShorECDLP.Paper2607_13816.ChallengeMigration

-- ==== part: IpxCircuit ====

/-! # In-place XOR correction: the circuit

Every wire of the correction block lies in the core streaming allocation:

* the accumulator ports `accumulatorPort` (263..518, 580..835, 838) are the data word;
* the one-hot flags are wires 0..3, the half-result of the split zero test is wire 4 and the
  v-chain scratch is 5..259; all of them are idle and clean between window additions
  (`Secp256k1ZeroAllowedInputValid`);
* table queries use the window's own 15-bit unary iteration (`batchWindowTree` on the address
  wires 839..853 with path wires 519..533), controlled by the window control 836 or by a flag.

A table query XORs one or two endpoint words of the selected row into the accumulator. A zero
test is three 257-bit `computeEqConst` calls: `h ^= [low = 0]`, `f ^= [(h :: high) = 1]`,
`h ^= [low = 0]`. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Classical Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1

def ipxFlag (k : Fin 4) : Wire := k.val
def ipxHalf : Wire := 4
def ipxScratch : List Wire := List.range' 5 255
def ipxLow : List Wire := List.range' 263 256 ++ [580]
def ipxHigh : List Wire := List.range' 581 255 ++ [838]

def ipxControl : Option (Fin 4) → Wire
  | none => 836
  | some k => ipxFlag k

def ipxPorts {n : Nat} (row : Fin n) (j : Fin 8) : List (Wire × EndpointBit n) :=
  List.ofFn fun i : Fin 513 => (accumulatorPort i, exceptionalEndpointWords row j i)

def ipxPortsOpt {n : Nat} (row : Fin n) : Option (Fin 8) → List (Wire × EndpointBit n)
  | none => []
  | some j => ipxPorts row j

def ipxLeaf {n : Nat} (row : Fin n) (q : Wire) (u : Fin 8) (v : Option (Fin 8)) :
    List (TemplateGate n) :=
  endpointSelectGates q (ipxPorts row u) ++ endpointSelectGates q (ipxPortsOpt row v)

def ipxLeafCircuit {n : Nat} (read : ConstantBit n → Bool) (row : Fin n) (q : Wire)
    (u : Fin 8) (v : Option (Fin 8)) : Circuit :=
  tableXorGates q (endpointRawMask read (ipxPorts row u)) ++
    tableXorGates q (endpointRawMask read (ipxPortsOpt row v))

theorem ipxLeaf_source {n : Nat} (read : ConstantBit n → Bool) (row : Fin n) (q : Wire)
    (u : Fin 8) (v : Option (Fin 8)) :
    (ipxLeaf row q u v).flatMap (TemplateGate.instantiate read) = ipxLeafCircuit read row q u v := by
  simp only [ipxLeaf,List.flatMap_append,endpointSelectGates_source,ipxLeafCircuit]

/-- Zero test of the complete accumulator word into flag `k`. -/
def ipxTest (k : Fin 4) : Circuit :=
  computeEqConst ipxLow 0 ipxHalf ipxScratch ++
    computeEqConst (ipxHalf :: ipxHigh) 1 (ipxFlag k) ipxScratch ++
    computeEqConst ipxLow 0 ipxHalf ipxScratch

/-- Measured uncomputation reuses the same clean scratch wires. -/
def ipxMeasuredTestOps {n : Nat} (k : Fin 4) : List (LookupOp n) :=
  measuredEqualityOps ipxLow 0 ipxHalf ipxScratch ++
    measuredEqualityOps (ipxHalf :: ipxHigh) 1 (ipxFlag k) ipxScratch ++
    measuredEqualityOps ipxLow 0 ipxHalf ipxScratch

theorem ipxMeasuredTestOps_skeleton {n : Nat} (k : Fin 4) :
    equalitySkeleton (@ipxMeasuredTestOps n k) = ipxTest k := by
  simp only [ipxMeasuredTestOps,equalitySkeleton_append,measuredEqualityOps_skeleton,ipxTest]

noncomputable def ipxMeasuredTest (k : Fin 4) : AdaptiveCircuit :=
  ((computeEqConstAdaptive ipxLow 0 ipxHalf ipxScratch).seq
    (computeEqConstAdaptive (ipxHalf :: ipxHigh) 1 (ipxFlag k) ipxScratch)).seq
    (computeEqConstAdaptive ipxLow 0 ipxHalf ipxScratch)

theorem ipxMeasuredTestOps_source {n : Nat} (read : ConstantBit n → Bool) (k : Fin 4) :
    lookupCircuit read (ipxMeasuredTestOps k) = ipxMeasuredTest k := by
  simp only [ipxMeasuredTestOps,lookupCircuit_append,measuredEqualityOps_source,ipxMeasuredTest]

theorem ipxMeasuredTestOps_measurements {n : Nat} (k : Fin 4) :
    lookupMeasurements (@ipxMeasuredTestOps n k) = 765 := by
  simp only [ipxMeasuredTestOps,lookupMeasurements_append]
  rw [measuredEqualityOps_measurements _ _ _ _ (by simp [ipxLow,ipxScratch]),
    measuredEqualityOps_measurements _ _ _ _ (by simp [ipxHigh,ipxScratch])]
  simp [ipxLow,ipxHigh]

theorem ipxMeasuredTest_tCount (k : Fin 4) : (ipxMeasuredTest k).tCount = 5376 := by
  simp only [ipxMeasuredTest,adaptive_tCount_seq]
  rw [computeEqConstAdaptive_tCount _ _ _ _ (by simp [ipxLow,ipxScratch]),
    computeEqConstAdaptive_tCount _ _ _ _ (by simp [ipxHigh,ipxScratch])]
  simp [ipxLow,ipxHigh,mcxVChainAdaptiveToffoliCost]

def ipxOps {n : Nat} (rows : Nat → Fin n) (tree : UnaryActionTree) (paths : List Wire) :
    List IpxOp → List (LookupOp n)
  | [] => []
  | .query c u v :: ops =>
    unaryLookupOps (fun l q => ipxLeaf (rows l) q u v) tree (ipxControl c) paths ++
      ipxOps rows tree paths ops
  | .test k :: ops => ipxMeasuredTestOps k ++ ipxOps rows tree paths ops

noncomputable def ipxSourceOps {n : Nat} (read : ConstantBit n → Bool) (rows : Nat → Fin n)
    (tree : UnaryActionTree) (paths : List Wire) : List IpxOp → AdaptiveCircuit
  | [] => .done
  | .query c u v :: ops =>
    (unaryAction .inc (fun l q => ipxLeafCircuit read (rows l) q u v) tree
      (ipxControl c) paths).seq (ipxSourceOps read rows tree paths ops)
  | .test k :: ops => (ipxMeasuredTest k).seq (ipxSourceOps read rows tree paths ops)

theorem ipxOps_source {n : Nat} (read : ConstantBit n → Bool) (rows : Nat → Fin n)
    (tree : UnaryActionTree) (paths : List Wire) (ops : List IpxOp) :
    lookupCircuit read (ipxOps rows tree paths ops) = ipxSourceOps read rows tree paths ops := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | query c u v =>
      simp only [ipxOps,lookupCircuit_append,unaryLookupOps_circuit,ipxLeaf_source,ih,ipxSourceOps]
    | test k => simp only [ipxOps,lookupCircuit_append,ipxMeasuredTestOps_source,ih,ipxSourceOps]

def ipxProgramOf {n : Nat} (rows : Nat → Fin n) (tree : UnaryActionTree) (paths : List Wire)
    (start : Nat) : (count : Nat) × Straight n start (start+count) :=
  ⟨lookupMeasurements (ipxOps rows tree paths ipxSchedule), lookupProgram n (ipxOps rows tree paths ipxSchedule) start⟩

/-- The compiled correction block of one window. -/
def ipxProgram (w : OddWindow) (start : Nat) : (count : Nat) × Straight 983040 start (start+count) :=
  ipxProgramOf (batchWindowRows w) batchWindowTree pointLookupPath start

noncomputable def ipxSource (Q : Point) (w : OddWindow) : AdaptiveCircuit :=
  ipxSourceOps (readConstant coefficientAt Q) (batchWindowRows w) batchWindowTree pointLookupPath
    ipxSchedule

theorem ipxProgram_run (w : OddWindow) (start : Nat) (Q : Point) (history : Fin start → Bool) :
    compiledRun (ipxProgram w start) (readConstant coefficientAt Q) history = (ipxSource Q w).run := by
  simp only [ipxProgram,ipxProgramOf,compiledRun,lookupProgram_run,ipxOps_source,ipxSource]

/-! ## Layout facts -/

theorem ipxControl_lt (c : Option (Fin 4)) : ipxControl c < 4 ∨ ipxControl c = 836 := by
  cases c with
  | none => exact Or.inr rfl
  | some k => exact Or.inl k.isLt

theorem ipxTree_layout (c : Option (Fin 4)) : batchWindowTree.Layout (ipxControl c) pointLookupPath := by
  apply tableAddressTree_layout _ _ _ _ _ (by decide)
  have hc := ipxControl_lt c
  simp only [pointLookupAddress,pointLookupPath,List.cons_append,List.nodup_cons,List.mem_append,
    List.mem_range'_1,List.nodup_append]
  refine ⟨by (try dsimp only [Wire] at *); omega,List.nodup_range',List.nodup_range',?_⟩
  intro a ha b hb
  (try dsimp only [Wire] at *)
  omega

theorem ipxTree_wires (c : Option (Fin 4)) (w : Wire)
    (hw : w ∈ ipxControl c :: batchWindowTree.indexWires.dedup ++ pointLookupPath) :
    w < 4 ∨ w = 836 ∨ (519 ≤ w ∧ w < 534) ∨ (839 ≤ w ∧ w < 854) := by
  unfold batchWindowTree at hw
  rw [tableAddressTree_index pointLookupAddress 0 1 (by decide)] at hw
  have hc := ipxControl_lt c
  simp only [List.mem_cons,List.mem_append,pointLookupAddress,pointLookupPath,List.mem_range'_1] at hw
  (try dsimp only [Wire] at *)
  omega

theorem accumulatorPort_mem (i : Fin 513) : accumulatorPort i ∈ pointLogicalWires := by
  rw [← accumulatorPort_list]
  exact List.mem_ofFn.mpr ⟨i,rfl⟩

theorem accumulatorPort_injective : Function.Injective accumulatorPort := by
  have h := pointLogicalWires_nodup
  rw [← accumulatorPort_list] at h
  exact List.nodup_ofFn.mp h

theorem pointLogicalWires_bounds (w : Wire) (hw : w ∈ pointLogicalWires) :
    (263 ≤ w ∧ w < 519) ∨ (580 ≤ w ∧ w < 836) ∨ w = 838 := by
  simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,List.mem_range'_1,
    List.mem_cons,List.not_mem_nil,or_false] at hw
  (try dsimp only [Wire] at *)
  omega

theorem ipxPorts_nodup {n : Nat} (row : Fin n) (j : Fin 8) : ((ipxPorts row j).map Prod.fst).Nodup := by
  simp only [ipxPorts,List.map_ofFn,Function.comp_def]
  exact List.nodup_ofFn.mpr accumulatorPort_injective

theorem ipxPortsOpt_nodup {n : Nat} (row : Fin n) (v : Option (Fin 8)) :
    ((ipxPortsOpt row v).map Prod.fst).Nodup := by
  cases v with
  | none => exact List.nodup_nil
  | some j => exact ipxPorts_nodup row j

theorem ipxPorts_wire {n : Nat} (row : Fin n) (j : Fin 8) (w : Wire)
    (hw : w ∈ (ipxPorts row j).map Prod.fst) : w ∈ pointLogicalWires := by
  simp only [ipxPorts,List.map_ofFn,Function.comp_def,List.mem_ofFn] at hw
  obtain ⟨i,rfl⟩ := hw
  exact accumulatorPort_mem i

theorem ipxPortsOpt_wire {n : Nat} (row : Fin n) (v : Option (Fin 8)) (w : Wire)
    (hw : w ∈ (ipxPortsOpt row v).map Prod.fst) : w ∈ pointLogicalWires := by
  cases v with
  | none => simp [ipxPortsOpt] at hw
  | some j => exact ipxPorts_wire row j w hw

theorem endpointRawMask_wire {n : Nat} (read : ConstantBit n → Bool) (ports : List (Wire × EndpointBit n))
    (w : Wire) (hw : w ∈ endpointRawMask read ports) : w ∈ ports.map Prod.fst := by
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hw
  exact List.mem_map.mpr ⟨p,(List.mem_filter.mp hp).1,rfl⟩

theorem ipxMask_point {n : Nat} (read : ConstantBit n → Bool) (row : Fin n) (u : Fin 8) (w : Wire)
    (hw : w ∈ endpointRawMask read (ipxPorts row u)) : w ∈ pointLogicalWires :=
  ipxPorts_wire row u w (endpointRawMask_wire read _ w hw)

theorem ipxMaskOpt_point {n : Nat} (read : ConstantBit n → Bool) (row : Fin n) (v : Option (Fin 8))
    (w : Wire) (hw : w ∈ endpointRawMask read (ipxPortsOpt row v)) : w ∈ pointLogicalWires :=
  ipxPortsOpt_wire row v w (endpointRawMask_wire read _ w hw)

theorem ipxTree_outside (c : Option (Fin 4)) (w : Wire)
    (hw : w ∈ ipxControl c :: batchWindowTree.indexWires.dedup ++ pointLookupPath) :
    w ∉ pointLogicalWires := by
  intro hp
  have h1 := ipxTree_wires c w hw
  have h2 := pointLogicalWires_bounds w hp
  (try dsimp only [Wire] at *)
  omega

theorem ipxFlag_lt (k : Fin 4) : ipxFlag k < 4 := k.isLt

theorem ipxLow_layout : EqConstLayout ipxLow ipxHalf ipxScratch := by
  refine ⟨by simp [ipxLow,ipxScratch],?_⟩
  unfold McxVChainLayout ipxLow ipxHalf ipxScratch
  refine List.nodup_append.mpr ⟨?_,?_,?_⟩
  · refine List.nodup_append.mpr ⟨List.nodup_range',List.nodup_singleton _,?_⟩
    intro a ha b hb
    simp at ha hb
    (try dsimp only [Wire] at *)
    omega
  · refine List.nodup_cons.mpr ⟨?_,List.nodup_range'⟩
    simp
  · intro a ha b hb
    simp at ha hb
    (try dsimp only [Wire] at *)
    omega

theorem ipxHigh_layout (k : Fin 4) : EqConstLayout (ipxHalf :: ipxHigh) (ipxFlag k) ipxScratch := by
  refine ⟨by simp [ipxHigh,ipxScratch],?_⟩
  have hk := ipxFlag_lt k
  generalize ipxFlag k = f at hk ⊢
  unfold McxVChainLayout ipxHigh ipxHalf ipxScratch
  refine List.nodup_append.mpr ⟨?_,?_,?_⟩
  · refine List.nodup_cons.mpr ⟨?_,?_⟩
    · simp
    · refine List.nodup_append.mpr ⟨List.nodup_range',List.nodup_singleton _,?_⟩
      intro a ha b hb
      simp at ha hb
      (try dsimp only [Wire] at *)
      omega
  · refine List.nodup_cons.mpr ⟨?_,List.nodup_range'⟩
    simp
    (try dsimp only [Wire] at *)
    omega
  · intro a ha b hb
    simp at ha hb
    (try dsimp only [Wire] at *)
    omega

/-! ## Resources -/

def ipxQueries : List IpxOp → Nat
  | [] => 0
  | .query _ _ _ :: ops => 1 + ipxQueries ops
  | .test _ :: ops => ipxQueries ops

theorem ipxSchedule_queries : ipxQueries ipxSchedule = 13 := rfl

def ipxTests : List IpxOp → Nat
  | [] => 0
  | .query _ _ _ :: ops => ipxTests ops
  | .test _ :: ops => 1 + ipxTests ops

theorem ipxSchedule_tests : ipxTests ipxSchedule = 8 := rfl

theorem ipxOps_measurements {n : Nat} (rows : Nat → Fin n) (tree : UnaryActionTree) (paths : List Wire)
    (hl : ∀ c, tree.Layout (ipxControl c) paths) (ops : List IpxOp) :
    lookupMeasurements (ipxOps rows tree paths ops) = ipxQueries ops * tree.internalNodes + 765 * ipxTests ops := by
  induction ops with
  | nil => simp [ipxOps,lookupMeasurements,ipxQueries,ipxTests]
  | cons op ops ih =>
    cases op with
    | query c u v =>
      simp only [ipxOps,lookupMeasurements_append,unaryLookupOps_measurements _ _ _ _ (hl c),
        ih,ipxQueries,ipxTests,Nat.add_mul,Nat.one_mul]
      omega
    | test k =>
      simp only [ipxOps,lookupMeasurements_append,ipxMeasuredTestOps_measurements,ih,ipxQueries,ipxTests]
      omega

theorem batchWindowTree_nodes : batchWindowTree.internalNodes = 32767 := by
  have h := tableAddressTree_nodes pointLookupAddress 0 1
  change batchWindowTree.internalNodes + 1 = 32768 at h
  omega

theorem ipxProgram_count (w : OddWindow) (start : Nat) : (ipxProgram w start).1 = 432091 := by
  simp only [ipxProgram,ipxProgramOf]
  rw [ipxOps_measurements _ _ _ ipxTree_layout,ipxSchedule_queries,ipxSchedule_tests,batchWindowTree_nodes]

theorem ipxTest_tCount (k : Fin 4) : ShorECDLP.tCount (ipxTest k) = 10731 := by
  simp only [ipxTest,tCount_append]
  rw [computeEqConst_tCount _ _ _ _ (by simp [ipxLow,ipxScratch]),
    computeEqConst_tCount _ _ _ _ (by simp [ipxHigh,ipxScratch])]
  simp only [ipxLow,ipxHigh,List.length_cons,List.length_append,List.length_range']
  rfl

theorem ipxQuery_tCount {n : Nat} (read : ConstantBit n → Bool) (rows : Nat → Fin n)
    (tree : UnaryActionTree) (paths : List Wire) (c : Option (Fin 4)) (u : Fin 8) (v : Option (Fin 8))
    (hl : tree.Layout (ipxControl c) paths) :
    (unaryAction .inc (fun l q => ipxLeafCircuit read (rows l) q u v) tree
      (ipxControl c) paths).tCount = 7 * tree.internalNodes := by
  rw [unaryAction_tCount _ _ _ _ _ hl]
  have hz (t : UnaryActionTree) (q : Wire) (ws : List Wire) :
      t.leafCostSum (fun l wire => ShorECDLP.tCount (ipxLeafCircuit read (rows l) wire u v)) q ws = 0 := by
    induction t generalizing q ws with
    | leaf l => simp [UnaryActionTree.leafCostSum,ipxLeafCircuit,tCount_append]
    | node bit zero one ihz iho =>
      cases ws <;> simp only [UnaryActionTree.leafCostSum,ihz,iho,zero_add]
  rw [hz,zero_add]

def ipxCost (nodes : Nat) : List IpxOp → Nat
  | [] => 0
  | .query _ _ _ :: ops => 7*nodes + ipxCost nodes ops
  | .test _ :: ops => 5376 + ipxCost nodes ops

theorem ipxSourceOps_tCount {n : Nat} (read : ConstantBit n → Bool) (rows : Nat → Fin n)
    (tree : UnaryActionTree) (paths : List Wire) (hl : ∀ c, tree.Layout (ipxControl c) paths)
    (ops : List IpxOp) :
    (ipxSourceOps read rows tree paths ops).tCount = ipxCost tree.internalNodes ops := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | query c u v => simp only [ipxSourceOps,adaptive_tCount_seq,ipxQuery_tCount _ _ _ _ _ _ _ (hl c),ih,ipxCost]
    | test k => simp only [ipxSourceOps,adaptive_tCount_seq,ipxMeasuredTest_tCount,ih,ipxCost]

theorem ipxSchedule_cost (nodes : Nat) : ipxCost nodes ipxSchedule = 91*nodes+43008 := by
  simp only [ipxSchedule,ipxPhase1,ipxPhase2,ipxPhase3,List.cons_append,List.nil_append,ipxCost]
  omega

theorem ipxSource_tCount (Q : Point) (w : OddWindow) : (ipxSource Q w).tCount = 3024805 := by
  rw [ipxSource,ipxSourceOps_tCount _ _ _ _ ipxTree_layout,ipxSchedule_cost,batchWindowTree_nodes]

theorem ipxProgram_tCount (w : OddWindow) (start : Nat) (Q : Point) (history : Fin start → Bool) :
    compiledTCount (ipxProgram w start) (readConstant coefficientAt Q) history = (ipxSource Q w).tCount := by
  simp only [ipxProgram,ipxProgramOf,compiledTCount,lookupProgram_tCount,ipxOps_source,ipxSource]

/-! ## Well-formedness -/

theorem ipxLeaf_wellFormed {n : Nat} (row : Fin n) (q : Wire) (u : Fin 8) (v : Option (Fin 8))
    (hq : q ∉ pointLogicalWires) : ∀ g ∈ ipxLeaf row q u v, g.WellFormed := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · apply endpointSelectGates_wellFormed q _ ?_ g hg
    intro p hp he
    exact hq (he ▸ ipxPorts_wire row u p.1 (List.mem_map.mpr ⟨p,hp,rfl⟩))
  · apply endpointSelectGates_wellFormed q _ ?_ g hg
    intro p hp he
    exact hq (he ▸ ipxPortsOpt_wire row v p.1 (List.mem_map.mpr ⟨p,hp,rfl⟩))

theorem ipxTest_wellFormed (k : Fin 4) : CircuitWellFormed (ipxTest k) := by
  rw [ipxTest,circuitWellFormed_append,circuitWellFormed_append]
  exact ⟨⟨computeEqConst_wellFormed _ _ _ _ ipxLow_layout,
    computeEqConst_wellFormed _ _ _ _ (ipxHigh_layout k)⟩,
    computeEqConst_wellFormed _ _ _ _ ipxLow_layout⟩

theorem ipxOps_physical {n : Nat} (rows : Nat → Fin n) (tree : UnaryActionTree) (paths : List Wire)
    (hl : ∀ c, tree.Layout (ipxControl c) paths)
    (hout : ∀ c, ∀ w ∈ ipxControl c :: paths, w ∉ pointLogicalWires) (ops : List IpxOp) :
    ∀ op ∈ ipxOps rows tree paths ops, op.Physical := by
  induction ops with
  | nil => intro op ho; cases ho
  | cons op ops ih =>
    cases op with
    | query c u v =>
      rw [ipxOps,List.forall_mem_append]
      exact ⟨unaryLookupOps_physical _ _ _ _ (hl c)
        (fun l q hq => ipxLeaf_wellFormed _ _ _ _ (hout c q hq)),ih⟩
    | test k =>
      simp only [ipxOps,List.forall_mem_append,ipxMeasuredTestOps]
      exact ⟨⟨⟨measuredEqualityOps_physical _ _ _ _ ipxLow_layout,
        measuredEqualityOps_physical _ _ _ _ (ipxHigh_layout k)⟩,
        measuredEqualityOps_physical _ _ _ _ ipxLow_layout⟩,ih⟩

theorem ipxPaths_outside (c : Option (Fin 4)) (w : Wire) (hw : w ∈ ipxControl c :: pointLookupPath) :
    w ∉ pointLogicalWires := by
  intro hp
  have h2 := pointLogicalWires_bounds w hp
  have hc := ipxControl_lt c
  simp only [List.mem_cons,pointLookupPath,List.mem_range'_1] at hw
  (try dsimp only [Wire] at *)
  omega

theorem ipxProgramOf_wellFormed {n : Nat} (rows : Nat → Fin n) (tree : UnaryActionTree)
    (paths : List Wire) (hl : ∀ c, tree.Layout (ipxControl c) paths)
    (hout : ∀ c, ∀ w ∈ ipxControl c :: paths, w ∉ pointLogicalWires) (start : Nat) :
    (ipxProgramOf rows tree paths start).2.WellFormed :=
  lookupProgram_wellFormed _ (ipxOps_physical _ _ _ hl hout _) start

attribute [local irreducible] ipxProgramOf in
theorem ipxProgram_wellFormed (w : OddWindow) (start : Nat) : (ipxProgram w start).2.WellFormed :=
  ipxProgramOf_wellFormed _ _ _ ipxTree_layout ipxPaths_outside start

end ShorECDLP.Paper2607_13816.ChallengeMigration

-- ==== part: IpxSemantics ====

/-! # In-place XOR correction: semantics

Every step of the correction block acts on the accumulator word `s ∘ accumulatorPort` and the
four flags exactly as `ipxModelStep` prescribes, keeps the path, scratch and half-result wires
clean and the window control set, and leaves every other wire unchanged. On every reachable
window state the model (`ipxModel_point`) then turns `F(enc P)` into `enc (P + C)` and clears
the flags, so the block writes `P + C` into the accumulator and restores every other wire. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Classical Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1

/-- Clean path, scratch and half-result wires and an enabled window control. -/
def IpxInv (paths : List Wire) (s : BasisState) : Prop :=
  Clean paths s ∧ Clean ipxScratch s ∧ s ipxHalf = false ∧ s 836 = true

/-- Wire roles of a query tree; instantiated by `batchWindowTree` below. -/
structure IpxGeometry (tree : UnaryActionTree) (paths : List Wire) : Prop where
  layout : ∀ c, tree.Layout (ipxControl c) paths
  route : ∀ c, ∀ w ∈ ipxControl c :: tree.indexWires.dedup ++ paths, w ∉ pointLogicalWires
  index : ∀ w ∈ tree.indexWires, ∀ k, w ≠ ipxFlag k
  path : ∀ w ∈ paths, ∀ k, w ≠ ipxFlag k

theorem ipxGeometry_window : IpxGeometry batchWindowTree pointLookupPath := by
  refine ⟨ipxTree_layout,ipxTree_outside,?_,?_⟩
  · intro w hw k he
    have h := (tableAddressTree_mem_index pointLookupAddress 0 1 w).mp hw
    have hk := ipxFlag_lt k
    simp only [pointLookupAddress,List.mem_range'_1] at h
    (try dsimp only [Wire] at *)
    omega
  · intro w hw k he
    have hk := ipxFlag_lt k
    simp only [pointLookupPath,List.mem_range'_1] at hw
    (try dsimp only [Wire] at *)
    omega

theorem ipxFlag_injective : Function.Injective ipxFlag := fun _ _ h => Fin.ext h

theorem ipxFlag_outside (k : Fin 4) : ipxFlag k ∉ pointLogicalWires := by
  intro h
  have h1 := pointLogicalWires_bounds _ h
  have h2 := ipxFlag_lt k
  (try dsimp only [Wire] at *)
  omega

theorem ipxScratch_outside (w : Wire) (hw : w ∈ ipxScratch) : w ∉ pointLogicalWires := by
  intro h
  have h1 := pointLogicalWires_bounds _ h
  simp only [ipxScratch,List.mem_range'_1] at hw
  (try dsimp only [Wire] at *)
  omega

theorem ipxScratch_flag (w : Wire) (hw : w ∈ ipxScratch) (k : Fin 4) : w ≠ ipxFlag k := by
  have h2 := ipxFlag_lt k
  simp only [ipxScratch,List.mem_range'_1] at hw
  (try dsimp only [Wire] at *)
  omega

theorem ipxHalf_outside : ipxHalf ∉ pointLogicalWires := by
  intro h
  have h1 := pointLogicalWires_bounds _ h
  simp only [ipxHalf] at h1
  (try dsimp only [Wire] at *)
  omega

theorem ipxHalf_flag (k : Fin 4) : ipxHalf ≠ ipxFlag k := by
  have h2 := ipxFlag_lt k
  simp only [ipxHalf]
  (try dsimp only [Wire] at *)
  omega

theorem ipxFlag_ne_of_ge (w : Wire) (hw : 4 ≤ w) (k : Fin 4) : w ≠ ipxFlag k := by
  have h2 := ipxFlag_lt k
  (try dsimp only [Wire] at *)
  omega

theorem ipxFlag_ne_control (k : Fin 4) : (836 : Wire) ≠ ipxFlag k := by
  have h2 := ipxFlag_lt k
  (try dsimp only [Wire] at *)
  omega

/-! ## Table queries -/

theorem ipxMask_word {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point) (row : Fin n) (u : Fin 8)
    (i : Fin 513) :
    decide (accumulatorPort i ∈ endpointRawMask (readConstant coeffs Q) (ipxPorts row u)) =
      readEndpointWords coeffs Q row u i := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  apply endpointRawMask_mem _ _ (ipxPorts_nodup row u)
  exact List.mem_ofFn.mpr ⟨i,rfl⟩

theorem ipxMaskOpt_word {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point) (row : Fin n)
    (v : Option (Fin 8)) (i : Fin 513) :
    decide (accumulatorPort i ∈ endpointRawMask (readConstant coeffs Q) (ipxPortsOpt row v)) =
      ipxOptWord (readEndpointWords coeffs Q row) v i := by
  cases v with
  | none => simp [ipxPortsOpt,endpointRawMask,ipxOptWord]
  | some j => exact ipxMask_word coeffs Q row j i

theorem ipxQuery_run {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point) (rows : Nat → Fin n)
    (tree : UnaryActionTree) (paths : List Wire) (hg : IpxGeometry tree paths)
    (c : Option (Fin 4)) (u : Fin 8) (v : Option (Fin 8)) (s : BasisState) (hc : Clean paths s) :
    let e := readEndpointWords coeffs Q (rows (tree.routeLabel s))
    let out := Classical.run (unaryActionUnitary .inc
      (fun l q => ipxLeafCircuit (readConstant coeffs Q) (rows l) q u v) tree (ipxControl c) paths) s
    (∀ i, out (accumulatorPort i) =
      xor (s (accumulatorPort i)) (s (ipxControl c) && xor (e u i) (ipxOptWord e v i))) ∧
    (∀ w, w ∉ pointLogicalWires → out w = s w) := by
  dsimp only
  have hrun := endpointXorPair_run
    (fun l => endpointRawMask (readConstant coeffs Q) (ipxPorts (rows l) u))
    (fun l => endpointRawMask (readConstant coeffs Q) (ipxPortsOpt (rows l) v))
    tree (ipxControl c) paths (hg.layout c)
    (fun l => endpointRawMask_nodup _ _ (ipxPorts_nodup _ _))
    (fun l => endpointRawMask_nodup _ _ (ipxPortsOpt_nodup _ _))
    (fun l w hw hm => hg.route c w hw (ipxMask_point _ _ _ w hm))
    (fun l w hw hm => hg.route c w hw (ipxMaskOpt_point _ _ _ w hm)) s hc
  change Classical.run (unaryActionUnitary .inc
      (fun l q => tableXorGates q (endpointRawMask (readConstant coeffs Q) (ipxPorts (rows l) u)) ++
        tableXorGates q (endpointRawMask (readConstant coeffs Q) (ipxPortsOpt (rows l) v)))
      tree (ipxControl c) paths) s = _ at hrun
  unfold ipxLeafCircuit
  rw [hrun]
  refine ⟨?_,?_⟩
  · intro i
    simp only [tableXorState,ipxMask_word,ipxMaskOpt_word]
    cases s (accumulatorPort i) <;> cases s (ipxControl c) <;>
      cases readEndpointWords coeffs Q (rows (tree.routeLabel s)) u i <;>
      cases ipxOptWord (readEndpointWords coeffs Q (rows (tree.routeLabel s))) v i <;> rfl
  · intro w hw
    rw [tableXorState_outside _ _ _ w (fun hm => hw (ipxMaskOpt_point _ _ _ w hm)),
      tableXorState_outside _ _ _ w (fun hm => hw (ipxMask_point _ _ _ w hm))]

/-! ## Zero tests -/

theorem registerMatchesFrom_zero (reg : List Wire) (value bit : Nat)
    (hv : ∀ j, bit ≤ j → value.testBit j = false) (s : BasisState) :
    registerMatchesFrom reg value bit s = decide (∀ w ∈ reg, s w = false) := by
  induction reg generalizing bit with
  | nil => simp [registerMatchesFrom]
  | cons w ws ih =>
    rw [registerMatchesFrom,hv bit (Nat.le_refl _),ih (bit+1) (fun j hj => hv j (by omega))]
    simp only [List.mem_cons,forall_eq_or_imp]
    cases s w <;> simp

theorem ipxLowHigh_mem (w : Wire) : w ∈ pointLogicalWires ↔ w ∈ ipxLow ∨ w ∈ ipxHigh := by
  simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,ipxLow,ipxHigh,List.mem_append,
    List.mem_range'_1,List.mem_cons,List.not_mem_nil,or_false]
  (try dsimp only [Wire] at *)
  omega

theorem ipxAcc_zero (s : BasisState) :
    decide (s ∘ accumulatorPort = fun _ => false) =
      (decide (∀ w ∈ ipxLow, s w = false) && decide (∀ w ∈ ipxHigh, s w = false)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · intro h
    have hp : ∀ w ∈ pointLogicalWires, s w = false := by
      intro w hw
      rw [← accumulatorPort_list] at hw
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
      exact congrFun h i
    exact ⟨fun w hw => hp w ((ipxLowHigh_mem w).mpr (Or.inl hw)),
      fun w hw => hp w ((ipxLowHigh_mem w).mpr (Or.inr hw))⟩
  · rintro ⟨hl,hh⟩
    funext i
    rcases (ipxLowHigh_mem _).mp (accumulatorPort_mem i) with h | h
    · exact hl _ h
    · exact hh _ h

theorem ipxHalf_notLow : ipxHalf ∉ ipxLow := by
  simp only [ipxHalf,ipxLow,List.mem_append,List.mem_range'_1,List.mem_singleton]
  (try dsimp only [Wire] at *)
  omega

theorem ipxFlag_notLow (k : Fin 4) : ipxFlag k ∉ ipxLow := by
  have hk := ipxFlag_lt k
  simp only [ipxLow,List.mem_append,List.mem_range'_1,List.mem_singleton]
  (try dsimp only [Wire] at *)
  omega

theorem ipxHalf_notHigh : ipxHalf ∉ ipxHigh := by
  simp only [ipxHalf,ipxHigh,List.mem_append,List.mem_range'_1,List.mem_singleton]
  (try dsimp only [Wire] at *)
  omega

theorem ipxHalf_notScratch : ipxHalf ∉ ipxScratch := by
  simp only [ipxHalf,ipxScratch,List.mem_range'_1]
  omega

theorem registerMatches_upd_not_mem (reg : List Wire) (value : Nat) (s : BasisState) (w : Wire)
    (b : Bool) (hw : w ∉ reg) : registerMatches reg value (s[w ↦ b]) = registerMatches reg value s :=
  registerMatchesFrom_upd_not_mem reg value 0 s w b hw

theorem ipxTest_run (k : Fin 4) (s : BasisState) (hs : Clean ipxScratch s) (hh : s ipxHalf = false) :
    Classical.run (ipxTest k) s =
      s[ipxFlag k ↦ xor (s (ipxFlag k)) (decide (s ∘ accumulatorPort = fun _ => false))] := by
  have hfh := ipxHalf_flag k
  have h1 : Classical.run (computeEqConst ipxLow 0 ipxHalf ipxScratch) s =
      s[ipxHalf ↦ registerMatches ipxLow 0 s] := by
    rw [run_computeEqConst _ _ _ _ s ipxLow_layout hs,hh,Bool.false_xor]
  have hc1 : Clean ipxScratch (s[ipxHalf ↦ registerMatches ipxLow 0 s]) := by
    intro w hw
    rw [upd_other _ _ _ (fun he => ipxHalf_notScratch (by rw [← he]; exact hw))]
    exact hs w hw
  have h2 := run_computeEqConst (ipxHalf :: ipxHigh) 1 (ipxFlag k) ipxScratch
    (s[ipxHalf ↦ registerMatches ipxLow 0 s]) (ipxHigh_layout k) hc1
  have hhs : ∀ b, ∀ w ∈ ipxHigh, s[ipxHalf ↦ b] w = s w := by
    intro b w hw
    rw [upd_other _ _ _ (fun he => ipxHalf_notHigh (by rw [← he]; exact hw))]
  have hq : ∀ b, (∀ w ∈ ipxHigh, s[ipxHalf ↦ b] w = false) ↔ (∀ w ∈ ipxHigh, s w = false) := by
    intro b
    constructor
    · intro h w hw; rw [← hhs b w hw]; exact h w hw
    · intro h w hw; rw [hhs b w hw]; exact h w hw
  have hmatch : registerMatches (ipxHalf :: ipxHigh) 1 (s[ipxHalf ↦ registerMatches ipxLow 0 s]) =
      decide (s ∘ accumulatorPort = fun _ => false) := by
    rw [ipxAcc_zero,registerMatches,registerMatchesFrom,
      registerMatchesFrom_zero _ _ _ (fun j hj => Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le (by decide : 1 < 2^1) (Nat.pow_le_pow_right (by decide) hj))),upd_same,
      registerMatches,registerMatchesFrom_zero _ _ _ (fun j _ => Nat.zero_testBit j)]
    simp only [Nat.testBit_zero]
    cases decide (∀ w ∈ ipxLow, s w = false) <;> simp [hq]
  have hf1 : s[ipxHalf ↦ registerMatches ipxLow 0 s] (ipxFlag k) = s (ipxFlag k) :=
    upd_other _ _ _ hfh.symm
  rw [hmatch,hf1] at h2
  have hc2 : Clean ipxScratch ((s[ipxHalf ↦ registerMatches ipxLow 0 s])[ipxFlag k ↦
      xor (s (ipxFlag k)) (decide (s ∘ accumulatorPort = fun _ => false))]) := by
    intro w hw
    rw [upd_other _ _ _ (ipxScratch_flag w hw k)]
    exact hc1 w hw
  have h3 := run_computeEqConst ipxLow 0 ipxHalf ipxScratch _ ipxLow_layout hc2
  rw [registerMatches_upd_not_mem _ _ _ _ _ (ipxFlag_notLow k),
    registerMatches_upd_not_mem _ _ _ _ _ ipxHalf_notLow,upd_other _ _ _ hfh,upd_same,
    Bool.xor_self] at h3
  rw [ipxTest,Classical.run_append,Classical.run_append,h1,h2,h3]
  funext w
  by_cases hwh : w = ipxHalf
  · subst hwh
    rw [upd_same,upd_other _ _ _ hfh,hh]
  · rw [upd_other _ _ _ hwh]
    by_cases hwf : w = ipxFlag k
    · subst hwf
      rw [upd_same,upd_same]
    · rw [upd_other _ _ _ hwf,upd_other _ _ _ hwf,upd_other _ _ _ hwh]

/-! ## The schedule -/

noncomputable def ipxStepCircuit {n : Nat} (read : ConstantBit n → Bool) (rows : Nat → Fin n)
    (tree : UnaryActionTree) (paths : List Wire) : IpxOp → Circuit
  | .query c u v => unaryActionUnitary .inc
      (fun l q => ipxLeafCircuit read (rows l) q u v) tree (ipxControl c) paths
  | .test k => ipxTest k

noncomputable def ipxUnitaryOps {n : Nat} (read : ConstantBit n → Bool) (rows : Nat → Fin n)
    (tree : UnaryActionTree) (paths : List Wire) : List IpxOp → Circuit
  | [] => []
  | op :: ops => ipxStepCircuit read rows tree paths op ++ ipxUnitaryOps read rows tree paths ops

theorem ipxStep_model {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point) (rows : Nat → Fin n)
    (tree : UnaryActionTree) (paths : List Wire) (hg : IpxGeometry tree paths)
    (op : IpxOp) (s : BasisState) (hs : IpxInv paths s) :
    let out := Classical.run (ipxStepCircuit (readConstant coeffs Q) rows tree paths op) s
    (out ∘ accumulatorPort,fun k => out (ipxFlag k)) =
      ipxModelStep (readEndpointWords coeffs Q (rows (tree.routeLabel s)))
        (s ∘ accumulatorPort,fun k => s (ipxFlag k)) op ∧
    IpxInv paths out ∧ (∀ w, w ∉ pointLogicalWires → (∀ k, w ≠ ipxFlag k) → out w = s w) := by
  dsimp only
  cases op with
  | query c u v =>
    simp only [ipxStepCircuit]
    have h := ipxQuery_run coeffs Q rows tree paths hg c u v s hs.1
    dsimp only at h
    have hact : s (ipxControl c) = ipxActive (fun k => s (ipxFlag k)) c := by
      cases c with
      | none => exact hs.2.2.2
      | some k => rfl
    have hpath : ∀ w ∈ paths, w ∉ pointLogicalWires := fun w hw =>
      hg.route c w (List.mem_cons_of_mem _ (List.mem_append_right _ hw))
    refine ⟨?_,⟨?_,?_,?_,?_⟩,fun w hw _ => h.2 w hw⟩
    · simp only [ipxModelStep]
      refine Prod.ext ?_ ?_
      · dsimp only
        funext i
        simp only [Function.comp_apply,h.1 i,← hact]
        cases s (ipxControl c) <;> simp [wordXor]
      · dsimp only
        funext k
        exact h.2 _ (ipxFlag_outside k)
    · intro w hw; rw [h.2 w (hpath w hw)]; exact hs.1 w hw
    · intro w hw; rw [h.2 w (ipxScratch_outside w hw)]; exact hs.2.1 w hw
    · rw [h.2 _ ipxHalf_outside]; exact hs.2.2.1
    · rw [h.2 836 (by decide +kernel)]; exact hs.2.2.2
  | test k =>
    simp only [ipxStepCircuit]
    rw [ipxTest_run k s hs.2.1 hs.2.2.1]
    refine ⟨?_,⟨?_,?_,?_,?_⟩,?_⟩
    · simp only [ipxModelStep]
      refine Prod.ext ?_ ?_
      · dsimp only
        funext i
        simp only [Function.comp_apply]
        rw [upd_other _ _ _ (fun he => ipxFlag_outside k (by rw [← he]; exact accumulatorPort_mem i))]
      · dsimp only
        funext j
        by_cases hj : j = k
        · subst hj; simp only [upd_same,Function.update_self]
        · rw [upd_other _ _ _ (fun he => hj (ipxFlag_injective he)),Function.update_of_ne hj]
    · intro w hw; rw [upd_other _ _ _ (hg.path w hw k)]; exact hs.1 w hw
    · intro w hw; rw [upd_other _ _ _ (ipxScratch_flag w hw k)]; exact hs.2.1 w hw
    · rw [upd_other _ _ _ (ipxHalf_flag k)]; exact hs.2.2.1
    · rw [upd_other _ _ _ (ipxFlag_ne_control k)]; exact hs.2.2.2
    · intro w _ hf; exact upd_other _ _ _ (hf k)

attribute [local irreducible] ipxStepCircuit

theorem ipxUnitary_model {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point) (rows : Nat → Fin n)
    (tree : UnaryActionTree) (paths : List Wire) (hg : IpxGeometry tree paths)
    (ops : List IpxOp) (s : BasisState) (hs : IpxInv paths s) :
    let out := Classical.run (ipxUnitaryOps (readConstant coeffs Q) rows tree paths ops) s
    (out ∘ accumulatorPort,fun k => out (ipxFlag k)) =
      ops.foldl (ipxModelStep (readEndpointWords coeffs Q (rows (tree.routeLabel s))))
        (s ∘ accumulatorPort,fun k => s (ipxFlag k)) ∧
    IpxInv paths out ∧ (∀ w, w ∉ pointLogicalWires → (∀ k, w ≠ ipxFlag k) → out w = s w) := by
  induction ops generalizing s with
  | nil => exact ⟨rfl,hs,fun _ _ _ => rfl⟩
  | cons op ops ih =>
    let mid := Classical.run (ipxStepCircuit (readConstant coeffs Q) rows tree paths op) s
    have hstep := ipxStep_model coeffs Q rows tree paths hg op s hs
    have htail := ih mid hstep.2.1
    have hr : tree.routeLabel mid = tree.routeLabel s := by
      apply UnaryActionTree.routeLabel_congr
      intro w hw
      apply hstep.2.2 w
      · exact hg.route none w (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_dedup.mpr hw)))
      · exact hg.index w hw
    dsimp only at htail ⊢
    rw [ipxUnitaryOps,Classical.run_append]
    refine ⟨?_,htail.2.1,fun w hw hf => (htail.2.2 w hw hf).trans (hstep.2.2 w hw hf)⟩
    rw [htail.1,hr,hstep.1]
    rfl

/-! ## Coherence -/

theorem ipxStep_HPFree {n : Nat} (read : ConstantBit n → Bool) (rows : Nat → Fin n)
    (tree : UnaryActionTree) (paths : List Wire) (op : IpxOp) :
    HPFree (ipxStepCircuit read rows tree paths op) := by
  cases op with
  | query c u v =>
    unfold ipxStepCircuit
    apply unaryActionUnitary_HPFree
    intro l q
    unfold ipxLeafCircuit
    rw [Classical.hpFree_append]
    exact ⟨tableXorGates_HPFree _ _,tableXorGates_HPFree _ _⟩
  | test k =>
    unfold ipxStepCircuit ipxTest
    rw [Classical.hpFree_append,Classical.hpFree_append]
    exact ⟨⟨computeEqConst_HPFree _ _ _ _,computeEqConst_HPFree _ _ _ _⟩,computeEqConst_HPFree _ _ _ _⟩

theorem ipxUnitaryOps_HPFree {n : Nat} (read : ConstantBit n → Bool) (rows : Nat → Fin n)
    (tree : UnaryActionTree) (paths : List Wire) (ops : List IpxOp) :
    HPFree (ipxUnitaryOps read rows tree paths ops) := by
  induction ops with
  | nil => intro g hg; cases hg
  | cons op ops ih =>
    rw [ipxUnitaryOps]
    exact (Classical.hpFree_append _ _).mpr ⟨ipxStep_HPFree read rows tree paths op,ih⟩

private theorem ipxCoherentRestrict {a : AdaptiveCircuit} {v : State →ₗ[ℂ] State}
    {P R : BasisState → Prop} (h : CoherentlyImplementsOn a v P)
    (hp : ∀ s, R s → P s) : CoherentlyImplementsOn a v R := by
  obtain ⟨cs,hc,hm⟩ := h
  exact ⟨cs,hc.imp (fun _ _ hb s hs => hb s (hp s hs)),hm⟩

private theorem ipxCoherentSeq {a b : AdaptiveCircuit} {u v : Circuit} {P R : BasisState → Prop}
    (ha : CoherentlyImplementsOn a (Quantum.run u) P)
    (hb : CoherentlyImplementsOn b (Quantum.run v) R)
    (hu : HPFree u) (hp : ∀ s, P s → R (Classical.run u s)) :
    CoherentlyImplementsOn (a.seq b) (Quantum.run (u ++ v)) P := by
  have h := ha.seq hb (by
    intro s hs
    rw [run_ket_agrees_classical u s hu]
    exact supportedOn_ket R _ (hp s hs))
  apply h.congrIdeal
  intro s _
  exact (Quantum.run_append u v (ket s)).symm

theorem ipxMeasuredTest_coherent (k : Fin 4) :
    CoherentlyImplementsOn (ipxMeasuredTest k) (Quantum.run (ipxTest k))
      (Clean ipxScratch) := by
  have hl := computeEqConstAdaptive_coherent ipxLow 0 ipxHalf ipxScratch ipxLow_layout
  have hh := computeEqConstAdaptive_coherent (ipxHalf :: ipxHigh) 1 (ipxFlag k)
    ipxScratch (ipxHigh_layout k)
  have h12 := ipxCoherentSeq hl hh (computeEqConst_HPFree _ _ _ _)
    (equality_preserves_clean _ _ _ _ ipxLow_layout)
  have h123 := ipxCoherentSeq h12 hl
    ((Classical.hpFree_append _ _).mpr ⟨computeEqConst_HPFree _ _ _ _,computeEqConst_HPFree _ _ _ _⟩)
    (by
      intro st hs
      rw [Classical.run_append]
      exact equality_preserves_clean _ _ _ _ (ipxHigh_layout k) _
        (equality_preserves_clean _ _ _ _ ipxLow_layout st hs))
  exact h123

theorem ipxSourceOps_coherent {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point) (rows : Nat → Fin n)
    (tree : UnaryActionTree) (paths : List Wire) (hg : IpxGeometry tree paths) (ops : List IpxOp) :
    CoherentlyImplementsOn (ipxSourceOps (readConstant coeffs Q) rows tree paths ops)
      (Quantum.run (ipxUnitaryOps (readConstant coeffs Q) rows tree paths ops)) (IpxInv paths) := by
  induction ops with
  | nil =>
    refine ⟨[1],?_,by simp⟩
    apply List.Forall₂.cons
    · intro st hs; simp [ipxUnitaryOps,Quantum.run]
    · exact .nil
  | cons op ops ih =>
    have hp := fun st hs => (ipxStep_model coeffs Q rows tree paths hg op st hs).2.1
    have hf := ipxStep_HPFree (readConstant coeffs Q) rows tree paths op
    cases op with
    | query c u v =>
      have hq := endpointXorPair_coherent
        (fun l => endpointRawMask (readConstant coeffs Q) (ipxPorts (rows l) u))
        (fun l => endpointRawMask (readConstant coeffs Q) (ipxPortsOpt (rows l) v))
        tree (ipxControl c) paths (hg.layout c)
        (fun l => endpointRawMask_nodup _ _ (ipxPorts_nodup _ _))
        (fun l => endpointRawMask_nodup _ _ (ipxPortsOpt_nodup _ _))
        (fun l w hw hm => hg.route c w hw (ipxMask_point _ _ _ w hm))
        (fun l w hw hm => hg.route c w hw (ipxMaskOpt_point _ _ _ w hm))
      have hq' := ipxCoherentRestrict hq (fun st (hs : IpxInv paths st) => hs.1)
      unfold ipxStepCircuit at hf hp
      simpa only [ipxSourceOps,ipxUnitaryOps,ipxStepCircuit,ipxLeafCircuit] using
        ipxCoherentSeq hq' ih hf hp
    | test k =>
      have hu := ipxCoherentRestrict (ipxMeasuredTest_coherent k)
        (fun st (hs : IpxInv paths st) => hs.2.1)
      unfold ipxStepCircuit at hf hp
      simpa only [ipxSourceOps,ipxUnitaryOps,ipxStepCircuit,AdaptiveCircuit.seq] using
        ipxCoherentSeq hu ih hf hp

/-! ## The window correction block -/

noncomputable def ipxUnitary (Q : Point) (w : OddWindow) : Circuit :=
  ipxUnitaryOps (readConstant coefficientAt Q) (batchWindowRows w) batchWindowTree pointLookupPath
    ipxSchedule

noncomputable def ipxState (Q : Point) (w : OddWindow) (s : BasisState) : BasisState :=
  Classical.run (ipxUnitary Q w) s

attribute [local irreducible] ipxUnitaryOps ipxSourceOps

theorem ipxSource_state (Q : Point) (w : OddWindow) :
    CoherentlyImplementsOn (ipxSource Q w) (Finsupp.lmapDomain ℂ ℂ (ipxState Q w))
      (IpxInv pointLookupPath) := by
  have h := ipxSourceOps_coherent coefficientAt Q (batchWindowRows w) batchWindowTree pointLookupPath
    ipxGeometry_window ipxSchedule
  apply h.congrIdeal
  intro st _
  rw [run_ket_agrees_classical _ st (ipxUnitaryOps_HPFree _ _ _ _ _)]
  simp only [ipxState,ipxUnitary,ket,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]

theorem ipxInv_of_valid (s : BasisState) (hv : Secp256k1ZeroAllowedInputValid s) (hq : s 836 = true) :
    IpxInv pointLookupPath s := by
  refine ⟨?_,?_,?_,hq⟩
  · intro w hw
    apply hv.1 w
    simp only [pointLookupPath,List.mem_range'_1] at hw
    simp only [List.mem_append,List.mem_range'_1]
    omega
  · intro w hw
    apply hv.1 w
    simp only [ipxScratch,List.mem_range'_1] at hw
    simp only [List.mem_append,List.mem_range'_1]
    omega
  · exact hv.1 4 (by simp)

theorem ipxFlags_clean (s : BasisState) (hv : Secp256k1ZeroAllowedInputValid s) (k : Fin 4) :
    s (ipxFlag k) = false := by
  apply hv.1
  have hk := ipxFlag_lt k
  simp only [List.mem_append,List.mem_range'_1]
  (try dsimp only [Wire] at *)
  omega

/-- Every wire outside the accumulator and the four flags is restored. -/
theorem ipxState_frame (Q : Point) (win : OddWindow) (s : BasisState)
    (hs : IpxInv pointLookupPath s) (w : Wire) (hw : w ∉ pointLogicalWires) (hf : ∀ k, w ≠ ipxFlag k) :
    ipxState Q win s w = s w :=
  (ipxUnitary_model coefficientAt Q (batchWindowRows win) batchWindowTree pointLookupPath
    ipxGeometry_window ipxSchedule s hs).2.2 w hw hf

theorem ipxState_inv (Q : Point) (win : OddWindow) (s : BasisState) (hs : IpxInv pointLookupPath s) :
    IpxInv pointLookupPath (ipxState Q win s) :=
  (ipxUnitary_model coefficientAt Q (batchWindowRows win) batchWindowTree pointLookupPath
    ipxGeometry_window ipxSchedule s hs).2.1

/-- On every reachable state the correction block writes `P + C` into the accumulator and
restores every other wire. -/
theorem ipxState_pointWrite (Q : Point) (w : OddWindow) (st : BasisState)
    (hv : Secp256k1ZeroAllowedInputValid st) (hq : st 836 = true)
    {x y : Fp} (hC : curve.toAffine.Nonsingular x y)
    (hr : constantPoint Q (coefficientAt (batchWindowRows w (batchWindowTree.routeLabel st))) = .some hC)
    (hord : order • (.some hC : Point) = 0)
    (P : Point) (hdata : pointStateCoordinates st = fig14EncodedEquiv x y (fig14PointEncoding P)) :
    ipxState Q w st = pointWrite (P + .some hC) st := by
  have hinv := ipxInv_of_valid st hv hq
  have hm := ipxUnitary_model coefficientAt Q (batchWindowRows w) batchWindowTree pointLookupPath
    ipxGeometry_window ipxSchedule st hinv
  have hA : st ∘ accumulatorPort = coordinateWordBits (fig14EncodedEquiv x y (fig14PointEncoding P)) :=
    (accumulatorPort_coordinates st hv).trans (congrArg coordinateWordBits hdata)
  have hF : (fun k => st (ipxFlag k)) = fun _ => false := funext (ipxFlags_clean st hv)
  have hres := hm.1
  rw [hA,hF] at hres
  change _ = ipxModel _ _ at hres
  rw [ipxModel_point coefficientAt Q _ hC hr hord P] at hres
  have hacc := congrArg Prod.fst hres
  have hfl := congrArg Prod.snd hres
  dsimp only at hacc hfl
  apply accumulator_word_frame_ext
  · exact (accumulatorPort_encoding_iff _ _).mp hacc
  · intro v hv'
    by_cases hk : ∃ k, v = ipxFlag k
    · obtain ⟨k,rfl⟩ := hk
      exact (congrFun hfl k).trans (ipxFlags_clean st hv k).symm
    · push_neg at hk
      exact hm.2.2 v hv' hk

end ShorECDLP.Paper2607_13816.ChallengeMigration

-- ==== part: IpxWindow ====

/-! # Windows and outer plan with the in-place XOR correction

Adapted from `ShorECDLP/Submission/2607_13816/Challenge/WindowBody.lean` (VerifiedQC/ShorECDLP,
branch `streaming-dev`, PR #551, Apache-2.0; see the repository LICENSE and NOTICE). The window
body is unchanged except that the five-word correction block `placedBatchProgram` is replaced by
`ipxProgram`, which lives entirely in the core allocation, so the round reset list is the core
`resetWires` (854 wires) instead of `batchedResetWires` (3931 wires). -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
attribute [local irreducible] sharedCoordinateProgram yNegateProgram ipxProgram

/-- Internal additions only; address preparation and Fourier are outside this list. -/
def ipxWindowSegments (w : OddWindow) : List (FixedSegment 983040) :=
  [sharedCoordinateProgram w, sharedYNegateProgram w, ipxProgram w, sharedYNegateProgram w]

noncomputable def ipxWindowSources (Q : Point) (w : OddWindow) : List AdaptiveCircuit :=
  [signedLookupCoordinateProgram (fun l => fieldValue (windowPoint Q w l) .x)
    (fun l => fieldValue (windowPoint Q w l) .y),windowYNegate,ipxSource Q w,windowYNegate]

def ipxWindowCore (w : OddWindow) (start : Nat) :
    (count : Nat) × Straight 983040 start (start+count) :=
  sequenceProgram 983040 (ipxWindowSegments w) start

theorem ipxWindowCore_run (w : OddWindow) (start : Nat) (Q : Point) (hQ : order • Q = 0)
    (history : Fin start → Bool) :
    compiledRun (ipxWindowCore w start) (readConstant coefficientAt Q) history =
      (sequenceCircuit (ipxWindowSources Q w)).run := by
  apply sequenceProgram_run
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ .nil)))
  · intro cursor h; exact sharedCoordinateProgram_run w cursor Q hQ h
  · intro cursor h; exact sharedYNegateProgram_run w cursor _ h
  · intro cursor h; exact ipxProgram_run w cursor Q h
  · intro cursor h; exact sharedYNegateProgram_run w cursor _ h

attribute [local irreducible] ipxWindowCore

def ipxWindowPrepared (w : OddWindow) (start : Nat) :
    (count : Nat) × Straight 983040 start (start+count) :=
  surroundCompiled (signedAddressCircuit 836 854 pointLookupAddress)
    (signedAddressCircuit 836 854 pointLookupAddress) (ipxWindowCore w start)

noncomputable def ipxWindowPreparedSource (Q : Point) (w : OddWindow) : AdaptiveCircuit :=
  (AdaptiveCircuit.unitary (signedAddressCircuit 836 854 pointLookupAddress) .done).seq
    ((sequenceCircuit (ipxWindowSources Q w)).seq
      (AdaptiveCircuit.unitary (signedAddressCircuit 836 854 pointLookupAddress) .done))

theorem ipxWindowPrepared_run (w : OddWindow) (start : Nat) (Q : Point) (hQ : order • Q = 0)
    (history : Fin start → Bool) :
    compiledRun (ipxWindowPrepared w start) (readConstant coefficientAt Q) history =
      (ipxWindowPreparedSource Q w).run := by
  exact surroundCompiled_run _ _ _ _ _ _ (ipxWindowCore_run w start Q hQ history)

/-- Address bank is relabeled to the reused 855–870 bank. -/
def actualIpxWindow (w : OddWindow) : OuterWindow 983040 :=
  closedWindow (relabelStraight (windowAddressPerm 855 (by decide)) (ipxWindowPrepared w 0).2)

theorem actualIpxWindow_run (w : OddWindow) (start : Nat) (Q : Point) (hQ : order • Q = 0)
    (history : Fin start → Bool) :
    (((actualIpxWindow w).program start).instantiate (readConstant coefficientAt Q) history).run =
      ((ipxWindowPreparedSource Q w).relabel (windowAddressPerm 855 (by decide))).run := by
  simp only [actualIpxWindow,closedWindow_run,relabelStraight_instantiate,AdaptiveCircuit.run_relabel]
  exact congrArg (List.map (InstrumentBranch.relabel (windowAddressPerm 855 (by decide))))
    (ipxWindowPrepared_run w 0 Q hQ Fin.elim0)

def ipxLeftWindows : List (OuterWindow 983040) :=
  actualFirstWindow :: List.ofFn (fun k : Fin 15 => actualIpxWindow (.left ⟨14-k.val,by omega⟩))
def ipxRightWindows : List (OuterWindow 983040) :=
  List.ofFn (fun k : Fin 13 => actualIpxWindow (.right ⟨12-k.val,by omega⟩))

theorem ipxLeftWindows_length : ipxLeftWindows.length = 16 := by simp [ipxLeftWindows]
theorem ipxRightWindows_length : ipxRightWindows.length = 13 := by simp [ipxRightWindows]

/-- The round resets exactly the core allocation; the correction needs no extra wire. -/
def ipxOuterPlan : OuterPlan 983040 :=
  standardOuterPlan ⟨ipxLeftWindows.toArray,by simp [ipxLeftWindows_length]⟩
    ⟨ipxRightWindows.toArray,by simp [ipxRightWindows_length]⟩ resetWires

end ShorECDLP.Paper2607_13816.ChallengeMigration
