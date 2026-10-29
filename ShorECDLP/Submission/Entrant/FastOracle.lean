import ShorECDLP.Submission.Entrant.FastAdd
import ShorECDLP.Submission.Naive.EllipticCurve.ECDLPOracle

/-! EDITABLE. ECDLP oracle built from `fastCPA`.

Each `fastCPA` agrees with the Naive `controlledPointAdd` on every basis state whose
point register holds a valid encoding and whose workspace is clean, and both preserve
that set of states.  The Naive classical correctness theorem then transfers to the new
circuit, which gives the oracle specification used by order finding. -/

namespace ShorECDLP
namespace Secp256k1

open Classical
open Arithmetic

variable [Fact (Nat.Prime p)]

def fastCore (pointReg : List Wire) (workStart : Wire) : List Wire → List Point → Circuit
  | control :: controls, C :: Cs =>
      fastCPA control pointReg workStart C ++ fastCore pointReg workStart controls Cs
  | _, _ => []

def fastOracle (aReg bReg pointReg : List Wire) (workStart : Wire) (P Q : Point) : Circuit :=
  fastCore pointReg workStart aReg (scalarMulTable aReg P) ++
    fastCore pointReg workStart bReg (scalarMulTable bReg Q)

omit [Fact (Nat.Prime p)] in
theorem writeReg_clean_other (ws vs : List Wire) (n : Nat) (s : BasisState)
    (h : Clean vs s) (hd : ∀ w ∈ vs, w ∉ ws) : Clean vs (writeReg ws n s) := by
  intro w hw
  rw [writeReg_not_mem' _ _ _ _ (hd w hw), h w hw]

theorem fastCore_agree (pointReg : List Wire) (workStart : Wire) :
    ∀ (controls : List Wire) (points : List Point) (R : Point) (st : BasisState),
      (∀ C ∈ points, C ≠ 0) →
      pointReg.length = pointWidth →
      (controls ++ pointReg ++ scalarMulWork workStart).Nodup →
      regValue pointReg st = encodeNat R →
      Clean (scalarMulWork workStart) st →
      Classical.run (fastCore pointReg workStart controls points) st =
        Classical.run (scalarMulCore pointReg workStart controls points) st := by
  intro controls
  induction controls with
  | nil => intro points R st _ _ _ _ _; cases points <;> rfl
  | cons c cs ih =>
    intro points R st hne hlen hnd hpoint hclean
    cases points with
    | nil => rfl
    | cons C Cs =>
      have hnd1 : ([c] ++ pointReg ++ controlledPointAddWork workStart).Nodup := by
        exact List.Sublist.nodup (((List.cons_sublist_cons.mpr (List.nil_sublist cs)).append_right
          pointReg).append_right (scalarMulWork workStart)) hnd
      have hfast := fastCPA_correct c pointReg workStart C R (hne C List.mem_cons_self) st hlen
        hnd1 hpoint hclean
      have hold := controlledPointAdd_correct c pointReg workStart C R st hlen hnd1 hpoint hclean
      simp only [fastCore, scalarMulCore, Classical.run_append, hfast, hold]
      have hPnd : pointReg.Nodup := by
        have h := (List.nodup_append.mp hnd).1
        exact (List.nodup_append.mp h).2.1
      have hPW : ∀ w ∈ scalarMulWork workStart, w ∉ pointReg := by
        intro w hw hp
        have h := List.nodup_append.mp hnd
        exact h.2.2 w (List.mem_append_right _ hp) w hw rfl
      exact ih Cs _ _ (fun C hC => hne C (List.mem_cons_of_mem _ hC)) hlen
        (by
          rw [List.cons_append, List.cons_append] at hnd
          exact (List.nodup_cons.mp hnd).2)
        (PointRegister.regValue_write_encode pointReg _ st hlen hPnd)
        (writeReg_clean_other _ _ _ _ hclean hPW)

theorem fastOracle_agree (aReg bReg pointReg : List Wire) (workStart : Wire) (P Q R : Point)
    (st : BasisState) (hP : ∀ C ∈ scalarMulTable aReg P, C ≠ 0)
    (hQ : ∀ C ∈ scalarMulTable bReg Q, C ≠ 0)
    (hpointLength : pointReg.length = pointWidth)
    (hnodup : (aReg ++ bReg ++ pointReg ++ scalarMulWork workStart).Nodup)
    (hpoint : regValue pointReg st = encodeNat R)
    (hclean : Clean (scalarMulWork workStart) st) :
    Classical.run (fastOracle aReg bReg pointReg workStart P Q) st =
      Classical.run (ecdlpOracle aReg bReg pointReg workStart P Q) st := by
  have hsub (xs : List Wire) (hx : ∀ w ∈ xs, w ∈ aReg ++ bReg) :
      (xs ++ pointReg ++ scalarMulWork workStart).Nodup → True := fun _ => trivial
  have hA : (aReg ++ pointReg ++ scalarMulWork workStart).Nodup := by
    apply List.Sublist.nodup _ hnodup
    simp only [List.append_assoc]
    exact (List.sublist_append_left aReg bReg).append (List.Sublist.refl _) |>.trans
      (by simp [List.append_assoc])
  have hB : (bReg ++ pointReg ++ scalarMulWork workStart).Nodup := by
    apply List.Sublist.nodup _ hnodup
    simp only [List.append_assoc]
    exact (List.sublist_append_right aReg bReg).append (List.Sublist.refl _) |>.trans
      (by simp [List.append_assoc])
  have hPnd : pointReg.Nodup := (List.nodup_append.mp (List.nodup_append.mp hA).1).2.1
  have hPW : ∀ w ∈ scalarMulWork workStart, w ∉ pointReg := by
    intro w hw hp
    exact (List.nodup_append.mp hA).2.2 w (List.mem_append_right _ hp) w hw rfl
  simp only [fastOracle, ecdlpOracle, scalarMul, Classical.run_append]
  rw [fastCore_agree pointReg workStart aReg _ R st hP hpointLength hA hpoint hclean,
    scalarMulCore_correct aReg pointReg _ workStart R st hpointLength hA hpoint hclean]
  exact fastCore_agree pointReg workStart bReg _ _ _ hQ hpointLength hB
    (PointRegister.regValue_write_encode pointReg _ st hpointLength hPnd)
    (writeReg_clean_other _ _ _ _ hclean hPW)

omit [Fact (Nat.Prime p)] in
theorem fastCore_HPFree (pointReg : List Wire) (workStart : Wire) :
    ∀ (controls : List Wire) (points : List Point),
      HPFree (fastCore pointReg workStart controls points) := by
  intro controls
  induction controls with
  | nil => intro points; cases points <;> simp [fastCore]
  | cons c cs ih =>
    intro points
    cases points with
    | nil => simp [fastCore]
    | cons C Cs =>
      simp only [fastCore, hpFree_append]
      exact ⟨fastCPA_HPFree _ _ _ _, ih Cs⟩

omit [Fact (Nat.Prime p)] in
theorem fastCore_structural (pointReg : List Wire) (workStart : Wire) :
    ∀ (controls : List Wire) (points : List Point),
      (controls ++ pointReg ++ scalarMulWork workStart).Nodup →
      CircuitWellFormed (fastCore pointReg workStart controls points) ∧
        CircuitUsesOnly (controls ++ pointReg ++ scalarMulWork workStart)
          (fastCore pointReg workStart controls points) := by
  intro controls
  induction controls with
  | nil =>
    intro points _
    cases points <;> exact ⟨fun _ h => by simp [fastCore] at h, fun _ h => by simp [fastCore] at h⟩
  | cons c cs ih =>
    intro points hnd
    cases points with
    | nil => exact ⟨fun _ h => by simp [fastCore] at h, fun _ h => by simp [fastCore] at h⟩
    | cons C Cs =>
      have hnd1 : ([c] ++ pointReg ++ controlledPointAddWork workStart).Nodup := by
        exact List.Sublist.nodup (((List.cons_sublist_cons.mpr (List.nil_sublist cs)).append_right
          pointReg).append_right (scalarMulWork workStart)) hnd
      have hhead := fastCPA_structural c pointReg workStart C hnd1
      have htail := ih Cs (by
        rw [List.cons_append, List.cons_append] at hnd
        exact (List.nodup_cons.mp hnd).2)
      simp only [fastCore, circuitWellFormed_append]
      refine ⟨⟨hhead.1, htail.1⟩, usesOnly_append ?_ ?_⟩
      · apply usesOnly_mono hhead.2
        intro w hw
        simp only [List.mem_append, List.mem_cons, scalarMulWork] at hw ⊢
        tauto
      · apply usesOnly_mono htail.2
        intro w hw
        simp only [List.mem_append, List.mem_cons] at hw ⊢
        tauto

theorem fastOracle_spec (aReg bReg pointReg : List Wire) (workStart : Wire) (P Q : Point)
    (hP : ∀ C ∈ scalarMulTable aReg P, C ≠ 0) (hQ : ∀ C ∈ scalarMulTable bReg Q, C ≠ 0)
    (hpointLength : pointReg.length = pointWidth)
    (hnodup : (aReg ++ bReg ++ pointReg ++ scalarMulWork workStart).Nodup) :
    ECDLPOracleSpec pointEncoding
      (Quantum.run (fastOracle aReg bReg pointReg workStart P Q))
      P Q aReg bReg pointReg (scalarMulWork workStart) := by
  have hA : (aReg ++ pointReg ++ scalarMulWork workStart).Nodup := by
    apply List.Sublist.nodup _ hnodup
    simp only [List.append_assoc]
    exact (List.sublist_append_left aReg bReg).append (List.Sublist.refl _) |>.trans
      (by simp [List.append_assoc])
  have hB : (bReg ++ pointReg ++ scalarMulWork workStart).Nodup := by
    apply List.Sublist.nodup _ hnodup
    simp only [List.append_assoc]
    exact (List.sublist_append_right aReg bReg).append (List.Sublist.refl _) |>.trans
      (by simp [List.append_assoc])
  apply ECDLPOracleSpec.ofCircuit
  · exact hpointLength
  · exact hnodup
  · simp only [fastOracle, hpFree_append]
    exact ⟨fastCore_HPFree _ _ _ _, fastCore_HPFree _ _ _ _⟩
  · rw [fastOracle, circuitWellFormed_append]
    exact ⟨(fastCore_structural _ _ _ _ hA).1, (fastCore_structural _ _ _ _ hB).1⟩
  · intro st a b R ha hb hpoint hclean
    have hp : regValue pointReg st = encodeNat R := by
      simpa only [pointEncoding_encode_val] using hpoint
    rw [fastOracle_agree aReg bReg pointReg workStart P Q R st hP hQ hpointLength hnodup hp
      hclean]
    have h := ecdlpOracle_correct aReg bReg pointReg workStart P Q R st hpointLength hnodup hp
      hclean
    rw [ha, hb] at h
    simpa only [pointEncoding_encode_val, encode_val] using h

omit [Fact (Nat.Prime p)] in
/-- Nonzero entries of a doubling table for a point of prime order. -/
theorem doublingTable_ne_zero (n : Nat) (P : Point) (hP : P ≠ 0) (ho : order • P = 0) :
    ∀ C ∈ Precompute.doublingTable n P, C ≠ 0 := by
  intro C hC
  simp only [Precompute.doublingTable, List.mem_ofFn] at hC
  obtain ⟨i, rfl⟩ := hC
  intro hz
  have hord : addOrderOf P = order := by
    have hd : addOrderOf P ∣ order := addOrderOf_dvd_of_nsmul_eq_zero ho
    rcases (Nat.dvd_prime order_prime).mp hd with h | h
    · exact (hP (AddMonoid.addOrderOf_eq_one_iff.mp h)).elim
    · exact h
  have hdvd : order ∣ 2 ^ (i : Nat) := by
    rw [← hord]; exact addOrderOf_dvd_of_nsmul_eq_zero hz
  have h2 := Nat.Prime.dvd_of_dvd_pow order_prime hdvd
  have : order ≤ 2 := Nat.le_of_dvd (by norm_num) h2
  norm_num [order] at this

end Secp256k1
end ShorECDLP
