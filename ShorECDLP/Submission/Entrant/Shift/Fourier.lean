import ShorECDLP.Submission.Naive.OrderFinding.Proofs.Probability
import ShorECDLP.Submission.Entrant.Shift.Kickback

/-! EDITABLE. Two-width copy of the Naive order-finding sampling argument
(register `a` has `pa` qubits, register `b` has `pb` qubits). -/

namespace ShorECDLP.Quantum.OrderFinding.Two

open ShorECDLP.Quantum.OrderFinding
open PhaseEstimation
open scoped BigOperators




noncomputable def orderFindingFourierState2
    {G : Type*} [AddCommGroup G]
    {w r d pa pb : ℕ} {σ : ℝ}
    (enc : PointEncoding G w)
    (P : G)
    (aReg bReg pointReg : List Wire)
    (s : BasisState) : State :=
  (((Real.sqrt r)⁻¹ : ℝ) : ℂ) •
    ∑ k : Fin r,
      ∑ a : Fin (2 ^ pa),
        ∑ b : Fin (2 ^ pb),
          (qpeAmplitude pa
              ((k.val : ℝ) / (r : ℝ)) a.val *
            qpeAmplitude pb
              ((((k.val * d) % r : ℕ) : ℝ) / (r : ℝ) + σ)
              b.val) •
            labelState bReg b.val
              (labelState aReg a.val
                (pointEigenstate enc P pointReg s k))

/-- The two-register order-finding circuit with a diagonal `shift` on `b`
inserted before the second inverse QFT. -/
noncomputable def orderFindingShift
    (aReg bReg : List Wire)
    (qftAncilla : Wire)
    (shift : Circuit)
    (oracle : State →ₗ[ℂ] State) :
    State →ₗ[ℂ] State :=
  (run (iqft bReg qftAncilla)).comp
    ((run shift).comp
      ((run (iqft aReg qftAncilla)).comp
        (oracle.comp
          (run (hadamards (aReg ++ bReg))))))

private noncomputable def phaseNorm (precision : ℕ) : ℂ :=
  (((Real.sqrt (2 ^ precision))⁻¹ : ℝ) : ℂ)

private noncomputable def orderFindingHadamardState2
    {G : Type*} [AddCommGroup G]
    {w r pa pb : ℕ}
    (enc : PointEncoding G w)
    (P : G)
    (aReg bReg pointReg : List Wire)
    (s : BasisState) : State :=
  (((Real.sqrt r)⁻¹ : ℝ) : ℂ) •
    ∑ k : Fin r,
      phaseNorm pa •
        ∑ a : Fin (2 ^ pa),
          phaseNorm pb •
            ∑ b : Fin (2 ^ pb),
              labelState bReg b.val
                (labelState aReg a.val
                  (pointEigenstate enc P pointReg s k))

private noncomputable def orderFindingKickedState2
    {G : Type*} [AddCommGroup G]
    {w r d pa pb : ℕ}
    (enc : PointEncoding G w)
    (P : G)
    (aReg bReg pointReg : List Wire)
    (s : BasisState) : State :=
  (((Real.sqrt r)⁻¹ : ℝ) : ℂ) •
    ∑ k : Fin r,
      phaseNorm pb •
        ∑ b : Fin (2 ^ pb),
          eigenvalue
              ((((k.val * d) % r : ℕ) : ℝ) / (r : ℝ)) ^ b.val •
            (phaseNorm pa •
              ∑ a : Fin (2 ^ pa),
                eigenvalue
                    ((k.val : ℝ) / (r : ℝ)) ^ a.val •
                  labelState aReg a.val
                    (labelState bReg b.val
                      (pointEigenstate enc P pointReg s k)))

private noncomputable def orderFindingAfterFirstIQFT2
    {G : Type*} [AddCommGroup G]
    {w r d pa pb : ℕ}
    (enc : PointEncoding G w)
    (P : G)
    (aReg bReg pointReg : List Wire)
    (s : BasisState) : State :=
  (((Real.sqrt r)⁻¹ : ℝ) : ℂ) •
    ∑ k : Fin r,
      ∑ a : Fin (2 ^ pa),
        qpeAmplitude pa
            ((k.val : ℝ) / (r : ℝ)) a.val •
          (phaseNorm pb •
            ∑ b : Fin (2 ^ pb),
              eigenvalue
                  ((((k.val * d) % r : ℕ) : ℝ) / (r : ℝ)) ^ b.val •
                labelState bReg b.val
                  (labelState aReg a.val
                    (pointEigenstate enc P pointReg s k)))

private noncomputable def orderFindingAfterShift2
    {G : Type*} [AddCommGroup G]
    {w r d pa pb : ℕ} {σ : ℝ}
    (enc : PointEncoding G w)
    (P : G)
    (aReg bReg pointReg : List Wire)
    (s : BasisState) : State :=
  (((Real.sqrt r)⁻¹ : ℝ) : ℂ) •
    ∑ k : Fin r,
      ∑ a : Fin (2 ^ pa),
        qpeAmplitude pa
            ((k.val : ℝ) / (r : ℝ)) a.val •
          (phaseNorm pb •
            ∑ b : Fin (2 ^ pb),
              eigenvalue
                  (((((k.val * d) % r : ℕ) : ℝ) / (r : ℝ)) + σ) ^ b.val •
                labelState bReg b.val
                  (labelState aReg a.val
                    (pointEigenstate enc P pointReg s k)))

private theorem ket_nonzero_eq
    (s t : BasisState)
    (h : ket s t ≠ 0) :
    t = s := by
  by_contra hne
  exact h (ket_ne (fun hst => hne hst.symm))

private theorem regValue_writeReg_disjoint'
    (r₁ r₂ : List Wire)
    (x : ℕ)
    (s : BasisState)
    (h : List.Disjoint r₁ r₂) :
    regValue r₁ (writeReg r₂ x s) =
      regValue r₁ s := by
  rw [writeReg_eq_setReg]
  induction r₁ with
  | nil => rfl
  | cons w ws ih =>
      have hw : w ∉ r₂ := by
        intro hw
        aesop
      have hws : List.Disjoint ws r₂ := by
        intro a ha b
        aesop
      rw [regValue_cons, regValue_cons]
      rw [setReg_not_mem r₂ x s hw]
      rw [ih hws]

private theorem sum_range_eq_sum_fin
    {α : Type*} [AddCommMonoid α]
    (N : ℕ)
    (f : ℕ → α) :
    (∑ y ∈ Finset.range N, f y) =
      ∑ y : Fin N, f y.val := by
  symm
  simp[Fin.sum_univ_eq_sum_range f]

private theorem triple_sum_reorder
    {ι κ L : Type*}
    [Fintype ι] [Fintype κ] [Fintype L]
    (f : ι → κ → L → State) :
    (∑ a : κ, ∑ b : L, ∑ k : ι, f k a b) =
      ∑ k : ι, ∑ a : κ, ∑ b : L, f k a b := by
  classical
  calc
    (∑ a : κ, ∑ b : L, ∑ k : ι, f k a b) =
        ∑ a : κ, ∑ k : ι, ∑ b : L, f k a b := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ k : ι, ∑ a : κ, ∑ b : L, f k a b := by
      rw [Finset.sum_comm]

private theorem scaled_triple_sum_reorder
    {ι κ L : Type*}
    [Fintype ι] [Fintype κ] [Fintype L]
    (c p q : ℂ)
    (f : ι → κ → L → State) :
    p •
        (∑ a : κ,
          q •
            (∑ b : L,
              c • ∑ k : ι, f k a b)) =
      c •
        (∑ k : ι,
          p •
            (∑ a : κ,
              q • ∑ b : L, f k a b)) := by
  classical
  have h :=
    triple_sum_reorder
      (fun k a b => (p * q * c) • f k a b)
  simpa only [
    Finset.smul_sum,
    smul_smul,
    mul_assoc,
    mul_comm,
    mul_left_comm
  ] using h

private theorem run_hadamards_pair_ket_zero2
    (aReg bReg : List Wire)
    (pa pb : ℕ)
    (s : BasisState)
    (haWidth : aReg.length = pa)
    (hbWidth : bReg.length = pb)
    (haZero : regValue aReg s = 0)
    (hbZero : regValue bReg s = 0)
    (haNodup : aReg.Nodup)
    (hbNodup : bReg.Nodup)
    (hab : List.Disjoint aReg bReg) :
    run (hadamards (aReg ++ bReg)) (ket s) =
      phaseNorm pa •
        ∑ a : Fin (2 ^ pa),
          phaseNorm pb •
            ∑ b : Fin (2 ^ pb),
              labelState bReg b.val
                (labelState aReg a.val (ket s)) := by
  classical

  have haClean :
      ∀ t, ket s t ≠ 0 → regValue aReg t = 0 := by
    intro t ht
    have hts := ket_nonzero_eq s t ht
    subst t
    exact haZero

  have hsplit :
      hadamards (aReg ++ bReg) =
        hadamards aReg ++ hadamards bReg := by
    simp [hadamards]

  rw [hsplit, run_append]

  have haRun :=
    run_hadamards_clean
      aReg (ket s) haClean haNodup

  rw [haWidth] at haRun

  have haRun' :
      run (hadamards aReg) (ket s) =
        phaseNorm pa •
          ∑ a : Fin (2 ^ pa),
            labelState aReg a.val (ket s) := by
    rw [haRun]
    unfold phaseNorm
    rw [sum_range_eq_sum_fin]

  rw [haRun']
  rw [map_smul, map_sum]

  apply congrArg
    (fun ψ : State => phaseNorm pa • ψ)

  apply Finset.sum_congr rfl
  intro a _

  have hbClean :
      ∀ t,
        labelState aReg a.val (ket s) t ≠ 0 →
          regValue bReg t = 0 := by
    intro t ht
    rw [labelState_ket] at ht
    have ht' :=
      ket_nonzero_eq
        (writeReg aReg a.val s) t ht
    subst t
    rw [regValue_writeReg_disjoint'
      bReg aReg a.val s hab.symm]
    exact hbZero

  have hbRun :=
    run_hadamards_clean
      bReg
      (labelState aReg a.val (ket s))
      hbClean hbNodup

  rw [hbWidth] at hbRun

  calc
    run (hadamards bReg)
        (labelState aReg a.val (ket s)) =
      (((Real.sqrt (2 ^ pb))⁻¹ : ℝ) : ℂ) •
        ∑ y ∈ Finset.range (2 ^ pb),
          labelState bReg y
            (labelState aReg a.val (ket s)) := hbRun
    _ =
      phaseNorm pb •
        ∑ b : Fin (2 ^ pb),
          labelState bReg b.val
            (labelState aReg a.val (ket s)) := by
      unfold phaseNorm
      rw [sum_range_eq_sum_fin]

private theorem labelPair_ket_eq_pointEigenstate_average2
    {G : Type*} [AddCommGroup G]
    {w r : ℕ}
    (enc : PointEncoding G w)
    (P : G)
    (aReg bReg pointReg : List Wire)
    (s : BasisState)
    (hr : Nat.Prime r)
    (horder : addOrderOf P = r)
    (hwidth : pointReg.length = w)
    (hnd : pointReg.Nodup)
    (hzero :
      regValue pointReg s = (enc.encode (0 : G)).val)
    (a b : ℕ) :
    labelState bReg b
        (labelState aReg a (ket s)) =
      (((Real.sqrt r)⁻¹ : ℝ) : ℂ) •
        ∑ k : Fin r,
          labelState bReg b
            (labelState aReg a
              (pointEigenstate enc P pointReg s k)) := by
  rw [ket_eq_pointEigenstate_average
    enc P pointReg s hr horder hwidth hnd hzero]
  simp only [map_smul, map_sum]

set_option maxHeartbeats 400000 in
theorem orderFinding_hadamard_step2
    {G : Type*} [AddCommGroup G]
    {w r d pa pb : ℕ}
    (enc : PointEncoding G w)
    (oracle : State →ₗ[ℂ] State)
    (P Q : G)
    (aReg bReg pointReg oracleWork : List Wire)
    (qftAncilla : Wire)
    (s : BasisState)
    (hsetting : ECDLPSetting P Q r d)
    (hspec :
      ECDLPOracleSpec enc oracle P Q
        aReg bReg pointReg oracleWork)
    (hsetup :
      Setup2 enc aReg bReg pointReg oracleWork qftAncilla pa pb s) :
    run (hadamards (aReg ++ bReg)) (ket s) =
      orderFindingHadamardState2
        (r := r) (pa := pa) (pb := pb)
        enc P aReg bReg pointReg s := by
  classical

  have hmainWork :=
    List.nodup_append.mp hspec.registers_nodup
  have habPoint :=
    List.nodup_append.mp hmainWork.1
  have habRegs :=
    List.nodup_append.mp habPoint.1

  have haNodup : aReg.Nodup :=
    habRegs.1

  have hbNodup : bReg.Nodup :=
    habRegs.2.1

  have hpNodup : pointReg.Nodup :=
    habPoint.2.1

  have hab : List.Disjoint aReg bReg := by
    intro x hx hy
    exact (habRegs.2.2 x hx x hy) rfl


  rw [run_hadamards_pair_ket_zero2
    aReg bReg pa pb s
    hsetup.a_width hsetup.b_width
    hsetup.a_zero hsetup.b_zero
    haNodup hbNodup hab]

  unfold orderFindingHadamardState2

  refine Eq.trans
    (b :=
      phaseNorm pa •
        ∑ a : Fin (2 ^ pa),
          phaseNorm pb •
            ∑ b : Fin (2 ^ pb),
              ((((Real.sqrt r)⁻¹ : ℝ) : ℂ)) •
                ∑ k : Fin r,
                  labelState bReg b.val
                    (labelState aReg a.val
                      (pointEigenstate enc P pointReg s k)))
    ?_ ?_
  · apply congrArg (fun ψ : State => phaseNorm pa • ψ)
    apply Finset.sum_congr rfl
    intro a _
    apply congrArg (fun ψ : State => phaseNorm pb • ψ)
    apply Finset.sum_congr rfl
    intro b _
    exact labelPair_ket_eq_pointEigenstate_average2
      enc P aReg bReg pointReg s
      hsetting.prime_order
      hsetting.order_P
      hspec.point_width
      hpNodup
      hsetup.point_zero
      a.val b.val
  · exact
      scaled_triple_sum_reorder
        (ι := Fin r)
        (κ := Fin (2 ^ pa))
        (L := Fin (2 ^ pb))
        ((((Real.sqrt r)⁻¹ : ℝ) : ℂ))
        (phaseNorm pa) (phaseNorm pb)
        (fun k a b =>
          labelState bReg b.val
            (labelState aReg a.val
              (pointEigenstate enc P pointReg s k)))

private theorem oracle_character_block2
    {G : Type*} [AddCommGroup G]
    {w r d pa pb : ℕ}
    (enc : PointEncoding G w)
    (oracle : State →ₗ[ℂ] State)
    (P Q : G)
    (aReg bReg pointReg oracleWork : List Wire)
    (qftAncilla : Wire)
    (s : BasisState)
    (hsetting : ECDLPSetting P Q r d)
    (hspec :
      ECDLPOracleSpec enc oracle P Q
        aReg bReg pointReg oracleWork)
    (hsetup :
      Setup2 enc aReg bReg pointReg oracleWork qftAncilla pa pb s)
    (hab : List.Disjoint aReg bReg)
    (hap : List.Disjoint aReg pointReg)
    (hbp : List.Disjoint bReg pointReg)
    (k : Fin r) :
    oracle
        (phaseNorm pa •
          ∑ a : Fin (2 ^ pa),
            phaseNorm pb •
              ∑ b : Fin (2 ^ pb),
                labelState bReg b.val
                  (labelState aReg a.val
                    (pointEigenstate enc P pointReg s k))) =
      phaseNorm pb •
        ∑ b : Fin (2 ^ pb),
          eigenvalue
              ((((k.val * d) % r : ℕ) : ℝ) / (r : ℝ)) ^ b.val •
            (phaseNorm pa •
              ∑ a : Fin (2 ^ pa),
                eigenvalue
                    ((k.val : ℝ) / (r : ℝ)) ^ a.val •
                  labelState aReg a.val
                    (labelState bReg b.val
                      (pointEigenstate enc P pointReg s k))) := by
  classical
  simp only [map_smul, map_sum]
  simp_rw [oracle_pointEigenstate_kickback2
    enc oracle P Q
    aReg bReg pointReg oracleWork
    qftAncilla s hsetting hspec hsetup]
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  rw [labelState_pointEigenstate_comm
    enc P aReg bReg pointReg s
    a.val b.val k hab hap hbp]
  congr 1
  ring

theorem orderFinding_oracle_step2
    {G : Type*} [AddCommGroup G]
    {w r d pa pb : ℕ}
    (enc : PointEncoding G w)
    (oracle : State →ₗ[ℂ] State)
    (P Q : G)
    (aReg bReg pointReg oracleWork : List Wire)
    (qftAncilla : Wire)
    (s : BasisState)
    (hsetting : ECDLPSetting P Q r d)
    (hspec :
      ECDLPOracleSpec enc oracle P Q
        aReg bReg pointReg oracleWork)
    (hsetup :
      Setup2 enc aReg bReg pointReg oracleWork qftAncilla pa pb s) :
    oracle
        (orderFindingHadamardState2
          (r := r) (pa := pa) (pb := pb)
          enc P aReg bReg pointReg s) =
      orderFindingKickedState2
        (r := r) (d := d) (pa := pa) (pb := pb)
        enc P aReg bReg pointReg s := by
  classical

  have hmainWork :=
    List.nodup_append.mp hspec.registers_nodup
  have habPoint :=
    List.nodup_append.mp hmainWork.1
  have habRegs :=
    List.nodup_append.mp habPoint.1

  have hab : List.Disjoint aReg bReg := by
    intro x hx hy
    exact (habRegs.2.2 x hx x hy) rfl

  have hap : List.Disjoint aReg pointReg := by
    intro x hx hy
    exact (habPoint.2.2 x (by simp [hx]) x hy) rfl

  have hbp : List.Disjoint bReg pointReg := by
    intro x hx hy
    exact (habPoint.2.2 x (by simp [hx]) x hy) rfl

  unfold orderFindingHadamardState2
  unfold orderFindingKickedState2

  rw [map_smul, map_sum]

  apply congrArg
    (fun ψ : State =>
      (((Real.sqrt r)⁻¹ : ℝ) : ℂ) • ψ)

  apply Finset.sum_congr rfl
  intro k _

  exact oracle_character_block2
    enc oracle P Q
    aReg bReg pointReg oracleWork
    qftAncilla s
    hsetting hspec hsetup
    hab hap hbp k

private theorem writeReg_not_mem_iqft
    (r : List Wire) (y : Nat) (s : BasisState)
    {q : Wire} (hq : q ∉ r) :
    writeReg r y s q = s q := by
  induction r generalizing y s with
  | nil => rfl
  | cons w ws ih =>
      simp only [List.mem_cons, not_or] at hq
      simp only [writeReg]
      rw [ih (y := y / 2) (s := s[w ↦ y.testBit 0]) hq.2]
      exact upd_other s w _ hq.1

private theorem labelState_eq_mapDomain_iqft
    (reg : List Wire) (value : Nat) (ψ : State) :
    labelState reg value ψ =
      Finsupp.mapDomain (writeReg reg value) ψ := by
  classical
  unfold labelState
  rw [Finsupp.linearCombination_apply]
  unfold Finsupp.mapDomain
  apply Finsupp.sum_congr
  intro s _
  simp [ket]

private def AncillaZero
    (q : Wire) (ψ : State) : Prop :=
  ∀ t, ψ t ≠ 0 → t q = false

private theorem ancillaZero_smul
    (q : Wire) (c : ℂ) (ψ : State)
    (hψ : AncillaZero q ψ) :
    AncillaZero q (c • ψ) := by
  intro t ht
  apply hψ t
  intro hz
  apply ht
  simp [hz]

private theorem ancillaZero_sum
    {ι : Type*} [Fintype ι]
    (q : Wire)
    (f : ι → State)
    (hf : ∀ i, AncillaZero q (f i)) :
    AncillaZero q (∑ i, f i) := by
  classical
  intro t ht
  by_contra hq
  have hz : ∀ i, f i t = 0 := by
    intro i
    by_contra hi
    exact hq (hf i t hi)
  apply ht
  simp [Finset.sum_apply, hz]

private theorem ancillaZero_ket_writeReg
    (q : Wire)
    (reg : List Wire)
    (value : Nat)
    (s : BasisState)
    (hq : q ∉ reg)
    (hs : s q = false) :
    AncillaZero q (ket (writeReg reg value s)) := by
  intro t ht
  have hts : t = writeReg reg value s := by
    by_contra hne
    have hne' : writeReg reg value s ≠ t := Ne.symm hne
    apply ht
    simp [ket, hne']
  subst t
  rw [writeReg_not_mem_iqft reg value s hq]
  exact hs

private theorem ancillaZero_pointEigenstate
    {G : Type*} [AddCommGroup G]
    {w r : ℕ}
    (enc : PointEncoding G w)
    (P : G)
    (pointReg : List Wire)
    (q : Wire)
    (s : BasisState)
    (k : Fin r)
    (hq : q ∉ pointReg)
    (hs : s q = false) :
    AncillaZero q
      (pointEigenstate enc P pointReg s k) := by
  unfold pointEigenstate
  apply ancillaZero_smul
  apply ancillaZero_sum
  intro j
  apply ancillaZero_smul
  exact ancillaZero_ket_writeReg
    q pointReg (enc.encode (j.val • P)).val s hq hs

private theorem ancillaZero_labelState
    (q : Wire)
    (reg : List Wire)
    (value : Nat)
    (ψ : State)
    (hq : q ∉ reg)
    (hψ : AncillaZero q ψ) :
    AncillaZero q (labelState reg value ψ) := by
  classical
  intro t ht
  have htmem :
      t ∈
        (Finsupp.mapDomain
          (writeReg reg value) ψ).support := by
    rw [← labelState_eq_mapDomain_iqft]
    exact Finsupp.mem_support_iff.mpr ht
  have htimg :
      t ∈ Finset.image (writeReg reg value) ψ.support :=
    Finsupp.mapDomain_support htmem
  rcases Finset.mem_image.mp htimg with ⟨u, hu, rfl⟩
  rw [writeReg_not_mem_iqft reg value u hq]
  exact hψ u (Finsupp.mem_support_iff.mp hu)

private theorem weighted_sum_swap_iqft
    {α β : Type*}
    [Fintype α] [Fintype β]
    (p : ℂ)
    (a : α → ℂ)
    (b : β → ℂ)
    (v : α → β → State) :
    p •
        ∑ j : β,
          b j • ∑ i : α, a i • v i j =
      ∑ i : α,
        a i •
          (p • ∑ j : β, b j • v i j) := by
  classical
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  ring

theorem first_iqft_character_block2
    {G : Type*} [AddCommGroup G]
    {w r d pa pb : ℕ}
    (enc : PointEncoding G w)
    (P : G)
    (aReg bReg pointReg : List Wire)
    (qftAncilla : Wire)
    (s : BasisState)
    (k : Fin r)
    (haWidth : aReg.length = pa)
    (haNodup : aReg.Nodup)
    (hancillaA : qftAncilla ∉ aReg)
    (hancillaB : qftAncilla ∉ bReg)
    (hancillaPoint : qftAncilla ∉ pointReg)
    (hancillaZero : s qftAncilla = false)
    (hab : List.Disjoint aReg bReg)
    (hap : List.Disjoint aReg pointReg)
    (hbp : List.Disjoint bReg pointReg) :
    run (iqft aReg qftAncilla)
        (phaseNorm pb •
          ∑ b : Fin (2 ^ pb),
            eigenvalue
                ((((k.val * d) % r : ℕ) : ℝ) / (r : ℝ)) ^ b.val •
              (phaseNorm pa •
                ∑ a : Fin (2 ^ pa),
                  eigenvalue
                      ((k.val : ℝ) / (r : ℝ)) ^ a.val •
                    labelState aReg a.val
                      (labelState bReg b.val
                        (pointEigenstate enc P pointReg s k)))) =
      ∑ a : Fin (2 ^ pa),
        qpeAmplitude pa
            ((k.val : ℝ) / (r : ℝ)) a.val •
          (phaseNorm pb •
            ∑ b : Fin (2 ^ pb),
              eigenvalue
                  ((((k.val * d) % r : ℕ) : ℝ) / (r : ℝ)) ^ b.val •
                labelState bReg b.val
                  (labelState aReg a.val
                    (pointEigenstate enc P pointReg s k))) := by
  classical

  let phaseA : ℝ := (k.val : ℝ) / (r : ℝ)
  let phaseB : ℝ :=
    (((k.val * d) % r : ℕ) : ℝ) / (r : ℝ)

  let χ : State :=
    pointEigenstate enc P pointReg s k

  have hχAnc :
      AncillaZero qftAncilla χ := by
    exact ancillaZero_pointEigenstate
      enc P pointReg qftAncilla s k
      hancillaPoint hancillaZero

  have hψAnc :
      ∀ b : Fin (2 ^ pb),
        AncillaZero qftAncilla
          (labelState bReg b.val χ) := by
    intro b
    exact ancillaZero_labelState
      qftAncilla bReg b.val χ hancillaB hχAnc

  have hiqft :
      ∀ b : Fin (2 ^ pb),
        run (iqft aReg qftAncilla)
            (phaseNorm pa •
              ∑ a : Fin (2 ^ pa),
                eigenvalue phaseA ^ a.val •
                  labelState aReg a.val
                    (labelState bReg b.val χ)) =
          ∑ a : Fin (2 ^ pa),
            qpeAmplitude pa phaseA a.val •
              labelState aReg a.val
                (labelState bReg b.val χ) := by
    intro b

    have h :=
      run_iqft_kicked_phase_state
        aReg qftAncilla
        (labelState bReg b.val χ)
        phaseA
        (hψAnc b)
        hancillaA
        haNodup

    rw [haWidth] at h

    unfold phaseNorm
    rw [sum_range_eq_sum_fin] at h
    rw [sum_range_eq_sum_fin] at h
    simpa using h

  change
    run (iqft aReg qftAncilla)
        (phaseNorm pb •
          ∑ b : Fin (2 ^ pb),
            eigenvalue phaseB ^ b.val •
              (phaseNorm pa •
                ∑ a : Fin (2 ^ pa),
                  eigenvalue phaseA ^ a.val •
                    labelState aReg a.val
                      (labelState bReg b.val χ))) =
      ∑ a : Fin (2 ^ pa),
        qpeAmplitude pa phaseA a.val •
          (phaseNorm pb •
            ∑ b : Fin (2 ^ pb),
              eigenvalue phaseB ^ b.val •
                labelState bReg b.val
                  (labelState aReg a.val χ))

  rw [map_smul, map_sum]

  refine Eq.trans
    (b :=
      phaseNorm pb •
        ∑ b : Fin (2 ^ pb),
          eigenvalue phaseB ^ b.val •
            ∑ a : Fin (2 ^ pa),
              qpeAmplitude pa phaseA a.val •
                labelState aReg a.val
                  (labelState bReg b.val χ))
    ?_ ?_
  · apply congrArg
      (fun ψ : State => phaseNorm pb • ψ)
    apply Finset.sum_congr rfl
    intro b _
    rw [map_smul, hiqft b]

  · rw [weighted_sum_swap_iqft
      (α := Fin (2 ^ pa))
      (β := Fin (2 ^ pb))
      (phaseNorm pb)
      (fun a : Fin (2 ^ pa) =>
        qpeAmplitude pa phaseA a.val)
      (fun b : Fin (2 ^ pb) =>
        eigenvalue phaseB ^ b.val)
      (fun a b =>
        labelState aReg a.val
          (labelState bReg b.val χ))]

    apply Finset.sum_congr rfl
    intro a _

    apply congrArg
      (fun ψ : State =>
        qpeAmplitude pa phaseA a.val • ψ)

    apply congrArg
      (fun ψ : State => phaseNorm pb • ψ)

    apply Finset.sum_congr rfl
    intro b _

    apply congrArg
      (fun ψ : State =>
        eigenvalue phaseB ^ b.val • ψ)

    dsimp [χ]
    exact (labelState_pointEigenstate_comm
      enc P aReg bReg pointReg s
      a.val b.val k
      hab hap hbp).symm

theorem orderFinding_first_iqft_step2
    {G : Type*} [AddCommGroup G]
    {w r d pa pb : ℕ}
    (enc : PointEncoding G w)
    (oracle : State →ₗ[ℂ] State)
    (P Q : G)
    (aReg bReg pointReg oracleWork : List Wire)
    (qftAncilla : Wire)
    (s : BasisState)
    (_hsetting : ECDLPSetting P Q r d)
    (hspec :
      ECDLPOracleSpec enc oracle P Q
        aReg bReg pointReg oracleWork)
    (hsetup :
      Setup2 enc aReg bReg pointReg oracleWork qftAncilla pa pb s) :
    run (iqft aReg qftAncilla)
        (orderFindingKickedState2
          (r := r) (d := d) (pa := pa) (pb := pb)
          enc P aReg bReg pointReg s) =
      orderFindingAfterFirstIQFT2
        (r := r) (d := d) (pa := pa) (pb := pb)
        enc P aReg bReg pointReg s := by
  classical

  have hmainWork :=
    List.nodup_append.mp hspec.registers_nodup
  have habPoint :=
    List.nodup_append.mp hmainWork.1
  have habRegs :=
    List.nodup_append.mp habPoint.1

  have haNodup : aReg.Nodup :=
    habRegs.1

  have hab : List.Disjoint aReg bReg := by
    intro x hx hy
    exact (habRegs.2.2 x hx x hy) rfl

  have hap : List.Disjoint aReg pointReg := by
    intro x hx hy
    exact (habPoint.2.2 x (by simp [hx]) x hy) rfl

  have hbp : List.Disjoint bReg pointReg := by
    intro x hx hy
    exact (habPoint.2.2 x (by simp [hx]) x hy) rfl

  have hancillaA : qftAncilla ∉ aReg := by
    intro h
    exact hsetup.ancilla_fresh (by simp [h])

  have hancillaB : qftAncilla ∉ bReg := by
    intro h
    exact hsetup.ancilla_fresh (by simp [h])

  have hancillaPoint : qftAncilla ∉ pointReg := by
    intro h
    exact hsetup.ancilla_fresh (by simp [h])

  unfold orderFindingKickedState2
  unfold orderFindingAfterFirstIQFT2

  rw [map_smul, map_sum]

  apply congrArg
    (fun ψ : State =>
      (((Real.sqrt r)⁻¹ : ℝ) : ℂ) • ψ)

  apply Finset.sum_congr rfl
  intro k _

  exact first_iqft_character_block2
    enc P
    aReg bReg pointReg
    qftAncilla s k
    hsetup.a_width
    haNodup
    hancillaA
    hancillaB
    hancillaPoint
    hsetup.ancilla_zero
    hab hap hbp

private theorem run_iqft_kicked_phase_state_fin
    (phaseReg : List Wire)
    (qftAncilla : Wire)
    (ψ : State)
    (precision : ℕ)
    (phase : ℝ)
    (hwidth : phaseReg.length = precision)
    (hancillaZero : AncillaZero qftAncilla ψ)
    (hancilla : qftAncilla ∉ phaseReg)
    (hnd : phaseReg.Nodup) :
    run (iqft phaseReg qftAncilla)
        (phaseNorm precision •
          ∑ y : Fin (2 ^ precision),
            eigenvalue phase ^ y.val •
              labelState phaseReg y.val ψ) =
      ∑ z : Fin (2 ^ precision),
        qpeAmplitude precision phase z.val •
          labelState phaseReg z.val ψ := by
  have h :=
    run_iqft_kicked_phase_state
      phaseReg qftAncilla ψ phase
      hancillaZero hancilla hnd
  rw [hwidth] at h
  simpa only [phaseNorm, sum_range_eq_sum_fin] using h

private theorem second_iqft_character_block2
    {G : Type*} [AddCommGroup G]
    {w r d pa pb : ℕ} {σ : ℝ}
    (enc : PointEncoding G w)
    (P : G)
    (aReg bReg pointReg : List Wire)
    (qftAncilla : Wire)
    (s : BasisState)
    (k : Fin r)
    (a : Fin (2 ^ pa))
    (hbWidth : bReg.length = pb)
    (hbNodup : bReg.Nodup)
    (hancillaA : qftAncilla ∉ aReg)
    (hancillaB : qftAncilla ∉ bReg)
    (hancillaPoint : qftAncilla ∉ pointReg)
    (hancillaZero : s qftAncilla = false) :
    run (iqft bReg qftAncilla)
        (phaseNorm pb •
          ∑ b : Fin (2 ^ pb),
            eigenvalue
                (((((k.val * d) % r : ℕ) : ℝ) / (r : ℝ)) + σ) ^ b.val •
              labelState bReg b.val
                (labelState aReg a.val
                  (pointEigenstate enc P pointReg s k))) =
      ∑ b : Fin (2 ^ pb),
        qpeAmplitude pb
            (((((k.val * d) % r : ℕ) : ℝ) / (r : ℝ)) + σ) b.val •
          labelState bReg b.val
            (labelState aReg a.val
              (pointEigenstate enc P pointReg s k)) := by
  let χ := pointEigenstate enc P pointReg s k
  let ψ := labelState aReg a.val χ

  have hχ :
      AncillaZero qftAncilla χ := by
    exact ancillaZero_pointEigenstate
      enc P pointReg qftAncilla s k
      hancillaPoint hancillaZero

  have hψ :
      AncillaZero qftAncilla ψ := by
    exact ancillaZero_labelState
      qftAncilla aReg a.val χ hancillaA hχ

  exact run_iqft_kicked_phase_state_fin
    bReg qftAncilla ψ pb
    (((((k.val * d) % r : ℕ) : ℝ) / (r : ℝ)) + σ)
    hbWidth hψ hancillaB hbNodup

theorem orderFinding_second_iqft_step2
    {G : Type*} [AddCommGroup G]
    {w r d pa pb : ℕ} {σ : ℝ}
    (enc : PointEncoding G w)
    (oracle : State →ₗ[ℂ] State)
    (P Q : G)
    (aReg bReg pointReg oracleWork : List Wire)
    (qftAncilla : Wire)
    (s : BasisState)
    (_hsetting : ECDLPSetting P Q r d)
    (hspec :
      ECDLPOracleSpec enc oracle P Q
        aReg bReg pointReg oracleWork)
    (hsetup :
      Setup2 enc aReg bReg pointReg oracleWork qftAncilla pa pb s) :
    run (iqft bReg qftAncilla)
        (orderFindingAfterShift2
          (r := r) (d := d) (pa := pa) (pb := pb) (σ := σ)
          enc P aReg bReg pointReg s) =
      orderFindingFourierState2
        (r := r) (d := d) (pa := pa) (pb := pb) (σ := σ)
        enc P aReg bReg pointReg s := by
  classical

  have hmainWork :=
    List.nodup_append.mp hspec.registers_nodup
  have habPoint :=
    List.nodup_append.mp hmainWork.1
  have habRegs :=
    List.nodup_append.mp habPoint.1

  have hbNodup : bReg.Nodup :=
    habRegs.2.1

  have hancillaA : qftAncilla ∉ aReg := by
    intro h
    exact hsetup.ancilla_fresh (by simp [h])

  have hancillaB : qftAncilla ∉ bReg := by
    intro h
    exact hsetup.ancilla_fresh (by simp [h])

  have hancillaPoint : qftAncilla ∉ pointReg := by
    intro h
    exact hsetup.ancilla_fresh (by simp [h])

  unfold orderFindingAfterShift2
  unfold orderFindingFourierState2

  rw [map_smul, map_sum]

  apply congrArg
    (fun ψ : State =>
      (((Real.sqrt r)⁻¹ : ℝ) : ℂ) • ψ)

  apply Finset.sum_congr rfl
  intro k _

  rw [map_sum]

  apply Finset.sum_congr rfl
  intro a _

  rw [map_smul]

  rw [second_iqft_character_block2
    enc P aReg bReg pointReg
    qftAncilla s k a
    hsetup.b_width
    hbNodup
    hancillaA
    hancillaB
    hancillaPoint
    hsetup.ancilla_zero]

  rw [Finset.smul_sum]

  apply Finset.sum_congr rfl
  intro b _

  rw [smul_smul]

private theorem eigenvalue_add_shift (x y : ℝ) :
    eigenvalue (x + y) = eigenvalue x * eigenvalue y := by
  unfold eigenvalue
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem orderFinding_shift_step2
    {G : Type*} [AddCommGroup G]
    {w r d pa pb : ℕ} {σ : ℝ}
    (enc : PointEncoding G w)
    (P : G)
    (aReg bReg pointReg : List Wire)
    (s : BasisState)
    (shift : Circuit)
    (hshift : ∀ (v : Fin (2 ^ pb)) (ψ : State),
      run shift (labelState bReg v.val ψ) = eigenvalue σ ^ v.val • labelState bReg v.val ψ) :
    run shift
        (orderFindingAfterFirstIQFT2
          (r := r) (d := d) (pa := pa) (pb := pb)
          enc P aReg bReg pointReg s) =
      orderFindingAfterShift2
        (r := r) (d := d) (pa := pa) (pb := pb) (σ := σ)
        enc P aReg bReg pointReg s := by
  unfold orderFindingAfterFirstIQFT2 orderFindingAfterShift2
  simp only [map_smul, map_sum, hshift, smul_smul, eigenvalue_add_shift, mul_pow]

theorem orderFinding_eq_fourierState2
    {G : Type*} [AddCommGroup G]
    {w r d pa pb : ℕ} {σ : ℝ}
    (enc : PointEncoding G w)
    (oracle : State →ₗ[ℂ] State)
    (P Q : G)
    (aReg bReg pointReg oracleWork : List Wire)
    (qftAncilla : Wire)
    (s : BasisState)
    (shift : Circuit)
    (hshift : ∀ (v : Fin (2 ^ pb)) (ψ : State),
      run shift (labelState bReg v.val ψ) = eigenvalue σ ^ v.val • labelState bReg v.val ψ)
    (hsetting : ECDLPSetting P Q r d)
    (hspec :
      ECDLPOracleSpec enc oracle P Q
        aReg bReg pointReg oracleWork)
    (hsetup :
      Setup2 enc aReg bReg pointReg oracleWork qftAncilla pa pb s) :
    orderFindingShift aReg bReg qftAncilla shift oracle (ket s) =
      orderFindingFourierState2
        (r := r) (d := d) (pa := pa) (pb := pb) (σ := σ)
        enc P aReg bReg pointReg s := by
  change
    run (iqft bReg qftAncilla)
      (run shift
        (run (iqft aReg qftAncilla)
          (oracle
            (run (hadamards (aReg ++ bReg)) (ket s))))) =
      orderFindingFourierState2
        (r := r) (d := d) (pa := pa) (pb := pb) (σ := σ)
        enc P aReg bReg pointReg s
  rw [orderFinding_hadamard_step2
    enc oracle P Q aReg bReg pointReg oracleWork
    qftAncilla s hsetting hspec hsetup]
  rw [orderFinding_oracle_step2
    enc oracle P Q aReg bReg pointReg oracleWork
    qftAncilla s hsetting hspec hsetup]
  rw [orderFinding_first_iqft_step2
    enc oracle P Q aReg bReg pointReg oracleWork
    qftAncilla s hsetting hspec hsetup]
  rw [orderFinding_shift_step2 enc P aReg bReg pointReg s shift hshift]
  exact orderFinding_second_iqft_step2
    enc oracle P Q aReg bReg pointReg oracleWork
    qftAncilla s hsetting hspec hsetup

end ShorECDLP.Quantum.OrderFinding.Two
