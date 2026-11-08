import ShorECDLP.Submission.Entrant.Schedule27

namespace ShorECDLP.Entrant.GeometricPhase
open Quantum Challenge Secp256k1 AndGadget WEXCredit WeightedPhase28 ApproximatePhase34
open Paper2607_13816 Paper2607_13816.ChallengeMigration Single Single.Distribution
noncomputable section
set_option Elab.async false
attribute [local irreducible] List.ofFn
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
theorem sharp_unit : unit = (6283186/1000000:ℝ)/2^28 := rfl
theorem charge_balance (dir : PhaseDir) (w : Wire) (k : Nat) :
    charge (.P dir k w) + potential (k+1) = potential k := by
  by_cases hk : 27 < k
  · have h1 : max 28 k = k := max_eq_right (by omega)
    have h2 : max 28 (k+1) = k+1 := max_eq_right (by omega)
    simp only [charge,hk,if_true,potential,h1,h2,pow_succ]
    have hp : (2:ℝ)^k ≠ 0 := by positivity
    field_simp
    <;> ring
  · have h1 : max 28 k = 28 := max_eq_left (by omega)
    have h2 : max 28 (k+1) = 28 := max_eq_left (by omega)
    simp [charge,hk,potential,h1,h2]


theorem error_feedback_balance {n s e} (dir : PhaseDir) (w : Wire) (indices : List (Fin s))
    (k : Nat) (p : Straight n s e) :
    errorCost (feedbackProgram dir w indices k p) + potential (k+indices.length) =
      potential k + errorCost p := by
  induction indices generalizing k with
  | nil => simp [feedbackProgram,add_comm]
  | cons i is ih =>
    have hi := ih (k+1)
    have hc := charge_balance dir w k
    have he : k + (i::is).length = (k+1)+is.length := by simp; omega
    simp only [feedbackProgram,errorCost,he]
    linarith

def account : Nat → Nat → ℝ
  | 0,_ => 0
  | n+1,p => unit - potential (p+2) + account n (p+1)

theorem account_append (a b p : Nat) :
    account (a+b) p = account a p + account b (p+a) := by
  induction a generalizing p with
  | zero => simp [account]
  | succ a ih =>
    rw [Nat.succ_add]
    simp only [account,ih]
    have he : p+(a+1) = (p+1)+a := by omega
    rw [he]
    ring

theorem error_fourier_exact (n : Nat) (dir : PhaseDir) (ws : List Wire)
    (start : Nat) (prior : List (Fin start)) :
    errorCost (fourierProgram n dir ws start prior) = account ws.length prior.length := by
  induction ws generalizing start with
  | nil => simp [fourierProgram,errorCost,account]
  | cons w ws ih =>
    simp only [fourierProgram,error_cast]
    have hi := ih (start+1) (Fin.last start :: prior.map Fin.castSucc)
    have hf := error_feedback_balance dir w prior 2 (.measure w
      (fourierProgram n dir ws (start+1) (Fin.last start :: prior.map Fin.castSucc)))
    have he : potential 2 = unit := by norm_num [potential,unit]
    simp only [errorCost,hi,he,List.length_cons,List.length_map] at hf hi
    rw [List.length_cons,account]
    have hn : 2+prior.length = prior.length+2 := by omega
    rw [hn] at hf
    linarith


theorem potential_half (k : Nat) (hk : 28 ≤ k) :
    2*potential (k+1) = potential k := by
  have h1 : max 28 k = k := max_eq_right hk
  have h2 : max 28 (k+1) = k+1 := max_eq_right (by omega)
  simp only [potential,h1,h2,pow_succ]
  ring

theorem account_geometric (n p : Nat) (hp : 26 ≤ p) :
    account n p + 2*potential (p+2) = (n:ℝ)*unit + 2*potential (p+n+2) := by
  induction n generalizing p with
  | zero => simp [account]
  | succ n ih =>
    have hi := ih (p+1) (by omega)
    have hh := potential_half (p+2) (by omega)
    have he : p+2+1 = p+1+2 := by omega
    rw [he] at hh
    have he2 : p+(n+1)+2 = (p+1)+n+2 := by omega
    simp only [account,Nat.cast_add,Nat.cast_one,he2]
    linarith

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
theorem joint_error : account 261 0 + account 208 0 ≤ (1653/4:ℝ)*unit := by
  have hz : account 26 0 = 0 := by norm_num [account,potential,unit]
  rw [show 261=26+235 from rfl, show 208=26+182 from rfl,account_append,account_append,hz]
  norm_num only [zero_add]
  have h1 := account_geometric 235 26 (by decide)
  have h2 := account_geometric 182 26 (by decide)
  norm_num [potential,unit] at h1 h2 ⊢
  rw [show 263=255+8 from rfl,pow_add] at h1
  norm_num at h1
  linarith

theorem error_axis_exact {n} (ws : List (Window n))
    (hz : ∀ w ∈ ws, ∀ start, errorCost (w.program start) = 0)
    (start : Nat) (prior : List (Fin start)) :
    errorCost (axis ws start prior) =
      account ((ws.map (fun w => w.wires.length)).sum) prior.length := by
  induction ws generalizing start with
  | nil => simp [axis,errorCost,account]
  | cons w ws ih =>
    simp only [axis,error_cast,error_append,error_prepare]
    rw [hz w (by simp) start,zero_add]
    have hf := error_fourier_exact n .inverse w.wires (start+w.count) (bankPrior w.count prior)
    have hi := ih (fun v hv s => hz v (List.mem_cons_of_mem w hv) s)
      (start+w.count+w.wires.length) (nextPrior w.count w.wires.length prior)
    rw [hf,hi]
    simp only [bankPrior,nextPrior,List.length_append,List.length_reverse,List.length_ofFn,List.length_map,List.map_cons,List.sum_cons,account_append]
    rw [Nat.add_comm w.wires.length prior.length]

theorem budget_floor : 2 * ((1653/4:ℝ) + 399) * ((6283186/1000000:ℝ)/2^28) ≤
    990038025/1000000000 - 99/100 := by norm_num


open Width16Schedule ConditionalCatalyst
variable [body : Single.WindowBody] [ledger : Single.ProducerResources body]
set_option linter.unusedSectionVars false
attribute [local irreducible] Width16Schedule.sourceEntry Width16Schedule.program
  Width16Schedule.fullProgram Width16Schedule.readout Single.fixedEntry Single.axis

theorem axis_width_sum {n} {ws : List (Single.Window n)} {widths : List Nat}
    (h : List.Forall₂ (fun w c => w.wires.length = c) ws widths) :
    (ws.map (fun w => w.wires.length)).sum = widths.sum := by
  induction h with
  | nil => rfl
  | cons head tail ih => simp only [List.map_cons,List.sum_cons,head,ih]

theorem full_error (impl : Width16Schedule.Implementation) (reset : List Wire) :
    errorCost (Width16Schedule.fullProgram impl reset) ≤ (1653/4:ℝ)*unit := by
  have hA := error_axis_exact ([impl.headA])
    (by
      intro w hw start
      apply error_zero
      rcases List.mem_singleton.mp hw with rfl
      exact impl.headA_zero start) 0 List.nil
  have hB := error_axis_exact ([impl.headB])
    (by
      intro w hw start
      apply error_zero
      rcases List.mem_singleton.mp hw with rfl
      exact impl.headB_zero start) (mixS1 impl.headA 0) List.nil
  have hL := error_axis_exact (leftBodies impl)
    (by
      intro w hw start
      apply error_zero
      obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hw
      exact impl.signed_zero d start) (mixS2 impl.headA impl.headB 0) (mixPriorL impl.headA impl.headB 0)
  have hR := error_axis_exact (rightBodies impl)
    (by
      intro w hw start
      apply error_zero
      obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hw
      exact impl.signed_zero d start)
    (mixS3 impl.headA impl.headB (leftBodies impl) 0) (mixPriorR impl.headA impl.headB (leftBodies impl) 0)
  rw [mixPriorL_length] at hL
  rw [mixPriorR_length] at hR
  rw [axis_width_sum (left_width_relation impl)] at hL
  rw [axis_width_sum (right_width_relation impl)] at hR
  have hsA : (([impl.headA]).map (fun w => w.wires.length)).sum = 10 := by
    simp [impl.headA_width]
  have hsB : (([impl.headB]).map (fun w => w.wires.length)).sum = 8 := by
    simp [impl.headB_width]
  rw [hsA, List.length_nil] at hA
  rw [hsB, List.length_nil] at hB
  have hlw : leftWidthsBody.sum = 251 := by simp [leftWidthsBody, List.replicate]
  have hrw : rightWidthsBody.sum = 200 := by simp [rightWidthsBody, List.replicate]
  rw [hlw] at hL
  rw [hrw] at hR
  have hz (n start : Nat) (ws : List Wire) : residue (resetProgram n start ws) = 0 := by
    induction ws generalizing start with
    | nil => simp [resetProgram,residue]
    | cons w ws ih => simpa [resetProgram,residue_cast,residue] using ih (start+1)
  have hreset : errorCost (resetProgram 1769472
      (mixS4 impl.headA impl.headB (leftBodies impl) (rightBodies impl) 0) reset) = 0 :=
    error_zero _ (hz _ _ _)
  have hro : errorCost (Width16Schedule.readout impl reset) = 0 := by
    apply error_zero
    simp only [Width16Schedule.readout,residue_cast,ApproximatePhase34.residue_suffix56]
  have hacc1 : account 261 0 = account 10 0 + account 251 10 := by
    have := account_append 10 251 0
    simpa using this
  have hacc2 : account 208 0 = account 8 0 + account 200 8 := by
    have := account_append 8 200 0
    simpa using this
  simp only [Width16Schedule.fullProgram,error_append,Width16Schedule.program,Single.framed,error_cast,errorCost,charge,zero_add,hreset,hro,mixHead,mixTail]
  linarith [joint_error]

theorem source_error (impl : Width16Schedule.Implementation) (reset : List Wire) :
    errorCost (Width16Schedule.sourceEntry impl reset).program ≤ (1653/4:ℝ)*unit := by
  unfold Width16Schedule.sourceEntry Single.fixedEntry
  rw [error_reindex]
  exact full_error impl reset

def entryTrim (entry : StraightEntry) : StraightEntry where
  coefficients := entry.coefficients
  finalCursor := entry.finalCursor
  program := trimN 399 entry.program
theorem trim_certificate (limits : Limits) (layout : DecodeLayout) (entry : StraightEntry)
    (bounds : Bounds) (ws : List ShorECDLP.Wire) (cert : Certificate limits layout entry bounds)
    (hs : Within ws entry.program) (herror : errorCost entry.program ≤ (1653/4:ℝ)*unit)
    (hstrong : ∀ (Q : ShorECDLP.Secp256k1.Point) (d : Nat), Q ≠ 0 →
      Q = d • ShorECDLP.Secp256k1.G →
      (990038025/1000000000 : ℝ) ≤ Instrument.bornMass ((entry.instantiate Q).run.filter
        (fun b => (verifiedCandidate layout Q b.history).isSome)) (ket ShorECDLP.zeroBasisState)) :
    Certificate limits layout (entryTrim entry) ⟨ws.length, bounds.tModel, entry.finalCursor⟩ where
  gateBudget := (trimN_slots 399 entry.program).trans cert.gateBudget
  recordBudget := cert.recordBudget
  tableBudget := cert.tableBudget
  candidateBudget := cert.candidateBudget
  wellFormed := trimN_wellFormed 399 entry.program cert.wellFormed
  resources := by
    intro Q
    have hsup := (trimN_within 399 entry.program ws hs).instantiate
      (readConstant entry.coefficients.get Q) Fin.elim0
    have hc : (((entryTrim entry).instantiate Q).wires.dedup.toFinset).card ≤ ws.length := by
      apply (Finset.card_le_card ?_).trans (List.toFinset_card_le ws)
      intro w hw
      apply List.mem_toFinset.mpr
      apply hsup
      simpa only [List.mem_toFinset, List.mem_dedup] using hw
    have hqc : ((entryTrim entry).instantiate Q).qubitCount ≤ ws.length := by
      rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
      exact hc
    refine ⟨hqc, ?_, ?_⟩
    · exact (trimN_t 399 entry.program (readConstant entry.coefficients.get Q) Fin.elim0).trans
        (cert.resources Q).2.1
    · have he := (entryTrim entry).program.measurementCount
        (readConstant entry.coefficients.get Q) Fin.elim0
      simpa only [Nat.add_zero] using he.le
  success := by
    intro Q d hn hd
    have h := trimN_expectation (readConstant entry.coefficients.get Q) entry.program 399 Fin.elim0
      (ket ShorECDLP.zeroBasisState) (fun h => (verifiedCandidate layout Q (List.ofFn h)).isSome) cert.wellFormed
    rw [expectation_verified, expectation_verified, normSq_ket] at h
    have hS := hstrong Q d hn hd
    change 99/100 ≤ Instrument.bornMass
      (((trimN 399 entry.program).instantiate (readConstant entry.coefficients.get Q) Fin.elim0).run.filter
        (fun b => (verifiedCandidate layout Q b.history).isSome)) (ket ShorECDLP.zeroBasisState)
    change 990038025/1000000000 ≤ Instrument.bornMass
      ((entry.program.instantiate (readConstant entry.coefficients.get Q) Fin.elim0).run.filter
        (fun b => (verifiedCandidate layout Q b.history).isSome)) (ket ShorECDLP.zeroBasisState) at hS
    norm_num [unit] at herror h
    nlinarith


theorem source_weight (impl : Implementation) (reset : List Wire) :
    weight4 (trimN 399 (sourceEntry impl reset).program) ≤
      4*(133758+19*impl.credit17+8*impl.credit16)+10626 := by
  have hw := fullProgram_weight impl reset
  have hr := fullProgram_removed impl reset
  have hc := fullProgram_band_count impl reset
  have hew : weight4 (sourceEntry impl reset).program = weight4 (fullProgram impl reset) := by
    unfold sourceEntry
    exact weight4_fixedEntry _ _
  have her (k : Nat) (hk : k=26 ∨ k=27) :
      removed k (sourceEntry impl reset).program = removed k (fullProgram impl reset) := by
    unfold sourceEntry
    rcases hk with rfl | rfl
    · exact weighted26_removed_fixedEntry _ _
    · exact removed27_fixedEntry _ _
  have h := weight4_trimN 399 (sourceEntry impl reset).program
  have hs : trimSpent 399 (sourceEntry impl reset).program = 399 := by
    rw [trimSpent_eq, her 26 (Or.inl rfl), her 27 (Or.inr rfl)]
    omega
  rw [hew,hs,her 27 (Or.inr rfl)] at h
  omega


theorem compiled_coefficients (impl : Width16Schedule.Implementation) (reset : List Wire) :
    (ConditionalCatalyst.fourEntry 1938 1939 (entryTrim (sourceEntry impl reset))).coefficients =
      List.ofFn Width16Schedule.coefficientAt :=
  (four_coefficients 1938 1939 (entryTrim (sourceEntry impl reset))).trans
    (by simpa only [entryTrim] using Width16Schedule.source_coefficients impl reset)

def finalEntry (impl : Width16Schedule.Implementation) (reset : List Wire) : StraightEntry :=
  specializeEntry (ConditionalCatalyst.fourEntry 1938 1939 (entryTrim (sourceEntry impl reset)))
    (compiled_coefficients impl reset)
theorem conditional_certificate (impl : Implementation) (reset ws : List Wire)
    (baseBounds : Bounds) (qBound : Nat)
    (rawCertificate : Certificate rawLimits (Width16Schedule.layout impl reset) (sourceEntry impl reset) baseBounds)
    (support : Within ws (sourceEntry impl reset).program)
    (strongSuccess : ∀ (Q : Point) (d : Nat), Q ≠ 0 → Q=d•G →
      (990038025/1000000000 : ℝ) ≤ Instrument.bornMass (((sourceEntry impl reset).instantiate Q).run.filter
        (fun b => (verifiedCandidate (Width16Schedule.layout impl reset) Q b.history).isSome)) (ket zeroBasisState))
    (hq : (1938 : Wire) ∉ ws) (hy : (1939 : Wire) ∉ 1938::ws)
    (slotBudget : 4*((sourceEntry impl reset).program.gateSlots+
      18*added (sourceEntry impl reset).program)+2 ≤ officialLimits.gateSlots)
    (recordBudget : (sourceEntry impl reset).finalCursor+added (sourceEntry impl reset).program ≤ officialLimits.measurements)
    (qubitBudget : ws.length+2 ≤ qBound)
    (measurementBound : (sourceEntry impl reset).finalCursor+added (sourceEntry impl reset).program ≤ 544000000) :
    Certificate officialLimits
      (lowerLayout 1938 (entryTrim (sourceEntry impl reset)) (Width16Schedule.layout impl reset))
      (finalEntry impl reset) ⟨qBound,4*(133758+19*impl.credit17+8*impl.credit16)+10627,544000000⟩ := by
  have trimmed := trim_certificate rawLimits (Width16Schedule.layout impl reset) (sourceEntry impl reset) baseBounds ws
    rawCertificate support (source_error impl reset) strongSuccess
  have hslots := trimN_slots 399 (sourceEntry impl reset).program
  have hw := source_weight impl reset
  unfold finalEntry
  apply specializeEntry_certificate _ (compiled_coefficients impl reset)
  apply ConditionalCatalyst.four_certificate rawLimits (Width16Schedule.layout impl reset)
    (entryTrim (sourceEntry impl reset)) _ _ 1938 1939 ws
    trimmed (trimN_within 399 (sourceEntry impl reset).program ws support) hq hy
  · change 4*((trimN 399 (sourceEntry impl reset).program).gateSlots+
      18*added (trimN 399 (sourceEntry impl reset).program))+2 ≤ officialLimits.gateSlots
    rw [trimN_added]
    omega
  · change (sourceEntry impl reset).finalCursor+added (trimN 399 (sourceEntry impl reset).program) ≤ officialLimits.measurements
    rw [trimN_added]
    exact recordBudget
  · exact qubitBudget
  · change weight4 (trimN 399 (sourceEntry impl reset).program)+1 ≤
      4*(133758+19*impl.credit17+8*impl.credit16)+10627
    omega
  · change (sourceEntry impl reset).finalCursor+added (trimN 399 (sourceEntry impl reset).program) ≤ 544000000
    rw [trimN_added]
    exact measurementBound


end
end ShorECDLP.Entrant.GeometricPhase

namespace ShorECDLP.Entrant.GeometricActual
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open Width16Actual
attribute [local instance] Width16Actual.bodyInstance Width16Actual.resourceInstance
attribute [local irreducible] Single.axis WideSigned.Signed16.program WEXFast.W15F.compactProgram
  ConditionalCatalyst.fourEntry ConditionalCatalyst.compileEntry ConditionalCatalyst.compile
  AndGadget.lowerEntry AndGadget.lowerLayout
noncomputable section
set_option Elab.async false
attribute [local irreducible] List.ofFn
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

def entry : StraightEntry := GeometricPhase.finalEntry implementation reset

def layout : DecodeLayout := lowerLayout 1938 (GeometricPhase.entryTrim rawEntry) rawLayout

def bounds : Bounds := ⟨1620,251046387,544000000⟩

theorem hcert : Certificate officialLimits
      (lowerLayout 1938 (GeometricPhase.entryTrim (Width16Schedule.sourceEntry implementation reset))
        (Width16Schedule.layout implementation reset))
      (GeometricPhase.finalEntry implementation reset)
      ⟨1620,4*(133758+19*implementation.credit17+8*implementation.credit16)+10627,544000000⟩ :=
  GeometricPhase.conditional_certificate implementation reset (List.range 1618)
    rawBounds 1620 raw_certificate source_within strong_success (by decide) (by decide)
    source_counts.2.2 (source_counts.2.1.trans (by decide)) (by decide) source_counts.2.1

theorem tmodel_key : ∀ a b : Nat, a ≤ 2346682 → b ≤ 2254778 →
    4*(133758+19*a+8*b)+10627 ≤ 251046387 := by
  intro a b ha hb
  omega

theorem hres (Q : Point) : (resources (entry.instantiate Q)).qubits ≤ bounds.qubits ∧
    (resources (entry.instantiate Q)).tModel ≤ bounds.tModel ∧
    (resources (entry.instantiate Q)).measurements ≤ bounds.measurements :=
  ⟨(hcert.resources Q).1, (Width16Actual.tmodel_of hcert Q).trans (tmodel_key _ _ credits.1 credits.2),
    (hcert.resources Q).2.2⟩

theorem certificate : Certificate officialLimits layout entry bounds :=
  Certificate.mk hcert.gateBudget hcert.recordBudget hcert.tableBudget hcert.candidateBudget
    hcert.wellFormed hres hcert.success

#print axioms certificate
end
end ShorECDLP.Entrant.GeometricActual
