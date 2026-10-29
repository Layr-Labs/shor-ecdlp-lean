import ShorECDLP.Submission.«2607_13816».Challenge.WindowBody
import ShorECDLP.Submission.Entrant.Streaming.Correction
import ShorECDLP.Submission.«2607_13816».Arithmetic.ZeroAllowedPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».Arithmetic.UnitaryPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.EndpointPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.BlockEPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».Challenge.OuterResources
import ShorECDLP.Submission.«2607_13816».EEA.WrapperPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.ScheduleLayout
import ShorECDLP.Submission.«2607_13816».EEA.IndexedStepPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».Challenge.Records
import ShorECDLP.Submission.«2607_13816».Challenge.GidneyAdd
import ShorECDLP.Submission.«2607_13816».Challenge.BatchCost
import ShorECDLP.Submission.«2607_13816».Window.LookupPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».Challenge.BatchTemplate
import ShorECDLP.Submission.«2607_13816».Challenge.LengthRefresh
import ShorECDLP.Submission.«2607_13816».EEA.PhysicalSupport
import ShorECDLP.Submission.«2607_13816».Challenge.MeasuredStep
import ShorECDLP.Submission.«2607_13816».Challenge.MeasuredWorkspace
import ShorECDLP.Submission.«2607_13816».EEA.WrapperSupport
import ShorECDLP.Submission.«2607_13816».Challenge.Coordinate
import ShorECDLP.Submission.«2607_13816».Arithmetic.ZeroAllowedResources

/-! EDITABLE. Single-trial entrant: inherited resource and support lemmas.
Concatenated in dependency order to bound parallel kernel replay memory.
Original provenance comments are retained beside each source part. -/

-- ==== part: Streaming/LookupSlots ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/LookupSlots.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

/-- Every fixed gate slot counts, including disabled constant/record controls. -/
def lookupSlots {n : Nat} : List (LookupOp n) → Nat
  | [] => 0
  | .gates gs :: ops => gs.length + lookupSlots ops
  | .erase _ _ _ :: ops => 3 + lookupSlots ops

theorem recordGates_slots {n s e : Nat} (i : Fin s) (gs : Circuit) (next : Straight n s e) :
    (recordGates i gs next).gateSlots = gs.length + next.gateSlots := by
  induction gs <;> simp_all [recordGates,Straight.gateSlots,Nat.add_assoc,Nat.add_left_comm]

theorem lookupProgram_slots (n : Nat) (ops : List (LookupOp n)) (start : Nat) :
    (lookupProgram n ops start).gateSlots = lookupSlots ops := by
  induction ops generalizing start with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | gates gs => simp only [lookupProgram,Straight.gateSlots_append,gateProgram_slots,ih,lookupSlots]
    | erase a b t =>
      simp only [lookupProgram,castFinish_gateSlots,Straight.gateSlots_append,andEraseProgram,
        Straight.gateSlots,recordGates_slots,controlledZ,List.length_cons,List.length_nil,ih,lookupSlots]

theorem lookupSlots_append {n : Nat} (xs ys : List (LookupOp n)) :
    lookupSlots (xs++ys) = lookupSlots xs + lookupSlots ys := by
  induction xs with
  | nil => simp [lookupSlots]
  | cons x xs ih => cases x <;> simp_all [lookupSlots,Nat.add_assoc]

theorem unaryLookupOps_slots_le {n : Nat} (leaf : Nat → Wire → List (TemplateGate n))
    (bound : Nat) (hleaf : ∀ l q, (leaf l q).length ≤ bound)
    (tree : UnaryActionTree) (q : Wire) (anc : List Wire) :
    lookupSlots (unaryLookupOps leaf tree q anc) ≤
      bound * (tree.internalNodes+1) + 10*tree.internalNodes := by
  induction tree generalizing q anc with
  | leaf l => simpa [unaryLookupOps,lookupSlots,UnaryActionTree.internalNodes] using hleaf l q
  | node bit zero one ihz iho =>
    cases anc with
    | nil => simp [unaryLookupOps,lookupSlots]
    | cons path rest =>
      have hz := ihz path rest
      have ho := iho path rest
      simp only [unaryLookupOps,lookupSlots_append,lookupSlots,ordinaryOp,List.length_map,
        computeZeroAnd,List.length_cons,List.length_nil,UnaryActionTree.internalNodes,
        Nat.mul_add,Nat.mul_one] at *
      omega

theorem pointLeaf_slots {n : Nat} (row : Fin n) (q : Wire) : (pointLeaf row q).length ≤ 513 := by
  simp only [pointLeaf,lookupLeafGates,List.length_map,List.length_zip]
  apply Nat.min_le_left _ _ |>.trans
  simp only [pointRefs,List.length_append,List.length_ofFn,List.length_cons,List.length_nil]
  decide

theorem actualFirstWindow_slots (start : Nat) :
    (actualFirstWindow.program start).gateSlots ≤ 34275318 := by
  have h := unaryLookupOps_slots_le
    (fun l q => pointLeaf ⟨l % 65536,Nat.mod_lt _ (by decide)⟩ q)
    513 (fun _ q => pointLeaf_slots _ q)
    (tableAddressTree (List.range' 855 16) 0 1) 836 (List.range' 519 16)
  have hn := tableAddressTree_nodes (List.range' 855 16) 0 1
  change (tableAddressTree (List.range' 855 16) 0 1).internalNodes+1 = 65536 at hn
  simpa only [actualFirstWindow,reindexStraight_gateSlots,firstLookupProgram,
    castFinish_gateSlots,lookupProgram_slots,firstLookupOps] using
    (show lookupSlots (unaryLookupOps (fun l q => pointLeaf ⟨l % 65536,Nat.mod_lt _ (by decide)⟩ q)
      (tableAddressTree (List.range' 855 16) 0 1) 836 (List.range' 519 16)) ≤ 34275318 by omega)

/-- For a unitary list the five primitive counters partition its actual gates. -/
theorem circuit_length_primitive (gs : Circuit) :
    gs.length = (primitiveResources (.unitary gs .done)).x +
      (primitiveResources (.unitary gs .done)).h +
      (primitiveResources (.unitary gs .done)).cnot +
      (primitiveResources (.unitary gs .done)).toffoli +
      (primitiveResources (.unitary gs .done)).phase := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    cases g <;> simp_all [primitiveResources,gidneyGateCount,gidneyCnotCount,gidneyToffoliCount,
      primitiveXCost,primitiveHCost,primitivePhaseCost] <;> omega

theorem zeroBitCount_bound (value bit width : Nat) : zeroBitCount value bit width ≤ width := by
  induction width generalizing bit with
  | zero => rfl
  | succ width ih =>
    simp only [zeroBitCount]
    have h := ih (bit+1)
    split <;> omega

theorem registerEqualCircuit_length_le (cells : List (Wire × Wire)) (flag : Wire) (scratch : List Wire)
    (hl : cells.length = 513) (hs : 511 ≤ scratch.length) :
    (registerEqualCircuit cells flag scratch).length ≤ 3075 := by
  have hx : (xorWordCircuit cells).length = cells.length := by
    simp only [xorWordCircuit,List.length_map]
  have hc := computeEqConst_primitive (cells.map Prod.snd) 0 flag scratch
    (by simpa only [List.length_map,hl] using hs)
  have hlen := circuit_length_primitive (computeEqConst (cells.map Prod.snd) 0 flag scratch)
  rw [hc] at hlen
  simp only [List.length_map,hl] at hlen
  have hz := zeroBitCount_bound 0 0 513
  simp only [registerEqualCircuit,List.length_append,hx,hl]
  norm_num only [mcxVChainCnotCost,mcxVChainToffoliCost] at hlen
  simp only [ite_false] at hlen
  omega

theorem batchOpCircuit_length_le (base : Wire) (source : Fin 4) (target : Fin 6) :
    (batchOpCircuit base source target).length ≤ 13326 := by
  have he (a t : Fin 513 → Wire) :
      (registerEqualCircuit (equalityCells a t) (batchFlag base) (batchScratch base)).length ≤ 3075 :=
    registerEqualCircuit_length_le _ _ _ (by simp only [equalityCells,List.length_ofFn]) (by simp only [batchScratch,List.length_ofFn]; decide)
  unfold batchOpCircuit endpointTranspositionCircuit endpointTests
  simp only [List.length_append,endpointWordCircuit_length,endpointUpdateCells,List.length_ofFn]
  have ha := he (batchWord base ⟨source.val,by omega⟩) (batchWord base target)
  have hb := he (batchWord base 4) (batchWord base target)
  omega

theorem endpointSelectGates_length_le {n : Nat} (q : Wire) (ports : List (Wire × EndpointBit n)) :
    (endpointSelectGates q ports).length ≤ ports.length := by
  induction ports with
  | nil => rfl
  | cons port ports ih =>
    rcases port with ⟨w,tag⟩
    cases tag with
    | inl b =>
      cases b
      · simp_all [endpointSelectGates,endpointSelectGate]; omega
      · simp_all [endpointSelectGates,endpointSelectGate]
    | inr r => simp_all [endpointSelectGates,endpointSelectGate]

theorem batchLeaf_length_le {n : Nat} (row : Fin n) (base q : Wire) (selection : List (Fin 8 × Fin 5)) :
    (batchLeaf row base q selection).length ≤ 514 * selection.length := by
  have hp : (batchPorts row base selection).length = 513 * selection.length := by
    induction selection with
    | nil => simp only [batchPorts,List.flatMap_nil,List.length_nil,Nat.mul_zero]
    | cons x xs ih =>
      simp only [batchPorts,List.flatMap_cons,List.length_append,List.length_ofFn] at ih ⊢
      simp only [List.length_cons,Nat.mul_add,Nat.mul_one]
      omega
  have he := endpointSelectGates_length_le q (batchPorts row base selection)
  have ht : (batchTags base selection).length ≤ selection.length := by
    simpa only [batchTags,List.length_map] using List.length_filter_le (fun p => endpointTagMask p.1 512) selection
  simp only [batchLeaf,List.length_append,List.length_map]
  omega

def batchSlotBound (nodes : Nat) : List BatchOp → Nat
  | [] => 0
  | .query _ _ :: ops => 2570*(nodes+1)+10*nodes+batchSlotBound nodes ops
  | .swap _ _ :: ops => 13326+batchSlotBound nodes ops

theorem batchOps_slots_le {n : Nat} (rows : Nat → Fin n) (base : Wire) (tree : UnaryActionTree)
    (q : Wire) (paths : List Wire) (ops : List BatchOp) :
    lookupSlots (batchOps rows base tree q paths ops) ≤ batchSlotBound tree.internalNodes ops := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | query sources target =>
      have hl (l : Nat) (control : Wire) :
          (batchLeaf (rows l) base control (batchSelection sources target)).length ≤ 2570 := by
        have h := batchLeaf_length_le (rows l) base control (batchSelection sources target)
        have hs : (batchSelection sources target).length ≤ 5 := by
          cases sources <;> simp only [batchSelection,Bool.false_eq_true,ite_false,ite_true,
            List.length_append,List.length_cons,List.length_nil] <;> decide
        omega
      have h := unaryLookupOps_slots_le _ 2570 hl tree q paths
      simp only [batchOps,lookupSlots_append,batchSlotBound]
      omega
    | swap source target =>
      have h := batchOpCircuit_length_le base source target
      simp only [batchOps,lookupSlots,ordinaryOp,List.length_map,batchSlotBound]
      omega

theorem relabelStraight_slots {n s t : Nat} (e : Wire ≃ Wire) (p : Straight n s t) :
    (relabelStraight e p).gateSlots = p.gateSlots := by
  induction p <;> simp_all only [relabelStraight,Straight.gateSlots]

theorem batchSlotBound_schedule (nodes : Nat) :
    batchSlotBound nodes batchSchedule = 14*(2570*(nodes+1)+10*nodes)+16*13326 := by
  simp only [batchSchedule,batchSlotBound]
  omega

theorem computeEqConst_length_le (r : List Wire) (value : Nat) (flag : Wire) (scratch : List Wire)
    (hs : r.length-2 ≤ scratch.length) (hr : r.length = 257) :
    (computeEqConst r value flag scratch).length ≤ 1025 := by
  have hc := computeEqConst_primitive r value flag scratch hs
  have hlen := circuit_length_primitive (computeEqConst r value flag scratch)
  rw [hc] at hlen
  have hz := zeroBitCount_bound value 0 r.length
  rw [hr] at hlen hz
  norm_num only [mcxVChainCnotCost,mcxVChainToffoliCost] at hlen
  (try simp only [ite_false] at hlen)
  omega

theorem ipxTest_length_le (k : Fin 4) : (ipxTest k).length ≤ 3075 := by
  have h1 := computeEqConst_length_le ipxLow 0 ipxHalf ipxScratch
    (by simp [ipxLow,ipxScratch]) (by simp [ipxLow])
  have h2 := computeEqConst_length_le (ipxHalf :: ipxHigh) 1 (ipxFlag k) ipxScratch
    (by simp [ipxHigh,ipxScratch]) (by simp [ipxHigh])
  simp only [ipxTest,List.length_append]
  omega

theorem ipxLeaf_length_le {n : Nat} (row : Fin n) (q : Wire) (u : Fin 8) (v : Option (Fin 8)) :
    (ipxLeaf row q u v).length ≤ 1026 := by
  have h1 := endpointSelectGates_length_le q (ipxPorts row u)
  have h2 := endpointSelectGates_length_le q (ipxPortsOpt row v)
  have l1 : (ipxPorts row u).length = 513 := by simp only [ipxPorts,List.length_ofFn]
  have l2 : (ipxPortsOpt row v).length ≤ 513 := by
    cases v <;> simp only [ipxPortsOpt,ipxPorts,List.length_nil,List.length_ofFn] <;> omega
  simp only [ipxLeaf,List.length_append]
  omega

def ipxSlotBound (nodes : Nat) : List IpxOp → Nat
  | [] => 0
  | .query _ _ _ :: ops => 1026*(nodes+1)+10*nodes+ipxSlotBound nodes ops
  | .test _ :: ops => 3075+ipxSlotBound nodes ops

theorem ipxOps_slots_le {n : Nat} (rows : Nat → Fin n) (tree : UnaryActionTree) (paths : List Wire)
    (ops : List IpxOp) :
    lookupSlots (ipxOps rows tree paths ops) ≤ ipxSlotBound tree.internalNodes ops := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | query c u v =>
      have h := unaryLookupOps_slots_le _ 1026 (fun l q => ipxLeaf_length_le (rows l) q u v)
        tree (ipxControl c) paths
      simp only [ipxOps,lookupSlots_append,ipxSlotBound]
      omega
    | test k =>
      have h := ipxTest_length_le k
      simp only [ipxOps,lookupSlots,ordinaryOp,List.length_map,ipxSlotBound]
      omega

theorem ipxSlotBound_schedule (nodes : Nat) :
    ipxSlotBound nodes ipxSchedule = 13*(1026*(nodes+1)+10*nodes)+8*3075 := by
  simp only [ipxSchedule,ipxPhase1,ipxPhase2,ipxPhase3,List.cons_append,List.nil_append,ipxSlotBound]
  omega

/-- The correction block keeps the slot budget of the block it replaces. -/
theorem ipxProgram_slots (w : OddWindow) (start : Nat) :
    (ipxProgram w start).2.gateSlots ≤ 1183793236 := by
  simp only [ipxProgram,ipxProgramOf,lookupProgram_slots]
  have h := ipxOps_slots_le (batchWindowRows w) batchWindowTree pointLookupPath ipxSchedule
  rw [ipxSlotBound_schedule,batchWindowTree_nodes] at h
  omega

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/ArithmeticSlots ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/ArithmeticSlots.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

def nonCarryCost : Gate → Nat
  | .CX _ _ | .CCX _ _ _ => 0
  | _ => 1

theorem circuit_length_carry (gs : Circuit) :
    gs.length = eeaCnotCount gs + eeaToffoliCount gs + (gs.map nonCarryCost).sum := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    cases g <;> simp_all [eeaCnotCount,eeaToffoliCount,nonCarryCost] <;> omega

theorem carryXor_length_le (input dirty : List Wire) (constant : List Bool) (q c : Wire)
    (hd : input.length = dirty.length) (hk : constant.length = input.length) :
    (controlledConstCarryXor input dirty constant q c).length ≤ 9*input.length := by
  have hw (bs : List Bool) : constantBitWeight bs ≤ bs.length := by
    induction bs with
    | nil => rfl
    | cons b bs ih =>
      cases b <;> simp only [constantBitWeight,List.map_cons,List.sum_cons,List.length_cons,
        Bool.toNat_false,Bool.toNat_true] at ih ⊢ <;> omega
  cases input with
  | nil => simp [controlledConstCarryXor]
  | cons a input =>
    cases constant with
    | nil => simp at hk
    | cons k constant =>
      have h := controlledConstCarryXor_counts a input dirty k constant q c (by simpa using hk.symm) hd
      have hz := controlledConstCarryXor_cost_zero nonCarryCost (by intros; rfl) (by intros; rfl)
        (a::input) dirty (k::constant) q c
      have hwc := hw constant
      rw [circuit_length_carry,h.2.1,h.2.2.1,hz]
      have hb : k.toNat ≤ 1 := by cases k <;> decide
      simp only [List.length_cons] at hk ⊢
      omega

theorem gidneyAddCleanup_length_le (input dirty : List Wire) (constant : List Bool) (q c : Wire)
    (hd : input.length = dirty.length+1) (hk : constant.length=input.length) :
    (gidneyAddCleanup input dirty constant q c).length ≤ 11*input.length := by
  have h := carryXor_length_le (input.take dirty.length) dirty (constant.take dirty.length) q c
    (by simp only [List.length_take]; omega) (by simp only [List.length_take]; omega)
  simp only [gidneyAddCleanup,gidneyFlipWord,List.length_append,List.length_map]
  simp only [List.length_take] at h
  omega

theorem deferredCorrectionSlots_le (targets cleanup prior : Nat) (cells : List (Circuit × Wire)) :
    deferredCorrectionSlots targets cleanup prior cells ≤
      (cells.map (fun c => c.1.length)).sum + 6*targets + cleanup := by
  induction cells generalizing prior with
  | nil => simp only [deferredCorrectionSlots,List.map_nil,List.sum_nil]; omega
  | cons c cells ih =>
    rcases c with ⟨gs,w⟩
    simp only [deferredCorrectionSlots,List.map_cons,List.sum_cons]
    have h := ih (prior+1)
    omega

theorem gidneyCarryCells_slots_le (q current spare ancilla : Wire)
    (input dirty : List Wire) (constant : List Bool)
    (hd : input.length=dirty.length+1) (hk : constant.length=input.length) :
    ((gidneyCarryCells q current spare ancilla input dirty constant).map (fun c => c.1.length)).sum ≤
      9*input.length := by
  induction input generalizing current spare dirty constant with
  | nil => simp at hd
  | cons a input ih =>
    cases constant with
    | nil => simp at hk
    | cons k ks =>
      cases input with
      | nil =>
        have hd' : dirty=[] := List.eq_nil_of_length_eq_zero (by simp_all)
        have hk' : ks=[] := List.eq_nil_of_length_eq_zero (by simp_all)
        subst dirty; subst ks
        cases k <;> simp [gidneyCarryCells]
      | cons b bs =>
        cases dirty with
        | nil => simp at hd
        | cons d ds =>
          have h := ih spare current ds ks (by simpa using hd) (by simpa using hk)
          simp only [gidneyCarryCells,List.map_cons,List.sum_cons,List.length_cons]
          have hc : (gidneyAddCarryCell q current spare ancilla a d k).length ≤ 9 := by
            cases k <;> simp [gidneyAddCarryCell]
          simp only [List.length_cons] at h
          omega
theorem gidneyNontrivialProgram_slots_le (n start : Nat) (a d q carry spare ancilla : Wire)
    (as ds : List Wire) (k : Bool) (ks : List Bool)
    (hd : as.length=ds.length+1) (hk : ks.length=as.length) :
    (gidneyNontrivialProgram n start a d q carry spare ancilla as ds k ks).gateSlots ≤
      26*(as.length+1) := by
  have ht := gidneyCarryCells_slots_le q spare carry ancilla as ds ks hd hk
  have hc := gidneyAddCleanup_length_le (a::as) (d::ds) (k::ks) q carry
    (by simp only [List.length_cons]; omega) (by simp only [List.length_cons]; omega)
  have hf : (gidneyAddCarryCell q carry spare ancilla a d k).length ≤ 9 := by
    cases k <;> simp [gidneyAddCarryCell]
  have hb := deferredCorrectionSlots_le (d::ds).length
    (gidneyAddCleanup (a::as) (d::ds) (k::ks) q carry).length 0
    (gidneyCarryCells q spare carry ancilla as ds ks)
  simp only [gidneyNontrivialProgram,Straight.gateSlots_append,literalProgram_slots,
    deferredCorrectionProgram_slots,List.length_nil,List.length_cons]
  simp only [List.length_cons] at hc hb
  omega

theorem gidneyProgram_slots_le (n start : Nat) (input dirty : List Wire) (constant : List Bool)
    (q carry spare ancilla : Wire) (hd : input.length=dirty.length+1)
    (hk : constant.length=input.length) :
    (gidneyProgram n start input dirty constant q carry spare ancilla).2.gateSlots ≤ 26*input.length := by
  by_cases hz : constant.all (fun k => !k) = true
  · rw [show gidneyProgram n start input dirty constant q carry spare ancilla = ⟨0,.done⟩ by simp only [gidneyProgram,hz,ite_true]]; exact Nat.zero_le _
  · rw [show gidneyProgram n start input dirty constant q carry spare ancilla = _ by exact if_neg hz]
    cases input with
    | nil => simp at hd
    | cons a as =>
      cases constant with
      | nil => simp at hk
      | cons k ks =>
        cases dirty with
        | nil =>
          have ha : as=[] := List.eq_nil_of_length_eq_zero (by simp_all)
          have hks : ks=[] := List.eq_nil_of_length_eq_zero (by simp_all)
          subst as; subst ks
          cases k <;> simp [literalProgram_slots]
        | cons d ds =>
          have h := gidneyNontrivialProgram_slots_le n start a d q carry spare ancilla as ds k ks
            (by simpa using hd) (by simpa using hk)
          cases as with
          | nil => simp at hd
          | cons b bs => exact h

theorem compareCarryCell_length_le (q c r t a d f : Wire) (k last : Bool) :
    (gidneyCompareCarryCell q c r t a d f k last).length ≤ 10 := by
  cases k <;> cases last <;> simp [gidneyCompareCarryCell]

theorem compareCarryCells_slots_le (q current spare ancilla flag : Wire)
    (input dirty : List Wire) (constant : List Bool)
    (hd : input.length=dirty.length) (hk : constant.length=input.length) :
    ((compareCarryCells q current spare ancilla flag input dirty constant).map (fun c => c.1.length)).sum ≤
      10*input.length := by
  induction input generalizing current spare dirty constant with
  | nil =>
    have hd' : dirty=[] := List.eq_nil_of_length_eq_zero hd.symm
    have hk' : constant=[] := List.eq_nil_of_length_eq_zero hk
    subst dirty; subst constant
    rfl
  | cons a input ih =>
    cases constant with
    | nil => simp at hk
    | cons k ks =>
      cases dirty with
      | nil => simp at hd
      | cons d ds =>
        have h := ih spare current ds ks (by simpa using hd) (by simpa using hk)
        have hc := compareCarryCell_length_le q current spare ancilla a d flag k input.isEmpty
        simp only [compareCarryCells,List.map_cons,List.sum_cons,List.length_cons]
        omega

theorem compareCarryProgram_slots_le (n start : Nat) (a d q carry spare ancilla flag : Wire)
    (input dirty : List Wire) (k : Bool) (constant : List Bool)
    (hd : input.length=dirty.length) (hk : constant.length=input.length) :
    (compareCarryProgram n start a d q carry spare ancilla flag input dirty k constant).gateSlots ≤
      25*(input.length+1) := by
  have ht := compareCarryCells_slots_le q spare carry ancilla flag input dirty constant hd hk
  have hc := carryXor_length_le (a::input) (d::dirty) (k::constant) q carry
    (by simp only [List.length_cons]; omega) (by simp only [List.length_cons]; omega)
  have hf := compareCarryCell_length_le q carry spare ancilla a d flag k input.isEmpty
  have hb := deferredCorrectionSlots_le (d::dirty).length
    (controlledConstCarryXor (a::input) (d::dirty) (k::constant) q carry).length 0
    (compareCarryCells q spare carry ancilla flag input dirty constant)
  simp only [compareCarryProgram,Straight.gateSlots_append,literalProgram_slots,
    deferredCorrectionProgram_slots,List.length_nil,List.length_cons]
  simp only [List.length_cons] at hc hb
  omega

theorem compareCoreProgram_slots_le (n start : Nat) (input dirty : List Wire) (constant : List Bool)
    (q carry spare ancilla flag : Wire) (hd : input.length=dirty.length)
    (hk : constant.length=input.length) :
    (compareCoreProgram n start input dirty constant q carry spare ancilla flag).2.gateSlots ≤ 25*input.length := by
  cases input with
  | nil => simp [compareCoreProgram,Straight.gateSlots]
  | cons a input =>
    cases dirty with
    | nil => simp at hd
    | cons d dirty =>
      cases constant with
      | nil => simp at hk
      | cons k constant =>
        exact compareCarryProgram_slots_le n start a d q carry spare ancilla flag input dirty k constant
          (by simpa using hd) (by simpa using hk)

theorem compareGEProgram_slots_le (n start : Nat) (input dirty : List Wire) (threshold : Nat)
    (q carry spare ancilla flag : Wire) (hd : input.length=dirty.length) :
    (compareGEProgram n start input dirty threshold q carry spare ancilla flag).2.gateSlots ≤ 25*input.length+1 := by
  by_cases hz : threshold=0
  · rw [show compareGEProgram n start input dirty threshold q carry spare ancilla flag = ⟨0,literalProgram [.CX q flag]⟩ by exact if_pos hz]
    simp only [literalProgram_slots,List.length_cons,List.length_nil]; omega
  · by_cases hh : 2^input.length ≤ threshold
    · rw [show compareGEProgram n start input dirty threshold q carry spare ancilla flag = ⟨0,.done⟩ by simp only [compareGEProgram, hz,ite_false,hh,ite_true]]
      exact Nat.zero_le _
    · rw [show compareGEProgram n start input dirty threshold q carry spare ancilla flag = _ by exact if_neg hz]
      rw [if_neg hh]
      have h := compareCoreProgram_slots_le n start input dirty
        ((List.range input.length).map (Nat.testBit (2^input.length-threshold))) q carry spare ancilla flag hd
        (by simp only [List.length_map,List.length_range])
      omega

theorem appendCompiled_slots {n start : Nat} (p : (count : Nat) × Straight n start (start+count))
    (q : (count : Nat) × Straight n (start+p.1) (start+p.1+count)) :
    (appendCompiled p q).2.gateSlots = p.2.gateSlots+q.2.gateSlots := by
  simp only [appendCompiled,castFinish_gateSlots,Straight.gateSlots_append]

theorem prependCompiled_slots {n start : Nat} (gs : Circuit)
    (p : (count : Nat) × Straight n start (start+count)) :
    (prependCompiled gs p).2.gateSlots = gs.length+p.2.gateSlots := by
  simp only [prependCompiled,Straight.gateSlots_append,literalProgram_slots]

attribute [local irreducible] compareGEProgram gidneyProgram

theorem modularNegateProgram_slots_le (n start : Nat) (target dirty : List Wire) (modulus : List Bool)
    (q c r t f : Wire) (hd : target.length=dirty.length) (hk : modulus.length=target.length)
    (hpos : 0<target.length) :
    (modularNegateProgram n start target dirty modulus q c r t f).2.gateSlots ≤ 103*target.length+2 := by
  have htake : target.length=(dirty.take (target.length-1)).length+1 := by
    simp only [List.length_take]; omega
  have ht (s : Nat) := compareGEProgram_slots_le n s target dirty 1 q c r t f hd
  have hi (s : Nat) := gidneyProgram_slots_le n s target (dirty.take (target.length-1))
    ((List.range target.length).map (Nat.testBit 1)) q c r t htake
    (by simp only [List.length_map,List.length_range])
  have ha (s : Nat) := gidneyProgram_slots_le n s target (dirty.take (target.length-1)) modulus f c r t htake hk
  simp only [modularNegateProgram,appendCompiled_slots,prependCompiled_slots]
  have hc : (controlledComplement target q).length=target.length := by
    simp only [controlledComplement,List.length_map]
  rw [hc]
  grind only

theorem negativeNegateProgram_slots_le (n start : Nat) (target dirty : List Wire) (modulus : List Bool)
    (q c r t f : Wire) (hd : target.length=dirty.length) (hk : modulus.length=target.length)
    (hpos : 0<target.length) :
    (negativeNegateProgram n start target dirty modulus q c r t f).2.gateSlots ≤ 103*target.length+4 := by
  have h := modularNegateProgram_slots_le n start target dirty modulus q c r t f hd hk hpos
  simp only [negativeNegateProgram,prependCompiled_slots,appendCompiled_slots,literalProgram_slots,
    List.length_cons,List.length_nil]
  omega

theorem yNegateProgram_slots_le (start : Nat) : (yNegateProgram start).2.gateSlots ≤ 26372 := by
  have h := negativeNegateProgram_slots_le 32768 start (List.range' 580 256) (List.range' 7 256)
    (constantBits 256 ShorECDLP.p) 854 559 560 561 558
    (by simp only [List.length_range']) (by rw [constantBits_length,List.length_range']) (by simp only [List.length_range']; decide)
  change (yNegateProgram start).2.gateSlots ≤ _ at h
  simpa only [List.length_range'] using h

theorem uncontrolledCompareProgram_slots_le (n start : Nat) (input dirty : List Wire) (threshold : Nat)
    (c r t f : Wire) (hd : input.length=dirty.length) :
    (uncontrolledCompareProgram n start input dirty threshold c r t f).2.gateSlots ≤ 25*input.length+1 := by
  simp only [uncontrolledCompareProgram,constantStraight_slots]
  exact compareGEProgram_slots_le n start input dirty threshold _ c r t f hd

theorem controlledAddCarry_length256 (bs as : List Wire) (q c f : Wire)
    (hb : bs.length=256) (ha : as.length=256) : (controlledAddCarry bs as q c f).length=1793 := by
  rw [circuit_length_primitive,controlledAddCarry256_primitive _ _ _ _ _ hb ha .done]
  rfl

theorem controlledCompareLT_length256 (bs as : List Wire) (q c f : Wire)
    (hb : bs.length=256) (ha : as.length=256) : (controlledCompareLT bs as q c f).length=2053 := by
  rw [circuit_length_primitive,controlledCompareLT256_primitive _ _ _ _ _ hb ha .done]
  rfl

attribute [local irreducible] uncontrolledCompareProgram

theorem modularAddProgram_slots256 (n start : Nat) (input acc : List Wire) (correction : List Bool)
    (p : Nat) (q c r t f : Wire) (hi : input.length=256) (ha : acc.length=256)
    (hk : correction.length=256) :
    (modularAddProgram n start input acc correction p q c r t f).2.gateSlots ≤ 16903 := by
  have ht (s : Nat) := uncontrolledCompareProgram_slots_le n s acc input p c r t f (ha.trans hi.symm)
  have hg (s : Nat) := gidneyProgram_slots_le n s acc (input.take (acc.length-1)) correction f c r t
    (by simp only [List.length_take,hi,ha]; decide) (hk.trans ha.symm)
  have hb := controlledAddCarry_length256 input acc q c f hi ha
  have hc := controlledCompareLT_length256 acc input q c f ha hi
  simp only [modularAddProgram,appendCompiled_slots,Straight.gateSlots_append,literalProgram_slots,hb,hc]
  simp only [ha] at ht hg
  grind only

theorem circuit_adjoint_length (gs : Circuit) : gs.adjoint.length=gs.length := by
  simp only [Circuit.adjoint,List.length_map,List.length_reverse]

theorem modularSubProgram_slots256 (n start : Nat) (input acc : List Wire) (bits : List Bool)
    (p : Nat) (q c r t f : Wire) (hi : input.length=256) (ha : acc.length=256)
    (hk : bits.length=256) :
    (modularSubProgram n start input acc bits p q c r t f).2.gateSlots ≤ 16903 := by
  have ht (s : Nat) := uncontrolledCompareProgram_slots_le n s acc input p c r t f (ha.trans hi.symm)
  have hg (s : Nat) := gidneyProgram_slots_le n s acc (input.take (acc.length-1)) bits f c r t
    (by simp only [List.length_take,hi,ha]; decide) (hk.trans ha.symm)
  have hb := controlledAddCarry_length256 input acc q c f hi ha
  have hc := controlledCompareLT_length256 acc input q c f ha hi
  simp only [modularSubProgram,appendCompiled_slots,prependCompiled_slots,literalProgram_slots,
    controlledSubCarry,circuit_adjoint_length,hb,hc]
  simp only [ha] at ht hg
  grind only

theorem doublingShift_length256 (acc : List Wire) (f : Wire) (ha : acc.length=256) :
    (doublingShift acc f).length=767 := by
  rw [circuit_length_primitive,doublingShift256_primitive _ _ ha .done]
  rfl

theorem modularDoubleProgram_slots256 (n start : Nat) (acc dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (ha : acc.length=256) (hd : dirty.length=256) (hk : bits.length=256) :
    (modularDoubleProgram n start acc dirty bits p c r t f).2.gateSlots ≤ 13825 := by
  cases acc with
  | nil => simp at ha
  | cons a rest =>
    have ht (s : Nat) := uncontrolledCompareProgram_slots_le n s (a::rest) dirty p c r t f (ha.trans hd.symm)
    have hg (s : Nat) := gidneyProgram_slots_le n s (a::rest) (dirty.take rest.length) bits f c r t
      (by simp only [List.length_take,List.length_cons] at ha ⊢; omega) (hk.trans ha.symm)
    have hb := doublingShift_length256 (a::rest) f ha
    simp only [modularDoubleProgram,appendCompiled_slots,prependCompiled_slots,literalProgram_slots,
      List.length_cons,List.length_nil,hb]
    simp only [ha] at ht hg
    grind only

theorem modularHalveProgram_slots256 (n start : Nat) (acc dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (ha : acc.length=256) (hd : dirty.length=256) (hk : bits.length=256) :
    (modularHalveProgram n start acc dirty bits p c r t f).2.gateSlots ≤ 13825 := by
  cases acc with
  | nil => simp at ha
  | cons a rest =>
    have ht (s : Nat) := uncontrolledCompareProgram_slots_le n s (a::rest) dirty p c r t f (ha.trans hd.symm)
    have hg (s : Nat) := gidneyProgram_slots_le n s (a::rest) (dirty.take rest.length) bits f c r t
      (by simp only [List.length_take,List.length_cons] at ha ⊢; omega) (hk.trans ha.symm)
    have hb := doublingShift_length256 (a::rest) f ha
    simp only [modularHalveProgram,appendCompiled_slots,prependCompiled_slots,literalProgram_slots,
      List.length_cons,List.length_nil,circuit_adjoint_length,hb]
    simp only [ha] at ht hg
    grind only

theorem compiledIf_slots {n start : Nat} (b : Prop) [Decidable b]
    (p q : (count : Nat) × Straight n start (start+count)) :
    (if b then p else q).2.gateSlots = if b then p.2.gateSlots else q.2.gateSlots := by
  by_cases hb : b
  · rw [if_pos hb,if_pos hb]
  · rw [if_neg hb,if_neg hb]

attribute [local irreducible] modularAddProgram modularSubProgram modularDoubleProgram modularHalveProgram

theorem hornerProgram_slots256 (n start : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (hi : input.length=256) (ha : acc.length=256) (hk : bits.length=256) :
    (hornerProgram n start controls input acc bits p c r t f).2.gateSlots ≤ 30728*controls.length := by
  induction controls generalizing start with
  | nil => exact Nat.zero_le _
  | cons q qs ih =>
    have hb := ih start
    have hadd (s : Nat) := modularAddProgram_slots256 n s input acc bits p q c r t f hi ha hk
    have hdbl (s : Nat) := modularDoubleProgram_slots256 n s acc input bits p f r t c ha hi hk
    by_cases hz : qs=[]
    · subst qs
      simp only [hornerProgram,appendCompiled_slots,Straight.gateSlots,List.length_cons,List.length_nil]
      grind only
    · rw [hornerProgram]
      simp only [appendCompiled_slots,compiledIf_slots,hz,ite_false,List.length_cons]
      grind only

theorem hornerInverseProgram_slots256 (n start : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (hi : input.length=256) (ha : acc.length=256) (hk : bits.length=256) :
    (hornerInverseProgram n start controls input acc bits p c r t f).2.gateSlots ≤ 30728*controls.length := by
  induction controls generalizing start with
  | nil => exact Nat.zero_le _
  | cons q qs ih =>
    have hsub (s : Nat) := modularSubProgram_slots256 n s input acc bits p q c r t f hi ha hk
    have hhalf (s : Nat) := modularHalveProgram_slots256 n s acc input bits p f r t c ha hi hk
    by_cases hz : qs=[]
    · subst qs
      simp only [hornerInverseProgram,appendCompiled_slots,compiledIf_slots,ite_true,Straight.gateSlots,List.length_cons,List.length_nil]
      grind only
    · rw [hornerInverseProgram]
      simp only [appendCompiled_slots,compiledIf_slots,hz,ite_false,List.length_cons]
      grind only

theorem squareAddProgram_slots256 (n start : Nat) (input acc : List Wire) (bits : List Bool)
    (p : Nat) (q copied c r t f : Wire) (hi : input.length=256) (ha : acc.length=256) (hk : bits.length=256) :
    (squareAddProgram n start input acc bits p q copied c r t f).2.gateSlots ≤ 16905 := by
  have h := modularAddProgram_slots256 n start input acc bits p copied c r t f hi ha hk
  simp only [squareAddProgram,prependCompiled_slots,appendCompiled_slots,literalProgram_slots,List.length_cons,List.length_nil]
  omega

theorem squareSubProgram_slots256 (n start : Nat) (input acc : List Wire) (bits : List Bool)
    (p : Nat) (q copied c r t f : Wire) (hi : input.length=256) (ha : acc.length=256) (hk : bits.length=256) :
    (squareSubProgram n start input acc bits p q copied c r t f).2.gateSlots ≤ 16905 := by
  have h := modularSubProgram_slots256 n start input acc bits p copied c r t f hi ha hk
  simp only [squareSubProgram,prependCompiled_slots,appendCompiled_slots,literalProgram_slots,List.length_cons,List.length_nil]
  omega

attribute [local irreducible] squareAddProgram squareSubProgram
theorem squareProgram_slots256 (n start : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (copied c r t f : Wire) (hi : input.length=256) (ha : acc.length=256) (hk : bits.length=256) :
    (squareProgram n start controls input acc bits p copied c r t f).2.gateSlots ≤ 30730*controls.length := by
  induction controls generalizing start with
  | nil => exact Nat.zero_le _
  | cons q qs ih =>
    have hb := ih start
    have hadd (s : Nat) := squareAddProgram_slots256 n s input acc bits p q copied c r t f hi ha hk
    have hdbl (s : Nat) := modularDoubleProgram_slots256 n s acc input bits p f r t c ha hi hk
    by_cases hz : qs=[]
    · subst qs
      simp only [squareProgram,appendCompiled_slots,Straight.gateSlots,List.length_cons,List.length_nil]
      grind only
    · rw [squareProgram]
      simp only [appendCompiled_slots,compiledIf_slots,hz,ite_false,List.length_cons]
      grind only

theorem squareInverseProgram_slots256 (n start : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (copied c r t f : Wire) (hi : input.length=256) (ha : acc.length=256) (hk : bits.length=256) :
    (squareInverseProgram n start controls input acc bits p copied c r t f).2.gateSlots ≤ 30730*controls.length := by
  induction controls generalizing start with
  | nil => exact Nat.zero_le _
  | cons q qs ih =>
    have hsub (s : Nat) := squareSubProgram_slots256 n s input acc bits p q copied c r t f hi ha hk
    have hhalf (s : Nat) := modularHalveProgram_slots256 n s acc input bits p f r t c ha hi hk
    by_cases hz : qs=[]
    · subst qs
      simp only [squareInverseProgram,appendCompiled_slots,compiledIf_slots,ite_true,Straight.gateSlots,List.length_cons,List.length_nil]
      grind only
    · rw [squareInverseProgram]
      simp only [appendCompiled_slots,compiledIf_slots,hz,ite_false,List.length_cons]
      grind only

attribute [local irreducible] squareProgram squareInverseProgram

theorem squareSubtractProgram_slots256 (n start : Nat) (x y acc : List Wire) (correction modulus : List Bool)
    (p : Nat) (q copied c r t f : Wire) (hx : x.length=256) (hy : y.length=256) (ha : acc.length=256)
    (hk : correction.length=256) (hm : modulus.length=256) :
    (squareSubtractProgram n start x y acc correction modulus p q copied c r t f).2.gateSlots ≤ 15750663 := by
  have hs (s : Nat) := squareProgram_slots256 n s y y acc correction p copied c r t f hy ha hk
  have hu (s : Nat) := squareInverseProgram_slots256 n s y y acc modulus p copied c r t f hy ha hm
  have hb (s : Nat) := modularSubProgram_slots256 n s acc x modulus p q copied f r c ha hx hm
  simp only [squareSubtractProgram,appendCompiled_slots]
  simp only [hy] at hs hu
  grind only

theorem fieldLeaf_slots {n : Nat} (row : Fin n) (field : PointField) (q : Wire) :
    (fieldLeaf row field q).length=256 := by
  simp only [fieldLeaf,lookupLeafGates,List.length_map,List.length_zip,fieldRefs,List.length_ofFn,List.length_range']
  rfl

theorem fieldLoadProgram_slots (field : PointField) (start : Nat) :
    (fieldLoadProgram field start).gateSlots ≤ 8716278 := by
  simp only [fieldLoadProgram,castFinish_gateSlots,lookupProgram_slots,fieldLoadOps]
  have h := unaryLookupOps_slots_le
    (fun l q => fieldLeaf (⟨l%32768,Nat.mod_lt _ (by decide)⟩ : Fin 32768) field q)
    256 (fun l q => (fieldLeaf_slots _ field q).le)
    (tableAddressTree pointLookupAddress 0 1) 836 pointLookupPath
  have hn := tableAddressTree_nodes pointLookupAddress 0 1
  change (tableAddressTree pointLookupAddress 0 1).internalNodes + 1 = 32768 at hn
  omega

theorem fieldLookupAddProgram_slots (field : PointField) (acc : List Wire) (start : Nat)
    (ha : acc.length=256) : (fieldLookupAddProgram field acc start).2.gateSlots ≤ 17449459 := by
  have h (s : Nat) := fieldLoadProgram_slots field s
  have ha' (s : Nat) := modularAddProgram_slots256 32768 s (List.range' 7 256) acc
    secp256k1ReductionConstantBits ShorECDLP.p 836 559 560 561 558
    (by simp only [List.length_range']) ha (by simp [secp256k1ReductionConstantBits])
  simp only [fieldLookupAddProgram,appendCompiled_slots]
  grind only

theorem signedFieldProgram_slots (field : PointField) (start : Nat) :
    (signedFieldProgram field start).2.gateSlots ≤ 17502203 := by
  have hy (s : Nat) := yNegateProgram_slots_le s
  have hf (s : Nat) := fieldLookupAddProgram_slots field (List.range' 580 256) s (by simp only [List.length_range'])
  simp only [signedFieldProgram,appendCompiled_slots]
  grind only

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/DecoderSlots ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/DecoderSlots.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

theorem andEraseProgram_slots (n s : Nat) (a b w : Wire) :
    (andEraseProgram n s a b w).gateSlots=3 := by
  simp only [andEraseProgram,Straight.gateSlots,recordGates_slots,controlledZ,List.length_cons,List.length_nil]

theorem vchainTailProgram_slots (n : Nat) (controls : List Wire) (acc target : Wire)
    (scratch : List Wire) (start : Nat) :
    (vchainTailProgram n controls acc target scratch start).2.gateSlots ≤ 4*controls.length := by
  induction controls generalizing acc scratch start with
  | nil => exact Nat.zero_le _
  | cons c cs ih =>
    cases cs with
    | nil => simp only [vchainTailProgram,literalProgram_slots,List.length_cons,List.length_nil]; decide
    | cons c' cs =>
      cases scratch with
      | nil => exact Nat.zero_le _
      | cons work scratch =>
        have h := ih work scratch start
        simp only [vchainTailProgram,prependCompiled_slots,appendCompiled_slots,andEraseProgram_slots,
          List.length_cons,List.length_nil]
        simp only [List.length_cons] at h
        omega

theorem vchainProgram_slots (n start : Nat) (controls : List Wire) (target : Wire) (scratch : List Wire) :
    (vchainProgram n start controls target scratch).2.gateSlots ≤ 4*controls.length+1 := by
  cases controls with
  | nil => simp only [vchainProgram,literalProgram_slots,List.length_cons,List.length_nil]; decide
  | cons a rest =>
    cases rest with
    | nil => simp only [vchainProgram,literalProgram_slots,List.length_cons,List.length_nil]; decide
    | cons b bs =>
      have h := vchainTailProgram_slots n (a::bs) b target scratch start
      change (vchainTailProgram n (a::bs) b target scratch start).2.gateSlots ≤ _
      simp only [List.length_cons] at h ⊢
      omega

theorem zeroEraseProgram_slots (n s : Nat) (a b w : Wire) :
    (zeroEraseProgram n s a b w).2.gateSlots=5 := by
  simp only [zeroEraseProgram,prependCompiled_slots,appendCompiled_slots,andEraseProgram_slots,
    literalProgram_slots,List.length_cons,List.length_nil]

theorem unaryProgram_slots_le (n : Nat) (order : UnaryOrder)
    (leaf : (label : Nat) → (control : Wire) → (start : Nat) →
      (count : Nat) × Straight n start (start+count))
    (bound : Nat) (hl : ∀ l q s, (leaf l q s).2.gateSlots ≤ bound)
    (tree : UnaryActionTree) (q : Wire) (paths : List Wire) (start : Nat) :
    (unaryProgram n order leaf tree q paths start).2.gateSlots ≤
      bound*(tree.internalNodes+1)+10*tree.internalNodes := by
  induction tree generalizing q paths start with
  | leaf l =>
    rw [unaryProgram]
    simpa only [UnaryActionTree.internalNodes,Nat.zero_add,Nat.mul_one,Nat.mul_zero,Nat.add_zero] using hl l q start
  | node bit zero one ihz iho =>
    cases paths with
    | nil => rw [unaryProgram]; exact Nat.zero_le _
    | cons path rest =>
      have hz (s : Nat) := ihz path rest s
      have ho (s : Nat) := iho path rest s
      rw [unaryProgram]
      cases order <;>
        simp only [compiledIf_slots,ite_true,reduceCtorEq,ite_false,
          prependCompiled_slots,appendCompiled_slots,zeroEraseProgram_slots,computeZeroAnd,
          List.length_cons,List.length_nil,UnaryActionTree.internalNodes]
      all_goals grind only

theorem zeroMaskFrom_length_le (register : List Wire) (v k : Nat) :
    (zeroMaskFrom register v k).length ≤ register.length := by
  induction register generalizing k with
  | nil => rfl
  | cons w ws ih =>
    simp only [zeroMaskFrom,List.length_append,List.length_cons]
    have h := ih (k+1)
    split <;> simp only [List.length_cons,List.length_nil] <;> omega

theorem equalityProgram_slots (n start : Nat) (register : List Wire) (value : Nat) (flag : Wire)
    (scratch : List Wire) :
    (equalityProgram n start register value flag scratch).2.gateSlots ≤ 6*register.length+1 := by
  have hb := vchainProgram_slots n start register flag scratch
  have hm := zeroMaskFrom_length_le register value 0
  simp only [equalityProgram,prependCompiled_slots,appendCompiled_slots,literalProgram_slots,zeroMask]
  omega

theorem toggleEqualityProgram_slots (n start : Nat) (root : Wire) (register : List Wire) (value : Nat)
    (acc flag : Wire) (scratch : List Wire) :
    (toggleEqualityProgram n start root register value acc flag scratch).2.gateSlots ≤ 12*register.length+3 := by
  have he (s : Nat) := equalityProgram_slots n s register value flag scratch
  simp only [toggleEqualityProgram,appendCompiled_slots,prependCompiled_slots,List.length_cons,List.length_nil]
  grind only

theorem rippleMajProgram_slots (n start : Nat) (control target addend carry scratch : Wire) :
    (rippleMajProgram n start control target addend carry scratch).2.gateSlots ≤ 16 := by
  have h := vchainProgram_slots n start ([control,target,addend] : List Wire) carry ([scratch] : List Wire)
  simp only [List.length_cons,List.length_nil] at h
  simp only [rippleMajProgram,prependCompiled_slots,List.length_cons,List.length_nil]
  omega

theorem rippleUmaProgram_slots (n start : Nat) (control target addend carry scratch : Wire) :
    (rippleUmaProgram n start control target addend carry scratch).2.gateSlots ≤ 16 := by
  have h := vchainProgram_slots n start ([control,target,addend] : List Wire) carry ([scratch] : List Wire)
  simp only [List.length_cons,List.length_nil] at h
  simp only [rippleUmaProgram,appendCompiled_slots,literalProgram_slots,List.length_cons,List.length_nil]
  omega

theorem rippleMajInvProgram_slots (n start : Nat) (control target addend carry scratch : Wire) :
    (rippleMajInvProgram n start control target addend carry scratch).2.gateSlots ≤ 16 := by
  have h := vchainProgram_slots n start ([control,target,addend] : List Wire) carry ([scratch] : List Wire)
  simp only [List.length_cons,List.length_nil] at h
  simp only [rippleMajInvProgram,appendCompiled_slots,literalProgram_slots,List.length_cons,List.length_nil]
  omega

theorem rippleUmaInvProgram_slots (n start : Nat) (control target addend carry scratch : Wire) :
    (rippleUmaInvProgram n start control target addend carry scratch).2.gateSlots ≤ 16 := by
  have h := vchainProgram_slots n start ([control,target,addend] : List Wire) carry ([scratch] : List Wire)
  simp only [List.length_cons,List.length_nil] at h
  simp only [rippleUmaInvProgram,prependCompiled_slots,List.length_cons,List.length_nil]
  omega

theorem dualEraseProgram_slots (n s : Nat) (a i x b j y : Wire) :
    (dualEraseProgram n s a i x b j y).2.gateSlots=10 := by
  simp only [dualEraseProgram,appendCompiled_slots,zeroEraseProgram_slots]

theorem dualProgram_slots_le (n : Nat) (order : UnaryOrder)
    (leaf : (label : Nat) → (a b : Wire) → (start : Nat) →
      (count : Nat) × Straight n start (start+count))
    (bound : Nat) (hl : ∀ l a b s, (leaf l a b s).2.gateSlots ≤ bound)
    (tree : DualUnaryActionTree) (a b : Wire) (xs ys : List Wire) (start : Nat) :
    (dualProgram n order leaf tree a b xs ys start).2.gateSlots ≤
      bound*(tree.internalNodes+1)+20*tree.internalNodes := by
  induction tree generalizing a b xs ys start with
  | leaf l =>
    rw [dualProgram]
    simpa only [DualUnaryActionTree.internalNodes,Nat.zero_add,Nat.mul_one,Nat.mul_zero,Nat.add_zero] using hl l a b start
  | node i j zero one ihz iho =>
    cases xs with
    | nil =>
      rw [dualProgram]
      · exact Nat.zero_le _
      · simp
    | cons x xs =>
      cases ys with
      | nil =>
        rw [dualProgram]
        · exact Nat.zero_le _
        · simp
      | cons y ys =>
        have hz (s : Nat) := ihz x y xs ys s
        have ho (s : Nat) := iho x y xs ys s
        rw [dualProgram]
        cases order <;>
          simp only [compiledIf_slots,ite_true,reduceCtorEq,ite_false,
            prependCompiled_slots,appendCompiled_slots,dualEraseProgram_slots,computeZeroAnd,
            List.length_cons,List.length_nil,DualUnaryActionTree.internalNodes]
        all_goals grind only

theorem rippleFirstProgram_slots (n start : Nat) (mode : RippleMode) (control target addend carry scratch : Wire) :
    (rippleFirstProgram n start mode control target addend carry scratch).2.gateSlots ≤ 16 := by
  cases mode
  · exact rippleMajProgram_slots n start control target addend carry scratch
  · exact rippleUmaInvProgram_slots n start control target addend carry scratch

theorem rippleSecondProgram_slots (n start : Nat) (mode : RippleMode) (control target addend carry scratch : Wire) :
    (rippleSecondProgram n start mode control target addend carry scratch).2.gateSlots ≤ 16 := by
  cases mode
  · exact rippleUmaProgram_slots n start control target addend carry scratch
  · exact rippleMajInvProgram_slots n start control target addend carry scratch

theorem endpointLeafToggle_length_le (topSpecial : Bool) (label : Nat) (endpoint control acc : Wire) :
    (endpointLeafToggle topSpecial label endpoint control acc).length ≤ 3 := by
  unfold endpointLeafToggle
  split <;> simp only [List.length_cons,List.length_nil] <;> decide

theorem intervalFirstProgram_slots (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc target addend carry scratch : Wire) (label : Nat)
    (rightControl leftControl : Wire) :
    (intervalFirstProgram n start mode topSpecial rightTop leftTop acc target addend carry scratch label rightControl leftControl).2.gateSlots ≤ 22 := by
  have hr := endpointLeafToggle_length_le topSpecial label rightTop rightControl acc
  have hl := endpointLeafToggle_length_le topSpecial label leftTop leftControl acc
  have hc (s : Nat) := rippleFirstProgram_slots n s mode acc target addend carry scratch
  simp only [intervalFirstProgram,prependCompiled_slots,appendCompiled_slots,literalProgram_slots]
  grind only

theorem intervalSecondProgram_slots (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc target addend carry scratch : Wire) (label : Nat)
    (rightControl leftControl : Wire) :
    (intervalSecondProgram n start mode topSpecial rightTop leftTop acc target addend carry scratch label rightControl leftControl).2.gateSlots ≤ 22 := by
  have hr := endpointLeafToggle_length_le topSpecial label rightTop rightControl acc
  have hl := endpointLeafToggle_length_le topSpecial label leftTop leftControl acc
  have hc (s : Nat) := rippleSecondProgram_slots n s mode acc target addend carry scratch
  simp only [intervalSecondProgram,prependCompiled_slots,appendCompiled_slots,literalProgram_slots]
  grind only

theorem topFirstProgram_slots (n start : Nat) (mode : RippleMode) (value : Nat)
    (rightRegister leftRegister : List Wire) (acc target addend carry work flag : Wire)
    (scratch : List Wire) (rightRoot leftRoot : Wire) :
    (topFirstProgram n start mode value rightRegister leftRegister acc target addend carry work flag scratch rightRoot leftRoot).2.gateSlots ≤
      12*rightRegister.length+12*leftRegister.length+22 := by
  have hr (s : Nat) := toggleEqualityProgram_slots n s rightRoot rightRegister value acc flag scratch
  have hl (s : Nat) := toggleEqualityProgram_slots n s leftRoot leftRegister value acc flag scratch
  have hc (s : Nat) := rippleFirstProgram_slots n s mode acc target addend carry work
  simp only [topFirstProgram,appendCompiled_slots]
  grind only

theorem topSecondProgram_slots (n start : Nat) (mode : RippleMode) (value : Nat)
    (rightRegister leftRegister : List Wire) (acc target addend carry work flag : Wire)
    (scratch : List Wire) (rightRoot leftRoot : Wire) :
    (topSecondProgram n start mode value rightRegister leftRegister acc target addend carry work flag scratch rightRoot leftRoot).2.gateSlots ≤
      12*rightRegister.length+12*leftRegister.length+22 := by
  have hr (s : Nat) := toggleEqualityProgram_slots n s rightRoot rightRegister value acc flag scratch
  have hl (s : Nat) := toggleEqualityProgram_slots n s leftRoot leftRegister value acc flag scratch
  have hc (s : Nat) := rippleSecondProgram_slots n s mode acc target addend carry work
  simp only [topSecondProgram,appendCompiled_slots]
  grind only

theorem traversalFirstProgram_slots (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc carry scratch : Wire) (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire) (rightPaths leftPaths : List Wire) :
    (traversalFirstProgram n start mode topSpecial rightTop leftTop acc carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).2.gateSlots ≤
      22*(tree.internalNodes+1)+20*tree.internalNodes := by
  unfold traversalFirstProgram
  apply dualProgram_slots_le
  intro label right left cursor
  exact intervalFirstProgram_slots n cursor mode topSpecial rightTop leftTop acc (targetAt label) (addendAt label) carry scratch label right left

theorem traversalSecondProgram_slots (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc carry scratch : Wire) (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire) (rightPaths leftPaths : List Wire) :
    (traversalSecondProgram n start mode topSpecial rightTop leftTop acc carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).2.gateSlots ≤
      22*(tree.internalNodes+1)+20*tree.internalNodes := by
  unfold traversalSecondProgram
  apply dualProgram_slots_le
  intro label right left cursor
  exact intervalSecondProgram_slots n cursor mode topSpecial rightTop leftTop acc (targetAt label) (addendAt label) carry scratch label right left

theorem intervalTopFirstProgram_slots (n start : Nat) (r : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (target : IntervalTarget) :
    (intervalTopFirstProgram n start r k K mode target).2.gateSlots ≤ 12*r.lengthS.length+12*r.lengthQ.length+22 := by
  simp only [intervalTopFirstProgram,compiledIf_slots]
  split
  · exact topFirstProgram_slots n start mode (intervalTopRelative k K) r.lengthS r.lengthQ
      (r.accumulator k K) (r.targetAt target (intervalTopRelative k K)) (r.addendAt target (intervalTopRelative k K))
      (r.carry k K) (r.cellScratch k K) (r.cellScratch k K) (r.equalityScratch k K) r.control r.control
  · exact Nat.zero_le _

theorem intervalTopSecondProgram_slots (n start : Nat) (r : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (target : IntervalTarget) :
    (intervalTopSecondProgram n start r k K mode target).2.gateSlots ≤ 12*r.lengthS.length+12*r.lengthQ.length+22 := by
  simp only [intervalTopSecondProgram,compiledIf_slots]
  split
  · exact topSecondProgram_slots n start mode (intervalTopRelative k K) r.lengthS r.lengthQ
      (r.accumulator k K) (r.targetAt target (intervalTopRelative k K)) (r.addendAt target (intervalTopRelative k K))
      (r.carry k K) (r.cellScratch k K) (r.cellScratch k K) (r.equalityScratch k K) r.control r.control
  · exact Nat.zero_le _

theorem prepareIntervalEndpoints_length9 (t q s scratch : List Wire) (carry : Wire) (width k : Nat)
    (ht : t.length=9) (hq : q.length=9) (hs : s.length=9) (hw : 9≤scratch.length) :
    (prepareIntervalEndpoints t q s scratch carry width k).length ≤ 376 := by
  have hb (v : Nat) : (constantBits 9 v).count true ≤ 9 := by
    have h := List.count_le_length (l := constantBits 9 v) (a := true)
    simpa only [constantBits_length] using h
  rw [circuit_length_primitive,prepareIntervalEndpoints9_primitive _ _ _ _ _ _ _ ht hq hs hw]
  dsimp only [PrimitiveResources.x,PrimitiveResources.h,PrimitiveResources.cnot,PrimitiveResources.toffoli,PrimitiveResources.phase]
  have h4 := hb 4
  have hn := hb (width+2)
  have hk := hb k
  omega

theorem restoreIntervalEndpoints_length9 (t q s scratch : List Wire) (carry : Wire) (width k : Nat)
    (ht : t.length=9) (hq : q.length=9) (hs : s.length=9) (hw : 9≤scratch.length) :
    (restoreIntervalEndpoints t q s scratch carry width k).length ≤ 376 := by
  have hb (v : Nat) : (constantBits 9 v).count true ≤ 9 := by
    have h := List.count_le_length (l := constantBits 9 v) (a := true)
    simpa only [constantBits_length] using h
  rw [circuit_length_primitive,restoreIntervalEndpoints9_primitive _ _ _ _ _ _ _ ht hq hs hw]
  dsimp only [PrimitiveResources.x,PrimitiveResources.h,PrimitiveResources.cnot,PrimitiveResources.toffoli,PrimitiveResources.phase]
  have h4 := hb 4
  have hn := hb (width+2)
  have hk := hb k
  omega

theorem intervalSignUpdate_length_le (r : IntervalRegisters) (k K : Nat) (signUpdate : Bool) :
    (intervalSignUpdate r k K signUpdate).length ≤ 1 := by
  cases signUpdate <;> simp only [intervalSignUpdate,Bool.false_eq_true,ite_false,ite_true,List.length_cons,List.length_nil] <;> decide

theorem intervalProgram_slots9 (n start : Nat) (r : IntervalRegisters) (width k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget)
    (ht : r.lengthT.length=9) (hq : r.lengthQ.length=9) (hs : r.lengthS.length=9)
    (hw : 9≤r.endpointScratch.length) :
    (intervalProgram n start r width k K mode signUpdate target).2.gateSlots ≤
      84*(intervalTree r k K).internalNodes+1273 := by
  have hp := prepareIntervalEndpoints_length9 r.lengthT r.lengthQ r.lengthS r.endpointScratch (r.carry k K) width k ht hq hs hw
  have hr := restoreIntervalEndpoints_length9 r.lengthT r.lengthQ r.lengthS r.endpointScratch (r.carry k K) width k ht hq hs hw
  have hsg := intervalSignUpdate_length_le r k K signUpdate
  have ht1 (s : Nat) := intervalTopFirstProgram_slots n s r k K mode target
  have ht2 (s : Nat) := intervalTopSecondProgram_slots n s r k K mode target
  have hf (s : Nat) := traversalFirstProgram_slots n s mode (intervalHasTopSpecial k K)
    (r.rightTop k K) (r.leftTop k K) (r.accumulator k K) (r.carry k K) (r.cellScratch k K)
    (r.targetAt target) (r.addendAt target) (intervalTree r k K) r.control r.control (r.rightPaths k K) (r.leftPaths k K)
  have hb (s : Nat) := traversalSecondProgram_slots n s mode (intervalHasTopSpecial k K)
    (r.rightTop k K) (r.leftTop k K) (r.accumulator k K) (r.carry k K) (r.cellScratch k K)
    (r.targetAt target) (r.addendAt target) (intervalTree r k K) r.control r.control (r.rightPaths k K) (r.leftPaths k K)
  simp only [hs,hq] at ht1 ht2
  simp only [intervalProgram,prependCompiled_slots,appendCompiled_slots,literalProgram_slots]
  grind only

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/EEACellSlots ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/EEACellSlots.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

theorem sequenceProgram_slots_le (n : Nat) (ps : List (FixedSegment n)) (bounds : List Nat)
    (h : List.Forall₂ (fun p bound => ∀ s, (p s).2.gateSlots ≤ bound) ps bounds) (start : Nat) :
    (sequenceProgram n ps start).2.gateSlots ≤ bounds.sum := by
  induction h generalizing start with
  | nil => exact Nat.zero_le _
  | cons hp hs ih =>
    rw [sequenceProgram,appendCompiled_slots]
    simp only [List.sum_cons]
    exact Nat.add_le_add (hp start) (ih _)

theorem coefficientFirstProgram_slots (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (label : Nat) (control : Wire) :
    (coefficientFirstProgram n start r k K mode target label control).2.gateSlots ≤ 17 := by
  have h := rippleFirstProgram_slots n start mode (r.accumulator k K) (r.targetAt target k label)
    (r.addendAt target k label) (r.carry k K) (r.cellScratch k K)
  simp only [coefficientFirstProgram,appendCompiled_slots,literalProgram_slots,List.length_cons,List.length_nil]
  omega

theorem coefficientSecondProgram_slots (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (label : Nat) (control : Wire) :
    (coefficientSecondProgram n start r k K mode target label control).2.gateSlots ≤ 17 := by
  have h := rippleSecondProgram_slots n start mode (r.accumulator k K) (r.targetAt target k label)
    (r.addendAt target k label) (r.carry k K) (r.cellScratch k K)
  simp only [coefficientSecondProgram,prependCompiled_slots,List.length_cons,List.length_nil]
  omega

theorem coefficientProgram_slots (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget) :
    (coefficientProgram n start r k K mode signUpdate target).2.gateSlots ≤
      54*(coefficientPrefixTree r k K).internalNodes+37 := by
  have hf (s : Nat) := unaryProgram_slots_le n .inc
    (fun label control cursor => coefficientFirstProgram n cursor r k K mode target label control)
    17 (fun label control cursor => coefficientFirstProgram_slots n cursor r k K mode target label control)
    (coefficientPrefixTree r k K) r.control (r.path k K) s
  have hb (s : Nat) := unaryProgram_slots_le n .dec
    (fun label control cursor => coefficientSecondProgram n cursor r k K mode target label control)
    17 (fun label control cursor => coefficientSecondProgram_slots n cursor r k K mode target label control)
    (coefficientPrefixTree r k K) r.control (r.path k K) s
  have hs : (coefficientPrefixSignCircuit r k K signUpdate).length ≤ 1 := by
    cases signUpdate <;> simp only [coefficientPrefixSignCircuit,Bool.false_eq_true,ite_false,ite_true,List.length_cons,List.length_nil] <;> decide
  simp only [coefficientProgram,appendCompiled_slots,prependCompiled_slots,literalProgram_slots,List.length_cons,List.length_nil]
  grind only
theorem phaseSegments_slots (n start : Nat) (r : PhaseUpdateRegisters) (shift : Wire) (core : Circuit) :
    (sequenceProgram n (phaseSegments n r shift core) start).2.gateSlots ≤
      8*(r.lengthQ.length+r.lengthRPrime.length+r.lengthS.length)+18+core.length := by
  let inner := r.withShiftEpoch shift
  let a := 4*inner.lengthQ.length+1
  let b := 4*inner.lengthRPrime.length+1
  let c := 4*inner.lengthS.length+1
  have h : List.Forall₂ (fun p bound => ∀ s, (p s).2.gateSlots ≤ bound)
      (phaseSegments n r shift core) ([a,b,1,c,1,core.length,1,c,1,b,a] : List Nat) := by
    unfold phaseSegments
    repeat' apply List.Forall₂.cons
    all_goals first | exact List.Forall₂.nil | intro cursor
    all_goals first | exact vchainProgram_slots n cursor _ _ _ | (simp only [literalProgram_slots,List.length_cons,List.length_nil]; rfl)
  have hb := sequenceProgram_slots_le n _ _ h start
  simp only [List.sum_cons,List.sum_nil,a,b,c,inner,PhaseUpdateRegisters.withShiftEpoch,
    List.length_append,List.length_cons,List.length_nil] at hb
  omega

theorem phaseProgram_slots (n start : Nat) (r : PhaseUpdateRegisters) (shift : Wire) :
    (phaseProgram n start r shift).2.gateSlots ≤
      8*(r.lengthQ.length+r.lengthRPrime.length+r.lengthS.length)+32 := by
  have h := phaseSegments_slots n start r shift (phaseCoreGates (r.withShiftEpoch shift))
  simp only [phaseCoreGates,List.length_cons,List.length_nil] at h
  exact h

theorem phaseInverseProgram_slots (n start : Nat) (r : PhaseUpdateRegisters) (shift : Wire) :
    (phaseInverseProgram n start r shift).2.gateSlots ≤
      8*(r.lengthQ.length+r.lengthRPrime.length+r.lengthS.length)+32 := by
  have h := phaseSegments_slots n start r shift (phaseInverseCoreGates (r.withShiftEpoch shift))
  simp only [phaseInverseCoreGates,List.length_cons,List.length_nil] at h
  exact h

theorem zeroCellProgram_slots (n start : Nat) (base : Bool) (r bit guard target temporary : Wire) :
    (zeroCellProgram n start base r bit guard target temporary).2.gateSlots ≤ 7 := by
  cases base <;> simp only [zeroCellProgram,prependCompiled_slots,andEraseProgram_slots,measuredZeroPrefix,
    Bool.false_eq_true,ite_false,ite_true,List.length_append,List.length_cons,List.length_nil] <;> decide

theorem upperForwardLeafProgram_slots (n start k K : Nat) (control temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire) :
    (upperForwardLeafProgram n start k K control temporary bitAt dirtyAt label r).2.gateSlots ≤ 7 := by
  simp only [upperForwardLeafProgram,compiledIf_slots]
  split
  · split <;> exact zeroCellProgram_slots n start _ _ _ _ _ _
  · exact Nat.zero_le _

theorem upperReverseLeafProgram_slots (n start k K : Nat) (temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire) :
    (upperReverseLeafProgram n start k K temporary bitAt dirtyAt label r).2.gateSlots ≤ 7 := by
  simp only [upperReverseLeafProgram,compiledIf_slots]
  split
  · exact zeroCellProgram_slots n start _ _ _ _ _ _
  · exact Nat.zero_le _

theorem lowerForwardLeafProgram_slots (n start k K : Nat) (control temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire) :
    (lowerForwardLeafProgram n start k K control temporary bitAt dirtyAt label r).2.gateSlots ≤ 7 := by
  simp only [lowerForwardLeafProgram,compiledIf_slots]
  split
  · split <;> exact zeroCellProgram_slots n start _ _ _ _ _ _
  · exact Nat.zero_le _

theorem lowerReverseLeafProgram_slots (n start k K : Nat) (temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire) :
    (lowerReverseLeafProgram n start k K temporary bitAt dirtyAt label r).2.gateSlots ≤ 7 := by
  simp only [lowerReverseLeafProgram,compiledIf_slots]
  split
  · exact zeroCellProgram_slots n start _ _ _ _ _ _
  · exact Nat.zero_le _

theorem rangeLeafProgram_slots (n : Nat) (after : Bool) (r : Wire)
    (leaf : Nat → Wire → FixedSegment n) (bound : Nat)
    (hl : ∀ label control cursor, (leaf label control cursor).2.gateSlots ≤ bound)
    (label : Nat) (dynamic : Wire) (start : Nat) :
    (rangeLeafProgram n after r leaf label dynamic start).2.gateSlots ≤ bound+1 := by
  have h := hl label r start
  cases after <;> simp only [rangeLeafProgram,compiledIf_slots,Bool.false_eq_true,ite_false,ite_true,
    appendCompiled_slots,prependCompiled_slots,literalProgram_slots,List.length_cons,List.length_nil] <;> omega

theorem rangeScanProgram_slots (n : Nat) (after : Bool) (order : UnaryOrder)
    (tree : UnaryActionTree) (control r : Wire) (path : List Wire)
    (leaf : Nat → Wire → FixedSegment n) (bound : Nat)
    (hl : ∀ label dynamic cursor, (leaf label dynamic cursor).2.gateSlots ≤ bound) (start : Nat) :
    (rangeScanProgram n after order tree control r path leaf start).2.gateSlots ≤
      (bound+1)*(tree.internalNodes+1)+10*tree.internalNodes+1 := by
  have h (a : Bool) := unaryProgram_slots_le n order (rangeLeafProgram n a r leaf) (bound+1)
    (fun label dynamic cursor => rangeLeafProgram_slots n a r leaf bound hl label dynamic cursor)
    tree control path start
  have hf := h false
  have ht := h true
  cases after <;> simp only [rangeScanProgram,compiledIf_slots,Bool.false_eq_true,ite_false,ite_true,
    appendCompiled_slots,prependCompiled_slots,literalProgram_slots,List.length_cons,List.length_nil] <;> omega

theorem upperMapProgram_slots (n k K : Nat) (tree : UnaryActionTree) (control r t : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) (start : Nat) :
    (upperMapProgram n k K tree control r t path bitAt dirtyAt start).2.gateSlots ≤ 36*tree.internalNodes+18 := by
  have hf (s : Nat) := rangeScanProgram_slots n true .inc tree control r path
    (fun label dynamic cursor => upperForwardLeafProgram n cursor k K control t bitAt dirtyAt label dynamic) 7
    (fun label dynamic cursor => upperForwardLeafProgram_slots n cursor k K control t bitAt dirtyAt label dynamic) s
  have hb (s : Nat) := rangeScanProgram_slots n false .dec tree control r path
    (fun label dynamic cursor => upperReverseLeafProgram n cursor k K t bitAt dirtyAt label dynamic) 7
    (fun label dynamic cursor => upperReverseLeafProgram_slots n cursor k K t bitAt dirtyAt label dynamic) s
  simp only [upperMapProgram,appendCompiled_slots]
  grind only

theorem lowerMapProgram_slots (n k K : Nat) (tree : UnaryActionTree) (control r t : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) (start : Nat) :
    (lowerMapProgram n k K tree control r t path bitAt dirtyAt start).2.gateSlots ≤ 36*tree.internalNodes+18 := by
  have hf (s : Nat) := rangeScanProgram_slots n true .dec tree control r path
    (fun label dynamic cursor => lowerForwardLeafProgram n cursor k K control t bitAt dirtyAt label dynamic) 7
    (fun label dynamic cursor => lowerForwardLeafProgram_slots n cursor k K control t bitAt dirtyAt label dynamic) s
  have hb (s : Nat) := rangeScanProgram_slots n false .inc tree control r path
    (fun label dynamic cursor => lowerReverseLeafProgram n cursor k K t bitAt dirtyAt label dynamic) 7
    (fun label dynamic cursor => lowerReverseLeafProgram_slots n cursor k K t bitAt dirtyAt label dynamic) s
  simp only [lowerMapProgram,appendCompiled_slots]
  grind only

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/EEALengthSlots ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/EEALengthSlots.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

theorem controlledXorConstant_length_le (control : Wire) (targets : List Wire) (value : Nat) :
    (controlledXorConstant control targets value).length ≤ targets.length := by
  induction targets generalizing value with
  | nil => exact Nat.zero_le _
  | cons target targets ih =>
    simp only [controlledXorConstant,List.length_append,List.length_cons]
    split <;> simp only [List.length_cons,List.length_nil] <;> have h := ih (value/2) <;> omega

theorem dirtyConstantWrites_length_le (targets : List Wire) (dirtyAt valueAt : Nat → Nat) (labels : List Nat) :
    (dirtyConstantWrites targets dirtyAt valueAt labels).length ≤ labels.length*targets.length := by
  induction labels with
  | nil => exact Nat.zero_le _
  | cons label labels ih =>
    have h := controlledXorConstant_length_le (dirtyAt label) targets (valueAt label)
    simp only [dirtyConstantWrites,List.length_append,List.length_cons]
    nlinarith

theorem upperWriterProgram_slots (n k K : Nat) (tree : UnaryActionTree) (control r t : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) (targets : List Wire) (start : Nat) :
    (upperWriterProgram n k K tree control r t path bitAt dirtyAt targets start).2.gateSlots ≤
      targets.length+2*((zeroMapLabels k K).length*targets.length)+72*tree.internalNodes+36 := by
  have hm (s : Nat) := upperMapProgram_slots n k K tree control r t path bitAt dirtyAt s
  have hs := controlledXorConstant_length_le control targets (truthMinusOneValue targets.length K)
  have hd := dirtyConstantWrites_length_le targets dirtyAt (highestPositionWriteValue targets.length k) (zeroMapLabels k K).reverse
  simp only [List.length_reverse] at hd
  simp only [upperWriterProgram,prependCompiled_slots,appendCompiled_slots,List.length_append,highestPositionDirtyWrites]
  grind only

theorem lowerWriterProgram_slots (n width k K : Nat) (tree : UnaryActionTree) (control r t : Wire) (path : List Wire)
    (bitAt dirtyAt : Nat → Wire) (targets : List Wire) (start : Nat) :
    (lowerWriterProgram n width k K tree control r t path bitAt dirtyAt targets start).2.gateSlots ≤
      targets.length+2*((zeroMapLabels k K).length*targets.length)+72*tree.internalNodes+36 := by
  have hm (s : Nat) := lowerMapProgram_slots n k K tree control r t path bitAt dirtyAt s
  have hs := controlledXorConstant_length_le control targets (rightLengthValue width targets.length k)
  have hd := dirtyConstantWrites_length_le targets dirtyAt (rightLengthWriteValue width targets.length K) (zeroMapLabels k K)
  simp only [lowerWriterProgram,prependCompiled_slots,appendCompiled_slots,List.length_append,rightLengthDirtyWrites]
  grind only

theorem surroundCompiled_slots {n start : Nat} (before after : Circuit)
    (p : (count : Nat) × Straight n start (start+count)) :
    (surroundCompiled before after p).2.gateSlots = before.length+p.2.gateSlots+after.length := by
  simp only [surroundCompiled,prependCompiled_slots,appendCompiled_slots,literalProgram_slots]
  omega


theorem xorConstant_length_le (wires : List Wire) (value : Nat) :
    (xorConstant wires value).length ≤ wires.length := by
  induction wires generalizing value with
  | nil => exact Nat.zero_le _
  | cons w ws ih =>
    simp only [xorConstant,List.length_append,List.length_cons]
    split <;> simp only [List.length_cons,List.length_nil] <;> have h := ih (value/2) <;> omega

theorem cuccaroAdd_length_le (as bs : List Wire) (carry : Wire) :
    (cuccaroAdd as bs carry).length ≤ 6*as.length := by
  induction as generalizing bs carry with
  | nil => cases bs <;> exact Nat.zero_le _
  | cons a as ih =>
    cases bs with
    | nil => exact Nat.zero_le _
    | cons b bs =>
      have h := ih bs a
      simp only [cuccaroAdd,List.length_append,cuccaroMaj,cuccaroUma,List.length_cons,List.length_nil]
      omega

theorem addConstant_length_le (register constants : List Wire) (carry : Wire) (value : Nat) :
    (addConstant register constants carry value).length ≤ 8*constants.length := by
  have h := xorConstant_length_le constants value
  have hc := cuccaroAdd_length_le constants register carry
  simp only [addConstant,List.length_append]
  omega

theorem subConstant_length_le (register constants : List Wire) (carry : Wire) (value : Nat) :
    (subConstant register constants carry value).length ≤ 8*constants.length := by
  have h := xorConstant_length_le constants value
  have hc := cuccaroAdd_length_le constants register carry
  simp only [subConstant,List.length_append,cuccaroSub,circuit_adjoint_length]
  omega

theorem notRegister_length (register : List Wire) : (notRegister register).length=register.length := by
  induction register with
  | nil => rfl
  | cons w ws ih => simpa only [notRegister,List.length_cons] using congrArg Nat.succ ih

theorem incrementTail_length_le (bits : List Wire) (carry : Wire) (carries : List Wire) :
    (incrementTail bits carry carries).length ≤ 3*bits.length := by
  induction bits generalizing carry carries with
  | nil => exact Nat.zero_le _
  | cons bit bits ih =>
    cases bits with
    | nil => cases carries <;> simp [incrementTail]
    | cons next rest =>
      cases carries with
      | nil => exact Nat.zero_le _
      | cons c cs =>
        have h := ih c cs
        simp only [incrementTail,List.length_append,List.length_cons,List.length_nil]
        simp only [List.length_cons] at h
        omega

theorem uncontrolledIncrement_length_le (bits carries : List Wire) :
    (uncontrolledIncrement bits carries).length ≤ 3*bits.length := by
  cases bits with
  | nil => exact Nat.zero_le _
  | cons low bits =>
    cases bits with
    | nil => simp [uncontrolledIncrement]
    | cons next rest =>
      cases carries with
      | nil => exact Nat.zero_le _
      | cons c cs =>
        have h := incrementTail_length_le (next::rest) c (cs.take rest.length)
        simp only [uncontrolledIncrement,List.length_append,List.length_cons,List.length_nil]
        simp only [List.length_cons] at h
        omega

theorem constMinus_length_le (register constants : List Wire) (carry : Wire) (value : Nat) :
    (constMinus register constants carry value).length ≤ 4*register.length+8*constants.length := by
  have h := uncontrolledIncrement_length_le register (constants.take (register.length-1))
  have ha := addConstant_length_le register constants carry value
  simp only [constMinus,List.length_append,notRegister_length]
  omega


theorem ltUpdateProgram_slots (n width k K : Nat) (tree : UnaryActionTree) (control r t carry : Wire)
    (path : List Wire) (work1At work2At : Nat → Wire) (lengthT lengthRP constants : List Wire) (start : Nat) :
    (ltUpdateProgram n width k K tree control r t carry path work1At work2At lengthT lengthRP constants start).2.gateSlots ≤
      2*lengthT.length+4*((zeroMapLabels k K).length*lengthT.length)+144*tree.internalNodes+72+
        8*lengthRP.length+16*constants.length := by
  have h1 (s : Nat) := upperWriterProgram_slots n k K tree control r t path work2At work1At lengthT s
  have h2 (s : Nat) := upperWriterProgram_slots n k K tree control r t path work1At work2At lengthT s
  have hc := constMinus_length_le lengthRP constants carry (width+2)
  simp only [ltUpdateProgram,surroundCompiled_slots,appendCompiled_slots]
  grind only

theorem lrpUpdateProgram_slots (n width k K : Nat) (tree : UnaryActionTree) (control r t carry : Wire)
    (path : List Wire) (work1At work2At : Nat → Wire) (lengthT lengthRP constants : List Wire) (start : Nat) :
    (lrpUpdateProgram n width k K tree control r t carry path work1At work2At lengthT lengthRP constants start).2.gateSlots ≤
      2*lengthRP.length+4*((zeroMapLabels k K).length*lengthRP.length)+144*tree.internalNodes+72+
        16*constants.length := by
  have h1 (s : Nat) := lowerWriterProgram_slots n width k K tree control r t path work1At work2At lengthRP s
  have h2 (s : Nat) := lowerWriterProgram_slots n width k K tree control r t path work2At work1At lengthRP s
  have ha := addConstant_length_le lengthT constants carry 3
  have hs := subConstant_length_le lengthT constants carry 3
  simp only [lrpUpdateProgram,surroundCompiled_slots,appendCompiled_slots]
  grind only


def endUpperSlotBound (r : EndIterationRegisters) (w : EndIterationWindows) : Nat :=
  2*r.lengthT.length+4*((zeroMapLabels w.k4 w.K4).length*r.lengthT.length)+
    144*(r.upperTree w).internalNodes+72+8*r.lengthRP.length+16*r.constants.length

def endLowerSlotBound (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows) : Nat :=
  2*r.lengthRP.length+4*((zeroMapLabels w.k5 (w.K5Decode width)).length*r.lengthRP.length)+
    144*(r.lowerTree width w).internalNodes+72+16*r.constants.length

theorem upperEndProgram_slots (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows) :
    (upperEndProgram n start r width w).2.gateSlots ≤ endUpperSlotBound r w :=
  ltUpdateProgram_slots n width w.k4 w.K4 (r.upperTree w) r.control (r.rangeAccumulator w.k4 w.K4)
    (r.temporary w.k4 w.K4) r.carry (r.path w.k4 w.K4) r.work1At r.work2At r.lengthT r.lengthRP r.constants start

theorem lowerEndProgram_slots (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows) :
    (lowerEndProgram n start r width w).2.gateSlots ≤ endLowerSlotBound r width w :=
  lrpUpdateProgram_slots n width w.k5 (w.K5Decode width) (r.lowerTree width w) r.control
    (r.rangeAccumulator w.k5 (w.K5Decode width)) (r.temporary w.k5 (w.K5Decode width)) r.carry
    (r.path w.k5 (w.K5Decode width)) r.work1At r.work2At r.lengthT r.lengthRP r.constants start

theorem controlledWorkSwap_length_le (control : Wire) (left right : List Wire) :
    (controlledWorkSwap control left right).length ≤ 3*left.length := by
  induction left generalizing right with
  | nil => cases right <;> exact Nat.zero_le _
  | cons l ls ih =>
    cases right with
    | nil => exact Nat.zero_le _
    | cons r rs =>
      have h := ih rs
      simp only [controlledWorkSwap,controlledSwap,List.length_append,List.length_cons,List.length_nil]
      omega

def endSlotBound (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows) : Nat :=
  3*r.work1.length+endUpperSlotBound r w+endLowerSlotBound r width w

theorem endProgram_slots (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows) :
    (endProgram n start r width w).2.gateSlots ≤ endSlotBound r width w := by
  have hu := upperEndProgram_slots n start r width w
  have hl (s : Nat) := lowerEndProgram_slots n s r width w
  have hs := controlledWorkSwap_length_le r.control r.work1 r.work2
  simp only [endProgram,prependCompiled_slots,appendCompiled_slots,endSlotBound]
  grind only

theorem endInverseProgram_slots (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows) :
    (endInverseProgram n start r width w).2.gateSlots ≤ endSlotBound r width w := by
  have hu (s : Nat) := upperEndProgram_slots n s r width w
  have hl := lowerEndProgram_slots n start r width w
  have hs := controlledWorkSwap_length_le r.control r.work1.reverse r.work2.reverse
  simp only [List.length_reverse] at hs
  simp only [endInverseProgram,appendCompiled_slots,literalProgram_slots,controlledWorkSwapInverse,endSlotBound]
  grind only


theorem mcxVChainTail_length_le (acc : Wire) (controls : List Wire) (target : Wire) (scratch : List Wire) :
    (mcxVChainTail acc controls target scratch).length ≤ 2*controls.length := by
  induction controls generalizing acc scratch with
  | nil => exact Nat.zero_le _
  | cons c cs ih =>
    cases cs with
    | nil => simp [mcxVChainTail]
    | cons next rest =>
      cases scratch with
      | nil => exact Nat.zero_le _
      | cons s ss =>
        have h := ih s ss
        simp only [mcxVChainTail,List.length_append,List.length_cons,List.length_nil]
        simp only [List.length_cons] at h
        omega

theorem mcxVChain_length_le (controls : List Wire) (target : Wire) (scratch : List Wire) :
    (mcxVChain controls target scratch).length ≤ 2*controls.length+1 := by
  cases controls with
  | nil => simp [mcxVChain]
  | cons c cs =>
    cases cs with
    | nil => simp [mcxVChain]
    | cons next rest =>
      have h := mcxVChainTail_length_le next (c::rest) target scratch
      simp only [mcxVChain,List.length_cons]
      simp only [List.length_cons] at h
      omega

theorem blockHPrefix_length_le (r : IndexedStepRegisters) :
    (blockHPrefix r).length ≤ 2*r.lengthQ.length+2*r.lengthS.length+7 := by
  have hq := mcxVChain_length_le r.lengthQ (r.sourceScratch.getD 0 0) (r.sourceScratch.drop 2)
  have hs := mcxVChain_length_le (r.lengthS++[r.shiftEpoch]) (r.sourceScratch.getD 1 0) (r.sourceScratch.drop 2)
  simp only [List.length_append,List.length_cons,List.length_nil] at hs
  simp only [blockHPrefix,List.length_append,List.length_cons,List.length_nil]
  omega

theorem blockHSuffix_length_le (r : IndexedStepRegisters) :
    (blockHSuffix r).length ≤ 2*r.lengthQ.length+2*r.lengthS.length+7 := by
  have hq := mcxVChain_length_le r.lengthQ (r.sourceScratch.getD 0 0) (r.sourceScratch.drop 2)
  have hs := mcxVChain_length_le (r.lengthS++[r.shiftEpoch]) (r.sourceScratch.getD 1 0) (r.sourceScratch.drop 2)
  simp only [List.length_append,List.length_cons,List.length_nil] at hs
  simp only [blockHSuffix,List.length_append,List.length_cons,List.length_nil]
  omega

def hSlotBound (r : IndexedStepRegisters) (width T : Nat) : Nat :=
  4*r.lengthQ.length+4*r.lengthS.length+15+
    endSlotBound (r.endIteration width T) width (endIterationWindowsAt width T)

theorem hProgram_slots (n start : Nat) (r : IndexedStepRegisters) (width T : Nat) :
    (hProgram n start r width T).2.gateSlots ≤ hSlotBound r width T := by
  have hp := blockHPrefix_length_le r
  have hs := blockHSuffix_length_le r
  have he := endProgram_slots n start (r.endIteration width T) width (endIterationWindowsAt width T)
  simp only [hProgram,compiledIf_slots]
  split
  · simp only [surroundCompiled_slots,List.length_append,List.length_cons,List.length_nil,hSlotBound]
    omega
  · exact Nat.zero_le _

theorem hInverseProgram_slots (n start : Nat) (r : IndexedStepRegisters) (width T : Nat) :
    (hInverseProgram n start r width T).2.gateSlots ≤ hSlotBound r width T := by
  have hp := blockHPrefix_length_le r
  have hs := blockHSuffix_length_le r
  have he := endInverseProgram_slots n start (r.endIteration width T) width (endIterationWindowsAt width T)
  simp only [hInverseProgram,compiledIf_slots]
  split
  · simp only [surroundCompiled_slots,List.length_append,List.length_cons,List.length_nil,hSlotBound]
    omega
  · exact Nat.zero_le _

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/EEAScheduleSlots ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/EEAScheduleSlots.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

theorem computeControl_length_le (controls : List Wire) (value : Nat) (target : Wire) (scratch : List Wire) :
    (computeControl controls value target scratch).length ≤ 4*controls.length+1 := by
  have hm := zeroMaskFrom_length_le controls value 0
  have hc := mcxVChain_length_le controls target scratch
  simp only [computeControl,List.length_append,circuit_adjoint_length,zeroMask]
  omega

theorem rControlNonterminal_length_le (conditions : List Wire) (value : Nat) (control : Wire)
    (lengthRPrime : List Wire) (zeroRPrime : Wire) (scratch : List Wire) :
    (rControlNonterminal conditions value control lengthRPrime zeroRPrime scratch).length ≤
      4*lengthRPrime.length+4*conditions.length+7 := by
  have hr := mcxVChain_length_le lengthRPrime zeroRPrime scratch
  have hc := computeControl_length_le (conditions++[zeroRPrime]) (value%2^conditions.length) control scratch
  simp only [List.length_append,List.length_cons,List.length_nil] at hc
  simp only [rControlNonterminal,List.length_append]
  omega

theorem blockB2_length_le (r : IndexedStepRegisters) :
    (blockB2 r).length ≤ 8*r.lengthRPrime.length+31 := by
  have h := rControlNonterminal_length_le [r.phase1,r.phase2] 2 r.control r.lengthRPrime r.terminal r.blockScratch
  change ((rControlNonterminal [r.phase1,r.phase2] 2 r.control r.lengthRPrime r.terminal r.blockScratch ++
    [Gate.CX r.control r.sign]) ++ rControlNonterminal [r.phase1,r.phase2] 2 r.control r.lengthRPrime r.terminal r.blockScratch).length ≤ _
  simp only [List.length_cons,List.length_nil] at h
  simp only [List.length_append,List.length_cons,List.length_nil]
  omega

theorem prepareLatestPaperTBoundary_length256 (r : TBoundaryRegisters)
    (hl : TBoundaryLayout r) (hw : r.width=9) :
    (prepareLatestPaperTBoundary r 256).length = 229 := by
  rw [circuit_length_primitive,prepareLatestPaperTBoundary256_primitive r hl hw]
  rfl

theorem restoreLatestPaperTBoundary_length256 (r : TBoundaryRegisters)
    (hl : TBoundaryLayout r) (hw : r.width=9) :
    (restoreLatestPaperTBoundary r 256).length = 229 := by
  rw [circuit_length_primitive,restoreLatestPaperTBoundary256_primitive r hl hw]
  rfl


theorem remainderBlockProgram_slots9 (n start : Nat) (r : IndexedStepRegisters) (width : Nat) (w : ActiveWindow)
    (ht : (r.remainder w).lengthT.length=9) (hq : (r.remainder w).lengthQ.length=9)
    (hs : (r.remainder w).lengthS.length=9) (hw : 9≤(r.remainder w).endpointScratch.length) :
    (remainderBlockProgram n start r width w).2.gateSlots ≤
      24*r.lengthRPrime.length+168*(intervalTree (r.remainder w) w.start w.stop).internalNodes+2633 := by
  let b := 84*(intervalTree (r.remainder w) w.start w.stop).internalNodes+1273
  let a := 4*r.lengthRPrime.length+11
  let c := 4*r.lengthRPrime.length+17
  have hi (s : Nat) (m : RippleMode) (sg : Bool) := intervalProgram_slots9 n s (r.remainder w) width w.start w.stop m sg .work1 ht hq hs hw
  have h1 := rControlNonterminal_length_le [r.phase1] 0 r.control r.lengthRPrime r.terminal r.blockScratch
  have h2 := rControlNonterminal_length_le [r.phase1,r.terminal] 0 r.control r.lengthRPrime (r.blockScratch.getD 0 0) (r.blockScratch.drop 1)
  have hb := blockB2_length_le r
  simp only [List.length_cons,List.length_nil] at h1 h2
  have h := sequenceProgram_slots_le n (remainderBlockSegments n r width w)
    ([a,b,a,8*r.lengthRPrime.length+31,c,b,c] : List Nat) (by
      unfold remainderBlockSegments
      refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil))))))
      · intro s; simpa only [literalProgram_slots,a] using h1
      · intro s; exact hi s .sub true
      · intro s; simpa only [literalProgram_slots,a] using h1
      · intro s; simpa only [literalProgram_slots] using hb
      · intro s; simp only [literalProgram_slots,List.length_append,List.length_cons,List.length_nil,c]; omega
      · intro s; exact hi s .add false
      · intro s; simp only [literalProgram_slots,List.length_append,List.length_cons,List.length_nil,c]; omega) start
  simp only [List.sum_cons,List.sum_nil,a,b,c] at h
  unfold remainderBlockProgram
  omega

theorem coefficientBlockProgram_slots256 (n start : Nat) (r : IndexedStepRegisters) (w : ActiveWindow)
    (hb : TBoundaryLayout r.tBoundary) (hw : r.tBoundary.width=9) :
    (coefficientBlockProgram n start r 256 w).2.gateSlots ≤
      108*(coefficientPrefixTree (r.coefficient w) w.start w.stop).internalNodes+597 := by
  let b := 54*(coefficientPrefixTree (r.coefficient w) w.start w.stop).internalNodes+37
  have hc (s : Nat) (m : RippleMode) (sg : Bool) := coefficientProgram_slots n s (r.coefficient w) w.start w.stop m sg .work2
  have h1 := computeControl_length_le [r.phase2,r.sign] 2 r.terminal r.blockScratch
  have h2 := computeControl_length_le [r.phase1,r.terminal] 1 r.control r.blockScratch
  have h3 := computeControl_length_le [r.phase1] 1 r.control r.blockScratch
  have hp := prepareLatestPaperTBoundary_length256 r.tBoundary hb hw
  have hr := restoreLatestPaperTBoundary_length256 r.tBoundary hb hw
  simp only [List.length_cons,List.length_nil] at h1 h2 h3
  have h := sequenceProgram_slots_le n (coefficientBlockSegments n r 256 w)
    ([256,b,33,b,234] : List Nat) (by
      unfold coefficientBlockSegments
      refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil))))
      · intro s; simp only [literalProgram_slots,List.length_append]; omega
      · intro s; exact hc s .sub false
      · intro s; simp only [literalProgram_slots,List.length_append,List.length_cons,List.length_nil]; omega
      · intro s; exact hc s .add true
      · intro s; simp only [literalProgram_slots,List.length_append]; omega) start
  simp only [List.sum_cons,List.sum_nil,b] at h
  unfold coefficientBlockProgram
  omega


def measuredStepSlotBound (r : IndexedStepRegisters) (T : Nat) : Nat :=
  (blockAForward r).length+
    (24*r.lengthRPrime.length+168*(intervalTree (r.remainder (certifiedActiveWindows 256 T).remainder)
      (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop).internalNodes+2633)+
    (blockCForward r).length+(blockDForward r (certifiedActiveWindows 256 T).quotientSwap).length+
    (108*(coefficientPrefixTree (r.coefficient (certifiedActiveWindows 256 T).coefficient)
      (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop).internalNodes+597)+
    (blockFForward r).length+
    (8*(r.phaseUpdate.lengthQ.length+r.phaseUpdate.lengthRPrime.length+r.phaseUpdate.lengthS.length)+32)+hSlotBound r 256 T

theorem measuredStepProgram_slots (n start : Nat) (r : IndexedStepRegisters) (T : Nat)
    (ht : (r.remainder (certifiedActiveWindows 256 T).remainder).lengthT.length=9)
    (hq : (r.remainder (certifiedActiveWindows 256 T).remainder).lengthQ.length=9)
    (hs : (r.remainder (certifiedActiveWindows 256 T).remainder).lengthS.length=9)
    (he : 9≤(r.remainder (certifiedActiveWindows 256 T).remainder).endpointScratch.length)
    (hb : TBoundaryLayout r.tBoundary) (hw : r.tBoundary.width=9) :
    (measuredStepProgram n start r 256 T).2.gateSlots ≤ measuredStepSlotBound r T := by
  let rem := (certifiedActiveWindows 256 T).remainder
  let coef := (certifiedActiveWindows 256 T).coefficient
  have h := sequenceProgram_slots_le n (measuredStepSegments n r 256 T)
    ([(blockAForward r).length,
      24*r.lengthRPrime.length+168*(intervalTree (r.remainder rem) rem.start rem.stop).internalNodes+2633,
      (blockCForward r).length+(blockDForward r (certifiedActiveWindows 256 T).quotientSwap).length,
      108*(coefficientPrefixTree (r.coefficient coef) coef.start coef.stop).internalNodes+597,
      (blockFForward r).length,
      8*(r.phaseUpdate.lengthQ.length+r.phaseUpdate.lengthRPrime.length+r.phaseUpdate.lengthS.length)+32,
      hSlotBound r 256 T] : List Nat) (by
      unfold measuredStepSegments
      refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil))))))
      · intro s; simp only [literalProgram_slots]; exact Nat.le_refl _
      · intro s; exact remainderBlockProgram_slots9 n s r 256 rem ht hq hs he
      · intro s; simp only [literalProgram_slots,List.length_append]; exact Nat.le_refl _
      · intro s; exact coefficientBlockProgram_slots256 n s r coef hb hw
      · intro s; simp only [literalProgram_slots]; exact Nat.le_refl _
      · intro s; exact phaseProgram_slots n s r.phaseUpdate r.shiftEpoch
      · intro s; exact hProgram_slots n s r 256 T) start
  simp only [List.sum_cons,List.sum_nil,rem,coef] at h
  unfold measuredStepProgram measuredStepSlotBound
  omega

theorem measuredScheduleProgram_slots_le (n : Nat) (r : IndexedStepRegisters) (width count first bound : Nat)
    (hstep : ∀ T, first≤T → T<first+count → ∀ cursor,
      (measuredStepProgram n cursor r width T).2.gateSlots≤bound) (start : Nat) :
    (measuredScheduleProgram n r width count first start).2.gateSlots ≤ count*bound := by
  induction count generalizing first start with
  | zero => exact Nat.zero_le _
  | succ count ih =>
    have hf := hstep first (by omega) (by omega) start
    have hr := ih (first+1) (by intro T h1 h2; exact hstep T (by omega) (by omega))
      (start+(measuredStepProgram n start r width first).1)
    rw [measuredScheduleProgram,appendCompiled_slots]
    nlinarith


def measuredInverseStepSlotBounds (r : IndexedStepRegisters) (T : Nat) : List Nat :=
  [ hSlotBound r 256 T,
    8*(r.phaseUpdate.lengthQ.length+r.phaseUpdate.lengthRPrime.length+r.phaseUpdate.lengthS.length)+32,
    (((blockFForward r).adjoint ++ prepareLatestPaperTBoundary r.tBoundary 256 ++ computeControl [r.phase1] 1 r.control r.blockScratch)).length,
    54*(coefficientPrefixTree (r.coefficient (certifiedActiveWindows 256 T).coefficient) (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop).internalNodes+37,
    ((computeControl [r.phase1] 1 r.control r.blockScratch ++ [Gate.CX r.phase1 r.sign] ++ computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++ computeControl [r.phase1,r.terminal] 1 r.control r.blockScratch ++ computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch)).length,
    54*(coefficientPrefixTree (r.coefficient (certifiedActiveWindows 256 T).coefficient) (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop).internalNodes+37,
    ((computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++ computeControl [r.phase1,r.terminal] 1 r.control r.blockScratch ++ computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++ restoreLatestPaperTBoundary r.tBoundary 256 ++ blockDInverse r (certifiedActiveWindows 256 T).quotientSwap ++ blockCInverse r ++ (([Gate.CCX r.phase2 r.sign r.terminal] ++ rControlNonterminal [r.phase1,r.terminal] 0 r.control r.lengthRPrime (r.blockScratch.getD 0 0) (r.blockScratch.drop 1)) ++ [Gate.CCX r.phase2 r.sign r.terminal]))).length,
    84*(intervalTree (r.remainder (certifiedActiveWindows 256 T).remainder) (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop).internalNodes+1273,
    (((([Gate.CCX r.phase2 r.sign r.terminal] ++ rControlNonterminal [r.phase1,r.terminal] 0 r.control r.lengthRPrime (r.blockScratch.getD 0 0) (r.blockScratch.drop 1)) ++ [Gate.CCX r.phase2 r.sign r.terminal]) ++ blockB2 r ++ rControlNonterminal [r.phase1] 0 r.control r.lengthRPrime r.terminal r.blockScratch)).length,
    84*(intervalTree (r.remainder (certifiedActiveWindows 256 T).remainder) (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop).internalNodes+1273,
    ((rControlNonterminal [r.phase1] 0 r.control r.lengthRPrime r.terminal r.blockScratch ++ blockAInverse r)).length ]

theorem measuredInverseStepProgram_slots (n start : Nat) (r : IndexedStepRegisters) (T : Nat)
    (ht : (r.remainder (certifiedActiveWindows 256 T).remainder).lengthT.length=9)
    (hq : (r.remainder (certifiedActiveWindows 256 T).remainder).lengthQ.length=9)
    (hs : (r.remainder (certifiedActiveWindows 256 T).remainder).lengthS.length=9)
    (he : 9≤(r.remainder (certifiedActiveWindows 256 T).remainder).endpointScratch.length) :
    (measuredInverseStepProgram n start r T).2.gateSlots ≤ (measuredInverseStepSlotBounds r T).sum := by
  unfold measuredInverseStepProgram
  apply sequenceProgram_slots_le
  unfold measuredInverseStepSegments measuredInverseStepSlotBounds
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))))))))
  · intro s; exact hInverseProgram_slots n s r 256 T
  · intro s; exact phaseInverseProgram_slots n s r.phaseUpdate r.shiftEpoch
  · intro s; simp only [literalProgram_slots]; exact Nat.le_refl _
  · intro s; exact coefficientProgram_slots n s (r.coefficient (certifiedActiveWindows 256 T).coefficient) (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop (RippleMode.add.inverse) true .work2
  · intro s; simp only [literalProgram_slots]; exact Nat.le_refl _
  · intro s; exact coefficientProgram_slots n s (r.coefficient (certifiedActiveWindows 256 T).coefficient) (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop (RippleMode.sub.inverse) false .work2
  · intro s; simp only [literalProgram_slots]; exact Nat.le_refl _
  · intro s; exact intervalProgram_slots9 n s (r.remainder (certifiedActiveWindows 256 T).remainder) 256 (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop (RippleMode.add.inverse) false .work1 ht hq hs he
  · intro s; simp only [literalProgram_slots]; exact Nat.le_refl _
  · intro s; exact intervalProgram_slots9 n s (r.remainder (certifiedActiveWindows 256 T).remainder) 256 (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop (RippleMode.sub.inverse) true .work1 ht hq hs he
  · intro s; simp only [literalProgram_slots]; exact Nat.le_refl _


theorem measuredInverseScheduleProgram_slots_le (n : Nat) (r : IndexedStepRegisters) (count first bound : Nat)
    (hstep : ∀ T, first≤T → T<first+count → ∀ cursor,
      (measuredInverseStepProgram n cursor r T).2.gateSlots≤bound) (start : Nat) :
    (measuredInverseScheduleProgram n r count first start).2.gateSlots ≤ count*bound := by
  induction count generalizing first start with
  | zero => exact Nat.zero_le _
  | succ count ih =>
    have hr := ih (first+1) (by intro T h1 h2; exact hstep T (by omega) (by omega)) start
    have hf := hstep first (by omega) (by omega)
      (start+(measuredInverseScheduleProgram n r count (first+1) start).1)
    rw [measuredInverseScheduleProgram,appendCompiled_slots]
    nlinarith

theorem intervalTree_nodes_le (r : IntervalRegisters) (k K : Nat) :
    (intervalTree r k K).internalNodes ≤ K := by
  have hn := dualUnaryAction_internalNodes_add_one (intervalTree r k K)
  have hl := dualUnaryAction_leaves_eq_labels_length (intervalTree r k K)
  rw [intervalTree_labels,Finset.length_sort] at hl
  have hc := List.toFinset_card_le (intervalMainLabels k K)
  have hb : (intervalMainLabels k K).length ≤ K+1 := by
    simp only [intervalMainLabels]
    split <;> simp only [List.length_range,intervalLaneCount] <;> omega
  omega

theorem quotientSwapTree_nodes_le (r : QuotientSwapRegisters) (k K : Nat) (hk : k≤K) :
    (quotientSwapTree r k K).internalNodes ≤ K := by
  have hn := unaryAction_internalNodes_add_one (quotientSwapTree r k K)
  have hl := unaryAction_leaves_eq_labels_length (quotientSwapTree r k K)
  rw [quotientSwapTree_labels r hk,Finset.length_sort] at hl
  have hc := List.toFinset_card_le (quotientSwapLabels k K)
  simp only [quotientSwapLabels,List.length_range'] at hc hl
  omega

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/ProductionEEASlots ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/ProductionEEASlots.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

theorem schedule_layout_at {r : IndexedStepRegisters} {width first count : Nat}
    (h : IndexedScheduleLayout r width first count) (offset : Nat) (ho : offset<count) :
    IndexedStepLayout r width (first+offset) := by
  induction h generalizing offset with
  | done => omega
  | @step first count head tail ih =>
    cases offset with
    | zero => simpa using head
    | succ offset => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih offset (by omega)

theorem production_step_layout (T : Nat) (hT : 1≤T) (hmax : T≤1620) :
    IndexedStepLayout indexedStepProductionRegisters 256 T := by
  have h := schedule_layout_at secp256k1ScheduleLayout_production (T-1) (by change T-1<1620; omega)
  simpa [show 1+(T-1)=T by omega] using h

theorem endSlotBound_le (r : EndIterationRegisters) (w : EndIterationWindows)
    (hl : EndIterationLayout r 256 w) (ht : r.lengthT.length=9) :
    endSlotBound r 256 w ≤ 99900 := by
  have hu := r.upperTree_visitLabels w hl.k4_le_K4
  have hd := r.lowerTree_visitLabels 256 w hl.k5_le_decode
  rw [UnaryActionTree.visitLabels_inc] at hu hd
  have hnu := unaryAction_internalNodes_add_one (r.upperTree w)
  have hnd := unaryAction_internalNodes_add_one (r.lowerTree 256 w)
  have hlu := unaryAction_leaves_eq_labels_length (r.upperTree w)
  have hld := unaryAction_leaves_eq_labels_length (r.lowerTree 256 w)
  rw [hu] at hlu
  rw [hd] at hld
  simp only [zeroMapLabels,List.length_map,List.length_range] at hlu hld
  have hk := hl.K4_le_work
  have hk5 : w.K5Decode 256 ≤259 := Nat.min_le_right _ _
  have hr : r.lengthRP.length=9 := hl.lengthRP_length.trans ht
  have hc : r.constants.length≤9 := by
    simp only [EndIterationRegisters.constants,List.length_take,EndIterationRegisters.width,ht]
    exact Nat.min_le_left _ _
  simp only [endSlotBound,endUpperSlotBound,endLowerSlotBound,hl.work1_length,ht,hr,
    zeroMapLabels,List.length_map,List.length_range ]
  omega

theorem production_hProgram_slots (n start T : Nat)
    (hl : IndexedStepLayout indexedStepProductionRegisters 256 T) :
    (hProgram n start indexedStepProductionRegisters 256 T).2.gateSlots≤100000 := by
  by_cases hm : T%4=0
  · have he := endSlotBound_le _ _ (hl.endIteration hm) (by rfl)
    have hp := hProgram_slots n start indexedStepProductionRegisters 256 T
    change (hProgram n start indexedStepProductionRegisters 256 T).2.gateSlots≤100000
    change (hProgram n start indexedStepProductionRegisters 256 T).2.gateSlots≤
      4*9+4*9+15+endSlotBound (indexedStepProductionRegisters.endIteration 256 T) 256 (endIterationWindowsAt 256 T) at hp
    omega
  · simp only [hProgram,compiledIf_slots,if_neg hm,Straight.gateSlots]
    omega


local notation "R" => indexedStepProductionRegisters
attribute [local irreducible] blockAForward blockAInverse blockCForward blockCInverse blockDForward blockDInverse blockFForward
  intervalTree coefficientPrefixTree quotientSwapTree remainderBlockProgram coefficientBlockProgram phaseProgram
  measuredStepProgram measuredEEAForwardProgram measuredScheduleProgram primitiveResources
  canonicalWork2Rotation canonicalWork2InverseRotation terminalEpochCompression terminalWork1Clear
  measuredForwardWrapperProgram measuredReverseWrapperProgram
  hornerProgram hornerInverseProgram multiplyWorkProgram multiplyDataProgram unmultiplyDataProgram fig15SwapOutput
  intervalProgram coefficientProgram measuredInverseStepProgram measuredEEAReverseProgram measuredInverseScheduleProgram


theorem production_blockA_length : (blockAForward R).length=2613 := by
  rw [circuit_length_primitive,blockAForward259_primitive R indexedStepProduction_layout.terminalPadding
    indexedStepProduction_layout.preShift (by simp only [indexedStepProductionRegisters,List.length_range']) (by rfl) (by rfl) (by decide)]
  rfl

theorem production_blockC_length : (blockCForward R).length=42 := by
  rw [circuit_length_primitive,blockCForward9_primitive R (by rfl) (by decide)]
  rfl

theorem production_blockF_length : (blockFForward R).length=1695 := by
  rw [blockFForward]
  rw [circuit_length_primitive,postShiftUnitary259_primitive (R).postShift indexedStepProduction_layout.postShift (by simp only [IndexedStepRegisters.postShift,indexedStepProductionRegisters,List.length_range']) (by rfl)]
  rfl

theorem production_blockD_length (T : Nat) (hl : IndexedStepLayout R 256 T) :
    (blockDForward R (certifiedActiveWindows 256 T).quotientSwap).length≤4000 := by
  let w := (certifiedActiveWindows 256 T).quotientSwap
  have hn := quotientSwapTree_nodes_le ((R).quotient w) w.start w.stop hl.quotient.k_le_K
  have hleaf := unaryAction_internalNodes_add_one (quotientSwapTree ((R).quotient w) w.start w.stop)
  have hk : w.stop≤258 := by simp only [w,certifiedActiveWindows,quotientSwapWindow]; omega
  rw [circuit_length_primitive,blockDForward9_primitive R _ hl.quotient (by rfl) (by rfl) (by decide)]
  change 48+4*(quotientSwapTree ((R).quotient w) w.start w.stop).internalNodes+0+
    (170+2*(quotientSwapTree ((R).quotient w) w.start w.stop).leaves+2*(quotientSwapTree ((R).quotient w) w.start w.stop).internalNodes)+
    (108+(quotientSwapTree ((R).quotient w) w.start w.stop).leaves+2*(quotientSwapTree ((R).quotient w) w.start w.stop).internalNodes)+0≤4000
  omega

theorem production_remainderBlock_slots (n start T : Nat) (hl : IndexedStepLayout R 256 T) :
    (remainderBlockProgram n start R 256 (certifiedActiveWindows 256 T).remainder).2.gateSlots≤47000 := by
  let w := (certifiedActiveWindows 256 T).remainder
  have hn := intervalTree_nodes_le ((R).remainder w) w.start w.stop
  have h := remainderBlockProgram_slots9 n start R 256 w (by rfl) (by rfl) (by rfl) (intervalLengthQ_le_endpointScratch _ _ _ .work1 hl.remainder)
  change _≤24*9+168*(intervalTree ((R).remainder w) w.start w.stop).internalNodes+2633 at h
  have hk : w.stop=259 := rfl
  change (remainderBlockProgram n start R 256 w).2.gateSlots≤47000
  omega

theorem production_coefficientBlock_slots (n start T : Nat) (hl : IndexedStepLayout R 256 T) :
    (coefficientBlockProgram n start R 256 (certifiedActiveWindows 256 T).coefficient).2.gateSlots≤29000 := by
  let w := (certifiedActiveWindows 256 T).coefficient
  have hn := quotientSwapTree_nodes_le (((R).coefficient w).routing w.start w.stop) w.start w.stop hl.coefficient.k_le_K
  have hk : w.stop≤257 := by simp only [w,certifiedActiveWindows,coefficientWindow]; omega
  have h := coefficientBlockProgram_slots256 n start R w hl.tBoundary (by rfl)
  have hn2 : (coefficientPrefixTree ((R).coefficient w) w.start w.stop).internalNodes≤w.stop := by
    simpa only [coefficientPrefixTree] using hn
  change (coefficientBlockProgram n start R 256 w).2.gateSlots≤29000
  omega

theorem production_measuredStep_slots (n start T : Nat) (hl : IndexedStepLayout R 256 T) :
    (measuredStepProgram n start R 256 T).2.gateSlots≤200000 := by
  have hd := production_blockD_length T hl
  have h := sequenceProgram_slots_le n (measuredStepSegments n R 256 T)
    ([2613,47000,4042,29000,1695,248,100000] : List Nat) (by
      unfold measuredStepSegments
      refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil))))))
      · intro s; simp only [literalProgram_slots,production_blockA_length]; exact Nat.le_refl _
      · intro s; exact production_remainderBlock_slots n s T hl
      · intro s; simp only [literalProgram_slots,List.length_append,production_blockC_length]; omega
      · intro s; exact production_coefficientBlock_slots n s T hl
      · intro s; simp only [literalProgram_slots,production_blockF_length]; exact Nat.le_refl _
      · intro s; exact phaseProgram_slots n s (R).phaseUpdate (R).shiftEpoch
      · intro s; exact production_hProgram_slots n s T hl) start
  simp only [List.sum_cons,List.sum_nil] at h
  unfold measuredStepProgram
  omega

theorem production_measuredForward_slots (n start : Nat) :
    (measuredEEAForwardProgram n start R).2.gateSlots≤324000000 := by
  have h := measuredScheduleProgram_slots_le n R 256 1620 1 200000
    (by intro T ht hmax s; exact production_measuredStep_slots n s T (production_step_layout T ht (by omega))) start
  simpa only [measuredEEAForwardProgram,secp256k1ScheduleLength] using h


theorem production_hInverseProgram_slots (n start T : Nat)
    (hl : IndexedStepLayout R 256 T) :
    (hInverseProgram n start R 256 T).2.gateSlots≤100000 := by
  by_cases hm : T%4=0
  · have he := endSlotBound_le _ _ (hl.endIteration hm) (by rfl)
    have hp := hInverseProgram_slots n start R 256 T
    change (hInverseProgram n start R 256 T).2.gateSlots≤
      4*9+4*9+15+endSlotBound ((R).endIteration 256 T) 256 (endIterationWindowsAt 256 T) at hp
    omega
  · simp only [hInverseProgram,compiledIf_slots,if_neg hm,Straight.gateSlots]
    omega

theorem production_blockAInverse_length : (blockAInverse R).length=2645 := by
  rw [circuit_length_primitive,blockAInverse259_primitive R indexedStepProduction_layout.terminalPadding
    indexedStepProduction_layout.preShift (by simp only [indexedStepProductionRegisters,List.length_range']) (by rfl) (by rfl) (by decide)]
  rfl

theorem production_blockCInverse_length : (blockCInverse R).length=42 := by
  rw [circuit_length_primitive,blockCInverse9_primitive R (by rfl) (by decide)]
  rfl

theorem production_blockDInverse_length (T : Nat) (hl : IndexedStepLayout R 256 T) :
    (blockDInverse R (certifiedActiveWindows 256 T).quotientSwap).length≤4000 := by
  let w := (certifiedActiveWindows 256 T).quotientSwap
  have hn := quotientSwapTree_nodes_le ((R).quotient w) w.start w.stop hl.quotient.k_le_K
  have hleaf := unaryAction_internalNodes_add_one (quotientSwapTree ((R).quotient w) w.start w.stop)
  have hk : w.stop≤258 := by simp only [w,certifiedActiveWindows,quotientSwapWindow]; omega
  rw [circuit_length_primitive,blockDInverse9_primitive R _ hl.quotient (by rfl) (by rfl) (by decide)]
  change 48+4*(quotientSwapTree ((R).quotient w) w.start w.stop).internalNodes+0+
    (170+2*(quotientSwapTree ((R).quotient w) w.start w.stop).leaves+2*(quotientSwapTree ((R).quotient w) w.start w.stop).internalNodes)+
    (108+(quotientSwapTree ((R).quotient w) w.start w.stop).leaves+2*(quotientSwapTree ((R).quotient w) w.start w.stop).internalNodes)+0≤4000
  omega

theorem production_coefficient_slots (n start T : Nat) (mode : RippleMode) (sg : Bool)
    (hl : IndexedStepLayout R 256 T) :
    (coefficientProgram n start ((R).coefficient (certifiedActiveWindows 256 T).coefficient)
      (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop mode sg .work2).2.gateSlots≤14500 := by
  let w := (certifiedActiveWindows 256 T).coefficient
  have hn := quotientSwapTree_nodes_le (((R).coefficient w).routing w.start w.stop) w.start w.stop hl.coefficient.k_le_K
  have hk : w.stop≤257 := by simp only [w,certifiedActiveWindows,coefficientWindow]; omega
  have h := coefficientProgram_slots n start ((R).coefficient w) w.start w.stop mode sg .work2
  have hn2 : (coefficientPrefixTree ((R).coefficient w) w.start w.stop).internalNodes≤w.stop := by
    simpa only [coefficientPrefixTree] using hn
  change (coefficientProgram n start ((R).coefficient w) w.start w.stop mode sg .work2).2.gateSlots≤14500
  omega

theorem production_interval_slots (n start T : Nat) (mode : RippleMode) (sg : Bool)
    (hl : IndexedStepLayout R 256 T) :
    (intervalProgram n start ((R).remainder (certifiedActiveWindows 256 T).remainder) 256
      (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop mode sg .work1).2.gateSlots≤23500 := by
  let w := (certifiedActiveWindows 256 T).remainder
  have hn := intervalTree_nodes_le ((R).remainder w) w.start w.stop
  have h := intervalProgram_slots9 n start ((R).remainder w) 256 w.start w.stop mode sg .work1 (by rfl) (by rfl) (by rfl)
    (intervalLengthQ_le_endpointScratch _ _ _ .work1 hl.remainder)
  have hk : w.stop=259 := rfl
  change (intervalProgram n start ((R).remainder w) 256 w.start w.stop mode sg .work1).2.gateSlots≤23500
  omega


theorem production_measuredInverseStep_slots (n start T : Nat) (hl : IndexedStepLayout R 256 T) :
    (measuredInverseStepProgram n start R T).2.gateSlots≤200000 := by
  have hd := production_blockDInverse_length T hl
  have hp := prepareLatestPaperTBoundary_length256 (R).tBoundary hl.tBoundary (by rfl)
  have hr := restoreLatestPaperTBoundary_length256 (R).tBoundary hl.tBoundary (by rfl)
  have h1 := computeControl_length_le [(R).phase1] 1 (R).control (R).blockScratch
  have h2 := computeControl_length_le [(R).phase2,(R).sign] 2 (R).terminal (R).blockScratch
  have h3 := computeControl_length_le [(R).phase1,(R).terminal] 1 (R).control (R).blockScratch
  have h4 := rControlNonterminal_length_le [(R).phase1,(R).terminal] 0 (R).control (R).lengthRPrime ((R).blockScratch.getD 0 0) ((R).blockScratch.drop 1)
  have h5 := rControlNonterminal_length_le [(R).phase1] 0 (R).control (R).lengthRPrime (R).terminal (R).blockScratch
  have hb := blockB2_length_le R
  simp only [List.length_cons,List.length_nil] at h1 h2 h3 h4 h5
  change _≤4*9+4*2+7 at h4
  change _≤4*9+4*1+7 at h5
  change _≤8*9+31 at hb
  have h := sequenceProgram_slots_le n (measuredInverseStepSegments n R T)
    ([100000,248,1929,14500,33,14500,4500,23500,210,23500,2700] : List Nat) (by
      unfold measuredInverseStepSegments
      refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil))))))))))
      · intro s; exact production_hInverseProgram_slots n s T hl
      · intro s; exact phaseInverseProgram_slots n s (R).phaseUpdate (R).shiftEpoch
      · intro s; simp only [literalProgram_slots,List.length_append,circuit_adjoint_length,production_blockF_length]; omega
      · intro s; exact production_coefficient_slots n s T (RippleMode.add.inverse) true hl
      · intro s; simp only [literalProgram_slots,List.length_append,List.length_cons,List.length_nil]; omega
      · intro s; exact production_coefficient_slots n s T (RippleMode.sub.inverse) false hl
      · intro s; simp only [literalProgram_slots,List.length_append,List.length_cons,List.length_nil,production_blockCInverse_length]; omega
      · intro s; exact production_interval_slots n s T (RippleMode.add.inverse) false hl
      · intro s; simp only [literalProgram_slots,List.length_append,List.length_cons,List.length_nil]; omega
      · intro s; exact production_interval_slots n s T (RippleMode.sub.inverse) true hl
      · intro s; simp only [literalProgram_slots,List.length_append,production_blockAInverse_length]; omega) start
  simp only [List.sum_cons,List.sum_nil] at h
  unfold measuredInverseStepProgram
  omega

theorem production_measuredReverse_slots (n start : Nat) :
    (measuredEEAReverseProgram n start R).2.gateSlots≤324000000 := by
  have h := measuredInverseScheduleProgram_slots_le n R 1620 1 200000
    (by intro T ht hmax s; exact production_measuredInverseStep_slots n s T (production_step_layout T ht (by omega))) start
  simpa only [measuredEEAReverseProgram,secp256k1ScheduleLength] using h


theorem constMinusProgram_slots (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (q c r t : Wire) (hd : input.length=dirty.length+1) (hk : bits.length=input.length) :
    (constMinusProgram n start input dirty bits q c r t).2.gateSlots≤53*input.length := by
  have hi := gidneyProgram_slots_le n start input dirty ((List.range input.length).map (Nat.testBit 1)) q c r t hd (by simp)
  have hb (s : Nat) := gidneyProgram_slots_le n s input dirty bits q c r t hd hk
  simp only [constMinusProgram,prependCompiled_slots,appendCompiled_slots,controlledComplement,List.length_map]
  grind only

theorem eeaCenterProgram_slots (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t iter : Wire) (hd : input.length=dirty.length) (hk : bits.length=input.length)
    (hp : 0 < input.length) :
    (eeaCenterProgram n start input dirty bits p c r t iter).2.gateSlots≤78*input.length+1 := by
  have ht : input.length=(dirty.take (input.length-1)).length+1 := by simp only [List.length_take,← hd]; omega
  have hc := uncontrolledCompareProgram_slots_le n start input dirty (p/2+1) c r t iter hd
  have hn (s : Nat) := constMinusProgram_slots n s input (dirty.take (input.length-1)) bits iter c r t ht hk
  simp only [eeaCenterProgram,appendCompiled_slots]
  grind only

theorem eeaUncenterProgram_slots (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t iter : Wire) (hd : input.length=dirty.length) (hk : bits.length=input.length)
    (hp : 0 < input.length) :
    (eeaUncenterProgram n start input dirty bits p c r t iter).2.gateSlots≤78*input.length+1 := by
  have ht : input.length=(dirty.take (input.length-1)).length+1 := by simp only [List.length_take,← hd]; omega
  have hn := constMinusProgram_slots n start input (dirty.take (input.length-1)) bits iter c r t ht hk
  have hc (s : Nat) := uncontrolledCompareProgram_slots_le n s input dirty (p/2+1) c r t iter hd
  simp only [eeaUncenterProgram,appendCompiled_slots]
  grind only

theorem eeaParityProgram_slots (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (c r t iter : Wire) (hd : input.length=dirty.length+1) (hk : bits.length=input.length) :
    (eeaParityProgram n start input dirty bits c r t iter).2.gateSlots≤53*input.length+2 := by
  have h := constMinusProgram_slots n start input dirty bits iter c r t hd hk
  simp only [eeaParityProgram,prependCompiled_slots,appendCompiled_slots,literalProgram_slots,List.length_cons,List.length_nil]
  omega

theorem preprocessProgram_slots (n start : Nat) : (preprocessProgram n start).2.gateSlots≤600000 := by
  have hc := eeaCenterProgram_slots n start (List.range' 266 256).reverse (List.range' 4 256)
    (constantBits 256 (2^256-2^32-977)) (2^256-2^32-977) 560 561 562 2 (by simp) (by simp) (by simp)
  have hp : workRegistersPrepare.length=641 := by rw [circuit_length_primitive,workRegistersPrepare_primitive]; rfl
  have hl : eeaLengthSetup.length=518649 := by rw [circuit_length_primitive,eeaLengthSetup_primitive]; rfl
  simp only [List.length_reverse,List.length_range'] at hc
  simp only [preprocessProgram,surroundCompiled_slots,hp,hl]
  omega

theorem unpreprocessProgram_slots (n start : Nat) : (unpreprocessProgram n start).2.gateSlots≤600000 := by
  have hc := eeaUncenterProgram_slots n start (List.range' 266 256).reverse (List.range' 4 256)
    (constantBits 256 (2^256-2^32-977)) (2^256-2^32-977) 560 561 562 2 (by simp) (by simp) (by simp)
  have hp : workRegistersRestore.length=641 := by rw [circuit_length_primitive,workRegistersRestore_primitive]; rfl
  have hl : eeaLengthUndo.length=518649 := by rw [circuit_length_primitive,eeaLengthUndo_primitive]; rfl
  simp only [List.length_reverse,List.length_range'] at hc
  simp only [unpreprocessProgram,surroundCompiled_slots,hp,hl]
  omega

theorem productionParityProgram_slots (n start : Nat) : (productionParityProgram n start).2.gateSlots≤13570 := by
  have h := eeaParityProgram_slots n start (List.range' 263 256) (List.range' 4 255) secp256k1ModulusBits 560 561 562 2 (by simp) (by simp [secp256k1ModulusBits])
  simpa only [List.length_range'] using h


theorem canonicalWork2Rotation_length : canonicalWork2Rotation.length=7866 := by
  rw [circuit_length_primitive,canonicalWork2Rotation_primitive]; rfl

theorem canonicalWork2InverseRotation_length : canonicalWork2InverseRotation.length=7866 := by
  rw [circuit_length_primitive,canonicalWork2InverseRotation_primitive]; rfl

theorem terminalEpochCompression_length : terminalEpochCompression.length=25 := by
  rw [circuit_length_primitive,terminalEpochCompression_primitive]; rfl

theorem terminalWork1Clear_length : terminalWork1Clear.length=251 := by
  rw [circuit_length_primitive,terminalWork1Clear_primitive]; rfl

theorem measuredForwardWrapperProgram_slots (n start : Nat) :
    (measuredForwardWrapperProgram n start).2.gateSlots≤325000000 := by
  have h := sequenceProgram_slots_le n (measuredForwardWrapperSegments n)
    ([600000,324000000,7891,13570,251] : List Nat) (by
      unfold measuredForwardWrapperSegments
      refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil))))
      · intro s; exact preprocessProgram_slots n s
      · intro s; exact production_measuredForward_slots n s
      · intro s; simp only [literalProgram_slots,List.length_append,canonicalWork2Rotation_length,terminalEpochCompression_length]; decide
      · intro s; exact productionParityProgram_slots n s
      · intro s; simp only [literalProgram_slots,terminalWork1Clear_length]; decide) start
  simp only [List.sum_cons,List.sum_nil] at h
  unfold measuredForwardWrapperProgram
  omega

theorem measuredReverseWrapperProgram_slots (n start : Nat) :
    (measuredReverseWrapperProgram n start).2.gateSlots≤325000000 := by
  have h := sequenceProgram_slots_le n (measuredReverseWrapperSegments n)
    ([251,13570,7891,324000000,600000] : List Nat) (by
      unfold measuredReverseWrapperSegments
      refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil))))
      · intro s; simp only [literalProgram_slots,terminalWork1Clear_length]; decide
      · intro s; exact productionParityProgram_slots n s
      · intro s; simp only [literalProgram_slots,List.length_append,canonicalWork2InverseRotation_length,terminalEpochCompression_length]; decide
      · intro s; exact production_measuredReverse_slots n s
      · intro s; exact unpreprocessProgram_slots n s) start
  simp only [List.sum_cons,List.sum_nil] at h
  unfold measuredReverseWrapperProgram
  omega



end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/InPlaceSlots ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/InPlaceSlots.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
attribute [local irreducible] measuredForwardWrapperProgram measuredReverseWrapperProgram
  hornerProgram hornerInverseProgram multiplyWorkProgram multiplyDataProgram unmultiplyDataProgram fig15SwapOutput
theorem collectProgram_slots_le (n : Nat)
    (next : (cursor : Nat) → List (Fin cursor) → (count : Nat) × Straight n cursor (cursor+count))
    (bound : Nat) (h : ∀ cursor prior, (next cursor prior).2.gateSlots≤bound)
    (ws : List Wire) (start : Nat) (prior : List (Fin start)) :
    (collectProgram n next ws start prior).2.gateSlots≤bound := by
  induction ws generalizing start with
  | nil => exact h start prior
  | cons w ws ih =>
    simp only [collectProgram,castFinish_gateSlots,Straight.gateSlots]
    exact ih _ _

theorem relabelCompiled_slots {n start : Nat} (e : Wire ≃ Wire)
    (p : (count : Nat) × Straight n start (start+count)) :
    (relabelCompiled e p).2.gateSlots=p.2.gateSlots := by
  exact relabelStraight_slots e p.2

attribute [local irreducible] relabelCompiled measuredForwardDataBankProgram measuredReverseDataBankProgram
  divisionCleanupProgram divisionCorrectionProgram divisionAfterResetProgram divisionProgram
  multiplicationCleanupProgram multiplicationCorrectionProgram multiplicationAfterResetProgram multiplicationProgram

theorem measuredForwardDataBankProgram_slots (n start : Nat) :
    (measuredForwardDataBankProgram n start).2.gateSlots≤325000000 := by
  simp only [measuredForwardDataBankProgram,relabelCompiled_slots]
  exact measuredForwardWrapperProgram_slots n start

theorem measuredReverseDataBankProgram_slots (n start : Nat) :
    (measuredReverseDataBankProgram n start).2.gateSlots≤325000000 := by
  simp only [measuredReverseDataBankProgram,relabelCompiled_slots]
  exact measuredReverseWrapperProgram_slots n start

theorem correctionCompiled_slots_le (n start : Nat) (ws : List Wire) (prior : List (Fin start)) :
    (correctionCompiled n start ws prior).2.gateSlots≤3*ws.length := by
  simp only [correctionCompiled,registerCorrectionProgram_slots,Straight.gateSlots]
  omega

theorem appendLiteral_slots {n start : Nat} (p : (count : Nat) × Straight n start (start+count)) (gs : Circuit) :
    (appendLiteral p gs).2.gateSlots=p.2.gateSlots+gs.length := by
  simp only [appendLiteral,appendCompiled_slots,literalProgram_slots]

theorem fig15SwapOutput_length : fig15SwapOutput.length=768 := by
  rw [circuit_length_primitive,fig15SwapOutput_primitive]; rfl

theorem multiplyWorkProgram_slots (n start : Nat) : (multiplyWorkProgram n start).2.gateSlots≤8000000 := by
  have h := hornerProgram_slots256 n start (List.range' 263 256) (List.range' 580 256) (List.range' 7 256) secp256k1ReductionConstantBits ShorECDLP.p 558 560 561 559 (by simp) (by simp) (by simp [secp256k1ReductionConstantBits])
  simp only [List.length_range'] at h
  unfold multiplyWorkProgram
  omega

theorem multiplyDataProgram_slots (n start : Nat) : (multiplyDataProgram n start).2.gateSlots≤8000000 := by
  have h := hornerProgram_slots256 n start (List.range' 263 256) (List.range' 7 256) (List.range' 580 256) secp256k1ReductionConstantBits ShorECDLP.p 558 560 561 559 (by simp) (by simp) (by simp [secp256k1ReductionConstantBits])
  simp only [List.length_range'] at h
  unfold multiplyDataProgram
  omega

theorem unmultiplyDataProgram_slots (n start : Nat) : (unmultiplyDataProgram n start).2.gateSlots≤8000000 := by
  have h := hornerInverseProgram_slots256 n start (List.range' 263 256) (List.range' 7 256) (List.range' 580 256) (constantBits 256 ShorECDLP.p) ShorECDLP.p 558 560 561 559 (by simp) (by simp) (by simp)
  simp only [List.length_range'] at h
  unfold unmultiplyDataProgram
  omega

theorem divisionCorrectionProgram_slots (n start : Nat) (prior : List (Fin start)) :
    (divisionCorrectionProgram n start prior).2.gateSlots≤8001536 := by
  have hc := correctionCompiled_slots_le n start (List.range' 580 256) prior
  have hm := unmultiplyDataProgram_slots n start
  simp only [List.length_range'] at hc
  simp only [divisionCorrectionProgram,divisionCleanupProgram,appendCompiled_slots,appendLiteral_slots,fig15SwapOutput_length]
  omega

theorem divisionAfterResetProgram_slots (n start : Nat) (prior : List (Fin start)) :
    (divisionAfterResetProgram n start prior).2.gateSlots≤341001536 := by
  have he := measuredReverseDataBankProgram_slots n start
  have hm (s : Nat) := multiplyDataProgram_slots n s
  have hc (s : Nat) (p : List (Fin s)) := divisionCorrectionProgram_slots n s p
  simp only [divisionAfterResetProgram,appendRetaining,appendCompiled_slots]
  grind only

theorem divisionProgram_slots (n start : Nat) : (divisionProgram n start).2.gateSlots≤675000000 := by
  have he := measuredForwardWrapperProgram_slots n start
  have hm (s : Nat) := multiplyWorkProgram_slots n s
  have hc (s : Nat) (p : List (Fin s)) := collectProgram_slots_le n (divisionAfterResetProgram n)
    341001536 (divisionAfterResetProgram_slots n) (List.range' 580 256) s p
  simp only [divisionProgram,appendCompiled_slots]
  grind only

theorem multiplicationCorrectionProgram_slots (n start : Nat) (prior : List (Fin start)) :
    (multiplicationCorrectionProgram n start prior).2.gateSlots≤333001536 := by
  have hc := correctionCompiled_slots_le n start (List.range' 580 256) prior
  have hm := unmultiplyDataProgram_slots n start
  have he (s : Nat) := measuredReverseDataBankProgram_slots n s
  simp only [List.length_range'] at hc
  simp only [multiplicationCorrectionProgram,multiplicationCleanupProgram,appendCompiled_slots,appendLiteral_slots,fig15SwapOutput_length]
  grind only

theorem multiplicationAfterResetProgram_slots (n start : Nat) (prior : List (Fin start)) :
    (multiplicationAfterResetProgram n start prior).2.gateSlots≤666001536 := by
  have he := measuredForwardDataBankProgram_slots n start
  have hm (s : Nat) := multiplyDataProgram_slots n s
  have hc (s : Nat) (p : List (Fin s)) := multiplicationCorrectionProgram_slots n s p
  simp only [multiplicationAfterResetProgram,appendRetaining,appendCompiled_slots]
  grind only

theorem multiplicationProgram_slots (n start : Nat) : (multiplicationProgram n start).2.gateSlots≤675000000 := by
  have hm := multiplyWorkProgram_slots n start
  have hc (s : Nat) (p : List (Fin s)) := collectProgram_slots_le n (multiplicationAfterResetProgram n)
    666001536 (multiplicationAfterResetProgram_slots n) (List.range' 580 256) s p
  simp only [multiplicationProgram,appendCompiled_slots]
  grind only


end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/WindowSlots ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/WindowSlots.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
attribute [local irreducible] divisionProgram multiplicationProgram
attribute [local irreducible] zeroDivisionProgram zeroMultiplicationProgram modularNegateProgram squareSubtractProgram coordinateProgram

theorem fig15ZeroPrepare_length : fig15ZeroPrepare.length=1022 := by
  rw [circuit_length_primitive,fig15ZeroPrepare_primitive]; rfl

theorem fig15ZeroRestore_length : fig15ZeroRestore.length=1022 := by
  rw [circuit_length_primitive,fig15ZeroRestore_primitive]; rfl

theorem zeroDivisionProgram_slots (n start : Nat) :
    (zeroDivisionProgram n start).2.gateSlots≤676000000 := by
  have h := divisionProgram_slots n start
  simp only [zeroDivisionProgram,surroundCompiled_slots,fig15ZeroPrepare_length,fig15ZeroRestore_length]
  omega

theorem zeroMultiplicationProgram_slots (n start : Nat) :
    (zeroMultiplicationProgram n start).2.gateSlots≤676000000 := by
  have h := multiplicationProgram_slots n start
  simp only [zeroMultiplicationProgram,surroundCompiled_slots,fig15ZeroPrepare_length,fig15ZeroRestore_length]
  omega

theorem xNegateProgram_slots (n start : Nat) :
    (xNegateProgram n start).2.gateSlots≤26370 := by
  have h := modularNegateProgram_slots_le n start (List.range' 263 256) (List.range' 7 256)
    (constantBits 256 ShorECDLP.p) 836 559 560 561 558 (by simp) (by simp) (by simp)
  simpa only [List.length_range'] using h

theorem pointSquareProgram_slots (n start : Nat) :
    (pointSquareProgram n start).2.gateSlots≤15750663 := by
  exact squareSubtractProgram_slots256 n start _ _ _ _ _ _ _ _ _ _ _ _
    (by simp) (by simp) (by simp) (by simp [secp256k1ReductionConstantBits]) (by simp)

theorem coordinateProgram_slots (start : Nat) :
    (coordinateProgram start).2.gateSlots≤1500000000 := by
  have h := sequenceProgram_slots_le 32768 coordinateSegments
    ([17449459,17502203,676000000,15750663,17449459,676000000,26370,17449459,17502203] : List Nat) (by
      unfold coordinateSegments
      refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil))))))))
      · intro s; exact fieldLookupAddProgram_slots _ _ s (by simp)
      · intro s; exact signedFieldProgram_slots _ s
      · intro s; exact zeroDivisionProgram_slots _ s
      · intro s; exact pointSquareProgram_slots _ s
      · intro s; exact fieldLookupAddProgram_slots _ _ s (by simp)
      · intro s; exact zeroMultiplicationProgram_slots _ s
      · intro s; exact xNegateProgram_slots _ s
      · intro s; exact fieldLookupAddProgram_slots _ _ s (by simp)
      · intro s; exact signedFieldProgram_slots _ s) start
  simp only [List.sum_cons,List.sum_nil] at h
  unfold coordinateProgram
  omega


theorem reindexCompiled_slots {n m start : Nat} (f : Fin n → Fin m)
    (p : (count : Nat) × Straight n start (start+count)) :
    (reindexCompiled f p).2.gateSlots=p.2.gateSlots := by
  exact reindexStraight_gateSlots f p.2

attribute [local irreducible] reindexCompiled sharedCoordinateProgram sharedYNegateProgram
  ipxProgram ipxWindowCore ipxWindowPrepared actualIpxWindow actualFirstWindow
  ipxLeftWindows ipxRightWindows ipxOuterPlan

theorem sharedCoordinateProgram_slots (w : OddWindow) (start : Nat) :
    (sharedCoordinateProgram w start).2.gateSlots≤1500000000 := by
  simp only [sharedCoordinateProgram,reindexCompiled_slots]
  exact coordinateProgram_slots start

theorem sharedYNegateProgram_slots (w : OddWindow) (start : Nat) :
    (sharedYNegateProgram w start).2.gateSlots≤26372 := by
  simp only [sharedYNegateProgram,reindexCompiled_slots]
  exact yNegateProgram_slots_le start

theorem ipxWindowCore_slots (w : OddWindow) (start : Nat) :
    (ipxWindowCore w start).2.gateSlots≤2683845980 := by
  have h := sequenceProgram_slots_le 983040 (ipxWindowSegments w)
    ([1500000000,26372,1183793236,26372] : List Nat) (by
      unfold ipxWindowSegments
      refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ .nil)))
      · intro s; exact sharedCoordinateProgram_slots w s
      · intro s; exact sharedYNegateProgram_slots w s
      · intro s; exact ipxProgram_slots w s
      · intro s; exact sharedYNegateProgram_slots w s) start
  simpa only [ipxWindowCore,List.sum_cons,List.sum_nil] using h

theorem ipxWindowPrepared_slots (w : OddWindow) (start : Nat) :
    (ipxWindowPrepared w start).2.gateSlots≤3000000000 := by
  have h := ipxWindowCore_slots w start
  simp only [ipxWindowPrepared,surroundCompiled_slots,signedAddressCircuit_length,
    pointLookupAddress,List.length_range']
  omega

theorem actualIpxWindow_slots (w : OddWindow) (start : Nat) :
    ((actualIpxWindow w).program start).gateSlots≤3000000000 := by
  simp only [actualIpxWindow,closedWindow,shiftStraight_gateSlots,relabelStraight_slots]
  exact ipxWindowPrepared_slots w 0

theorem ipxOuterPlan_windowSlots :
    ∀ w ∈ ipxOuterPlan.left.toList ++ ipxOuterPlan.right.toList,
      ∀ start, (w.program start).gateSlots≤3000000000 := by
  intro w hw start
  simp only [ipxOuterPlan,standardOuterPlan,Vector.toList,List.toList_toArray,
    ipxLeftWindows,ipxRightWindows,List.mem_append,List.mem_cons,List.mem_ofFn] at hw
  rcases hw with (rfl | ⟨i,rfl⟩) | ⟨i,rfl⟩
  · exact (actualFirstWindow_slots start).trans (by decide)
  · exact actualIpxWindow_slots _ start
  · exact actualIpxWindow_slots _ start

/-- Syntactic slots of the actual 56-round program. This counts every fixed
correction slot; it does not assert physical validity, success, or wire support. -/
theorem ipxOuterPlan_slots (start : Nat) :
    (ipxOuterPlan.repeat 56 start).gateSlots≤5000000000000 := by
  exact (ipxOuterPlan.repeat_slots_le 3000000000 ipxOuterPlan_windowSlots 56 start).trans (by decide)

/-- Syntactic slots of the entrant's 6-round program. -/
theorem ipxOuterPlan_rounds_slots (start : Nat) :
    (ipxOuterPlan.repeat 6 start).gateSlots≤5000000000000 := by
  exact (ipxOuterPlan.repeat_slots_le 3000000000 ipxOuterPlan_windowSlots 6 start).trans (by decide)


end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/MeasurementBridge ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/MeasurementBridge.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

/-- The branch tree retains every measurement outcome, including zero-mass branches. -/
theorem adaptive_run_nonempty (a : AdaptiveCircuit) : ∃ b, b ∈ a.run := by
  induction a with
  | done => exact ⟨_, List.mem_singleton_self _⟩
  | unitary gs a ih =>
    obtain ⟨b,hb⟩ := ih
    exact ⟨_, List.mem_map_of_mem hb⟩
  | xMeasureReset w a b iha ihb =>
    obtain ⟨c,hc⟩ := iha
    exact ⟨_, List.mem_append_left _ (List.mem_map_of_mem hc)⟩

/-- Uniform actual branch record lengths determine the syntactic measurement count. -/
theorem measurementCount_of_uniform_run (a : AdaptiveCircuit) (k : Nat)
    (h : ∀ b ∈ a.run, b.history.length = k) : a.measurementCount = k := by
  induction a generalizing k with
  | done => exact h ⟨[],LinearMap.id⟩ (List.mem_singleton_self _)
  | unitary gs a ih =>
    apply ih
    intro b hb
    have hh := h _ (List.mem_map.mpr ⟨b,hb,rfl⟩)
    exact hh
  | xMeasureReset w a b iha ihb =>
    have ha : ∀ c ∈ a.run, c.history.length + 1 = k := by
      intro c hc
      exact h _ (List.mem_append_left _ (List.mem_map_of_mem hc))
    have hb : ∀ c ∈ b.run, c.history.length + 1 = k := by
      intro c hc
      exact h _ (List.mem_append_right _ (List.mem_map_of_mem hc))
    have hk : 0 < k := by
      obtain ⟨c,hc⟩ := adaptive_run_nonempty a
      have := ha c hc
      omega
    have hca := iha (k-1) (by intro c hc; have := ha c hc; omega)
    have hcb := ihb (k-1) (by intro c hc; have := hb c hc; omega)
    simp only [AdaptiveCircuit.measurementCount,hca,hcb,max_self]
    omega

/-- Transfer measurement counts through a proved execution binding, without
unfolding the compiled circuit or enumerating its branches. -/
theorem compiled_count_of_run {n start : Nat}
    (p : (count : Nat) × Straight n start (start+count))
    (read : ConstantBit n → Bool) (history : Fin start → Bool) (a : AdaptiveCircuit)
    (h : compiledRun p read history = a.run) : p.1 = a.measurementCount := by
  apply Eq.symm
  apply measurementCount_of_uniform_run
  intro b hb
  rw [← h] at hb
  have hh := straight_history_length p.2 read history b hb
  simpa using hh
end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/WindowCounts ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/WindowCounts.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
attribute [local irreducible] sharedCoordinateProgram yNegateProgram ipxProgram
  ipxWindowCore ipxWindowPrepared signedLookupCoordinateProgram primitiveResources
  sharedYNegateProgram actualIpxWindow ipxLeftWindows ipxRightWindows
  ipxSource windowYNegate sequenceCircuit ipxWindowSources

private theorem adder_counts : pointLookupAdderPrimitives.toffoli=2813 ∧
    pointLookupAdderPrimitives.phase=0 ∧ pointLookupAdderPrimitives.measurements=511 := by
  decide +kernel
private theorem lookup_counts (table : Nat → Nat) :
    (pointLookupPrimitives table).toffoli=68347 ∧
    (pointLookupPrimitives table).phase=0 ∧ (pointLookupPrimitives table).measurements=66045 := by
  simp only [pointLookupPrimitives,lookupWordPrimitives,pointLookupAddress,List.length_range',
    PrimitiveResources.add,adder_counts.1,adder_counts.2.1,adder_counts.2.2]
  decide

/-- Source coordinate arithmetic includes both zero-allowed field operations. -/
theorem coordinate_numeric_counts (x y : Nat → Nat) :
    (signedLookupCoordinateProgram x y).tCount = 510203526 ∧
    (signedLookupCoordinateProgram x y).measurementCount = 30272702 := by
  have h : (primitiveResources (signedLookupCoordinateProgram x y)).toffoli = 72886218 ∧
      (primitiveResources (signedLookupCoordinateProgram x y)).phase = 0 ∧
      (primitiveResources (signedLookupCoordinateProgram x y)).measurements = 30272702 := by
    rw [signedLookupCoordinateProgram_primitive]
    simp only [signedCoordinatePrimitives,signedPointLookupPrimitives,PrimitiveResources.add,
      (lookup_counts _).1,(lookup_counts _).2.1,(lookup_counts _).2.2]
    decide
  have ht := primitiveResources_T_of_no_phase _ h.2.1
  rw [h.1] at ht
  exact ⟨ht,by simpa only [primitiveResources] using h.2.2⟩

/-- One actual sign-negation segment, including its two X wrappers. -/
theorem windowYNegate_numeric_counts :
    windowYNegate.tCount = 21434 ∧ windowYNegate.measurementCount = 1022 := by
  have h := controlledModularNegate256_primitive_exact (List.range' 580 256) (List.range' 7 256)
    (constantBits 256 ShorECDLP.p) 854 559 560 561 558 (by simp) (by simp) (by simp)
  have he : primitiveResources (controlledModularNegate (List.range' 580 256) (List.range' 7 256)
      (constantBits 256 ShorECDLP.p) 854 559 560 561 558)=⟨3068,4088,12983,3062,0,1022⟩ := by
    rw [h]
    decide +kernel
  have ht := primitiveResources_T_of_no_phase _ (congrArg PrimitiveResources.phase he)
  rw [he] at ht
  have hm := congrArg PrimitiveResources.measurements he
  have hn := negativeControlledModularNegate_resources (List.range' 580 256) (List.range' 7 256)
    (constantBits 256 ShorECDLP.p) 854 559 560 561 558
  unfold windowYNegate
  rw [hn.1,hn.2]
  constructor
  · exact ht
  · simpa only [primitiveResources] using hm

theorem sharedCoordinateProgram_count (w : OddWindow) (start : Nat) :
    (sharedCoordinateProgram w start).1 = 30272702 := by
  have h := compiled_count_of_run (sharedCoordinateProgram w start)
    (readConstant coefficientAt (0 : Point)) (fun _ => false) _
    (sharedCoordinateProgram_run w start 0 (by simp) (fun _ => false))
  exact h.trans (coordinate_numeric_counts _ _).2

theorem sharedYNegateProgram_count (w : OddWindow) (start : Nat) :
    (sharedYNegateProgram w start).1 = 1022 := by
  exact (compiled_count_of_run _ (fun _ => false) (fun _ => false) _
    (sharedYNegateProgram_run w start (fun _ => false) (fun _ => false))).trans
    windowYNegate_numeric_counts.2

theorem sharedYNegateProgram_tCount (w : OddWindow) (start : Nat)
    (read : ConstantBit 983040 → Bool) (history : Fin start → Bool) :
    compiledTCount (sharedYNegateProgram w start) read history = windowYNegate.tCount := by
  simp only [sharedYNegateProgram,reindexCompiled,compiledTCount,reindexStraight_instantiate]
  unfold windowYNegate
  exact yNegateProgram_tCount start _ history

theorem ipxWindowCore_tCount (w : OddWindow) (start : Nat) (Q : Point) (hQ : order • Q = 0)
    (history : Fin start → Bool) :
    compiledTCount (ipxWindowCore w start) (readConstant coefficientAt Q) history =
      (sequenceCircuit (ipxWindowSources Q w)).tCount := by
  unfold ipxWindowCore
  apply sequenceProgram_tCount
  unfold ipxWindowSegments ipxWindowSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ .nil)))
  · intro cursor h; exact sharedCoordinateProgram_tCount w cursor Q hQ h
  · intro cursor h; exact sharedYNegateProgram_tCount w cursor _ h
  · intro cursor h; exact ipxProgram_tCount w cursor Q h
  · intro cursor h; exact sharedYNegateProgram_tCount w cursor _ h

theorem sequenceCircuit_four_tCount (a b c d : AdaptiveCircuit) :
    (sequenceCircuit [a,b,c,d]).tCount = a.tCount+b.tCount+c.tCount+d.tCount := by
  simp only [sequenceCircuit,adaptive_tCount_seq,AdaptiveCircuit.tCount]
  omega

theorem ipxWindowSources_tCount (Q : Point) (w : OddWindow) :
    (sequenceCircuit (ipxWindowSources Q w)).tCount = 513314039 := by
  unfold ipxWindowSources
  rw [sequenceCircuit_four_tCount,(coordinate_numeric_counts _ _).1,
    windowYNegate_numeric_counts.1,ipxSource_tCount]

theorem actualFirstWindow_tCount (start : Nat) (Q : Point) (hQ : order • Q = 0)
    (history : Fin start → Bool) :
    ((actualFirstWindow.program start).instantiate (readConstant coefficientAt Q) history).tCount = 458745 := by
  simp only [actualFirstWindow,reindexStraight_instantiate,
    readConstant_reindex firstIndex _ _ Q coefficientAt_first]
  exact firstLookupProgram_tCount start Q hQ history

theorem actualIpxWindow_tCount (w : OddWindow) (start : Nat) (Q : Point) (hQ : order • Q = 0)
    (history : Fin start → Bool) :
    (((actualIpxWindow w).program start).instantiate (readConstant coefficientAt Q) history).tCount =
      513314039 := by
  have h := surroundCompiled_tCount (signedAddressCircuit 836 854 pointLookupAddress)
    (signedAddressCircuit 836 854 pointLookupAddress) (ipxWindowCore w 0)
    (sequenceCircuit (ipxWindowSources Q w)) (readConstant coefficientAt Q) Fin.elim0
    (ipxWindowCore_tCount w 0 Q hQ Fin.elim0)
  simp only [AdaptiveCircuit.tCount,adaptive_tCount_seq,signedAddressCircuit_tCount,
    Nat.zero_add,Nat.add_zero,ipxWindowSources_tCount] at h
  simp only [actualIpxWindow,closedWindow_run,relabelStraight_instantiate,AdaptiveCircuit.relabel_tCount]
  change compiledTCount (ipxWindowPrepared w 0) (readConstant coefficientAt Q) Fin.elim0 = _
  unfold ipxWindowPrepared
  exact h

theorem ipxWindowCore_count (w : OddWindow) (start : Nat) :
    (ipxWindowCore w start).1 = 30700717 := by
  simp only [ipxWindowCore,ipxWindowSegments,sequenceProgram,appendCompiled,
    sharedCoordinateProgram_count,sharedYNegateProgram_count,ipxProgram_count]

theorem surroundCompiled_count {n start : Nat} (before after : Circuit)
    (p : (count : Nat) × Straight n start (start+count)) :
    (surroundCompiled before after p).1 = p.1 := by
  simp only [surroundCompiled,prependCompiled,appendCompiled,Nat.add_zero]

theorem actualIpxWindow_count (w : OddWindow) :
    (actualIpxWindow w).count = 30700717 := by
  unfold actualIpxWindow closedWindow
  change 0 + (ipxWindowPrepared w 0).1 = 30700717
  rw [Nat.zero_add]
  have hp : (ipxWindowPrepared w 0).1 = (ipxWindowCore w 0).1 := by
    unfold ipxWindowPrepared
    exact surroundCompiled_count _ _ _
  rw [hp,ipxWindowCore_count]

theorem actualFirstWindow_count : actualFirstWindow.count = 65535 := rfl

theorem axisCount_constant {n : Nat} (ws : List (OuterWindow n)) (m : Nat)
    (hm : ∀ w ∈ ws, w.count = m) : axisCount ws = ws.length * (m+16) := by
  induction ws with
  | nil => simp [axisCount]
  | cons w ws ih =>
    rw [axisCount,hm w (by simp),ih (by intro v hv; exact hm v (by simp [hv]))]
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem ipxLeftWindows_count : axisCount ipxLeftWindows = 460576546 := by
  unfold ipxLeftWindows
  rw [axisCount,actualFirstWindow_count]
  rw [axisCount_constant _ 30700717]
  · simp
  · intro w hw
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    exact actualIpxWindow_count _

theorem ipxRightWindows_count : axisCount ipxRightWindows = 399109529 := by
  unfold ipxRightWindows
  rw [axisCount_constant _ 30700717]
  · simp
  · intro w hw
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    exact actualIpxWindow_count _

theorem standardOuterPlan_lists_stride {n : Nat} (left right : List (OuterWindow n))
    (hl : left.length = 16) (hr : right.length = 13) (reset : List Wire) :
    (standardOuterPlan ⟨left.toArray,by simpa using hl⟩
      ⟨right.toArray,by simpa using hr⟩ reset).stride =
      axisCount left + axisCount right + reset.length := by
  simp only [OuterPlan.stride,standardOuterPlan,Vector.toList,List.toList_toArray]

theorem ipxOuterPlan_stride : ipxOuterPlan.stride = 859686929 := by
  have h := standardOuterPlan_lists_stride ipxLeftWindows ipxRightWindows
    ipxLeftWindows_length ipxRightWindows_length resetWires
  apply h.trans
  rw [ipxLeftWindows_count,ipxRightWindows_count,resetWires_length]

/-- Exact final record count includes the first lookup, all 28 addition windows,
all Fourier measurements, and the full 854-wire reset in each of 56 rounds. -/
theorem ipxOuterPlan_finalCursor : 56 * ipxOuterPlan.stride = 48142468024 := by
  rw [ipxOuterPlan_stride]

/-- Exact final record count of the entrant's 6-round program. -/
theorem ipxOuterPlan_finalCursor6 : 6 * ipxOuterPlan.stride = 5158121574 := by
  rw [ipxOuterPlan_stride]

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/StructuralSupport ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/StructuralSupport.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

/-- Every mentioned wire, including disabled constant-controlled gates. -/
def templateGateWires {n : Nat} : TemplateGate n → List Wire
  | .literal g => gateWires g
  | .whenBit _ _ g => gateWires g

/-- Syntactic support includes measurement targets and all record-controlled gates. -/
def straightWires {n s e : Nat} : Straight n s e → List Wire
  | .done => []
  | .gate g p => templateGateWires g ++ straightWires p
  | .recordGate _ _ g p => gateWires g ++ straightWires p
  | .measure w p => w :: straightWires p

private theorem subset_append {a b c d : List Wire} (h : a ⊆ c) (k : b ⊆ d) :
    a ++ b ⊆ c ++ d := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact List.mem_append_left _ (h hx)
  · exact List.mem_append_right _ (k hx)

theorem templateGate_instantiate_support {n : Nat} (g : TemplateGate n)
    (read : ConstantBit n → Bool) : circuitWires (g.instantiate read) ⊆ templateGateWires g := by
  cases g <;> simp only [TemplateGate.instantiate,templateGateWires]
  · simp [circuitWires]
  · split <;> simp [circuitWires]

theorem straight_instantiate_support {n s e : Nat} (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    (p.instantiate read history).wires ⊆ straightWires p := by
  induction p with
  | done => exact List.Subset.refl _
  | gate g p ih =>
    exact subset_append (templateGate_instantiate_support g read) (ih history)
  | recordGate i v g p ih =>
    simp only [Straight.instantiate,AdaptiveCircuit.wires,straightWires]
    apply subset_append _ (ih history)
    split <;> simp [circuitWires]
  | measure w p ih =>
    intro x hx
    simp only [Straight.instantiate,AdaptiveCircuit.wires,List.mem_cons,List.mem_append] at hx
    rcases hx with rfl | hx | hx
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih _ hx)
    · exact List.mem_cons_of_mem _ (ih _ hx)

theorem straightWires_append {n a b c : Nat} (p : Straight n a b) (q : Straight n b c) :
    straightWires (p.append q)=straightWires p ++ straightWires q := by
  induction p <;> simp_all only [Straight.append,straightWires,List.nil_append,List.append_assoc,List.cons_append]

theorem straightWires_castFinish {n s e f : Nat} (h : e=f) (p : Straight n s e) :
    straightWires (castFinish h p)=straightWires p := by subst f; rfl

theorem straightWires_shift {n s e : Nat} (p : Straight n s e) (offset : Nat) :
    straightWires (shiftStraight offset p)=straightWires p := by
  induction p <;> simp_all only [shiftStraight,straightWires]

theorem templateGateWires_reindex {n m : Nat} (f : Fin n → Fin m) (g : TemplateGate n) :
    templateGateWires (reindexGate f g)=templateGateWires g := by cases g <;> rfl

theorem straightWires_reindex {n m s e : Nat} (f : Fin n → Fin m) (p : Straight n s e) :
    straightWires (reindexStraight f p)=straightWires p := by
  induction p <;> simp_all only [reindexStraight,straightWires,templateGateWires_reindex]

theorem gateProgram_support {n s : Nat} (gs : List (TemplateGate n)) :
    straightWires (gateProgram (cursor := s) gs)=gs.flatMap templateGateWires := by
  induction gs <;> simp_all only [gateProgram,straightWires,List.flatMap_nil,List.flatMap_cons]

theorem literalProgram_support (n start : Nat) (gs : Circuit) :
    straightWires (literalProgram (n := n) (s := start) gs)=circuitWires gs := by
  simp only [literalProgram,gateProgram_support,List.flatMap_map,templateGateWires,circuitWires]

theorem recordGates_support {n s e : Nat} (i : Fin s) (gs : Circuit) (p : Straight n s e) :
    straightWires (recordGates i gs p)=circuitWires gs ++ straightWires p := by
  induction gs <;> simp_all only [recordGates,straightWires,circuitWires,List.flatMap_nil,List.flatMap_cons,List.nil_append,List.append_assoc]

theorem appendCompiled_support {n start : Nat} (p : (count : Nat) × Straight n start (start+count))
    (q : (count : Nat) × Straight n (start+p.1) (start+p.1+count)) :
    straightWires (appendCompiled p q).2=straightWires p.2 ++ straightWires q.2 := by
  simp only [appendCompiled,straightWires_castFinish,straightWires_append]

theorem surroundCompiled_support {n start : Nat} (before after : Circuit)
    (p : (count : Nat) × Straight n start (start+count)) :
    straightWires (surroundCompiled before after p).2=
      circuitWires before ++ straightWires p.2 ++ circuitWires after := by
  simp only [surroundCompiled,prependCompiled,appendCompiled_support,straightWires_append,literalProgram_support,List.append_assoc]


theorem templateGateWires_relabel {n : Nat} (e : Wire ≃ Wire) (g : TemplateGate n) :
    templateGateWires (relabelTemplateGate e g)=(templateGateWires g).map e := by
  cases g <;> rename_i g <;> cases g <;> rfl

theorem straightWires_relabel {n s t : Nat} (e : Wire ≃ Wire) (p : Straight n s t) :
    straightWires (relabelStraight e p)=(straightWires p).map e := by
  have hg (g : Gate) : gateWires (g.relabel e)=(gateWires g).map e := by cases g <;> rfl
  induction p <;> simp_all only [relabelStraight,straightWires,templateGateWires_relabel,List.map_nil,List.map_append,List.map_cons]

theorem reindexCompiled_support {n m start : Nat} (f : Fin n → Fin m)
    (p : (count : Nat) × Straight n start (start+count)) :
    straightWires (reindexCompiled f p).2=straightWires p.2 := by
  exact straightWires_reindex f p.2

theorem relabelCompiled_support {n start : Nat} (e : Wire ≃ Wire)
    (p : (count : Nat) × Straight n start (start+count)) :
    straightWires (relabelCompiled e p).2=(straightWires p.2).map e := by
  exact straightWires_relabel e p.2

theorem sequenceProgram_support (n : Nat) (ps : List (FixedSegment n)) (support : List Wire)
    (h : ∀ p ∈ ps, ∀ start, straightWires (p start).2 ⊆ support) (start : Nat) :
    straightWires (sequenceProgram n ps start).2 ⊆ support := by
  induction ps generalizing start with
  | nil => exact List.nil_subset _
  | cons p ps ih =>
    simp only [sequenceProgram,appendCompiled_support]
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact h p (by simp) start hw
    · exact ih (fun p hp => h p (by simp [hp])) _ hw

theorem collectProgram_support (n : Nat)
    (next : (cursor : Nat) → List (Fin cursor) → (count : Nat) × Straight n cursor (cursor+count))
    (support : List Wire) (h : ∀ cursor prior, straightWires (next cursor prior).2 ⊆ support)
    (ws : List Wire) (hw : ws ⊆ support) (start : Nat) (prior : List (Fin start)) :
    straightWires (collectProgram n next ws start prior).2 ⊆ support := by
  induction ws generalizing start with
  | nil => exact h start prior
  | cons w ws ih =>
    simp only [collectProgram,straightWires_castFinish,straightWires,List.cons_subset]
    exact ⟨hw List.mem_cons_self,ih (fun _ hx => hw (List.mem_cons_of_mem _ hx)) _ _⟩

theorem resetProgram_support_static (n start : Nat) (ws : List Wire) :
    straightWires (resetProgram n start ws)=ws := by
  induction ws generalizing start <;> simp_all only [resetProgram,straightWires_castFinish,straightWires]

/-- A syntactic allocation is a sound support certificate for every readout and
history, including disabled constant gates and both measurement outcomes. -/
theorem compiled_support_of_static {n start : Nat}
    (p : (count : Nat) × Straight n start (start+count)) (support : List Wire)
    (hp : straightWires p.2 ⊆ support) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    (p.2.instantiate read history).wires ⊆ support :=
  (straight_instantiate_support p.2 read history).trans hp


def lookupOpWires {n : Nat} : LookupOp n → List Wire
  | .gates gs => gs.flatMap templateGateWires
  | .erase a b t => t :: circuitWires (controlledZ a b)

theorem lookupProgram_support (n : Nat) (ops : List (LookupOp n)) (start : Nat) :
    straightWires (lookupProgram n ops start)=ops.flatMap lookupOpWires := by
  induction ops generalizing start with
  | nil => rfl
  | cons op ops ih =>
    cases op <;> simp only [lookupProgram,straightWires_castFinish,straightWires_append,
      gateProgram_support,andEraseProgram,straightWires,recordGates_support,List.append_nil,
      List.flatMap_cons,lookupOpWires,ih]

theorem ordinaryOp_support {n : Nat} (gs : Circuit) :
    lookupOpWires (@ordinaryOp n gs)=circuitWires gs := by
  simp only [ordinaryOp,lookupOpWires,List.flatMap_map,templateGateWires,circuitWires]

theorem unaryLookupOps_support {n : Nat} (leaf : Nat → Wire → List (TemplateGate n))
    (tree : UnaryActionTree) (q : Wire) (paths support : List Wire)
    (hq : q ∈ support) (hp : paths ⊆ support) (hb : tree.indexWires ⊆ support)
    (hl : ∀ l c, c ∈ support → (leaf l c).flatMap templateGateWires ⊆ support) :
    ∀ op ∈ unaryLookupOps leaf tree q paths, lookupOpWires op ⊆ support := by
  induction tree generalizing q paths with
  | leaf l => simpa only [unaryLookupOps,List.forall_mem_singleton,lookupOpWires] using hl l q hq
  | node bit zero one ihz iho =>
    cases paths with
    | nil => simp [unaryLookupOps]
    | cons path rest =>
      have hpath := hp List.mem_cons_self
      have hrest : rest ⊆ support := fun _ hx => hp (List.mem_cons_of_mem _ hx)
      have hbit : bit ∈ support := hb List.mem_cons_self
      have hz : zero.indexWires ⊆ support := fun _ hx => hb (List.mem_cons_of_mem _ (List.mem_append_left _ hx))
      have ho : one.indexWires ⊆ support := fun _ hx => hb (List.mem_cons_of_mem _ (List.mem_append_right _ hx))
      have hz' := ihz path rest hpath hrest hz
      have ho' := iho path rest hpath hrest ho
      simp only [unaryLookupOps,List.forall_mem_append,List.forall_mem_cons,List.mem_nil_iff,false_implies]
      refine ⟨⟨⟨⟨⟨?_,fun _ => trivial⟩,hz'⟩,⟨?_,fun _ => trivial⟩⟩,ho'⟩,?_,?_,?_,?_,fun _ => trivial⟩
      all_goals simp [ordinaryOp,templateGateWires,lookupOpWires,computeZeroAnd,controlledZ,circuitWires,gateWires,hbit,hq,hpath]

theorem lookupLeafGates_support {n : Nat} (q : Wire) (ports : List (ConstantBit n × Wire))
    (support : List Wire) (hq : q ∈ support) (hp : ∀ p ∈ ports, p.2 ∈ support) :
    (lookupLeafGates q ports).flatMap templateGateWires ⊆ support := by
  intro w hw
  simp only [lookupLeafGates,List.flatMap_map,List.mem_flatMap] at hw
  obtain ⟨p,hp',hw⟩ := hw
  simp only [templateGateWires,gateWires,List.mem_cons,List.mem_nil_iff,or_false] at hw
  rcases hw with rfl | rfl
  · exact hq
  · exact hp p hp'

theorem pointLeaf_support {n : Nat} (row : Fin n) (q : Wire) (support : List Wire)
    (hq : q ∈ support) (hp : pointLogicalWires ⊆ support) :
    (pointLeaf row q).flatMap templateGateWires ⊆ support := by
  apply lookupLeafGates_support q _ support hq
  intro p hp'
  exact hp (List.of_mem_zip hp').2

theorem firstLookupOps_support : ∀ op ∈ firstLookupOps, lookupOpWires op ⊆ resetWires := by
  apply unaryLookupOps_support
  · simp [resetWires]
  · intro w hw
    apply List.mem_append_left
    apply List.mem_append_left
    simp only [List.mem_range'_1] at hw
    simp only [List.mem_range]
    omega
  · intro w hw
    have h := (tableAddressTree_mem_index (List.range' 855 16) 0 1 w).mp hw
    exact List.mem_append_right _ h
  · intro l q hq
    apply pointLeaf_support _ q resetWires hq
    intro w hw
    simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,
      List.mem_range'_1,List.mem_cons,List.mem_nil_iff,or_false] at hw
    simp only [resetWires,List.mem_append,List.mem_range,List.mem_singleton,List.mem_range'_1]
    rcases hw with hw | hw | hw
    · exact Or.inl (Or.inl (by omega))
    · exact Or.inl (Or.inl (by omega))
    · exact Or.inl (Or.inr hw)

theorem actualFirstWindow_support_static (start : Nat) :
    straightWires (actualFirstWindow.program start) ⊆ resetWires := by
  simp only [actualFirstWindow,straightWires_reindex,firstLookupProgram,
    straightWires_castFinish,lookupProgram_support]
  intro w hw
  obtain ⟨op,hop,hw⟩ := List.mem_flatMap.mp hw
  exact firstLookupOps_support op hop hw

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/BatchSupport ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/BatchSupport.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

/-- Turn the source gate-by-gate support judgment into the wire collector used
by the challenge. No semantic equivalence is used to infer support. -/
theorem circuitWires_subset_of_usesOnly {support : List Wire} {gs : Circuit}
    (h : PaperCircuitUsesOnly support gs) : circuitWires gs ⊆ support := by
  intro w hw
  obtain ⟨g,hg,hw⟩ := List.mem_flatMap.mp hw
  exact h g hg w hw

theorem registerEqualCircuit_support (cells : List (Wire × Wire)) (flag : Wire)
    (scratch support : List Wire) (hf : flag ∈ support) (hs : scratch ⊆ support)
    (hc : ∀ c ∈ cells, c.1 ∈ support ∧ c.2 ∈ support) :
    circuitWires (registerEqualCircuit cells flag scratch) ⊆ support := by
  have hx : circuitWires (xorWordCircuit cells) ⊆ support := by
    intro w hw
    obtain ⟨g,hg,hw⟩ := List.mem_flatMap.mp hw
    obtain ⟨c,hc',rfl⟩ := List.mem_map.mp hg
    simp only [gateWires,List.mem_cons,List.mem_nil_iff,or_false] at hw
    rcases hw with rfl | rfl
    · exact (hc c hc').1
    · exact (hc c hc').2
  have he : circuitWires (computeEqConst (cells.map Prod.snd) 0 flag scratch) ⊆ support := by
    apply (circuitWires_subset_of_usesOnly (computeEqConst_usesOnly _ _ _ _)).trans
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨c,hc',rfl⟩ := List.mem_map.mp hw
      exact (hc c hc').2
    · rcases List.mem_cons.mp hw with rfl | hw
      · exact hf
      · exact hs hw
  simpa only [registerEqualCircuit,circuitWires,List.flatMap_append,List.append_subset] using
    And.intro (And.intro hx he) hx

theorem endpointTranspositionCircuit_support {n : Nat} (a b target : Fin n → Wire)
    (flag : Wire) (scratch support : List Wire)
    (ha : ∀ i, a i ∈ support) (hb : ∀ i, b i ∈ support) (ht : ∀ i, target i ∈ support)
    (hf : flag ∈ support) (hs : scratch ⊆ support) :
    circuitWires (endpointTranspositionCircuit a b target flag scratch) ⊆ support := by
  have he (r : Fin n → Wire) (hr : ∀ i, r i ∈ support) :
      circuitWires (registerEqualCircuit (equalityCells r target) flag scratch) ⊆ support := by
    apply registerEqualCircuit_support _ _ _ _ hf hs
    intro c hc
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
    exact ⟨hr i,ht i⟩
  have hu : circuitWires (endpointWordCircuit flag (endpointUpdateCells a b target)) ⊆ support := by
    intro w hw
    obtain ⟨g,hg,hw⟩ := List.mem_flatMap.mp hw
    obtain ⟨c,hc,hg⟩ := List.mem_flatMap.mp hg
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
    simp only [endpointBitCircuit,List.mem_cons,List.mem_nil_iff,or_false] at hg
    rcases hg with rfl | rfl
    all_goals simp only [gateWires,List.mem_cons,List.mem_nil_iff,or_false] at hw
    all_goals rcases hw with rfl | rfl | rfl
    all_goals first | exact hf | exact ha i | exact hb i | exact ht i
  have he' : circuitWires (endpointTests a b target flag scratch) ⊆ support := by
    simpa only [endpointTests,circuitWires,List.flatMap_append,List.append_subset] using And.intro (he a ha) (he b hb)
  simpa only [endpointTranspositionCircuit,circuitWires,List.flatMap_append,List.append_subset] using
    And.intro (And.intro he' hu) he'


/-- Static support of a constant-controlled leaf, including disabled slots. -/
theorem endpointSelectGates_support {n : Nat} (control : Wire)
    (ports : List (Wire × EndpointBit n)) (support : List Wire)
    (hq : control ∈ support) (hp : ∀ p ∈ ports, p.1 ∈ support) :
    (endpointSelectGates control ports).flatMap templateGateWires ⊆ support := by
  intro w hw
  obtain ⟨g,hg,hw⟩ := List.mem_flatMap.mp hw
  obtain ⟨p,hp',hg⟩ := List.mem_flatMap.mp hg
  have hpw := hp p hp'
  rcases p with ⟨port,bit⟩
  cases bit with
  | inl bit =>
    cases bit with
    | false => simp [endpointSelectGate] at hg
    | true =>
      simp only [endpointSelectGate,List.mem_singleton] at hg
      subst g
      rcases (show w = control ∨ w = port by simpa [templateGateWires,gateWires] using hw) with rfl | rfl
      · exact hq
      · exact hpw
  | inr bit =>
    simp only [endpointSelectGate,List.mem_singleton] at hg
    subst g
    rcases (show w = control ∨ w = port by simpa [templateGateWires,gateWires] using hw) with rfl | rfl
    · exact hq
    · exact hpw

theorem batchLeaf_support {n : Nat} (row : Fin n) (base control : Wire)
    (selection : List (Fin 8 × Fin 5)) (support : List Wire)
    (hq : control ∈ support) (hb : List.range' base 2565 ⊆ support) :
    (batchLeaf row base control selection).flatMap templateGateWires ⊆ support := by
  simp only [batchLeaf,List.flatMap_append,List.append_subset]
  constructor
  · apply endpointSelectGates_support _ _ _ hq
    intro p hp
    exact hb (List.mem_range'_1.mpr (batchPorts_bounds row base p.1 selection (List.mem_map.mpr ⟨p,hp,rfl⟩)))
  · intro w hw
    simp only [List.flatMap_map,List.mem_flatMap] at hw
    obtain ⟨p,hp,hw⟩ := hw
    have hpw := hb (List.mem_range'_1.mpr (batchTags_bounds base p selection hp))
    rcases (show w = control ∨ w = p by simpa [templateGateWires,gateWires] using hw) with rfl | rfl
    · exact hq
    · exact hpw

theorem batchOpCircuit_support (base : Wire) (source : Fin 4) (target : Fin 6) :
    circuitWires (batchOpCircuit base source target) ⊆ List.range' base 3590 := by
  apply endpointTranspositionCircuit_support
  all_goals simp only [List.mem_range'_1,batchWord,batchFlag,batchScratch]
  all_goals try (intro i; have := i.isLt; dsimp only [Wire] at *; omega)
  · dsimp only [Wire] at *; omega
  · intro w hw
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    have := i.isLt
    simp only [List.mem_range'_1]
    dsimp only [Wire] at *; omega

theorem batchOps_support {n : Nat} (rows : Nat → Fin n) (base : Wire)
    (tree : UnaryActionTree) (control : Wire) (paths support : List Wire)
    (hc : control ∈ support) (hp : paths ⊆ support) (ht : tree.indexWires ⊆ support)
    (hb : List.range' base 3590 ⊆ support) (ops : List BatchOp) :
    ∀ op ∈ batchOps rows base tree control paths ops, lookupOpWires op ⊆ support := by
  have hsmall : List.range' base 2565 ⊆ support := by
    intro w hw
    apply hb
    simp only [List.mem_range'_1] at hw ⊢
    omega
  induction ops with
  | nil => simp [batchOps]
  | cons op ops ih =>
    cases op with
    | query sources target =>
      simp only [batchOps,List.forall_mem_append]
      exact ⟨unaryLookupOps_support _ _ _ _ _ hc hp ht
        (fun l q hq => batchLeaf_support _ _ _ _ _ hq hsmall),ih⟩
    | swap source target =>
      simp only [batchOps,List.forall_mem_cons,ordinaryOp_support]
      exact ⟨(batchOpCircuit_support base source target).trans hb,ih⟩

theorem batchedEndpointProgram_support {n : Nat} (rows : Nat → Fin n) (base : Wire)
    (tree : UnaryActionTree) (control : Wire) (paths support : List Wire)
    (hc : control ∈ support) (hp : paths ⊆ support) (ht : tree.indexWires ⊆ support)
    (hb : List.range' base 3590 ⊆ support) (start : Nat) :
    straightWires (batchedEndpointProgram rows base tree control paths start).2 ⊆ support := by
  simp only [batchedEndpointProgram,lookupProgram_support]
  intro w hw
  obtain ⟨op,hop,hw⟩ := List.mem_flatMap.mp hw
  exact batchOps_support rows base tree control paths support hc hp ht hb batchSchedule op hop hw


/-- Allocation of the in-place XOR correction before the address-bank permutation: core wires
below 839 except the zero-divisor flag 837, and the window address. -/
def ipxRawSupport : List Wire := List.range 837 ++ [838] ++ pointLookupAddress

theorem ipxRawSupport_mem (z : Wire) (hz : z < 839 ∨ (839 ≤ z ∧ z < 854)) (h837 : z ≠ 837) :
    z ∈ ipxRawSupport := by
  simp only [ipxRawSupport,pointLookupAddress,List.mem_append,List.mem_range,List.mem_singleton,
    List.mem_range'_1]
  (try dsimp only [Wire] at *)
  omega

theorem ipxPoint_support (w : Wire) (hw : w ∈ pointLogicalWires) : w ∈ ipxRawSupport := by
  have h := pointLogicalWires_bounds w hw
  apply ipxRawSupport_mem w <;> (try dsimp only [Wire] at *) <;> omega

theorem ipxScratch_support (w : Wire) (hw : w ∈ ipxScratch) : w ∈ ipxRawSupport := by
  simp only [ipxScratch,List.mem_range'_1] at hw
  apply ipxRawSupport_mem w <;> (try dsimp only [Wire] at *) <;> omega

theorem ipxTest_support (k : Fin 4) : circuitWires (ipxTest k) ⊆ ipxRawSupport := by
  have hf : ipxFlag k ∈ ipxRawSupport := by
    have hk := ipxFlag_lt k
    apply ipxRawSupport_mem _ <;> (try dsimp only [Wire] at *) <;> omega
  have hh : ipxHalf ∈ ipxRawSupport := ipxRawSupport_mem _ (by decide) (by decide)
  have hlow : ∀ w ∈ ipxLow, w ∈ ipxRawSupport := fun w hw =>
    ipxPoint_support w ((ipxLowHigh_mem w).mpr (Or.inl hw))
  have hhigh : ∀ w ∈ ipxHigh, w ∈ ipxRawSupport := fun w hw =>
    ipxPoint_support w ((ipxLowHigh_mem w).mpr (Or.inr hw))
  have he (r : List Wire) (value : Nat) (flag : Wire) (hr : ∀ w ∈ r, w ∈ ipxRawSupport)
      (hfl : flag ∈ ipxRawSupport) :
      circuitWires (computeEqConst r value flag ipxScratch) ⊆ ipxRawSupport := by
    apply (circuitWires_subset_of_usesOnly (computeEqConst_usesOnly _ _ _ _)).trans
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact hr w hw
    · rcases List.mem_cons.mp hw with rfl | hw
      · exact hfl
      · exact ipxScratch_support w hw
  have h1 := he ipxLow 0 ipxHalf hlow hh
  have h2 := he (ipxHalf :: ipxHigh) 1 (ipxFlag k) (by
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact hh
    · exact hhigh w hw) hf
  simpa only [ipxTest,circuitWires,List.flatMap_append,List.append_subset] using
    And.intro (And.intro h1 h2) h1

theorem ipxLeaf_support {n : Nat} (row : Fin n) (q : Wire) (u : Fin 8) (v : Option (Fin 8))
    (hq : q ∈ ipxRawSupport) : (ipxLeaf row q u v).flatMap templateGateWires ⊆ ipxRawSupport := by
  simp only [ipxLeaf,List.flatMap_append,List.append_subset]
  constructor
  · apply endpointSelectGates_support _ _ _ hq
    intro p hp
    exact ipxPoint_support _ (ipxPorts_wire row u p.1 (List.mem_map.mpr ⟨p,hp,rfl⟩))
  · apply endpointSelectGates_support _ _ _ hq
    intro p hp
    exact ipxPoint_support _ (ipxPortsOpt_wire row v p.1 (List.mem_map.mpr ⟨p,hp,rfl⟩))

theorem ipxOps_support {n : Nat} (rows : Nat → Fin n) (tree : UnaryActionTree) (paths : List Wire)
    (hc : ∀ c, ipxControl c ∈ ipxRawSupport) (hp : paths ⊆ ipxRawSupport)
    (ht : tree.indexWires ⊆ ipxRawSupport) (ops : List IpxOp) :
    ∀ op ∈ ipxOps rows tree paths ops, lookupOpWires op ⊆ ipxRawSupport := by
  induction ops with
  | nil => simp [ipxOps]
  | cons op ops ih =>
    cases op with
    | query c u v =>
      simp only [ipxOps,List.forall_mem_append]
      exact ⟨unaryLookupOps_support _ _ _ _ _ (hc c) hp ht
        (fun l q hq => ipxLeaf_support _ _ _ _ hq),ih⟩
    | test k =>
      simp only [ipxOps,List.forall_mem_cons,ordinaryOp_support]
      exact ⟨ipxTest_support k,ih⟩

theorem ipxProgramOf_support {n : Nat} (rows : Nat → Fin n) (tree : UnaryActionTree)
    (paths : List Wire) (hc : ∀ c, ipxControl c ∈ ipxRawSupport) (hp : paths ⊆ ipxRawSupport)
    (ht : tree.indexWires ⊆ ipxRawSupport) (start : Nat) :
    straightWires (ipxProgramOf rows tree paths start).2 ⊆ ipxRawSupport := by
  simp only [ipxProgramOf,lookupProgram_support]
  intro w hw
  obtain ⟨op,hop,hw⟩ := List.mem_flatMap.mp hw
  exact ipxOps_support rows tree paths hc hp ht ipxSchedule op hop hw

theorem ipxRawSupport_placed (z : Wire) (hz : z ∈ ipxRawSupport) :
    windowAddressPerm 855 (by decide) z ∈ resetWires := by
  change windowAddressSwap 855 z ∈ resetWires
  simp only [ipxRawSupport,pointLookupAddress,List.mem_append,List.mem_range,List.mem_singleton,
    List.mem_range'_1] at hz
  simp only [resetWires,List.mem_append,List.mem_range,List.mem_singleton,List.mem_range'_1]
  unfold windowAddressSwap
  split_ifs <;> (try dsimp only [Wire] at *) <;> omega

attribute [local irreducible] ipxProgramOf

/-- The whole correction block, after the address-bank permutation, stays in the core reset
allocation. -/
theorem ipxProgram_support_static (w : OddWindow) (start : Nat) :
    (straightWires (ipxProgram w start).2).map (windowAddressPerm 855 (by decide)) ⊆ resetWires := by
  have hraw : straightWires (ipxProgram w start).2 ⊆ ipxRawSupport := by
    apply ipxProgramOf_support
    · intro c
      have hc := ipxControl_lt c
      apply ipxRawSupport_mem _ <;> (try dsimp only [Wire] at *) <;> omega
    · intro z hz
      simp only [pointLookupPath,List.mem_range'_1] at hz
      apply ipxRawSupport_mem _ <;> (try dsimp only [Wire] at *) <;> omega
    · intro z hz
      have h := (tableAddressTree_mem_index pointLookupAddress 0 1 z).mp hz
      simp only [pointLookupAddress,List.mem_range'_1] at h
      apply ipxRawSupport_mem _ <;> (try dsimp only [Wire] at *) <;> omega
  intro z hz
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hz
  exact ipxRawSupport_placed v (hraw hv)

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/ArithmeticSupport ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/ArithmeticSupport.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

theorem registerCorrectionProgram_support {n s e : Nat} (ws support : List Wire)
    (indices : List (Fin s)) (next : Straight n s e) (hw : ws ⊆ support)
    (hn : straightWires next ⊆ support) :
    straightWires (registerCorrectionProgram ws indices next) ⊆ support := by
  induction ws generalizing indices with
  | nil => exact hn
  | cons w ws ih =>
    cases indices with
    | nil => exact hn
    | cons i is =>
      simp only [registerCorrectionProgram,recordGates_support,List.append_subset]
      refine ⟨?_,ih is (fun _ h => hw (List.mem_cons_of_mem _ h))⟩
      simpa [pauliZ,circuitWires,gateWires] using hw List.mem_cons_self

theorem deferredCorrectionProgram_support (n : Nat) (targets support : List Wire)
    (cleanup : Circuit) (cells : List (Circuit × Wire))
    (ht : targets ⊆ support) (hc : circuitWires cleanup ⊆ support)
    (hcell : ∀ c ∈ cells, circuitWires c.1 ⊆ support ∧ c.2 ∈ support)
    (start : Nat) (prior : List (Fin start)) :
    straightWires (deferredCorrectionProgram n targets cleanup cells start prior) ⊆ support := by
  induction cells generalizing start with
  | nil =>
    apply registerCorrectionProgram_support _ _ _ _ ht
    simp only [straightWires_append,literalProgram_support,List.append_subset]
    exact ⟨hc,registerCorrectionProgram_support _ _ _ _ ht (List.nil_subset _)⟩
  | cons c cells ih =>
    simp only [deferredCorrectionProgram,straightWires_castFinish,straightWires_append,
      literalProgram_support,straightWires,List.append_subset,List.cons_subset]
    exact ⟨(hcell c (by simp)).1,(hcell c (by simp)).2,
      ih (fun d hd => hcell d (by simp [hd])) _ _⟩

theorem gidneyAddCarryCell_support (q current spare ancilla input dirty : Wire)
    (constant : Bool) (support : List Wire) (hq : q ∈ support) (hc : current ∈ support)
    (hs : spare ∈ support) (ha : ancilla ∈ support) (hi : input ∈ support) (hd : dirty ∈ support) :
    circuitWires (gidneyAddCarryCell q current spare ancilla input dirty constant) ⊆ support := by
  cases constant <;> simp [gidneyAddCarryCell,circuitWires,gateWires,hq,hc,hs,ha,hi,hd]

theorem gidneyCarryCells_support (q current spare ancilla : Wire)
    (input dirty : List Wire) (constant : List Bool) (support : List Wire)
    (hq : q ∈ support) (hc : current ∈ support) (hs : spare ∈ support) (ha : ancilla ∈ support)
    (hi : input ⊆ support) (hd : dirty ⊆ support) :
    ∀ c ∈ gidneyCarryCells q current spare ancilla input dirty constant,
      circuitWires c.1 ⊆ support ∧ c.2 ∈ support := by
  induction input generalizing current spare dirty constant with
  | nil => simp [gidneyCarryCells]
  | cons a input ih =>
    have ha' := hi List.mem_cons_self
    have hi' : input ⊆ support := fun _ h => hi (List.mem_cons_of_mem _ h)
    cases constant with
    | nil => cases input <;> cases dirty <;> simp [gidneyCarryCells]
    | cons k ks =>
      cases dirty with
      | nil =>
        cases input with
        | nil =>
          cases ks with
          | nil => cases k <;> simp [gidneyCarryCells,circuitWires,gateWires,hq,hc,ha']
          | cons _ _ => simp [gidneyCarryCells]
        | cons _ _ => simp [gidneyCarryCells]
      | cons d ds =>
        simp only [gidneyCarryCells,List.forall_mem_cons]
        exact ⟨⟨gidneyAddCarryCell_support _ _ _ _ _ _ _ _ hq hc hs ha ha' (hd List.mem_cons_self),hc⟩,
          ih spare current ds ks hs hc hi' (fun _ h => hd (List.mem_cons_of_mem _ h))⟩

theorem gidneyAddCleanup_support (input dirty : List Wire) (constant : List Bool)
    (q carry : Wire) (support : List Wire) (hq : q ∈ support) (hc : carry ∈ support)
    (hi : input ⊆ support) (hd : dirty ⊆ support) :
    circuitWires (gidneyAddCleanup input dirty constant q carry) ⊆ support := by
  have hf : circuitWires (gidneyFlipWord input) ⊆ support := by
    intro w hw
    obtain ⟨g,hg,hw⟩ := List.mem_flatMap.mp hw
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hg
    have he : w = v := by simpa only [gateWires,List.mem_singleton] using hw
    exact he ▸ hi hv
  have hm := circuitWires_subset_of_usesOnly (controlledConstCarryXor_usesOnly
    (input.take dirty.length) dirty (constant.take dirty.length) q carry)
  have hm' : circuitWires (controlledConstCarryXor (input.take dirty.length) dirty
      (constant.take dirty.length) q carry) ⊆ support := by
    apply hm.trans
    intro w hw
    simp only [List.mem_append,List.mem_cons] at hw
    rcases hw with (rfl | rfl | hw) | hw
    · exact hq
    · exact hc
    · exact hi (List.mem_of_mem_take hw)
    · exact hd hw
  simpa only [gidneyAddCleanup,circuitWires,List.flatMap_append,List.append_subset] using
    And.intro (And.intro hf hm') hf



theorem gidneyNontrivialProgram_support (n start : Nat) (a d q carry spare ancilla : Wire)
    (input dirty : List Wire) (k : Bool) (constant : List Bool) (support : List Wire)
    (ha : a ∈ support) (hd : d ∈ support) (hq : q ∈ support) (hc : carry ∈ support)
    (hs : spare ∈ support) (ht : ancilla ∈ support)
    (hi : input ⊆ support) (hds : dirty ⊆ support) :
    straightWires (gidneyNontrivialProgram n start a d q carry spare ancilla input dirty k constant) ⊆ support := by
  simp only [gidneyNontrivialProgram,straightWires_append,literalProgram_support,List.append_subset]
  refine ⟨gidneyAddCarryCell_support _ _ _ _ _ _ _ _ hq hc hs ht ha hd,?_⟩
  apply deferredCorrectionProgram_support
  · exact List.cons_subset.mpr ⟨hd,hds⟩
  · exact gidneyAddCleanup_support _ _ _ _ _ _ hq hc
      (List.cons_subset.mpr ⟨ha,hi⟩) (List.cons_subset.mpr ⟨hd,hds⟩)
  · exact gidneyCarryCells_support _ _ _ _ _ _ _ _ hq hs hc ht hi hds

theorem gidneyProgram_support (n start : Nat) (input dirty : List Wire) (constant : List Bool)
    (q carry spare ancilla : Wire) (support : List Wire)
    (hlen : input.length = dirty.length+1) (hk : constant.length = input.length)
    (hq : q ∈ support) (hc : carry ∈ support) (hs : spare ∈ support) (ht : ancilla ∈ support)
    (hi : input ⊆ support) (hd : dirty ⊆ support) :
    straightWires (gidneyProgram n start input dirty constant q carry spare ancilla).2 ⊆ support := by
  by_cases hz : constant.all (fun k => !k) = true
  · rw [show gidneyProgram n start input dirty constant q carry spare ancilla = ⟨0,.done⟩ by simp only [gidneyProgram,hz,ite_true]]
    exact List.nil_subset _
  · rw [show gidneyProgram n start input dirty constant q carry spare ancilla = _ by exact if_neg hz]
    cases input with
    | nil => simp at hlen
    | cons a input =>
      cases constant with
      | nil => simp at hk
      | cons k ks =>
        cases dirty with
        | nil =>
          have he : input=[] := List.eq_nil_of_length_eq_zero (by simp_all)
          have he' : ks=[] := List.eq_nil_of_length_eq_zero (by simp_all)
          subst input; subst ks
          have ha := hi List.mem_cons_self
          cases k <;> simp [literalProgram_support,circuitWires,gateWires,hq,ha]
        | cons d ds =>
          have h := gidneyNontrivialProgram_support n start a d q carry spare ancilla input ds k ks support
            (hi List.mem_cons_self) (hd List.mem_cons_self) hq hc hs ht
            (fun _ h => hi (List.mem_cons_of_mem _ h)) (fun _ h => hd (List.mem_cons_of_mem _ h))
          cases input with
          | nil => simp at hlen
          | cons b bs => exact h



theorem compareCarryCell_support (q current spare ancilla input dirty flag : Wire)
    (constant last : Bool) (support : List Wire) (hq : q ∈ support) (hc : current ∈ support)
    (hs : spare ∈ support) (ha : ancilla ∈ support) (hi : input ∈ support)
    (hd : dirty ∈ support) (hf : flag ∈ support) :
    circuitWires (gidneyCompareCarryCell q current spare ancilla input dirty flag constant last) ⊆ support := by
  cases constant <;> cases last <;>
    simp [gidneyCompareCarryCell,circuitWires,gateWires,hq,hc,hs,ha,hi,hd,hf]

theorem compareCarryCells_support (q current spare ancilla flag : Wire)
    (input dirty : List Wire) (constant : List Bool) (support : List Wire)
    (hq : q ∈ support) (hc : current ∈ support) (hs : spare ∈ support)
    (ha : ancilla ∈ support) (hf : flag ∈ support)
    (hi : input ⊆ support) (hd : dirty ⊆ support) :
    ∀ c ∈ compareCarryCells q current spare ancilla flag input dirty constant,
      circuitWires c.1 ⊆ support ∧ c.2 ∈ support := by
  induction input generalizing current spare dirty constant with
  | nil => cases dirty <;> cases constant <;> simp [compareCarryCells,circuitWires,hc]
  | cons a input ih =>
    cases dirty with
    | nil => simp [compareCarryCells]
    | cons d ds =>
      cases constant with
      | nil => simp [compareCarryCells]
      | cons k ks =>
        simp only [compareCarryCells,List.forall_mem_cons]
        exact ⟨⟨compareCarryCell_support _ _ _ _ _ _ _ _ _ _ hq hc hs ha
          (hi List.mem_cons_self) (hd List.mem_cons_self) hf,hc⟩,
          ih spare current ds ks hs hc (fun _ h => hi (List.mem_cons_of_mem _ h))
            (fun _ h => hd (List.mem_cons_of_mem _ h))⟩

theorem carryXor_support (input dirty : List Wire) (constant : List Bool)
    (q carry : Wire) (support : List Wire) (hq : q ∈ support) (hc : carry ∈ support)
    (hi : input ⊆ support) (hd : dirty ⊆ support) :
    circuitWires (controlledConstCarryXor input dirty constant q carry) ⊆ support := by
  apply (circuitWires_subset_of_usesOnly (controlledConstCarryXor_usesOnly _ _ _ _ _)).trans
  intro w hw
  simp only [List.mem_append,List.mem_cons] at hw
  rcases hw with (rfl | rfl | hw) | hw
  · exact hq
  · exact hc
  · exact hi hw
  · exact hd hw

theorem compareCarryProgram_support (n start : Nat) (a d q carry spare ancilla flag : Wire)
    (input dirty : List Wire) (k : Bool) (constant : List Bool) (support : List Wire)
    (ha : a ∈ support) (hd : d ∈ support) (hq : q ∈ support) (hc : carry ∈ support)
    (hs : spare ∈ support) (ht : ancilla ∈ support) (hf : flag ∈ support)
    (hi : input ⊆ support) (hds : dirty ⊆ support) :
    straightWires (compareCarryProgram n start a d q carry spare ancilla flag input dirty k constant) ⊆ support := by
  simp only [compareCarryProgram,straightWires_append,literalProgram_support,List.append_subset]
  refine ⟨compareCarryCell_support _ _ _ _ _ _ _ _ _ _ hq hc hs ht ha hd hf,?_⟩
  apply deferredCorrectionProgram_support
  · exact List.cons_subset.mpr ⟨hd,hds⟩
  · exact carryXor_support _ _ _ _ _ _ hq hc
      (List.cons_subset.mpr ⟨ha,hi⟩) (List.cons_subset.mpr ⟨hd,hds⟩)
  · exact compareCarryCells_support _ _ _ _ _ _ _ _ _ hq hs hc ht hf hi hds

theorem compareGEProgram_support (n start : Nat) (input dirty : List Wire) (threshold : Nat)
    (q carry spare ancilla flag : Wire) (support : List Wire)
    (hq : q ∈ support) (hc : carry ∈ support) (hs : spare ∈ support)
    (ht : ancilla ∈ support) (hf : flag ∈ support)
    (hi : input ⊆ support) (hd : dirty ⊆ support) :
    straightWires (compareGEProgram n start input dirty threshold q carry spare ancilla flag).2 ⊆ support := by
  by_cases hz : threshold = 0
  · rw [show compareGEProgram n start input dirty threshold q carry spare ancilla flag = ⟨0,literalProgram [.CX q flag]⟩ by simp only [compareGEProgram,hz,ite_true]]
    simp [literalProgram_support,circuitWires,gateWires,hq,hf]
  · by_cases hb : 2^input.length ≤ threshold
    · rw [show compareGEProgram n start input dirty threshold q carry spare ancilla flag = ⟨0,.done⟩ by simp only [compareGEProgram,hz,hb,ite_false,ite_true]]
      exact List.nil_subset _
    · rw [show compareGEProgram n start input dirty threshold q carry spare ancilla flag = _ by exact (if_neg hz).trans (if_neg hb)]
      cases input with
      | nil => exact List.nil_subset _
      | cons a input =>
        cases dirty with
        | nil => exact List.nil_subset _
        | cons d ds =>
          generalize (List.map (2 ^ (a :: input).length - threshold).testBit (List.range (a :: input).length)) = bits
          cases bits with
          | nil => exact List.nil_subset _
          | cons k ks =>
            exact compareCarryProgram_support _ _ _ _ _ _ _ _ _ _ _ _ _ _
              (hi List.mem_cons_self) (hd List.mem_cons_self) hq hc hs ht hf
              (fun _ h => hi (List.mem_cons_of_mem _ h)) (fun _ h => hd (List.mem_cons_of_mem _ h))



theorem prependCompiled_support {n start : Nat} (gs : Circuit)
    (p : (count : Nat) × Straight n start (start+count)) :
    straightWires (prependCompiled gs p).2 = circuitWires gs ++ straightWires p.2 := by
  simp only [prependCompiled,straightWires_append,literalProgram_support]

theorem modularNegateProgram_support (n start : Nat) (target dirty : List Wire) (modulus : List Bool)
    (q c r t f : Wire) (support : List Wire)
    (hd : target.length = dirty.length) (hk : modulus.length = target.length) (hpos : 0 < target.length)
    (hq : q ∈ support) (hc : c ∈ support) (hr : r ∈ support) (ht : t ∈ support) (hf : f ∈ support)
    (hx : target ⊆ support) (hy : dirty ⊆ support) :
    straightWires (modularNegateProgram n start target dirty modulus q c r t f).2 ⊆ support := by
  have htake : target.length = (dirty.take (target.length-1)).length+1 := by
    simp only [List.length_take]; omega
  have hyt : dirty.take (target.length-1) ⊆ support := fun _ h => hy (List.mem_of_mem_take h)
  have htest cursor := compareGEProgram_support n cursor target dirty 1 q c r t f support hq hc hr ht hf hx hy
  have hinc cursor := gidneyProgram_support n cursor target (dirty.take (target.length-1))
    ((List.range target.length).map (Nat.testBit 1)) q c r t support htake (by simp) hq hc hr ht hx hyt
  have hadd cursor := gidneyProgram_support n cursor target (dirty.take (target.length-1))
    modulus f c r t support htake hk hf hc hr ht hx hyt
  have hcomp : circuitWires (controlledComplement target q) ⊆ support := by
    intro w hw
    obtain ⟨g,hg,hw⟩ := List.mem_flatMap.mp hw
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hg
    have hv' := hx hv
    rcases (show w = q ∨ w = v by simpa [gateWires] using hw) with rfl | rfl
    · exact hq
    · exact hv'
  simp only [modularNegateProgram,appendCompiled_support,prependCompiled_support,List.append_subset]
  exact ⟨htest _,hcomp,hinc _,hadd _,htest _⟩

theorem negativeNegateProgram_support (n start : Nat) (target dirty : List Wire) (modulus : List Bool)
    (q c r t f : Wire) (support : List Wire)
    (hd : target.length = dirty.length) (hk : modulus.length = target.length) (hpos : 0 < target.length)
    (hq : q ∈ support) (hc : c ∈ support) (hr : r ∈ support) (ht : t ∈ support) (hf : f ∈ support)
    (hx : target ⊆ support) (hy : dirty ⊆ support) :
    straightWires (negativeNegateProgram n start target dirty modulus q c r t f).2 ⊆ support := by
  have hp := modularNegateProgram_support n start target dirty modulus q c r t f support hd hk hpos hq hc hr ht hf hx hy
  have hq' : circuitWires [.X q] ⊆ support := by simpa [circuitWires,gateWires] using hq
  simp only [negativeNegateProgram,prependCompiled_support,appendCompiled_support,literalProgram_support,List.append_subset]
  exact ⟨hq',hp,hq'⟩

/-- Active source bank before relocation; gap 837 is not an allocated wire. -/
def windowBaseSupport : List Wire := List.range 837 ++ [838] ++ List.range' 839 16

theorem yNegateProgram_support_static (start : Nat) :
    straightWires (yNegateProgram start).2 ⊆ windowBaseSupport := by
  apply negativeNegateProgram_support
  all_goals try simp [windowBaseSupport]
  all_goals intro w hw
  all_goals simp only [List.mem_append,List.mem_cons,List.mem_range'_1,List.mem_range] at hw ⊢
  all_goals (try dsimp only [Wire] at *); omega



theorem windowBaseSupport_relocated (z : Wire) (hz : z ∈ windowBaseSupport) :
    windowAddressPerm 855 (by decide) z ∈ resetWires := by
  change windowAddressSwap 855 z ∈ resetWires
  simp only [windowBaseSupport,List.mem_append,List.mem_range,List.mem_singleton,List.mem_range'_1] at hz
  simp only [resetWires,List.mem_append,List.mem_range,List.mem_singleton,List.mem_range'_1]
  unfold windowAddressSwap
  split_ifs <;> dsimp only [Wire] at * <;> omega

theorem sharedYNegateProgram_support_static (w : OddWindow) (start : Nat) :
    (straightWires (sharedYNegateProgram w start).2).map (windowAddressPerm 855 (by decide))
      ⊆ resetWires := by
  simp only [sharedYNegateProgram,reindexCompiled_support]
  intro z hz
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hz
  exact windowBaseSupport_relocated v (yNegateProgram_support_static start hv)

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/ControlSupport ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/ControlSupport.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

def templateControlSafe {n : Nat} (q : Wire) : TemplateGate n → Prop
  | .literal g | .whenBit _ _ g => constantControlSafe q g

def straightControlSafe {n s e : Nat} (q : Wire) : Straight n s e → Prop
  | .done => True
  | .gate g p => templateControlSafe q g ∧ straightControlSafe q p
  | .recordGate _ _ g p => constantControlSafe q g ∧ straightControlSafe q p
  | .measure w p => w ≠ q ∧ straightControlSafe q p

theorem constantStraight_support_erase {n s e : Nat} (q : Wire) (p : Straight n s e)
    (safe : straightControlSafe q p) (support : List Wire) (hp : straightWires p ⊆ q::support) :
    straightWires (constantStraight q p) ⊆ support := by
  have hg (g : Gate) (hs : constantControlSafe q g) (h : gateWires g ⊆ q::support) :
      gateWires (constantControlGate q g) ⊆ support := by
    intro w hw
    have hh := (constantControlGate_wires q g hs w).mp hw
    exact (List.mem_cons.mp (h hh.1)).resolve_left hh.2
  induction p with
  | done => exact List.nil_subset _
  | gate g p ih =>
    obtain ⟨hs,sp⟩ := safe
    have hh := List.append_subset.mp hp
    simp only [constantStraight,straightWires,List.append_subset]
    refine ⟨?_,ih sp hh.2⟩
    cases g <;> exact hg _ hs hh.1
  | recordGate i b g p ih =>
    have hh := List.append_subset.mp hp
    exact List.append_subset.mpr ⟨hg g safe.1 hh.1,ih safe.2 hh.2⟩
  | measure w p ih =>
    have hh := List.cons_subset.mp hp
    exact List.cons_subset.mpr ⟨(List.mem_cons.mp hh.1).resolve_left safe.1,ih safe.2 hh.2⟩

theorem straightControlSafe_append {n s m e : Nat} (q : Wire) (p : Straight n s m) (r : Straight n m e) :
    straightControlSafe q (p.append r) ↔ straightControlSafe q p ∧ straightControlSafe q r := by
  induction p <;> simp_all only [Straight.append,straightControlSafe,true_and,and_assoc]

theorem straightControlSafe_castFinish {n s e f : Nat} (q : Wire) (h : e=f) (p : Straight n s e) :
    straightControlSafe q (castFinish h p) ↔ straightControlSafe q p := by subst f; rfl

theorem literalProgram_controlSafe (n start : Nat) (q : Wire) (gs : Circuit)
    (h : ∀ g ∈ gs, constantControlSafe q g) :
    straightControlSafe q (literalProgram (n:=n) (s:=start) gs) := by
  induction gs with
  | nil => trivial
  | cons g gs ih => exact ⟨h g (by simp),ih (fun x hx => h x (by simp [hx]))⟩

theorem recordGates_controlSafe {n s e : Nat} (q : Wire) (i : Fin s) (gs : Circuit) (p : Straight n s e)
    (hg : ∀ g ∈ gs, constantControlSafe q g) (hp : straightControlSafe q p) :
    straightControlSafe q (recordGates i gs p) := by
  induction gs with
  | nil => exact hp
  | cons g gs ih => exact ⟨hg g (by simp),ih (fun x hx => hg x (by simp [hx]))⟩

theorem registerCorrectionProgram_controlSafe {n s e : Nat} (q : Wire) (ws : List Wire)
    (indices : List (Fin s)) (p : Straight n s e) (hw : q ∉ ws) (hp : straightControlSafe q p) :
    straightControlSafe q (registerCorrectionProgram ws indices p) := by
  induction ws generalizing indices with
  | nil => exact hp
  | cons w ws ih =>
    cases indices with
    | nil => exact hp
    | cons i indices =>
      apply recordGates_controlSafe
      · have hne : w ≠ q := by intro he; subst w; exact hw List.mem_cons_self
        simp [pauliZ,constantControlSafe,hne]
      · exact ih indices (fun h => hw (List.mem_cons_of_mem _ h))

theorem deferredCorrectionProgram_controlSafe (n : Nat) (q : Wire) (targets : List Wire)
    (cleanup : Circuit) (cells : List (Circuit × Wire))
    (ht : q ∉ targets) (hc : ∀ g ∈ cleanup, constantControlSafe q g)
    (hcell : ∀ c ∈ cells, (∀ g ∈ c.1, constantControlSafe q g) ∧ c.2 ≠ q)
    (start : Nat) (prior : List (Fin start)) :
    straightControlSafe q (deferredCorrectionProgram n targets cleanup cells start prior) := by
  induction cells generalizing start with
  | nil =>
    apply registerCorrectionProgram_controlSafe _ _ _ _ ht
    apply (straightControlSafe_append _ _ _).mpr
    exact ⟨literalProgram_controlSafe _ _ _ _ hc,
      registerCorrectionProgram_controlSafe _ _ _ _ ht trivial⟩
  | cons c cells ih =>
    simp only [deferredCorrectionProgram,straightControlSafe_castFinish,straightControlSafe_append,straightControlSafe]
    exact ⟨literalProgram_controlSafe _ _ _ _ (hcell c (by simp)).1,
      (hcell c (by simp)).2,ih (fun d hd => hcell d (by simp [hd])) _ _⟩



theorem compareCarryCell_controlSafe (q c r t a d f : Wire) (k last : Bool)
    (h : q ∉ [c,r,t,a,d,f]) :
    ∀ g ∈ gidneyCompareCarryCell q c r t a d f k last, constantControlSafe q g := by
  cases k <;> cases last <;> simp_all [gidneyCompareCarryCell,constantControlSafe,eq_comm]

theorem compareCarryCells_controlSafe (q current spare ancilla flag : Wire)
    (input dirty : List Wire) (constant : List Bool) (support : List Wire) (hq : q ∉ support)
    (hc : current ∈ support) (hs : spare ∈ support) (ha : ancilla ∈ support) (hf : flag ∈ support)
    (hi : input ⊆ support) (hd : dirty ⊆ support) :
    ∀ c ∈ compareCarryCells q current spare ancilla flag input dirty constant,
      (∀ g ∈ c.1, constantControlSafe q g) ∧ c.2 ≠ q := by
  have hneq (w : Wire) (h : w ∈ support) : w ≠ q := fun he => hq (he ▸ h)
  induction input generalizing current spare dirty constant with
  | nil => cases dirty <;> cases constant <;> simp [compareCarryCells,hneq current hc]
  | cons a input ih =>
    cases dirty with
    | nil => simp [compareCarryCells]
    | cons d ds =>
      cases constant with
      | nil => simp [compareCarryCells]
      | cons k ks =>
        simp only [compareCarryCells,List.forall_mem_cons]
        refine ⟨⟨compareCarryCell_controlSafe _ _ _ _ _ _ _ _ _ ?_,hneq current hc⟩,
          ih spare current ds ks hs hc (fun _ h => hi (List.mem_cons_of_mem _ h))
            (fun _ h => hd (List.mem_cons_of_mem _ h))⟩
        intro h
        have hsupp : [current,spare,ancilla,a,d,flag] ⊆ support := by
          simp only [List.cons_subset,List.nil_subset,and_true]
          exact ⟨hc,hs,ha,hi List.mem_cons_self,hd List.mem_cons_self,hf⟩
        exact hq (hsupp h)

theorem compareCarryProgram_controlSafe (n start : Nat) (a d q c r t f : Wire)
    (input dirty : List Wire) (k : Bool) (constant : List Bool) (support : List Wire)
    (hq : q ∉ support) (ha : a ∈ support) (hd : d ∈ support) (hc : c ∈ support)
    (hr : r ∈ support) (ht : t ∈ support) (hf : f ∈ support)
    (hi : input ⊆ support) (hds : dirty ⊆ support) :
    straightControlSafe q (compareCarryProgram n start a d q c r t f input dirty k constant) := by
  have hneq (w : Wire) (h : w ∈ support) : w ≠ q := fun he => hq (he ▸ h)
  simp only [compareCarryProgram,straightControlSafe_append]
  refine ⟨literalProgram_controlSafe _ _ _ _ (compareCarryCell_controlSafe _ _ _ _ _ _ _ _ _ ?_),?_⟩
  · intro h
    have hsupp : [c,r,t,a,d,f] ⊆ support := by
      simp only [List.cons_subset,List.nil_subset,and_true]
      exact ⟨hc,hr,ht,ha,hd,hf⟩
    exact hq (hsupp h)
  · apply deferredCorrectionProgram_controlSafe
    · intro h
      rcases List.mem_cons.mp h with he | h
      · exact hneq d hd he.symm
      · exact hq (hds h)
    · apply controlledConstCarryXor_controlSafe
      intro h
      simp only [List.mem_append,List.mem_cons] at h
      rcases h with (he | he | h) | he | h
      · exact hneq c hc he.symm
      · exact hneq a ha he.symm
      · exact hq (hi h)
      · exact hneq d hd he.symm
      · exact hq (hds h)
    · exact compareCarryCells_controlSafe q r c t f input dirty constant support hq hr hc ht hf hi hds

theorem compareGEProgram_controlSafe (n start : Nat) (input dirty : List Wire) (threshold : Nat)
    (q c r t f : Wire) (support : List Wire) (hq : q ∉ support)
    (hc : c ∈ support) (hr : r ∈ support) (ht : t ∈ support) (hf : f ∈ support)
    (hi : input ⊆ support) (hd : dirty ⊆ support) :
    straightControlSafe q (compareGEProgram n start input dirty threshold q c r t f).2 := by
  by_cases hz : threshold = 0
  · rw [show compareGEProgram n start input dirty threshold q c r t f = ⟨0,literalProgram [.CX q f]⟩ by simp only [compareGEProgram,hz,ite_true]]
    apply literalProgram_controlSafe
    simp only [List.forall_mem_singleton,constantControlSafe]
    exact fun he => hq (he ▸ hf)
  · by_cases hb : 2^input.length ≤ threshold
    · rw [show compareGEProgram n start input dirty threshold q c r t f = ⟨0,.done⟩ by simp only [compareGEProgram,hz,hb,ite_false,ite_true]]
      trivial
    · rw [show compareGEProgram n start input dirty threshold q c r t f = _ by exact (if_neg hz).trans (if_neg hb)]
      cases input with
      | nil => trivial
      | cons a input =>
        cases dirty with
        | nil => trivial
        | cons d ds =>
          generalize (List.map (2 ^ (a :: input).length - threshold).testBit (List.range (a :: input).length)) = bits
          cases bits with
          | nil => trivial
          | cons k ks =>
            exact compareCarryProgram_controlSafe n start a d q c r t f input ds k ks support hq
              (hi List.mem_cons_self) (hd List.mem_cons_self) hc hr ht hf
              (fun _ h => hi (List.mem_cons_of_mem _ h)) (fun _ h => hd (List.mem_cons_of_mem _ h))

theorem uncontrolledCompareProgram_support (n start : Nat) (input dirty : List Wire) (threshold : Nat)
    (c r t f : Wire) :
    straightWires (uncontrolledCompareProgram n start input dirty threshold c r t f).2 ⊆
      [c,r,t,f] ++ input ++ dirty := by
  let support := [c,r,t,f] ++ input ++ dirty
  let q := gidneyCompareVirtualControl input dirty c r t f
  have hq : q ∉ support := by
    intro h
    have hh := List.le_sum_of_mem h
    change support.sum+1 ≤ support.sum at hh
    exact (Nat.not_succ_le_self _) hh
  have hc : c ∈ support := by simp [support]
  have hr : r ∈ support := by simp [support]
  have ht : t ∈ support := by simp [support]
  have hf : f ∈ support := by simp [support]
  have hi : input ⊆ support := fun _ h => by simp [support,h]
  have hd : dirty ⊆ support := fun _ h => by simp [support,h]
  apply constantStraight_support_erase
  · exact compareGEProgram_controlSafe n start input dirty threshold q c r t f support hq hc hr ht hf hi hd
  · exact compareGEProgram_support n start input dirty threshold q c r t f (q::support)
      List.mem_cons_self (List.mem_cons_of_mem _ hc) (List.mem_cons_of_mem _ hr)
      (List.mem_cons_of_mem _ ht) (List.mem_cons_of_mem _ hf)
      (fun _ h => List.mem_cons_of_mem _ (hi h)) (fun _ h => List.mem_cons_of_mem _ (hd h))



theorem modularAddProgram_support (n start : Nat) (input acc : List Wire) (correction : List Bool)
    (modulus : Nat) (q c r t f : Wire) (support : List Wire)
    (hl : input.length = acc.length) (hk : correction.length = acc.length) (hpos : 0 < acc.length)
    (hq : q ∈ support) (hc : c ∈ support) (hr : r ∈ support) (ht : t ∈ support) (hf : f ∈ support)
    (hi : input ⊆ support) (ha : acc ⊆ support) :
    straightWires (modularAddProgram n start input acc correction modulus q c r t f).2 ⊆ support := by
  have hsmall : q::c::f::input++acc ⊆ support := by
    simp only [List.append_subset,List.cons_subset]
    exact ⟨⟨hq,hc,hf,hi⟩,ha⟩
  have hfirst := (circuitWires_subset_of_usesOnly (controlledAddCarry_usesOnly input acc q c f)).trans hsmall
  have hcompare cursor := (uncontrolledCompareProgram_support n cursor acc input modulus c r t f).trans
    (show [c,r,t,f]++acc++input ⊆ support by
      simp only [List.append_subset,List.cons_subset,List.nil_subset,and_true]
      exact ⟨⟨⟨hc,hr,ht,hf⟩,ha⟩,hi⟩)
  have htake : acc.length = (input.take (acc.length-1)).length+1 := by
    simp only [List.length_take]; omega
  have hadd cursor := gidneyProgram_support n cursor acc (input.take (acc.length-1)) correction f c r t
    support htake hk hf hc hr ht ha (fun _ h => hi (List.mem_of_mem_take h))
  have hlast : circuitWires (controlledCompareLT acc input q c f) ⊆ support := by
    cases acc with
    | nil => simp at hpos
    | cons a acc =>
      intro w hw
      have h := (controlledCompareLT_wires a acc input q c f w hl.symm).mp hw
      have hsub : q::c::f::(a::acc)++input ⊆ support := by
        simp only [List.append_subset,List.cons_subset]
        exact ⟨⟨hq,hc,hf,(List.cons_subset.mp ha).1,(List.cons_subset.mp ha).2⟩,hi⟩
      exact hsub h
  simp only [modularAddProgram,straightWires_append,literalProgram_support,appendCompiled_support,List.append_subset]
  exact ⟨hfirst,hcompare _,hadd _,hlast⟩



theorem fieldLoadProgram_support_static (field : PointField) (start : Nat) :
    straightWires (fieldLoadProgram field start) ⊆ windowBaseSupport := by
  have hl : ∀ op ∈ fieldLoadOps field, lookupOpWires op ⊆ windowBaseSupport := by
    apply unaryLookupOps_support
    · simp [windowBaseSupport]
    · intro z hz
      simp only [pointLookupPath,List.mem_range'_1] at hz
      simp only [windowBaseSupport,List.mem_append,List.mem_range,List.mem_singleton,List.mem_range'_1]
      (try dsimp only [Wire] at *); omega
    · intro z hz
      have h := (tableAddressTree_mem_index pointLookupAddress 0 1 z).mp hz
      simp only [pointLookupAddress,List.mem_range'_1] at h
      simp only [windowBaseSupport,List.mem_append,List.mem_range,List.mem_singleton,List.mem_range'_1]
      (try dsimp only [Wire] at *); omega
    · intro label q hq
      apply lookupLeafGates_support _ _ _ hq
      intro p hp
      have h := (List.of_mem_zip hp).2
      simp only [List.mem_range'_1] at h
      simp only [windowBaseSupport,List.mem_append,List.mem_range,List.mem_singleton,List.mem_range'_1]
      (try dsimp only [Wire] at *); omega
  simp only [fieldLoadProgram,straightWires_castFinish,lookupProgram_support]
  intro z hz
  obtain ⟨op,hop,hz⟩ := List.mem_flatMap.mp hz
  exact hl op hop hz

theorem fieldLookupAddProgram_support_static (field : PointField) (acc : List Wire)
    (ha : acc ⊆ windowBaseSupport) (hlen : acc.length = 256) (start : Nat) :
    straightWires (fieldLookupAddProgram field acc start).2 ⊆ windowBaseSupport := by
  have had cursor : straightWires (modularAddProgram 32768 cursor (List.range' 7 256) acc
      secp256k1ReductionConstantBits ShorECDLP.p 836 559 560 561 558).2 ⊆ windowBaseSupport := by
    apply modularAddProgram_support
    all_goals try exact ha
    all_goals try simp [hlen,secp256k1ReductionConstantBits,windowBaseSupport]
    · intro w hw
      simp only [List.mem_range'_1] at hw
      simp only [List.mem_append,List.mem_range,List.mem_cons,List.mem_range'_1]
      (try dsimp only [Wire] at *); omega
  simp only [fieldLookupAddProgram,appendCompiled_support,List.append_subset]
  exact ⟨fieldLoadProgram_support_static _ _,had _,fieldLoadProgram_support_static _ _⟩

theorem signedFieldProgram_support_static (field : PointField) (start : Nat) :
    straightWires (signedFieldProgram field start).2 ⊆ windowBaseSupport := by
  have hy : List.range' 580 256 ⊆ windowBaseSupport := by
    intro w hw
    simp only [List.mem_range'_1] at hw
    simp only [windowBaseSupport,List.mem_append,List.mem_range,List.mem_singleton,List.mem_range'_1]
    omega
  simp only [signedFieldProgram,appendCompiled_support,List.append_subset]
  exact ⟨yNegateProgram_support_static _,fieldLookupAddProgram_support_static _ _ hy (by simp) _,yNegateProgram_support_static _⟩

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/WindowSupport ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/WindowSupport.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

/-- Mapping a shared allocation through a fixed wire permutation commutes with
sequential compilation, without expanding any window body. -/
theorem sequenceProgram_mapped_support (n : Nat) (ps : List (FixedSegment n))
    (e : Wire → Wire) (support : List Wire)
    (h : ∀ p ∈ ps, ∀ start, (straightWires (p start).2).map e ⊆ support) (start : Nat) :
    (straightWires (sequenceProgram n ps start).2).map e ⊆ support := by
  induction ps generalizing start with
  | nil => exact List.nil_subset _
  | cons p ps ih =>
    simp only [sequenceProgram,appendCompiled_support,List.map_append,List.append_subset]
    exact ⟨h p (by simp) start,ih (fun q hq => h q (by simp [hq])) _⟩

theorem signedAddressCircuit_support_static :
    (circuitWires (signedAddressCircuit 836 854 pointLookupAddress)).map
      (windowAddressPerm 855 (by decide)) ⊆ resetWires := by
  have hx (q : Wire) (hq : q ∈ windowBaseSupport) :
      circuitWires (tableXorGates q pointLookupAddress) ⊆ windowBaseSupport := by
    intro z hz
    obtain ⟨g,hg,hz⟩ := List.mem_flatMap.mp hz
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hg
    have hw' : w ∈ windowBaseSupport := by simp [windowBaseSupport,pointLookupAddress] at hw ⊢; omega
    rcases (show z = q ∨ z = w by simpa [gateWires] using hz) with rfl | rfl
    · exact hq
    · exact hw'
  have hp : circuitWires (signedAddressCircuit 836 854 pointLookupAddress) ⊆ windowBaseSupport := by
    simpa only [signedAddressCircuit,circuitWires,List.flatMap_append,List.append_subset] using
      And.intro (hx 836 (by simp [windowBaseSupport])) (hx 854 (by simp [windowBaseSupport]))
  intro z hz
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hz
  exact windowBaseSupport_relocated v (hp hv)

/-- The remaining arithmetic obligation is explicit. The correction and both
negation segments have unconditional concrete support proofs. -/
theorem actualIpxWindow_support_of_coordinate (w : OddWindow)
    (hc : ∀ start, (straightWires (sharedCoordinateProgram w start).2).map
      (windowAddressPerm 855 (by decide)) ⊆ resetWires) (start : Nat) :
    straightWires ((actualIpxWindow w).program start) ⊆ resetWires := by
  have hcore cursor : (straightWires (ipxWindowCore w cursor).2).map
      (windowAddressPerm 855 (by decide)) ⊆ resetWires := by
    apply sequenceProgram_mapped_support
    simp only [ipxWindowSegments,List.forall_mem_cons,List.mem_nil_iff,false_implies,implies_true,and_true]
    exact ⟨hc,sharedYNegateProgram_support_static w,ipxProgram_support_static w,
      sharedYNegateProgram_support_static w⟩
  simp only [actualIpxWindow,closedWindow,straightWires_shift,straightWires_relabel,
    ipxWindowPrepared,surroundCompiled_support,List.map_append,List.append_subset]
  exact ⟨⟨signedAddressCircuit_support_static,hcore 0⟩,signedAddressCircuit_support_static⟩



theorem actualWindows_support_of_coordinate
    (hc : ∀ w start, (straightWires (sharedCoordinateProgram w start).2).map
      (windowAddressPerm 855 (by decide)) ⊆ resetWires)
    (window : OuterWindow 983040) (hw : window ∈ ipxLeftWindows ++ ipxRightWindows)
    (start : Nat) : straightWires (window.program start) ⊆ resetWires := by
  simp only [ipxLeftWindows,ipxRightWindows,List.mem_append,List.mem_cons,List.mem_ofFn] at hw
  rcases hw with (rfl | ⟨k,rfl⟩) | ⟨k,rfl⟩
  · exact actualFirstWindow_support_static start
  · exact actualIpxWindow_support_of_coordinate _ (hc _) start
  · exact actualIpxWindow_support_of_coordinate _ (hc _) start

theorem ipxOuter_support_of_coordinate
    (hc : ∀ w start, (straightWires (sharedCoordinateProgram w start).2).map
      (windowAddressPerm 855 (by decide)) ⊆ resetWires)
    (count start : Nat) (read : ConstantBit 983040 → Bool) (history : Fin start → Bool) :
    ((ipxOuterPlan.repeat count start).instantiate read history).wires ⊆ resetWires := by
  apply OuterPlan.repeat_support
  · intro w hw
    simp only [ipxOuterPlan,standardOuterPlan,Vector.toList_mk,List.mem_reverse] at hw
    exact List.mem_append_right _ hw
  · exact List.Subset.refl _
  · simp [resetWires]
  · intro window hw cursor h
    apply (straight_instantiate_support _ read h).trans
    apply actualWindows_support_of_coordinate hc window _ cursor
    simpa only [ipxOuterPlan,standardOuterPlan,Vector.toList_mk,List.toList_toArray] using hw

/-- Conditional assembly only: the concrete coordinate compiler support must
still be supplied. This is not an unconditional Streaming resource certificate. -/
theorem ipxOuter_qubits_le_of_coordinate
    (hc : ∀ w start, (straightWires (sharedCoordinateProgram w start).2).map
      (windowAddressPerm 855 (by decide)) ⊆ resetWires)
    (count start : Nat) (read : ConstantBit 983040 → Bool) (history : Fin start → Bool) :
    ((ipxOuterPlan.repeat count start).instantiate read history).wires.toFinset.card ≤ 854 := by
  have hs := ipxOuter_support_of_coordinate hc count start read history
  have hfin : ((ipxOuterPlan.repeat count start).instantiate read history).wires.toFinset ⊆
      resetWires.toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (hs (List.mem_toFinset.mp hw))
  exact (Finset.card_le_card hfin).trans ((List.toFinset_card_le _).trans_eq resetWires_length)

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/EEACoreSupport ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/EEACoreSupport.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

theorem andEraseProgram_support (n start : Nat) (a b t : Wire) (support : List Wire)
    (ha : a ∈ support) (hb : b ∈ support) (ht : t ∈ support) :
    straightWires (andEraseProgram n start a b t) ⊆ support := by
  simp only [andEraseProgram,straightWires,recordGates_support,List.append_nil,List.cons_subset]
  refine ⟨ht,?_⟩
  by_cases h : a = b
  · simp [controlledZ,h,circuitWires,gateWires,hb]
  · simp [controlledZ,circuitWires,gateWires,ha,hb]

theorem vchainTailProgram_support (n : Nat) (controls : List Wire) (acc target : Wire)
    (scratch : List Wire) (start : Nat) (support : List Wire)
    (hc : controls ⊆ support) (ha : acc ∈ support) (ht : target ∈ support)
    (hs : scratch ⊆ support) :
    straightWires (vchainTailProgram n controls acc target scratch start).2 ⊆ support := by
  induction controls generalizing acc scratch start with
  | nil => exact List.nil_subset _
  | cons control controls ih =>
    have hcontrol := hc List.mem_cons_self
    cases controls with
    | nil => simp [vchainTailProgram,literalProgram_support,circuitWires,gateWires,hcontrol,ha,ht]
    | cons next controls =>
      cases scratch with
      | nil => exact List.nil_subset _
      | cons work scratch =>
        have hw := hs List.mem_cons_self
        have hi := ih work scratch start (fun _ h => hc (List.mem_cons_of_mem _ h)) hw (fun _ h => hs (List.mem_cons_of_mem _ h))
        have he cursor := andEraseProgram_support n cursor control acc work support hcontrol ha hw
        simp only [vchainTailProgram,prependCompiled_support,appendCompiled_support,List.append_subset]
        refine ⟨?_,hi,he _⟩
        simp [circuitWires,gateWires,hcontrol,ha,hw]

theorem vchainProgram_support (n start : Nat) (controls : List Wire) (target : Wire)
    (scratch : List Wire) (support : List Wire)
    (hc : controls ⊆ support) (ht : target ∈ support) (hs : scratch ⊆ support) :
    straightWires (vchainProgram n start controls target scratch).2 ⊆ support := by
  cases controls with
  | nil => simp [vchainProgram,literalProgram_support,circuitWires,gateWires,ht]
  | cons first rest =>
    have hf := hc List.mem_cons_self
    cases rest with
    | nil => simp [vchainProgram,literalProgram_support,circuitWires,gateWires,hf,ht]
    | cons second rest =>
      apply vchainTailProgram_support n (first::rest) second target scratch start support
      · intro w hw
        exact hc (by simp only [List.mem_cons] at hw ⊢; tauto)
      · exact hc (by simp)
      · exact ht
      · exact hs

theorem rippleMajProgram_support (n start : Nat) (control target addend carry scratch : Wire)
    (support : List Wire) (hc : control ∈ support) (ht : target ∈ support)
    (ha : addend ∈ support) (hcarry : carry ∈ support) (hs : scratch ∈ support) :
    straightWires (rippleMajProgram n start control target addend carry scratch).2 ⊆ support := by
  have hb := vchainProgram_support n start ([control,target,addend] : List Wire) carry ([scratch] : List Wire) support
    (by simp [hc,ht,ha]) hcarry (by simp [hs])
  simp only [rippleMajProgram,prependCompiled_support,List.append_subset]
  refine ⟨?_,hb⟩
  simp [circuitWires,gateWires,ht,ha,hcarry]

theorem rippleUmaProgram_support (n start : Nat) (control target addend carry scratch : Wire)
    (support : List Wire) (hc : control ∈ support) (ht : target ∈ support)
    (ha : addend ∈ support) (hcarry : carry ∈ support) (hs : scratch ∈ support) :
    straightWires (rippleUmaProgram n start control target addend carry scratch).2 ⊆ support := by
  have hb := vchainProgram_support n start ([control,target,addend] : List Wire) carry ([scratch] : List Wire) support
    (by simp [hc,ht,ha]) hcarry (by simp [hs])
  simp only [rippleUmaProgram,appendCompiled_support,literalProgram_support,List.append_subset]
  refine ⟨hb,?_⟩
  simp [circuitWires,gateWires,hc,ht,ha,hcarry]

theorem rippleMajInvProgram_support (n start : Nat) (control target addend carry scratch : Wire)
    (support : List Wire) (hc : control ∈ support) (ht : target ∈ support)
    (ha : addend ∈ support) (hcarry : carry ∈ support) (hs : scratch ∈ support) :
    straightWires (rippleMajInvProgram n start control target addend carry scratch).2 ⊆ support := by
  have hb := vchainProgram_support n start ([control,target,addend] : List Wire) carry ([scratch] : List Wire) support
    (by simp [hc,ht,ha]) hcarry (by simp [hs])
  simp only [rippleMajInvProgram,appendCompiled_support,literalProgram_support,List.append_subset]
  refine ⟨hb,?_⟩
  simp [circuitWires,gateWires,ht,ha,hcarry]

theorem rippleUmaInvProgram_support (n start : Nat) (control target addend carry scratch : Wire)
    (support : List Wire) (hc : control ∈ support) (ht : target ∈ support)
    (ha : addend ∈ support) (hcarry : carry ∈ support) (hs : scratch ∈ support) :
    straightWires (rippleUmaInvProgram n start control target addend carry scratch).2 ⊆ support := by
  have hb := vchainProgram_support n start ([control,target,addend] : List Wire) carry ([scratch] : List Wire) support
    (by simp [hc,ht,ha]) hcarry (by simp [hs])
  simp only [rippleUmaInvProgram,prependCompiled_support,List.append_subset]
  refine ⟨?_,hb⟩
  simp [circuitWires,gateWires,hc,ht,ha,hcarry]

theorem rippleFirstProgram_support (n start : Nat) (mode : RippleMode) (control target addend carry scratch : Wire)
    (support : List Wire) (hc : control ∈ support) (ht : target ∈ support)
    (ha : addend ∈ support) (hcarry : carry ∈ support) (hs : scratch ∈ support) :
    straightWires (rippleFirstProgram n start mode control target addend carry scratch).2 ⊆ support := by
  cases mode
  · exact rippleMajProgram_support n start control target addend carry scratch support hc ht ha hcarry hs
  · exact rippleUmaInvProgram_support n start control target addend carry scratch support hc ht ha hcarry hs

theorem rippleSecondProgram_support (n start : Nat) (mode : RippleMode) (control target addend carry scratch : Wire)
    (support : List Wire) (hc : control ∈ support) (ht : target ∈ support)
    (ha : addend ∈ support) (hcarry : carry ∈ support) (hs : scratch ∈ support) :
    straightWires (rippleSecondProgram n start mode control target addend carry scratch).2 ⊆ support := by
  cases mode
  · exact rippleUmaProgram_support n start control target addend carry scratch support hc ht ha hcarry hs
  · exact rippleMajInvProgram_support n start control target addend carry scratch support hc ht ha hcarry hs


theorem equalityProgram_support (n start : Nat) (register : List Wire) (value : Nat)
    (flag : Wire) (scratch support : List Wire)
    (hr : register ⊆ support) (hf : flag ∈ support) (hs : scratch ⊆ support) :
    straightWires (equalityProgram n start register value flag scratch).2 ⊆ support := by
  have hx := (circuitWires_subset_of_usesOnly (zeroMask_usesOnly register value)).trans hr
  have hb := vchainProgram_support n start register flag scratch support hr hf hs
  simp only [equalityProgram,prependCompiled_support,appendCompiled_support,literalProgram_support,List.append_subset]
  exact ⟨hx,hb,hx⟩

theorem toggleEqualityProgram_support (n start : Nat) (root : Wire) (register : List Wire)
    (value : Nat) (acc flag : Wire) (scratch support : List Wire)
    (hroot : root ∈ support) (hr : register ⊆ support) (ha : acc ∈ support)
    (hf : flag ∈ support) (hs : scratch ⊆ support) :
    straightWires (toggleEqualityProgram n start root register value acc flag scratch).2 ⊆ support := by
  have hb cursor := equalityProgram_support n cursor register value flag scratch support hr hf hs
  simp only [toggleEqualityProgram,appendCompiled_support,prependCompiled_support,List.append_subset]
  refine ⟨hb _,?_,hb _⟩
  simp [circuitWires,gateWires,hroot,ha,hf]

theorem intervalFirstProgram_support (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc target addend carry scratch : Wire) (label : Nat)
    (rightControl leftControl : Wire) (support : List Wire)
    (hrt : rightTop ∈ support) (hlt : leftTop ∈ support) (ha : acc ∈ support)
    (ht : target ∈ support) (had : addend ∈ support) (hc : carry ∈ support)
    (hs : scratch ∈ support) (hrc : rightControl ∈ support) (hlc : leftControl ∈ support) :
    straightWires (intervalFirstProgram n start mode topSpecial rightTop leftTop acc target addend carry scratch label rightControl leftControl).2 ⊆ support := by
  have hr := (circuitWires_subset_of_usesOnly (endpointLeafToggle_usesOnly topSpecial label rightTop rightControl acc)).trans
    (show [rightControl,rightTop,acc] ⊆ support by simp [hrc,hrt,ha])
  have hl := (circuitWires_subset_of_usesOnly (endpointLeafToggle_usesOnly topSpecial label leftTop leftControl acc)).trans
    (show [leftControl,leftTop,acc] ⊆ support by simp [hlc,hlt,ha])
  have hb := rippleFirstProgram_support n start mode acc target addend carry scratch support ha ht had hc hs
  simp only [intervalFirstProgram,prependCompiled_support,appendCompiled_support,literalProgram_support,List.append_subset]
  exact ⟨hr,hb,hl⟩

theorem intervalSecondProgram_support (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc target addend carry scratch : Wire) (label : Nat)
    (rightControl leftControl : Wire) (support : List Wire)
    (hrt : rightTop ∈ support) (hlt : leftTop ∈ support) (ha : acc ∈ support)
    (ht : target ∈ support) (had : addend ∈ support) (hc : carry ∈ support)
    (hs : scratch ∈ support) (hrc : rightControl ∈ support) (hlc : leftControl ∈ support) :
    straightWires (intervalSecondProgram n start mode topSpecial rightTop leftTop acc target addend carry scratch label rightControl leftControl).2 ⊆ support := by
  have hr := (circuitWires_subset_of_usesOnly (endpointLeafToggle_usesOnly topSpecial label rightTop rightControl acc)).trans
    (show [rightControl,rightTop,acc] ⊆ support by simp [hrc,hrt,ha])
  have hl := (circuitWires_subset_of_usesOnly (endpointLeafToggle_usesOnly topSpecial label leftTop leftControl acc)).trans
    (show [leftControl,leftTop,acc] ⊆ support by simp [hlc,hlt,ha])
  have hb := rippleSecondProgram_support n start mode acc target addend carry scratch support ha ht had hc hs
  simp only [intervalSecondProgram,prependCompiled_support,appendCompiled_support,literalProgram_support,List.append_subset]
  exact ⟨hl,hb,hr⟩


theorem zeroEraseProgram_support (n start : Nat) (a b w : Wire) (support : List Wire)
    (ha : a ∈ support) (hb : b ∈ support) (hw : w ∈ support) :
    straightWires (zeroEraseProgram n start a b w).2 ⊆ support := by
  have he := andEraseProgram_support n start a b w support ha hb hw
  have hx : circuitWires [.X b] ⊆ support := by simp [circuitWires,gateWires,hb]
  simp only [zeroEraseProgram,prependCompiled_support,appendCompiled_support,literalProgram_support,List.append_subset]
  exact ⟨hx,he,hx⟩

theorem dualEraseProgram_support (n start : Nat) (a i x b j y : Wire) (support : List Wire)
    (ha : a ∈ support) (hi : i ∈ support) (hx : x ∈ support)
    (hb : b ∈ support) (hj : j ∈ support) (hy : y ∈ support) :
    straightWires (dualEraseProgram n start a i x b j y).2 ⊆ support := by
  simp only [dualEraseProgram,appendCompiled_support,List.append_subset]
  exact ⟨zeroEraseProgram_support n _ b j y support hb hj hy,
    zeroEraseProgram_support n _ a i x support ha hi hx⟩

private theorem compiledSupportIf {n start : Nat} (b : Prop) [Decidable b]
    (p q : (count : Nat) × Straight n start (start+count)) :
    straightWires (if b then p else q).2 = if b then straightWires p.2 else straightWires q.2 := by
  by_cases hb : b
  · rw [if_pos hb,if_pos hb]
  · rw [if_neg hb,if_neg hb]

theorem dualProgram_support (n : Nat) (order : UnaryOrder)
    (leaf : (label : Nat) → (a b : Wire) → (start : Nat) →
      (count : Nat) × Straight n start (start+count))
    (tree : DualUnaryActionTree) (a b : Wire) (xs ys : List Wire) (start : Nat) (support : List Wire)
    (hleaf : ∀ label ∈ tree.labels, ∀ a b start, a ∈ support → b ∈ support →
      straightWires (leaf label a b start).2 ⊆ support)
    (hi : tree.indexAWires ⊆ support) (hj : tree.indexBWires ⊆ support)
    (ha : a ∈ support) (hb : b ∈ support) (hx : xs ⊆ support) (hy : ys ⊆ support) :
    straightWires (dualProgram n order leaf tree a b xs ys start).2 ⊆ support := by
  induction tree generalizing a b xs ys start with
  | leaf label =>
    rw [dualProgram]
    exact hleaf label (by simp [DualUnaryActionTree.labels]) a b start ha hb
  | node i j zero one ihz iho =>
    cases xs with
    | nil => rw [dualProgram] <;> simp [straightWires]
    | cons x xs =>
      cases ys with
      | nil => rw [dualProgram] <;> simp [straightWires]
      | cons y ys =>
        have hix : i ∈ support := hi List.mem_cons_self
        have hjy : j ∈ support := hj List.mem_cons_self
        have hxx : x ∈ support := hx List.mem_cons_self
        have hyy : y ∈ support := hy List.mem_cons_self
        have hz cursor := ihz x y xs ys cursor
          (fun l hl => hleaf l (List.mem_append_left _ hl))
          (fun _ h => hi (List.mem_cons_of_mem _ (List.mem_append_left _ h)))
          (fun _ h => hj (List.mem_cons_of_mem _ (List.mem_append_left _ h)))
          hxx hyy (fun _ h => hx (List.mem_cons_of_mem _ h)) (fun _ h => hy (List.mem_cons_of_mem _ h))
        have ho cursor := iho x y xs ys cursor
          (fun l hl => hleaf l (List.mem_append_right _ hl))
          (fun _ h => hi (List.mem_cons_of_mem _ (List.mem_append_right _ h)))
          (fun _ h => hj (List.mem_cons_of_mem _ (List.mem_append_right _ h)))
          hxx hyy (fun _ h => hx (List.mem_cons_of_mem _ h)) (fun _ h => hy (List.mem_cons_of_mem _ h))
        have he cursor := dualEraseProgram_support n cursor a i x b j y support ha hix hxx hb hjy hyy
        have hca : circuitWires (computeZeroAnd a i x) ⊆ support := by simp [computeZeroAnd,circuitWires,gateWires,ha,hix,hxx]
        have hcb : circuitWires (computeZeroAnd b j y) ⊆ support := by simp [computeZeroAnd,circuitWires,gateWires,hb,hjy,hyy]
        have hab : circuitWires [.CX a x,.CX b y] ⊆ support := by simp [circuitWires,gateWires,ha,hb,hxx,hyy]
        have hba : circuitWires [.CX b y,.CX a x] ⊆ support := by simp [circuitWires,gateWires,ha,hb,hxx,hyy]
        rw [dualProgram]
        rw [compiledSupportIf]
        cases order <;> simp only [ite_true,ite_false,reduceCtorEq,prependCompiled_support,appendCompiled_support,List.append_subset]
        · exact ⟨hca,hcb,hz _,hab,ho _,hba,he _⟩
        · exact ⟨hca,hcb,hab,ho _,hba,hz _,he _⟩


theorem topFirstProgram_support (n start : Nat) (mode : RippleMode) (value : Nat)
    (rightRegister leftRegister : List Wire) (acc target addend carry work flag : Wire)
    (scratch : List Wire) (rightRoot leftRoot : Wire) (support : List Wire)
    (hr : rightRegister ⊆ support) (hl : leftRegister ⊆ support)
    (ha : acc ∈ support) (ht : target ∈ support) (had : addend ∈ support)
    (hc : carry ∈ support) (hw : work ∈ support) (hf : flag ∈ support)
    (hs : scratch ⊆ support) (hrr : rightRoot ∈ support) (hlr : leftRoot ∈ support) :
    straightWires (topFirstProgram n start mode value rightRegister leftRegister acc target addend carry work flag scratch rightRoot leftRoot).2 ⊆ support := by
  have hright cursor := toggleEqualityProgram_support n cursor rightRoot rightRegister value acc flag scratch support hrr hr ha hf hs
  have hleft cursor := toggleEqualityProgram_support n cursor leftRoot leftRegister value acc flag scratch support hlr hl ha hf hs
  have hb cursor := rippleFirstProgram_support n cursor mode acc target addend carry work support ha ht had hc hw
  simp only [topFirstProgram,appendCompiled_support,List.append_subset]
  exact ⟨hright _,hb _,hleft _⟩

theorem topSecondProgram_support (n start : Nat) (mode : RippleMode) (value : Nat)
    (rightRegister leftRegister : List Wire) (acc target addend carry work flag : Wire)
    (scratch : List Wire) (rightRoot leftRoot : Wire) (support : List Wire)
    (hr : rightRegister ⊆ support) (hl : leftRegister ⊆ support)
    (ha : acc ∈ support) (ht : target ∈ support) (had : addend ∈ support)
    (hc : carry ∈ support) (hw : work ∈ support) (hf : flag ∈ support)
    (hs : scratch ⊆ support) (hrr : rightRoot ∈ support) (hlr : leftRoot ∈ support) :
    straightWires (topSecondProgram n start mode value rightRegister leftRegister acc target addend carry work flag scratch rightRoot leftRoot).2 ⊆ support := by
  have hright cursor := toggleEqualityProgram_support n cursor rightRoot rightRegister value acc flag scratch support hrr hr ha hf hs
  have hleft cursor := toggleEqualityProgram_support n cursor leftRoot leftRegister value acc flag scratch support hlr hl ha hf hs
  have hb cursor := rippleSecondProgram_support n cursor mode acc target addend carry work support ha ht had hc hw
  simp only [topSecondProgram,appendCompiled_support,List.append_subset]
  exact ⟨hleft _,hb _,hright _⟩

theorem traversalFirstProgram_support (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc carry scratch : Wire) (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire) (rightPaths leftPaths support : List Wire)
    (hrt : rightTop ∈ support) (hlt : leftTop ∈ support) (ha : acc ∈ support)
    (hc : carry ∈ support) (hs : scratch ∈ support)
    (htarget : ∀ l ∈ tree.labels, targetAt l ∈ support)
    (haddend : ∀ l ∈ tree.labels, addendAt l ∈ support)
    (hi : tree.indexAWires ⊆ support) (hj : tree.indexBWires ⊆ support)
    (hrr : rightRoot ∈ support) (hlr : leftRoot ∈ support)
    (hrp : rightPaths ⊆ support) (hlp : leftPaths ⊆ support) :
    straightWires (traversalFirstProgram n start mode topSpecial rightTop leftTop acc carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).2 ⊆ support := by
  unfold traversalFirstProgram
  apply dualProgram_support n .dec _ tree rightRoot leftRoot rightPaths leftPaths start support
  · intro l hl a b cursor hsa hsb
    exact intervalFirstProgram_support n cursor mode topSpecial rightTop leftTop acc (targetAt l) (addendAt l) carry scratch l a b support hrt hlt ha (htarget l hl) (haddend l hl) hc hs hsa hsb
  · exact hi
  · exact hj
  · exact hrr
  · exact hlr
  · exact hrp
  · exact hlp

theorem traversalSecondProgram_support (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc carry scratch : Wire) (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire) (rightPaths leftPaths support : List Wire)
    (hrt : rightTop ∈ support) (hlt : leftTop ∈ support) (ha : acc ∈ support)
    (hc : carry ∈ support) (hs : scratch ∈ support)
    (htarget : ∀ l ∈ tree.labels, targetAt l ∈ support)
    (haddend : ∀ l ∈ tree.labels, addendAt l ∈ support)
    (hi : tree.indexAWires ⊆ support) (hj : tree.indexBWires ⊆ support)
    (hrr : rightRoot ∈ support) (hlr : leftRoot ∈ support)
    (hrp : rightPaths ⊆ support) (hlp : leftPaths ⊆ support) :
    straightWires (traversalSecondProgram n start mode topSpecial rightTop leftTop acc carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).2 ⊆ support := by
  unfold traversalSecondProgram
  apply dualProgram_support n .inc _ tree rightRoot leftRoot rightPaths leftPaths start support
  · intro l hl a b cursor hsa hsb
    exact intervalSecondProgram_support n cursor mode topSpecial rightTop leftTop acc (targetAt l) (addendAt l) carry scratch l a b support hrt hlt ha (htarget l hl) (haddend l hl) hc hs hsa hsb
  · exact hi
  · exact hj
  · exact hrr
  · exact hlr
  · exact hrp
  · exact hlp


theorem unaryProgram_support (n : Nat) (order : UnaryOrder)
    (leaf : (label : Nat) → (control : Wire) → (start : Nat) →
      (count : Nat) × Straight n start (start+count))
    (tree : UnaryActionTree) (control : Wire) (paths : List Wire) (start : Nat) (support : List Wire)
    (hleaf : ∀ label ∈ tree.labels, ∀ control start, control ∈ support →
      straightWires (leaf label control start).2 ⊆ support)
    (hi : tree.indexWires ⊆ support) (hc : control ∈ support) (hp : paths ⊆ support) :
    straightWires (unaryProgram n order leaf tree control paths start).2 ⊆ support := by
  induction tree generalizing control paths start with
  | leaf label =>
    rw [unaryProgram]
    exact hleaf label (by simp [UnaryActionTree.labels]) control start hc
  | node bit zero one ihz iho =>
    cases paths with
    | nil => rw [unaryProgram]; exact List.nil_subset _
    | cons path rest =>
      have hib : bit ∈ support := hi List.mem_cons_self
      have hpath : path ∈ support := hp List.mem_cons_self
      have hz cursor := ihz path rest cursor
        (fun l hl => hleaf l (List.mem_append_left _ hl))
        (fun _ h => hi (List.mem_cons_of_mem _ (List.mem_append_left _ h)))
        hpath (fun _ h => hp (List.mem_cons_of_mem _ h))
      have ho cursor := iho path rest cursor
        (fun l hl => hleaf l (List.mem_append_right _ hl))
        (fun _ h => hi (List.mem_cons_of_mem _ (List.mem_append_right _ h)))
        hpath (fun _ h => hp (List.mem_cons_of_mem _ h))
      have he cursor := zeroEraseProgram_support n cursor control bit path support hc hib hpath
      have hca : circuitWires (computeZeroAnd control bit path) ⊆ support := by simp [computeZeroAnd,circuitWires,gateWires,hc,hib,hpath]
      have hcx : circuitWires [.CX control path] ⊆ support := by simp [circuitWires,gateWires,hc,hpath]
      rw [unaryProgram,compiledSupportIf]
      cases order <;> simp only [ite_true,ite_false,reduceCtorEq,prependCompiled_support,appendCompiled_support,List.append_subset]
      · exact ⟨hca,hz _,hcx,ho _,hcx,he _⟩
      · exact ⟨hca,hcx,ho _,hcx,hz _,he _⟩

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/EEACenterSupport ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/EEACenterSupport.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

theorem constMinusProgram_support (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (q c r t : Wire) (support : List Wire)
    (hd : input.length = dirty.length+1) (hk : bits.length = input.length)
    (hq : q ∈ support) (hc : c ∈ support) (hr : r ∈ support) (ht : t ∈ support)
    (hi : input ⊆ support) (hy : dirty ⊆ support) :
    straightWires (constMinusProgram n start input dirty bits q c r t).2 ⊆ support := by
  have hx : circuitWires (controlledComplement input q) ⊆ support := by
    intro w hw
    simp only [controlledComplement,circuitWires,List.mem_flatMap,List.mem_map] at hw
    obtain ⟨g,⟨z,hz,rfl⟩,hw⟩ := hw
    simp only [gateWires,List.mem_cons,List.mem_nil_iff,or_false] at hw
    rcases hw with rfl | rfl
    · exact hq
    · exact hi hz
  have hinc := gidneyProgram_support n start input dirty ((List.range input.length).map (Nat.testBit 1)) q c r t support hd (by simp) hq hc hr ht hi hy
  have hbody cursor := gidneyProgram_support n cursor input dirty bits q c r t support hd hk hq hc hr ht hi hy
  simp only [constMinusProgram,prependCompiled_support,appendCompiled_support,List.append_subset]
  exact ⟨hx,hinc,hbody _⟩

theorem eeaCenterProgram_support (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t iter : Wire) (support : List Wire)
    (hd : input.length = dirty.length) (hk : bits.length = input.length) (hpos : 0 < input.length)
    (hc : c ∈ support) (hr : r ∈ support) (ht : t ∈ support) (he : iter ∈ support)
    (hi : input ⊆ support) (hy : dirty ⊆ support) :
    straightWires (eeaCenterProgram n start input dirty bits p c r t iter).2 ⊆ support := by
  have htake : input.length = (dirty.take (input.length-1)).length+1 := by
    simp only [List.length_take]; omega
  have hb cursor := constMinusProgram_support n cursor input (dirty.take (input.length-1)) bits iter c r t support htake hk he hc hr ht hi (fun _ h => hy (List.mem_of_mem_take h))
  have htst := (uncontrolledCompareProgram_support n start input dirty (p/2+1) c r t iter).trans
    (show [c,r,t,iter]++input++dirty ⊆ support by
      simp only [List.append_subset,List.cons_subset,List.nil_subset,and_true]
      exact ⟨⟨⟨hc,hr,ht,he⟩,hi⟩,hy⟩)
  simp only [eeaCenterProgram,appendCompiled_support,List.append_subset]
  exact ⟨htst,hb _⟩

theorem eeaUncenterProgram_support (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t iter : Wire) (support : List Wire)
    (hd : input.length = dirty.length) (hk : bits.length = input.length) (hpos : 0 < input.length)
    (hc : c ∈ support) (hr : r ∈ support) (ht : t ∈ support) (he : iter ∈ support)
    (hi : input ⊆ support) (hy : dirty ⊆ support) :
    straightWires (eeaUncenterProgram n start input dirty bits p c r t iter).2 ⊆ support := by
  have htake : input.length = (dirty.take (input.length-1)).length+1 := by
    simp only [List.length_take]; omega
  have hb := constMinusProgram_support n start input (dirty.take (input.length-1)) bits iter c r t support htake hk he hc hr ht hi (fun _ h => hy (List.mem_of_mem_take h))
  have htst cursor := (uncontrolledCompareProgram_support n cursor input dirty (p/2+1) c r t iter).trans
    (show [c,r,t,iter]++input++dirty ⊆ support by
      simp only [List.append_subset,List.cons_subset,List.nil_subset,and_true]
      exact ⟨⟨⟨hc,hr,ht,he⟩,hi⟩,hy⟩)
  simp only [eeaUncenterProgram,appendCompiled_support,List.append_subset]
  exact ⟨hb,htst _⟩

theorem eeaParityProgram_support (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (c r t iter : Wire) (support : List Wire)
    (hd : input.length = dirty.length+1) (hk : bits.length = input.length)
    (hc : c ∈ support) (hr : r ∈ support) (ht : t ∈ support) (he : iter ∈ support)
    (hi : input ⊆ support) (hy : dirty ⊆ support) :
    straightWires (eeaParityProgram n start input dirty bits c r t iter).2 ⊆ support := by
  have hb := constMinusProgram_support n start input dirty bits iter c r t support hd hk he hc hr ht hi hy
  have hx : circuitWires [.X iter] ⊆ support := by simp [circuitWires,gateWires,he]
  simp only [eeaParityProgram,prependCompiled_support,appendCompiled_support,literalProgram_support,List.append_subset]
  exact ⟨hx,hb,hx⟩
end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/MultiplicationSupport ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/MultiplicationSupport.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

theorem modularSubProgram_support (n start : Nat) (input acc : List Wire) (modulus : List Bool)
    (p : Nat) (q c r t f : Wire) (support : List Wire)
    (hl : input.length = acc.length) (hk : modulus.length = acc.length) (hpos : 0 < acc.length)
    (hq : q ∈ support) (hc : c ∈ support) (hr : r ∈ support) (ht : t ∈ support) (hf : f ∈ support)
    (hi : input ⊆ support) (ha : acc ⊆ support) :
    straightWires (modularSubProgram n start input acc modulus p q c r t f).2 ⊆ support := by
  have hsmall : q::c::f::input++acc ⊆ support := by
    simp only [List.append_subset,List.cons_subset]
    exact ⟨⟨hq,hc,hf,hi⟩,ha⟩
  have hsub : circuitWires (controlledSubCarry input acc q c f) ⊆ support :=
    (circuitWires_subset_of_usesOnly (controlledAddCarry_usesOnly input acc q c f).adjoint).trans hsmall
  have hcompare cursor := (uncontrolledCompareProgram_support n cursor acc input p c r t f).trans
    (show [c,r,t,f]++acc++input ⊆ support by
      simp only [List.append_subset,List.cons_subset,List.nil_subset,and_true]
      exact ⟨⟨⟨hc,hr,ht,hf⟩,ha⟩,hi⟩)
  have htake : acc.length = (input.take (acc.length-1)).length+1 := by
    simp only [List.length_take]; omega
  have hadd cursor := gidneyProgram_support n cursor acc (input.take (acc.length-1)) modulus f c r t
    support htake hk hf hc hr ht ha (fun _ h => hi (List.mem_of_mem_take h))
  have hlast : circuitWires (controlledCompareLT acc input q c f) ⊆ support := by
    cases acc with
    | nil => simp at hpos
    | cons a acc =>
      intro w hw
      have h := (controlledCompareLT_wires a acc input q c f w hl.symm).mp hw
      have hsub : q::c::f::(a::acc)++input ⊆ support := by
        simp only [List.append_subset,List.cons_subset]
        exact ⟨⟨hq,hc,hf,(List.cons_subset.mp ha).1,(List.cons_subset.mp ha).2⟩,hi⟩
      exact hsub h
  simp only [modularSubProgram,prependCompiled_support,appendCompiled_support,literalProgram_support,List.append_subset]
  exact ⟨hlast,hadd _,hcompare _,hsub⟩

theorem modularDoubleProgram_support (n start : Nat) (acc dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (support : List Wire)
    (hd : acc.length = dirty.length) (hk : bits.length = acc.length)
    (hc : c ∈ support) (hr : r ∈ support) (ht : t ∈ support) (hf : f ∈ support)
    (ha : acc ⊆ support) (hy : dirty ⊆ support) :
    straightWires (modularDoubleProgram n start acc dirty bits p c r t f).2 ⊆ support := by
  cases acc with
  | nil => exact List.nil_subset _
  | cons a acc =>
    have hcompare cursor := (uncontrolledCompareProgram_support n cursor (a::acc) dirty p c r t f).trans
      (show [c,r,t,f]++(a::acc)++dirty ⊆ support by
        simp only [List.append_subset,List.cons_subset,List.nil_subset,and_true]
        exact ⟨⟨⟨hc,hr,ht,hf⟩,(List.cons_subset.mp ha).1,(List.cons_subset.mp ha).2⟩,hy⟩)
    have htake : (a::acc).length = (dirty.take acc.length).length+1 := by
      simp only [List.length_take,List.length_cons] at hd ⊢; omega
    have hadd cursor := gidneyProgram_support n cursor (a::acc) (dirty.take acc.length) bits f c r t
      support htake hk hf hc hr ht ha (fun _ h => hy (List.mem_of_mem_take h))
    have hshift := (circuitWires_subset_of_usesOnly (doublingShift_usesOnly a f acc)).trans
      (List.cons_subset.mpr ⟨hf,ha⟩)
    have hlast : circuitWires [.CX a f] ⊆ support := by
      simp [circuitWires,gateWires,(List.cons_subset.mp ha).1,hf]
    simp only [modularDoubleProgram,prependCompiled_support,appendCompiled_support,literalProgram_support,List.append_subset]
    exact ⟨hshift,hcompare _,hadd _,hlast⟩

theorem modularHalveProgram_support (n start : Nat) (acc dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (support : List Wire)
    (hd : acc.length = dirty.length) (hk : bits.length = acc.length)
    (hc : c ∈ support) (hr : r ∈ support) (ht : t ∈ support) (hf : f ∈ support)
    (ha : acc ⊆ support) (hy : dirty ⊆ support) :
    straightWires (modularHalveProgram n start acc dirty bits p c r t f).2 ⊆ support := by
  cases acc with
  | nil => exact List.nil_subset _
  | cons a acc =>
    have hcompare cursor := (uncontrolledCompareProgram_support n cursor (a::acc) dirty p c r t f).trans
      (show [c,r,t,f]++(a::acc)++dirty ⊆ support by
        simp only [List.append_subset,List.cons_subset,List.nil_subset,and_true]
        exact ⟨⟨⟨hc,hr,ht,hf⟩,(List.cons_subset.mp ha).1,(List.cons_subset.mp ha).2⟩,hy⟩)
    have htake : (a::acc).length = (dirty.take acc.length).length+1 := by
      simp only [List.length_take,List.length_cons] at hd ⊢; omega
    have hadd cursor := gidneyProgram_support n cursor (a::acc) (dirty.take acc.length) bits f c r t
      support htake hk hf hc hr ht ha (fun _ h => hy (List.mem_of_mem_take h))
    have hshift := (circuitWires_subset_of_usesOnly (doublingShift_usesOnly a f acc).adjoint).trans
      (List.cons_subset.mpr ⟨hf,ha⟩)
    have hfirst : circuitWires [.CX a f] ⊆ support := by
      simp [circuitWires,gateWires,(List.cons_subset.mp ha).1,hf]
    simp only [modularHalveProgram,prependCompiled_support,appendCompiled_support,literalProgram_support,List.append_subset]
    exact ⟨hfirst,hadd _,hcompare _,hshift⟩



theorem compiledIf_support {n start : Nat} (b : Prop) [Decidable b]
    (p q : (count : Nat) × Straight n start (start+count)) :
    straightWires (if b then p else q).2 = if b then straightWires p.2 else straightWires q.2 := by
  by_cases hb : b
  · rw [if_pos hb,if_pos hb]
  · rw [if_neg hb,if_neg hb]

attribute [local irreducible] modularAddProgram modularSubProgram modularDoubleProgram modularHalveProgram

theorem hornerProgram_support (n start : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (support : List Wire)
    (hd : input.length = acc.length) (hk : bits.length = acc.length) (hpos : 0 < acc.length)
    (hc : c ∈ support) (hr : r ∈ support) (ht : t ∈ support) (hf : f ∈ support)
    (hqs : controls ⊆ support) (hi : input ⊆ support) (ha : acc ⊆ support) :
    straightWires (hornerProgram n start controls input acc bits p c r t f).2 ⊆ support := by
  induction controls generalizing start with
  | nil => exact List.nil_subset _
  | cons q qs ih =>
    have hb cursor := ih cursor (fun _ h => hqs (List.mem_cons_of_mem _ h))
    have hadd cursor := modularAddProgram_support n cursor input acc bits p q c r t f support hd hk hpos
      (hqs List.mem_cons_self) hc hr ht hf hi ha
    have hdbl cursor := modularDoubleProgram_support n cursor acc input bits p f r t c support hd.symm hk hf hr ht hc ha hi
    rw [hornerProgram]
    simp only [appendCompiled_support,compiledIf_support,List.append_subset]
    refine ⟨hb _,?_⟩
    split
    · exact hadd _
    · exact List.append_subset.mpr ⟨hdbl _,hadd _⟩

theorem hornerInverseProgram_support (n start : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (support : List Wire)
    (hd : input.length = acc.length) (hk : bits.length = acc.length) (hpos : 0 < acc.length)
    (hc : c ∈ support) (hr : r ∈ support) (ht : t ∈ support) (hf : f ∈ support)
    (hqs : controls ⊆ support) (hi : input ⊆ support) (ha : acc ⊆ support) :
    straightWires (hornerInverseProgram n start controls input acc bits p c r t f).2 ⊆ support := by
  induction controls generalizing start with
  | nil => exact List.nil_subset _
  | cons q qs ih =>
    have hb cursor := ih cursor (fun _ h => hqs (List.mem_cons_of_mem _ h))
    have hsub cursor := modularSubProgram_support n cursor input acc bits p q c r t f support hd hk hpos
      (hqs List.mem_cons_self) hc hr ht hf hi ha
    have hhalf cursor := modularHalveProgram_support n cursor acc input bits p f r t c support hd.symm hk hf hr ht hc ha hi
    rw [hornerInverseProgram]
    simp only [appendCompiled_support,compiledIf_support,List.append_subset]
    refine ⟨hsub _,?_⟩
    split
    · exact List.nil_subset _
    · exact List.append_subset.mpr ⟨hhalf _,hb _⟩

theorem squareAddProgram_support (n start : Nat) (input acc : List Wire) (bits : List Bool)
    (p : Nat) (q copied c r t f : Wire) (support : List Wire)
    (hd : input.length = acc.length) (hk : bits.length = acc.length) (hpos : 0 < acc.length)
    (hq : q ∈ support) (hcopy : copied ∈ support) (hc : c ∈ support) (hr : r ∈ support)
    (ht : t ∈ support) (hf : f ∈ support) (hi : input ⊆ support) (ha : acc ⊆ support) :
    straightWires (squareAddProgram n start input acc bits p q copied c r t f).2 ⊆ support := by
  have hb := modularAddProgram_support n start input acc bits p copied c r t f support hd hk hpos hcopy hc hr ht hf hi ha
  have hx : circuitWires [.CX q copied] ⊆ support := by simp [circuitWires,gateWires,hq,hcopy]
  simp only [squareAddProgram,prependCompiled_support,appendCompiled_support,literalProgram_support,List.append_subset]
  exact ⟨hx,hb,hx⟩

theorem squareSubProgram_support (n start : Nat) (input acc : List Wire) (bits : List Bool)
    (p : Nat) (q copied c r t f : Wire) (support : List Wire)
    (hd : input.length = acc.length) (hk : bits.length = acc.length) (hpos : 0 < acc.length)
    (hq : q ∈ support) (hcopy : copied ∈ support) (hc : c ∈ support) (hr : r ∈ support)
    (ht : t ∈ support) (hf : f ∈ support) (hi : input ⊆ support) (ha : acc ⊆ support) :
    straightWires (squareSubProgram n start input acc bits p q copied c r t f).2 ⊆ support := by
  have hb := modularSubProgram_support n start input acc bits p copied c r t f support hd hk hpos hcopy hc hr ht hf hi ha
  have hx : circuitWires [.CX q copied] ⊆ support := by simp [circuitWires,gateWires,hq,hcopy]
  simp only [squareSubProgram,prependCompiled_support,appendCompiled_support,literalProgram_support,List.append_subset]
  exact ⟨hx,hb,hx⟩

attribute [local irreducible] squareAddProgram squareSubProgram

theorem squareProgram_support (n start : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (copied c r t f : Wire) (support : List Wire)
    (hd : input.length = acc.length) (hk : bits.length = acc.length) (hpos : 0 < acc.length)
    (hcopy : copied ∈ support) (hc : c ∈ support) (hr : r ∈ support) (ht : t ∈ support) (hf : f ∈ support)
    (hqs : controls ⊆ support) (hi : input ⊆ support) (ha : acc ⊆ support) :
    straightWires (squareProgram n start controls input acc bits p copied c r t f).2 ⊆ support := by
  induction controls generalizing start with
  | nil => exact List.nil_subset _
  | cons q qs ih =>
    have hb cursor := ih cursor (fun _ h => hqs (List.mem_cons_of_mem _ h))
    have hadd cursor := squareAddProgram_support n cursor input acc bits p q copied c r t f support hd hk hpos
      (hqs List.mem_cons_self) hcopy hc hr ht hf hi ha
    have hdbl cursor := modularDoubleProgram_support n cursor acc input bits p f r t c support hd.symm hk hf hr ht hc ha hi
    rw [squareProgram]
    simp only [appendCompiled_support,compiledIf_support,List.append_subset]
    refine ⟨hb _,?_⟩
    split
    · exact hadd _
    · exact List.append_subset.mpr ⟨hdbl _,hadd _⟩

theorem squareInverseProgram_support (n start : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (copied c r t f : Wire) (support : List Wire)
    (hd : input.length = acc.length) (hk : bits.length = acc.length) (hpos : 0 < acc.length)
    (hcopy : copied ∈ support) (hc : c ∈ support) (hr : r ∈ support) (ht : t ∈ support) (hf : f ∈ support)
    (hqs : controls ⊆ support) (hi : input ⊆ support) (ha : acc ⊆ support) :
    straightWires (squareInverseProgram n start controls input acc bits p copied c r t f).2 ⊆ support := by
  induction controls generalizing start with
  | nil => exact List.nil_subset _
  | cons q qs ih =>
    have hb cursor := ih cursor (fun _ h => hqs (List.mem_cons_of_mem _ h))
    have hsub cursor := squareSubProgram_support n cursor input acc bits p q copied c r t f support hd hk hpos
      (hqs List.mem_cons_self) hcopy hc hr ht hf hi ha
    have hhalf cursor := modularHalveProgram_support n cursor acc input bits p f r t c support hd.symm hk hf hr ht hc ha hi
    rw [squareInverseProgram]
    simp only [appendCompiled_support,compiledIf_support,List.append_subset]
    refine ⟨hsub _,?_⟩
    split
    · exact List.nil_subset _
    · exact List.append_subset.mpr ⟨hhalf _,hb _⟩



attribute [local irreducible] squareProgram squareInverseProgram

theorem squareSubtractProgram_support (n start : Nat) (x y acc : List Wire) (correction modulus : List Bool)
    (p : Nat) (q copied c r t f : Wire) (support : List Wire)
    (hx : x.length = acc.length) (hy : y.length = acc.length)
    (hk : correction.length = acc.length) (hm : modulus.length = acc.length) (hpos : 0 < acc.length)
    (hq : q ∈ support) (hcopy : copied ∈ support) (hc : c ∈ support) (hr : r ∈ support)
    (ht : t ∈ support) (hf : f ∈ support)
    (hsx : x ⊆ support) (hsy : y ⊆ support) (hsa : acc ⊆ support) :
    straightWires (squareSubtractProgram n start x y acc correction modulus p q copied c r t f).2 ⊆ support := by
  have hs cursor := squareProgram_support n cursor y y acc correction p copied c r t f support hy hk hpos hcopy hc hr ht hf hsy hsy hsa
  have hu cursor := squareInverseProgram_support n cursor y y acc modulus p copied c r t f support hy hm hpos hcopy hc hr ht hf hsy hsy hsa
  have hsub cursor := modularSubProgram_support n cursor acc x modulus p q copied f r c support hx.symm
    (hm.trans hx.symm) (hx.symm ▸ hpos) hq hcopy hf hr hc hsa hsx
  simp only [squareSubtractProgram,appendCompiled_support,List.append_subset]
  exact ⟨hs _,hsub _,hu _⟩

theorem pointSquareProgram_support_static (n start : Nat) :
    straightWires (pointSquareProgram n start).2 ⊆ windowBaseSupport := by
  apply squareSubtractProgram_support
  all_goals try simp [secp256k1ReductionConstantBits,windowBaseSupport]
  all_goals intro w hw
  all_goals simp only [List.mem_range'_1,List.mem_cons,List.mem_append,List.mem_range] at hw ⊢
  all_goals omega


theorem multiplyWorkProgram_support_static (n start : Nat) :
    straightWires (multiplyWorkProgram n start).2 ⊆ windowBaseSupport := by
  apply hornerProgram_support
  all_goals try simp [secp256k1ReductionConstantBits,windowBaseSupport]
  all_goals intro w hw
  all_goals simp only [List.mem_range'_1,List.mem_cons,List.mem_append,List.mem_range] at hw ⊢
  all_goals omega

theorem multiplyDataProgram_support_static (n start : Nat) :
    straightWires (multiplyDataProgram n start).2 ⊆ windowBaseSupport := by
  apply hornerProgram_support
  all_goals try simp [secp256k1ReductionConstantBits,windowBaseSupport]
  all_goals intro w hw
  all_goals simp only [List.mem_range'_1,List.mem_cons,List.mem_append,List.mem_range] at hw ⊢
  all_goals omega

theorem unmultiplyDataProgram_support_static (n start : Nat) :
    straightWires (unmultiplyDataProgram n start).2 ⊆ windowBaseSupport := by
  apply hornerInverseProgram_support
  all_goals try simp [windowBaseSupport]
  all_goals intro w hw
  all_goals simp only [List.mem_range'_1,List.mem_cons,List.mem_append,List.mem_range] at hw ⊢
  all_goals omega

theorem xNegateProgram_support_static (n start : Nat) :
    straightWires (xNegateProgram n start).2 ⊆ windowBaseSupport := by
  apply modularNegateProgram_support
  all_goals try simp [windowBaseSupport]
  all_goals intro w hw
  all_goals simp only [List.mem_range'_1,List.mem_cons,List.mem_append,List.mem_range] at hw ⊢
  all_goals omega

end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/CoefficientSupport ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/CoefficientSupport.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

theorem coefficientFirstProgram_support (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (label : Nat) (control : Wire) (support : List Wire)
    (hc : control ∈ support) (ha : r.accumulator k K ∈ support) (ht : r.targetAt target k label ∈ support)
    (had : r.addendAt target k label ∈ support) (hcarry : r.carry k K ∈ support)
    (hs : r.cellScratch k K ∈ support) :
    straightWires (coefficientFirstProgram n start r k K mode target label control).2 ⊆ support := by
  have hb := rippleFirstProgram_support n start mode _ _ _ _ _ support ha ht had hcarry hs
  simp only [coefficientFirstProgram,appendCompiled_support,literalProgram_support,List.append_subset]
  refine ⟨hb,?_⟩
  simp [circuitWires,gateWires,hc,ha]

theorem coefficientSecondProgram_support (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (label : Nat) (control : Wire) (support : List Wire)
    (hc : control ∈ support) (ha : r.accumulator k K ∈ support) (ht : r.targetAt target k label ∈ support)
    (had : r.addendAt target k label ∈ support) (hcarry : r.carry k K ∈ support)
    (hs : r.cellScratch k K ∈ support) :
    straightWires (coefficientSecondProgram n start r k K mode target label control).2 ⊆ support := by
  have hb := rippleSecondProgram_support n start mode _ _ _ _ _ support ha ht had hcarry hs
  simp only [coefficientSecondProgram,prependCompiled_support,List.append_subset]
  refine ⟨?_,hb⟩
  simp [circuitWires,gateWires,hc,ha]

theorem coefficientProgram_support (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget) (support : List Wire)
    (hc : r.control ∈ support) (ha : r.accumulator k K ∈ support)
    (hcarry : r.carry k K ∈ support) (hs : r.cellScratch k K ∈ support)
    (hindex : (coefficientPrefixTree r k K).indexWires ⊆ support)
    (hpath : r.path k K ⊆ support)
    (ht : ∀ l ∈ (coefficientPrefixTree r k K).labels, r.targetAt target k l ∈ support)
    (had : ∀ l ∈ (coefficientPrefixTree r k K).labels, r.addendAt target k l ∈ support)
    (hsgn : circuitWires (coefficientPrefixSignCircuit r k K signUpdate) ⊆ support) :
    straightWires (coefficientProgram n start r k K mode signUpdate target).2 ⊆ support := by
  have hfirst cursor := unaryProgram_support n .inc
    (fun label control cursor => coefficientFirstProgram n cursor r k K mode target label control)
    (coefficientPrefixTree r k K) r.control (r.path k K) cursor support
    (fun l hl q cursor hq => coefficientFirstProgram_support n cursor r k K mode target l q support hq ha (ht l hl) (had l hl) hcarry hs)
    hindex hc hpath
  have hsecond cursor := unaryProgram_support n .dec
    (fun label control cursor => coefficientSecondProgram n cursor r k K mode target label control)
    (coefficientPrefixTree r k K) r.control (r.path k K) cursor support
    (fun l hl q cursor hq => coefficientSecondProgram_support n cursor r k K mode target l q support hq ha (ht l hl) (had l hl) hcarry hs)
    hindex hc hpath
  have hx : circuitWires [.CX r.control (r.accumulator k K)] ⊆ support := by simp [circuitWires,gateWires,hc,ha]
  simp only [coefficientProgram,prependCompiled_support,appendCompiled_support,literalProgram_support,List.append_subset]
  exact ⟨hx,hfirst _,hsgn,hsecond _,hx⟩

private theorem getD_support {xs support : List Wire} (i : Nat) (fallback : Wire)
    (hxs : xs ⊆ support) (hf : fallback ∈ support) : xs.getD i fallback ∈ support := by
  by_cases h : i < xs.length
  · rw [List.getD_eq_getElem xs fallback h]
    exact hxs (List.getElem_mem h)
  · rw [List.getD_eq_default xs fallback (by omega)]
    exact hf

theorem coefficientProgram_support_layout (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (hl : CoefficientPrefixLayout r k K) :
    straightWires (coefficientProgram n start r k K mode signUpdate target).2 ⊆ r.allWires := by
  have hscratch : r.scratch ⊆ r.allWires := by intro w hw; simp [CoefficientPrefixRegisters.allWires,hw]
  have hsget (i : Nat) (hi : i < r.scratch.length) : r.scratch.getD i 0 ∈ r.allWires := by
    rw [List.getD_eq_getElem r.scratch 0 hi]
    exact hscratch (List.getElem_mem hi)
  have hcarry : r.carry k K ∈ r.allWires := hsget _ (by rw [hl.scratch_length]; omega)
  have hw1 : r.work1 ⊆ r.allWires := by intro w hw; simp [CoefficientPrefixRegisters.allWires,hw]
  have hw2 : r.work2 ⊆ r.allWires := by intro w hw; simp [CoefficientPrefixRegisters.allWires,hw]
  have hfirst1 : r.work1.getD 0 0 ∈ r.allWires := by
    have hp : 0 < r.work1.length := by rw [hl.work1_length]; omega
    rw [List.getD_eq_getElem r.work1 0 hp]
    exact hw1 (List.getElem_mem hp)
  have hfirst2 : r.work2.getD 0 0 ∈ r.allWires := by
    have hp : 0 < r.work2.length := by rw [hl.work2_length]; omega
    rw [List.getD_eq_getElem r.work2 0 hp]
    exact hw2 (List.getElem_mem hp)
  have hwork1 l : r.work1At k l ∈ r.allWires := getD_support _ _ hw1 hfirst1
  have hwork2 l : r.work2At k l ∈ r.allWires := getD_support _ _ hw2 hfirst2
  apply coefficientProgram_support
  · simp [CoefficientPrefixRegisters.allWires]
  · exact hsget _ (by rw [hl.scratch_length]; omega)
  · exact hcarry
  · exact hsget _ (by rw [hl.scratch_length]; omega)
  · intro w hw
    have hmem := quotientSwapTree_indexWires_mem_lengthQ (r.routing k K) hl.k_le_K
      (by simpa [CoefficientPrefixRegisters.routing] using hl.index_width) w hw
    have hb : w ∈ r.boundary := hmem
    simp [CoefficientPrefixRegisters.allWires,hb]
  · intro w hw
    exact hscratch (List.mem_of_mem_take hw)
  · intro l _
    cases target
    · exact hwork1 l
    · exact hwork2 l
  · intro l _
    cases target
    · exact hwork2 l
    · exact hwork1 l
  · have hsign : r.sign ∈ r.allWires := by simp [CoefficientPrefixRegisters.allWires]
    cases signUpdate <;> simp [coefficientPrefixSignCircuit,circuitWires,gateWires,hcarry,hsign]

theorem coefficientInverseProgram_support_layout (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (hl : CoefficientPrefixLayout r k K) :
    straightWires (coefficientInverseProgram n start r k K mode signUpdate target).2 ⊆ r.allWires := by
  exact coefficientProgram_support_layout n start r k K mode.inverse signUpdate target hl
end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/PhaseSupport ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/PhaseSupport.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

theorem phaseCoreGates_support (r : PhaseUpdateRegisters) :
    circuitWires (phaseCoreGates r) ⊆ r.allWires := by
  intro w hw
  simp only [phaseCoreGates,circuitWires,List.flatMap_cons,List.flatMap_nil,gateWires,
    List.mem_append,List.mem_cons,List.mem_nil_iff,or_false] at hw
  simp only [PhaseUpdateRegisters.allWires,PhaseUpdateRegisters.scratch,
    List.mem_append,List.mem_cons,List.mem_nil_iff,or_false]
  tauto

theorem phaseInverseCoreGates_support (r : PhaseUpdateRegisters) :
    circuitWires (phaseInverseCoreGates r) ⊆ r.allWires := by
  intro w hw
  simp only [phaseInverseCoreGates,circuitWires,List.flatMap_cons,List.flatMap_nil,gateWires,
    List.mem_append,List.mem_cons,List.mem_nil_iff,or_false] at hw
  simp only [PhaseUpdateRegisters.allWires,PhaseUpdateRegisters.scratch,
    List.mem_append,List.mem_cons,List.mem_nil_iff,or_false]
  tauto

theorem phaseSegments_support (n : Nat) (r : PhaseUpdateRegisters) (shift : Wire)
    (core : Circuit) (hcore : circuitWires core ⊆ r.epochWires shift) :
    ∀ seg ∈ phaseSegments n r shift core, ∀ start,
      straightWires (seg start).2 ⊆ r.epochWires shift := by
  have hq cursor := vchainProgram_support n cursor (r.withShiftEpoch shift).lengthQ
    (r.withShiftEpoch shift).zeroQ (r.withShiftEpoch shift).equalityScratch (r.epochWires shift)
    (by intro w hw; simp [PhaseUpdateRegisters.epochWires,PhaseUpdateRegisters.allWires,hw])
    (by simp [PhaseUpdateRegisters.epochWires,PhaseUpdateRegisters.allWires,PhaseUpdateRegisters.scratch])
    (by intro w hw; simp [PhaseUpdateRegisters.epochWires,PhaseUpdateRegisters.allWires,PhaseUpdateRegisters.scratch,hw])
  have hr cursor := vchainProgram_support n cursor (r.withShiftEpoch shift).lengthRPrime
    (r.withShiftEpoch shift).zeroRPrime (r.withShiftEpoch shift).equalityScratch (r.epochWires shift)
    (by intro w hw; simp [PhaseUpdateRegisters.epochWires,PhaseUpdateRegisters.allWires,hw])
    (by simp [PhaseUpdateRegisters.epochWires,PhaseUpdateRegisters.allWires,PhaseUpdateRegisters.scratch])
    (by intro w hw; simp [PhaseUpdateRegisters.epochWires,PhaseUpdateRegisters.allWires,PhaseUpdateRegisters.scratch,hw])
  have hs cursor := vchainProgram_support n cursor (r.withShiftEpoch shift).lengthS
    (r.withShiftEpoch shift).zeroS (r.withShiftEpoch shift).equalityScratch (r.epochWires shift)
    (by intro w hw; simp [PhaseUpdateRegisters.epochWires,PhaseUpdateRegisters.allWires,hw])
    (by simp [PhaseUpdateRegisters.epochWires,PhaseUpdateRegisters.allWires,PhaseUpdateRegisters.scratch])
    (by intro w hw; simp [PhaseUpdateRegisters.epochWires,PhaseUpdateRegisters.allWires,PhaseUpdateRegisters.scratch,hw])
  have hx : circuitWires [.X shift] ⊆ r.epochWires shift := by
    simp [circuitWires,gateWires,PhaseUpdateRegisters.epochWires,PhaseUpdateRegisters.withShiftEpoch,PhaseUpdateRegisters.allWires]
  intro seg hseg start
  simp only [phaseSegments,List.mem_cons,List.mem_nil_iff,or_false] at hseg
  rcases hseg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact hq _ | exact hr _ | exact hs _ | simpa only [literalProgram_support] using hx | simpa only [literalProgram_support] using hcore

theorem phaseProgram_support (n start : Nat) (r : PhaseUpdateRegisters) (shift : Wire) :
    straightWires (phaseProgram n start r shift).2 ⊆ r.epochWires shift := by
  exact sequenceProgram_support n _ _ (phaseSegments_support n r shift _ (phaseCoreGates_support _)) start

theorem phaseInverseProgram_support (n start : Nat) (r : PhaseUpdateRegisters) (shift : Wire) :
    straightWires (phaseInverseProgram n start r shift).2 ⊆ r.epochWires shift := by
  exact sequenceProgram_support n _ _ (phaseSegments_support n r shift _ (phaseInverseCoreGates_support _)) start
end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/IntervalSupport ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/IntervalSupport.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
private theorem list_getD_mem
    (list : List α) (index : Nat) (fallback : α)
    (hindex : index < list.length) :
    list.getD index fallback ∈ list := by
  rw [List.getD_eq_getElem list fallback hindex]
  exact List.getElem_mem hindex


private theorem intervalTopRelative_lt_laneCount
    (k K : Nat) (hkK : k ≤ K) :
    intervalTopRelative k K < intervalLaneCount k K := by
  simp only [intervalTopRelative, intervalLaneCount]
  omega


private theorem intervalTargetAt_mem_allWires
    (registers : IntervalRegisters) (k K label : Nat)
    (target : IntervalTarget) (hlayout : IntervalLayout registers k K target)
    (hlabel : label < intervalLaneCount k K) :
    registers.targetAt target label ∈ registers.allWires := by
  cases target with
  | work1 =>
      have hbound : label < registers.work1.length := by
        rw [hlayout.work1_length]
        exact hlabel
      have hmem := list_getD_mem registers.work1 label 0 hbound
      change registers.work1.getD label 0 ∈ registers.allWires
      rw [IntervalRegisters.allWires]
      exact List.mem_append_right _ (List.mem_append_left _ hmem)
  | work2 =>
      have hbound : label < registers.work2.length := by
        rw [hlayout.work2_length]
        exact hlabel
      have hmem := list_getD_mem registers.work2 label 0 hbound
      change registers.work2.getD label 0 ∈ registers.allWires
      rw [IntervalRegisters.allWires]
      exact List.mem_append_right _
        (List.mem_append_right _ (List.mem_append_left _ hmem))


private theorem intervalAddendAt_mem_allWires
    (registers : IntervalRegisters) (k K label : Nat)
    (target : IntervalTarget) (hlayout : IntervalLayout registers k K target)
    (hlabel : label < intervalLaneCount k K) :
    registers.addendAt target label ∈ registers.allWires := by
  cases target with
  | work1 =>
      have hbound : label < registers.work2.length := by
        rw [hlayout.work2_length]
        exact hlabel
      have hmem := list_getD_mem registers.work2 label 0 hbound
      change registers.work2.getD label 0 ∈ registers.allWires
      rw [IntervalRegisters.allWires]
      exact List.mem_append_right _
        (List.mem_append_right _ (List.mem_append_left _ hmem))
  | work2 =>
      have hbound : label < registers.work1.length := by
        rw [hlayout.work1_length]
        exact hlabel
      have hmem := list_getD_mem registers.work1 label 0 hbound
      change registers.work1.getD label 0 ∈ registers.allWires
      rw [IntervalRegisters.allWires]
      exact List.mem_append_right _ (List.mem_append_left _ hmem)


private theorem intervalScratch_mem_allWires
    (registers : IntervalRegisters) {wire : Wire}
    (hwire : wire ∈ registers.scratch) :
    wire ∈ registers.allWires := by
  rw [IntervalRegisters.allWires]
  exact List.mem_append_right _ (List.mem_append_right _
    (List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_right _ hwire)))))


private theorem intervalRightTop_mem_allWires
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    registers.rightTop k K ∈ registers.allWires := by
  by_cases hspecial : intervalHasTopSpecial k K = true
  · have hmem := list_getD_mem registers.lengthS (intervalTopBit k K) 0
      (hlayout.right_top_capacity hspecial)
    rw [IntervalRegisters.rightTop, if_pos hspecial, IntervalRegisters.allWires]
    exact List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_right _ (List.mem_append_left _ hmem)))))
  · have hbound : 0 < registers.lengthT.length := by
      have := hlayout.lengthT_two_le
      omega
    have hmem := list_getD_mem registers.lengthT 0 0 hbound
    rw [IntervalRegisters.rightTop, if_neg hspecial, IntervalRegisters.allWires]
    exact List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_left _ hmem)))


private theorem intervalLeftTop_mem_allWires
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    registers.leftTop k K ∈ registers.allWires := by
  by_cases hspecial : intervalHasTopSpecial k K = true
  · have hmem := list_getD_mem registers.lengthQ (intervalTopBit k K) 0
      (hlayout.left_top_capacity hspecial)
    rw [IntervalRegisters.leftTop, if_pos hspecial, IntervalRegisters.allWires]
    exact List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_left _ hmem))))
  · have hbound : 1 < registers.lengthT.length := by
      have := hlayout.lengthT_two_le
      omega
    have hmem := list_getD_mem registers.lengthT 1 0 hbound
    rw [IntervalRegisters.leftTop, if_neg hspecial, IntervalRegisters.allWires]
    exact List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_left _ hmem)))


private theorem intervalEndpointSupport_mem_allWires
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    ∀ wire,
      wire ∈ intervalEndpointSupport registers.lengthT registers.lengthQ
          registers.lengthS registers.endpointScratch (registers.carry k K) →
        wire ∈ registers.allWires := by
  intro wire hwire
  simp only [intervalEndpointSupport, List.mem_append, List.mem_singleton] at hwire
  rcases hwire with ((((hscratch | hcarry) | ht) | hq) | hs)
  · exact intervalScratch_mem_allWires registers
      (List.mem_of_mem_take hscratch)
  · subst wire
    exact intervalScratch_mem_allWires registers
      (intervalCarry_mem_scratch registers k K target hlayout)
  · simp [IntervalRegisters.allWires, ht]
  · simp [IntervalRegisters.allWires, hq]
  · simp [IntervalRegisters.allWires, hs]


private theorem intervalDecoder_mem_allWires
    (registers : IntervalRegisters) (k K : Nat) (target : IntervalTarget)
    (hlayout : IntervalLayout registers k K target) :
    ∀ wire,
      wire ∈ (intervalTree registers k K).decoderWires registers.control
          registers.control (registers.rightPaths k K) (registers.leftPaths k K) →
        wire ∈ registers.allWires := by
  intro wire hwire
  simp only [DualUnaryActionTree.decoderWires, List.mem_append,
    List.mem_dedup, List.mem_cons, List.not_mem_nil, or_false] at hwire
  rcases hwire with hcontrol | hindexA | hindexB | hrightPath | hleftPath
  · rcases hcontrol with rfl | rfl <;> simp [IntervalRegisters.allWires]
  · obtain ⟨bit, hbit, rfl⟩ := DualUnaryActionTree.build_indexAWires
      registers.rightIndex registers.leftIndex
      (DualUnaryActionTree.sourceWidth (intervalMainLabels k K).toFinset)
      (intervalMainLabels k K).toFinset (intervalTree registers k K) (by
        simpa [DualUnaryActionTree.buildSourceFromList,
          DualUnaryActionTree.buildSource] using intervalTree_built registers k K)
      (by simpa using hindexA)
    have hbound : bit < registers.lengthS.length :=
      lt_of_lt_of_le hbit hlayout.right_index_capacity
    have hmem := list_getD_mem registers.lengthS bit 0 hbound
    change registers.lengthS.getD bit 0 ∈ registers.allWires
    rw [IntervalRegisters.allWires]
    exact List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_right _ (List.mem_append_left _ hmem)))))
  · obtain ⟨bit, hbit, rfl⟩ := DualUnaryActionTree.build_indexBWires
      registers.rightIndex registers.leftIndex
      (DualUnaryActionTree.sourceWidth (intervalMainLabels k K).toFinset)
      (intervalMainLabels k K).toFinset (intervalTree registers k K) (by
        simpa [DualUnaryActionTree.buildSourceFromList,
          DualUnaryActionTree.buildSource] using intervalTree_built registers k K)
      (by simpa using hindexB)
    have hbound : bit < registers.lengthQ.length :=
      lt_of_lt_of_le hbit hlayout.left_index_capacity
    have hmem := list_getD_mem registers.lengthQ bit 0 hbound
    change registers.lengthQ.getD bit 0 ∈ registers.allWires
    rw [IntervalRegisters.allWires]
    exact List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_left _ hmem))))
  · have hscratch : wire ∈ registers.scratch :=
      List.mem_of_mem_take hrightPath
    simp [IntervalRegisters.allWires, hscratch]
  · have hscratch : wire ∈ registers.scratch :=
      List.mem_of_mem_drop (List.mem_of_mem_take hleftPath)
    simp [IntervalRegisters.allWires, hscratch]



theorem intervalTopFirstProgram_support (n start : Nat) (r : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (target : IntervalTarget) (hl : IntervalLayout r k K target) :
    straightWires (intervalTopFirstProgram n start r k K mode target).2 ⊆ r.allWires := by
  unfold intervalTopFirstProgram
  rw [compiledIf_support]
  split
  · apply topFirstProgram_support
    · intro w hw; simp [IntervalRegisters.allWires,hw]
    · intro w hw; simp [IntervalRegisters.allWires,hw]
    · exact intervalScratch_mem_allWires r (intervalAccumulator_mem_scratch r k K target hl)
    · exact intervalTargetAt_mem_allWires r k K _ target hl (intervalTopRelative_lt_laneCount k K hl.k_le_K)
    · exact intervalAddendAt_mem_allWires r k K _ target hl (intervalTopRelative_lt_laneCount k K hl.k_le_K)
    · exact intervalScratch_mem_allWires r (intervalCarry_mem_scratch r k K target hl)
    · exact intervalScratch_mem_allWires r (intervalCellScratch_mem_scratch r k K target hl)
    · exact intervalScratch_mem_allWires r (intervalCellScratch_mem_scratch r k K target hl)
    · intro w hw; exact intervalScratch_mem_allWires r (List.mem_of_mem_take hw)
    · simp [IntervalRegisters.allWires]
    · simp [IntervalRegisters.allWires]
  · exact List.nil_subset _

theorem intervalTopSecondProgram_support (n start : Nat) (r : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (target : IntervalTarget) (hl : IntervalLayout r k K target) :
    straightWires (intervalTopSecondProgram n start r k K mode target).2 ⊆ r.allWires := by
  unfold intervalTopSecondProgram
  rw [compiledIf_support]
  split
  · apply topSecondProgram_support
    · intro w hw; simp [IntervalRegisters.allWires,hw]
    · intro w hw; simp [IntervalRegisters.allWires,hw]
    · exact intervalScratch_mem_allWires r (intervalAccumulator_mem_scratch r k K target hl)
    · exact intervalTargetAt_mem_allWires r k K _ target hl (intervalTopRelative_lt_laneCount k K hl.k_le_K)
    · exact intervalAddendAt_mem_allWires r k K _ target hl (intervalTopRelative_lt_laneCount k K hl.k_le_K)
    · exact intervalScratch_mem_allWires r (intervalCarry_mem_scratch r k K target hl)
    · exact intervalScratch_mem_allWires r (intervalCellScratch_mem_scratch r k K target hl)
    · exact intervalScratch_mem_allWires r (intervalCellScratch_mem_scratch r k K target hl)
    · intro w hw; exact intervalScratch_mem_allWires r (List.mem_of_mem_take hw)
    · simp [IntervalRegisters.allWires]
    · simp [IntervalRegisters.allWires]
  · exact List.nil_subset _

theorem intervalTraversalFirstProgram_support (n start : Nat) (r : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (target : IntervalTarget) (hl : IntervalLayout r k K target) :
    straightWires (traversalFirstProgram n start mode (intervalHasTopSpecial k K)
      (r.rightTop k K) (r.leftTop k K) (r.accumulator k K) (r.carry k K)
      (r.cellScratch k K) (r.targetAt target) (r.addendAt target) (intervalTree r k K)
      r.control r.control (r.rightPaths k K) (r.leftPaths k K)).2 ⊆ r.allWires := by
  have hd := intervalDecoder_mem_allWires r k K target hl
  apply traversalFirstProgram_support
  · exact intervalRightTop_mem_allWires r k K target hl
  · exact intervalLeftTop_mem_allWires r k K target hl
  · exact intervalScratch_mem_allWires r (intervalAccumulator_mem_scratch r k K target hl)
  · exact intervalScratch_mem_allWires r (intervalCarry_mem_scratch r k K target hl)
  · exact intervalScratch_mem_allWires r (intervalCellScratch_mem_scratch r k K target hl)
  · intro l hlab; exact intervalTargetAt_mem_allWires r k K l target hl (intervalTree_label_lt_laneCount r k K l hlab)
  · intro l hlab; exact intervalAddendAt_mem_allWires r k K l target hl (intervalTree_label_lt_laneCount r k K l hlab)
  · intro w hw; exact hd w (by simp [DualUnaryActionTree.decoderWires,hw])
  · intro w hw; exact hd w (by simp [DualUnaryActionTree.decoderWires,hw])
  · simp [IntervalRegisters.allWires]
  · simp [IntervalRegisters.allWires]
  · intro w hw; exact hd w (by simp [DualUnaryActionTree.decoderWires,hw])
  · intro w hw; exact hd w (by simp [DualUnaryActionTree.decoderWires,hw])

theorem intervalTraversalSecondProgram_support (n start : Nat) (r : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (target : IntervalTarget) (hl : IntervalLayout r k K target) :
    straightWires (traversalSecondProgram n start mode (intervalHasTopSpecial k K)
      (r.rightTop k K) (r.leftTop k K) (r.accumulator k K) (r.carry k K)
      (r.cellScratch k K) (r.targetAt target) (r.addendAt target) (intervalTree r k K)
      r.control r.control (r.rightPaths k K) (r.leftPaths k K)).2 ⊆ r.allWires := by
  have hd := intervalDecoder_mem_allWires r k K target hl
  apply traversalSecondProgram_support
  · exact intervalRightTop_mem_allWires r k K target hl
  · exact intervalLeftTop_mem_allWires r k K target hl
  · exact intervalScratch_mem_allWires r (intervalAccumulator_mem_scratch r k K target hl)
  · exact intervalScratch_mem_allWires r (intervalCarry_mem_scratch r k K target hl)
  · exact intervalScratch_mem_allWires r (intervalCellScratch_mem_scratch r k K target hl)
  · intro l hlab; exact intervalTargetAt_mem_allWires r k K l target hl (intervalTree_label_lt_laneCount r k K l hlab)
  · intro l hlab; exact intervalAddendAt_mem_allWires r k K l target hl (intervalTree_label_lt_laneCount r k K l hlab)
  · intro w hw; exact hd w (by simp [DualUnaryActionTree.decoderWires,hw])
  · intro w hw; exact hd w (by simp [DualUnaryActionTree.decoderWires,hw])
  · simp [IntervalRegisters.allWires]
  · simp [IntervalRegisters.allWires]
  · intro w hw; exact hd w (by simp [DualUnaryActionTree.decoderWires,hw])
  · intro w hw; exact hd w (by simp [DualUnaryActionTree.decoderWires,hw])


theorem intervalProgram_support_layout (n start : Nat) (r : IntervalRegisters) (width k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget)
    (hl : IntervalLayout r k K target) :
    straightWires (intervalProgram n start r width k K mode signUpdate target).2 ⊆ r.allWires := by
  have he := intervalEndpointSupport_mem_allWires r k K target hl
  have hprep := (circuitWires_subset_of_usesOnly (prepareIntervalEndpoints_usesOnly r.lengthT r.lengthQ r.lengthS r.endpointScratch (r.carry k K) width k)).trans (fun _ h => he _ h)
  have hrest := (circuitWires_subset_of_usesOnly (restoreIntervalEndpoints_usesOnly r.lengthT r.lengthQ r.lengthS r.endpointScratch (r.carry k K) width k)).trans (fun _ h => he _ h)
  have ht1 cursor := intervalTopFirstProgram_support n cursor r k K mode target hl
  have ht2 cursor := intervalTopSecondProgram_support n cursor r k K mode target hl
  have hp1 cursor := intervalTraversalFirstProgram_support n cursor r k K mode target hl
  have hp2 cursor := intervalTraversalSecondProgram_support n cursor r k K mode target hl
  have hcarry := intervalScratch_mem_allWires r (intervalCarry_mem_scratch r k K target hl)
  have hsign : r.sign ∈ r.allWires := by simp [IntervalRegisters.allWires]
  have hsgn : circuitWires (intervalSignUpdate r k K signUpdate) ⊆ r.allWires := by
    cases signUpdate <;> simp [intervalSignUpdate,circuitWires,gateWires,hcarry,hsign]
  simp only [intervalProgram,prependCompiled_support,appendCompiled_support,literalProgram_support,List.append_subset]
  exact ⟨hprep,ht1 _,hp1 _,hsgn,hp2 _,ht2 _,hrest⟩

theorem intervalInverseProgram_support_layout (n start : Nat) (r : IntervalRegisters) (width k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget)
    (hl : IntervalLayout r k K target) :
    straightWires (intervalInverseProgram n start r width k K mode signUpdate target).2 ⊆ r.allWires := by
  exact intervalProgram_support_layout n start r width k K mode.inverse signUpdate target hl
end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/LengthSupport ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/LengthSupport.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

theorem zeroCellProgram_support (n start : Nat) (base : Bool) (r bit guard target temporary : Wire)
    (support : List Wire) (hr : r ∈ support) (hb : bit ∈ support)
    (hg : guard ∈ support) (ht : target ∈ support) (hm : temporary ∈ support) :
    straightWires (zeroCellProgram n start base r bit guard target temporary).2 ⊆ support := by
  simp only [zeroCellProgram,prependCompiled_support,List.append_subset]
  constructor
  · cases base <;> simp [measuredZeroPrefix,circuitWires,gateWires,hr,hb,hg,ht,hm]
  · exact andEraseProgram_support n start r bit temporary support hr hb hm

attribute [local irreducible] zeroCellProgram

theorem upperForwardLeafProgram_support (n start k K : Nat) (control temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire) (support : List Wire)
    (hr : r ∈ support) (ht : temporary ∈ support)
    (hc : control ∈ support)
    (hb : ∀ i, bitAt i ∈ support) (hd : ∀ i, dirtyAt i ∈ support) :
    straightWires (upperForwardLeafProgram n start k K control temporary bitAt dirtyAt label r).2 ⊆ support := by
  unfold upperForwardLeafProgram
  rw [compiledIf_support]
  split
  · rw [compiledIf_support]
    split <;> exact zeroCellProgram_support _ _ _ _ _ _ _ _ support hr (hb _) (by first | exact hc | exact hd _) (hd _) ht
  · simp [straightWires]

theorem upperReverseLeafProgram_support (n start k K : Nat) (temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire) (support : List Wire)
    (hr : r ∈ support) (ht : temporary ∈ support)
    (hb : ∀ i, bitAt i ∈ support) (hd : ∀ i, dirtyAt i ∈ support) :
    straightWires (upperReverseLeafProgram n start k K temporary bitAt dirtyAt label r).2 ⊆ support := by
  unfold upperReverseLeafProgram
  rw [compiledIf_support]
  split
  · exact zeroCellProgram_support _ _ _ _ _ _ _ _ support hr (hb _) (hd _) (hd _) ht
  · simp [straightWires]

theorem lowerForwardLeafProgram_support (n start k K : Nat) (control temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire) (support : List Wire)
    (hr : r ∈ support) (ht : temporary ∈ support)
    (hc : control ∈ support)
    (hb : ∀ i, bitAt i ∈ support) (hd : ∀ i, dirtyAt i ∈ support) :
    straightWires (lowerForwardLeafProgram n start k K control temporary bitAt dirtyAt label r).2 ⊆ support := by
  unfold lowerForwardLeafProgram
  rw [compiledIf_support]
  split
  · rw [compiledIf_support]
    split <;> exact zeroCellProgram_support _ _ _ _ _ _ _ _ support hr (hb _) (by first | exact hc | exact hd _) (hd _) ht
  · simp [straightWires]

theorem lowerReverseLeafProgram_support (n start k K : Nat) (temporary : Wire)
    (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire) (support : List Wire)
    (hr : r ∈ support) (ht : temporary ∈ support)
    (hb : ∀ i, bitAt i ∈ support) (hd : ∀ i, dirtyAt i ∈ support) :
    straightWires (lowerReverseLeafProgram n start k K temporary bitAt dirtyAt label r).2 ⊆ support := by
  unfold lowerReverseLeafProgram
  rw [compiledIf_support]
  split
  · exact zeroCellProgram_support _ _ _ _ _ _ _ _ support hr (hb _) (hd _) (hd _) ht
  · simp [straightWires]

theorem rangeLeafProgram_support (n : Nat) (after : Bool) (r : Wire)
    (leaf : Nat → Wire → FixedSegment n) (label : Nat) (dynamic : Wire) (start : Nat)
    (support : List Wire) (hr : r ∈ support) (hd : dynamic ∈ support)
    (hl : straightWires (leaf label r start).2 ⊆ support) :
    straightWires (rangeLeafProgram n after r leaf label dynamic start).2 ⊆ support := by
  unfold rangeLeafProgram
  rw [compiledIf_support]
  cases after <;> simp only [Bool.false_eq_true,ite_false,ite_true,prependCompiled_support,appendCompiled_support,
    literalProgram_support,List.append_subset]
  · exact ⟨by simp [circuitWires,gateWires,hr,hd],hl⟩
  · exact ⟨hl,by simp [circuitWires,gateWires,hr,hd]⟩

theorem rangeScanProgram_support (n : Nat) (after : Bool) (order : UnaryOrder)
    (tree : UnaryActionTree) (control r : Wire) (path : List Wire)
    (leaf : Nat → Wire → FixedSegment n) (start : Nat) (support : List Wire)
    (hl : ∀ label ∈ tree.labels, ∀ cursor,
      straightWires (leaf label r cursor).2 ⊆ support)
    (hi : tree.indexWires ⊆ support) (hc : control ∈ support)
    (hr : r ∈ support) (hp : path ⊆ support) :
    straightWires (rangeScanProgram n after order tree control r path leaf start).2 ⊆ support := by
  have hu (a : Bool) := unaryProgram_support n order (rangeLeafProgram n a r leaf)
    tree control path start support
    (fun label hlabel dynamic cursor hd => rangeLeafProgram_support n a r leaf label dynamic cursor support hr hd (hl label hlabel cursor)) hi hc hp
  unfold rangeScanProgram
  rw [compiledIf_support]
  cases after <;> simp only [Bool.false_eq_true,ite_false,ite_true,prependCompiled_support,appendCompiled_support,
    literalProgram_support,List.append_subset]
  · exact ⟨hu false,by simp [circuitWires,gateWires,hc,hr]⟩
  · exact ⟨by simp [circuitWires,gateWires,hc,hr],hu true⟩


theorem upperMapProgram_support (n k K : Nat) (tree : UnaryActionTree)
    (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (start : Nat)
    (support : List Wire) (hi : tree.indexWires ⊆ support) (hc : control ∈ support)
    (hr : r ∈ support) (ht : t ∈ support) (hp : path ⊆ support)
    (hb : ∀ i, bitAt i ∈ support) (hd : ∀ i, dirtyAt i ∈ support) :
    straightWires (upperMapProgram n k K tree control r t path bitAt dirtyAt start).2 ⊆ support := by
  unfold upperMapProgram
  rw [appendCompiled_support,List.append_subset]
  constructor
  · apply rangeScanProgram_support _ _ _ _ _ _ _ _ _ support
    · intro label _ cursor
      exact upperForwardLeafProgram_support n cursor k K control t bitAt dirtyAt label r support hr ht hc hb hd
    · exact hi
    · exact hc
    · exact hr
    · exact hp
  · apply rangeScanProgram_support _ _ _ _ _ _ _ _ _ support
    · intro label _ cursor
      exact upperReverseLeafProgram_support n cursor k K t bitAt dirtyAt label r support hr ht hb hd
    · exact hi
    · exact hc
    · exact hr
    · exact hp

theorem lowerMapProgram_support (n k K : Nat) (tree : UnaryActionTree)
    (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (start : Nat)
    (support : List Wire) (hi : tree.indexWires ⊆ support) (hc : control ∈ support)
    (hr : r ∈ support) (ht : t ∈ support) (hp : path ⊆ support)
    (hb : ∀ i, bitAt i ∈ support) (hd : ∀ i, dirtyAt i ∈ support) :
    straightWires (lowerMapProgram n k K tree control r t path bitAt dirtyAt start).2 ⊆ support := by
  unfold lowerMapProgram
  rw [appendCompiled_support,List.append_subset]
  constructor
  · apply rangeScanProgram_support _ _ _ _ _ _ _ _ _ support
    · intro label _ cursor
      exact lowerForwardLeafProgram_support n cursor k K control t bitAt dirtyAt label r support hr ht hc hb hd
    · exact hi
    · exact hc
    · exact hr
    · exact hp
  · apply rangeScanProgram_support _ _ _ _ _ _ _ _ _ support
    · intro label _ cursor
      exact lowerReverseLeafProgram_support n cursor k K t bitAt dirtyAt label r support hr ht hb hd
    · exact hi
    · exact hc
    · exact hr
    · exact hp


theorem upperWriterProgram_support (n k K : Nat) (tree : UnaryActionTree)
    (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (targets : List Wire) (start : Nat)
    (support : List Wire) (hi : tree.indexWires ⊆ support) (hc : control ∈ support)
    (hr : r ∈ support) (ht : t ∈ support) (hp : path ⊆ support)
    (hb : ∀ i, bitAt i ∈ support) (hd : ∀ i, dirtyAt i ∈ support)
    (hx : targets ⊆ support) :
    straightWires (upperWriterProgram n k K tree control r t path bitAt dirtyAt targets start).2 ⊆ support := by
  have hseed := circuitWires_subset_of_usesOnly ((controlledXorConstant_usesOnly control targets (truthMinusOneValue targets.length K)).mono
    (by
      intro wire hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact hc
      · exact hx hw))
  have hwrites : circuitWires (highestPositionDirtyWrites k K targets dirtyAt) ⊆ support := by
    unfold highestPositionDirtyWrites
    apply circuitWires_subset_of_usesOnly
    apply (dirtyConstantWrites_usesOnly targets dirtyAt _ _).mono
    intro wire hw
    simp only [dirtyConstantWritesSupport,List.mem_append,List.mem_map] at hw
    rcases hw with hw | ⟨i,_,rfl⟩
    · exact hx hw
    · exact hd i
  have hm cursor := upperMapProgram_support n k K tree control r t path bitAt dirtyAt cursor support hi hc hr ht hp hb hd
  unfold upperWriterProgram
  simp only [prependCompiled_support,appendCompiled_support,circuitWires,List.flatMap_append,List.append_subset] at hseed hwrites ⊢
  exact ⟨⟨hseed,hwrites⟩,hm _,hwrites,hm _⟩

theorem lowerWriterProgram_support (n width k K : Nat) (tree : UnaryActionTree)
    (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (targets : List Wire) (start : Nat)
    (support : List Wire) (hi : tree.indexWires ⊆ support) (hc : control ∈ support)
    (hr : r ∈ support) (ht : t ∈ support) (hp : path ⊆ support)
    (hb : ∀ i, bitAt i ∈ support) (hd : ∀ i, dirtyAt i ∈ support)
    (hx : targets ⊆ support) :
    straightWires (lowerWriterProgram n width k K tree control r t path bitAt dirtyAt targets start).2 ⊆ support := by
  have hseed := circuitWires_subset_of_usesOnly ((controlledXorConstant_usesOnly control targets (rightLengthValue width targets.length k)).mono
    (by
      intro wire hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact hc
      · exact hx hw))
  have hwrites : circuitWires (rightLengthDirtyWrites width k K targets dirtyAt) ⊆ support := by
    unfold rightLengthDirtyWrites
    apply circuitWires_subset_of_usesOnly
    apply (dirtyConstantWrites_usesOnly targets dirtyAt _ _).mono
    intro wire hw
    simp only [dirtyConstantWritesSupport,List.mem_append,List.mem_map] at hw
    rcases hw with hw | ⟨i,_,rfl⟩
    · exact hx hw
    · exact hd i
  have hm cursor := lowerMapProgram_support n k K tree control r t path bitAt dirtyAt cursor support hi hc hr ht hp hb hd
  unfold lowerWriterProgram
  simp only [prependCompiled_support,appendCompiled_support,circuitWires,List.flatMap_append,List.append_subset] at hseed hwrites ⊢
  exact ⟨⟨hseed,hwrites⟩,hm _,hwrites,hm _⟩


theorem ltUpdateProgram_support (n width k K : Nat) (tree : UnaryActionTree)
    (control r t carry : Wire) (path : List Wire) (work1At work2At : Nat → Wire)
    (lengthT lengthRP constants : List Wire) (start : Nat) (support : List Wire)
    (hi : tree.indexWires ⊆ support) (hc : control ∈ support) (hr : r ∈ support)
    (ht : t ∈ support) (hcarry : carry ∈ support) (hp : path ⊆ support)
    (h1 : ∀ i, work1At i ∈ support) (h2 : ∀ i, work2At i ∈ support)
    (hx : lengthT ⊆ support) (hy : lengthRP ⊆ support) (hz : constants ⊆ support) :
    straightWires (ltUpdateProgram n width k K tree control r t carry path work1At work2At lengthT lengthRP constants start).2 ⊆ support := by
  have hs : constants ++ lengthRP ++ [carry] ⊆ support := by
    simp only [List.append_subset,List.cons_subset,List.nil_subset,and_true]
    exact ⟨⟨hz,hy⟩,hcarry⟩
  have ha := (circuitWires_subset_of_usesOnly (constMinus_usesOnly lengthRP constants carry (width+2))).trans hs
  have hb := (circuitWires_subset_of_usesOnly (constMinus_usesOnly lengthRP constants carry (width+2))).trans hs
  unfold ltUpdateProgram
  simp only [surroundCompiled_support,appendCompiled_support,List.append_subset]
  refine ⟨⟨ha,?_,?_⟩,hb⟩
  all_goals apply upperWriterProgram_support <;> assumption

theorem lrpUpdateProgram_support (n width k K : Nat) (tree : UnaryActionTree)
    (control r t carry : Wire) (path : List Wire) (work1At work2At : Nat → Wire)
    (lengthT lengthRP constants : List Wire) (start : Nat) (support : List Wire)
    (hi : tree.indexWires ⊆ support) (hc : control ∈ support) (hr : r ∈ support)
    (ht : t ∈ support) (hcarry : carry ∈ support) (hp : path ⊆ support)
    (h1 : ∀ i, work1At i ∈ support) (h2 : ∀ i, work2At i ∈ support)
    (hx : lengthT ⊆ support) (hy : lengthRP ⊆ support) (hz : constants ⊆ support) :
    straightWires (lrpUpdateProgram n width k K tree control r t carry path work1At work2At lengthT lengthRP constants start).2 ⊆ support := by
  have hs : constants ++ lengthT ++ [carry] ⊆ support := by
    simp only [List.append_subset,List.cons_subset,List.nil_subset,and_true]
    exact ⟨⟨hz,hx⟩,hcarry⟩
  have ha := (circuitWires_subset_of_usesOnly (addConstant_usesOnly lengthT constants carry 3)).trans hs
  have hb := (circuitWires_subset_of_usesOnly (subConstant_usesOnly lengthT constants carry 3)).trans hs
  unfold lrpUpdateProgram
  simp only [surroundCompiled_support,appendCompiled_support,List.append_subset]
  refine ⟨⟨ha,?_,?_⟩,hb⟩
  all_goals apply lowerWriterProgram_support <;> assumption
end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/StepSupport ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/StepSupport.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
private theorem support_to_580 (support : List Wire)
    (h : support.all (fun w => decide (w < 580)) = true) :
    ∀ w ∈ support, w ∈ List.range 580 := by
  intro w hw
  exact List.mem_range.mpr (of_decide_eq_true ((List.all_eq_true.mp h) w hw))


private theorem range580_of_closed (ws : List Wire) (h : ws.all (fun w => decide (w < 580)) = true)
    (w : Wire) (hw : w ∈ ws) : w ∈ List.range 580 := support_to_580 ws h w hw


private theorem window_mem {work : List Wire} {window : ActiveWindow} {w : Wire}
    (hw : w ∈ IndexedStepRegisters.windowSlice work window) : w ∈ work :=
  List.mem_of_mem_drop (List.mem_of_mem_take hw)


private theorem production_remainder_support (window : ActiveWindow) :
    ∀ w ∈ (indexedStepProductionRegisters.remainder window).allWires, w ∈ List.range 580 := by
  let r := indexedStepProductionRegisters
  intro w hw
  change w ∈ [r.control,r.sign] ++
    (IndexedStepRegisters.windowSlice r.work1 window ++ (IndexedStepRegisters.windowSlice r.work2 window ++
    (r.lengthT ++ (r.lengthQ ++ (r.lengthS ++
    (r.shiftEpoch :: (r.sourceScratch ++ r.remainderRepairScratch)).take (r.remainderScratchSize window)))))) at hw
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with (hw | hw) | hw | hw | hw | hw | hw | hw
  · subst w; exact List.mem_range.mpr (show (558 : Nat) < 580 by decide)
  · subst w; exact List.mem_range.mpr (show (3 : Nat) < 580 by decide)
  · exact range580_of_closed r.work1 (by decide +kernel) w (window_mem hw)
  · exact range580_of_closed r.work2 (by decide +kernel) w (window_mem hw)
  · exact range580_of_closed r.lengthT (by decide +kernel) w hw
  · exact range580_of_closed r.lengthQ (by decide +kernel) w hw
  · exact range580_of_closed r.lengthS (by decide +kernel) w hw
  · exact range580_of_closed (r.shiftEpoch :: (r.sourceScratch ++ r.remainderRepairScratch))
      (by decide +kernel) w (List.mem_of_mem_take hw)


private theorem gate_support_580 (g : Gate)
    (h : (gateWires g).all (fun w => decide (w < 580)) = true) :
    PaperCircuitUsesOnly (List.range 580) ([g] : Circuit) := by
  intro g' hg
  simp only [List.mem_singleton] at hg
  subst g'
  exact support_to_580 _ h


private theorem production_coefficient_support (window : ActiveWindow) :
    ∀ w ∈ (indexedStepProductionRegisters.coefficient window).allWires, w ∈ List.range 580 := by
  let r := indexedStepProductionRegisters
  intro w hw
  change w ∈ [r.control,r.sign] ++
    (IndexedStepRegisters.windowSlice r.work1 window ++ (IndexedStepRegisters.windowSlice r.work2 window ++
    (r.lengthT ++ r.blockScratch.take (max (quotientSwapUnaryDepth window.start window.stop) r.lengthT.length+3)))) at hw
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with (hw | hw) | hw | hw | hw | hw
  · subst w; exact List.mem_range.mpr (show (558 : Nat) < 580 by decide)
  · subst w; exact List.mem_range.mpr (show (3 : Nat) < 580 by decide)
  · exact range580_of_closed r.work1 (by decide +kernel) w (window_mem hw)
  · exact range580_of_closed r.work2 (by decide +kernel) w (window_mem hw)
  · exact range580_of_closed r.lengthT (by decide +kernel) w hw
  · exact range580_of_closed r.blockScratch (by decide +kernel) w (List.mem_of_mem_take hw)


attribute [local irreducible] intervalProgram rControlNonterminal coefficientProgram

theorem remainderBlockProgram_support_production (n start width : Nat) (w : ActiveWindow)
    (hl : IntervalLayout (indexedStepProductionRegisters.remainder w) w.start w.stop .work1) :
    straightWires (remainderBlockProgram n start indexedStepProductionRegisters width w).2 ⊆ List.range 580 := by
  let r := indexedStepProductionRegisters
  have hs := (rControlNonterminal_usesOnly [r.phase1] 0 r.control r.lengthRPrime
    r.terminal r.blockScratch).mono (support_to_580 _ (by decide +kernel))
  have hp := (rControlNonterminal_usesOnly [r.phase1,r.phase2] 2 r.control r.lengthRPrime
    r.terminal r.blockScratch).mono (support_to_580 _ (by decide +kernel))
  have hr := (rControlNonterminal_usesOnly [r.phase1,r.terminal] 0 r.control r.lengthRPrime
    (r.blockScratch.getD 0 0) (r.blockScratch.drop 1)).mono
    (support_to_580 _ (by decide +kernel))
  have hc := gate_support_580 (.CCX r.phase2 r.sign r.terminal) (by decide +kernel)
  have hx := gate_support_580 (.CX r.control r.sign) (by decide +kernel)
  have hrestore := circuitWires_subset_of_usesOnly ((hc.append hr).append hc)
  have h2 : circuitWires (blockB2 r) ⊆ List.range 580 := by
    exact circuitWires_subset_of_usesOnly ((hp.append hx).append hp)
  have hiSub cursor := (intervalProgram_support_layout n cursor (r.remainder w) width w.start w.stop .sub true .work1 hl).trans
    (fun _ h => production_remainder_support w _ h)
  have hiAdd cursor := (intervalProgram_support_layout n cursor (r.remainder w) width w.start w.stop .add false .work1 hl).trans
    (fun _ h => production_remainder_support w _ h)
  unfold remainderBlockProgram
  apply sequenceProgram_support
  intro seg hseg cursor
  simp only [remainderBlockSegments,List.mem_cons,List.mem_nil_iff,or_false] at hseg
  rcases hseg with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact hiSub _ | exact hiAdd _ | simpa only [literalProgram_support] using circuitWires_subset_of_usesOnly hs | simpa only [literalProgram_support] using h2 | simpa only [literalProgram_support] using hrestore

theorem coefficientBlockProgram_support_production (n start width : Nat) (w : ActiveWindow)
    (hl : CoefficientPrefixLayout (indexedStepProductionRegisters.coefficient w) w.start w.stop) :
    straightWires (coefficientBlockProgram n start indexedStepProductionRegisters width w).2 ⊆ List.range 580 := by
  let r := indexedStepProductionRegisters
  have ht := (computeControl_usesOnly [r.phase2,r.sign] 2 r.terminal r.blockScratch).mono
    (support_to_580 _ (by decide +kernel))
  have hs := (computeControl_usesOnly [r.phase1,r.terminal] 1 r.control r.blockScratch).mono
    (support_to_580 _ (by decide +kernel))
  have ha := (computeControl_usesOnly [r.phase1] 1 r.control r.blockScratch).mono
    (support_to_580 _ (by decide +kernel))
  have hp := (prepareLatestPaperTBoundary_usesOnly r.tBoundary width).mono
    (support_to_580 _ (by decide +kernel))
  have hr := (restoreLatestPaperTBoundary_usesOnly r.tBoundary width).mono
    (support_to_580 _ (by decide +kernel))
  have hx := gate_support_580 (.CX r.phase1 r.sign) (by decide +kernel)
  have hfirst := circuitWires_subset_of_usesOnly (((ht.append hs).append ht).append hp)
  have hmiddle := circuitWires_subset_of_usesOnly ((((ht.append hs).append ht).append hx).append ha)
  have hlast := circuitWires_subset_of_usesOnly (ha.append hr)
  have hiSub cursor := (coefficientProgram_support_layout n cursor (r.coefficient w) w.start w.stop .sub false .work2 hl).trans
    (fun _ h => production_coefficient_support w _ h)
  have hiAdd cursor := (coefficientProgram_support_layout n cursor (r.coefficient w) w.start w.stop .add true .work2 hl).trans
    (fun _ h => production_coefficient_support w _ h)
  unfold coefficientBlockProgram
  apply sequenceProgram_support
  intro seg hseg cursor
  simp only [coefficientBlockSegments,List.mem_cons,List.mem_nil_iff,or_false] at hseg
  rcases hseg with rfl|rfl|rfl|rfl|rfl
  all_goals first | exact hiSub _ | exact hiAdd _ | simpa only [literalProgram_support] using hfirst | simpa only [literalProgram_support] using hmiddle | simpa only [literalProgram_support] using hlast

attribute [local irreducible] remainderBlockProgram coefficientBlockProgram phaseProgram
  blockAForward blockBForward blockCForward blockDForward blockEForward blockFForward blockGForward blockHForward

theorem indexedStepProgram_support_production (n start T : Nat)
    (hl : IndexedStepLayout indexedStepProductionRegisters 256 T) :
    straightWires (indexedStepProgram n start indexedStepProductionRegisters 256 T).2 ⊆ List.range 580 := by
  have hs := circuitWires_subset_of_usesOnly (indexedStepUnitary_production_usesOnly T hl)
  simp only [indexedStepUnitary,circuitWires,List.flatMap_append,List.append_subset] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨hA,hB⟩,hC⟩,hD⟩,hE⟩,hF⟩,hG⟩,hH⟩ := hs
  have hCD : circuitWires (blockCForward indexedStepProductionRegisters ++ blockDForward indexedStepProductionRegisters (certifiedActiveWindows 256 T).quotientSwap) ⊆ List.range 580 := by
    simp only [circuitWires,List.flatMap_append,List.append_subset]
    exact ⟨hC,hD⟩
  have hrem cursor := remainderBlockProgram_support_production n cursor 256 _ hl.remainder
  have hcoef cursor := coefficientBlockProgram_support_production n cursor 256 _ hl.coefficient
  have hphase cursor := (phaseProgram_support n cursor indexedStepProductionRegisters.phaseUpdate indexedStepProductionRegisters.shiftEpoch).trans
    (support_to_580 _ (by decide +kernel))
  unfold indexedStepProgram
  apply sequenceProgram_support
  intro seg hseg cursor
  simp only [indexedStepSegments,List.mem_cons,List.mem_nil_iff,or_false] at hseg
  rcases hseg with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · simpa only [literalProgram_support,circuitWires] using hA
  · exact hrem _
  · simpa only [literalProgram_support] using hCD
  · exact hcoef _
  · simpa only [literalProgram_support,circuitWires] using hF
  · exact hphase _
  · simpa only [literalProgram_support,circuitWires] using hH
end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/EndpointSupport ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/EndpointSupport.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
private theorem getD_support_EndpointSupport (ws : List Wire) (i : Nat)
    (hws : ∀ w ∈ ws, w ∈ List.range 580) : ws.getD i 0 ∈ List.range 580 := by
  by_cases hi : i < ws.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact hws _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact List.mem_range.mpr (by decide)

private theorem endpoint_width {k K : Nat} (hK : K ≤ 259) :
    DualUnaryActionTree.sourceWidth (quotientSwapLabels k K).toFinset ≤ 9 := by
  apply DualUnaryActionTree.sourceWidth_le _ 9 (by decide)
  intro label hlabel
  have hmem : label ∈ quotientSwapLabels k K := by simpa using hlabel
  simp only [quotientSwapLabels, List.mem_range'_1] at hmem
  norm_num
  omega

theorem endPrograms_support_production (n start T : Nat)
    (hlayout : EndIterationLayout (indexedStepProductionRegisters.endIteration 256 T) 256
      (endIterationWindowsAt 256 T)) :
    straightWires (endProgram n start (indexedStepProductionRegisters.endIteration 256 T) 256 (endIterationWindowsAt 256 T)).2 ⊆ List.range 580 ∧
    straightWires (endInverseProgram n start (indexedStepProductionRegisters.endIteration 256 T) 256 (endIterationWindowsAt 256 T)).2 ⊆ List.range 580 := by
  let r := indexedStepProductionRegisters.endIteration 256 T
  let windows := endIterationWindowsAt 256 T
  have hc : r.control ∈ List.range 580 := List.mem_range.mpr (show (558 : Nat) < 580 by decide)
  have h1 : ∀ w ∈ r.work1, w ∈ List.range 580 := support_to_580 indexedStepProductionRegisters.work1 (by decide +kernel)
  have h2 : ∀ w ∈ r.work2, w ∈ List.range 580 := support_to_580 indexedStepProductionRegisters.work2 (by decide +kernel)
  have hT : ∀ w ∈ r.lengthT, w ∈ List.range 580 := support_to_580 indexedStepProductionRegisters.lengthT (by decide +kernel)
  have hRP : ∀ w ∈ r.lengthRP, w ∈ List.range 580 := support_to_580 indexedStepProductionRegisters.lengthRPrime (by decide +kernel)
  have hs : ∀ w ∈ r.scratch, w ∈ List.range 580 := by
    intro w hw
    exact support_to_580 (indexedStepProductionRegisters.sourceScratch.drop 2)
      (by decide +kernel) w (List.mem_of_mem_take hw)
  have hpath : ∀ k K w, w ∈ r.path k K → w ∈ List.range 580 := by
    intro k K w hw; exact hs w (List.mem_of_mem_take hw)
  have hconst : ∀ w ∈ r.constants, w ∈ List.range 580 := by
    intro w hw; exact hs w (List.mem_of_mem_take hw)
  have huIndex : ∀ w ∈ (r.upperTree windows).indexWires, w ∈ List.range 580 := by
    let q : QuotientSwapRegisters := ⟨0,0,[],[],r.lengthRP,[]⟩
    intro w hw
    exact hRP w (quotientSwapTree_indexWires_mem_lengthQ q hlayout.k4_le_K4
      (endpoint_width hlayout.K4_le_work) w hw)
  have hlIndex : ∀ w ∈ (r.lowerTree 256 windows).indexWires, w ∈ List.range 580 := by
    let q : QuotientSwapRegisters := ⟨0,0,[],[],r.lengthT,[]⟩
    intro w hw
    exact hT w (quotientSwapTree_indexWires_mem_lengthQ q hlayout.k5_le_decode
      (endpoint_width (Nat.min_le_right _ _)) w hw)
  have hu cursor := ltUpdateProgram_support n 256 windows.k4 windows.K4 (r.upperTree windows) r.control
    (r.rangeAccumulator windows.k4 windows.K4) (r.temporary windows.k4 windows.K4) r.carry
    (r.path windows.k4 windows.K4) r.work1At r.work2At r.lengthT r.lengthRP r.constants cursor (List.range 580)
    (fun _ h => huIndex _ h) hc (getD_support_EndpointSupport _ _ hs) (getD_support_EndpointSupport _ _ hs) (getD_support_EndpointSupport _ _ hs)
    (fun _ h => hpath _ _ _ h) (fun _ => getD_support_EndpointSupport _ _ h1) (fun _ => getD_support_EndpointSupport _ _ h2)
    (fun _ h => hT _ h) (fun _ h => hRP _ h) (fun _ h => hconst _ h)
  have hl cursor := lrpUpdateProgram_support n 256 windows.k5 (windows.K5Decode 256) (r.lowerTree 256 windows) r.control
    (r.rangeAccumulator windows.k5 (windows.K5Decode 256)) (r.temporary windows.k5 (windows.K5Decode 256)) r.carry
    (r.path windows.k5 (windows.K5Decode 256)) r.work1At r.work2At r.lengthT r.lengthRP r.constants cursor (List.range 580)
    (fun _ h => hlIndex _ h) hc (getD_support_EndpointSupport _ _ hs) (getD_support_EndpointSupport _ _ hs) (getD_support_EndpointSupport _ _ hs)
    (fun _ h => hpath _ _ _ h) (fun _ => getD_support_EndpointSupport _ _ h1) (fun _ => getD_support_EndpointSupport _ _ h2)
    (fun _ h => hT _ h) (fun _ h => hRP _ h) (fun _ h => hconst _ h)
  have hws : r.control :: r.work1 ++ r.work2 ⊆ List.range 580 := by
    simp only [List.append_subset,List.cons_subset]
    exact ⟨⟨hc,fun _ h => h1 _ h⟩,fun _ h => h2 _ h⟩
  have hf := (circuitWires_subset_of_usesOnly (controlledWorkSwap_usesOnly r.control r.work1 r.work2)).trans hws
  have hb := (circuitWires_subset_of_usesOnly (controlledWorkSwapInverse_usesOnly r.control r.work1 r.work2)).trans hws
  constructor
  · simp only [endProgram,prependCompiled_support,appendCompiled_support,List.append_subset]
    exact ⟨hf,hu _,hl _⟩
  · simp only [endInverseProgram,appendCompiled_support,literalProgram_support,List.append_subset]
    exact ⟨hl _,hu _,hb⟩


private theorem production_h_literals :
    circuitWires (blockHPrefix indexedStepProductionRegisters) ⊆ List.range 580 ∧
    circuitWires (blockHSuffix indexedStepProductionRegisters) ⊆ List.range 580 := by
  let r := indexedStepProductionRegisters
  have hq := (mcxVChain_usesOnly r.lengthQ (r.sourceScratch.getD 0 0)
    (r.sourceScratch.drop 2)).mono (support_to_580 _ (by decide +kernel))
  have hs := (mcxVChain_usesOnly (r.lengthS ++ [r.shiftEpoch]) (r.sourceScratch.getD 1 0)
    (r.sourceScratch.drop 2)).mono (support_to_580 _ (by decide +kernel))
  have hx : PaperCircuitUsesOnly (List.range 580) ([.X r.shiftEpoch] : Circuit) := by
    intro g hg w hw
    simp only [List.mem_singleton] at hg
    subst g
    exact support_to_580 _ (by decide +kernel) w hw
  have hc : PaperCircuitUsesOnly (List.range 580)
      ([.CCX (r.sourceScratch.getD 0 0) (r.sourceScratch.getD 1 0) r.control] : Circuit) := by
    intro g hg w hw
    simp only [List.mem_singleton] at hg
    subst g
    exact support_to_580 _ (by decide +kernel) w hw
  constructor
  · exact circuitWires_subset_of_usesOnly ((((hq.append hx).append hs).append hx).append hc)
  · exact circuitWires_subset_of_usesOnly ((((hc.append hx).append hs).append hx).append hq)

theorem hPrograms_support_production (n start T : Nat)
    (hl : T%4=0 → EndIterationLayout (indexedStepProductionRegisters.endIteration 256 T) 256
      (endIterationWindowsAt 256 T)) :
    straightWires (hProgram n start indexedStepProductionRegisters 256 T).2 ⊆ List.range 580 ∧
    straightWires (hInverseProgram n start indexedStepProductionRegisters 256 T).2 ⊆ List.range 580 := by
  have hx : circuitWires ([.CX indexedStepProductionRegisters.control indexedStepProductionRegisters.iter] : Circuit) ⊆ List.range 580 := by
    intro w hw
    exact support_to_580 _ (by decide +kernel) w hw
  unfold hProgram hInverseProgram
  rw [compiledIf_support,compiledIf_support]
  by_cases h : T%4=0
  · simp only [h,ite_true,surroundCompiled_support,circuitWires,List.flatMap_append,List.append_subset]
    obtain ⟨hf,hb⟩ := production_h_literals
    obtain ⟨he,hi⟩ := endPrograms_support_production n start T (hl h)
    exact ⟨⟨⟨hf,he⟩,hx,hb⟩,⟨⟨hf,hx⟩,hi⟩,hb⟩
  · simp [h,straightWires]

attribute [local irreducible] remainderBlockProgram coefficientBlockProgram phaseProgram
  blockAForward blockBForward blockCForward blockDForward blockEForward blockFForward blockGForward blockHForward

theorem measuredStepProgram_support_production (n start T : Nat)
    (hl : IndexedStepLayout indexedStepProductionRegisters 256 T) :
    straightWires (measuredStepProgram n start indexedStepProductionRegisters 256 T).2 ⊆ List.range 580 := by
  have hs := circuitWires_subset_of_usesOnly (indexedStepUnitary_production_usesOnly T hl)
  simp only [indexedStepUnitary,circuitWires,List.flatMap_append,List.append_subset] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨hA,hB⟩,hC⟩,hD⟩,hE⟩,hF⟩,hG⟩,hH⟩ := hs
  have hCD : circuitWires (blockCForward indexedStepProductionRegisters ++ blockDForward indexedStepProductionRegisters (certifiedActiveWindows 256 T).quotientSwap) ⊆ List.range 580 := by
    simp only [circuitWires,List.flatMap_append,List.append_subset]
    exact ⟨hC,hD⟩
  have hrem cursor := remainderBlockProgram_support_production n cursor 256 _ hl.remainder
  have hcoef cursor := coefficientBlockProgram_support_production n cursor 256 _ hl.coefficient
  have hphase cursor := (phaseProgram_support n cursor indexedStepProductionRegisters.phaseUpdate indexedStepProductionRegisters.shiftEpoch).trans
    (support_to_580 _ (by decide +kernel))
  unfold measuredStepProgram
  apply sequenceProgram_support
  intro seg hseg cursor
  simp only [measuredStepSegments,List.mem_cons,List.mem_nil_iff,or_false] at hseg
  rcases hseg with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · simpa only [literalProgram_support,circuitWires] using hA
  · exact hrem _
  · simpa only [literalProgram_support] using hCD
  · exact hcoef _
  · simpa only [literalProgram_support,circuitWires] using hF
  · exact hphase _
  · exact (hPrograms_support_production n _ T hl.endIteration).1
end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/WrapperSupport ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/WrapperSupport.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge













attribute [local irreducible] coefficientInverseProgram intervalInverseProgram phaseInverseProgram hInverseProgram
  blockAInverse blockCInverse blockDInverse blockFForward

theorem measuredInverseStepProgram_support_production (n start T : Nat)
    (hl : IndexedStepLayout indexedStepProductionRegisters 256 T) :
    straightWires (measuredInverseStepProgram n start indexedStepProductionRegisters T).2 ⊆ List.range 580 := by
  let r := indexedStepProductionRegisters
  have hs := circuitWires_subset_of_usesOnly (indexedStepInverseUnitary_production_usesOnly T hl)
  simp only [indexedStepInverseUnitary,circuitWires,List.flatMap_append,List.append_subset] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨hH,hG⟩,hF⟩,hE⟩,hD⟩,hC⟩,hB⟩,hA⟩ := hs
  have hsf := circuitWires_subset_of_usesOnly (indexedStepUnitary_production_usesOnly T hl)
  simp only [indexedStepUnitary,circuitWires,List.flatMap_append,List.append_subset] at hsf
  have hforwardF : PaperCircuitUsesOnly (List.range 580) (blockFForward r) := by
    intro g hg w hw
    exact hsf.1.1.2 (List.mem_flatMap.mpr ⟨g,hg,hw⟩)
  have hFadj := circuitWires_subset_of_usesOnly hforwardF.adjoint
  have hcAdd := circuitWires_subset_of_usesOnly ((computeControl_usesOnly [r.phase1] 1 r.control r.blockScratch).mono (support_to_580 _ (by decide +kernel)))
  have hcSub := circuitWires_subset_of_usesOnly ((computeControl_usesOnly [r.phase1,r.terminal] 1 r.control r.blockScratch).mono (support_to_580 _ (by decide +kernel)))
  have hcTmp := circuitWires_subset_of_usesOnly ((computeControl_usesOnly [r.phase2,r.sign] 2 r.terminal r.blockScratch).mono (support_to_580 _ (by decide +kernel)))
  have hprep := circuitWires_subset_of_usesOnly ((prepareLatestPaperTBoundary_usesOnly r.tBoundary 256).mono (support_to_580 _ (by decide +kernel)))
  have hrest := circuitWires_subset_of_usesOnly ((restoreLatestPaperTBoundary_usesOnly r.tBoundary 256).mono (support_to_580 _ (by decide +kernel)))
  have hx := circuitWires_subset_of_usesOnly (gate_support_580 (.CX r.phase1 r.sign) (by decide +kernel))
  have hterm := circuitWires_subset_of_usesOnly (gate_support_580 (.CCX r.phase2 r.sign r.terminal) (by decide +kernel))
  have hrst := circuitWires_subset_of_usesOnly ((rControlNonterminal_usesOnly [r.phase1,r.terminal] 0 r.control r.lengthRPrime (r.blockScratch.getD 0 0) (r.blockScratch.drop 1)).mono (support_to_580 _ (by decide +kernel)))
  have hrsub := circuitWires_subset_of_usesOnly ((rControlNonterminal_usesOnly [r.phase1] 0 r.control r.lengthRPrime r.terminal r.blockScratch).mono (support_to_580 _ (by decide +kernel)))
  have hrc := (rControlNonterminal_usesOnly [r.phase1,r.phase2] 2 r.control r.lengthRPrime r.terminal r.blockScratch).mono (support_to_580 _ (by decide +kernel))
  have hrx := gate_support_580 (.CX r.control r.sign) (by decide +kernel)
  have hB2 : circuitWires (blockB2 r) ⊆ List.range 580 := circuitWires_subset_of_usesOnly ((hrc.append hrx).append hrc)
  have hci mode phase cursor := (coefficientInverseProgram_support_layout n cursor (r.coefficient (certifiedActiveWindows 256 T).coefficient) _ _ mode phase .work2 hl.coefficient).trans (fun _ h => production_coefficient_support _ _ h)
  have hii mode phase cursor := (intervalInverseProgram_support_layout n cursor (r.remainder (certifiedActiveWindows 256 T).remainder) 256 _ _ mode phase .work1 hl.remainder).trans (fun _ h => production_remainder_support _ _ h)
  have hphase cursor := (phaseInverseProgram_support n cursor r.phaseUpdate r.shiftEpoch).trans (support_to_580 _ (by decide +kernel))
  unfold measuredInverseStepProgram
  apply sequenceProgram_support
  intro seg hseg cursor
  simp only [measuredInverseStepSegments,List.mem_cons,List.mem_nil_iff,or_false] at hseg
  rcases hseg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact (hPrograms_support_production n _ T hl.endIteration).2
  · exact hphase _
  · simp only [literalProgram_support,circuitWires,List.flatMap_append,List.append_subset]
    exact ⟨⟨hFadj,hprep⟩,hcAdd⟩
  · exact hci _ _ _
  · simp only [literalProgram_support,circuitWires,List.flatMap_append,List.append_subset]
    exact ⟨⟨⟨⟨hcAdd,hx⟩,hcTmp⟩,hcSub⟩,hcTmp⟩
  · exact hci _ _ _
  · simp only [literalProgram_support,circuitWires,List.flatMap_append,List.append_subset]
    exact ⟨⟨⟨⟨⟨⟨hcTmp,hcSub⟩,hcTmp⟩,hrest⟩,hD⟩,hC⟩,⟨hterm,hrst⟩,hterm⟩
  · exact hii _ _ _
  · simp only [literalProgram_support,circuitWires,List.flatMap_append,List.append_subset]
    exact ⟨⟨⟨⟨hterm,hrst⟩,hterm⟩,hB2⟩,hrsub⟩
  · exact hii _ _ _
  · simp only [literalProgram_support,circuitWires,List.flatMap_append,List.append_subset]
    exact ⟨hrsub,hA⟩


attribute [local irreducible] measuredStepProgram measuredInverseStepProgram

theorem measuredScheduleProgram_support_production (n first count start : Nat)
    (hl : IndexedScheduleLayout indexedStepProductionRegisters 256 first count) :
    straightWires (measuredScheduleProgram n indexedStepProductionRegisters 256 count first start).2 ⊆ List.range 580 := by
  induction hl generalizing start with
  | done first => simp [measuredScheduleProgram,literalProgram_support,circuitWires]
  | step head tail ih =>
    rw [measuredScheduleProgram,appendCompiled_support,List.append_subset]
    exact ⟨measuredStepProgram_support_production n _ _ head,ih _⟩

theorem measuredInverseScheduleProgram_support_production (n first count start : Nat)
    (hl : IndexedScheduleLayout indexedStepProductionRegisters 256 first count) :
    straightWires (measuredInverseScheduleProgram n indexedStepProductionRegisters count first start).2 ⊆ List.range 580 := by
  induction hl generalizing start with
  | done first => simp [measuredInverseScheduleProgram,literalProgram_support,circuitWires]
  | step head tail ih =>
    rw [measuredInverseScheduleProgram,appendCompiled_support,List.append_subset]
    exact ⟨ih _,measuredInverseStepProgram_support_production n _ _ head⟩

theorem measuredEEAForwardProgram_support_production (n start : Nat) :
    straightWires (measuredEEAForwardProgram n start indexedStepProductionRegisters).2 ⊆ List.range 580 :=
  measuredScheduleProgram_support_production n 1 secp256k1ScheduleLength start secp256k1ScheduleLayout_production

theorem measuredEEAReverseProgram_support_production (n start : Nat) :
    straightWires (measuredEEAReverseProgram n start indexedStepProductionRegisters).2 ⊆ List.range 580 :=
  measuredInverseScheduleProgram_support_production n 1 secp256k1ScheduleLength start secp256k1ScheduleLayout_production


theorem preprocessProgram_support (n start : Nat) :
    straightWires (preprocessProgram n start).2 ⊆ List.range 580 := by
  have hc := eeaCenterProgram_support n start (List.range' 266 256).reverse (List.range' 4 256)
    (constantBits 256 (2^256-2^32-977)) (2^256-2^32-977) 560 561 562 2 (List.range 580)
    (by simp) (by simp [constantBits_length]) (by simp)
    (List.mem_range.mpr (by decide)) (List.mem_range.mpr (by decide)) (List.mem_range.mpr (by decide)) (List.mem_range.mpr (by decide))
    (fun _ h => support_to_580 _ (by decide +kernel) _ h)
    (fun _ h => support_to_580 _ (by decide +kernel) _ h)
  have hbefore : circuitWires workRegistersPrepare ⊆ List.range 580 := by
    intro w hw
    apply eeaPreprocess_wires_subset
    simp only [eeaPreprocess,AdaptiveCircuit.wires,modularWires_seq,List.mem_append,List.not_mem_nil,or_false]
    exact Or.inl hw
  have hafter : circuitWires eeaLengthSetup ⊆ List.range 580 := by
    intro w hw
    apply eeaPreprocess_wires_subset
    simp only [eeaPreprocess,AdaptiveCircuit.wires,modularWires_seq,List.mem_append,List.not_mem_nil,or_false]
    exact Or.inr (Or.inr hw)
  unfold preprocessProgram
  simp only [surroundCompiled_support,List.append_subset]
  exact ⟨⟨hbefore,hc⟩,hafter⟩

theorem unpreprocessProgram_support (n start : Nat) :
    straightWires (unpreprocessProgram n start).2 ⊆ List.range 580 := by
  have hc := eeaUncenterProgram_support n start (List.range' 266 256).reverse (List.range' 4 256)
    (constantBits 256 (2^256-2^32-977)) (2^256-2^32-977) 560 561 562 2 (List.range 580)
    (by simp) (by simp [constantBits_length]) (by simp)
    (List.mem_range.mpr (by decide)) (List.mem_range.mpr (by decide)) (List.mem_range.mpr (by decide)) (List.mem_range.mpr (by decide))
    (fun _ h => support_to_580 _ (by decide +kernel) _ h)
    (fun _ h => support_to_580 _ (by decide +kernel) _ h)
  have hbefore : circuitWires eeaLengthUndo ⊆ List.range 580 := by
    intro w hw
    apply eeaUnpreprocess_wires_subset
    simp only [eeaUnpreprocess,AdaptiveCircuit.wires,modularWires_seq,List.mem_append,List.not_mem_nil,or_false]
    exact Or.inl hw
  have hafter : circuitWires workRegistersRestore ⊆ List.range 580 := by
    intro w hw
    apply eeaUnpreprocess_wires_subset
    simp only [eeaUnpreprocess,AdaptiveCircuit.wires,modularWires_seq,List.mem_append,List.not_mem_nil,or_false]
    exact Or.inr (Or.inr hw)
  unfold unpreprocessProgram
  simp only [surroundCompiled_support,List.append_subset]
  exact ⟨⟨hbefore,hc⟩,hafter⟩

theorem productionParityProgram_support (n start : Nat) :
    straightWires (productionParityProgram n start).2 ⊆ List.range 580 := by
  exact eeaParityProgram_support n start (List.range' 263 256) (List.range' 4 255)
    secp256k1ModulusBits 560 561 562 2 (List.range 580)
    (by simp) (by simp [secp256k1ModulusBits])
    (List.mem_range.mpr (by decide)) (List.mem_range.mpr (by decide)) (List.mem_range.mpr (by decide)) (List.mem_range.mpr (by decide))
    (fun _ h => support_to_580 _ (by decide +kernel) _ h)
    (fun _ h => support_to_580 _ (by decide +kernel) _ h)


attribute [local irreducible] preprocessProgram unpreprocessProgram productionParityProgram
  measuredEEAForwardProgram measuredEEAReverseProgram
  eeaPreprocess eeaUnpreprocess secp256k1EEAForwardAdaptive secp256k1EEAReverseAdaptive
  secp256k1EEAParityCorrection canonicalWork2Rotation canonicalWork2InverseRotation
  terminalEpochCompression terminalWork1Clear

theorem measuredForwardWrapperProgram_support (n start : Nat) :
    straightWires (measuredForwardWrapperProgram n start).2 ⊆ List.range 580 := by
  have hmid : circuitWires (canonicalWork2Rotation ++ terminalEpochCompression) ⊆ List.range 580 := by
    intro w hw
    apply secp256k1EEAForwardWrapper_wires_subset
    simp only [secp256k1EEAForwardWrapper,modularWires_seq,AdaptiveCircuit.wires,
      circuitWires,List.flatMap_append,List.mem_append,List.not_mem_nil,or_false] at hw ⊢
    aesop
  have hclear : circuitWires terminalWork1Clear ⊆ List.range 580 := by
    intro w hw
    apply secp256k1EEAForwardWrapper_wires_subset
    simp only [secp256k1EEAForwardWrapper,modularWires_seq,AdaptiveCircuit.wires,
      circuitWires,List.flatMap_append,List.mem_append,List.not_mem_nil,or_false] at hw ⊢
    aesop
  unfold measuredForwardWrapperProgram
  apply sequenceProgram_support
  intro seg hseg cursor
  simp only [measuredForwardWrapperSegments,List.mem_cons,List.mem_nil_iff,or_false] at hseg
  rcases hseg with rfl|rfl|rfl|rfl|rfl
  · exact preprocessProgram_support n _
  · exact measuredEEAForwardProgram_support_production n _
  · simpa only [literalProgram_support] using hmid
  · exact productionParityProgram_support n _
  · simpa only [literalProgram_support] using hclear

theorem measuredReverseWrapperProgram_support (n start : Nat) :
    straightWires (measuredReverseWrapperProgram n start).2 ⊆ List.range 580 := by
  have hmid : circuitWires (terminalEpochCompression ++ canonicalWork2InverseRotation) ⊆ List.range 580 := by
    intro w hw
    apply secp256k1EEAReverseWrapper_wires_subset
    simp only [secp256k1EEAReverseWrapper,secp256k1EEAReversePostprocessing,modularWires_seq,AdaptiveCircuit.wires,
      circuitWires,List.flatMap_append,List.mem_append,List.not_mem_nil,or_false] at hw ⊢
    aesop
  have hclear : circuitWires terminalWork1Clear ⊆ List.range 580 := by
    intro w hw
    apply secp256k1EEAReverseWrapper_wires_subset
    simp only [secp256k1EEAReverseWrapper,secp256k1EEAReversePostprocessing,modularWires_seq,AdaptiveCircuit.wires,
      circuitWires,List.flatMap_append,List.mem_append,List.not_mem_nil,or_false] at hw ⊢
    aesop
  unfold measuredReverseWrapperProgram
  apply sequenceProgram_support
  intro seg hseg cursor
  simp only [measuredReverseWrapperSegments,List.mem_cons,List.mem_nil_iff,or_false] at hseg
  rcases hseg with rfl|rfl|rfl|rfl|rfl
  · simpa only [literalProgram_support] using hclear
  · exact productionParityProgram_support n _
  · simpa only [literalProgram_support] using hmid
  · exact measuredEEAReverseProgram_support_production n _
  · exact unpreprocessProgram_support n _


private theorem exchanged_580_in_base (w : Wire) (hw : w ∈ List.range 580) :
    eeaWorkspaceExchange w ∈ windowBaseSupport := by
  have h : (List.range 580).all (fun w => decide (eeaWorkspaceExchange w < 837)) = true := by decide +kernel
  have hlt := of_decide_eq_true ((List.all_eq_true.mp h) w hw)
  simp only [windowBaseSupport,List.mem_append,List.mem_range,List.mem_singleton,List.mem_range'_1]
  exact Or.inl (Or.inl hlt)

theorem measuredForwardDataBankProgram_support_static (n start : Nat) :
    straightWires (measuredForwardDataBankProgram n start).2 ⊆ windowBaseSupport := by
  rw [measuredForwardDataBankProgram,relabelCompiled_support]
  intro w hw
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
  exact exchanged_580_in_base v (measuredForwardWrapperProgram_support n start hv)

theorem measuredReverseDataBankProgram_support_static (n start : Nat) :
    straightWires (measuredReverseDataBankProgram n start).2 ⊆ windowBaseSupport := by
  rw [measuredReverseDataBankProgram,relabelCompiled_support]
  intro w hw
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
  exact exchanged_580_in_base v (measuredReverseWrapperProgram_support n start hv)
end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/InPlaceSupport ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/InPlaceSupport.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
private theorem swap_support : circuitWires fig15SwapOutput ⊆ List.range 836 := by
  intro w hw
  simp only [circuitWires,fig15SwapOutput,List.mem_flatMap] at hw
  obtain ⟨g,⟨i,hi,hg⟩,hw⟩ := hw
  simp only [List.mem_range] at hi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl <;>
    simp only [gateWires,List.mem_cons,List.not_mem_nil,or_false] at hw <;>
    simp only [List.mem_range] <;> dsimp only [Wire] at * <;> omega

private theorem range_in_base (k : Nat) (hk : k ≤ 837) : List.range k ⊆ windowBaseSupport := by
  intro w hw
  have := List.mem_range.mp hw
  simp only [windowBaseSupport,List.mem_append,List.mem_range,List.mem_singleton,List.mem_range'_1]
  exact Or.inl (Or.inl (by omega))
private theorem data_in_base : List.range' 580 256 ⊆ windowBaseSupport := by
  intro w hw
  apply range_in_base 837 (by omega)
  simp only [List.mem_range'_1] at hw
  exact List.mem_range.mpr (by omega)

theorem correctionCompiled_support (n start : Nat) (ws : List Wire) (prior : List (Fin start)) :
    straightWires (correctionCompiled n start ws prior).2 ⊆ ws := by
  unfold correctionCompiled
  induction ws generalizing prior with
  | nil => simp [registerCorrectionProgram,straightWires]
  | cons w ws ih =>
    cases prior with
    | nil => simp [registerCorrectionProgram,straightWires]
    | cons i rest =>
      simp only [registerCorrectionProgram,recordGates_support]
      intro z hz
      simp only [circuitWires,pauliZ,List.flatMap_cons,List.flatMap_nil,List.append_nil,
        gateWires,List.mem_append,List.mem_cons,List.mem_nil_iff,or_false,or_self] at hz
      rcases hz with h | h
      · exact List.mem_cons.mpr (Or.inl h)
      · exact List.mem_cons_of_mem w (ih rest h)

attribute [local irreducible] unmultiplyDataProgram multiplyDataProgram multiplyWorkProgram
  measuredForwardWrapperProgram measuredForwardDataBankProgram measuredReverseDataBankProgram

theorem divisionCleanupProgram_support_static (n start : Nat) :
    straightWires (divisionCleanupProgram n start).2 ⊆ windowBaseSupport := by
  simp only [divisionCleanupProgram,appendLiteral,appendCompiled_support,literalProgram_support,List.append_subset]
  exact ⟨unmultiplyDataProgram_support_static n start,swap_support.trans (range_in_base _ (by omega))⟩

theorem multiplicationCleanupProgram_support_static (n start : Nat) :
    straightWires (multiplicationCleanupProgram n start).2 ⊆ windowBaseSupport := by
  simp only [multiplicationCleanupProgram,appendLiteral,appendCompiled_support,literalProgram_support,List.append_subset]
  exact ⟨unmultiplyDataProgram_support_static n start,measuredReverseDataBankProgram_support_static n _,swap_support.trans (range_in_base _ (by omega))⟩

theorem divisionCorrectionProgram_support_static (n start : Nat) (prior : List (Fin start)) :
    straightWires (divisionCorrectionProgram n start prior).2 ⊆ windowBaseSupport := by
  simp only [divisionCorrectionProgram,appendCompiled_support,List.append_subset]
  exact ⟨(correctionCompiled_support n start _ prior).trans data_in_base,divisionCleanupProgram_support_static n start⟩

theorem divisionAfterResetProgram_support_static (n start : Nat) (prior : List (Fin start)) :
    straightWires (divisionAfterResetProgram n start prior).2 ⊆ windowBaseSupport := by
  simp only [divisionAfterResetProgram,appendRetaining,appendCompiled_support,List.append_subset]
  exact ⟨⟨measuredReverseDataBankProgram_support_static n start,multiplyDataProgram_support_static n _⟩,divisionCorrectionProgram_support_static n _ _⟩

theorem multiplicationCorrectionProgram_support_static (n start : Nat) (prior : List (Fin start)) :
    straightWires (multiplicationCorrectionProgram n start prior).2 ⊆ windowBaseSupport := by
  simp only [multiplicationCorrectionProgram,appendCompiled_support,List.append_subset]
  exact ⟨(correctionCompiled_support n start _ prior).trans data_in_base,multiplicationCleanupProgram_support_static n start⟩

theorem multiplicationAfterResetProgram_support_static (n start : Nat) (prior : List (Fin start)) :
    straightWires (multiplicationAfterResetProgram n start prior).2 ⊆ windowBaseSupport := by
  simp only [multiplicationAfterResetProgram,appendRetaining,appendCompiled_support,List.append_subset]
  exact ⟨⟨measuredForwardDataBankProgram_support_static n start,multiplyDataProgram_support_static n _⟩,multiplicationCorrectionProgram_support_static n _ _⟩

theorem divisionProgram_support_static (n start : Nat) :
    straightWires (divisionProgram n start).2 ⊆ windowBaseSupport := by
  simp only [divisionProgram,appendCompiled_support,List.append_subset]
  refine ⟨⟨(measuredForwardWrapperProgram_support n start).trans (range_in_base _ (by omega)),multiplyWorkProgram_support_static n _⟩,?_⟩
  exact collectProgram_support n (divisionAfterResetProgram n) windowBaseSupport
    (divisionAfterResetProgram_support_static n) _ data_in_base _ _

theorem multiplicationProgram_support_static (n start : Nat) :
    straightWires (multiplicationProgram n start).2 ⊆ windowBaseSupport := by
  simp only [multiplicationProgram,appendCompiled_support,List.append_subset]
  refine ⟨multiplyWorkProgram_support_static n start,?_⟩
  exact collectProgram_support n (multiplicationAfterResetProgram n) windowBaseSupport
    (multiplicationAfterResetProgram_support_static n) _ data_in_base _ _
end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/CoordinateSupport ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/CoordinateSupport.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
/-- Complete coordinate candidate allocation, including the zero-divisor flag. -/
def coordinateBaseSupport : List Wire := 837 :: windowBaseSupport
private theorem old_in_complete : windowBaseSupport ⊆ coordinateBaseSupport :=
  List.subset_cons_of_subset 837 (List.Subset.refl _)
private theorem zero_layout_in_complete : zeroAllowedLayout ⊆ coordinateBaseSupport := by
  intro w hw
  simp only [zeroAllowedLayout,List.mem_append,List.mem_range,List.mem_singleton] at hw
  simp only [coordinateBaseSupport,windowBaseSupport,List.mem_cons,List.mem_append,List.mem_range,List.mem_nil_iff,or_false,List.mem_range'_1]
  dsimp only [Wire] at *
  omega
private theorem zero_wrapper_literals :
    circuitWires fig15ZeroPrepare ⊆ coordinateBaseSupport ∧
    circuitWires fig15ZeroRestore ⊆ coordinateBaseSupport := by
  constructor
  · intro w hw
    apply zero_layout_in_complete
    apply secp256k1ZeroAllowedDivision_wires_subset
    simp only [secp256k1ZeroAllowedDivision,modularWires_seq,AdaptiveCircuit.wires,List.mem_append,List.not_mem_nil,or_false]
    exact Or.inl (Or.inl hw)
  · intro w hw
    apply zero_layout_in_complete
    apply secp256k1ZeroAllowedDivision_wires_subset
    simp only [secp256k1ZeroAllowedDivision,modularWires_seq,AdaptiveCircuit.wires,List.mem_append,List.not_mem_nil,or_false]
    exact Or.inr hw

theorem zeroDivisionProgram_support_static (n start : Nat) :
    straightWires (zeroDivisionProgram n start).2 ⊆ coordinateBaseSupport := by
  simp only [zeroDivisionProgram,surroundCompiled_support,List.append_subset]
  exact ⟨⟨zero_wrapper_literals.1,(divisionProgram_support_static n start).trans old_in_complete⟩,zero_wrapper_literals.2⟩

theorem zeroMultiplicationProgram_support_static (n start : Nat) :
    straightWires (zeroMultiplicationProgram n start).2 ⊆ coordinateBaseSupport := by
  simp only [zeroMultiplicationProgram,surroundCompiled_support,List.append_subset]
  exact ⟨⟨zero_wrapper_literals.1,(multiplicationProgram_support_static n start).trans old_in_complete⟩,zero_wrapper_literals.2⟩

attribute [local irreducible] fieldLookupAddProgram signedFieldProgram zeroDivisionProgram
  pointSquareProgram zeroMultiplicationProgram xNegateProgram

theorem coordinateProgram_support_static (start : Nat) :
    straightWires (coordinateProgram start).2 ⊆ coordinateBaseSupport := by
  have ha : List.range' 263 256 ⊆ windowBaseSupport := by
    intro w hw
    simp only [List.mem_range'_1] at hw
    simp only [windowBaseSupport,List.mem_append,List.mem_range,List.mem_singleton,List.mem_range'_1]
    omega
  have hf field cursor := (fieldLookupAddProgram_support_static field _ ha (by simp) cursor).trans old_in_complete
  have hs field cursor := (signedFieldProgram_support_static field cursor).trans old_in_complete
  unfold coordinateProgram
  apply sequenceProgram_support
  intro seg hseg cursor
  simp only [coordinateSegments,List.mem_cons,List.mem_nil_iff,or_false] at hseg
  rcases hseg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact hf _ _
  · exact hs _ _
  · exact zeroDivisionProgram_support_static _ _
  · exact (pointSquareProgram_support_static _ _).trans old_in_complete
  · exact hf _ _
  · exact zeroMultiplicationProgram_support_static _ _
  · exact (xNegateProgram_support_static _ _).trans old_in_complete
  · exact hf _ _
  · exact hs _ _
theorem zeroDivision_touches837 (n start : Nat) :
    837 ∈ straightWires (zeroDivisionProgram n start).2 := by
  simp only [zeroDivisionProgram,surroundCompiled_support,List.mem_append]
  left; left
  simp only [fig15ZeroPrepare,nonzeroInputPrepare,circuitWires,List.flatMap_append,List.mem_append]
  right
  simp [gateWires]

theorem coordinateProgram_touches837 (start : Nat) :
    837 ∈ straightWires (coordinateProgram start).2 := by
  simp only [coordinateProgram,coordinateSegments,sequenceProgram,appendCompiled_support,List.mem_append]
  exact Or.inr (Or.inr (Or.inl (zeroDivision_touches837 _ _)))
end ShorECDLP.Paper2607_13816.ChallengeMigration

end

-- ==== part: Streaming/CompleteSupport ====

section
/-! Ported from VerifiedQC/ShorECDLP, branch `streaming-dev` (PR #551), file
`ShorECDLP/Submission/2607_13816/Challenge/CompleteSupport.lean`, Apache-2.0 (see the repository
LICENSE and NOTICE). Construction: arXiv:2607.13816v2 (Luo, Yang, Luo, Wang, Su, Sun, Li, Li).
Moved into the editable Entrant tree; module imports renamed accordingly. -/

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
/-- Static allocation includes the zero-divisor flag even though the reset list omits it. -/
def completeBatchedSupport : List Wire := 837 :: resetWires

theorem completeBatchedSupport_length : completeBatchedSupport.length = 855 := by
  simp only [completeBatchedSupport,List.length_cons,resetWires_length]

private theorem old_in_complete_CompleteSupport : resetWires ⊆ completeBatchedSupport :=
  List.subset_cons_of_subset 837 (List.Subset.refl _)

theorem sharedCoordinateProgram_support_static (w : OddWindow) (start : Nat) :
    (straightWires (sharedCoordinateProgram w start).2).map
      (windowAddressPerm 855 (by decide)) ⊆ completeBatchedSupport := by
  simp only [sharedCoordinateProgram,reindexCompiled_support]
  intro z hz
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hz
  have h := coordinateProgram_support_static start hv
  rcases List.mem_cons.mp h with rfl | h
  · have he : windowAddressPerm 855 (by decide) 837 = 837 := by decide +kernel
    rw [he]
    exact List.mem_cons_self
  · exact old_in_complete_CompleteSupport (windowBaseSupport_relocated v h)

theorem actualIpxWindow_support_static (w : OddWindow) (start : Nat) :
    straightWires ((actualIpxWindow w).program start) ⊆ completeBatchedSupport := by
  have hcore cursor : (straightWires (ipxWindowCore w cursor).2).map
      (windowAddressPerm 855 (by decide)) ⊆ completeBatchedSupport := by
    apply sequenceProgram_mapped_support
    simp only [ipxWindowSegments,List.forall_mem_cons,List.mem_nil_iff,false_implies,implies_true,and_true]
    exact ⟨sharedCoordinateProgram_support_static w,
      fun cursor => (sharedYNegateProgram_support_static w cursor).trans old_in_complete_CompleteSupport,
      fun cursor => (ipxProgram_support_static w cursor).trans old_in_complete_CompleteSupport,
      fun cursor => (sharedYNegateProgram_support_static w cursor).trans old_in_complete_CompleteSupport⟩
  simp only [actualIpxWindow,closedWindow,straightWires_shift,straightWires_relabel,
    ipxWindowPrepared,surroundCompiled_support,List.map_append,List.append_subset]
  exact ⟨⟨signedAddressCircuit_support_static.trans old_in_complete_CompleteSupport,hcore 0⟩,
    signedAddressCircuit_support_static.trans old_in_complete_CompleteSupport⟩

theorem actualWindows_support_static
    (window : OuterWindow 983040) (hw : window ∈ ipxLeftWindows ++ ipxRightWindows)
    (start : Nat) : straightWires (window.program start) ⊆ completeBatchedSupport := by
  simp only [ipxLeftWindows,ipxRightWindows,List.mem_append,List.mem_cons,List.mem_ofFn] at hw
  rcases hw with (rfl | ⟨k,rfl⟩) | ⟨k,rfl⟩
  · exact (actualFirstWindow_support_static start).trans
      old_in_complete_CompleteSupport
  · exact actualIpxWindow_support_static _ start
  · exact actualIpxWindow_support_static _ start

theorem ipxOuter_support_static
    (count start : Nat) (read : ConstantBit 983040 → Bool) (history : Fin start → Bool) :
    ((ipxOuterPlan.repeat count start).instantiate read history).wires ⊆ completeBatchedSupport := by
  apply OuterPlan.repeat_support
  · intro w hw
    simp only [ipxOuterPlan,standardOuterPlan,Vector.toList_mk,List.mem_reverse] at hw
    exact old_in_complete_CompleteSupport (List.mem_append_right _ hw)
  · exact old_in_complete_CompleteSupport
  · simp [completeBatchedSupport,resetWires]
  · intro window hw cursor h
    apply (straight_instantiate_support _ read h).trans
    apply actualWindows_support_static window _ cursor
    simpa only [ipxOuterPlan,standardOuterPlan,Vector.toList_mk,List.toList_toArray] using hw

theorem wire837_not_in_old_allocation : 837 ∉ resetWires := by
  simp only [resetWires,List.mem_append,List.mem_range,List.mem_singleton,List.mem_range'_1]
  norm_num

theorem sharedCoordinateProgram_touches837 (w : OddWindow) (start : Nat) :
    837 ∈ (straightWires (sharedCoordinateProgram w start).2).map
      (windowAddressPerm 855 (by decide)) := by
  simp only [sharedCoordinateProgram,reindexCompiled_support]
  exact List.mem_map.mpr ⟨837,coordinateProgram_touches837 start,by decide +kernel⟩

theorem old_coordinate_support_false (w : OddWindow) (start : Nat) :
    ¬ (straightWires (sharedCoordinateProgram w start).2).map
      (windowAddressPerm 855 (by decide)) ⊆ resetWires := by
  intro h
  exact wire837_not_in_old_allocation (h (sharedCoordinateProgram_touches837 w start))

/-- An upper bound on the actual program's deduplicated wire set, not an exact usage count. -/
theorem ipxOuter_qubits_le_855
    (count start : Nat) (read : ConstantBit 983040 → Bool) (history : Fin start → Bool) :
    ((ipxOuterPlan.repeat count start).instantiate read history).wires.toFinset.card ≤ 855 := by
  have hs := ipxOuter_support_static count start read history
  have hfin : ((ipxOuterPlan.repeat count start).instantiate read history).wires.toFinset ⊆
      completeBatchedSupport.toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (hs (List.mem_toFinset.mp hw))
  exact (Finset.card_le_card hfin).trans ((List.toFinset_card_le _).trans_eq completeBatchedSupport_length)
end ShorECDLP.Paper2607_13816.ChallengeMigration

end
