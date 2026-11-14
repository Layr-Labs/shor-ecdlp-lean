import ShorECDLP.Submission.Entrant.Prefix
import ShorECDLP.Submission.Entrant.Bank9

namespace ShorECDLP.Entrant.SelectSchedule18
open Quantum Secp256k1 Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
def bits : List Wire := List.range' 855 17 ++ [537]
def Input (s : BasisState) : Prop := s 836=true ∧ ∀ v,v≠836 → v∉bits → s v=false
def tablePoint (coeffs : Fin 262144 → PointCoeff) (Q : Point) (a : Nat) : Point :=
  constantPoint Q (coeffs ⟨a%262144,Nat.mod_lt _ (by decide +kernel)⟩)
def update (init : Point → Nat → Point) (Q : Point) (s : BasisState) : BasisState :=
  pointWrite (init Q (tableAddressValue bits s)) s
end
end ShorECDLP.Entrant.SelectSchedule18
namespace ShorECDLP.Entrant.First18
open Quantum Challenge Secp256k1 Paper2607_13816 Paper2607_13816.ChallengeMigration AndGadget WEXCredit
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false

/-! ### Registers -/

/-- The high sixteen address bits, little-endian. -/
def selBits : List Wire := List.range' 856 16 ++ [537]
def selPaths : List Wire := List.range' 519 17
/-- The partner register: 513 pool wires that are clean before the first window. -/
def garb : List Wire := List.range' 872 513
def high : List Wire := List.range' 864 8 ++ [537]
def clearPaths : List Wire := List.range' 519 9
def scratch : Wire := 872
def hot (i : Fin 512) : Wire := 873 + i.val
def low (i : Fin 9) : Wire := 855 + i.val

def row (a : Nat) : Fin 262144 := ⟨a % 262144, Nat.mod_lt _ (by decide +kernel)⟩
/-- The address that differs from `a` in bit 0. -/
def partner (a : Nat) : Nat := 2 * (a / 2) + (1 - a % 2)

theorem mem_point {w : Nat} (h : w ∈ pointLogicalWires) :
    (263 ≤ w ∧ w < 519) ∨ (580 ≤ w ∧ w < 836) ∨ w = 838 := by
  simp only [pointLogicalWires, pointCorrectionX, pointCorrectionYInf, List.mem_append,
    List.mem_range'_1, List.mem_singleton, List.not_mem_nil, or_false] at h
  (try dsimp only [Wire] at *); omega

theorem mem_garb {w : Nat} (h : w ∈ garb) : 872 ≤ w ∧ w < 1385 := by
  simp only [garb, List.mem_range'_1] at h
  (try dsimp only [Wire] at *); omega

theorem point_length : pointLogicalWires.length = 513 := by
  simp [pointLogicalWires, pointCorrectionX, pointCorrectionYInf]

theorem garb_length : garb.length = 513 := by simp [garb]

theorem garb_nodup : garb.Nodup := List.nodup_range'

theorem point_not_garb {w : Nat} (h1 : w ∈ pointLogicalWires) (h2 : w ∈ garb) : False := by
  have := mem_point h1
  have := mem_garb h2
  (try dsimp only [Wire] at *); omega

theorem point_garb_nodup : (pointLogicalWires ++ garb).Nodup :=
  List.nodup_append.mpr ⟨pointLogicalWires_nodup, garb_nodup,
    fun _ ha _ hb he => point_not_garb ha (by rw [he]; exact hb)⟩

theorem n855_point : (855 : Wire) ∉ pointLogicalWires := fun h => by have := mem_point h; (try dsimp only [Wire] at *); omega
theorem n855_garb : (855 : Wire) ∉ garb := fun h => by have := mem_garb h; (try dsimp only [Wire] at *); omega

theorem low_eq : List.ofFn low = List.range' 855 9 := by decide +kernel
theorem hot_eq : List.ofFn hot = List.range' 873 512 := by decide +kernel

theorem input_clean (s : BasisState) (hs : SelectSchedule18.Input s) (w : Nat)
    (h1 : w ≠ 836) (h2 : w < 855 ∨ 872 ≤ w) (h3 : w ≠ 537) : s w = false := by
  apply hs.2 w h1
  simp only [SelectSchedule18.bits, List.mem_append, List.mem_range'_1, List.mem_singleton, List.not_mem_nil, or_false]
  (try dsimp only [Wire] at *); omega

theorem input_selPaths (s : BasisState) (hs : SelectSchedule18.Input s) : Clean selPaths s := by
  intro w hw
  simp only [selPaths, List.mem_range'_1] at hw
  exact input_clean s hs w (by (try dsimp only [Wire] at *); omega) (by (try dsimp only [Wire] at *); omega) (by (try dsimp only [Wire] at *); omega)

/-! ### The select -/

def selLeaf (l : Nat) (q : Wire) : List (TemplateGate 262144) :=
  lookupLeafGates q ((pointRefs (row (2 * l))).zip pointLogicalWires ++
    (pointRefs (row (2 * l + 1))).zip garb)

def selOps : List (LookupOp 262144) :=
  unaryLookupOps selLeaf (tableAddressTree selBits 0 1) 836 selPaths

theorem sel_layout : (tableAddressTree selBits 0 1).Layout 836 selPaths :=
  tableAddressTree_layout _ _ _ _ _ (by decide +kernel) (by decide +kernel)

theorem sel_nodes : (tableAddressTree selBits 0 1).internalNodes = 131071 := by
  have h := tableAddressTree_nodes selBits 0 1
  change _ + 1 = 131072 at h
  (try dsimp only [Wire] at *); omega

theorem selOps_measurements : lookupMeasurements selOps = 131071 := by
  rw [selOps, unaryLookupOps_measurements _ _ _ _ sel_layout, sel_nodes]

def word (read : ConstantBit 262144 → Bool) (a : Nat) : List Bool := (pointRefs (row a)).map read

def selMask (read : ConstantBit 262144 → Bool) (l : Nat) : List Wire :=
  tableBitsMask pointLogicalWires (word read (2 * l)) ++ tableBitsMask garb (word read (2 * l + 1))

theorem pointRefs_length (r : Fin 262144) : (pointRefs r).length = 513 := by
  rw [pointRefs, List.length_append, List.length_append, List.length_ofFn, List.length_ofFn,
    List.length_singleton] <;> rfl

theorem word_length (read : ConstantBit 262144 → Bool) (a : Nat) : (word read a).length = 513 := by
  rw [word, List.length_map, pointRefs_length]

theorem selLeaf_instantiate (read : ConstantBit 262144 → Bool) (l : Nat) (q : Wire) :
    (selLeaf l q).flatMap (TemplateGate.instantiate read) = tableXorGates q (selMask read l) := by
  rw [selLeaf, lookupLeafGates_instantiate,
    show (fun p : ConstantBit 262144 × Wire => Gate.CX q p.2) = (Gate.CX q) ∘ Prod.snd from rfl,
    ← List.map_map, List.filter_append, List.map_append, filtered_zip_mask, filtered_zip_mask]
  rfl

theorem selOps_circuit (read : ConstantBit 262144 → Bool) :
    lookupCircuit read selOps = tableLookupProgram (selMask read) selBits 836 selPaths := by
  rw [selOps, unaryLookupOps_circuit]
  unfold tableLookupProgram tableLookup
  apply unaryAction_leaf_congr
  intro l _ q
  exact selLeaf_instantiate read l q

attribute [irreducible] selOps

theorem selMask_sub (read : ConstantBit 262144 → Bool) (l : Nat) {w : Wire} (h : w ∈ selMask read l) :
    w ∈ pointLogicalWires ∨ w ∈ garb := by
  rcases List.mem_append.mp h with h | h
  · exact Or.inl (tableBitsMask_subset _ _ h)
  · exact Or.inr (tableBitsMask_subset _ _ h)

theorem selMask_nodup (read : ConstantBit 262144 → Bool) (l : Nat) : (selMask read l).Nodup :=
  List.nodup_append.mpr ⟨tableBitsMask_nodup _ _ pointLogicalWires_nodup,
    tableBitsMask_nodup _ _ garb_nodup, fun _ ha _ hb he => point_not_garb
      (tableBitsMask_subset _ _ ha) (by rw [he]; exact tableBitsMask_subset _ _ hb)⟩

theorem sel_coherent (read : ConstantBit 262144 → Bool) :
    CoherentlyImplementsOn (lookupCircuit read selOps)
      (Finsupp.lmapDomain ℂ ℂ (tableLookupState (selMask read) selBits 836)) (Clean selPaths) := by
  rw [selOps_circuit]
  apply tableLookupProgram_coherent_state _ _ _ _ (by decide +kernel) (by decide +kernel) (selMask_nodup read)
  intro l w hw hm
  simp only [selBits, selPaths, List.mem_cons, List.mem_append, List.mem_range'_1,
    List.mem_singleton, List.not_mem_nil, or_false] at hw
  rcases selMask_sub read l hm with h | h
  · have := mem_point h; (try dsimp only [Wire] at *); omega
  · have := mem_garb h; (try dsimp only [Wire] at *); omega

theorem sel_frame (read : ConstantBit 262144 → Bool) (s : BasisState) (w : Wire)
    (h1 : w ∉ pointLogicalWires) (h2 : w ∉ garb) :
    tableLookupState (selMask read) selBits 836 s w = s w := by
  unfold tableLookupState
  apply tableXorState_outside
  intro hm
  rcases selMask_sub read _ hm with h | h
  · exact h1 h
  · exact h2 h

theorem input_point (s : BasisState) (hs : SelectSchedule18.Input s) : Clean pointLogicalWires s :=
  fun w hw => by
    have := mem_point hw
    exact input_clean s hs w (by (try dsimp only [Wire] at *); omega) (by (try dsimp only [Wire] at *); omega) (by (try dsimp only [Wire] at *); omega)

theorem input_garb (s : BasisState) (hs : SelectSchedule18.Input s) : Clean garb s :=
  fun w hw => by
    have := mem_garb hw
    exact input_clean s hs w (by (try dsimp only [Wire] at *); omega) (by (try dsimp only [Wire] at *); omega) (by (try dsimp only [Wire] at *); omega)

theorem sel_point (read : ConstantBit 262144 → Bool) (s : BasisState) (hs : SelectSchedule18.Input s) :
    wireValues pointLogicalWires (tableLookupState (selMask read) selBits 836 s) =
      word read (2 * tableAddressValue selBits s) := by
  have he : wireValues pointLogicalWires (tableLookupState (selMask read) selBits 836 s) =
      wireValues pointLogicalWires (tableXorState (tableBitsMask pointLogicalWires
        (word read (2 * tableAddressValue selBits s))) true s) := by
    apply List.map_congr_left
    intro w hw
    have hg : w ∉ tableBitsMask garb (word read (2 * tableAddressValue selBits s + 1)) :=
      fun h => point_not_garb hw (tableBitsMask_subset _ _ h)
    simp only [tableLookupState, tableXorState, selMask, List.mem_append, hg, or_false, hs.1]
  rw [he, tableBitsMask_read _ _ s pointLogicalWires_nodup (by rw [point_length, word_length])
    (input_point s hs)]

theorem sel_garb (read : ConstantBit 262144 → Bool) (s : BasisState) (hs : SelectSchedule18.Input s) :
    wireValues garb (tableLookupState (selMask read) selBits 836 s) =
      word read (2 * tableAddressValue selBits s + 1) := by
  have he : wireValues garb (tableLookupState (selMask read) selBits 836 s) =
      wireValues garb (tableXorState (tableBitsMask garb
        (word read (2 * tableAddressValue selBits s + 1))) true s) := by
    apply List.map_congr_left
    intro w hw
    have hp : w ∉ tableBitsMask pointLogicalWires (word read (2 * tableAddressValue selBits s)) :=
      fun h => point_not_garb (tableBitsMask_subset _ _ h) hw
    simp only [tableLookupState, tableXorState, selMask, List.mem_append, hp, false_or, hs.1]
  rw [he, tableBitsMask_read _ _ s garb_nodup (by rw [garb_length, word_length]) (input_garb s hs)]

/-! ### The swap layer -/

def swapWords (c : Wire) : List Wire → List Wire → Circuit
  | a :: as, b :: bs => controlledSwap c a b ++ swapWords c as bs
  | _, _ => []

theorem swapWords_run (c : Wire) : ∀ (as bs : List Wire), c ∉ as → c ∉ bs → (as ++ bs).Nodup →
    as.length = bs.length → ∀ s : BasisState,
    (∀ w, w ∉ as → w ∉ bs → Classical.run (swapWords c as bs) s w = s w) ∧
    wireValues as (Classical.run (swapWords c as bs) s) =
      (if s c then wireValues bs s else wireValues as s) ∧
    wireValues bs (Classical.run (swapWords c as bs) s) =
      (if s c then wireValues as s else wireValues bs s)
  | [], [], _, _, _, _, s => by simp [swapWords, wireValues]
  | [], _ :: _, _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, _, h, _ => by simp at h
  | a :: as, b :: bs, hca, hcb, hn, hl, s => by
    have hca' : c ≠ a := fun h => hca (by simp [h])
    have hcas : c ∉ as := fun h => hca (by simp [h])
    have hcb' : c ≠ b := fun h => hcb (by simp [h])
    have hcbs : c ∉ bs := fun h => hcb (by simp [h])
    have hn1 := List.nodup_cons.mp (by simpa only [List.cons_append] using hn)
    have ha_as : a ∉ as := fun h => hn1.1 (by simp [h])
    have ha_bs : a ∉ bs := fun h => hn1.1 (by simp [h])
    have hab : a ≠ b := fun h => hn1.1 (by simp [h])
    have hn2 := List.nodup_cons.mp (List.nodup_middle.mp hn1.2)
    have hb_as : b ∉ as := fun h => hn2.1 (List.mem_append_left _ h)
    have hb_bs : b ∉ bs := fun h => hn2.1 (List.mem_append_right _ h)
    have hl' : as.length = bs.length := by simpa using hl
    have hsw := run_controlledSwap c a b s hca' hcb' hab
    have hsc : Classical.run (controlledSwap c a b) s c = s c := by
      by_cases hc : s c = true <;> simp [hsw, hc, upd, hca', hcb']
    have hfr : ∀ w, w ≠ a → w ≠ b → Classical.run (controlledSwap c a b) s w = s w := by
      intro w h1 h2
      by_cases hc : s c = true <;> simp [hsw, hc, upd, h1, h2]
    have hsa : Classical.run (controlledSwap c a b) s a = (if s c then s b else s a) := by
      by_cases hc : s c = true <;> simp [hsw, hc, upd, hab]
    have hsb : Classical.run (controlledSwap c a b) s b = (if s c then s a else s b) := by
      by_cases hc : s c = true <;> simp [hsw, hc, upd]
    obtain ⟨ihf, iha, ihb⟩ :=
      swapWords_run c as bs hcas hcbs hn2.2 hl' (Classical.run (controlledSwap c a b) s)
    have hvas : wireValues as (Classical.run (controlledSwap c a b) s) = wireValues as s :=
      List.map_congr_left (fun w hw => hfr w (fun h => ha_as (h ▸ hw)) (fun h => hb_as (h ▸ hw)))
    have hvbs : wireValues bs (Classical.run (controlledSwap c a b) s) = wireValues bs s :=
      List.map_congr_left (fun w hw => hfr w (fun h => ha_bs (h ▸ hw)) (fun h => hb_bs (h ▸ hw)))
    have hrun : Classical.run (swapWords c (a :: as) (b :: bs)) s =
        Classical.run (swapWords c as bs) (Classical.run (controlledSwap c a b) s) := by
      rw [swapWords, Classical.run_append]
    rw [hrun]
    refine ⟨?_, ?_, ?_⟩
    · intro w hw1 hw2
      rw [ihf w (fun h => hw1 (List.mem_cons_of_mem _ h)) (fun h => hw2 (List.mem_cons_of_mem _ h))]
      exact hfr w (fun h => hw1 (by simp [h])) (fun h => hw2 (by simp [h]))
    · show Classical.run (swapWords c as bs) (Classical.run (controlledSwap c a b) s) a ::
          wireValues as (Classical.run (swapWords c as bs) (Classical.run (controlledSwap c a b) s)) = _
      rw [ihf a ha_as ha_bs, iha, hsc, hvas, hvbs, hsa]
      cases s c <;> rfl
    · show Classical.run (swapWords c as bs) (Classical.run (controlledSwap c a b) s) b ::
          wireValues bs (Classical.run (swapWords c as bs) (Classical.run (controlledSwap c a b) s)) = _
      rw [ihf b hb_as hb_bs, ihb, hsc, hvas, hvbs, hsb]
      cases s c <;> rfl

theorem swapWords_length (c : Wire) : ∀ as bs : List Wire,
    (swapWords c as bs).length = 3 * min as.length bs.length
  | [], _ => by simp [swapWords]
  | _ :: _, [] => by simp [swapWords]
  | a :: as, b :: bs => by
    rw [swapWords, List.length_append, swapWords_length c as bs]
    simp only [controlledSwap, List.length_cons, List.length_nil]
    (try dsimp only [Wire] at *); omega

theorem swapWords_ccx (c : Wire) : ∀ as bs : List Wire,
    ccxCount (swapWords c as bs) = min as.length bs.length
  | [], _ => by simp [swapWords, ccxCount]
  | _ :: _, [] => by simp [swapWords, ccxCount]
  | a :: as, b :: bs => by
    show Nat.succ (ccxCount (swapWords c as bs)) = min (as.length + 1) (bs.length + 1)
    rw [swapWords_ccx c as bs]
    (try dsimp only [Wire] at *); omega

theorem swapWords_hp (c : Wire) : ∀ as bs : List Wire, Classical.HPFree (swapWords c as bs)
  | [], _ => by simp [swapWords]
  | _ :: _, [] => by simp [swapWords]
  | a :: as, b :: bs => by
    rw [swapWords, Classical.hpFree_append]
    exact ⟨controlledSwap_HPFree c a b, swapWords_hp c as bs⟩

theorem swapWords_wf (c : Wire) : ∀ as bs : List Wire, c ∉ as → c ∉ bs → (as ++ bs).Nodup →
    CircuitWellFormed (swapWords c as bs)
  | [], _, _, _, _ => by simp [swapWords]
  | _ :: _, [], _, _, _ => by simp [swapWords]
  | a :: as, b :: bs, hca, hcb, hn => by
    rw [swapWords, circuitWellFormed_append]
    have hn1 := List.nodup_cons.mp (by simpa only [List.cons_append] using hn)
    have hn2 := List.nodup_cons.mp (List.nodup_middle.mp hn1.2)
    exact ⟨controlledSwap_wellFormed c a b (fun h => hca (by simp [h])) (fun h => hcb (by simp [h]))
      (fun h => hn1.1 (by simp [h])),
      swapWords_wf c as bs (fun h => hca (by simp [h])) (fun h => hcb (by simp [h])) hn2.2⟩

theorem swapWords_wires (c : Wire) : ∀ (as bs : List Wire) (w : Wire),
    w ∈ circuitWires (swapWords c as bs) → w = c ∨ w ∈ as ∨ w ∈ bs
  | [], _, w, h => by simp [swapWords, circuitWires] at h
  | _ :: _, [], w, h => by simp [swapWords, circuitWires] at h
  | a :: as, b :: bs, w, h => by
    rw [swapWords, circuitWires, List.flatMap_append] at h
    rcases List.mem_append.mp h with h | h
    · have hw : w = b ∨ w = a ∨ w = c := by
        simp only [controlledSwap, List.flatMap_cons, List.flatMap_nil, gateWires, List.mem_append,
          List.mem_cons, List.not_mem_nil, or_false, List.append_nil] at h
        tauto
      rcases hw with rfl | rfl | rfl
      · exact Or.inr (Or.inr List.mem_cons_self)
      · exact Or.inr (Or.inl List.mem_cons_self)
      · exact Or.inl rfl
    · rcases swapWords_wires c as bs w h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (List.mem_cons_of_mem _ h))
      · exact Or.inr (Or.inr (List.mem_cons_of_mem _ h))

def swapCircuit : Circuit := swapWords 855 pointLogicalWires garb

theorem swap_hp : Classical.HPFree swapCircuit := swapWords_hp _ _ _

theorem swap_wf : CircuitWellFormed swapCircuit :=
  swapWords_wf _ _ _ n855_point n855_garb point_garb_nodup

theorem swap_facts (s : BasisState) :
    (∀ w, w ∉ pointLogicalWires → w ∉ garb → Classical.run swapCircuit s w = s w) ∧
    wireValues pointLogicalWires (Classical.run swapCircuit s) =
      (if s 855 then wireValues garb s else wireValues pointLogicalWires s) ∧
    wireValues garb (Classical.run swapCircuit s) =
      (if s 855 then wireValues pointLogicalWires s else wireValues garb s) :=
  swapWords_run 855 pointLogicalWires garb n855_point n855_garb point_garb_nodup
    (by rw [point_length, garb_length]) s

theorem swap_wires (w : Wire) (h : w ∈ circuitWires swapCircuit) :
    w = 855 ∨ w ∈ pointLogicalWires ∨ w ∈ garb :=
  swapWords_wires 855 pointLogicalWires garb w h

attribute [irreducible] swapCircuit

/-! ### The loaded state -/

def loaded (read : ConstantBit 262144 → Bool) (s : BasisState) : BasisState :=
  Classical.run swapCircuit (tableLookupState (selMask read) selBits 836 s)

theorem bits_eq : SelectSchedule18.bits = 855 :: selBits := rfl

theorem address_split (s : BasisState) :
    tableAddressValue SelectSchedule18.bits s = (s 855).toNat + 2 * tableAddressValue selBits s := by
  rw [bits_eq] <;> rfl

theorem word_cases (read : ConstantBit 262144 → Bool) (b : Bool) (h : Nat) :
    (if b = true then word read (2 * h + 1) else word read (2 * h)) = word read (b.toNat + 2 * h) ∧
    (if b = true then word read (2 * h) else word read (2 * h + 1)) =
      word read (partner (b.toNat + 2 * h)) := by
  cases b
  · constructor
    · show word read (2 * h) = word read (Bool.toNat false + 2 * h)
      congr 1
      simp only [Bool.toNat_false]
      (try dsimp only [Wire] at *); omega
    · show word read (2 * h + 1) = word read (partner (Bool.toNat false + 2 * h))
      congr 1
      simp only [Bool.toNat_false, partner]
      (try dsimp only [Wire] at *); omega
  · constructor
    · show word read (2 * h + 1) = word read (Bool.toNat true + 2 * h)
      congr 1
      simp only [Bool.toNat_true]
      (try dsimp only [Wire] at *); omega
    · show word read (2 * h) = word read (partner (Bool.toNat true + 2 * h))
      congr 1
      simp only [Bool.toNat_true, partner]
      (try dsimp only [Wire] at *); omega

theorem loaded_facts (read : ConstantBit 262144 → Bool) (s : BasisState) (hs : SelectSchedule18.Input s) :
    (∀ w, w ∉ pointLogicalWires → w ∉ garb → loaded read s w = s w) ∧
    wireValues pointLogicalWires (loaded read s) = word read (tableAddressValue SelectSchedule18.bits s) ∧
    wireValues garb (loaded read s) =
      word read (partner (tableAddressValue SelectSchedule18.bits s)) := by
  obtain ⟨sf, sp, sg⟩ := swap_facts (tableLookupState (selMask read) selBits 836 s)
  have h855 : tableLookupState (selMask read) selBits 836 s 855 = s 855 :=
    sel_frame read s 855 n855_point n855_garb
  rw [h855, sel_point read s hs, sel_garb read s hs] at sp sg
  refine ⟨fun w h1 h2 => (sf w h1 h2).trans (sel_frame read s w h1 h2), ?_, ?_⟩
  · show wireValues pointLogicalWires (Classical.run swapCircuit _) = _
    rw [sp, address_split]
    exact (word_cases read (s 855) _).1
  · show wireValues garb (Classical.run swapCircuit _) = _
    rw [sg, address_split]
    exact (word_cases read (s 855) _).2

/-! ### The measured clear of the partner register -/

def slots : List (Fin 262144 → ConstantBit 262144) :=
  List.ofFn (fun i : Fin 256 => fun r => (⟨r, .x, i⟩ : ConstantBit 262144)) ++
  List.ofFn (fun i : Fin 256 => fun r => (⟨r, .y, i⟩ : ConstantBit 262144)) ++
  [fun r => (⟨r, .infinity, ⟨0, by decide +kernel⟩⟩ : ConstantBit 262144)]

theorem pointRefs_slots (r : Fin 262144) : pointRefs r = slots.map (fun f => f r) := by
  rw [pointRefs, slots, List.map_append, List.map_append, List.map_ofFn, List.map_ofFn, List.map_cons,
    List.map_nil] <;> rfl

theorem slots_length : slots.length = 513 := by
  rw [slots, List.length_append, List.length_append, List.length_ofFn, List.length_ofFn,
    List.length_singleton] <;> rfl

def clearData : List (MeasuredClear.ClearPort 262144) :=
  List.zipWith (fun f w => (⟨fun x => f (row (partner x)), true, w⟩ : MeasuredClear.ClearPort 262144))
    slots garb

theorem zipWith_targets {α : Type} (g : α → Wire → MeasuredClear.ClearPort 262144)
    (hg : ∀ x w, (g x w).target = w) :
    ∀ (xs : List α) (ws : List Wire), xs.length = ws.length →
      (List.zipWith g xs ws).map MeasuredClear.ClearPort.target = ws
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, w :: ws, h => by
    rw [List.zipWith_cons_cons, List.map_cons, hg, zipWith_targets g hg xs ws (by simpa using h)]

theorem clearData_targets : clearData.map MeasuredClear.ClearPort.target = garb :=
  zipWith_targets _ (fun _ _ => rfl) slots garb (by rw [slots_length, garb_length])

theorem clearData_length : clearData.length = 513 := by
  have h := congrArg List.length clearData_targets
  rw [List.length_map, garb_length] at h
  exact h

theorem clear_layout : (tableAddressTree high 0 1).Layout 836 clearPaths :=
  tableAddressTree_layout _ _ _ _ _ (by decide +kernel) (by decide +kernel)

theorem high_index : (tableAddressTree high 0 1).indexWires.dedup = high :=
  tableAddressTree_index _ _ _ (by decide +kernel)

theorem clear_nodes : (tableAddressTree high 0 1).internalNodes = 511 := by
  have h := tableAddressTree_nodes high 0 1
  change _ + 1 = 512 at h
  (try dsimp only [Wire] at *); omega

theorem clear_leaves : (tableAddressTree high 0 1).leaves = 512 := by
  rw [MeasuredClear.addressTree_leaves] <;> rfl

theorem clear_measurements : MeasuredClear.recordMeasurements
    (MeasuredClear.recordUnaryOps (tableAddressTree high 0 1) 836 clearPaths) = 511 := by
  rw [(MeasuredClear.recordUnary_counts _ _ _ clear_layout 0).1, clear_nodes]

theorem hot_injective : Function.Injective hot := by
  intro i j h
  simp only [hot] at h
  exact Fin.ext (by (try dsimp only [Wire] at *); omega)

theorem low_ne_hot : ∀ i j, low i ≠ hot j := by
  intro i j h
  simp only [low, hot] at h
  have := i.isLt
  (try dsimp only [Wire] at *); omega

theorem hot_disjoint : (MeasuredClear.hotBank9 hot).Disjoint
    (836 :: (tableAddressTree high 0 1).indexWires.dedup ++ clearPaths) := by
  rw [high_index]
  intro w hw hm
  simp only [MeasuredClear.hotBank9, hot_eq, high, clearPaths, List.mem_cons, List.mem_append,
    List.mem_range'_1, List.mem_singleton, List.not_mem_nil, or_false] at hw hm
  (try dsimp only [Wire] at *); omega

theorem scratch_not_tree : scratch ∉ 836 :: (tableAddressTree high 0 1).indexWires.dedup ++ clearPaths := by
  rw [high_index]
  decide +kernel

theorem scratch_not_hot : scratch ∉ MeasuredClear.hotBank9 hot := by
  rw [MeasuredClear.hotBank9, hot_eq]
  decide +kernel

theorem tree_not_targets : ∀ w ∈ 836 :: List.ofFn low ++ (tableAddressTree high 0 1).indexWires.dedup ++ clearPaths,
    w ∉ clearData.map MeasuredClear.ClearPort.target := by
  rw [high_index, clearData_targets, low_eq]
  intro w hw hg
  have hb := mem_garb hg
  simp only [high, clearPaths, List.mem_cons, List.mem_append, List.mem_range'_1,
    List.mem_singleton, List.not_mem_nil, or_false] at hw
  (try dsimp only [Wire] at *); omega

theorem hot_targets : ∀ i, hot i ∈ clearData.map MeasuredClear.ClearPort.target := by
  intro i
  rw [clearData_targets]
  simp only [hot, garb, List.mem_range'_1]
  have := i.isLt
  (try dsimp only [Wire] at *); omega

theorem low_high_bits : [MeasuredClear.lowN9 low 0, MeasuredClear.lowN9 low 1, MeasuredClear.lowN9 low 2,
    MeasuredClear.lowN9 low 3, MeasuredClear.lowN9 low 4, MeasuredClear.lowN9 low 5,
    MeasuredClear.lowN9 low 6, MeasuredClear.lowN9 low 7, MeasuredClear.lowN9 low 8] ++ high =
      SelectSchedule18.bits := by
  decide +kernel

theorem zip_loaded (read : ConstantBit 262144 → Bool) (a : Nat) (t : BasisState) :
    ∀ (fs : List (Fin 262144 → ConstantBit 262144)) (ws : List Wire),
    wireValues ws t = fs.map (fun f => read (f (row (partner a)))) →
    ∀ p ∈ List.zipWith (fun f w => (⟨fun x => f (row (partner x)), true, w⟩ :
        MeasuredClear.ClearPort 262144)) fs ws,
      t p.target = (true && decide (read (p.ref a) = p.value))
  | [], _, _, p, hp => by simp at hp
  | _ :: _, [], _, p, hp => by simp at hp
  | f :: fs, w :: ws, h, p, hp => by
    have h' : t w = read (f (row (partner a))) ∧
        wireValues ws t = fs.map (fun f => read (f (row (partner a)))) := List.cons.inj h
    rw [List.zipWith_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · show t w = (true && decide (read (f (row (partner a))) = true))
      rw [h'.1]
      cases read (f (row (partner a))) <;> rfl
    · exact zip_loaded read a t fs ws h'.2 p hp

theorem loaded_clear (read : ConstantBit 262144 → Bool) (s : BasisState) (hs : SelectSchedule18.Input s) :
    MeasuredClear.LoadedClear9 clearData read low (tableAddressTree high 0 1) 836 (loaded read s) := by
  obtain ⟨tf, -, tg⟩ := loaded_facts read s hs
  have haddr : 512 * (tableAddressTree high 0 1).routeLabel (loaded read s) +
      MeasuredClear.hotAddress9 low (loaded read s) = tableAddressValue SelectSchedule18.bits s := by
    rw [MeasuredClear.splitAddress_value9, low_high_bits]
    apply tableAddressValue_congr
    intro w hw
    have hw' : (855 ≤ w ∧ w < 872) ∨ w = 537 := by
      simp only [SelectSchedule18.bits, List.mem_append, List.mem_range'_1, List.mem_singleton, List.not_mem_nil, or_false] at hw
      (try dsimp only [Wire] at *); omega
    apply tf w
    · intro h; have := mem_point h; (try dsimp only [Wire] at *); omega
    · intro h; have := mem_garb h; (try dsimp only [Wire] at *); omega
  have h836 : loaded read s 836 = true := by
    rw [tf 836 (fun h => by have := mem_point h; (try dsimp only [Wire] at *); omega) (fun h => by have := mem_garb h; (try dsimp only [Wire] at *); omega)]
    exact hs.1
  unfold MeasuredClear.LoadedClear9
  intro p hp
  rw [haddr, h836]
  apply zip_loaded read _ (loaded read s) slots garb _ p hp
  rw [tg, word, pointRefs_slots, List.map_map] <;> rfl

theorem clear_paths_clean (read : ConstantBit 262144 → Bool) (s : BasisState)
    (hs : SelectSchedule18.Input s) : Clean clearPaths (loaded read s) := by
  obtain ⟨tf, -, -⟩ := loaded_facts read s hs
  intro w hw
  simp only [clearPaths, List.mem_range'_1] at hw
  rw [tf w (fun h => by have := mem_point h; (try dsimp only [Wire] at *); omega) (fun h => by have := mem_garb h; (try dsimp only [Wire] at *); omega)]
  exact input_clean s hs w (by (try dsimp only [Wire] at *); omega) (by (try dsimp only [Wire] at *); omega) (by (try dsimp only [Wire] at *); omega)

theorem final_state (coeffs : Fin 262144 → PointCoeff) (Q : Point) (s : BasisState)
    (hs : SelectSchedule18.Input s) :
    clearRegister garb (loaded (readConstant coeffs Q) s) =
      pointWrite (SelectSchedule18.tablePoint coeffs Q (tableAddressValue SelectSchedule18.bits s)) s := by
  obtain ⟨tf, tp, -⟩ := loaded_facts (readConstant coeffs Q) s hs
  have hw : wireValues pointLogicalWires (loaded (readConstant coeffs Q) s) =
      wireValues pointLogicalWires (pointWrite (SelectSchedule18.tablePoint coeffs Q
        (tableAddressValue SelectSchedule18.bits s)) s) := by
    rw [tp, pointWrite_word, word, pointRefs_read] <;> rfl
  funext w
  by_cases hg : w ∈ garb
  · rw [clearRegister_clean garb _ w hg, pointWrite_frame _ _ w (fun h => point_not_garb h hg)]
    exact (input_garb s hs w hg).symm
  · rw [MeasuredClear.clearRegister_frame _ _ _ hg]
    by_cases hp : w ∈ pointLogicalWires
    · exact List.map_inj_left.mp hw w hp
    · rw [tf w hp hg, pointWrite_frame _ _ w hp]

/-! ### Programs -/

def selProgram (start : Nat) : Straight 262144 start (start + 131071) :=
  castFinish (by rw [selOps_measurements]) (lookupProgram 262144 selOps start)

def swapProgram (start : Nat) : Straight 262144 start start := literalProgram swapCircuit

theorem clear_finish (start : Nat) : start + clearData.length + (MeasuredClear.recordMeasurements
    (MeasuredClear.recordUnaryOps (tableAddressTree high 0 1) 836 clearPaths) + 511) = start + 1535 := by
  rw [clearData_length, clear_measurements, Nat.add_assoc] <;> rfl

def clearProgram (start : Nat) : Straight 262144 start (start + 1535) :=
  castFinish (clear_finish start)
    (MeasuredClear.measuredClear9 clearData low hot (tableAddressTree high 0 1) 836 scratch clearPaths start)

theorem program_finish (start : Nat) : start + 131071 + 1535 = start + 132606 := by
  rw [Nat.add_assoc] <;> rfl

def program (start : Nat) : Straight 262144 start (start + 132606) :=
  castFinish (program_finish start)
    (((selProgram start).append (swapProgram (start + 131071))).append (clearProgram (start + 131071)))

attribute [irreducible] selProgram swapProgram clearProgram program

def clearSource (read : ConstantBit 262144 → Bool) : AdaptiveCircuit :=
  (MeasuredClear.measuredClear9 clearData low hot (tableAddressTree high 0 1) 836 scratch clearPaths 0).instantiate
    read Fin.elim0

def source (read : ConstantBit 262144 → Bool) : AdaptiveCircuit :=
  ((lookupCircuit read selOps).seq (.unitary swapCircuit .done)).seq (clearSource read)

theorem sel_run (read : ConstantBit 262144 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((selProgram start).instantiate read history).run = (lookupCircuit read selOps).run := by
  rw [selProgram, castFinish_instantiate, lookupProgram_run]

theorem swap_run (read : ConstantBit 262144 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((swapProgram start).instantiate read history).run = (AdaptiveCircuit.unitary swapCircuit .done).run := by
  rw [swapProgram]
  exact literalProgram_run _ _ _

theorem clear_run (read : ConstantBit 262144 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((clearProgram start).instantiate read history).run = (clearSource read).run := by
  simp only [clearProgram, clearSource, castFinish_instantiate, MeasuredClear.measuredClear_run9]

theorem program_run (read : ConstantBit 262144 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((program start).instantiate read history).run = (source read).run := by
  rw [program, castFinish_instantiate,
    append_run_fixed _ _ _ _ _ (fun h => clear_run read _ h), AdaptiveCircuit.run_seq,
    append_run_fixed _ _ _ _ _ (fun h => swap_run read _ h), AdaptiveCircuit.run_seq,
    sel_run read start history]
  simp only [source, AdaptiveCircuit.run_seq]

/-! ### Semantics -/

theorem lmap_ket (f : BasisState → BasisState) (s : BasisState) :
    Finsupp.lmapDomain ℂ ℂ f (ket s) = ket (f s) := by
  simp [ket, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem coherent_restrict {p : AdaptiveCircuit} {I : State →ₗ[ℂ] State} {V W : BasisState → Prop}
    (h : CoherentlyImplementsOn p I V) (hw : ∀ s, W s → V s) : CoherentlyImplementsOn p I W := by
  obtain ⟨cs, ha, hm⟩ := h
  exact ⟨cs, ha.imp (fun _ _ hb s hs => hb s (hw s hs)), hm⟩

theorem sel_swap_coherent (read : ConstantBit 262144 → Bool) :
    CoherentlyImplementsOn ((lookupCircuit read selOps).seq (.unitary swapCircuit .done))
      ((Quantum.run swapCircuit).comp
        (Finsupp.lmapDomain ℂ ℂ (tableLookupState (selMask read) selBits 836)))
      SelectSchedule18.Input :=
  (coherent_restrict (sel_coherent read) (fun s hs => input_selPaths s hs)).seq
    (CoherentlyImplementsOn.unitary swapCircuit (fun _ => True)) (fun _ _ _ _ => trivial)

theorem clear_coherent (read : ConstantBit 262144 → Bool) :
    CoherentlyImplementsOn (clearSource read)
      (Finsupp.lmapDomain ℂ ℂ (clearRegister (clearData.map MeasuredClear.ClearPort.target)))
      (fun s => Clean clearPaths s ∧
        MeasuredClear.LoadedClear9 clearData read low (tableAddressTree high 0 1) 836 s) :=
  MeasuredClear.measuredClear_recycled_coherent9 clearData read low hot (tableAddressTree high 0 1) 836
    scratch clearPaths clear_layout hot_injective low_ne_hot hot_disjoint scratch_not_tree scratch_not_hot
    (by rw [clearData_targets]; exact garb_nodup) tree_not_targets hot_targets 0 Fin.elim0

theorem sel_swap_ket (read : ConstantBit 262144 → Bool) (s : BasisState) :
    ((Quantum.run swapCircuit).comp
        (Finsupp.lmapDomain ℂ ℂ (tableLookupState (selMask read) selBits 836))) (ket s) =
      ket (loaded read s) := by
  rw [LinearMap.comp_apply, lmap_ket, run_ket_agrees_classical _ _ swap_hp]
  rfl

theorem loaded_supported (read : ConstantBit 262144 → Bool) (s : BasisState)
    (hs : SelectSchedule18.Input s) :
    SupportedOn (fun s => Clean clearPaths s ∧
        MeasuredClear.LoadedClear9 clearData read low (tableAddressTree high 0 1) 836 s)
      (((Quantum.run swapCircuit).comp
        (Finsupp.lmapDomain ℂ ℂ (tableLookupState (selMask read) selBits 836))) (ket s)) := by
  rw [sel_swap_ket]
  exact supportedOn_ket _ _ ⟨clear_paths_clean read s hs, loaded_clear read s hs⟩

theorem source_ket (coeffs : Fin 262144 → PointCoeff) (Q : Point) (s : BasisState)
    (hs : SelectSchedule18.Input s) :
    ((Finsupp.lmapDomain ℂ ℂ (clearRegister (clearData.map MeasuredClear.ClearPort.target))).comp
      ((Quantum.run swapCircuit).comp
        (Finsupp.lmapDomain ℂ ℂ (tableLookupState (selMask (readConstant coeffs Q)) selBits 836)))) (ket s) =
      Finsupp.lmapDomain ℂ ℂ (fun s => pointWrite (SelectSchedule18.tablePoint coeffs Q
        (tableAddressValue SelectSchedule18.bits s)) s) (ket s) := by
  rw [LinearMap.comp_apply, sel_swap_ket, lmap_ket, lmap_ket, clearData_targets, final_state coeffs Q s hs]

theorem source_coherent (coeffs : Fin 262144 → PointCoeff) (Q : Point) :
    CoherentlyImplementsOn (source (readConstant coeffs Q))
      (Finsupp.lmapDomain ℂ ℂ (fun s => pointWrite (SelectSchedule18.tablePoint coeffs Q
        (tableAddressValue SelectSchedule18.bits s)) s)) SelectSchedule18.Input := by
  have h12 := sel_swap_coherent (readConstant coeffs Q)
  have h123 := h12.seq (clear_coherent (readConstant coeffs Q)) (by
    intro s hs
    rw [sel_swap_ket]
    exact supportedOn_ket _ _ ⟨clear_paths_clean _ s hs, loaded_clear _ s hs⟩)
  rw [source]
  refine h123.congrIdeal (fun s hs => ?_)
  rw [LinearMap.comp_apply, sel_swap_ket, lmap_ket, lmap_ket, clearData_targets, final_state coeffs Q s hs]

theorem program_coherent (coeffs : Fin 262144 → PointCoeff) (Q : Point) (start : Nat)
    (history : Fin start → Bool) :
    CoherentlyImplementsOn ((program start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (fun s => pointWrite (SelectSchedule18.tablePoint coeffs Q
        (tableAddressValue SelectSchedule18.bits s)) s)) SelectSchedule18.Input := by
  unfold CoherentlyImplementsOn
  rw [program_run]
  exact source_coherent coeffs Q

/-! ### Resources -/

theorem selOps_physical : ∀ op ∈ selOps, op.Physical := by
  rw [selOps]
  apply unaryLookupOps_physical _ _ _ _ sel_layout
  intro l c hc g hg
  simp only [selLeaf, lookupLeafGates, List.mem_map] at hg
  obtain ⟨⟨ref, target⟩, hm, rfl⟩ := hg
  change c ≠ target
  have ht : target ∈ pointLogicalWires ∨ target ∈ garb := by
    rcases List.mem_append.mp hm with h | h
    · exact Or.inl (List.of_mem_zip h).2
    · exact Or.inr (List.of_mem_zip h).2
  have hc' : c = 836 ∨ (519 ≤ c ∧ c < 536) := by
    simp only [selPaths, List.mem_cons, List.mem_range'_1] at hc
    (try dsimp only [Wire] at *); omega
  intro he
  subst he
  rcases ht with h | h
  · have := mem_point h; (try dsimp only [Wire] at *); omega
  · have := mem_garb h; (try dsimp only [Wire] at *); omega

theorem sel_wellFormed (start : Nat) : (selProgram start).WellFormed := by
  rw [selProgram, castFinish_wellFormed]
  exact lookupProgram_wellFormed _ selOps_physical _

theorem swap_wellFormed (start : Nat) : (swapProgram start).WellFormed := by
  rw [swapProgram]
  exact literalProgram_wellFormed _ swap_wf

theorem clear_wellFormed (start : Nat) : (clearProgram start).WellFormed := by
  rw [clearProgram, castFinish_wellFormed]
  generalize htree : tableAddressTree high 0 1 = tree
  exact MeasuredClear.measuredClear_wellFormed9 clearData low hot tree 836 scratch clearPaths
    (by rw [← htree]; exact clear_layout) hot_injective low_ne_hot
    (by rw [← htree]; exact scratch_not_tree) scratch_not_hot start

theorem program_wellFormed (start : Nat) : (program start).WellFormed := by
  have h := straight_append_wellFormed _ _
    (straight_append_wellFormed _ _ (sel_wellFormed start) (swap_wellFormed (start + 131071)))
    (clear_wellFormed (start + 131071))
  rw [program, castFinish_wellFormed]
  exact h

theorem selLeaf_length (l : Nat) (q : Wire) : (selLeaf l q).length ≤ 1026 := by
  rw [selLeaf, lookupLeafGates, List.length_map, List.length_append, List.length_zip, List.length_zip,
    pointRefs_length, pointRefs_length, point_length, garb_length] <;> decide +kernel

theorem sel_slots (start : Nat) : (selProgram start).gateSlots ≤ 1026 * (131071 + 1) + 10 * 131071 := by
  rw [selProgram, castFinish_gateSlots, lookupProgram_slots]
  have h := unaryLookupOps_slots_le selLeaf 1026 selLeaf_length (tableAddressTree selBits 0 1) 836 selPaths
  rw [sel_nodes] at h
  rw [selOps]
  exact h

theorem swap_slots (start : Nat) : (swapProgram start).gateSlots = 3 * 513 := by
  rw [swapProgram, literalProgram_slots, swapCircuit, swapWords_length, point_length, garb_length,
    Nat.min_self]

theorem clear_slots (start : Nat) :
    (clearProgram start).gateSlots = 2048 * 513 * 512 + 10 * 511 + 4594 := by
  rw [clearProgram, castFinish_gateSlots, MeasuredClear.measuredClear_slots9 _ _ _ _ _ _ _ clear_layout,
    clearData_length, clear_leaves, clear_nodes]

theorem program_slots (start : Nat) : (program start).gateSlots ≤ 1000000000 := by
  rw [program, castFinish_gateSlots, Straight.gateSlots_append, Straight.gateSlots_append, swap_slots,
    clear_slots]
  exact Nat.le_trans (Nat.add_le_add_right (Nat.add_le_add_right (sel_slots start) _) _) (by decide +kernel)

/-- Every wire the first window touches. -/
def support : List Wire := 836 :: SelectSchedule18.bits ++ selPaths ++ pointLogicalWires ++ garb

theorem mem_support {w : Nat} (h : w = 836 ∨ (855 ≤ w ∧ w < 872) ∨ w = 537 ∨ (519 ≤ w ∧ w < 536) ∨
    (263 ≤ w ∧ w < 519) ∨ (580 ≤ w ∧ w < 836) ∨ w = 838 ∨ (872 ≤ w ∧ w < 1385)) : w ∈ support := by
  simp only [support, SelectSchedule18.bits, selPaths, pointLogicalWires, pointCorrectionX,
    pointCorrectionYInf, garb, List.mem_cons, List.mem_append, List.mem_range'_1, List.mem_singleton, List.not_mem_nil, or_false]
  (try dsimp only [Wire] at *); omega

theorem support_range : support ⊆ List.range 1616 := by
  intro w hw
  rw [List.mem_range]
  simp only [support, SelectSchedule18.bits, selPaths, pointLogicalWires, pointCorrectionX,
    pointCorrectionYInf, garb, List.mem_cons, List.mem_append, List.mem_range'_1,
    List.mem_singleton, List.not_mem_nil, or_false] at hw
  (try dsimp only [Wire] at *); omega

theorem sel_support (start : Nat) : straightWires (selProgram start) ⊆ support := by
  have hl : ∀ op ∈ selOps, lookupOpWires op ⊆ support := by
    rw [selOps]
    apply unaryLookupOps_support
    · exact mem_support (Or.inl rfl)
    · intro w hw
      simp only [selPaths, List.mem_range'_1] at hw
      exact mem_support (by (try dsimp only [Wire] at *); omega)
    · intro w hw
      have hb := (tableAddressTree_mem_index selBits 0 1 w).mp hw
      simp only [selBits, List.mem_append, List.mem_range'_1, List.mem_singleton, List.not_mem_nil, or_false] at hb
      exact mem_support (by (try dsimp only [Wire] at *); omega)
    · intro label q hq
      apply lookupLeafGates_support _ _ _ hq
      intro port hp
      rcases List.mem_append.mp hp with h | h
      · have := mem_point (List.of_mem_zip h).2
        exact mem_support (by (try dsimp only [Wire] at *); omega)
      · have := mem_garb (List.of_mem_zip h).2
        exact mem_support (by (try dsimp only [Wire] at *); omega)
  rw [selProgram, straightWires_castFinish, lookupProgram_support]
  intro w hw
  obtain ⟨op, hop, hw⟩ := List.mem_flatMap.mp hw
  exact hl op hop hw

theorem swap_support (start : Nat) : straightWires (swapProgram start) ⊆ support := by
  rw [swapProgram, literalProgram_support]
  intro w hw
  rcases swap_wires w hw with h | h | h
  · exact mem_support (by (try dsimp only [Wire] at *); omega)
  · have := mem_point h
    exact mem_support (by (try dsimp only [Wire] at *); omega)
  · have := mem_garb h
    exact mem_support (by (try dsimp only [Wire] at *); omega)

theorem clear_support (start : Nat) : straightWires (clearProgram start) ⊆ support := by
  rw [clearProgram, straightWires_castFinish, WEX.support_agrees]
  have hsc : scratch ∈ clearData.map MeasuredClear.ClearPort.target := by
    rw [clearData_targets]
    simp [scratch, garb]
  apply List.Subset.trans (MeasuredClear.measuredClear_static9 _ _ _ _ _ _ _ hsc start)
  intro w hw
  rw [MeasuredClear.clearSupport9, clearData_targets, high_index, MeasuredClear.hotBank9, hot_eq,
    low_eq] at hw
  simp only [high, clearPaths, garb, List.mem_cons, List.mem_append, List.mem_range'_1,
    List.mem_singleton, List.not_mem_nil, or_false] at hw
  exact mem_support (by (try dsimp only [Wire] at *); omega)

theorem program_support (start : Nat) : straightWires (program start) ⊆ support := by
  rw [program, straightWires_castFinish, straightWires_append, straightWires_append]
  exact List.append_subset.mpr ⟨List.append_subset.mpr ⟨sel_support start, swap_support _⟩,
    clear_support _⟩

theorem sel_residue (start : Nat) : residue (selProgram start) = 0 := by
  rw [selProgram, residue_cast, residue_lookup, selOps]
  apply WEXCredit.residue_unary
  intro label root
  unfold selLeaf
  generalize ((pointRefs (row (2 * label))).zip pointLogicalWires ++
    (pointRefs (row (2 * label + 1))).zip garb) = ports
  unfold lookupLeafGates
  induction ports with
  | nil => rfl
  | cons p ps ih => simpa [templateResidue, tCost] using ih

theorem swap_residue (start : Nat) : residue (swapProgram start) = 0 := by
  rw [swapProgram]
  exact residue_literal_HPFree _ swap_hp

theorem clear_residue (start : Nat) : residue (clearProgram start) = 0 := by
  rw [clearProgram, residue_cast]
  exact MeasuredClear.measuredClear_residue9 _ _ _ _ _ _ _ _

theorem program_residue (start : Nat) : residue (program start) = 0 := by
  rw [program, residue_cast, residue_append, residue_append, sel_residue, swap_residue, clear_residue] <;> rfl

theorem sel_added (start : Nat) : added (selProgram start) = 131071 := by
  have h := exact_t (selProgram start) (sel_residue start) (fun _ => false) (fun _ => false)
  have ht : ((selProgram start).instantiate (fun _ => false) (fun _ => false)).tCount = 7 * 131071 := by
    rw [selProgram, castFinish_instantiate, lookupProgram_tCount, selOps_circuit,
      tableLookupProgram_tCount (selMask (fun _ => false)) selBits selPaths 836 (by decide +kernel) (by decide +kernel)] <;> rfl
  exact Nat.eq_of_mul_eq_mul_left (by decide +kernel) (h.symm.trans ht)

theorem swap_added (start : Nat) : added (swapProgram start) = 513 := by
  rw [swapProgram, added_literal, swapCircuit, swapWords_ccx, point_length, garb_length, Nat.min_self]

theorem clear_added (start : Nat) : added (clearProgram start) = 1013 := by
  have h := exact_t (clearProgram start) (clear_residue start) (fun _ => false) (fun _ => false)
  have ht : ((clearProgram start).instantiate (fun _ => false) (fun _ => false)).tCount = 7 * 1013 := by
    rw [clearProgram, castFinish_instantiate,
      MeasuredClear.measuredClear_tCount9 _ _ _ _ _ _ _ clear_layout, clear_nodes] <;> rfl
  exact Nat.eq_of_mul_eq_mul_left (by decide +kernel) (h.symm.trans ht)

theorem program_added (start : Nat) : added (program start) = 132597 := by
  rw [program, added_cast, added_append, added_append, sel_added, swap_added, clear_added] <;> rfl

theorem program_credit (coeffs : Fin 262144 → PointCoeff) (Q : Point) (start : Nat)
    (history : Fin start → Bool) : added (program start) = 132597 := program_added start

theorem program_tCount (coeffs : Fin 262144 → PointCoeff) (Q : Point) (start : Nat)
    (history : Fin start → Bool) :
    ((program start).instantiate (readConstant coeffs Q) history).tCount = 928179 := by
  rw [exact_t _ (program_residue start), program_added] <;> rfl

/-! ### The window -/

def windowGeneric {n : Nat} (rows : Fin 262144 → Fin n) : Single.Window n :=
  ⟨SelectSchedule18.bits.reverse, 132606, fun start => reindexStraight rows (program start)⟩

theorem window_law_generic {n : Nat} (coeffs : Fin n → PointCoeff) (rows : Fin 262144 → Fin n)
    (init : Point → Nat → Point)
    (hcoeff : ∀ Q, order • Q = 0 → ∀ a : Fin 262144,
      constantPoint Q (coeffs (rows a)) = init Q a.val) :
    Single.WindowLaw coeffs (windowGeneric rows) (SelectSchedule18.update init)
      SelectSchedule18.Input := by
  intro Q hQ hn start history
  have hvalid := program_coherent (fun a => coeffs (rows a)) Q start history
  have hupdate : (fun s => pointWrite
      (SelectSchedule18.tablePoint (fun a => coeffs (rows a)) Q
        (tableAddressValue SelectSchedule18.bits s)) s) = SelectSchedule18.update init Q := by
    funext s
    unfold SelectSchedule18.tablePoint SelectSchedule18.update
    have hbound : tableAddressValue SelectSchedule18.bits s < 262144 := by
      have hb := tableAddressValue_lt SelectSchedule18.bits s
      have hlen : SelectSchedule18.bits.length = 18 := by decide +kernel
      simpa only [hlen] using hb
    simp only [Nat.mod_eq_of_lt hbound]
    rw [hcoeff Q hQ]
  rw [hupdate] at hvalid
  unfold windowGeneric
  rw [reindexStraight_instantiate,
    readConstant_reindex rows (fun a => coeffs (rows a)) coeffs Q (fun _ => rfl)]
  exact hvalid

theorem window_wellFormed {n : Nat} (rows : Fin 262144 → Fin n) (start : Nat) :
    ((windowGeneric rows).program start).WellFormed := by
  unfold windowGeneric
  exact (reindexStraight_wellFormed rows (program start)).mpr (program_wellFormed start)

theorem window_slots {n : Nat} (rows : Fin 262144 → Fin n) (start : Nat) :
    ((windowGeneric rows).program start).gateSlots ≤ 1000000000 := by
  unfold windowGeneric
  rw [reindexStraight_gateSlots]
  exact program_slots start

theorem window_support {n : Nat} (rows : Fin 262144 → Fin n) (start : Nat) :
    straightWires ((windowGeneric rows).program start) ⊆ support := by
  unfold windowGeneric
  rw [straightWires_reindex]
  exact program_support start

theorem window_t {n : Nat} (coeffs : Fin n → PointCoeff) (rows : Fin 262144 → Fin n)
    (Q : Point) (start : Nat) (history : Fin start → Bool) :
    (((windowGeneric rows).program start).instantiate (readConstant coeffs Q) history).tCount = 928179 := by
  unfold windowGeneric
  rw [reindexStraight_instantiate,
    readConstant_reindex rows (fun a => coeffs (rows a)) coeffs Q (fun _ => rfl)]
  exact program_tCount (fun a => coeffs (rows a)) Q start history

theorem window_credit {n : Nat} (coeffs : Fin n → PointCoeff) (rows : Fin 262144 → Fin n)
    (Q : Point) (start : Nat) (history : Fin start → Bool) :
    added ((windowGeneric rows).program start) = 132597 := by
  unfold windowGeneric
  rw [added_reindex]
  exact program_added start

end
end ShorECDLP.Entrant.First18


namespace ShorECDLP.Entrant.Single
open Quantum Secp256k1 Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] fourierOutcomes
theorem select18_nodup : SelectSchedule18.bits.Nodup := by decide +kernel

theorem select18_not_point : ∀ v ∈ SelectSchedule18.bits, v ∉ pointLogicalWires := by decide +kernel

theorem select18_clean (s : BasisState) (hs : FirstWindowInput s)
    (hz : Clean streamAddress s) : Clean SelectSchedule18.bits s := by
  intro v hv
  simp only [SelectSchedule18.bits,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with hv | rfl
  · have hb : 855 ≤ v ∧ v < 872 := by simpa only [List.mem_range'_1] using hv
    by_cases he : v = 871
    · subst v; exact hs.2 871 (by decide +kernel) (by decide +kernel)
    · apply hz v
      simp only [streamAddress, List.mem_range'_1]
      dsimp only [Wire] at *
      omega
  · exact hs.2 537 (by decide +kernel) (by decide +kernel)

theorem select18_assigned_digit (s : BasisState) (input : List Bool)
    (hi : input.length = SelectSchedule18.bits.length) :
    tableAddressValue SelectSchedule18.bits (phaseWordState SelectSchedule18.bits input s) = boolWordToNat input := by
  have he (ws : List Wire) (t : BasisState) :
      tableAddressValue ws t = boolWordToNat (wireValues ws t) := by
    induction ws with
    | nil => rfl
    | cons w ws ih =>
      change (t w).toNat + 2 * tableAddressValue ws t =
        (t w).toNat + 2 * boolWordToNat (wireValues ws t)
      rw [ih]
  rw [he,phaseWordState_word _ select18_nodup input hi s]


theorem select18_window_point_sum_generic (init : Point → Nat → Point) (Q : Point) (prior output : List Bool)
    (s : BasisState) (hs : FirstWindowInput s) (hz : Clean streamAddress s) :
    fourierBranch .inverse SelectSchedule18.bits.reverse prior output
      (Finsupp.lmapDomain ℂ ℂ (SelectSchedule18.update init Q)
        (Quantum.run (SelectSchedule18.bits.map Gate.H) (ket s))) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 18) •
        ((fourierOutcomes 18).map (fun input =>
          fourierBitAmplitude .inverse input.reverse prior output •
            ket (pointWrite (init Q (boolWordToNat input)) s))).sum := by
  have hlen : SelectSchedule18.bits.length = 18 := by decide +kernel
  rw [window_branch_uniform .inverse SelectSchedule18.bits select18_nodup
    (SelectSchedule18.update init Q) prior output s (select18_clean s hs hz) (by
      intro input hi
      have he : SelectSchedule18.bits.map (SelectSchedule18.update init Q (phaseWordState SelectSchedule18.bits input s)) =
          SelectSchedule18.bits.map (phaseWordState SelectSchedule18.bits input s) := by
        apply List.map_congr_left
        intro v hv
        exact pointWrite_frame _ _ v (select18_not_point v hv)
      rw [he]
      exact phaseWordState_word _ select18_nodup input
        ((fourierOutcomes_mem _ _).mp hi) s), hlen]
  apply congrArg (fun ψ : State => (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 18) • ψ)
  apply congrArg List.sum
  apply List.map_congr_left
  intro input hi
  unfold SelectSchedule18.update
  rw [select18_assigned_digit s input (by simpa only [hlen] using (fourierOutcomes_mem _ _).mp hi),
    clear_assigned_point _ input s (select18_clean s hs hz) select18_not_point]
end
end ShorECDLP.Entrant.Single


namespace ShorECDLP.Entrant.SelectSchedule18
open Quantum Secp256k1 Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
theorem input_of_strong (s : BasisState) (hs : FirstWindowInput s) : Input s := by
  refine ⟨hs.1,?_⟩
  intro v hv ha
  apply hs.2 v hv
  intro hh
  apply ha
  simp only [streamAddress] at hh
  change v ∈ List.range' 855 17 ++ [537]
  apply List.mem_append_left
  have hb : 855 ≤ v ∧ v < 871 := by simpa only [List.mem_range'_1] using hh
  simp only [List.mem_range'_1]
  dsimp only [Wire] at *
  omega

theorem input_update (s : BasisState) (hs : Input s) (w : Wire) (hw : w∈bits) (b : Bool) :
    Input (s[w↦b]) := by
  have ne : (836:Wire)≠w := by
    simp only [bits,List.mem_append,List.mem_range'_1,List.mem_cons,List.not_mem_nil,or_false] at hw
    dsimp only [Wire] at *
    omega
  refine ⟨by simpa only [upd,if_neg ne] using hs.1,?_⟩
  intro v hv ha
  have nvw : v≠w := by intro e; exact ha (e ▸ hw)
  simpa only [upd,if_neg nvw] using hs.2 v hv ha


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
end ShorECDLP.Entrant.SelectSchedule18

