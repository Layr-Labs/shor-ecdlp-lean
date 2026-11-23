import ShorECDLP.Submission.Entrant.RootPass
import ShorECDLP.Submission.Entrant.WideBank8

/-! Four-pass global-optimal SelectSwap loader for the 18-bit joint first window.

Splits the 513-wire point register into four passes `((2, 394), (4, 74), (5, 34), (6, 11))`
using the 1,065..1,069 clean non-point ancillas in `List.range 1613` (plus unwritten trailing
point wires in passes 1 and 2, reset to `|0⟩` before later passes write them):
- Pass 1 (`k=2`, 394 bits): 16-bit QROM (`65,535`) + `3 × 394 = 1,182` swaps
- Pass 2 (`k=4`,  74 bits): 14-bit QROM (`16,383`) + `15 × 74 = 1,110` swaps
- Pass 3 (`k=5`,  34 bits): 13-bit QROM (` 8,191`) + `31 × 34 = 1,054` swaps
- Pass 4 (`k=6`,  11 bits): 12-bit QROM (` 4,095`) + `63 × 11 =   693` swaps
- One fused 9-bit measured-clear phase fixup (`511 + 502 = 1,013` Toffolis) over all
  4,039 garbage measurement records, followed by `RootPass.seedProgram 836` (`-5` root hits).

Total: `99,251` Toffolis (down from `132,595`, saving `33,344` Toffolis = `133,376` T-model gates)
and `99,265` measurement records (down from `132,606`), within `List.range 1613`. -/

set_option Elab.async false

namespace ShorECDLP.Entrant.MeasuredClear
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

theorem fixupFactor9_append {n : Nat} (d1 d2 : List (ClearPort n)) (o1 o2 : List Bool)
    (h : o1.length = d1.length) (read : ConstantBit n → Bool) (low : Fin 9 → Wire) (hot : Fin 512 → Wire)
    (tree : UnaryActionTree) (root : Wire) (s : BasisState) :
    fixupFactor9 (d1 ++ d2) (o1 ++ o2) read low hot tree root s =
      fixupFactor9 d1 o1 read low hot tree root s * fixupFactor9 d2 o2 read low hot tree root s := by
  have hz : (d1 ++ d2).zip ((o1 ++ o2).map boolRecord) =
      d1.zip (o1.map boolRecord) ++ d2.zip (o2.map boolRecord) := by
    rw [List.map_append]
    exact List.zip_append (by simp [h])
  simp only [fixupFactor9, phaseLookupFactor, logicalPorts9, hz, phasePorts9, List.flatMap_append,
    recordTargets_append, xorPhase_append]

theorem fixupFactor9_loaded {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (read : ConstantBit n → Bool) (low : Fin 9 → Wire) (hot : Fin 512 → Wire)
    (tree : UnaryActionTree) (root : Wire) (paths : List Wire)
    (hi : Function.Injective hot) (hdlow : ∀ i j, low i ≠ hot j)
    (hbank : (hotBank9 hot).Disjoint (root :: tree.indexWires.dedup ++ paths))
    (t u : BasisState) (hhot : HotClean9 hot t)
    (hw : ∀ p ∈ data, u p.target =
      (t root && decide (read (p.ref (512 * tree.routeLabel t + hotAddress9 low t)) = p.value))) :
    fixupFactor9 data outcomes read low hot tree root t =
      registerXPhase (data.map ClearPort.target) outcomes u := by
  let prepared := Classical.run (hotPrepare9 low hot) t
  have hframe (w : Wire) (hw : w ∈ root :: tree.indexWires.dedup ++ paths) : prepared w = t w :=
    hotPrepare_frame9 low hot t w (by
      intro i he
      exact List.disjoint_left.mp hbank (List.mem_ofFn.mpr ⟨i, he.symm⟩) hw)
  have hroute : tree.routeLabel prepared = tree.routeLabel t := by
    apply tree.routeLabel_congr prepared t
    intro w hw
    exact hframe w (by simp [hw])
  let selected : Fin 512 := ⟨hotAddress9 low t, hotAddress_bound9 low t⟩
  apply phaseFactor_loaded9 data outcomes read hot tree root u prepared selected
  · intro i
    simpa only [Fin.ext_iff] using hotPrepare_marker9 low hot hi hdlow t hhot i
  · intro p hp
    rw [hframe root (by simp), hroute]
    exact hw p hp

end
end ShorECDLP.Entrant.MeasuredClear

namespace ShorECDLP.Entrant.First18Split
open Quantum Challenge Secp256k1 Paper2607_13816 Paper2607_13816.ChallengeMigration AndGadget WEXCredit
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false

/-! ### Part 1: Generic `k`-bit binary SelectSwap tree -/

def chunks {α : Type} : Nat → Nat → List α → List (List α)
  | 0, _, _ => []
  | c + 1, m, xs => xs.take m :: chunks c m (xs.drop m)

theorem chunks_length {α : Type} : ∀ (c m : Nat) (xs : List α), (chunks c m xs).length = c
  | 0, _, _ => rfl
  | c + 1, m, xs => by simp [chunks, chunks_length c m]

theorem chunks_mem_length {α : Type} : ∀ (c m : Nat) (xs : List α),
    xs.length = c * m → ∀ r ∈ chunks c m xs, r.length = m
  | 0, _, _, _, _, hr => by simp [chunks] at hr
  | c + 1, m, xs, hl, r, hr => by
    simp only [chunks, List.mem_cons] at hr
    rcases hr with rfl | hr
    · rw [List.length_take, hl, Nat.add_mul, Nat.one_mul]; omega
    · exact chunks_mem_length c m (xs.drop m) (by rw [List.length_drop, hl, Nat.add_mul, Nat.one_mul]; omega) r hr

theorem chunks_flatten {α : Type} : ∀ (c m : Nat) (xs : List α),
    xs.length = c * m → (chunks c m xs).flatten = xs
  | 0, _, xs, hl => by
    simp only [chunks, List.flatten_nil]
    exact (List.eq_nil_of_length_eq_zero (by simpa using hl)).symm
  | c + 1, m, xs, hl => by
    rw [chunks, List.flatten_cons, chunks_flatten c m (xs.drop m)
      (by rw [List.length_drop, hl, Nat.add_mul, Nat.one_mul]; omega), List.take_append_drop]

def evens {α : Type} : List α → List α
  | a :: _ :: rest => a :: evens rest
  | xs => xs

def odds {α : Type} : List α → List α
  | _ :: b :: rest => b :: odds rest
  | _ => []

def pairSwaps (c : Wire) : List (List Wire) → Circuit
  | a :: b :: rest => First18.swapWords c a b ++ pairSwaps c rest
  | _ => []

def swapTree : List Wire → List (List Wire) → Circuit
  | [], _ => []
  | c :: cs, regs => pairSwaps c regs ++ swapTree cs (evens regs)

def treeGarbs : List Wire → List (List Wire) → List (List Wire)
  | [], _ => []
  | _ :: cs, regs => odds regs ++ treeGarbs cs (evens regs)

def oddAddrs (k : Nat) : List (Nat → Nat) :=
  List.ofFn fun j : Fin (2 ^ k) => fun x => 2 * (2 ^ k * (x / 2 ^ (k + 1)) + j.val) + (1 - x % 2)

def treeAddrs : Nat → List (Nat → Nat)
  | 0 => []
  | k + 1 => oddAddrs k ++ (treeAddrs k).map (fun g => fun x => 2 * g (x / 2) + x % 2)

theorem evens_length {α : Type} : ∀ (n : Nat) (xs : List α),
    xs.length = 2 * n → (evens xs).length = n
  | 0, [], _ => rfl
  | 0, _ :: _, h => by simp at h
  | n + 1, _ :: _ :: rest, h => by
    simp only [evens, List.length_cons]
    have h' : rest.length = 2 * n := by simp at h; omega
    rw [evens_length n rest h']
  | n + 1, [], h => by simp at h
  | n + 1, [_], h => by simp at h; omega

theorem odds_length {α : Type} : ∀ (n : Nat) (xs : List α),
    xs.length = 2 * n → (odds xs).length = n
  | 0, [], _ => rfl
  | 0, _ :: _, h => by simp at h
  | n + 1, _ :: _ :: rest, h => by
    simp only [odds, List.length_cons]
    have h' : rest.length = 2 * n := by simp at h; omega
    rw [odds_length n rest h']
  | n + 1, [], h => by simp at h
  | n + 1, [_], h => by simp at h; omega

theorem mem_evens_sub {α : Type} : ∀ (xs : List α) {x : α}, x ∈ evens xs → x ∈ xs
  | [], _, h => h
  | [a], _, h => h
  | a :: b :: rest, x, h => by
    simp only [evens, List.mem_cons] at h ⊢
    rcases h with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (mem_evens_sub rest h))

theorem mem_odds_sub {α : Type} : ∀ (xs : List α) {x : α}, x ∈ odds xs → x ∈ xs
  | [], _, h => by simp [odds] at h
  | [_], _, h => by simp [odds] at h
  | a :: b :: rest, x, h => by
    simp only [odds, List.mem_cons] at h ⊢
    rcases h with rfl | h
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (mem_odds_sub rest h))

theorem mem_evens_or_odds {α : Type} : ∀ (xs : List α) {x : α},
    x ∈ xs ↔ x ∈ evens xs ∨ x ∈ odds xs
  | [], x => by simp [evens, odds]
  | [a], x => by simp [evens, odds]
  | a :: b :: rest, x => by
    simp only [evens, odds, List.mem_cons, mem_evens_or_odds rest]
    tauto

theorem evens_head {α : Type} : ∀ (a : α) (rest : List α),
    ∃ t, evens (a :: rest) = a :: t
  | a, [] => ⟨[], rfl⟩
  | a, _ :: rest => ⟨evens rest, rfl⟩

theorem nodup_evens_odds {α : Type} : ∀ (xs : List (List α)),
    xs.flatten.Nodup → (evens xs).flatten.Nodup ∧ (odds xs).flatten.Nodup ∧
      (evens xs).flatten.Disjoint (odds xs).flatten
  | [], _ => ⟨List.nodup_nil, List.nodup_nil, List.disjoint_nil_left _⟩
  | [a], h => ⟨by simpa [evens] using h, List.nodup_nil, List.disjoint_nil_right _⟩
  | a :: b :: rest, h => by
    simp only [List.flatten_cons, List.nodup_append] at h
    obtain ⟨ha, ⟨hb, hrest, hbr⟩, habr⟩ := h
    obtain ⟨he, ho, heo⟩ := nodup_evens_odds rest hrest
    have ha_sub : ∀ x ∈ a, ∀ y ∈ rest.flatten, x ≠ y :=
      fun x hx y hy => habr x hx y (List.mem_append_right _ hy)
    have ha_b : ∀ x ∈ a, ∀ y ∈ b, x ≠ y :=
      fun x hx y hy => habr x hx y (List.mem_append_left _ hy)
    have he_sub : ∀ y ∈ (evens rest).flatten, y ∈ rest.flatten := fun y hy => by
      obtain ⟨r, hr, hyr⟩ := List.mem_flatten.mp hy
      exact List.mem_flatten.mpr ⟨r, mem_evens_sub rest hr, hyr⟩
    have ho_sub : ∀ y ∈ (odds rest).flatten, y ∈ rest.flatten := fun y hy => by
      obtain ⟨r, hr, hyr⟩ := List.mem_flatten.mp hy
      exact List.mem_flatten.mpr ⟨r, mem_odds_sub rest hr, hyr⟩
    refine ⟨?_, ?_, ?_⟩
    · simp only [evens, List.flatten_cons, List.nodup_append]
      exact ⟨ha, he, fun x hx y hy => ha_sub x hx y (he_sub y hy)⟩
    · simp only [odds, List.flatten_cons, List.nodup_append]
      exact ⟨hb, ho, fun x hx y hy => hbr x hx y (ho_sub y hy)⟩
    · apply List.disjoint_left.mpr
      intro x hx hy
      simp only [evens, odds, List.flatten_cons, List.mem_append] at hx hy
      rcases hx with hxa | hxe <;> rcases hy with hyb | hyo
      · exact ha_b x hxa x hyb rfl
      · exact ha_sub x hxa x (ho_sub x hyo) rfl
      · exact hbr x hyb x (he_sub x hxe) rfl
      · exact List.disjoint_left.mp heo hxe hyo

theorem treeGarbs_nodup_and_mem : ∀ (ctrl : List Wire) (regs : List (List Wire)),
    regs.length = 2 ^ ctrl.length → regs.flatten.Nodup →
    (treeGarbs ctrl regs).flatten.Nodup ∧
    ∀ a rest, regs = a :: rest →
      (∀ w, w ∈ (treeGarbs ctrl regs).flatten ↔ w ∈ rest.flatten) ∧
      a.Disjoint (treeGarbs ctrl regs).flatten
  | [], regs, hl, hnd => by
    refine ⟨List.nodup_nil, fun a rest he => ?_⟩
    subst he
    have hnil : rest = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst hnil
    exact ⟨fun w => by simp [treeGarbs], List.disjoint_nil_right _⟩
  | c :: cs, regs, hl, hnd => by
    have h2 : regs.length = 2 * 2 ^ cs.length := by
      simpa only [List.length_cons, pow_succ, Nat.mul_comm] using hl
    obtain ⟨he_nd, ho_nd, heo⟩ := nodup_evens_odds regs hnd
    obtain ⟨ih_nd, ih_mem⟩ := treeGarbs_nodup_and_mem cs (evens regs) (evens_length _ _ h2) he_nd
    have hdisj_og : (odds regs).flatten.Disjoint (treeGarbs cs (evens regs)).flatten := by
      apply List.disjoint_left.mpr
      intro w hwo hwg
      obtain ⟨r, hr, hwr⟩ := List.mem_flatten.mp hwg
      have hne_ev : evens regs ≠ [] := by
        intro hnil; have := evens_length _ _ h2; rw [hnil] at this
        exact absurd this.symm (Nat.ne_of_gt (pow_pos (by decide) cs.length))
      cases hev : evens regs with
      | nil => exact hne_ev hev
      | cons a' t' =>
        rw [hev] at ih_mem hwg
        have hwt := (ih_mem a' t' rfl).1 w |>.mp hwg
        exact List.disjoint_left.mp heo (by rw [hev]; exact List.mem_flatten.mpr (by
          obtain ⟨q, hq, hwq⟩ := List.mem_flatten.mp hwt
          exact ⟨q, List.mem_cons_of_mem _ hq, hwq⟩)) hwo
    refine ⟨?_, fun a rest he => ?_⟩
    · simp only [treeGarbs, List.flatten_append, List.nodup_append]
      exact ⟨ho_nd, ih_nd, fun x hx y hy hxy => List.disjoint_left.mp hdisj_og hx (hxy ▸ hy)⟩
    · subst he
      cases rest with
      | nil =>
        have hp : 1 ≤ 2 ^ cs.length := Nat.one_le_pow _ _ (by decide)
        simp at h2; omega
      | cons b tail =>
        simp only [treeGarbs, evens, odds, List.flatten_append, List.flatten_cons]
        obtain ⟨ih_iff, ih_da⟩ := ih_mem a (evens tail) rfl
        have ih_iff' : ∀ w, w ∈ (treeGarbs cs (a :: evens tail)).flatten ↔ w ∈ (evens tail).flatten := by
          intro w; simpa only [evens] using ih_iff w
        have ha_b : a.Disjoint b := by
          simp only [List.flatten_cons, List.nodup_append] at hnd
          exact List.disjoint_left.mpr (fun x hx hy => hnd.2.2 x hx x (List.mem_append_left _ hy) rfl)
        have ha_ot : a.Disjoint (odds tail).flatten := by
          apply List.disjoint_left.mpr
          intro x hxa hxo
          simp only [List.flatten_cons, List.nodup_append] at hnd
          obtain ⟨r, hr, hxr⟩ := List.mem_flatten.mp hxo
          exact hnd.2.2 x hxa x (List.mem_append_right _ (List.mem_flatten.mpr ⟨r, mem_odds_sub tail hr, hxr⟩)) rfl
        refine ⟨fun w => ?_, ?_⟩
        · simp only [List.mem_append, ih_iff']
          constructor
          · rintro ((h | h) | h)
            · exact Or.inl h
            · obtain ⟨r, hr, hwr⟩ := List.mem_flatten.mp h
              exact Or.inr (List.mem_flatten.mpr ⟨r, mem_odds_sub tail hr, hwr⟩)
            · obtain ⟨r, hr, hwr⟩ := List.mem_flatten.mp h
              exact Or.inr (List.mem_flatten.mpr ⟨r, mem_evens_sub tail hr, hwr⟩)
          · rintro (h | h)
            · exact Or.inl (Or.inl h)
            · obtain ⟨r, hr, hwr⟩ := List.mem_flatten.mp h
              rcases (mem_evens_or_odds tail).mp hr with he | ho
              · exact Or.inr (List.mem_flatten.mpr ⟨r, he, hwr⟩)
              · exact Or.inl (Or.inr (List.mem_flatten.mpr ⟨r, ho, hwr⟩))
        · apply List.disjoint_left.mpr
          intro w hwa hwg
          simp only [List.mem_append] at hwg
          rcases hwg with (h | h) | h
          · exact List.disjoint_left.mp ha_b hwa h
          · exact List.disjoint_left.mp ha_ot hwa h
          · exact List.disjoint_left.mp ih_da hwa h

theorem treeGarbs_length : ∀ (ctrl : List Wire) (regs : List (List Wire)),
    regs.length = 2 ^ ctrl.length → (treeGarbs ctrl regs).length = 2 ^ ctrl.length - 1
  | [], regs, hl => by simp [treeGarbs]
  | c :: cs, regs, hl => by
    have h2 : regs.length = 2 * 2 ^ cs.length := by
      simpa only [List.length_cons, pow_succ, Nat.mul_comm] using hl
    simp only [treeGarbs, List.length_append, odds_length _ _ h2,
      treeGarbs_length cs (evens regs) (evens_length _ _ h2)]
    have hp : 1 ≤ 2 ^ cs.length := Nat.one_le_pow _ _ (by decide)
    simp only [List.length_cons, pow_succ]
    omega

theorem treeGarbs_mem_length : ∀ (ctrl : List Wire) (regs : List (List Wire)) (m : Nat),
    (∀ r ∈ regs, r.length = m) → ∀ r ∈ treeGarbs ctrl regs, r.length = m
  | [], _, _, _, _, hr => by simp [treeGarbs] at hr
  | c :: cs, regs, m, hm, r, hr => by
    simp only [treeGarbs, List.mem_append] at hr
    rcases hr with ho | ht
    · exact hm r (mem_odds_sub regs ho)
    · exact treeGarbs_mem_length cs (evens regs) m (fun x hx => hm x (mem_evens_sub regs hx)) r ht

theorem treeGarbs_flatten_length (ctrl : List Wire) (regs : List (List Wire)) (m : Nat)
    (hl : regs.length = 2 ^ ctrl.length) (hm : ∀ r ∈ regs, r.length = m) :
    (treeGarbs ctrl regs).flatten.length = (2 ^ ctrl.length - 1) * m := by
  have hf : ∀ (L : List (List Wire)), (∀ r ∈ L, r.length = m) → L.flatten.length = L.length * m := by
    intro L; induction L with
    | nil => intro _; simp
    | cons a L ih =>
      intro h
      rw [List.flatten_cons, List.length_append, h a List.mem_cons_self,
        ih (fun x hx => h x (List.mem_cons_of_mem _ hx)), List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm]
  rw [hf _ (treeGarbs_mem_length ctrl regs m hm), treeGarbs_length ctrl regs hl]

theorem treeAddrs_length : ∀ k : Nat, (treeAddrs k).length = 2 ^ k - 1
  | 0 => rfl
  | k + 1 => by
    simp only [treeAddrs, List.length_append, oddAddrs, List.length_ofFn, List.length_map, treeAddrs_length k]
    have hp : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by decide)
    rw [pow_succ]; omega

theorem pairSwaps_hp (c : Wire) : ∀ regs : List (List Wire), Classical.HPFree (pairSwaps c regs)
  | [] => by simp [pairSwaps]
  | [_] => by simp [pairSwaps]
  | a :: b :: rest => by
    rw [pairSwaps, Classical.hpFree_append]
    exact ⟨First18.swapWords_hp c a b, pairSwaps_hp c rest⟩

theorem swapTree_hp : ∀ (ctrl : List Wire) (regs : List (List Wire)),
    Classical.HPFree (swapTree ctrl regs)
  | [], _ => by simp [swapTree]
  | c :: cs, regs => by
    rw [swapTree, Classical.hpFree_append]
    exact ⟨pairSwaps_hp c regs, swapTree_hp cs (evens regs)⟩

theorem pairSwaps_wf (c : Wire) : ∀ regs : List (List Wire),
    c ∉ regs.flatten → regs.flatten.Nodup → CircuitWellFormed (pairSwaps c regs)
  | [], _, _ => by simp [pairSwaps]
  | [_], _, _ => by simp [pairSwaps]
  | a :: b :: rest, hc, hnd => by
    simp only [List.flatten_cons, List.mem_append, not_or] at hc
    simp only [List.flatten_cons, List.nodup_append] at hnd
    have hab_nd : (a ++ b).Nodup := List.nodup_append.mpr
      ⟨hnd.1, hnd.2.1.1, fun x hx y hy => hnd.2.2 x hx y (List.mem_append_left _ hy)⟩
    rw [pairSwaps, circuitWellFormed_append]
    exact ⟨First18.swapWords_wf c a b hc.1 hc.2.1 hab_nd,
      pairSwaps_wf c rest hc.2.2 hnd.2.1.2.1⟩

theorem swapTree_wf : ∀ (ctrl : List Wire) (regs : List (List Wire)),
    ctrl.Disjoint regs.flatten → regs.flatten.Nodup → CircuitWellFormed (swapTree ctrl regs)
  | [], _, _, _ => by simp [swapTree]
  | c :: cs, regs, hdisj, hnd => by
    have hc : c ∉ regs.flatten := List.disjoint_left.mp hdisj List.mem_cons_self
    have hcs : cs.Disjoint (evens regs).flatten := by
      apply List.disjoint_left.mpr
      intro x hxc hxe
      obtain ⟨r, hr, hxr⟩ := List.mem_flatten.mp hxe
      exact List.disjoint_left.mp hdisj (List.mem_cons_of_mem _ hxc)
        (List.mem_flatten.mpr ⟨r, mem_evens_sub regs hr, hxr⟩)
    rw [swapTree, circuitWellFormed_append]
    exact ⟨pairSwaps_wf c regs hc hnd, swapTree_wf cs (evens regs) hcs (nodup_evens_odds regs hnd).1⟩

theorem pairSwaps_wires (c : Wire) : ∀ (regs : List (List Wire)) (w : Wire),
    w ∈ circuitWires (pairSwaps c regs) → w = c ∨ w ∈ regs.flatten
  | [], _, h => by simp [pairSwaps, circuitWires] at h
  | [_], _, h => by simp [pairSwaps, circuitWires] at h
  | a :: b :: rest, w, h => by
    rw [pairSwaps, MeasuredClear.circuitWires_append] at h
    rcases List.mem_append.mp h with h | h
    · rcases First18.swapWords_wires c a b w h with rfl | ha | hb
      · exact Or.inl rfl
      · exact Or.inr (by simp [ha])
      · exact Or.inr (by simp [hb])
    · rcases pairSwaps_wires c rest w h with rfl | hr
      · exact Or.inl rfl
      · exact Or.inr (by simp [hr])

theorem swapTree_wires : ∀ (ctrl : List Wire) (regs : List (List Wire)) (w : Wire),
    w ∈ circuitWires (swapTree ctrl regs) → w ∈ ctrl ∨ w ∈ regs.flatten
  | [], _, _, h => by simp [swapTree, circuitWires] at h
  | c :: cs, regs, w, h => by
    rw [swapTree, MeasuredClear.circuitWires_append] at h
    rcases List.mem_append.mp h with h | h
    · rcases pairSwaps_wires c regs w h with rfl | hr
      · exact Or.inl List.mem_cons_self
      · exact Or.inr hr
    · rcases swapTree_wires cs (evens regs) w h with hc | hr
      · exact Or.inl (List.mem_cons_of_mem _ hc)
      · obtain ⟨r, hrm, hwr⟩ := List.mem_flatten.mp hr
        exact Or.inr (List.mem_flatten.mpr ⟨r, mem_evens_sub regs hrm, hwr⟩)

theorem pairSwaps_length (c : Wire) (m : Nat) : ∀ (n : Nat) (regs : List (List Wire)),
    regs.length = 2 * n → (∀ r ∈ regs, r.length = m) →
    (pairSwaps c regs).length = 3 * (n * m)
  | 0, [], _, _ => by simp [pairSwaps]
  | 0, _ :: _, h, _ => by simp at h
  | n + 1, a :: b :: rest, h, hm => by
    have h' : rest.length = 2 * n := by simp at h; omega
    rw [pairSwaps, List.length_append, First18.swapWords_length,
      hm a List.mem_cons_self, hm b (List.mem_cons_of_mem _ List.mem_cons_self), Nat.min_self,
      pairSwaps_length c m n rest h' (fun r hr => hm r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)))]
    ring
  | n + 1, [], h, _ => by simp at h
  | n + 1, [_], h, _ => by simp at h; omega

theorem ccxCount_append (c1 c2 : Circuit) : ccxCount (c1 ++ c2) = ccxCount c1 + ccxCount c2 := by
  induction c1 with
  | nil => simp [ccxCount]
  | cons g gs ih =>
    cases g <;> simp only [List.cons_append, ccxCount, ih] <;> omega

theorem pairSwaps_ccx (c : Wire) (m : Nat) : ∀ (n : Nat) (regs : List (List Wire)),
    regs.length = 2 * n → (∀ r ∈ regs, r.length = m) →
    ccxCount (pairSwaps c regs) = n * m
  | 0, [], _, _ => by simp [pairSwaps, ccxCount]
  | 0, _ :: _, h, _ => by simp at h
  | n + 1, a :: b :: rest, h, hm => by
    have h' : rest.length = 2 * n := by simp at h; omega
    rw [pairSwaps, ccxCount_append, First18.swapWords_ccx,
      hm a List.mem_cons_self, hm b (List.mem_cons_of_mem _ List.mem_cons_self), Nat.min_self,
      pairSwaps_ccx c m n rest h' (fun r hr => hm r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)))]
    ring
  | n + 1, [], h, _ => by simp at h
  | n + 1, [_], h, _ => by simp at h; omega

theorem swapTree_length (m : Nat) : ∀ (ctrl : List Wire) (regs : List (List Wire)),
    regs.length = 2 ^ ctrl.length → (∀ r ∈ regs, r.length = m) →
    (swapTree ctrl regs).length = 3 * ((2 ^ ctrl.length - 1) * m)
  | [], _, _, _ => by simp [swapTree]
  | c :: cs, regs, hl, hm => by
    have h2 : regs.length = 2 * 2 ^ cs.length := by
      simpa only [List.length_cons, pow_succ, Nat.mul_comm] using hl
    rw [swapTree, List.length_append, pairSwaps_length c m (2 ^ cs.length) regs h2 hm,
      swapTree_length m cs (evens regs) (evens_length _ _ h2) (fun r hr => hm r (mem_evens_sub regs hr))]
    have hp : 1 ≤ 2 ^ cs.length := Nat.one_le_pow _ _ (by decide)
    simp only [List.length_cons, pow_succ]
    zify [hp, show 1 ≤ 2 ^ cs.length * 2 by omega]
    ring

theorem swapTree_ccx (m : Nat) : ∀ (ctrl : List Wire) (regs : List (List Wire)),
    regs.length = 2 ^ ctrl.length → (∀ r ∈ regs, r.length = m) →
    ccxCount (swapTree ctrl regs) = (2 ^ ctrl.length - 1) * m
  | [], _, _, _ => by simp [swapTree, ccxCount]
  | c :: cs, regs, hl, hm => by
    have h2 : regs.length = 2 * 2 ^ cs.length := by
      simpa only [List.length_cons, pow_succ, Nat.mul_comm] using hl
    rw [swapTree, ccxCount_append, pairSwaps_ccx c m (2 ^ cs.length) regs h2 hm,
      swapTree_ccx m cs (evens regs) (evens_length _ _ h2) (fun r hr => hm r (mem_evens_sub regs hr))]
    have hp : 1 ≤ 2 ^ cs.length := Nat.one_le_pow _ _ (by decide)
    simp only [List.length_cons, pow_succ]
    zify [hp, show 1 ≤ 2 ^ cs.length * 2 by omega]
    ring

/-! ### Classical semantics of `pairSwaps` and `swapTree` -/

theorem pairSwaps_run (c : Wire) (m : Nat) : ∀ (n : Nat) (regs : List (List Wire))
    (wordFn : Nat → List Bool) (base : Nat),
    regs.length = 2 * n → (∀ r ∈ regs, r.length = m) →
    c ∉ regs.flatten → regs.flatten.Nodup →
    ∀ s : BasisState,
    (∀ (j : Nat) (hj : j < regs.length), wireValues (regs[j]'hj) s = wordFn (base + j)) →
    (∀ w, w ∉ regs.flatten → Classical.run (pairSwaps c regs) s w = s w) ∧
    (∀ (j : Nat) (hj : j < (evens regs).length),
      wireValues ((evens regs)[j]'hj) (Classical.run (pairSwaps c regs) s) =
        wordFn (base + 2 * j + (s c).toNat)) ∧
    (∀ (j : Nat) (hj : j < (odds regs).length),
      wireValues ((odds regs)[j]'hj) (Classical.run (pairSwaps c regs) s) =
        wordFn (base + 2 * j + (1 - (s c).toNat)))
  | 0, [], _, _, _, _, _, _, s, _ =>
    ⟨fun _ _ => rfl, fun j hj => by simp [evens] at hj, fun j hj => by simp [odds] at hj⟩
  | 0, _ :: _, _, _, h, _, _, _, _, _ => by simp at h
  | n + 1, [], _, _, h, _, _, _, _, _ => by simp at h
  | n + 1, [_], _, _, h, _, _, _, _, _ => by simp at h; omega
  | n + 1, a :: b :: rest, wordFn, base, hl, hm, hc, hnd, s, hinit => by
    have hl' : rest.length = 2 * n := by simp at hl; omega
    simp only [List.flatten_cons, List.mem_append, not_or] at hc
    simp only [List.flatten_cons, List.nodup_append] at hnd
    have hab_nd : (a ++ b).Nodup := List.nodup_append.mpr
      ⟨hnd.1, hnd.2.1.1, fun x hx y hy => hnd.2.2 x hx y (List.mem_append_left _ hy)⟩
    have ha_len : a.length = m := hm a List.mem_cons_self
    have hb_len : b.length = m := hm b (List.mem_cons_of_mem _ List.mem_cons_self)
    obtain ⟨hfr1, hva1, hvb1⟩ :=
      First18.swapWords_run c a b hc.1 hc.2.1 hab_nd (ha_len.trans hb_len.symm) s
    let s1 := Classical.run (First18.swapWords c a b) s
    have hs1_c : s1 c = s c := hfr1 c hc.1 hc.2.1
    have hs1_rest : ∀ w ∈ rest.flatten, s1 w = s w := fun w hw =>
      hfr1 w (fun ha => hnd.2.2 w ha w (List.mem_append_right _ hw) rfl)
             (fun hb => hnd.2.1.2.2 w hb w hw rfl)
    have hinit_rest : ∀ (j : Nat) (hj : j < rest.length),
        wireValues (rest[j]'hj) s1 = wordFn ((base + 2) + j) := by
      intro j hj
      have hcongr : wireValues (rest[j]'hj) s1 = wireValues (rest[j]'hj) s :=
        List.map_congr_left (fun w hw => hs1_rest w (List.mem_flatten.mpr ⟨rest[j]'hj, List.getElem_mem hj, hw⟩))
      rw [hcongr]
      have h0 := hinit (j + 2) (by simp; omega)
      simpa only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm 2 j] using h0
    obtain ⟨hfr2, hev2, hod2⟩ := pairSwaps_run c m n rest wordFn (base + 2) hl'
      (fun r hr => hm r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)))
      hc.2.2 hnd.2.1.2.1 s1 hinit_rest
    have hrun : Classical.run (pairSwaps c (a :: b :: rest)) s = Classical.run (pairSwaps c rest) s1 := by
      rw [pairSwaps, Classical.run_append]
    rw [hrun]
    have ha_out : ∀ w ∈ a, w ∉ rest.flatten := fun w hwa hwr =>
      hnd.2.2 w hwa w (List.mem_append_right _ hwr) rfl
    have hb_out : ∀ w ∈ b, w ∉ rest.flatten := fun w hwb hwr =>
      hnd.2.1.2.2 w hwb w hwr rfl
    refine ⟨?_, ?_, ?_⟩
    · intro w hw
      simp only [List.flatten_cons, List.mem_append, not_or] at hw
      rw [hfr2 w hw.2.2]
      exact hfr1 w hw.1 hw.2.1
    · intro j hj
      cases j with
      | zero =>
        change wireValues a (Classical.run (pairSwaps c rest) s1) = wordFn (base + 2 * 0 + (s c).toNat)
        have hstay : wireValues a (Classical.run (pairSwaps c rest) s1) = wireValues a s1 :=
          List.map_congr_left (fun w hw => hfr2 w (ha_out w hw))
        rw [hstay, hva1]
        have h0 := hinit 0 (by simp)
        have h1 := hinit 1 (by simp)
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1
        rw [h0, h1]; cases s c <;> simp
      | succ j =>
        change wireValues ((evens rest)[j]'(by simpa [evens] using hj)) (Classical.run (pairSwaps c rest) s1) = _
        rw [hev2 j (by simpa [evens] using hj), hs1_c]
        congr 1; omega
    · intro j hj
      cases j with
      | zero =>
        change wireValues b (Classical.run (pairSwaps c rest) s1) = wordFn (base + 2 * 0 + (1 - (s c).toNat))
        have hstay : wireValues b (Classical.run (pairSwaps c rest) s1) = wireValues b s1 :=
          List.map_congr_left (fun w hw => hfr2 w (hb_out w hw))
        rw [hstay, hvb1]
        have h0 := hinit 0 (by simp)
        have h1 := hinit 1 (by simp)
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1
        rw [h0, h1]; cases s c <;> simp
      | succ j =>
        change wireValues ((odds rest)[j]'(by simpa [odds] using hj)) (Classical.run (pairSwaps c rest) s1) = _
        rw [hod2 j (by simpa [odds] using hj), hs1_c]
        congr 1; omega

theorem swapTree_run (m : Nat) : ∀ (ctrl : List Wire) (regs : List (List Wire))
    (wordFn : Nat → List Bool) (hi : Nat),
    regs.length = 2 ^ ctrl.length → (∀ r ∈ regs, r.length = m) →
    ctrl.Disjoint regs.flatten → regs.flatten.Nodup →
    ∀ s : BasisState,
    (∀ (j : Nat) (hj : j < regs.length), wireValues (regs[j]'hj) s = wordFn (2 ^ ctrl.length * hi + j)) →
    let a := tableAddressValue ctrl s + 2 ^ ctrl.length * hi
    let t := Classical.run (swapTree ctrl regs) s
    (∀ w, w ∉ regs.flatten → t w = s w) ∧
    (∀ (h0 : 0 < regs.length), wireValues (regs[0]'h0) t = wordFn a) ∧
    (∀ p ∈ (treeAddrs ctrl.length).zip (treeGarbs ctrl regs), wireValues p.2 t = wordFn (p.1 a))
  | [], regs, wordFn, hi, hl, _, _, _, s, hinit => by
    dsimp only
    have hl1 : regs.length = 1 := by simpa using hl
    refine ⟨fun _ _ => rfl, fun h0 => ?_, fun p hp => by simp [treeAddrs, treeGarbs] at hp⟩
    simpa [tableAddressValue] using hinit 0 h0
  | c :: cs, regs, wordFn, hi, hl, hm, hdisj, hnd, s, hinit => by
    dsimp only
    have h2 : regs.length = 2 * 2 ^ cs.length := by
      simpa only [List.length_cons, pow_succ, Nat.mul_comm] using hl
    have hc_not : c ∉ regs.flatten := List.disjoint_left.mp hdisj List.mem_cons_self
    obtain ⟨he_nd, ho_nd, heo⟩ := nodup_evens_odds regs hnd
    have hinit' : ∀ (j : Nat) (hj : j < regs.length),
        wireValues (regs[j]'hj) s = wordFn (2 ^ (c :: cs).length * hi + j) := hinit
    obtain ⟨hfr1, hev1, hod1⟩ := pairSwaps_run c m (2 ^ cs.length) regs wordFn (2 ^ (c :: cs).length * hi)
      h2 hm hc_not hnd s hinit'
    let s1 := Classical.run (pairSwaps c regs) s
    let b0 := (s c).toNat
    let wordFn' : Nat → List Bool := fun y => wordFn (2 * y + b0)
    have hcs_disj : cs.Disjoint (evens regs).flatten := by
      apply List.disjoint_left.mpr
      intro x hxc hxe
      obtain ⟨r, hr, hxr⟩ := List.mem_flatten.mp hxe
      exact List.disjoint_left.mp hdisj (List.mem_cons_of_mem _ hxc)
        (List.mem_flatten.mpr ⟨r, mem_evens_sub regs hr, hxr⟩)
    have hs1_cs : tableAddressValue cs s1 = tableAddressValue cs s := by
      apply tableAddressValue_congr
      intro w hw
      exact hfr1 w (List.disjoint_left.mp hdisj (List.mem_cons_of_mem _ hw))
    have hinit_ev : ∀ (j : Nat) (hj : j < (evens regs).length),
        wireValues ((evens regs)[j]'hj) s1 = wordFn' (2 ^ cs.length * hi + j) := by
      intro j hj
      rw [hev1 j hj]
      simp only [wordFn', b0, List.length_cons, pow_succ]
      congr 1; ring
    obtain ⟨hfr2, h0_2, hgarb2⟩ := swapTree_run m cs (evens regs) wordFn' hi
      (evens_length _ _ h2) (fun r hr => hm r (mem_evens_sub regs hr)) hcs_disj he_nd s1 hinit_ev
    have hrun : Classical.run (swapTree (c :: cs) regs) s = Classical.run (swapTree cs (evens regs)) s1 := by
      rw [swapTree, Classical.run_append]
    rw [hrun]
    let a := tableAddressValue (c :: cs) s + 2 ^ (c :: cs).length * hi
    have ha_val : a = 2 * (tableAddressValue cs s + 2 ^ cs.length * hi) + b0 := by
      change (s c).toNat + 2 * tableAddressValue cs s + 2 ^ (cs.length + 1) * hi = _
      rw [pow_succ]; simp only [b0]; ring
    have ha_div2 : a / 2 = tableAddressValue cs s + 2 ^ cs.length * hi := by
      have hb0 : b0 < 2 := by simp only [b0]; cases s c <;> decide
      omega
    have ha_mod2 : a % 2 = b0 := by
      have hb0 : b0 < 2 := by simp only [b0]; cases s c <;> decide
      omega
    have ha_divK : a / 2 ^ (cs.length + 1) = hi := by
      have hlt : tableAddressValue (c :: cs) s < 2 ^ (cs.length + 1) := by
        simpa [List.length_cons] using tableAddressValue_lt (c :: cs) s
      change (tableAddressValue (c :: cs) s + 2 ^ (cs.length + 1) * hi) / 2 ^ (cs.length + 1) = hi
      rw [Nat.add_mul_div_left _ _ (pow_pos (by decide) _), Nat.div_eq_of_lt hlt, Nat.zero_add]
    refine ⟨?_, ?_, ?_⟩
    · intro w hw
      have hw_ev : w ∉ (evens regs).flatten := fun h => by
        obtain ⟨r, hr, hwr⟩ := List.mem_flatten.mp h
        exact hw (List.mem_flatten.mpr ⟨r, mem_evens_sub regs hr, hwr⟩)
      rw [hfr2 w hw_ev]
      exact hfr1 w hw
    · intro h0
      have h0_ev : 0 < (evens regs).length := by
        rw [evens_length _ _ h2]; exact pow_pos (by decide) _
      have hev0 : (evens regs)[0]'h0_ev = regs[0]'h0 := by
        cases regs with
        | nil => simp at h0
        | cons x xs =>
          cases xs with
          | nil =>
            have hp : 1 ≤ 2 ^ cs.length := Nat.one_le_pow _ _ (by decide)
            simp at h2; omega
          | cons y ys => rfl
      rw [← hev0, h0_2 h0_ev, hs1_cs]
      simp only [wordFn', a, ha_val]
    · intro p hp
      simp only [List.length_cons, treeAddrs, treeGarbs] at hp
      have hlen_odd : (oddAddrs cs.length).length = (odds regs).length := by
        rw [oddAddrs, List.length_ofFn, odds_length _ _ h2]
      rw [List.zip_append hlen_odd, List.mem_append] at hp
      rcases hp with hodd | htail
      · obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hodd
        have hj1 : j < (oddAddrs cs.length).length := by simp at hj; exact hj.1
        have hj2 : j < (odds regs).length := by simp at hj; exact hj.2
        have hpe : p = ((oddAddrs cs.length)[j]'hj1, (odds regs)[j]'hj2) := by
          simpa [List.getElem_zip] using heq.symm
        subst hpe
        have hdisj_r : ∀ w ∈ (odds regs)[j]'hj2, w ∉ (evens regs).flatten := fun w hw he =>
          List.disjoint_left.mp heo he (List.mem_flatten.mpr ⟨(odds regs)[j]'hj2, List.getElem_mem hj2, hw⟩)
        have hstay : wireValues ((odds regs)[j]'hj2) (Classical.run (swapTree cs (evens regs)) s1) =
            wireValues ((odds regs)[j]'hj2) s1 :=
          List.map_congr_left (fun w hw => hfr2 w (hdisj_r w hw))
        rw [hstay, hod1 j hj2]
        simp only [oddAddrs, List.getElem_ofFn]
        change wordFn (2 ^ (c :: cs).length * hi + 2 * j + (1 - (s c).toNat)) =
          wordFn (2 * (2 ^ cs.length * (a / 2 ^ (cs.length + 1)) + j) + (1 - a % 2))
        rw [ha_divK, ha_mod2]
        simp only [b0, List.length_cons, pow_succ]
        congr 1; ring
      · rw [List.zip_map_left, List.mem_map] at htail
        obtain ⟨⟨g, reg⟩, hmem, rfl⟩ := htail
        have h2' := hgarb2 (g, reg) hmem
        simp only [hs1_cs, wordFn'] at h2'
        dsimp only [Prod.map, id_eq]
        rw [h2', ha_div2, ha_mod2]

/-! ### Part 2: Address splitting and QROM multi-register loading -/

theorem tableAddressValue_append (lo hi : List Wire) (s : BasisState) :
    tableAddressValue (lo ++ hi) s = tableAddressValue lo s + 2 ^ lo.length * tableAddressValue hi s := by
  induction lo with
  | nil => simp [tableAddressValue]
  | cons w ws ih =>
    change (s w).toNat + 2 * tableAddressValue (ws ++ hi) s =
      ((s w).toNat + 2 * tableAddressValue ws s) + 2 ^ (ws.length + 1) * tableAddressValue hi s
    rw [ih, pow_succ]; ring

def sliceWord (sliceSlots : List (Fin 262144 → ConstantBit 262144))
    (read : ConstantBit 262144 → Bool) (a : Nat) : List Bool :=
  sliceSlots.map fun f => read (f (First18.row a))

theorem sliceWord_length (sliceSlots : List (Fin 262144 → ConstantBit 262144))
    (read : ConstantBit 262144 → Bool) (a : Nat) :
    (sliceWord sliceSlots read a).length = sliceSlots.length := by
  simp [sliceWord]

def passLeaf (k : Nat) (sliceSlots : List (Fin 262144 → ConstantBit 262144))
    (regs : List (List Wire)) (l : Nat) (q : Wire) : List (TemplateGate 262144) :=
  lookupLeafGates q (regs.zipIdx.flatMap fun p =>
    (sliceSlots.map fun f => f (First18.row (2 ^ k * l + p.2))).zip p.1)

def passMask (k : Nat) (sliceSlots : List (Fin 262144 → ConstantBit 262144))
    (regs : List (List Wire)) (read : ConstantBit 262144 → Bool) (l : Nat) : List Wire :=
  regs.zipIdx.flatMap fun p => tableBitsMask p.1 (sliceWord sliceSlots read (2 ^ k * l + p.2))

theorem passLeaf_instantiate (k : Nat) (sliceSlots : List (Fin 262144 → ConstantBit 262144))
    (regs : List (List Wire)) (read : ConstantBit 262144 → Bool) (l : Nat) (q : Wire) :
    (passLeaf k sliceSlots regs l q).flatMap (TemplateGate.instantiate read) =
      tableXorGates q (passMask k sliceSlots regs read l) := by
  rw [passLeaf, lookupLeafGates_instantiate]
  have h1 : ∀ (L : List (List Wire × Nat)),
      ((L.flatMap fun p => (sliceSlots.map fun f => f (First18.row (2 ^ k * l + p.2))).zip p.1).filter
        (fun x => read x.1)).map (fun x => Gate.CX q x.2) =
      tableXorGates q (L.flatMap fun p => tableBitsMask p.1 (sliceWord sliceSlots read (2 ^ k * l + p.2))) := by
    intro L
    induction L with
    | nil => rfl
    | cons p ps ih =>
      rw [List.flatMap_cons, List.filter_append, List.map_append, ih, List.flatMap_cons,
        show tableXorGates q (_ ++ _) = tableXorGates q _ ++ tableXorGates q _ from List.map_append]
      congr 1
      rw [show (fun x : ConstantBit 262144 × Wire => Gate.CX q x.2) = (Gate.CX q) ∘ Prod.snd from rfl,
        ← List.map_map, filtered_zip_mask, List.map_map]
      rfl
  exact h1 regs.zipIdx

theorem mem_zipIdx_iff {α : Type} : ∀ (L : List α) (base : Nat) (x : α) (t : Nat),
    (x, t) ∈ L.zipIdx base ↔ ∃ i : Nat, ∃ hi : i < L.length, L[i]'hi = x ∧ base + i = t
  | [], _, _, _ => by simp
  | a :: as, base, x, t => by
    rw [List.zipIdx_cons, List.mem_cons, mem_zipIdx_iff as (base + 1) x t]
    constructor
    · rintro (h | ⟨i, hi, heq, ht⟩)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        exact ⟨0, by simp, rfl, by omega⟩
      · exact ⟨i + 1, by simp; omega, heq, by omega⟩
    · rintro ⟨i, hi, heq, ht⟩
      cases i with
      | zero => exact Or.inl (Prod.ext heq.symm (by omega))
      | succ i => exact Or.inr ⟨i, by simpa using hi, heq, by omega⟩

theorem passLeaf_length (k : Nat) (sliceSlots : List (Fin 262144 → ConstantBit 262144))
    (regs : List (List Wire)) (l : Nat) (q : Wire) :
    (passLeaf k sliceSlots regs l q).length ≤ regs.length * sliceSlots.length := by
  rw [passLeaf, lookupLeafGates, List.length_map]
  have h1 : ∀ (L : List (List Wire × Nat)),
      (L.flatMap fun p => (sliceSlots.map fun f => f (First18.row (2 ^ k * l + p.2))).zip p.1).length ≤
        L.length * sliceSlots.length := by
    intro L; induction L with
    | nil => simp
    | cons p ps ih =>
      rw [List.flatMap_cons, List.length_append, List.length_zip, List.length_map, List.length_cons,
        Nat.add_mul, Nat.one_mul]
      have := Nat.min_le_left sliceSlots.length p.1.length
      omega
  simpa [List.length_zipIdx] using h1 regs.zipIdx

theorem passMask_sub (k : Nat) (sliceSlots : List (Fin 262144 → ConstantBit 262144))
    (regs : List (List Wire)) (read : ConstantBit 262144 → Bool) (l : Nat) :
    passMask k sliceSlots regs read l ⊆ regs.flatten := by
  intro w hw
  obtain ⟨⟨r, t⟩, hmem, hwm⟩ := List.mem_flatMap.mp hw
  have hr : r ∈ regs := by
    obtain ⟨i, hi, heq, _⟩ := (mem_zipIdx_iff regs 0 r t).mp hmem
    rw [← heq]; exact List.getElem_mem hi
  exact List.mem_flatten.mpr ⟨r, hr, tableBitsMask_subset _ _ hwm⟩

theorem passMask_nodup (k : Nat) (sliceSlots : List (Fin 262144 → ConstantBit 262144))
    (regs : List (List Wire)) (read : ConstantBit 262144 → Bool) (l : Nat)
    (hnd : regs.flatten.Nodup) : (passMask k sliceSlots regs read l).Nodup := by
  have hgen : ∀ (L : List (List Wire)) (idx : Nat), L.flatten.Nodup →
      ((L.zipIdx idx).flatMap fun p => tableBitsMask p.1 (sliceWord sliceSlots read (2 ^ k * l + p.2))).Nodup := by
    intro L
    induction L with
    | nil => intro _ _; simp
    | cons r rs ih =>
      intro idx hnd'
      simp only [List.flatten_cons, List.nodup_append] at hnd'
      rw [List.zipIdx_cons, List.flatMap_cons, List.nodup_append]
      refine ⟨tableBitsMask_nodup _ _ hnd'.1, ih (idx + 1) hnd'.2.1, ?_⟩
      intro x hx y hy hxy
      subst hxy
      obtain ⟨⟨r', t'⟩, hmem, hxm⟩ := List.mem_flatMap.mp hy
      obtain ⟨i, hi, heq, _⟩ := (mem_zipIdx_iff rs (idx + 1) r' t').mp hmem
      have hxr : x ∈ r := tableBitsMask_subset _ _ hx
      have hxr' : x ∈ rs.flatten := List.mem_flatten.mpr ⟨r', heq ▸ List.getElem_mem hi, tableBitsMask_subset _ _ hxm⟩
      exact hnd'.2.2 x hxr x hxr' rfl
  exact hgen regs 0 hnd

theorem passMask_read (k : Nat) (sliceSlots : List (Fin 262144 → ConstantBit 262144))
    (regs : List (List Wire)) (read : ConstantBit 262144 → Bool) (selBits : List Wire)
    (hnd : regs.flatten.Nodup) (hlen : ∀ r ∈ regs, r.length = sliceSlots.length)
    (s : BasisState) (hroot : s 836 = true) (hclean : Clean regs.flatten s) :
    ∀ (j : Nat) (hj : j < regs.length),
      wireValues (regs[j]'hj) (tableLookupState (passMask k sliceSlots regs read) selBits 836 s) =
        sliceWord sliceSlots read (2 ^ k * tableAddressValue selBits s + j) := by
  intro j hj
  let r := regs[j]'hj
  let l := tableAddressValue selBits s
  have hr_nd : r.Nodup := by
    have hmem : r ∈ regs := List.getElem_mem hj
    have hsplit : ∀ (L : List (List Wire)), L.flatten.Nodup → ∀ q ∈ L, q.Nodup := by
      intro L; induction L with
      | nil => intro _ _ h; cases h
      | cons a L ih =>
        intro h q hq
        rw [List.flatten_cons, List.nodup_append] at h
        rcases List.mem_cons.mp hq with rfl | hq
        · exact h.1
        · exact ih h.2.1 q hq
    exact hsplit regs hnd r hmem
  have hr_clean : Clean r s := fun w hw => hclean w (List.mem_flatten.mpr ⟨r, List.getElem_mem hj, hw⟩)
  have hmem_iff : ∀ w ∈ r, (w ∈ passMask k sliceSlots regs read l) ↔
      (w ∈ tableBitsMask r (sliceWord sliceSlots read (2 ^ k * l + j))) := by
    intro w hw
    constructor
    · intro hm
      obtain ⟨⟨r', t'⟩, hmt, hwm⟩ := List.mem_flatMap.mp hm
      obtain ⟨i, hi, heq1, heq2⟩ := (mem_zipIdx_iff regs 0 r' t').mp hmt
      simp only [Nat.zero_add] at heq2
      have hti : i = j := by
        by_contra hne
        have hdisj : ∀ (L : List (List Wire)), L.flatten.Nodup →
            ∀ (a b : Nat) (ha : a < L.length) (hb : b < L.length), a ≠ b →
              ∀ x ∈ L[a]'ha, x ∉ L[b]'hb := by
          intro L; induction L with
          | nil => intro _ _ _ ha; simp at ha
          | cons q qs ih =>
            intro h a b ha hb hne' x hxa hxb
            rw [List.flatten_cons, List.nodup_append] at h
            cases a with
            | zero =>
              cases b with
              | zero => exact hne' rfl
              | succ b =>
                exact h.2.2 x hxa x (List.mem_flatten.mpr ⟨qs[b]'(by simpa using hb), List.getElem_mem _, hxb⟩) rfl
            | succ a =>
              cases b with
              | zero =>
                exact h.2.2 x hxb x (List.mem_flatten.mpr ⟨qs[a]'(by simpa using ha), List.getElem_mem _, hxa⟩) rfl
              | succ b =>
                exact ih h.2.1 a b (by simpa using ha) (by simpa using hb) (by omega) x hxa hxb
        have hwi : w ∈ regs[i]'hi := heq1 ▸ tableBitsMask_subset _ _ hwm
        exact hdisj regs hnd i j hi hj hne w hwi hw
      subst hti
      rw [← heq1, ← heq2] at hwm
      exact hwm
    · intro hm
      refine List.mem_flatMap.mpr ⟨(r, j), ?_, hm⟩
      exact (mem_zipIdx_iff regs 0 r j).mpr ⟨j, hj, rfl, Nat.zero_add j⟩
  have heq : wireValues r (tableLookupState (passMask k sliceSlots regs read) selBits 836 s) =
      wireValues r (tableXorState (tableBitsMask r (sliceWord sliceSlots read (2 ^ k * l + j))) true s) := by
    apply List.map_congr_left
    intro w hw
    simp only [tableLookupState, tableXorState, hroot]
    have hl' : tableAddressValue selBits s = l := rfl
    rw [hl']
    simp only [hmem_iff w hw]
  rw [heq, tableBitsMask_read _ _ s hr_nd (by rw [hlen r (List.getElem_mem hj), sliceWord_length]) hr_clean]

/-! ### Part 3: Generic `Pass` structure and one-shot proofs -/

def passClearData (k : Nat) (sliceSlots : List (Fin 262144 → ConstantBit 262144))
    (ctrl : List Wire) (regs : List (List Wire)) : List (MeasuredClear.ClearPort 262144) :=
  ((treeAddrs k).zip (treeGarbs ctrl regs)).flatMap fun p =>
    List.zipWith (fun f w => (⟨fun x => f (First18.row (p.1 x)), true, w⟩ : MeasuredClear.ClearPort 262144))
      sliceSlots p.2

theorem passClearData_targets (k : Nat) (sliceSlots : List (Fin 262144 → ConstantBit 262144))
    (ctrl : List Wire) (regs : List (List Wire))
    (hk : ctrl.length = k) (hl : regs.length = 2 ^ k)
    (hm : ∀ r ∈ regs, r.length = sliceSlots.length) :
    (passClearData k sliceSlots ctrl regs).map MeasuredClear.ClearPort.target =
      (treeGarbs ctrl regs).flatten := by
  have hlen : (treeAddrs k).length = (treeGarbs ctrl regs).length := by
    rw [treeAddrs_length, treeGarbs_length ctrl regs (by rw [hk]; exact hl), hk]
  have hml : ∀ r ∈ treeGarbs ctrl regs, r.length = sliceSlots.length :=
    treeGarbs_mem_length ctrl regs sliceSlots.length hm
  have hgen : ∀ (fs : List (Nat → Nat)) (gs : List (List Wire)),
      fs.length = gs.length → (∀ r ∈ gs, r.length = sliceSlots.length) →
      ((fs.zip gs).flatMap fun p =>
        List.zipWith (fun f w => (⟨fun x => f (First18.row (p.1 x)), true, w⟩ : MeasuredClear.ClearPort 262144))
          sliceSlots p.2).map MeasuredClear.ClearPort.target = gs.flatten := by
    intro fs; induction fs with
    | nil =>
      intro gs h _
      have hnil : gs = [] := List.eq_nil_of_length_eq_zero (by simpa using h.symm)
      subst hnil; rfl
    | cons fn fs ih =>
      intro gs h hml'
      cases gs with
      | nil => simp at h
      | cons g gs =>
        simp only [List.zip_cons_cons, List.flatMap_cons, List.map_append, List.flatten_cons]
        rw [First18.zipWith_targets _ (fun _ _ => rfl) sliceSlots g (hml' g List.mem_cons_self).symm,
          ih gs (by simpa using h) (fun r hr => hml' r (List.mem_cons_of_mem _ hr))]
  exact hgen (treeAddrs k) (treeGarbs ctrl regs) hlen hml

theorem passClearData_loaded (k : Nat) (sliceSlots : List (Fin 262144 → ConstantBit 262144))
    (ctrl : List Wire) (regs : List (List Wire))
    (read : ConstantBit 262144 → Bool) (a : Nat) (u : BasisState)
    (hvals : ∀ p ∈ (treeAddrs k).zip (treeGarbs ctrl regs),
      wireValues p.2 u = sliceWord sliceSlots read (p.1 a)) :
    ∀ q ∈ passClearData k sliceSlots ctrl regs,
      u q.target = (true && decide (read (q.ref a) = q.value)) := by
  intro q hq
  obtain ⟨⟨fn, reg⟩, hmem, hq'⟩ := List.mem_flatMap.mp hq
  have hv := hvals (fn, reg) hmem
  have hgen : ∀ (ss : List (Fin 262144 → ConstantBit 262144)) (ws : List Wire),
      wireValues ws u = ss.map (fun f => read (f (First18.row (fn a)))) →
      ∀ port ∈ List.zipWith (fun f w => (⟨fun x => f (First18.row (fn x)), true, w⟩ : MeasuredClear.ClearPort 262144)) ss ws,
        u port.target = (true && decide (read (port.ref a) = port.value)) := by
    intro ss; induction ss with
    | nil => intro _ _ _ hp; simp at hp
    | cons f ss ih =>
      intro ws h port hp
      cases ws with
      | nil => simp at hp
      | cons w ws =>
        have h' : u w = read (f (First18.row (fn a))) ∧
            wireValues ws u = ss.map (fun f => read (f (First18.row (fn a)))) := List.cons.inj h
        rw [List.zipWith_cons_cons, List.mem_cons] at hp
        rcases hp with rfl | hp
        · show u w = (true && decide (read (f (First18.row (fn a))) = true))
          rw [h'.1]; cases read (f (First18.row (fn a))) <;> rfl
        · exact ih ws h'.2 port hp
  exact hgen sliceSlots reg hv q hq'

structure Pass where
  k : Nat
  m : Nat
  sliceSlots : List (Fin 262144 → ConstantBit 262144)
  ctrl : List Wire
  selBits : List Wire
  selPaths : List Wire
  out : List Wire
  garb : List Wire

namespace Pass

def regs (P : Pass) : List (List Wire) := P.out :: chunks (2 ^ P.k - 1) P.m P.garb
def leaf (P : Pass) (l : Nat) (q : Wire) : List (TemplateGate 262144) :=
  passLeaf P.k P.sliceSlots P.regs l q
def selOps (P : Pass) : List (LookupOp 262144) :=
  unaryLookupOps P.leaf (tableAddressTree P.selBits 0 1) 836 P.selPaths
def swap (P : Pass) : Circuit := swapTree P.ctrl P.regs
def targets (P : Pass) : List Wire := (treeGarbs P.ctrl P.regs).flatten
def clearData (P : Pass) : List (MeasuredClear.ClearPort 262144) :=
  passClearData P.k P.sliceSlots P.ctrl P.regs
def selMeas (P : Pass) : Nat := 2 ^ (18 - P.k) - 1
def garbLen (P : Pass) : Nat := (2 ^ P.k - 1) * P.m

structure Geo (P : Pass) : Prop where
  hk : 0 < P.k ∧ P.k < 18
  hctrl_len : P.ctrl.length = P.k
  hsel_len : P.selBits.length = 18 - P.k
  hpaths_len : P.selPaths.length = 18 - P.k
  hbits : P.ctrl ++ P.selBits = SelectSchedule18.bits
  hslots_len : P.sliceSlots.length = P.m
  hout_len : P.out.length = P.m
  hgarb_len : P.garb.length = (2 ^ P.k - 1) * P.m
  hsel_nodup : (836 :: P.selBits ++ P.selPaths).Nodup
  hregs_nodup : (P.out ++ P.garb).Nodup
  hdisj_sel : (836 :: SelectSchedule18.bits ++ P.selPaths).Disjoint (P.out ++ P.garb)
  hsupp : (836 :: SelectSchedule18.bits ++ P.selPaths ++ P.out ++ P.garb) ⊆ List.range 1613

theorem regs_length (P : Pass) (g : P.Geo) : P.regs.length = 2 ^ P.k := by
  rw [regs, List.length_cons, chunks_length]
  have hp : 1 ≤ 2 ^ P.k := Nat.one_le_pow _ _ (by decide)
  omega

theorem regs_mem_length (P : Pass) (g : P.Geo) : ∀ r ∈ P.regs, r.length = P.m := by
  intro r hr
  rw [regs, List.mem_cons] at hr
  rcases hr with rfl | hr
  · exact g.hout_len
  · exact chunks_mem_length _ _ _ g.hgarb_len r hr

theorem regs_flatten (P : Pass) (g : P.Geo) : P.regs.flatten = P.out ++ P.garb := by
  rw [regs, List.flatten_cons, chunks_flatten _ _ _ g.hgarb_len]

theorem regs_nodup (P : Pass) (g : P.Geo) : P.regs.flatten.Nodup := by
  rw [P.regs_flatten g]; exact g.hregs_nodup

theorem targets_nodup (P : Pass) (g : P.Geo) : P.targets.Nodup :=
  (treeGarbs_nodup_and_mem P.ctrl P.regs (by rw [g.hctrl_len]; exact P.regs_length g) (P.regs_nodup g)).1

theorem targets_mem_iff (P : Pass) (g : P.Geo) (w : Wire) : w ∈ P.targets ↔ w ∈ P.garb := by
  have h := (treeGarbs_nodup_and_mem P.ctrl P.regs (by rw [g.hctrl_len]; exact P.regs_length g)
    (P.regs_nodup g)).2 P.out (chunks (2 ^ P.k - 1) P.m P.garb) rfl
  rw [targets, h.1 w, chunks_flatten _ _ _ g.hgarb_len]

theorem targets_length (P : Pass) (g : P.Geo) : P.targets.length = P.garbLen := by
  rw [targets, treeGarbs_flatten_length P.ctrl P.regs P.m (by rw [g.hctrl_len]; exact P.regs_length g)
    (P.regs_mem_length g), g.hctrl_len, garbLen]

theorem clearData_targets (P : Pass) (g : P.Geo) :
    P.clearData.map MeasuredClear.ClearPort.target = P.targets :=
  passClearData_targets P.k P.sliceSlots P.ctrl P.regs g.hctrl_len (P.regs_length g)
    (fun r hr => (P.regs_mem_length g r hr).trans g.hslots_len.symm)

theorem clearData_length (P : Pass) (g : P.Geo) : P.clearData.length = P.garbLen := by
  have h := congrArg List.length (P.clearData_targets g)
  rw [List.length_map, P.targets_length g] at h
  exact h

theorem sel_layout (P : Pass) (g : P.Geo) : (tableAddressTree P.selBits 0 1).Layout 836 P.selPaths :=
  tableAddressTree_layout _ _ _ _ _ (g.hsel_len.trans g.hpaths_len.symm).le g.hsel_nodup

theorem sel_nodes (P : Pass) (g : P.Geo) : (tableAddressTree P.selBits 0 1).internalNodes = P.selMeas := by
  have h := tableAddressTree_nodes P.selBits 0 1
  rw [g.hsel_len] at h
  rw [selMeas]; omega

theorem selOps_measurements (P : Pass) (g : P.Geo) : lookupMeasurements P.selOps = P.selMeas := by
  rw [selOps, unaryLookupOps_measurements _ _ _ _ (P.sel_layout g), P.sel_nodes g]

theorem selOps_circuit (P : Pass) (read : ConstantBit 262144 → Bool) :
    lookupCircuit read P.selOps =
      tableLookupProgram (passMask P.k P.sliceSlots P.regs read) P.selBits 836 P.selPaths := by
  rw [selOps, unaryLookupOps_circuit]
  unfold tableLookupProgram tableLookup
  apply unaryAction_leaf_congr
  intro l _ q
  exact passLeaf_instantiate P.k P.sliceSlots P.regs read l q

def loadProg (P : Pass) (g : P.Geo) (start : Nat) : Straight 262144 start (start + P.selMeas) :=
  (castFinish (by rw [P.selOps_measurements g]) (lookupProgram 262144 P.selOps start)).append
    (literalProgram P.swap)

def loadSrc (P : Pass) (read : ConstantBit 262144 → Bool) : AdaptiveCircuit :=
  (lookupCircuit read P.selOps).seq (.unitary P.swap .done)

theorem loadProg_run (P : Pass) (g : P.Geo) (read : ConstantBit 262144 → Bool)
    (start : Nat) (h : Fin start → Bool) :
    ((P.loadProg g start).instantiate read h).run = (P.loadSrc read).run := by
  rw [loadProg, append_run_fixed _ _ _ _ _ (fun h' => literalProgram_run P.swap read h'),
    AdaptiveCircuit.run_seq, castFinish_instantiate, lookupProgram_run, ← AdaptiveCircuit.run_seq, loadSrc]

theorem loadProg_tCount (P : Pass) (g : P.Geo) (read : ConstantBit 262144 → Bool)
    (start : Nat) (h : Fin start → Bool) :
    ((P.loadProg g start).instantiate read h).tCount = 7 * (P.selMeas + P.garbLen) := by
  have hsel_t : ((lookupProgram 262144 P.selOps start).instantiate read h).tCount = 7 * P.selMeas := by
    rw [lookupProgram_tCount, P.selOps_circuit,
      tableLookupProgram_tCount _ P.selBits P.selPaths 836 (g.hsel_len.trans g.hpaths_len.symm).le g.hsel_nodup,
      g.hsel_len, selMeas]
  have hsw_t : ShorECDLP.tCount P.swap = 7 * P.garbLen := by
    have hccx := swapTree_ccx P.m P.ctrl P.regs (by rw [g.hctrl_len]; exact P.regs_length g) (P.regs_mem_length g)
    have hhp := swapTree_hp P.ctrl P.regs
    have ht_ccx : ∀ c : Circuit, Classical.HPFree c → ShorECDLP.tCount c = 7 * ccxCount c := by
      intro c; induction c with
      | nil => intro _; rfl
      | cons g' gs ih =>
        intro hhp'
        have hhd := hhp' g' List.mem_cons_self
        have htl : Classical.HPFree gs := fun x hx => hhp' x (List.mem_cons_of_mem _ hx)
        cases g' with
        | X _ => simpa [ShorECDLP.tCount, tCost, ccxCount] using ih htl
        | CX _ _ => simpa [ShorECDLP.tCount, tCost, ccxCount] using ih htl
        | CCX _ _ _ =>
          have hih := ih htl
          simp only [ShorECDLP.tCount] at hih ⊢
          simp only [tCost, ccxCount, List.map_cons, List.sum_cons]
          omega
        | H _ => cases hhd
        | P _ _ _ => cases hhd
    rw [swap, ht_ccx _ hhp, hccx, g.hctrl_len, garbLen]
  rw [loadProg, append_tCount_fixed _ _ _ _ _ (fun h' => literalProgram_tCount P.swap read h'),
    castFinish_instantiate, hsel_t, hsw_t]
  ring

theorem loadProg_residue (P : Pass) (g : P.Geo) (start : Nat) :
    residue (P.loadProg g start) = 0 := by
  rw [loadProg, swap, residue_append, residue_cast, residue_lookup, selOps,
    residue_literal_HPFree _ (swapTree_hp P.ctrl P.regs), Nat.add_zero]
  apply WEXCredit.residue_unary
  intro label root
  unfold leaf passLeaf lookupLeafGates
  generalize (P.regs.zipIdx.flatMap fun p =>
    (P.sliceSlots.map fun f => f (First18.row (2 ^ P.k * label + p.2))).zip p.1) = ports
  induction ports with
  | nil => rfl
  | cons p ps ih => simpa [templateResidue, tCost] using ih

theorem loadProg_slots (P : Pass) (g : P.Geo) (start : Nat) :
    (P.loadProg g start).gateSlots ≤
      (2 ^ P.k * P.m) * (P.selMeas + 1) + 10 * P.selMeas + 3 * P.garbLen := by
  rw [loadProg, Straight.gateSlots_append, castFinish_gateSlots, lookupProgram_slots, literalProgram_slots]
  have hs := unaryLookupOps_slots_le P.leaf (2 ^ P.k * P.m)
    (fun l q => by
      have h := passLeaf_length P.k P.sliceSlots P.regs l q
      rw [P.regs_length g, g.hslots_len] at h; exact h)
    (tableAddressTree P.selBits 0 1) 836 P.selPaths
  rw [P.sel_nodes g] at hs
  have hsw := swapTree_length P.m P.ctrl P.regs (by rw [g.hctrl_len]; exact P.regs_length g) (P.regs_mem_length g)
  rw [g.hctrl_len] at hsw
  rw [selOps, swap, hsw, garbLen]
  omega

theorem loadProg_wellFormed (P : Pass) (g : P.Geo) (start : Nat) :
    (P.loadProg g start).WellFormed := by
  rw [loadProg]
  refine straight_append_wellFormed _ _ ?_ ?_
  · rw [castFinish_wellFormed]
    apply lookupProgram_wellFormed
    rw [selOps]
    apply unaryLookupOps_physical _ _ _ _ (P.sel_layout g)
    intro l c hc gate hgate
    simp only [leaf, passLeaf, lookupLeafGates, List.mem_map] at hgate
    obtain ⟨⟨ref, tgt⟩, hm, rfl⟩ := hgate
    change c ≠ tgt
    obtain ⟨⟨reg, idx⟩, hreg, hzt⟩ := List.mem_flatMap.mp hm
    obtain ⟨i, hi, heq, _⟩ := (mem_zipIdx_iff P.regs 0 reg idx).mp hreg
    have htgt : tgt ∈ P.out ++ P.garb := by
      rw [← P.regs_flatten g]
      exact List.mem_flatten.mpr ⟨reg, heq ▸ List.getElem_mem hi, (List.of_mem_zip hzt).2⟩
    intro he; subst he
    have hc' : c ∈ 836 :: SelectSchedule18.bits ++ P.selPaths := by
      rcases List.mem_cons.mp hc with rfl | hc
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ hc)
    exact List.disjoint_left.mp g.hdisj_sel hc' htgt
  · apply literalProgram_wellFormed
    apply swapTree_wf
    · rw [P.regs_flatten g]
      apply List.disjoint_left.mpr
      intro w hwc hwr
      have hwb : w ∈ SelectSchedule18.bits := by rw [← g.hbits]; exact List.mem_append_left _ hwc
      exact List.disjoint_left.mp g.hdisj_sel (List.mem_cons_of_mem _ (List.mem_append_left _ hwb)) hwr
    · exact P.regs_nodup g

theorem loadProg_support (P : Pass) (g : P.Geo) (start : Nat) :
    straightWires (P.loadProg g start) ⊆ List.range 1613 := by
  rw [loadProg, straightWires_append, straightWires_castFinish, lookupProgram_support, literalProgram_support]
  apply List.append_subset.mpr
  constructor
  · have hl : ∀ op ∈ P.selOps, lookupOpWires op ⊆ List.range 1613 := by
      rw [selOps]
      apply unaryLookupOps_support
      · exact g.hsupp (by simp)
      · intro w hw; exact g.hsupp (by simp [hw])
      · intro w hw
        have hb := (tableAddressTree_mem_index P.selBits 0 1 w).mp hw
        have hwb : w ∈ SelectSchedule18.bits := by rw [← g.hbits]; exact List.mem_append_right _ hb
        exact g.hsupp (by simp [hwb])
      · intro l q hq
        apply lookupLeafGates_support _ _ _ hq
        intro port hp
        obtain ⟨⟨reg, idx⟩, hreg, hzt⟩ := List.mem_flatMap.mp hp
        obtain ⟨i, hi, heq, _⟩ := (mem_zipIdx_iff P.regs 0 reg idx).mp hreg
        have htgt : port.2 ∈ P.out ++ P.garb := by
          rw [← P.regs_flatten g]
          exact List.mem_flatten.mpr ⟨reg, heq ▸ List.getElem_mem hi, (List.of_mem_zip hzt).2⟩
        rcases List.mem_append.mp htgt with h | h <;> exact g.hsupp (by simp [h])
    intro w hw
    obtain ⟨op, hop, hw⟩ := List.mem_flatMap.mp hw
    exact hl op hop hw
  · intro w hw
    rcases swapTree_wires P.ctrl P.regs w hw with h | h
    · have hwb : w ∈ SelectSchedule18.bits := by rw [← g.hbits]; exact List.mem_append_left _ h
      exact g.hsupp (by simp [hwb])
    · rw [P.regs_flatten g] at h
      rcases List.mem_append.mp h with h | h <;> exact g.hsupp (by simp [h])

theorem loadProg_safe836 (P : Pass) (g : P.Geo) (start : Nat) :
    RootPass.safeProgram 836 (P.loadProg g start) := by
  rw [loadProg, RootPass.safeProgram_append, RootPass.safeProgram_cast]
  constructor
  · apply RootPass.lookupProgram_safe
    rw [selOps]
    obtain ⟨hb, hp⟩ := RootPass.layout_avoids (P.sel_layout g)
    apply RootPass.unaryOps_safe 836 P.leaf _ _ _ _ hb hp
    intro l c gate hg
    simp only [leaf, passLeaf, lookupLeafGates, List.mem_map] at hg
    obtain ⟨⟨ref, tgt⟩, hm, rfl⟩ := hg
    change tgt ≠ 836
    obtain ⟨⟨reg, idx⟩, hreg, hzt⟩ := List.mem_flatMap.mp hm
    obtain ⟨i, hi, heq, _⟩ := (mem_zipIdx_iff P.regs 0 reg idx).mp hreg
    have htgt : tgt ∈ P.out ++ P.garb := by
      rw [← P.regs_flatten g]
      exact List.mem_flatten.mpr ⟨reg, heq ▸ List.getElem_mem hi, (List.of_mem_zip hzt).2⟩
    intro he; subst he
    exact List.disjoint_left.mp g.hdisj_sel List.mem_cons_self htgt
  · apply RootPass.safeProgram_of_not_mem
    rw [literalProgram_support]
    intro h
    rcases swapTree_wires P.ctrl P.regs 836 h with hc | hr
    · have h836 : (836 : Wire) ∈ SelectSchedule18.bits := by rw [← g.hbits]; exact List.mem_append_left _ hc
      have : (836 : Wire) ∉ SelectSchedule18.bits := by decide
      exact this h836
    · rw [P.regs_flatten g] at hr
      exact List.disjoint_left.mp g.hdisj_sel List.mem_cons_self hr

theorem loadProg_hits836 (P : Pass) (g : P.Geo) (start : Nat) :
    RootPass.literalHits 836 (P.loadProg g start) = 1 := by
  rw [loadProg, RootPass.literalHits_append, RootPass.literalHits_cast,
    RootPass.literalHits_lookupProgram]
  have hsw : RootPass.literalHits 836 (literalProgram (n := 262144) (s := start + P.selMeas) P.swap) = 0 := by
    apply RootPass.literalHits_zero_of_not_mem
    rw [literalProgram_support]
    intro h
    rcases swapTree_wires P.ctrl P.regs 836 h with hc | hr
    · have h836 : (836 : Wire) ∈ SelectSchedule18.bits := by rw [← g.hbits]; exact List.mem_append_left _ hc
      have : (836 : Wire) ∉ SelectSchedule18.bits := by decide
      exact this h836
    · rw [P.regs_flatten g] at hr
      exact List.disjoint_left.mp g.hdisj_sel List.mem_cons_self hr
  rw [hsw, Nat.add_zero, selOps]
  apply RootPass.unaryOps_root_hits 836 P.leaf _ _ (P.sel_layout g)
  · rw [P.sel_nodes g, selMeas]
    have hpow : 2 ≤ 2 ^ (18 - P.k) := by
      have : 1 ≤ 18 - P.k := by have := g.hk; omega
      exact Nat.le_self_pow (by omega) 2
    omega
  · intro l c
    simp [leaf, passLeaf, lookupLeafGates, List.map_map, Function.comp_def, RootPass.templateHits]

/-- Classical post-swap state of a single pass. -/
def afterSwap (P : Pass) (read : ConstantBit 262144 → Bool) (s : BasisState) : BasisState :=
  Classical.run P.swap (tableLookupState (passMask P.k P.sliceSlots P.regs read) P.selBits 836 s)

/-- Classical post-reset state of a single pass. -/
def afterReset (P : Pass) (read : ConstantBit 262144 → Bool) (s : BasisState) : BasisState :=
  clearRegister P.targets (P.afterSwap read s)

theorem loadSrc_coherent (P : Pass) (g : P.Geo) (read : ConstantBit 262144 → Bool) :
    CoherentlyImplementsOn (P.loadSrc read)
      (Finsupp.lmapDomain ℂ ℂ (P.afterSwap read)) (Clean P.selPaths) := by
  have hsel : CoherentlyImplementsOn (lookupCircuit read P.selOps)
      (Finsupp.lmapDomain ℂ ℂ (tableLookupState (passMask P.k P.sliceSlots P.regs read) P.selBits 836))
      (Clean P.selPaths) := by
    rw [P.selOps_circuit]
    apply tableLookupProgram_coherent_state _ _ _ _ (g.hsel_len.trans g.hpaths_len.symm).le g.hsel_nodup
      (fun l => passMask_nodup P.k P.sliceSlots P.regs read l (P.regs_nodup g))
    intro l w hw hm
    have hmr : w ∈ P.out ++ P.garb := by rw [← P.regs_flatten g]; exact passMask_sub _ _ _ _ _ hm
    have hw' : w ∈ 836 :: SelectSchedule18.bits ++ P.selPaths := by
      simp only [List.mem_cons, List.mem_append] at hw ⊢
      rcases hw with (rfl | hw) | hw
      · exact Or.inl (Or.inl rfl)
      · exact Or.inl (Or.inr (by rw [← g.hbits]; exact List.mem_append_right _ hw))
      · exact Or.inr hw
    exact List.disjoint_left.mp g.hdisj_sel hw' hmr
  have hcomb := hsel.seq (CoherentlyImplementsOn.unitary P.swap (fun _ => True)) (fun _ _ _ _ => trivial)
  refine hcomb.congrIdeal (fun s _ => ?_)
  rw [LinearMap.comp_apply, First18.lmap_ket, First18.lmap_ket, swap,
    run_ket_agrees_classical _ _ (swapTree_hp P.ctrl P.regs)]
  rfl

theorem afterSwap_facts (P : Pass) (g : P.Geo) (read : ConstantBit 262144 → Bool)
    (s : BasisState) (h836 : s 836 = true) (hclean : Clean (P.out ++ P.garb) s) :
    (∀ w, w ∉ P.out → w ∉ P.garb → P.afterSwap read s w = s w) ∧
    wireValues P.out (P.afterSwap read s) = sliceWord P.sliceSlots read (tableAddressValue SelectSchedule18.bits s) ∧
    (∀ q ∈ P.clearData, (P.afterSwap read s) q.target =
      (true && decide (read (q.ref (tableAddressValue SelectSchedule18.bits s)) = q.value))) := by
  let s0 := tableLookupState (passMask P.k P.sliceSlots P.regs read) P.selBits 836 s
  have h0_fr : ∀ w, w ∉ P.out → w ∉ P.garb → s0 w = s w := by
    intro w h1 h2
    apply tableXorState_outside
    intro hm
    have hmr := passMask_sub P.k P.sliceSlots P.regs read _ hm
    rw [P.regs_flatten g] at hmr
    rcases List.mem_append.mp hmr with h | h
    · exact h1 h
    · exact h2 h
  have h0_ctrl : tableAddressValue P.ctrl s0 = tableAddressValue P.ctrl s := by
    apply tableAddressValue_congr
    intro w hw
    have hwb : w ∈ SelectSchedule18.bits := by rw [← g.hbits]; exact List.mem_append_left _ hw
    have hn : w ∉ P.out ++ P.garb := List.disjoint_left.mp g.hdisj_sel (by simp [hwb])
    exact h0_fr w (fun h => hn (List.mem_append_left _ h)) (fun h => hn (List.mem_append_right _ h))
  have h0_init : ∀ (j : Nat) (hj : j < P.regs.length),
      wireValues (P.regs[j]'hj) s0 = sliceWord P.sliceSlots read (2 ^ P.ctrl.length * tableAddressValue P.selBits s + j) := by
    rw [g.hctrl_len]
    exact passMask_read P.k P.sliceSlots P.regs read P.selBits (P.regs_nodup g)
      (fun r hr => (P.regs_mem_length g r hr).trans g.hslots_len.symm)
      s h836 (by rw [P.regs_flatten g]; exact hclean)
  have hctrl_disj : P.ctrl.Disjoint P.regs.flatten := by
    rw [P.regs_flatten g]
    apply List.disjoint_left.mpr
    intro w hw hmr
    have hwb : w ∈ SelectSchedule18.bits := by rw [← g.hbits]; exact List.mem_append_left _ hw
    exact List.disjoint_left.mp g.hdisj_sel (by simp [hwb]) hmr
  obtain ⟨hfr, h0, hgarb⟩ := swapTree_run P.m P.ctrl P.regs (sliceWord P.sliceSlots read)
    (tableAddressValue P.selBits s) (by rw [g.hctrl_len]; exact P.regs_length g)
    (P.regs_mem_length g) hctrl_disj (P.regs_nodup g) s0 h0_init
  have haddr : tableAddressValue P.ctrl s0 + 2 ^ P.ctrl.length * tableAddressValue P.selBits s =
      tableAddressValue SelectSchedule18.bits s := by
    rw [h0_ctrl, ← tableAddressValue_append, g.hbits]
  rw [haddr] at h0 hgarb
  refine ⟨fun w h1 h2 => ?_, ?_, ?_⟩
  · have hnw : w ∉ P.regs.flatten := by rw [P.regs_flatten g, List.mem_append]; tauto
    exact (hfr w hnw).trans (h0_fr w h1 h2)
  · have hpos : 0 < P.regs.length := by rw [P.regs_length g]; exact pow_pos (by decide) _
    exact h0 hpos
  · apply passClearData_loaded P.k P.sliceSlots P.ctrl P.regs read
    rw [← g.hctrl_len]
    exact hgarb

theorem afterReset_facts (P : Pass) (g : P.Geo) (read : ConstantBit 262144 → Bool)
    (s : BasisState) (h836 : s 836 = true) (hclean : Clean (P.out ++ P.garb) s) :
    (∀ w, w ∉ P.out → P.afterReset read s w = s w) ∧
    wireValues P.out (P.afterReset read s) = sliceWord P.sliceSlots read (tableAddressValue SelectSchedule18.bits s) := by
  obtain ⟨hfr, hout, _⟩ := P.afterSwap_facts g read s h836 hclean
  have hout_disj : P.out.Disjoint P.targets :=
    ((treeGarbs_nodup_and_mem P.ctrl P.regs (by rw [g.hctrl_len]; exact P.regs_length g)
      (P.regs_nodup g)).2 P.out (chunks (2 ^ P.k - 1) P.m P.garb) rfl).2
  refine ⟨fun w hw => ?_, ?_⟩
  · by_cases hg : w ∈ P.garb
    · have ht : w ∈ P.targets := (P.targets_mem_iff g w).mpr hg
      rw [afterReset, clearRegister_clean _ _ _ ht]
      exact (hclean w (List.mem_append_right _ hg)).symm
    · have ht : w ∉ P.targets := fun h => hg ((P.targets_mem_iff g w).mp h)
      rw [afterReset, MeasuredClear.clearRegister_frame _ _ _ ht]
      exact hfr w hw hg
  · rw [afterReset]
    have hcongr : wireValues P.out (clearRegister P.targets (P.afterSwap read s)) =
        wireValues P.out (P.afterSwap read s) :=
      List.map_congr_left (fun w hw => MeasuredClear.clearRegister_frame _ _ _
        (List.disjoint_left.mp hout_disj hw))
    rw [hcongr, hout]

/-- One CPS step: run `P.loadProg`, X-measure+reset `P.targets`, and continue with `next`. -/
def stepProg (P : Pass) (g : P.Geo) {R : Nat}
    (next : (c : Nat) → List (Fin c) → Straight 262144 c (c + R))
    (start : Nat) (refs : List (Fin start)) :
    Straight 262144 start (start + (P.selMeas + (P.garbLen + R))) :=
  castFinish (Nat.add_assoc start P.selMeas (P.garbLen + R))
    ((P.loadProg g start).append
      (castFinish (by rw [P.targets_length g]; exact Nat.add_assoc (start + P.selMeas) P.garbLen R)
        (MeasuredClear.measureThen (R := R) next P.targets (start + P.selMeas)
          (refs.map (Fin.castLE (Nat.le_add_right _ _))))))

def stepSrc (P : Pass) (read : ConstantBit 262144 → Bool)
    (nextSrc : List Bool → AdaptiveCircuit) (prior : List Bool) : AdaptiveCircuit :=
  (P.loadSrc read).seq (measureResetThen P.targets (fun o => nextSrc (prior ++ o)))

theorem stepProg_run (P : Pass) (g : P.Geo) {R : Nat}
    (next : (c : Nat) → List (Fin c) → Straight 262144 c (c + R))
    (nextSrc : List Bool → AdaptiveCircuit) (read : ConstantBit 262144 → Bool)
    (hn : ∀ c rs h, ((next c rs).instantiate read h).run = (nextSrc (rs.map h)).run)
    (start : Nat) (refs : List (Fin start)) (h : Fin start → Bool) :
    ((P.stepProg g next start refs).instantiate read h).run =
      (P.stepSrc read nextSrc (refs.map h)).run := by
  rw [stepProg, castFinish_instantiate,
    MeasuredClear.append_run_prefix _ _ read (Nat.le_refl start) h h rfl
      (measureResetThen P.targets (fun o => nextSrc (refs.map h ++ o))),
    AdaptiveCircuit.run_seq, P.loadProg_run g, ← AdaptiveCircuit.run_seq, stepSrc]
  intro h' hh'
  rw [castFinish_instantiate, MeasuredClear.measureThen_run _ nextSrc read hn, List.map_map]
  congr 2; ext o; congr 2; rw [← hh']; rfl

theorem stepProg_tCount (P : Pass) (g : P.Geo) {R t : Nat}
    (next : (c : Nat) → List (Fin c) → Straight 262144 c (c + R))
    (read : ConstantBit 262144 → Bool)
    (hn : ∀ c rs h, ((next c rs).instantiate read h).tCount = t)
    (start : Nat) (refs : List (Fin start)) (h : Fin start → Bool) :
    ((P.stepProg g next start refs).instantiate read h).tCount =
      7 * (P.selMeas + P.garbLen) + t := by
  rw [stepProg, castFinish_instantiate,
    append_tCount_fixed _ _ _ _ _ (fun h' => by
      rw [castFinish_instantiate, MeasuredClear.measureThen_tCount _ read hn]),
    P.loadProg_tCount g]

theorem stepProg_residue (P : Pass) (g : P.Geo) {R : Nat}
    (next : (c : Nat) → List (Fin c) → Straight 262144 c (c + R))
    (hn : ∀ c rs, residue (next c rs) = 0)
    (start : Nat) (refs : List (Fin start)) :
    residue (P.stepProg g next start refs) = 0 := by
  rw [stepProg, residue_cast, residue_append, P.loadProg_residue g, residue_cast,
    MeasuredClear.measureThen_residue _ hn]

theorem stepProg_slots (P : Pass) (g : P.Geo) {R B : Nat}
    (next : (c : Nat) → List (Fin c) → Straight 262144 c (c + R))
    (hn : ∀ c rs, (next c rs).gateSlots ≤ B)
    (start : Nat) (refs : List (Fin start)) :
    (P.stepProg g next start refs).gateSlots ≤
      (2 ^ P.k * P.m) * (P.selMeas + 1) + 10 * P.selMeas + 3 * P.garbLen + B := by
  rw [stepProg, castFinish_gateSlots, Straight.gateSlots_append, castFinish_gateSlots]
  have h1 := P.loadProg_slots g start
  have h2 : (MeasuredClear.measureThen (R := R) next P.targets (start + P.selMeas)
      (refs.map (Fin.castLE (Nat.le_add_right _ _)))).gateSlots ≤ B := by
    have hgen : ∀ (ws : List Wire) (st : Nat) (rs : List (Fin st)),
        (MeasuredClear.measureThen (R := R) next ws st rs).gateSlots ≤ B := by
      intro ws; induction ws with
      | nil => intro st rs; exact hn st rs
      | cons w ws ih =>
        intro st rs
        simp only [MeasuredClear.measureThen, castFinish_gateSlots, Straight.gateSlots]
        exact ih _ _
    exact hgen _ _ _
  omega

theorem stepProg_wellFormed (P : Pass) (g : P.Geo) {R : Nat}
    (next : (c : Nat) → List (Fin c) → Straight 262144 c (c + R))
    (hn : ∀ c rs, (next c rs).WellFormed)
    (start : Nat) (refs : List (Fin start)) :
    (P.stepProg g next start refs).WellFormed := by
  rw [stepProg, castFinish_wellFormed]
  refine straight_append_wellFormed _ _ (P.loadProg_wellFormed g start) ?_
  rw [castFinish_wellFormed]
  exact MeasuredClear.measureThen_wellFormed next hn _ _ _

theorem stepProg_support (P : Pass) (g : P.Geo) {R : Nat}
    (next : (c : Nat) → List (Fin c) → Straight 262144 c (c + R))
    (hn : ∀ c rs, straightWires (next c rs) ⊆ List.range 1613)
    (start : Nat) (refs : List (Fin start)) :
    straightWires (P.stepProg g next start refs) ⊆ List.range 1613 := by
  rw [stepProg, straightWires_castFinish, straightWires_append, straightWires_castFinish]
  refine List.append_subset.mpr ⟨P.loadProg_support g start, ?_⟩
  rw [RootPass.straightWires_eq_naive]
  apply MeasuredClear.measureThen_within next (List.range 1613)
  · intro c rs; rw [← RootPass.straightWires_eq_naive]; exact hn c rs
  · intro w hw
    have hg := (P.targets_mem_iff g w).mp hw
    exact g.hsupp (by simp [hg])

theorem stepProg_safe836 (P : Pass) (g : P.Geo) {R : Nat}
    (next : (c : Nat) → List (Fin c) → Straight 262144 c (c + R))
    (hn : ∀ c rs, RootPass.safeProgram 836 (next c rs))
    (start : Nat) (refs : List (Fin start)) :
    RootPass.safeProgram 836 (P.stepProg g next start refs) := by
  rw [stepProg, RootPass.safeProgram_cast, RootPass.safeProgram_append, RootPass.safeProgram_cast]
  refine ⟨P.loadProg_safe836 g start, RootPass.measureThen_safe 836 next hn _ _ _ ?_⟩
  intro w hw he
  subst he
  have hg := (P.targets_mem_iff g 836).mp hw
  exact List.disjoint_left.mp g.hdisj_sel List.mem_cons_self (List.mem_append_right _ hg)

theorem stepProg_hits836 (P : Pass) (g : P.Geo) {R hCount : Nat}
    (next : (c : Nat) → List (Fin c) → Straight 262144 c (c + R))
    (hn : ∀ c rs, RootPass.literalHits 836 (next c rs) = hCount)
    (start : Nat) (refs : List (Fin start)) :
    RootPass.literalHits 836 (P.stepProg g next start refs) = 1 + hCount := by
  rw [stepProg, RootPass.literalHits_cast, RootPass.literalHits_append, P.loadProg_hits836 g,
    RootPass.literalHits_cast, RootPass.literalHits_measureThen 836 hCount next hn]

theorem stepSrc_sim (P : Pass) (g : P.Geo) (read : ConstantBit 262144 → Bool)
    (nextSrc : List Bool → AdaptiveCircuit) (prior : List Bool)
    (V : BasisState → Prop) (inState fNext : BasisState → BasisState)
    (phasePrior : BasisState → ℂ)
    (hV_pre : ∀ s, V s → Clean P.selPaths (inState s) ∧ (inState s) 836 = true ∧ Clean (P.out ++ P.garb) (inState s))
    (hNext : ∀ o, o.length = P.targets.length →
      ∃ cs : List ℂ,
        List.Forall₂ (fun b c => ∀ s, V s →
          b.kraus (ket (P.afterReset read (inState s))) =
            c • (phasePrior s *
              registerXPhase P.targets o (P.afterSwap read (inState s))) • ket (fNext s))
          (nextSrc (prior ++ o)).run cs ∧
        (cs.map Complex.normSq).sum = 1) :
    ∃ cs : List ℂ,
      List.Forall₂ (fun b c => ∀ s, V s →
        b.kraus (ket (inState s)) = c • (phasePrior s) • ket (fNext s))
        (P.stepSrc read nextSrc prior).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  obtain ⟨cL, aL, mL⟩ := P.loadSrc_coherent g read
  have hM := MeasuredClear.measureResetThen_sim P.targets (fun o => nextSrc (prior ++ o))
    (fun o b c => ∀ s, V s → b.kraus (ket (P.afterReset read (inState s))) =
      c • (phasePrior s *
        registerXPhase P.targets o (P.afterSwap read (inState s))) • ket (fNext s))
    (fun b c => ∀ s, V s → b.kraus (ket (P.afterSwap read (inState s))) =
      c • (phasePrior s) • ket (fNext s))
    hNext
    (by
      intro o ho b c hb s hs
      have hx := xResetRegisterKraus_ket P.targets o (P.afterSwap read (inState s))
        ho (P.targets_nodup g)
      change b.kraus (xResetRegisterKraus P.targets o (ket (P.afterSwap read (inState s)))) = _
      rw [hx, map_smul]
      change registerXResetCoeff P.targets o (P.afterSwap read (inState s)) •
        b.kraus (ket (P.afterReset read (inState s))) = _
      rw [hb s hs]
      have hsq := MeasuredClear.registerXPhase_square P.targets o (P.afterSwap read (inState s))
      rw [registerXResetCoeff_eq_magnitude_mul_phase _ _ _ ho, smul_smul, smul_smul, smul_smul]
      congr 1
      calc
        _ = registerXResetMagnitude P.targets.length * c * phasePrior s *
              (registerXPhase P.targets o (P.afterSwap read (inState s)) *
                registerXPhase P.targets o (P.afterSwap read (inState s))) := by ring
        _ = registerXResetMagnitude P.targets.length * c * phasePrior s := by rw [hsq, mul_one])
  obtain ⟨cM, aM, mM⟩ := hM
  refine ⟨coherentSeqCoefficients cL cM, ?_, by rw [WEX.simulationCoefficients_mass, mL, mM]; norm_num⟩
  rw [stepSrc, AdaptiveCircuit.run_seq]
  apply WEX.simulationAligned_seq aL aM
  intro bL kL bM kM hbL hbM s hs
  change bM.kraus (bL.kraus (ket (inState s))) = _
  rw [hbL (inState s) (hV_pre s hs).1, First18.lmap_ket, map_smul, hbM s hs, smul_smul, smul_smul]

end Pass

/-! ### Part 4: Four-pass instantiation `((2, 394), (4, 74), (5, 34), (6, 11))` -/

def anc16 : List Wire :=
  List.range' 0 263 ++ List.range' 535 2 ++ List.range' 538 42 ++
    [837] ++ List.range' 839 16 ++ List.range' 872 741

def anc14 : List Wire := anc16 ++ [533, 534]
def anc13 : List Wire := anc16 ++ [532, 533, 534]
def anc12 : List Wire := anc16 ++ [531, 532, 533, 534]

theorem mem_anc16 {w : Wire} : w ∈ anc16 ↔
    w < 263 ∨ (535 ≤ w ∧ w < 537) ∨ (538 ≤ w ∧ w < 580) ∨ w = 837 ∨
    (839 ≤ w ∧ w < 855) ∨ (872 ≤ w ∧ w < 1613) := by
  simp only [anc16, List.mem_append, List.mem_range'_1, List.mem_singleton]
  dsimp only [Wire] at *
  omega

theorem anc16_length : anc16.length = 1065 := by
  simp [anc16]

theorem anc16_nodup : anc16.Nodup := by
  have h1 : (List.range' 0 263 ++ List.range' 535 2).Nodup :=
    List.nodup_append.mpr ⟨List.nodup_range', List.nodup_range', fun a ha b hb => by
      simp only [List.mem_range'_1] at ha hb; omega⟩
  have h2 : (List.range' 0 263 ++ List.range' 535 2 ++ List.range' 538 42).Nodup :=
    List.nodup_append.mpr ⟨h1, List.nodup_range', fun a ha b hb => by
      simp only [List.mem_append, List.mem_range'_1] at ha hb; omega⟩
  have h3 : (List.range' 0 263 ++ List.range' 535 2 ++ List.range' 538 42 ++ [837]).Nodup :=
    List.nodup_append.mpr ⟨h2, List.nodup_singleton _, fun a ha b hb => by
      simp only [List.mem_append, List.mem_range'_1, List.mem_singleton] at ha hb; omega⟩
  have h4 : (List.range' 0 263 ++ List.range' 535 2 ++ List.range' 538 42 ++ [837] ++ List.range' 839 16).Nodup :=
    List.nodup_append.mpr ⟨h3, List.nodup_range', fun a ha b hb => by
      simp only [List.mem_append, List.mem_range'_1, List.mem_singleton] at ha hb; omega⟩
  exact List.nodup_append.mpr ⟨h4, List.nodup_range', fun a ha b hb => by
    simp only [List.mem_append, List.mem_range'_1, List.mem_singleton] at ha hb
    (try dsimp only [Wire] at *); omega⟩

theorem anc16_disj_point : anc16.Disjoint pointLogicalWires := by
  apply List.disjoint_left.mpr
  intro w ha hp
  have h1 := mem_anc16.mp ha
  have h2 := First18.mem_point hp
  (try dsimp only [Wire] at *); omega

theorem anc14_nodup : anc14.Nodup :=
  List.nodup_append.mpr ⟨anc16_nodup, by decide, fun a ha b hb => by
    have h1 := mem_anc16.mp ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    (try dsimp only [Wire] at *); omega⟩

theorem anc13_nodup : anc13.Nodup :=
  List.nodup_append.mpr ⟨anc16_nodup, by decide, fun a ha b hb => by
    have h1 := mem_anc16.mp ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    (try dsimp only [Wire] at *); omega⟩

theorem anc12_nodup : anc12.Nodup :=
  List.nodup_append.mpr ⟨anc16_nodup, by decide, fun a ha b hb => by
    have h1 := mem_anc16.mp ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    (try dsimp only [Wire] at *); omega⟩

def p1 : List Wire := pointLogicalWires.take 394
def rem1 : List Wire := pointLogicalWires.drop 394
def p2 : List Wire := rem1.take 74
def rem2 : List Wire := rem1.drop 74
def p3 : List Wire := rem2.take 34
def rem3 : List Wire := rem2.drop 34
def p4 : List Wire := rem3

def s1 : List (Fin 262144 → ConstantBit 262144) := First18.slots.take 394
def s2 : List (Fin 262144 → ConstantBit 262144) := (First18.slots.drop 394).take 74
def s3 : List (Fin 262144 → ConstantBit 262144) := (First18.slots.drop 468).take 34
def s4 : List (Fin 262144 → ConstantBit 262144) := First18.slots.drop 502

theorem point_split : p1 ++ p2 ++ p3 ++ p4 = pointLogicalWires := by
  simp only [p1, p2, p3, p4, rem1, rem2, rem3, List.append_assoc, List.take_append_drop]

theorem slots_split : s1 ++ s2 ++ s3 ++ s4 = First18.slots := by
  have h1 : First18.slots.drop 468 = (First18.slots.drop 394).drop 74 := by rw [List.drop_drop]
  have h2 : First18.slots.drop 502 = (First18.slots.drop 468).drop 34 := by rw [List.drop_drop]
  simp only [s1, s2, s3, s4, h2, h1, List.append_assoc, List.take_append_drop]

theorem p1_len : p1.length = 394 := by rw [p1, List.length_take, First18.point_length]; decide
theorem rem1_len : rem1.length = 119 := by rw [rem1, List.length_drop, First18.point_length]
theorem p2_len : p2.length = 74 := by rw [p2, List.length_take, rem1_len]; decide
theorem rem2_len : rem2.length = 45 := by rw [rem2, List.length_drop, rem1_len]
theorem p3_len : p3.length = 34 := by rw [p3, List.length_take, rem2_len]; decide
theorem rem3_len : rem3.length = 11 := by rw [rem3, List.length_drop, rem2_len]
theorem p4_len : p4.length = 11 := rem3_len

theorem s1_len : s1.length = 394 := by rw [s1, List.length_take, First18.slots_length]; decide
theorem s2_len : s2.length = 74 := by rw [s2, List.length_take, List.length_drop, First18.slots_length]; decide
theorem s3_len : s3.length = 34 := by rw [s3, List.length_take, List.length_drop, First18.slots_length]; decide
theorem s4_len : s4.length = 11 := by rw [s4, List.length_drop, First18.slots_length]

theorem p_mem_point : ∀ w, (w ∈ p1 ∨ w ∈ p2 ∨ w ∈ p3 ∨ w ∈ p4) ↔ w ∈ pointLogicalWires := by
  intro w; rw [← point_split]; simp only [List.mem_append, or_assoc]

theorem p_nodup_split : (p1 ++ (p2 ++ (p3 ++ p4))).Nodup := by
  simpa only [← List.append_assoc, point_split] using pointLogicalWires_nodup

theorem p1_rem1_eq : p1 ++ rem1 = pointLogicalWires := List.take_append_drop 394 pointLogicalWires
theorem p2_rem2_eq : p2 ++ rem2 = rem1 := List.take_append_drop 74 rem1
theorem p3_p4_eq : p3 ++ p4 = rem2 := List.take_append_drop 34 rem2

theorem p1_disj_rem1 : p1.Disjoint rem1 := by
  have h : (p1 ++ rem1).Nodup := by rw [p1_rem1_eq]; exact pointLogicalWires_nodup
  exact List.disjoint_left.mpr (fun a ha hb => (List.nodup_append.mp h).2.2 a ha a hb rfl)

theorem p1_nodup : p1.Nodup :=
  (List.nodup_append.mp (by rw [p1_rem1_eq]; exact pointLogicalWires_nodup)).1

theorem rem1_nodup : rem1.Nodup :=
  (List.nodup_append.mp (by rw [p1_rem1_eq]; exact pointLogicalWires_nodup)).2.1

theorem p2_disj_rem2 : p2.Disjoint rem2 := by
  have h : (p2 ++ rem2).Nodup := by rw [p2_rem2_eq]; exact rem1_nodup
  exact List.disjoint_left.mpr (fun a ha hb => (List.nodup_append.mp h).2.2 a ha a hb rfl)

theorem p2_nodup : p2.Nodup :=
  (List.nodup_append.mp (by rw [p2_rem2_eq]; exact rem1_nodup)).1

theorem rem2_nodup : rem2.Nodup :=
  (List.nodup_append.mp (by rw [p2_rem2_eq]; exact rem1_nodup)).2.1

theorem p3_nodup : p3.Nodup :=
  (List.nodup_append.mp (by rw [p3_p4_eq]; exact rem2_nodup)).1

theorem p4_nodup : p4.Nodup :=
  (List.nodup_append.mp (by rw [p3_p4_eq]; exact rem2_nodup)).2.1

def pass1 : Pass :=
  ⟨2, 394, s1, SelectSchedule18.bits.take 2, SelectSchedule18.bits.drop 2,
    List.range' 519 16, p1, (anc16 ++ rem1).take 1182⟩

def pass2 : Pass :=
  ⟨4, 74, s2, SelectSchedule18.bits.take 4, SelectSchedule18.bits.drop 4,
    List.range' 519 14, p2, (anc14 ++ rem2).take 1110⟩

def pass3 : Pass :=
  ⟨5, 34, s3, SelectSchedule18.bits.take 5, SelectSchedule18.bits.drop 5,
    List.range' 519 13, p3, anc13.take 1054⟩

def pass4 : Pass :=
  ⟨6, 11, s4, SelectSchedule18.bits.take 6, SelectSchedule18.bits.drop 6,
    List.range' 519 12, p4, anc12.take 693⟩

theorem pass1_geo : pass1.Geo where
  hk := by decide
  hctrl_len := by decide
  hsel_len := by decide
  hpaths_len := by decide
  hbits := List.take_append_drop 2 SelectSchedule18.bits
  hslots_len := s1_len
  hout_len := p1_len
  hgarb_len := by simp [pass1, anc16_length, rem1_len]
  hsel_nodup := by decide
  hregs_nodup := by
    change (p1 ++ (anc16 ++ rem1).take 1182).Nodup
    have hfull : (p1 ++ (anc16 ++ rem1)).Nodup := by
      refine List.nodup_append.mpr ⟨p1_nodup, List.nodup_append.mpr ⟨anc16_nodup, rem1_nodup, ?_⟩, ?_⟩
      · intro a ha b hb he; subst he
        exact List.disjoint_left.mp anc16_disj_point ha (List.mem_of_mem_drop hb)
      · intro a ha b hb he; subst he
        rcases List.mem_append.mp hb with hb | hb
        · exact List.disjoint_left.mp anc16_disj_point hb (List.mem_of_mem_take ha)
        · exact List.disjoint_left.mp p1_disj_rem1 ha hb
    exact hfull.sublist (List.Sublist.append (List.Sublist.refl _) (List.take_sublist _ _))
  hdisj_sel := by
    apply List.disjoint_left.mpr
    intro w h1 h2
    simp only [pass1, SelectSchedule18.bits, List.mem_cons, List.mem_append, List.mem_range'_1,
      List.mem_singleton, List.not_mem_nil, or_false] at h1
    rcases List.mem_append.mp h2 with hp | hg
    · have := First18.mem_point (List.mem_of_mem_take hp); (try dsimp only [Wire] at *); omega
    · rcases List.mem_append.mp (List.mem_of_mem_take hg) with ha | hr
      · have := mem_anc16.mp ha; (try dsimp only [Wire] at *); omega
      · have := First18.mem_point (List.mem_of_mem_drop hr); (try dsimp only [Wire] at *); omega
  hsupp := by
    intro w hw
    rw [List.mem_range]
    simp only [pass1, SelectSchedule18.bits, List.mem_cons, List.mem_append, List.mem_range'_1,
      List.mem_singleton, List.not_mem_nil, or_false] at hw
    rcases hw with (((rfl | h | h) | h) | hp) | hg
    · decide
    · (try dsimp only [Wire] at *); omega
    · (try dsimp only [Wire] at *); omega
    · (try dsimp only [Wire] at *); omega
    · have := First18.mem_point (List.mem_of_mem_take hp); (try dsimp only [Wire] at *); omega
    · rcases List.mem_append.mp (List.mem_of_mem_take hg) with ha | hr
      · have := mem_anc16.mp ha; (try dsimp only [Wire] at *); omega
      · have := First18.mem_point (List.mem_of_mem_drop hr); (try dsimp only [Wire] at *); omega

theorem pass2_geo : pass2.Geo where
  hk := by decide
  hctrl_len := by decide
  hsel_len := by decide
  hpaths_len := by decide
  hbits := List.take_append_drop 4 SelectSchedule18.bits
  hslots_len := s2_len
  hout_len := p2_len
  hgarb_len := by simp [pass2, anc14, anc16_length, rem2_len]
  hsel_nodup := by decide
  hregs_nodup := by
    change (p2 ++ (anc14 ++ rem2).take 1110).Nodup
    have ha_pt : anc14.Disjoint pointLogicalWires := by
      apply List.disjoint_left.mpr
      intro w ha hp
      have hpt := First18.mem_point hp
      simp only [anc14, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with ha | rfl | rfl
      · exact List.disjoint_left.mp anc16_disj_point ha hp
      · (try dsimp only [Wire] at *); omega
      · (try dsimp only [Wire] at *); omega
    have hfull : (p2 ++ (anc14 ++ rem2)).Nodup := by
      refine List.nodup_append.mpr ⟨p2_nodup, List.nodup_append.mpr ⟨anc14_nodup, rem2_nodup, ?_⟩, ?_⟩
      · intro a ha b hb he; subst he
        exact List.disjoint_left.mp ha_pt ha (List.mem_of_mem_drop (List.mem_of_mem_drop hb))
      · intro a ha b hb he; subst he
        rcases List.mem_append.mp hb with hb | hb
        · exact List.disjoint_left.mp ha_pt hb (List.mem_of_mem_drop (List.mem_of_mem_take ha))
        · exact List.disjoint_left.mp p2_disj_rem2 ha hb
    exact hfull.sublist (List.Sublist.append (List.Sublist.refl _) (List.take_sublist _ _))
  hdisj_sel := by
    apply List.disjoint_left.mpr
    intro w h1 h2
    simp only [pass2, SelectSchedule18.bits, List.mem_cons, List.mem_append, List.mem_range'_1,
      List.mem_singleton, List.not_mem_nil, or_false] at h1
    rcases List.mem_append.mp h2 with hp | hg
    · have := First18.mem_point (List.mem_of_mem_drop (List.mem_of_mem_take hp)); (try dsimp only [Wire] at *); omega
    · rcases List.mem_append.mp (List.mem_of_mem_take hg) with ha | hr
      · simp only [anc14, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with ha | rfl | rfl
        · have := mem_anc16.mp ha; (try dsimp only [Wire] at *); omega
        · (try dsimp only [Wire] at *); omega
        · (try dsimp only [Wire] at *); omega
      · have := First18.mem_point (List.mem_of_mem_drop (List.mem_of_mem_drop hr)); (try dsimp only [Wire] at *); omega
  hsupp := by
    intro w hw
    rw [List.mem_range]
    simp only [pass2, SelectSchedule18.bits, List.mem_cons, List.mem_append, List.mem_range'_1,
      List.mem_singleton, List.not_mem_nil, or_false] at hw
    rcases hw with (((rfl | h | h) | h) | hp) | hg
    · decide
    · (try dsimp only [Wire] at *); omega
    · (try dsimp only [Wire] at *); omega
    · (try dsimp only [Wire] at *); omega
    · have := First18.mem_point (List.mem_of_mem_drop (List.mem_of_mem_take hp)); (try dsimp only [Wire] at *); omega
    · rcases List.mem_append.mp (List.mem_of_mem_take hg) with ha | hr
      · simp only [anc14, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with ha | rfl | rfl
        · have := mem_anc16.mp ha; (try dsimp only [Wire] at *); omega
        · decide
        · decide
      · have := First18.mem_point (List.mem_of_mem_drop (List.mem_of_mem_drop hr)); (try dsimp only [Wire] at *); omega

theorem pass3_geo : pass3.Geo where
  hk := by decide
  hctrl_len := by decide
  hsel_len := by decide
  hpaths_len := by decide
  hbits := List.take_append_drop 5 SelectSchedule18.bits
  hslots_len := s3_len
  hout_len := p3_len
  hgarb_len := by simp [pass3, anc13, anc16_length]
  hsel_nodup := by decide
  hregs_nodup := by
    change (p3 ++ anc13.take 1054).Nodup
    refine List.nodup_append.mpr ⟨p3_nodup, anc13_nodup.sublist (List.take_sublist _ _), ?_⟩
    intro a ha b hb he; subst he
    have hpt := First18.mem_point (List.mem_of_mem_drop (List.mem_of_mem_drop (List.mem_of_mem_take ha)))
    have hb' := List.mem_of_mem_take hb
    simp only [anc13, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb'
    rcases hb' with hb' | rfl | rfl | rfl
    · exact List.disjoint_left.mp anc16_disj_point hb' (List.mem_of_mem_drop (List.mem_of_mem_drop (List.mem_of_mem_take ha)))
    · (try dsimp only [Wire] at *); omega
    · (try dsimp only [Wire] at *); omega
    · (try dsimp only [Wire] at *); omega
  hdisj_sel := by
    apply List.disjoint_left.mpr
    intro w h1 h2
    simp only [pass3, SelectSchedule18.bits, List.mem_cons, List.mem_append, List.mem_range'_1,
      List.mem_singleton, List.not_mem_nil, or_false] at h1
    rcases List.mem_append.mp h2 with hp | hg
    · have := First18.mem_point (List.mem_of_mem_drop (List.mem_of_mem_drop (List.mem_of_mem_take hp)))
      (try dsimp only [Wire] at *); omega
    · have hg' := List.mem_of_mem_take hg
      simp only [anc13, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg'
      rcases hg' with hg' | rfl | rfl | rfl
      · have := mem_anc16.mp hg'; (try dsimp only [Wire] at *); omega
      · (try dsimp only [Wire] at *); omega
      · (try dsimp only [Wire] at *); omega
      · (try dsimp only [Wire] at *); omega
  hsupp := by
    intro w hw
    rw [List.mem_range]
    simp only [pass3, SelectSchedule18.bits, List.mem_cons, List.mem_append, List.mem_range'_1,
      List.mem_singleton, List.not_mem_nil, or_false] at hw
    rcases hw with (((rfl | h | h) | h) | hp) | hg
    · decide
    · (try dsimp only [Wire] at *); omega
    · (try dsimp only [Wire] at *); omega
    · (try dsimp only [Wire] at *); omega
    · have := First18.mem_point (List.mem_of_mem_drop (List.mem_of_mem_drop (List.mem_of_mem_take hp)))
      (try dsimp only [Wire] at *); omega
    · have hg' := List.mem_of_mem_take hg
      simp only [anc13, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg'
      rcases hg' with hg' | rfl | rfl | rfl
      · have := mem_anc16.mp hg'; (try dsimp only [Wire] at *); omega
      · decide
      · decide
      · decide

theorem pass4_geo : pass4.Geo where
  hk := by decide
  hctrl_len := by decide
  hsel_len := by decide
  hpaths_len := by decide
  hbits := List.take_append_drop 6 SelectSchedule18.bits
  hslots_len := s4_len
  hout_len := p4_len
  hgarb_len := by simp [pass4, anc12, anc16_length]
  hsel_nodup := by decide
  hregs_nodup := by
    change (p4 ++ anc12.take 693).Nodup
    refine List.nodup_append.mpr ⟨p4_nodup, anc12_nodup.sublist (List.take_sublist _ _), ?_⟩
    intro a ha b hb he; subst he
    have hpt := First18.mem_point (List.mem_of_mem_drop (List.mem_of_mem_drop (List.mem_of_mem_drop ha)))
    have hb' := List.mem_of_mem_take hb
    simp only [anc12, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb'
    rcases hb' with hb' | rfl | rfl | rfl | rfl
    · exact List.disjoint_left.mp anc16_disj_point hb' (List.mem_of_mem_drop (List.mem_of_mem_drop (List.mem_of_mem_drop ha)))
    · (try dsimp only [Wire] at *); omega
    · (try dsimp only [Wire] at *); omega
    · (try dsimp only [Wire] at *); omega
    · (try dsimp only [Wire] at *); omega
  hdisj_sel := by
    apply List.disjoint_left.mpr
    intro w h1 h2
    simp only [pass4, SelectSchedule18.bits, List.mem_cons, List.mem_append, List.mem_range'_1,
      List.mem_singleton, List.not_mem_nil, or_false] at h1
    rcases List.mem_append.mp h2 with hp | hg
    · have := First18.mem_point (List.mem_of_mem_drop (List.mem_of_mem_drop (List.mem_of_mem_drop hp)))
      (try dsimp only [Wire] at *); omega
    · have hg' := List.mem_of_mem_take hg
      simp only [anc12, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg'
      rcases hg' with hg' | rfl | rfl | rfl | rfl
      · have := mem_anc16.mp hg'; (try dsimp only [Wire] at *); omega
      · (try dsimp only [Wire] at *); omega
      · (try dsimp only [Wire] at *); omega
      · (try dsimp only [Wire] at *); omega
      · (try dsimp only [Wire] at *); omega
  hsupp := by
    intro w hw
    rw [List.mem_range]
    simp only [pass4, SelectSchedule18.bits, List.mem_cons, List.mem_append, List.mem_range'_1,
      List.mem_singleton, List.not_mem_nil, or_false] at hw
    rcases hw with (((rfl | h | h) | h) | hp) | hg
    · decide
    · (try dsimp only [Wire] at *); omega
    · (try dsimp only [Wire] at *); omega
    · (try dsimp only [Wire] at *); omega
    · have := First18.mem_point (List.mem_of_mem_drop (List.mem_of_mem_drop (List.mem_of_mem_drop hp)))
      (try dsimp only [Wire] at *); omega
    · have hg' := List.mem_of_mem_take hg
      simp only [anc12, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg'
      rcases hg' with hg' | rfl | rfl | rfl | rfl
      · have := mem_anc16.mp hg'; (try dsimp only [Wire] at *); omega
      · decide
      · decide
      · decide
      · decide

/-! ### Part 5: Chained 4-pass program + fused 9-bit fixup + root seeding -/

def tree9 : UnaryActionTree := tableAddressTree First18.high 0 1

def fixRec9 : Nat :=
  MeasuredClear.recordMeasurements (MeasuredClear.recordUnaryOps tree9 836 First18.clearPaths) + 511

theorem fixRec9_eq : fixRec9 = 1022 := by
  rw [fixRec9, tree9, First18.clear_measurements]

def allData : List (MeasuredClear.ClearPort 262144) :=
  pass1.clearData ++ pass2.clearData ++ pass3.clearData ++ pass4.clearData

theorem pass1_nums : pass1.k = 2 ∧ pass1.m = 394 ∧ pass1.selMeas = 65535 ∧ pass1.garbLen = 1182 := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> simp [Pass.selMeas, Pass.garbLen, pass1]
theorem pass2_nums : pass2.k = 4 ∧ pass2.m = 74 ∧ pass2.selMeas = 16383 ∧ pass2.garbLen = 1110 := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> simp [Pass.selMeas, Pass.garbLen, pass2]
theorem pass3_nums : pass3.k = 5 ∧ pass3.m = 34 ∧ pass3.selMeas = 8191 ∧ pass3.garbLen = 1054 := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> simp [Pass.selMeas, Pass.garbLen, pass3]
theorem pass4_nums : pass4.k = 6 ∧ pass4.m = 11 ∧ pass4.selMeas = 4095 ∧ pass4.garbLen = 693 := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> simp [Pass.selMeas, Pass.garbLen, pass4]

theorem allData_length : allData.length = 4039 := by
  simp only [allData, List.length_append, pass1.clearData_length pass1_geo,
    pass2.clearData_length pass2_geo, pass3.clearData_length pass3_geo,
    pass4.clearData_length pass4_geo, pass1_nums.2.2.2, pass2_nums.2.2.2,
    pass3_nums.2.2.2, pass4_nums.2.2.2]

attribute [local irreducible] pass1 pass2 pass3 pass4 allData tree9

def stepFix (c : Nat) (rs : List (Fin c)) : Straight 262144 c (c + fixRec9) :=
  castFinish (by rw [fixRec9]; exact Nat.add_assoc c _ 511)
    (MeasuredClear.fixupProgram9 allData rs First18.low First18.hot tree9 836 First18.scratch First18.clearPaths)

def step4 (c : Nat) (rs : List (Fin c)) :
    Straight 262144 c (c + (pass4.selMeas + (pass4.garbLen + fixRec9))) :=
  pass4.stepProg pass4_geo stepFix c rs

def step34 (c : Nat) (rs : List (Fin c)) :
    Straight 262144 c (c + (pass3.selMeas + (pass3.garbLen + (pass4.selMeas + (pass4.garbLen + fixRec9))))) :=
  pass3.stepProg pass3_geo step4 c rs

def step234 (c : Nat) (rs : List (Fin c)) :
    Straight 262144 c (c + (pass2.selMeas + (pass2.garbLen +
      (pass3.selMeas + (pass3.garbLen + (pass4.selMeas + (pass4.garbLen + fixRec9))))))) :=
  pass2.stepProg pass2_geo step34 c rs

theorem total_rec_eq :
    pass1.selMeas + (pass1.garbLen + (pass2.selMeas + (pass2.garbLen +
      (pass3.selMeas + (pass3.garbLen + (pass4.selMeas + (pass4.garbLen + fixRec9))))))) = 99265 := by
  rw [fixRec9_eq, pass1_nums.2.2.1, pass1_nums.2.2.2, pass2_nums.2.2.1, pass2_nums.2.2.2,
    pass3_nums.2.2.1, pass3_nums.2.2.2, pass4_nums.2.2.1, pass4_nums.2.2.2]

def rawProgram (start : Nat) : Straight 262144 start (start + 99265) :=
  castFinish (by rw [total_rec_eq])
    (pass1.stepProg pass1_geo step234 start ([] : List (Fin start)))

def program (start : Nat) : Straight 262144 start (start + 99265) :=
  RootPass.seedProgram 836 (rawProgram start)

attribute [local irreducible] stepFix step4 step34 step234 rawProgram program

def stepFixSrc (read : ConstantBit 262144 → Bool) (o : List Bool) : AdaptiveCircuit :=
  MeasuredClear.fixupSource9 allData o read First18.low First18.hot tree9 836 First18.scratch First18.clearPaths

def step4Src (read : ConstantBit 262144 → Bool) (o : List Bool) : AdaptiveCircuit :=
  pass4.stepSrc read (stepFixSrc read) o

def step34Src (read : ConstantBit 262144 → Bool) (o : List Bool) : AdaptiveCircuit :=
  pass3.stepSrc read (step4Src read) o

def step234Src (read : ConstantBit 262144 → Bool) (o : List Bool) : AdaptiveCircuit :=
  pass2.stepSrc read (step34Src read) o

def rawSource (read : ConstantBit 262144 → Bool) : AdaptiveCircuit :=
  pass1.stepSrc read (step234Src read) List.nil

theorem rawProgram_run (read : ConstantBit 262144 → Bool) (start : Nat) (h : Fin start → Bool) :
    ((rawProgram start).instantiate read h).run = (rawSource read).run := by
  have hFix : ∀ c rs hh, ((stepFix c rs).instantiate read hh).run = (stepFixSrc read (rs.map hh)).run := by
    intro c rs hh; rw [stepFix, castFinish_instantiate, MeasuredClear.fixupProgram_run9]; rfl
  have h4 : ∀ c rs hh, ((step4 c rs).instantiate read hh).run = (step4Src read (rs.map hh)).run :=
    fun c rs hh => by rw [step4]; exact pass4.stepProg_run pass4_geo stepFix (stepFixSrc read) read hFix c rs hh
  have h34 : ∀ c rs hh, ((step34 c rs).instantiate read hh).run = (step34Src read (rs.map hh)).run :=
    fun c rs hh => by rw [step34]; exact pass3.stepProg_run pass3_geo step4 (step4Src read) read h4 c rs hh
  have h234 : ∀ c rs hh, ((step234 c rs).instantiate read hh).run = (step234Src read (rs.map hh)).run :=
    fun c rs hh => by rw [step234]; exact pass2.stepProg_run pass2_geo step34 (step34Src read) read h34 c rs hh
  rw [rawProgram, castFinish_instantiate]
  exact pass1.stepProg_run pass1_geo step234 (step234Src read) read h234 start List.nil h

/-! ### Semantics: 4-pass coherent simulation -/

theorem rawSource_coherent (coeffs : Fin 262144 → PointCoeff) (Q : Point) :
    CoherentlyImplementsOn (rawSource (readConstant coeffs Q))
      (Finsupp.lmapDomain ℂ ℂ (fun s => pointWrite (SelectSchedule18.tablePoint coeffs Q
        (tableAddressValue SelectSchedule18.bits s)) s)) SelectSchedule18.Input := by
  let read := readConstant coeffs Q
  let st1 (s : BasisState) := pass1.afterReset read s
  let st2 (s : BasisState) := pass2.afterReset read (st1 s)
  let st3 (s : BasisState) := pass3.afterReset read (st2 s)
  let st4 (s : BasisState) := pass4.afterReset read (st3 s)
  let tgt (s : BasisState) :=
    pointWrite (SelectSchedule18.tablePoint coeffs Q (tableAddressValue SelectSchedule18.bits s)) s
  have h_out1 : pass1.out = p1 := by unfold pass1; rfl
  have h_out2 : pass2.out = p2 := by unfold pass2; rfl
  have h_out3 : pass3.out = p3 := by unfold pass3; rfl
  have h_out4 : pass4.out = p4 := by unfold pass4; rfl
  have h_s1 : pass1.sliceSlots = s1 := by unfold pass1; rfl
  have h_s2 : pass2.sliceSlots = s2 := by unfold pass2; rfl
  have h_s3 : pass3.sliceSlots = s3 := by unfold pass3; rfl
  have h_s4 : pass4.sliceSlots = s4 := by unfold pass4; rfl
  have h_in_range519 (s : BasisState) (hs : SelectSchedule18.Input s) (w : Wire)
      (hw : 519 ≤ w ∧ w < 535) : s w = false :=
    First18.input_clean s hs w (by (try dsimp only [Wire] at *); omega) (by (try dsimp only [Wire] at *); omega)
      (by (try dsimp only [Wire] at *); omega)
  have h_paths1 (s : BasisState) (hs : SelectSchedule18.Input s) : Clean pass1.selPaths s := fun w hw => by
    have : 519 ≤ w ∧ w < 535 := by unfold pass1 at hw; dsimp only at hw; simp only [List.mem_range'_1] at hw; (try dsimp only [Wire] at *); omega
    exact h_in_range519 s hs w this
  have h_paths2_s (s : BasisState) (hs : SelectSchedule18.Input s) : Clean pass2.selPaths s := fun w hw => by
    have : 519 ≤ w ∧ w < 535 := by unfold pass2 at hw; dsimp only at hw; simp only [List.mem_range'_1] at hw; (try dsimp only [Wire] at *); omega
    exact h_in_range519 s hs w this
  have h_paths3_s (s : BasisState) (hs : SelectSchedule18.Input s) : Clean pass3.selPaths s := fun w hw => by
    have : 519 ≤ w ∧ w < 535 := by unfold pass3 at hw; dsimp only at hw; simp only [List.mem_range'_1] at hw; (try dsimp only [Wire] at *); omega
    exact h_in_range519 s hs w this
  have h_paths4_s (s : BasisState) (hs : SelectSchedule18.Input s) : Clean pass4.selPaths s := fun w hw => by
    have : 519 ≤ w ∧ w < 535 := by unfold pass4 at hw; dsimp only at hw; simp only [List.mem_range'_1] at hw; (try dsimp only [Wire] at *); omega
    exact h_in_range519 s hs w this
  have h_clean_reg (P : Pass) (g : P.Geo) (s : BasisState) (hs : SelectSchedule18.Input s) :
      Clean (P.out ++ P.garb) s := fun w hw => by
    have hn : w ∉ 836 :: SelectSchedule18.bits ++ P.selPaths :=
      fun hm => List.disjoint_left.mp g.hdisj_sel hm hw
    exact hs.2 w (fun e => hn (by simp [e])) (fun hm => hn (by simp [hm]))
  -- Disjointness of p1, p2, p3, p4 from each other and from non-point wires
  have hp1_not_p2 : p1.Disjoint p2 := List.disjoint_left.mpr (fun w h1 h2 =>
    List.disjoint_left.mp p1_disj_rem1 h1 (List.mem_of_mem_take h2))
  have hp1_not_p3 : p1.Disjoint p3 := List.disjoint_left.mpr (fun w h1 h3 =>
    List.disjoint_left.mp p1_disj_rem1 h1 (List.mem_of_mem_drop (List.mem_of_mem_take h3)))
  have hp1_not_p4 : p1.Disjoint p4 := List.disjoint_left.mpr (fun w h1 h4 =>
    List.disjoint_left.mp p1_disj_rem1 h1 (List.mem_of_mem_drop (List.mem_of_mem_drop h4)))
  have hp2_not_p3 : p2.Disjoint p3 := List.disjoint_left.mpr (fun w h2 h3 =>
    List.disjoint_left.mp p2_disj_rem2 h2 (List.mem_of_mem_take h3))
  have hp2_not_p4 : p2.Disjoint p4 := List.disjoint_left.mpr (fun w h2 h4 =>
    List.disjoint_left.mp p2_disj_rem2 h2 (List.mem_of_mem_drop h4))
  have hp3_not_p4 : p3.Disjoint p4 := List.disjoint_left.mpr (fun w h3 h4 => by
    have hnd : (p3 ++ p4).Nodup := by simpa only [p3, p4, rem3, List.take_append_drop] using rem2_nodup
    exact (List.nodup_append.mp hnd).2.2 w h3 w h4 rfl)
  have hp1_not_garb2 : p1.Disjoint pass2.garb := by
    apply List.disjoint_left.mpr
    intro w h1 hg
    unfold pass2 at hg
    rcases List.mem_append.mp (List.mem_of_mem_take hg) with ha | hr
    · have hpt := First18.mem_point (List.mem_of_mem_take h1)
      simp only [anc14, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with ha | rfl | rfl
      · exact List.disjoint_left.mp anc16_disj_point ha (List.mem_of_mem_take h1)
      · (try dsimp only [Wire] at *); omega
      · (try dsimp only [Wire] at *); omega
    · exact List.disjoint_left.mp p1_disj_rem1 h1 (List.mem_of_mem_drop hr)
  have hp_not_anc13 (w : Wire) (hw : w ∈ pointLogicalWires) (hg : w ∈ pass3.garb) : False := by
    unfold pass3 at hg
    have hg' := List.mem_of_mem_take hg
    have hpt := First18.mem_point hw
    simp only [anc13, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg'
    rcases hg' with hg' | rfl | rfl | rfl
    · exact List.disjoint_left.mp anc16_disj_point hg' hw
    · (try dsimp only [Wire] at *); omega
    · (try dsimp only [Wire] at *); omega
    · (try dsimp only [Wire] at *); omega
  have hp_not_anc12 (w : Wire) (hw : w ∈ pointLogicalWires) (hg : w ∈ pass4.garb) : False := by
    unfold pass4 at hg
    have hg' := List.mem_of_mem_take hg
    have hpt := First18.mem_point hw
    simp only [anc12, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg'
    rcases hg' with hg' | rfl | rfl | rfl | rfl
    · exact List.disjoint_left.mp anc16_disj_point hg' hw
    · (try dsimp only [Wire] at *); omega
    · (try dsimp only [Wire] at *); omega
    · (try dsimp only [Wire] at *); omega
    · (try dsimp only [Wire] at *); omega
  -- Per-pass preconditions, frames, loaded words, and clearData facts
  have hpre1 : ∀ s, SelectSchedule18.Input s →
      Clean pass1.selPaths s ∧ s 836 = true ∧ Clean (pass1.out ++ pass1.garb) s :=
    fun s hs => ⟨h_paths1 s hs, hs.1, h_clean_reg pass1 pass1_geo s hs⟩
  have hfr1 : ∀ s, SelectSchedule18.Input s → ∀ w, w ∉ p1 → st1 s w = s w := fun s hs w hw =>
    (pass1.afterReset_facts pass1_geo read s hs.1 (h_clean_reg pass1 pass1_geo s hs)).1 w (by rwa [h_out1])
  have hval1 : ∀ s, SelectSchedule18.Input s →
      wireValues p1 (st1 s) = sliceWord s1 read (tableAddressValue SelectSchedule18.bits s) := fun s hs => by
    have h := (pass1.afterReset_facts pass1_geo read s hs.1 (h_clean_reg pass1 pass1_geo s hs)).2
    rwa [h_out1, h_s1] at h
  have hclr1 : ∀ s, SelectSchedule18.Input s → ∀ q ∈ pass1.clearData,
      (pass1.afterSwap read s) q.target =
        (true && decide (read (q.ref (tableAddressValue SelectSchedule18.bits s)) = q.value)) :=
    fun s hs => (pass1.afterSwap_facts pass1_geo read s hs.1 (h_clean_reg pass1 pass1_geo s hs)).2.2
  have haddr1 (s : BasisState) (hs : SelectSchedule18.Input s) :
      tableAddressValue SelectSchedule18.bits (st1 s) = tableAddressValue SelectSchedule18.bits s :=
    tableAddressValue_congr _ _ _ (fun w hw => hfr1 s hs w (fun h1 =>
      Single.select18_not_point w hw (List.mem_of_mem_take h1)))
  have hpre2 : ∀ s, SelectSchedule18.Input s →
      Clean pass2.selPaths (st1 s) ∧ st1 s 836 = true ∧ Clean (pass2.out ++ pass2.garb) (st1 s) := by
    intro s hs
    refine ⟨fun w hw => ?_, ?_, fun w hw => ?_⟩
    · have hnp : w ∉ p1 := fun h1 => by
        have hpt := First18.mem_point (List.mem_of_mem_take h1)
        unfold pass2 at hw; simp only [List.mem_range'_1] at hw; (try dsimp only [Wire] at *); omega
      rw [hfr1 s hs w hnp]; exact h_paths2_s s hs w hw
    · rw [hfr1 s hs 836 (fun h1 => by have := First18.mem_point (List.mem_of_mem_take h1); (try dsimp only [Wire] at *); omega)]
      exact hs.1
    · have hnp : w ∉ p1 := fun h1 => by
        rcases List.mem_append.mp hw with h2 | hg2
        · rw [h_out2] at h2; exact List.disjoint_left.mp hp1_not_p2 h1 h2
        · exact List.disjoint_left.mp hp1_not_garb2 h1 hg2
      rw [hfr1 s hs w hnp]; exact h_clean_reg pass2 pass2_geo s hs w hw
  have hfr2 : ∀ s, SelectSchedule18.Input s → ∀ w, w ∉ p2 → st2 s w = st1 s w := fun s hs w hw =>
    (pass2.afterReset_facts pass2_geo read (st1 s) (hpre2 s hs).2.1 (hpre2 s hs).2.2).1 w (by rwa [h_out2])
  have hval2 : ∀ s, SelectSchedule18.Input s →
      wireValues p2 (st2 s) = sliceWord s2 read (tableAddressValue SelectSchedule18.bits s) := fun s hs => by
    have h := (pass2.afterReset_facts pass2_geo read (st1 s) (hpre2 s hs).2.1 (hpre2 s hs).2.2).2
    rwa [h_out2, h_s2, haddr1 s hs] at h
  have hclr2 : ∀ s, SelectSchedule18.Input s → ∀ q ∈ pass2.clearData,
      (pass2.afterSwap read (st1 s)) q.target =
        (true && decide (read (q.ref (tableAddressValue SelectSchedule18.bits s)) = q.value)) := fun s hs => by
    have h := (pass2.afterSwap_facts pass2_geo read (st1 s) (hpre2 s hs).2.1 (hpre2 s hs).2.2).2.2
    rwa [haddr1 s hs] at h
  have haddr2 (s : BasisState) (hs : SelectSchedule18.Input s) :
      tableAddressValue SelectSchedule18.bits (st2 s) = tableAddressValue SelectSchedule18.bits s :=
    (tableAddressValue_congr _ _ _ (fun w hw => hfr2 s hs w (fun h2 =>
      Single.select18_not_point w hw (List.mem_of_mem_drop (List.mem_of_mem_take h2))))).trans (haddr1 s hs)
  have hpre3 : ∀ s, SelectSchedule18.Input s →
      Clean pass3.selPaths (st2 s) ∧ st2 s 836 = true ∧ Clean (pass3.out ++ pass3.garb) (st2 s) := by
    intro s hs
    have hnp12 (w : Wire) (h1 : w ∉ p1) (h2 : w ∉ p2) : st2 s w = s w :=
      (hfr2 s hs w h2).trans (hfr1 s hs w h1)
    refine ⟨fun w hw => ?_, ?_, fun w hw => ?_⟩
    · have hnp : w ∉ pointLogicalWires := fun hp => by
        have hpt := First18.mem_point hp
        unfold pass3 at hw; simp only [List.mem_range'_1] at hw; (try dsimp only [Wire] at *); omega
      rw [hnp12 w (fun h => hnp (List.mem_of_mem_take h)) (fun h => hnp (List.mem_of_mem_drop (List.mem_of_mem_take h)))]
      exact h_paths3_s s hs w hw
    · have hnp : (836 : Wire) ∉ pointLogicalWires := fun hp => by
        have := First18.mem_point hp; (try dsimp only [Wire] at *); omega
      rw [hnp12 836 (fun h => hnp (List.mem_of_mem_take h)) (fun h => hnp (List.mem_of_mem_drop (List.mem_of_mem_take h)))]
      exact hs.1
    · have hnp1 : w ∉ p1 := fun h1 => by
        rcases List.mem_append.mp hw with h3 | hg3
        · rw [h_out3] at h3; exact List.disjoint_left.mp hp1_not_p3 h1 h3
        · exact hp_not_anc13 w (List.mem_of_mem_take h1) hg3
      have hnp2 : w ∉ p2 := fun h2 => by
        rcases List.mem_append.mp hw with h3 | hg3
        · rw [h_out3] at h3; exact List.disjoint_left.mp hp2_not_p3 h2 h3
        · exact hp_not_anc13 w (List.mem_of_mem_drop (List.mem_of_mem_take h2)) hg3
      rw [hnp12 w hnp1 hnp2]; exact h_clean_reg pass3 pass3_geo s hs w hw
  have hfr3 : ∀ s, SelectSchedule18.Input s → ∀ w, w ∉ p3 → st3 s w = st2 s w := fun s hs w hw =>
    (pass3.afterReset_facts pass3_geo read (st2 s) (hpre3 s hs).2.1 (hpre3 s hs).2.2).1 w (by rwa [h_out3])
  have hval3 : ∀ s, SelectSchedule18.Input s →
      wireValues p3 (st3 s) = sliceWord s3 read (tableAddressValue SelectSchedule18.bits s) := fun s hs => by
    have h := (pass3.afterReset_facts pass3_geo read (st2 s) (hpre3 s hs).2.1 (hpre3 s hs).2.2).2
    rwa [h_out3, h_s3, haddr2 s hs] at h
  have hclr3 : ∀ s, SelectSchedule18.Input s → ∀ q ∈ pass3.clearData,
      (pass3.afterSwap read (st2 s)) q.target =
        (true && decide (read (q.ref (tableAddressValue SelectSchedule18.bits s)) = q.value)) := fun s hs => by
    have h := (pass3.afterSwap_facts pass3_geo read (st2 s) (hpre3 s hs).2.1 (hpre3 s hs).2.2).2.2
    rwa [haddr2 s hs] at h
  have haddr3 (s : BasisState) (hs : SelectSchedule18.Input s) :
      tableAddressValue SelectSchedule18.bits (st3 s) = tableAddressValue SelectSchedule18.bits s :=
    (tableAddressValue_congr _ _ _ (fun w hw => hfr3 s hs w (fun h3 =>
      Single.select18_not_point w hw (List.mem_of_mem_drop (List.mem_of_mem_drop (List.mem_of_mem_take h3)))))).trans (haddr2 s hs)
  have hpre4 : ∀ s, SelectSchedule18.Input s →
      Clean pass4.selPaths (st3 s) ∧ st3 s 836 = true ∧ Clean (pass4.out ++ pass4.garb) (st3 s) := by
    intro s hs
    have hnp123 (w : Wire) (h1 : w ∉ p1) (h2 : w ∉ p2) (h3 : w ∉ p3) : st3 s w = s w :=
      (hfr3 s hs w h3).trans ((hfr2 s hs w h2).trans (hfr1 s hs w h1))
    refine ⟨fun w hw => ?_, ?_, fun w hw => ?_⟩
    · have hnp : w ∉ pointLogicalWires := fun hp => by
        have hpt := First18.mem_point hp
        unfold pass4 at hw; simp only [List.mem_range'_1] at hw; (try dsimp only [Wire] at *); omega
      rw [hnp123 w (fun h => hnp (List.mem_of_mem_take h))
        (fun h => hnp (List.mem_of_mem_drop (List.mem_of_mem_take h)))
        (fun h => hnp (List.mem_of_mem_drop (List.mem_of_mem_drop (List.mem_of_mem_take h))))]
      exact h_paths4_s s hs w hw
    · have hnp : (836 : Wire) ∉ pointLogicalWires := fun hp => by
        have := First18.mem_point hp; (try dsimp only [Wire] at *); omega
      rw [hnp123 836 (fun h => hnp (List.mem_of_mem_take h))
        (fun h => hnp (List.mem_of_mem_drop (List.mem_of_mem_take h)))
        (fun h => hnp (List.mem_of_mem_drop (List.mem_of_mem_drop (List.mem_of_mem_take h))))]
      exact hs.1
    · have hnp1 : w ∉ p1 := fun h1 => by
        rcases List.mem_append.mp hw with h4 | hg4
        · rw [h_out4] at h4; exact List.disjoint_left.mp hp1_not_p4 h1 h4
        · exact hp_not_anc12 w (List.mem_of_mem_take h1) hg4
      have hnp2 : w ∉ p2 := fun h2 => by
        rcases List.mem_append.mp hw with h4 | hg4
        · rw [h_out4] at h4; exact List.disjoint_left.mp hp2_not_p4 h2 h4
        · exact hp_not_anc12 w (List.mem_of_mem_drop (List.mem_of_mem_take h2)) hg4
      have hnp3 : w ∉ p3 := fun h3 => by
        rcases List.mem_append.mp hw with h4 | hg4
        · rw [h_out4] at h4; exact List.disjoint_left.mp hp3_not_p4 h3 h4
        · exact hp_not_anc12 w (List.mem_of_mem_drop (List.mem_of_mem_drop (List.mem_of_mem_take h3))) hg4
      rw [hnp123 w hnp1 hnp2 hnp3]; exact h_clean_reg pass4 pass4_geo s hs w hw
  have hfr4 : ∀ s, SelectSchedule18.Input s → ∀ w, w ∉ p4 → st4 s w = st3 s w := fun s hs w hw =>
    (pass4.afterReset_facts pass4_geo read (st3 s) (hpre4 s hs).2.1 (hpre4 s hs).2.2).1 w (by rwa [h_out4])
  have hval4 : ∀ s, SelectSchedule18.Input s →
      wireValues p4 (st4 s) = sliceWord s4 read (tableAddressValue SelectSchedule18.bits s) := fun s hs => by
    have h := (pass4.afterReset_facts pass4_geo read (st3 s) (hpre4 s hs).2.1 (hpre4 s hs).2.2).2
    rwa [h_out4, h_s4, haddr3 s hs] at h
  have hclr4 : ∀ s, SelectSchedule18.Input s → ∀ q ∈ pass4.clearData,
      (pass4.afterSwap read (st3 s)) q.target =
        (true && decide (read (q.ref (tableAddressValue SelectSchedule18.bits s)) = q.value)) := fun s hs => by
    have h := (pass4.afterSwap_facts pass4_geo read (st3 s) (hpre4 s hs).2.1 (hpre4 s hs).2.2).2.2
    rwa [haddr3 s hs] at h
  -- Final basis state equality: st4 s = tgt s
  have hst4_out (s : BasisState) (hs : SelectSchedule18.Input s) (w : Wire) (hw : w ∉ pointLogicalWires) :
      st4 s w = s w := by
    have h1234 : w ∉ p1 ∧ w ∉ p2 ∧ w ∉ p3 ∧ w ∉ p4 := by
      have hm := (p_mem_point w).not.mpr hw; tauto
    exact (hfr4 s hs w h1234.2.2.2).trans ((hfr3 s hs w h1234.2.2.1).trans
      ((hfr2 s hs w h1234.2.1).trans (hfr1 s hs w h1234.1)))
  have hst4_eq (s : BasisState) (hs : SelectSchedule18.Input s) : st4 s = tgt s := by
    have hwp : wireValues pointLogicalWires (st4 s) =
        wireValues pointLogicalWires (tgt s) := by
      have hw1' : wireValues p1 (st4 s) = sliceWord s1 read (tableAddressValue SelectSchedule18.bits s) := by
        rw [← hval1 s hs]
        exact List.map_congr_left (fun w hw => (hfr4 s hs w (List.disjoint_left.mp hp1_not_p4 hw)).trans
          ((hfr3 s hs w (List.disjoint_left.mp hp1_not_p3 hw)).trans
            (hfr2 s hs w (List.disjoint_left.mp hp1_not_p2 hw))))
      have hw2' : wireValues p2 (st4 s) = sliceWord s2 read (tableAddressValue SelectSchedule18.bits s) := by
        rw [← hval2 s hs]
        exact List.map_congr_left (fun w hw => (hfr4 s hs w (List.disjoint_left.mp hp2_not_p4 hw)).trans
          (hfr3 s hs w (List.disjoint_left.mp hp2_not_p3 hw)))
      have hw3' : wireValues p3 (st4 s) = sliceWord s3 read (tableAddressValue SelectSchedule18.bits s) := by
        rw [← hval3 s hs]
        exact List.map_congr_left (fun w hw => hfr4 s hs w (List.disjoint_left.mp hp3_not_p4 hw))
      have hall : wireValues pointLogicalWires (st4 s) =
          First18.word read (tableAddressValue SelectSchedule18.bits s) := by
        rw [← point_split, wireValues, List.map_append, List.map_append, List.map_append]
        change wireValues p1 (st4 s) ++ wireValues p2 (st4 s) ++ wireValues p3 (st4 s) ++ wireValues p4 (st4 s) = _
        rw [hw1', hw2', hw3', hval4 s hs]
        simp only [sliceWord, ← List.map_append, slots_split, First18.word, First18.pointRefs_slots, List.map_map]
        rfl
      rw [hall]
      dsimp only [tgt]
      rw [pointWrite_word, First18.word, pointRefs_read]
      rfl
    funext w
    by_cases hp : w ∈ pointLogicalWires
    · exact List.map_inj_left.mp hwp w hp
    · rw [hst4_out s hs w hp]; dsimp only [tgt]; rw [pointWrite_frame _ _ w hp]
  -- Apply 4 nested stepSrc_sim + fixupSource_coherent9!
  have htree_lay : tree9.Layout 836 First18.clearPaths := by unfold tree9; exact First18.clear_layout
  have htree_hdisj : (MeasuredClear.hotBank9 First18.hot).Disjoint
      (836 :: tree9.indexWires.dedup ++ First18.clearPaths) := by unfold tree9; exact First18.hot_disjoint
  have htree_scr : First18.scratch ∉ 836 :: tree9.indexWires.dedup ++ First18.clearPaths := by
    unfold tree9; exact First18.scratch_not_tree
  have hst4_hot (s : BasisState) (hs : SelectSchedule18.Input s) :
      MeasuredClear.HotClean9 First18.hot (st4 s) := fun i => by
    have hhi : 873 ≤ First18.hot i ∧ First18.hot i < 1385 := by
      have := i.isLt; simp only [First18.hot]; (try dsimp only [Wire] at *); omega
    rw [hst4_out s hs (First18.hot i) (fun hp => by have := First18.mem_point hp; (try dsimp only [Wire] at *); omega)]
    exact First18.input_clean s hs (First18.hot i) (by (try dsimp only [Wire] at *); omega)
      (by (try dsimp only [Wire] at *); omega) (by (try dsimp only [Wire] at *); omega)
  have hst4_cpaths (s : BasisState) (hs : SelectSchedule18.Input s) : Clean First18.clearPaths (st4 s) := fun w hw => by
    simp only [First18.clearPaths, List.mem_range'_1] at hw
    rw [hst4_out s hs w (fun hp => by have := First18.mem_point hp; (try dsimp only [Wire] at *); omega)]
    exact First18.input_clean s hs w (by (try dsimp only [Wire] at *); omega)
      (by (try dsimp only [Wire] at *); omega) (by (try dsimp only [Wire] at *); omega)
  have hst4_836 (s : BasisState) (hs : SelectSchedule18.Input s) : st4 s 836 = true := by
    rw [hst4_out s hs 836 (fun hp => by have := First18.mem_point hp; (try dsimp only [Wire] at *); omega)]; exact hs.1
  have hst4_addr (s : BasisState) (hs : SelectSchedule18.Input s) :
      512 * tree9.routeLabel (st4 s) + MeasuredClear.hotAddress9 First18.low (st4 s) =
        tableAddressValue SelectSchedule18.bits s := by
    unfold tree9
    rw [MeasuredClear.splitAddress_value9, First18.low_high_bits]
    exact tableAddressValue_congr _ _ _ (fun w hw => hst4_out s hs w (Single.select18_not_point w hw))
  have hsim := pass1.stepSrc_sim pass1_geo read (step234Src read) List.nil SelectSchedule18.Input id tgt (fun _ => 1) hpre1
    (fun o1 ho1 =>
      pass2.stepSrc_sim pass2_geo read (step34Src read) (List.nil ++ o1) SelectSchedule18.Input st1 tgt
        (fun s => 1 * registerXPhase pass1.targets o1 (pass1.afterSwap read s)) hpre2
        (fun o2 ho2 =>
          pass3.stepSrc_sim pass3_geo read (step4Src read) ((List.nil ++ o1) ++ o2) SelectSchedule18.Input st2 tgt
            (fun s => (1 * registerXPhase pass1.targets o1 (pass1.afterSwap read s)) *
              registerXPhase pass2.targets o2 (pass2.afterSwap read (st1 s))) hpre3
            (fun o3 ho3 =>
              pass4.stepSrc_sim pass4_geo read (stepFixSrc read) (((List.nil ++ o1) ++ o2) ++ o3)
                SelectSchedule18.Input st3 tgt
                (fun s => ((1 * registerXPhase pass1.targets o1 (pass1.afterSwap read s)) *
                  registerXPhase pass2.targets o2 (pass2.afterSwap read (st1 s))) *
                  registerXPhase pass3.targets o3 (pass3.afterSwap read (st2 s))) hpre4
                (fun o4 ho4 => by
                  have hfc := MeasuredClear.fixupSource_coherent9 allData ((((List.nil ++ o1) ++ o2) ++ o3) ++ o4)
                    read First18.low First18.hot tree9 836 First18.scratch First18.clearPaths
                    htree_lay First18.hot_injective First18.low_ne_hot htree_hdisj htree_scr First18.scratch_not_hot
                  obtain ⟨cs, al, ma⟩ := hfc
                  refine ⟨cs, al.imp (fun b c hb s hs => ?_), ma⟩
                  rw [hb (st4 s) ⟨hst4_hot s hs, hst4_cpaths s hs⟩, MeasuredClear.basisIdeal_ket]
                  simp only [id_eq, List.nil_append]
                  have hd1 : o1.length = pass1.clearData.length := by
                    rw [ho1, pass1.targets_length pass1_geo, pass1.clearData_length pass1_geo]
                  have hd2 : o2.length = pass2.clearData.length := by
                    rw [ho2, pass2.targets_length pass2_geo, pass2.clearData_length pass2_geo]
                  have hd3 : o3.length = pass3.clearData.length := by
                    rw [ho3, pass3.targets_length pass3_geo, pass3.clearData_length pass3_geo]
                  have hff : MeasuredClear.fixupFactor9 allData (((o1 ++ o2) ++ o3) ++ o4) read
                      First18.low First18.hot tree9 836 (st4 s) =
                      registerXPhase pass1.targets o1 (pass1.afterSwap read s) *
                      registerXPhase pass2.targets o2 (pass2.afterSwap read (st1 s)) *
                      registerXPhase pass3.targets o3 (pass3.afterSwap read (st2 s)) *
                      registerXPhase pass4.targets o4 (pass4.afterSwap read (st3 s)) := by
                    have ha : allData = ((pass1.clearData ++ pass2.clearData) ++ pass3.clearData) ++ pass4.clearData := by
                      unfold allData; rfl
                    rw [ha,
                      MeasuredClear.fixupFactor9_append _ pass4.clearData ((o1 ++ o2) ++ o3) o4
                        (by simp [hd1, hd2, hd3]),
                      MeasuredClear.fixupFactor9_append _ pass3.clearData (o1 ++ o2) o3
                        (by simp [hd1, hd2]),
                      MeasuredClear.fixupFactor9_append pass1.clearData pass2.clearData o1 o2 hd1]
                    have hf1 := MeasuredClear.fixupFactor9_loaded pass1.clearData o1 read First18.low First18.hot
                      tree9 836 First18.clearPaths First18.hot_injective First18.low_ne_hot htree_hdisj
                      (st4 s) (pass1.afterSwap read s) (hst4_hot s hs)
                      (fun q hq => by rw [hst4_836 s hs, hst4_addr s hs]; exact hclr1 s hs q hq)
                    have hf2 := MeasuredClear.fixupFactor9_loaded pass2.clearData o2 read First18.low First18.hot
                      tree9 836 First18.clearPaths First18.hot_injective First18.low_ne_hot htree_hdisj
                      (st4 s) (pass2.afterSwap read (st1 s)) (hst4_hot s hs)
                      (fun q hq => by rw [hst4_836 s hs, hst4_addr s hs]; exact hclr2 s hs q hq)
                    have hf3 := MeasuredClear.fixupFactor9_loaded pass3.clearData o3 read First18.low First18.hot
                      tree9 836 First18.clearPaths First18.hot_injective First18.low_ne_hot htree_hdisj
                      (st4 s) (pass3.afterSwap read (st2 s)) (hst4_hot s hs)
                      (fun q hq => by rw [hst4_836 s hs, hst4_addr s hs]; exact hclr3 s hs q hq)
                    have hf4 := MeasuredClear.fixupFactor9_loaded pass4.clearData o4 read First18.low First18.hot
                      tree9 836 First18.clearPaths First18.hot_injective First18.low_ne_hot htree_hdisj
                      (st4 s) (pass4.afterSwap read (st3 s)) (hst4_hot s hs)
                      (fun q hq => by rw [hst4_836 s hs, hst4_addr s hs]; exact hclr4 s hs q hq)
                    rw [pass1.clearData_targets pass1_geo] at hf1
                    rw [pass2.clearData_targets pass2_geo] at hf2
                    rw [pass3.clearData_targets pass3_geo] at hf3
                    rw [pass4.clearData_targets pass4_geo] at hf4
                    rw [hf1, hf2, hf3, hf4]
                  rw [hff, hst4_eq s hs, one_mul]))))
  obtain ⟨cs, al, ma⟩ := hsim
  refine ⟨cs, al.imp (fun b c hb s hs => ?_), ma⟩
  simpa only [id_eq, one_smul, First18.lmap_ket] using hb s hs

theorem rawProgram_coherent (coeffs : Fin 262144 → PointCoeff) (Q : Point)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((rawProgram start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (fun s => pointWrite (SelectSchedule18.tablePoint coeffs Q
        (tableAddressValue SelectSchedule18.bits s)) s)) SelectSchedule18.Input := by
  unfold CoherentlyImplementsOn
  rw [rawProgram_run]
  exact rawSource_coherent coeffs Q

/-! ### Resources, root-seeding, and window interface -/

theorem rawProgram_tCount (read : ConstantBit 262144 → Bool) (start : Nat) (h : Fin start → Bool) :
    ((rawProgram start).instantiate read h).tCount = 7 * 99256 := by
  have hlay : tree9.Layout 836 First18.clearPaths := by unfold tree9; exact First18.clear_layout
  have hFix : ∀ c rs hh, ((stepFix c rs).instantiate read hh).tCount = 7 * 1013 := by
    intro c rs hh
    rw [stepFix, castFinish_instantiate,
      MeasuredClear.fixupProgram_tCount9 allData rs First18.low First18.hot tree9 836 First18.scratch
        First18.clearPaths hlay]
    have hn : tree9.internalNodes = 511 := by unfold tree9; exact First18.clear_nodes
    rw [hn]
  have h4 : ∀ c rs hh, ((step4 c rs).instantiate read hh).tCount = 7 * (pass4.selMeas + pass4.garbLen) + 7 * 1013 :=
    fun c rs hh => by rw [step4]; exact pass4.stepProg_tCount pass4_geo stepFix read hFix c rs hh
  have h34 : ∀ c rs hh, ((step34 c rs).instantiate read hh).tCount =
      7 * (pass3.selMeas + pass3.garbLen) + (7 * (pass4.selMeas + pass4.garbLen) + 7 * 1013) :=
    fun c rs hh => by rw [step34]; exact pass3.stepProg_tCount pass3_geo step4 read h4 c rs hh
  have h234 : ∀ c rs hh, ((step234 c rs).instantiate read hh).tCount =
      7 * (pass2.selMeas + pass2.garbLen) +
      (7 * (pass3.selMeas + pass3.garbLen) + (7 * (pass4.selMeas + pass4.garbLen) + 7 * 1013)) :=
    fun c rs hh => by rw [step234]; exact pass2.stepProg_tCount pass2_geo step34 read h34 c rs hh
  rw [rawProgram, castFinish_instantiate, pass1.stepProg_tCount pass1_geo step234 read h234,
    pass1_nums.2.2.1, pass1_nums.2.2.2, pass2_nums.2.2.1, pass2_nums.2.2.2,
    pass3_nums.2.2.1, pass3_nums.2.2.2, pass4_nums.2.2.1, pass4_nums.2.2.2]

theorem rawProgram_residue (start : Nat) : residue (rawProgram start) = 0 := by
  have hFix : ∀ c rs, residue (stepFix c rs) = 0 := fun c rs => by
    rw [stepFix, residue_cast]; exact MeasuredClear.fixupProgram_residue9 _ _ _ _ _ _ _ _
  have h4 : ∀ c rs, residue (step4 c rs) = 0 := fun c rs => by
    rw [step4]; exact pass4.stepProg_residue pass4_geo stepFix hFix c rs
  have h34 : ∀ c rs, residue (step34 c rs) = 0 := fun c rs => by
    rw [step34]; exact pass3.stepProg_residue pass3_geo step4 h4 c rs
  have h234 : ∀ c rs, residue (step234 c rs) = 0 := fun c rs => by
    rw [step234]; exact pass2.stepProg_residue pass2_geo step34 h34 c rs
  rw [rawProgram, residue_cast]
  exact pass1.stepProg_residue pass1_geo step234 h234 start List.nil

theorem rawProgram_added (start : Nat) : added (rawProgram start) = 99256 := by
  have h := exact_t (rawProgram start) (rawProgram_residue start) (fun _ => false) (fun _ => false)
  have ht := rawProgram_tCount (fun _ => false) start (fun _ => false)
  exact Nat.eq_of_mul_eq_mul_left (by decide) (h.symm.trans ht)

theorem rawProgram_slots (start : Nat) : (rawProgram start).gateSlots ≤ 4500000000 := by
  have hlay : tree9.Layout 836 First18.clearPaths := by unfold tree9; exact First18.clear_layout
  have hFix : ∀ c rs, (stepFix c rs).gateSlots ≤ 4240000000 := fun c rs => by
    rw [stepFix, castFinish_gateSlots,
      MeasuredClear.fixupProgram_slots9 allData rs First18.low First18.hot tree9 836 First18.scratch
        First18.clearPaths hlay]
    have hl : tree9.leaves = 512 := by unfold tree9; exact First18.clear_leaves
    have hn : tree9.internalNodes = 511 := by unfold tree9; exact First18.clear_nodes
    have hm : min allData.length rs.length ≤ 4039 := (Nat.min_le_left _ _).trans (by rw [allData_length])
    rw [hl, hn]
    omega
  have h4 : ∀ c rs, (step4 c rs).gateSlots ≤
      (2 ^ pass4.k * pass4.m) * (pass4.selMeas + 1) + 10 * pass4.selMeas + 3 * pass4.garbLen + 4240000000 :=
    fun c rs => by rw [step4]; exact pass4.stepProg_slots pass4_geo stepFix hFix c rs
  have h34 : ∀ c rs, (step34 c rs).gateSlots ≤
      (2 ^ pass3.k * pass3.m) * (pass3.selMeas + 1) + 10 * pass3.selMeas + 3 * pass3.garbLen +
      ((2 ^ pass4.k * pass4.m) * (pass4.selMeas + 1) + 10 * pass4.selMeas + 3 * pass4.garbLen + 4240000000) :=
    fun c rs => by rw [step34]; exact pass3.stepProg_slots pass3_geo step4 h4 c rs
  have h234 : ∀ c rs, (step234 c rs).gateSlots ≤
      (2 ^ pass2.k * pass2.m) * (pass2.selMeas + 1) + 10 * pass2.selMeas + 3 * pass2.garbLen +
      ((2 ^ pass3.k * pass3.m) * (pass3.selMeas + 1) + 10 * pass3.selMeas + 3 * pass3.garbLen +
      ((2 ^ pass4.k * pass4.m) * (pass4.selMeas + 1) + 10 * pass4.selMeas + 3 * pass4.garbLen + 4240000000)) :=
    fun c rs => by rw [step234]; exact pass2.stepProg_slots pass2_geo step34 h34 c rs
  rw [rawProgram, castFinish_gateSlots]
  refine (pass1.stepProg_slots pass1_geo step234 h234 start List.nil).trans ?_
  rw [pass1_nums.1, pass1_nums.2.1, pass1_nums.2.2.1, pass1_nums.2.2.2,
    pass2_nums.1, pass2_nums.2.1, pass2_nums.2.2.1, pass2_nums.2.2.2,
    pass3_nums.1, pass3_nums.2.1, pass3_nums.2.2.1, pass3_nums.2.2.2,
    pass4_nums.1, pass4_nums.2.1, pass4_nums.2.2.1, pass4_nums.2.2.2]
  norm_num

theorem rawProgram_wellFormed (start : Nat) : (rawProgram start).WellFormed := by
  have hlay : tree9.Layout 836 First18.clearPaths := by unfold tree9; exact First18.clear_layout
  have hscr : First18.scratch ∉ 836 :: tree9.indexWires.dedup ++ First18.clearPaths := by
    unfold tree9; exact First18.scratch_not_tree
  have hFix : ∀ c rs, (stepFix c rs).WellFormed := fun c rs => by
    rw [stepFix, castFinish_wellFormed]
    exact MeasuredClear.fixupProgram_wellFormed9 allData rs First18.low First18.hot tree9 836 First18.scratch
      First18.clearPaths hlay First18.hot_injective First18.low_ne_hot hscr First18.scratch_not_hot
  have h4 : ∀ c rs, (step4 c rs).WellFormed := fun c rs => by
    rw [step4]; exact pass4.stepProg_wellFormed pass4_geo stepFix hFix c rs
  have h34 : ∀ c rs, (step34 c rs).WellFormed := fun c rs => by
    rw [step34]; exact pass3.stepProg_wellFormed pass3_geo step4 h4 c rs
  have h234 : ∀ c rs, (step234 c rs).WellFormed := fun c rs => by
    rw [step234]; exact pass2.stepProg_wellFormed pass2_geo step34 h34 c rs
  rw [rawProgram, castFinish_wellFormed]
  exact pass1.stepProg_wellFormed pass1_geo step234 h234 start List.nil

theorem rawProgram_support (start : Nat) : straightWires (rawProgram start) ⊆ List.range 1613 := by
  have hFix : ∀ c rs, straightWires (stepFix c rs) ⊆ List.range 1613 := fun c rs => by
    rw [stepFix, straightWires_castFinish, RootPass.straightWires_eq_naive]
    apply MeasuredClear.fixupProgram_within9
    · decide
    · decide
    · intro i; rw [List.mem_range]; have := i.isLt; simp only [First18.low]; (try dsimp only [Wire] at *); omega
    · intro i; rw [List.mem_range]; have := i.isLt; simp only [First18.hot]; (try dsimp only [Wire] at *); omega
    · intro w hw
      have hi : w ∈ First18.high := by
        unfold tree9 at hw
        exact (tableAddressTree_mem_index First18.high 0 1 w).mp hw
      rw [List.mem_range]
      simp only [First18.high, List.mem_append, List.mem_range'_1, List.mem_singleton] at hi
      (try dsimp only [Wire] at *); omega
    · intro w hw
      rw [List.mem_range]
      simp only [First18.clearPaths, List.mem_range'_1] at hw
      (try dsimp only [Wire] at *); omega
  have h4 : ∀ c rs, straightWires (step4 c rs) ⊆ List.range 1613 := fun c rs => by
    rw [step4]; exact pass4.stepProg_support pass4_geo stepFix hFix c rs
  have h34 : ∀ c rs, straightWires (step34 c rs) ⊆ List.range 1613 := fun c rs => by
    rw [step34]; exact pass3.stepProg_support pass3_geo step4 h4 c rs
  have h234 : ∀ c rs, straightWires (step234 c rs) ⊆ List.range 1613 := fun c rs => by
    rw [step234]; exact pass2.stepProg_support pass2_geo step34 h34 c rs
  rw [rawProgram, straightWires_castFinish]
  exact pass1.stepProg_support pass1_geo step234 h234 start List.nil

theorem rawProgram_safe836 (start : Nat) : RootPass.safeProgram 836 (rawProgram start) := by
  have hlay : tree9.Layout 836 First18.clearPaths := by unfold tree9; exact First18.clear_layout
  obtain ⟨hb, hp⟩ := RootPass.layout_avoids hlay
  have hFix : ∀ c rs, RootPass.safeProgram 836 (stepFix c rs) := fun c rs => by
    rw [stepFix, RootPass.safeProgram_cast]
    exact RootPass.fixupProgram9_safe 836 allData rs First18.low First18.hot tree9 836 First18.scratch
      First18.clearPaths RootPass.first18_low_ne RootPass.first18_hot_ne (by decide) hb hp
  have h4 : ∀ c rs, RootPass.safeProgram 836 (step4 c rs) := fun c rs => by
    rw [step4]; exact pass4.stepProg_safe836 pass4_geo stepFix hFix c rs
  have h34 : ∀ c rs, RootPass.safeProgram 836 (step34 c rs) := fun c rs => by
    rw [step34]; exact pass3.stepProg_safe836 pass3_geo step4 h4 c rs
  have h234 : ∀ c rs, RootPass.safeProgram 836 (step234 c rs) := fun c rs => by
    rw [step234]; exact pass2.stepProg_safe836 pass2_geo step34 h34 c rs
  rw [rawProgram, RootPass.safeProgram_cast]
  exact pass1.stepProg_safe836 pass1_geo step234 h234 start List.nil

theorem rawProgram_hits836 (start : Nat) : RootPass.literalHits 836 (rawProgram start) = 5 := by
  have hlay : tree9.Layout 836 First18.clearPaths := by unfold tree9; exact First18.clear_layout
  have hnodes : tree9.internalNodes = 511 := by unfold tree9; exact First18.clear_nodes
  have hFix : ∀ c rs, RootPass.literalHits 836 (stepFix c rs) = 1 := fun c rs => by
    rw [stepFix, RootPass.literalHits_cast,
      RootPass.fixupProgram9_hits 836 allData rs First18.low First18.hot tree9 836 First18.scratch
        First18.clearPaths RootPass.first18_low_ne RootPass.first18_hot_ne]
    exact RootPass.recordUnaryOps_root_hits 836 tree9 First18.clearPaths hlay (by rw [hnodes]; decide)
  have h4 : ∀ c rs, RootPass.literalHits 836 (step4 c rs) = 2 := fun c rs => by
    rw [step4]; exact pass4.stepProg_hits836 pass4_geo stepFix hFix c rs
  have h34 : ∀ c rs, RootPass.literalHits 836 (step34 c rs) = 3 := fun c rs => by
    rw [step34]; exact pass3.stepProg_hits836 pass3_geo step4 h4 c rs
  have h234 : ∀ c rs, RootPass.literalHits 836 (step234 c rs) = 4 := fun c rs => by
    rw [step234]; exact pass2.stepProg_hits836 pass2_geo step34 h34 c rs
  rw [rawProgram, RootPass.literalHits_cast]
  exact pass1.stepProg_hits836 pass1_geo step234 h234 start List.nil

theorem program_coherent (coeffs : Fin 262144 → PointCoeff) (Q : Point)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((program start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (fun s => pointWrite (SelectSchedule18.tablePoint coeffs Q
        (tableAddressValue SelectSchedule18.bits s)) s)) SelectSchedule18.Input := by
  rw [program]
  exact RootPass.seedProgram_coherent 836 (rawProgram start) _ history _ _
    (rawProgram_safe836 start) (fun _ hs => hs.1) (rawProgram_coherent coeffs Q start history)

theorem program_residue (start : Nat) : residue (program start) = 0 := by
  have h := RootPass.seedProgram_residue_le 836 (rawProgram start)
  rw [rawProgram_residue] at h
  rw [program]
  exact Nat.eq_zero_of_le_zero h

theorem program_added (start : Nat) : added (program start) = 99251 := by
  have h := RootPass.seedProgram_added 836 (rawProgram start)
  rw [rawProgram_added, rawProgram_hits836] at h
  rw [program]
  omega

theorem program_slots (start : Nat) : (program start).gateSlots ≤ 4500000000 := by
  rw [program, RootPass.seedProgram_slots]
  exact rawProgram_slots start

theorem program_support (start : Nat) : straightWires (program start) ⊆ List.range 1613 := by
  rw [program]
  exact (RootPass.seedProgram_wires 836 _).trans (rawProgram_support start)

theorem program_wellFormed (start : Nat) : (program start).WellFormed := by
  rw [program]
  exact RootPass.seedProgram_wellFormed 836 _ (rawProgram_wellFormed start)

def windowGeneric {n : Nat} (rows : Fin 262144 → Fin n) : Single.Window n :=
  ⟨SelectSchedule18.bits.reverse, 99265, fun start => reindexStraight rows (program start)⟩

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
    ((windowGeneric rows).program start).gateSlots ≤ 4500000000 := by
  unfold windowGeneric
  rw [reindexStraight_gateSlots]
  exact program_slots start

theorem window_support {n : Nat} (rows : Fin 262144 → Fin n) (start : Nat) :
    straightWires ((windowGeneric rows).program start) ⊆ List.range 1613 := by
  unfold windowGeneric
  rw [straightWires_reindex]
  exact program_support start

theorem window_credit {n : Nat} (_coeffs : Fin n → PointCoeff) (rows : Fin 262144 → Fin n)
    (_Q : Point) (start : Nat) (_history : Fin start → Bool) :
    added ((windowGeneric rows).program start) = 99251 := by
  unfold windowGeneric
  rw [added_reindex]
  exact program_added start

#print axioms program_coherent
#print axioms program_added
#print axioms window_law_generic

end
end ShorECDLP.Entrant.First18Split

