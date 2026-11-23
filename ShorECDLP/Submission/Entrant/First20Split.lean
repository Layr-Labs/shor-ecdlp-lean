import ShorECDLP.Submission.Entrant.First18Split

/-! Five-pass global-optimal SelectSwap loader for the 20-bit left-axis first window.

Splits the 513-wire point register into five passes `((2, 393), (5, 37), (8, 4), (4, 71), (7, 8))`
inside `List.range 1613`, using unwritten trailing point wires in passes 1, 2, and 4 (reset to `|0⟩`
before later passes write them):
- Pass 1 (`k=2`, 393 bits): 18-bit QROM (`262,143`) + `3 × 393 = 1,179` swaps
- Pass 2 (`k=5`,  37 bits): 15-bit QROM (` 32,767`) + `31 × 37 = 1,147` swaps
- Pass 3 (`k=8`,   4 bits): 12-bit QROM (`  4,095`) + `255 × 4 = 1,020` swaps
- Pass 4 (`k=4`,  71 bits): 16-bit QROM (` 65,535`) + `15 × 71 = 1,065` swaps
- Pass 5 (`k=7`,   8 bits): 13-bit QROM (`  8,191`) + `127 × 8 = 1,016` swaps
- One fused 9-bit measured-clear phase fixup (`2,047 + 502 = 2,549` Toffolis) over all
  5,427 garbage measurement records, followed by `RootPass.seedProgram 836` (`-6` root hits).

Total: `380,701` Toffolis and `380,716` measurement records, within `List.range 1613`. -/

set_option Elab.async false

namespace ShorECDLP.Entrant.First20Split
open Quantum Challenge Secp256k1 Paper2607_13816 Paper2607_13816.ChallengeMigration AndGadget WEXCredit
open First18Split (chunks chunks_length chunks_mem_length chunks_flatten
  swapTree treeGarbs treeAddrs treeGarbs_nodup_and_mem treeGarbs_length treeGarbs_mem_length
  treeGarbs_flatten_length treeAddrs_length swapTree_hp swapTree_wf swapTree_wires
  swapTree_length swapTree_ccx swapTree_run tableAddressValue_append mem_zipIdx_iff)
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false

/-! ### Part 1: 20-bit address register, table point, and fixup bank -/

def bits : List Wire := List.range' 855 20

def Input (s : BasisState) : Prop :=
  s 836 = true ∧ ∀ v, v ≠ 836 → v ∉ bits → s v = false

def tablePoint (coeffs : Fin 1048576 → PointCoeff) (Q : Point) (a : Nat) : Point :=
  constantPoint Q (coeffs ⟨a % 1048576, Nat.mod_lt _ (by decide +kernel)⟩)

def update (init : Point → Nat → Point) (Q : Point) (s : BasisState) : BasisState :=
  pointWrite (init Q (tableAddressValue bits s)) s

def row (a : Nat) : Fin 1048576 := ⟨a % 1048576, Nat.mod_lt _ (by decide +kernel)⟩

def slots : List (Fin 1048576 → ConstantBit 1048576) :=
  List.ofFn (fun i : Fin 256 => fun r => (⟨r, .x, i⟩ : ConstantBit 1048576)) ++
  List.ofFn (fun i : Fin 256 => fun r => (⟨r, .y, i⟩ : ConstantBit 1048576)) ++
  [fun r => (⟨r, .infinity, ⟨0, by decide +kernel⟩⟩ : ConstantBit 1048576)]

def word (read : ConstantBit 1048576 → Bool) (a : Nat) : List Bool :=
  (pointRefs (row a)).map read

def low (i : Fin 9) : Wire := 855 + i.val
def high : List Wire := List.range' 864 11
def clearPaths : List Wire := List.range' 519 11
def scratch : Wire := 875
def hot (i : Fin 512) : Wire := 876 + i.val

theorem bits_length : bits.length = 20 := by decide +kernel
theorem bits_nodup : bits.Nodup := List.nodup_range'

theorem mem_bits {w : Wire} : w ∈ bits ↔ 855 ≤ w ∧ w < 875 := by
  simp only [bits, List.mem_range'_1]

theorem bits_not_point (w : Wire) (hb : w ∈ bits) (hp : w ∈ pointLogicalWires) : False := by
  have h1 := mem_bits.mp hb
  have h2 := First18.mem_point hp
  (try dsimp only [Wire] at *); omega

theorem bits_subset_range : bits ⊆ List.range 1613 := by
  intro w hw
  have h := mem_bits.mp hw
  rw [List.mem_range]; (try dsimp only [Wire] at *); omega

theorem input_clean (s : BasisState) (hs : Input s) (w : Nat)
    (h1 : w ≠ 836) (h2 : w < 855 ∨ 875 ≤ w) : s w = false := by
  apply hs.2 w h1
  intro hm
  have := mem_bits.mp hm
  (try dsimp only [Wire] at *); omega

theorem pointRefs_slots (r : Fin 1048576) : pointRefs r = slots.map (fun f => f r) := by
  rw [pointRefs, slots, List.map_append, List.map_append, List.map_ofFn, List.map_ofFn,
    List.map_cons, List.map_nil]
  rfl

theorem slots_length : slots.length = 513 := by
  rw [slots, List.length_append, List.length_append, List.length_ofFn, List.length_ofFn,
    List.length_singleton]

theorem zipWith_targets {α : Type} (g : α → Wire → MeasuredClear.ClearPort 1048576)
    (hg : ∀ x w, (g x w).target = w) :
    ∀ (xs : List α) (ws : List Wire), xs.length = ws.length →
      (List.zipWith g xs ws).map MeasuredClear.ClearPort.target = ws
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, w :: ws, h => by
    rw [List.zipWith_cons_cons, List.map_cons, hg, zipWith_targets g hg xs ws (by simpa using h)]

theorem hot_eq : List.ofFn hot = List.range' 876 512 := by decide +kernel

theorem low_high_bits :
    [MeasuredClear.lowN9 low 0, MeasuredClear.lowN9 low 1, MeasuredClear.lowN9 low 2,
     MeasuredClear.lowN9 low 3, MeasuredClear.lowN9 low 4, MeasuredClear.lowN9 low 5,
     MeasuredClear.lowN9 low 6, MeasuredClear.lowN9 low 7, MeasuredClear.lowN9 low 8] ++ high = bits := by
  decide +kernel

theorem clear_layout : (tableAddressTree high 0 1).Layout 836 clearPaths :=
  tableAddressTree_layout _ _ _ _ _ (by decide +kernel) (by decide +kernel)

theorem high_index : (tableAddressTree high 0 1).indexWires.dedup = high :=
  tableAddressTree_index _ _ _ (by decide +kernel)

theorem clear_nodes : (tableAddressTree high 0 1).internalNodes = 2047 := by
  have h := tableAddressTree_nodes high 0 1
  change _ + 1 = 2048 at h
  (try dsimp only [Wire] at *); omega

theorem clear_leaves : (tableAddressTree high 0 1).leaves = 2048 := by
  rw [MeasuredClear.addressTree_leaves]; rfl

theorem clear_measurements : MeasuredClear.recordMeasurements
    (MeasuredClear.recordUnaryOps (tableAddressTree high 0 1) 836 clearPaths) = 2047 := by
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

theorem low_ne_836 (i : Fin 9) : low i ≠ 836 := by
  simp only [low]; have := i.isLt; (try dsimp only [Wire] at *); omega

theorem hot_ne_836 (i : Fin 512) : hot i ≠ 836 := by
  simp only [hot]; (try dsimp only [Wire] at *); omega

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

/-! ### Part 2: QROM multi-register loading for `n = 1048576` -/

def sliceWord (sliceSlots : List (Fin 1048576 → ConstantBit 1048576))
    (read : ConstantBit 1048576 → Bool) (a : Nat) : List Bool :=
  sliceSlots.map fun f => read (f (row a))

theorem sliceWord_length (sliceSlots : List (Fin 1048576 → ConstantBit 1048576))
    (read : ConstantBit 1048576 → Bool) (a : Nat) :
    (sliceWord sliceSlots read a).length = sliceSlots.length := by
  simp [sliceWord]

def passLeaf (k : Nat) (sliceSlots : List (Fin 1048576 → ConstantBit 1048576))
    (regs : List (List Wire)) (l : Nat) (q : Wire) : List (TemplateGate 1048576) :=
  lookupLeafGates q (regs.zipIdx.flatMap fun p =>
    (sliceSlots.map fun f => f (row (2 ^ k * l + p.2))).zip p.1)

def passMask (k : Nat) (sliceSlots : List (Fin 1048576 → ConstantBit 1048576))
    (regs : List (List Wire)) (read : ConstantBit 1048576 → Bool) (l : Nat) : List Wire :=
  regs.zipIdx.flatMap fun p => tableBitsMask p.1 (sliceWord sliceSlots read (2 ^ k * l + p.2))

theorem passLeaf_instantiate (k : Nat) (sliceSlots : List (Fin 1048576 → ConstantBit 1048576))
    (regs : List (List Wire)) (read : ConstantBit 1048576 → Bool) (l : Nat) (q : Wire) :
    (passLeaf k sliceSlots regs l q).flatMap (TemplateGate.instantiate read) =
      tableXorGates q (passMask k sliceSlots regs read l) := by
  rw [passLeaf, lookupLeafGates_instantiate]
  have h1 : ∀ (L : List (List Wire × Nat)),
      ((L.flatMap fun p => (sliceSlots.map fun f => f (row (2 ^ k * l + p.2))).zip p.1).filter
        (fun x => read x.1)).map (fun x => Gate.CX q x.2) =
      tableXorGates q (L.flatMap fun p => tableBitsMask p.1 (sliceWord sliceSlots read (2 ^ k * l + p.2))) := by
    intro L
    induction L with
    | nil => rfl
    | cons p ps ih =>
      rw [List.flatMap_cons, List.filter_append, List.map_append, ih, List.flatMap_cons,
        show tableXorGates q (_ ++ _) = tableXorGates q _ ++ tableXorGates q _ from List.map_append]
      congr 1
      rw [show (fun x : ConstantBit 1048576 × Wire => Gate.CX q x.2) = (Gate.CX q) ∘ Prod.snd from rfl,
        ← List.map_map, filtered_zip_mask, List.map_map]
      rfl
  exact h1 regs.zipIdx

theorem passLeaf_length (k : Nat) (sliceSlots : List (Fin 1048576 → ConstantBit 1048576))
    (regs : List (List Wire)) (l : Nat) (q : Wire) :
    (passLeaf k sliceSlots regs l q).length ≤ regs.length * sliceSlots.length := by
  rw [passLeaf, lookupLeafGates, List.length_map]
  have h1 : ∀ (L : List (List Wire × Nat)),
      (L.flatMap fun p => (sliceSlots.map fun f => f (row (2 ^ k * l + p.2))).zip p.1).length ≤
        L.length * sliceSlots.length := by
    intro L; induction L with
    | nil => simp
    | cons p ps ih =>
      rw [List.flatMap_cons, List.length_append, List.length_zip, List.length_map, List.length_cons,
        Nat.add_mul, Nat.one_mul]
      have := Nat.min_le_left sliceSlots.length p.1.length
      omega
  simpa [List.length_zipIdx] using h1 regs.zipIdx

theorem passMask_sub (k : Nat) (sliceSlots : List (Fin 1048576 → ConstantBit 1048576))
    (regs : List (List Wire)) (read : ConstantBit 1048576 → Bool) (l : Nat) :
    passMask k sliceSlots regs read l ⊆ regs.flatten := by
  intro w hw
  obtain ⟨⟨r, t⟩, hmem, hwm⟩ := List.mem_flatMap.mp hw
  have hr : r ∈ regs := by
    obtain ⟨i, hi, heq, _⟩ := (mem_zipIdx_iff regs 0 r t).mp hmem
    rw [← heq]; exact List.getElem_mem hi
  exact List.mem_flatten.mpr ⟨r, hr, tableBitsMask_subset _ _ hwm⟩

theorem passMask_nodup (k : Nat) (sliceSlots : List (Fin 1048576 → ConstantBit 1048576))
    (regs : List (List Wire)) (read : ConstantBit 1048576 → Bool) (l : Nat)
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

theorem passMask_read (k : Nat) (sliceSlots : List (Fin 1048576 → ConstantBit 1048576))
    (regs : List (List Wire)) (read : ConstantBit 1048576 → Bool) (selBits : List Wire)
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

/-! ### Part 3: Generic `Pass` structure for 20-bit SelectSwap -/

def passClearData (k : Nat) (sliceSlots : List (Fin 1048576 → ConstantBit 1048576))
    (ctrl : List Wire) (regs : List (List Wire)) : List (MeasuredClear.ClearPort 1048576) :=
  ((treeAddrs k).zip (treeGarbs ctrl regs)).flatMap fun p =>
    List.zipWith (fun f w => (⟨fun x => f (row (p.1 x)), true, w⟩ : MeasuredClear.ClearPort 1048576))
      sliceSlots p.2

theorem passClearData_targets (k : Nat) (sliceSlots : List (Fin 1048576 → ConstantBit 1048576))
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
        List.zipWith (fun f w => (⟨fun x => f (row (p.1 x)), true, w⟩ : MeasuredClear.ClearPort 1048576))
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
        rw [zipWith_targets _ (fun _ _ => rfl) sliceSlots g (hml' g List.mem_cons_self).symm,
          ih gs (by simpa using h) (fun r hr => hml' r (List.mem_cons_of_mem _ hr))]
  exact hgen (treeAddrs k) (treeGarbs ctrl regs) hlen hml

theorem passClearData_loaded (k : Nat) (sliceSlots : List (Fin 1048576 → ConstantBit 1048576))
    (ctrl : List Wire) (regs : List (List Wire))
    (read : ConstantBit 1048576 → Bool) (a : Nat) (u : BasisState)
    (hvals : ∀ p ∈ (treeAddrs k).zip (treeGarbs ctrl regs),
      wireValues p.2 u = sliceWord sliceSlots read (p.1 a)) :
    ∀ q ∈ passClearData k sliceSlots ctrl regs,
      u q.target = (true && decide (read (q.ref a) = q.value)) := by
  intro q hq
  obtain ⟨⟨fn, reg⟩, hmem, hq'⟩ := List.mem_flatMap.mp hq
  have hv := hvals (fn, reg) hmem
  have hgen : ∀ (ss : List (Fin 1048576 → ConstantBit 1048576)) (ws : List Wire),
      wireValues ws u = ss.map (fun f => read (f (row (fn a)))) →
      ∀ port ∈ List.zipWith (fun f w => (⟨fun x => f (row (fn x)), true, w⟩ : MeasuredClear.ClearPort 1048576)) ss ws,
        u port.target = (true && decide (read (port.ref a) = port.value)) := by
    intro ss; induction ss with
    | nil => intro _ _ _ hp; simp at hp
    | cons f ss ih =>
      intro ws h port hp
      cases ws with
      | nil => simp at hp
      | cons w ws =>
        have h' : u w = read (f (row (fn a))) ∧
            wireValues ws u = ss.map (fun f => read (f (row (fn a)))) := List.cons.inj h
        rw [List.zipWith_cons_cons, List.mem_cons] at hp
        rcases hp with rfl | hp
        · show u w = (true && decide (read (f (row (fn a))) = true))
          rw [h'.1]; cases read (f (row (fn a))) <;> rfl
        · exact ih ws h'.2 port hp
  exact hgen sliceSlots reg hv q hq'

structure Pass where
  k : Nat
  m : Nat
  sliceSlots : List (Fin 1048576 → ConstantBit 1048576)
  ctrl : List Wire
  selBits : List Wire
  selPaths : List Wire
  out : List Wire
  garb : List Wire

namespace Pass

def regs (P : Pass) : List (List Wire) := P.out :: chunks (2 ^ P.k - 1) P.m P.garb
def leaf (P : Pass) (l : Nat) (q : Wire) : List (TemplateGate 1048576) :=
  passLeaf P.k P.sliceSlots P.regs l q
def selOps (P : Pass) : List (LookupOp 1048576) :=
  unaryLookupOps P.leaf (tableAddressTree P.selBits 0 1) 836 P.selPaths
def swap (P : Pass) : Circuit := swapTree P.ctrl P.regs
def targets (P : Pass) : List Wire := (treeGarbs P.ctrl P.regs).flatten
def clearData (P : Pass) : List (MeasuredClear.ClearPort 1048576) :=
  passClearData P.k P.sliceSlots P.ctrl P.regs
def selMeas (P : Pass) : Nat := 2 ^ (20 - P.k) - 1
def garbLen (P : Pass) : Nat := (2 ^ P.k - 1) * P.m

structure Geo (P : Pass) : Prop where
  hk : 0 < P.k ∧ P.k < 20
  hctrl_len : P.ctrl.length = P.k
  hsel_len : P.selBits.length = 20 - P.k
  hpaths_len : P.selPaths.length = 20 - P.k
  hbits : P.ctrl ++ P.selBits = bits
  hslots_len : P.sliceSlots.length = P.m
  hout_len : P.out.length = P.m
  hgarb_len : P.garb.length = (2 ^ P.k - 1) * P.m
  hsel_nodup : (836 :: P.selBits ++ P.selPaths).Nodup
  hregs_nodup : (P.out ++ P.garb).Nodup
  hdisj_sel : (836 :: bits ++ P.selPaths).Disjoint (P.out ++ P.garb)
  hsupp : (836 :: bits ++ P.selPaths ++ P.out ++ P.garb) ⊆ List.range 1613

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

theorem selOps_circuit (P : Pass) (read : ConstantBit 1048576 → Bool) :
    lookupCircuit read P.selOps =
      tableLookupProgram (passMask P.k P.sliceSlots P.regs read) P.selBits 836 P.selPaths := by
  rw [selOps, unaryLookupOps_circuit]
  unfold tableLookupProgram tableLookup
  apply unaryAction_leaf_congr
  intro l _ q
  exact passLeaf_instantiate P.k P.sliceSlots P.regs read l q

def loadProg (P : Pass) (g : P.Geo) (start : Nat) : Straight 1048576 start (start + P.selMeas) :=
  (castFinish (by rw [P.selOps_measurements g]) (lookupProgram 1048576 P.selOps start)).append
    (literalProgram P.swap)

def loadSrc (P : Pass) (read : ConstantBit 1048576 → Bool) : AdaptiveCircuit :=
  (lookupCircuit read P.selOps).seq (.unitary P.swap .done)

theorem loadProg_run (P : Pass) (g : P.Geo) (read : ConstantBit 1048576 → Bool)
    (start : Nat) (h : Fin start → Bool) :
    ((P.loadProg g start).instantiate read h).run = (P.loadSrc read).run := by
  rw [loadProg, append_run_fixed _ _ _ _ _ (fun h' => literalProgram_run P.swap read h'),
    AdaptiveCircuit.run_seq, castFinish_instantiate, lookupProgram_run, ← AdaptiveCircuit.run_seq, loadSrc]

theorem loadProg_tCount (P : Pass) (g : P.Geo) (read : ConstantBit 1048576 → Bool)
    (start : Nat) (h : Fin start → Bool) :
    ((P.loadProg g start).instantiate read h).tCount = 7 * (P.selMeas + P.garbLen) := by
  have hsel_t : ((lookupProgram 1048576 P.selOps start).instantiate read h).tCount = 7 * P.selMeas := by
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
    (P.sliceSlots.map fun f => f (row (2 ^ P.k * label + p.2))).zip p.1) = ports
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
    have hc' : c ∈ 836 :: bits ++ P.selPaths := by
      rcases List.mem_cons.mp hc with rfl | hc
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ hc)
    exact List.disjoint_left.mp g.hdisj_sel hc' htgt
  · apply literalProgram_wellFormed
    apply swapTree_wf
    · rw [P.regs_flatten g]
      apply List.disjoint_left.mpr
      intro w hwc hwr
      have hwb : w ∈ bits := by rw [← g.hbits]; exact List.mem_append_left _ hwc
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
        have hwb : w ∈ bits := by rw [← g.hbits]; exact List.mem_append_right _ hb
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
    · have hwb : w ∈ bits := by rw [← g.hbits]; exact List.mem_append_left _ h
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
    · have h836 : (836 : Wire) ∈ bits := by rw [← g.hbits]; exact List.mem_append_left _ hc
      have : (836 : Wire) ∉ bits := by decide
      exact this h836
    · rw [P.regs_flatten g] at hr
      exact List.disjoint_left.mp g.hdisj_sel List.mem_cons_self hr

theorem loadProg_hits836 (P : Pass) (g : P.Geo) (start : Nat) :
    RootPass.literalHits 836 (P.loadProg g start) = 1 := by
  rw [loadProg, RootPass.literalHits_append, RootPass.literalHits_cast,
    RootPass.literalHits_lookupProgram]
  have hsw : RootPass.literalHits 836 (literalProgram (n := 1048576) (s := start + P.selMeas) P.swap) = 0 := by
    apply RootPass.literalHits_zero_of_not_mem
    rw [literalProgram_support]
    intro h
    rcases swapTree_wires P.ctrl P.regs 836 h with hc | hr
    · have h836 : (836 : Wire) ∈ bits := by rw [← g.hbits]; exact List.mem_append_left _ hc
      have : (836 : Wire) ∉ bits := by decide
      exact this h836
    · rw [P.regs_flatten g] at hr
      exact List.disjoint_left.mp g.hdisj_sel List.mem_cons_self hr
  rw [hsw, Nat.add_zero, selOps]
  apply RootPass.unaryOps_root_hits 836 P.leaf _ _ (P.sel_layout g)
  · rw [P.sel_nodes g, selMeas]
    have hpow : 2 ≤ 2 ^ (20 - P.k) := by
      have : 1 ≤ 20 - P.k := by have := g.hk; omega
      exact Nat.le_self_pow (by omega) 2
    omega
  · intro l c
    simp [leaf, passLeaf, lookupLeafGates, List.map_map, Function.comp_def, RootPass.templateHits]

def afterSwap (P : Pass) (read : ConstantBit 1048576 → Bool) (s : BasisState) : BasisState :=
  Classical.run P.swap (tableLookupState (passMask P.k P.sliceSlots P.regs read) P.selBits 836 s)

def afterReset (P : Pass) (read : ConstantBit 1048576 → Bool) (s : BasisState) : BasisState :=
  clearRegister P.targets (P.afterSwap read s)

theorem loadSrc_coherent (P : Pass) (g : P.Geo) (read : ConstantBit 1048576 → Bool) :
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
    have hw' : w ∈ 836 :: bits ++ P.selPaths := by
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

theorem afterSwap_facts (P : Pass) (g : P.Geo) (read : ConstantBit 1048576 → Bool)
    (s : BasisState) (h836 : s 836 = true) (hclean : Clean (P.out ++ P.garb) s) :
    (∀ w, w ∉ P.out → w ∉ P.garb → P.afterSwap read s w = s w) ∧
    wireValues P.out (P.afterSwap read s) = sliceWord P.sliceSlots read (tableAddressValue bits s) ∧
    (∀ q ∈ P.clearData, (P.afterSwap read s) q.target =
      (true && decide (read (q.ref (tableAddressValue bits s)) = q.value))) := by
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
    have hwb : w ∈ bits := by rw [← g.hbits]; exact List.mem_append_left _ hw
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
    have hwb : w ∈ bits := by rw [← g.hbits]; exact List.mem_append_left _ hw
    exact List.disjoint_left.mp g.hdisj_sel (by simp [hwb]) hmr
  obtain ⟨hfr, h0, hgarb⟩ := swapTree_run P.m P.ctrl P.regs (sliceWord P.sliceSlots read)
    (tableAddressValue P.selBits s) (by rw [g.hctrl_len]; exact P.regs_length g)
    (P.regs_mem_length g) hctrl_disj (P.regs_nodup g) s0 h0_init
  have haddr : tableAddressValue P.ctrl s0 + 2 ^ P.ctrl.length * tableAddressValue P.selBits s =
      tableAddressValue bits s := by
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

theorem afterReset_facts (P : Pass) (g : P.Geo) (read : ConstantBit 1048576 → Bool)
    (s : BasisState) (h836 : s 836 = true) (hclean : Clean (P.out ++ P.garb) s) :
    (∀ w, w ∉ P.out → P.afterReset read s w = s w) ∧
    wireValues P.out (P.afterReset read s) = sliceWord P.sliceSlots read (tableAddressValue bits s) := by
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

def stepProg (P : Pass) (g : P.Geo) {R : Nat}
    (next : (c : Nat) → List (Fin c) → Straight 1048576 c (c + R))
    (start : Nat) (refs : List (Fin start)) :
    Straight 1048576 start (start + (P.selMeas + (P.garbLen + R))) :=
  castFinish (Nat.add_assoc start P.selMeas (P.garbLen + R))
    ((P.loadProg g start).append
      (castFinish (by rw [P.targets_length g]; exact Nat.add_assoc (start + P.selMeas) P.garbLen R)
        (MeasuredClear.measureThen (R := R) next P.targets (start + P.selMeas)
          (refs.map (Fin.castLE (Nat.le_add_right _ _))))))

def stepSrc (P : Pass) (read : ConstantBit 1048576 → Bool)
    (nextSrc : List Bool → AdaptiveCircuit) (prior : List Bool) : AdaptiveCircuit :=
  (P.loadSrc read).seq (measureResetThen P.targets (fun o => nextSrc (prior ++ o)))

theorem stepProg_run (P : Pass) (g : P.Geo) {R : Nat}
    (next : (c : Nat) → List (Fin c) → Straight 1048576 c (c + R))
    (nextSrc : List Bool → AdaptiveCircuit) (read : ConstantBit 1048576 → Bool)
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
    (next : (c : Nat) → List (Fin c) → Straight 1048576 c (c + R))
    (read : ConstantBit 1048576 → Bool)
    (hn : ∀ c rs h, ((next c rs).instantiate read h).tCount = t)
    (start : Nat) (refs : List (Fin start)) (h : Fin start → Bool) :
    ((P.stepProg g next start refs).instantiate read h).tCount =
      7 * (P.selMeas + P.garbLen) + t := by
  rw [stepProg, castFinish_instantiate,
    append_tCount_fixed _ _ _ _ _ (fun h' => by
      rw [castFinish_instantiate, MeasuredClear.measureThen_tCount _ read hn]),
    P.loadProg_tCount g]

theorem stepProg_residue (P : Pass) (g : P.Geo) {R : Nat}
    (next : (c : Nat) → List (Fin c) → Straight 1048576 c (c + R))
    (hn : ∀ c rs, residue (next c rs) = 0)
    (start : Nat) (refs : List (Fin start)) :
    residue (P.stepProg g next start refs) = 0 := by
  rw [stepProg, residue_cast, residue_append, P.loadProg_residue g, residue_cast,
    MeasuredClear.measureThen_residue _ hn]

theorem stepProg_slots (P : Pass) (g : P.Geo) {R B : Nat}
    (next : (c : Nat) → List (Fin c) → Straight 1048576 c (c + R))
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
    (next : (c : Nat) → List (Fin c) → Straight 1048576 c (c + R))
    (hn : ∀ c rs, (next c rs).WellFormed)
    (start : Nat) (refs : List (Fin start)) :
    (P.stepProg g next start refs).WellFormed := by
  rw [stepProg, castFinish_wellFormed]
  refine straight_append_wellFormed _ _ (P.loadProg_wellFormed g start) ?_
  rw [castFinish_wellFormed]
  exact MeasuredClear.measureThen_wellFormed next hn _ _ _

theorem stepProg_support (P : Pass) (g : P.Geo) {R : Nat}
    (next : (c : Nat) → List (Fin c) → Straight 1048576 c (c + R))
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
    (next : (c : Nat) → List (Fin c) → Straight 1048576 c (c + R))
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
    (next : (c : Nat) → List (Fin c) → Straight 1048576 c (c + R))
    (hn : ∀ c rs, RootPass.literalHits 836 (next c rs) = hCount)
    (start : Nat) (refs : List (Fin start)) :
    RootPass.literalHits 836 (P.stepProg g next start refs) = 1 + hCount := by
  rw [stepProg, RootPass.literalHits_cast, RootPass.literalHits_append, P.loadProg_hits836 g,
    RootPass.literalHits_cast, RootPass.literalHits_measureThen 836 hCount next hn]

theorem stepSrc_sim (P : Pass) (g : P.Geo) (read : ConstantBit 1048576 → Bool)
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

/-! ### Part 4: Five-pass instantiation `((2, 393), (5, 37), (8, 4), (4, 71), (7, 8))` -/

def anc18 : List Wire :=
  List.range' 0 263 ++ List.range' 537 43 ++ [837] ++ List.range' 839 16 ++ List.range' 875 738

def anc16 : List Wire := anc18 ++ [535, 536]
def anc15 : List Wire := anc18 ++ [534, 535, 536]
def anc13 : List Wire := anc18 ++ [532, 533, 534, 535, 536]
def anc12 : List Wire := anc18 ++ [531, 532, 533, 534, 535, 536]

theorem mem_anc18 {w : Wire} : w ∈ anc18 ↔
    w < 263 ∨ (537 ≤ w ∧ w < 580) ∨ w = 837 ∨ (839 ≤ w ∧ w < 855) ∨ (875 ≤ w ∧ w < 1613) := by
  simp only [anc18, List.mem_append, List.mem_range'_1, List.mem_singleton]
  (try dsimp only [Wire] at *); omega

theorem anc18_length : anc18.length = 1061 := by simp [anc18]

theorem anc18_nodup : anc18.Nodup := by
  have h1 : (List.range' 0 263 ++ List.range' 537 43).Nodup :=
    List.nodup_append.mpr ⟨List.nodup_range', List.nodup_range', fun a ha b hb => by
      simp only [List.mem_range'_1] at ha hb; omega⟩
  have h2 : (List.range' 0 263 ++ List.range' 537 43 ++ [837]).Nodup :=
    List.nodup_append.mpr ⟨h1, List.nodup_singleton _, fun a ha b hb => by
      simp only [List.mem_append, List.mem_range'_1, List.mem_singleton] at ha hb; omega⟩
  have h3 : (List.range' 0 263 ++ List.range' 537 43 ++ [837] ++ List.range' 839 16).Nodup :=
    List.nodup_append.mpr ⟨h2, List.nodup_range', fun a ha b hb => by
      simp only [List.mem_append, List.mem_range'_1, List.mem_singleton] at ha hb; omega⟩
  exact List.nodup_append.mpr ⟨h3, List.nodup_range', fun a ha b hb => by
    simp only [List.mem_append, List.mem_range'_1, List.mem_singleton] at ha hb
    (try dsimp only [Wire] at *); omega⟩

theorem anc18_disj_point : anc18.Disjoint pointLogicalWires := by
  apply List.disjoint_left.mpr
  intro w ha hp
  have h1 := mem_anc18.mp ha
  have h2 := First18.mem_point hp
  (try dsimp only [Wire] at *); omega

theorem anc16_nodup : anc16.Nodup :=
  List.nodup_append.mpr ⟨anc18_nodup, by decide, fun a ha b hb => by
    have h1 := mem_anc18.mp ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    (try dsimp only [Wire] at *); omega⟩

theorem anc15_nodup : anc15.Nodup :=
  List.nodup_append.mpr ⟨anc18_nodup, by decide, fun a ha b hb => by
    have h1 := mem_anc18.mp ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    (try dsimp only [Wire] at *); omega⟩

theorem anc13_nodup : anc13.Nodup :=
  List.nodup_append.mpr ⟨anc18_nodup, by decide, fun a ha b hb => by
    have h1 := mem_anc18.mp ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    (try dsimp only [Wire] at *); omega⟩

theorem anc12_nodup : anc12.Nodup :=
  List.nodup_append.mpr ⟨anc18_nodup, by decide, fun a ha b hb => by
    have h1 := mem_anc18.mp ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    (try dsimp only [Wire] at *); omega⟩

theorem mem_anc16 {w : Wire} : w ∈ anc16 ↔
    w < 263 ∨ (535 ≤ w ∧ w < 580) ∨ w = 837 ∨ (839 ≤ w ∧ w < 855) ∨ (875 ≤ w ∧ w < 1613) := by
  simp only [anc16, List.mem_append, mem_anc18, List.mem_cons, List.not_mem_nil, or_false]
  (try dsimp only [Wire] at *); omega

theorem mem_anc15 {w : Wire} : w ∈ anc15 ↔
    w < 263 ∨ (534 ≤ w ∧ w < 580) ∨ w = 837 ∨ (839 ≤ w ∧ w < 855) ∨ (875 ≤ w ∧ w < 1613) := by
  simp only [anc15, List.mem_append, mem_anc18, List.mem_cons, List.not_mem_nil, or_false]
  (try dsimp only [Wire] at *); omega

theorem mem_anc13 {w : Wire} : w ∈ anc13 ↔
    w < 263 ∨ (532 ≤ w ∧ w < 580) ∨ w = 837 ∨ (839 ≤ w ∧ w < 855) ∨ (875 ≤ w ∧ w < 1613) := by
  simp only [anc13, List.mem_append, mem_anc18, List.mem_cons, List.not_mem_nil, or_false]
  (try dsimp only [Wire] at *); omega

theorem mem_anc12 {w : Wire} : w ∈ anc12 ↔
    w < 263 ∨ (531 ≤ w ∧ w < 580) ∨ w = 837 ∨ (839 ≤ w ∧ w < 855) ∨ (875 ≤ w ∧ w < 1613) := by
  simp only [anc12, List.mem_append, mem_anc18, List.mem_cons, List.not_mem_nil, or_false]
  (try dsimp only [Wire] at *); omega

def p1 : List Wire := pointLogicalWires.take 393
def rem1 : List Wire := pointLogicalWires.drop 393
def p2 : List Wire := rem1.take 37
def rem2 : List Wire := rem1.drop 37
def p3 : List Wire := rem2.take 4
def rem3 : List Wire := rem2.drop 4
def p4 : List Wire := rem3.take 71
def rem4 : List Wire := rem3.drop 71
def p5 : List Wire := rem4

def s1 : List (Fin 1048576 → ConstantBit 1048576) := slots.take 393
def s2 : List (Fin 1048576 → ConstantBit 1048576) := (slots.drop 393).take 37
def s3 : List (Fin 1048576 → ConstantBit 1048576) := (slots.drop 430).take 4
def s4 : List (Fin 1048576 → ConstantBit 1048576) := (slots.drop 434).take 71
def s5 : List (Fin 1048576 → ConstantBit 1048576) := slots.drop 505

theorem point_split : p1 ++ p2 ++ p3 ++ p4 ++ p5 = pointLogicalWires := by
  simp only [p1, p2, p3, p4, p5, rem1, rem2, rem3, rem4, List.append_assoc, List.take_append_drop]

theorem slots_split : s1 ++ s2 ++ s3 ++ s4 ++ s5 = slots := by
  have h1 : slots.drop 430 = (slots.drop 393).drop 37 := by rw [List.drop_drop]
  have h2 : slots.drop 434 = (slots.drop 430).drop 4 := by rw [List.drop_drop]
  have h3 : slots.drop 505 = (slots.drop 434).drop 71 := by rw [List.drop_drop]
  simp only [s1, s2, s3, s4, s5, h3, h2, h1, List.append_assoc, List.take_append_drop]

theorem p1_len : p1.length = 393 := by rw [p1, List.length_take, First18.point_length]; decide
theorem rem1_len : rem1.length = 120 := by rw [rem1, List.length_drop, First18.point_length]
theorem p2_len : p2.length = 37 := by rw [p2, List.length_take, rem1_len]; decide
theorem rem2_len : rem2.length = 83 := by rw [rem2, List.length_drop, rem1_len]
theorem p3_len : p3.length = 4 := by rw [p3, List.length_take, rem2_len]; decide
theorem rem3_len : rem3.length = 79 := by rw [rem3, List.length_drop, rem2_len]
theorem p4_len : p4.length = 71 := by rw [p4, List.length_take, rem3_len]; decide
theorem rem4_len : rem4.length = 8 := by rw [rem4, List.length_drop, rem3_len]
theorem p5_len : p5.length = 8 := rem4_len

theorem s1_len : s1.length = 393 := by rw [s1, List.length_take, slots_length]; decide
theorem s2_len : s2.length = 37 := by rw [s2, List.length_take, List.length_drop, slots_length]; decide
theorem s3_len : s3.length = 4 := by rw [s3, List.length_take, List.length_drop, slots_length]; decide
theorem s4_len : s4.length = 71 := by rw [s4, List.length_take, List.length_drop, slots_length]; decide
theorem s5_len : s5.length = 8 := by rw [s5, List.length_drop, slots_length]

theorem p_mem_point : ∀ w, (w ∈ p1 ∨ w ∈ p2 ∨ w ∈ p3 ∨ w ∈ p4 ∨ w ∈ p5) ↔ w ∈ pointLogicalWires := by
  intro w; rw [← point_split]; simp only [List.mem_append, or_assoc]

theorem p1_rem1_eq : p1 ++ rem1 = pointLogicalWires := List.take_append_drop 393 pointLogicalWires
theorem p2_rem2_eq : p2 ++ rem2 = rem1 := List.take_append_drop 37 rem1
theorem p3_rem3_eq : p3 ++ rem3 = rem2 := List.take_append_drop 4 rem2
theorem p4_p5_eq : p4 ++ p5 = rem3 := List.take_append_drop 71 rem3

theorem p1_nodup : p1.Nodup :=
  (List.nodup_append.mp (by rw [p1_rem1_eq]; exact pointLogicalWires_nodup)).1
theorem rem1_nodup : rem1.Nodup :=
  (List.nodup_append.mp (by rw [p1_rem1_eq]; exact pointLogicalWires_nodup)).2.1
theorem p1_disj_rem1 : p1.Disjoint rem1 :=
  List.disjoint_left.mpr (fun a ha hb =>
    (List.nodup_append.mp (by rw [p1_rem1_eq]; exact pointLogicalWires_nodup)).2.2 a ha a hb rfl)

theorem p2_nodup : p2.Nodup :=
  (List.nodup_append.mp (by rw [p2_rem2_eq]; exact rem1_nodup)).1
theorem rem2_nodup : rem2.Nodup :=
  (List.nodup_append.mp (by rw [p2_rem2_eq]; exact rem1_nodup)).2.1
theorem p2_disj_rem2 : p2.Disjoint rem2 :=
  List.disjoint_left.mpr (fun a ha hb =>
    (List.nodup_append.mp (by rw [p2_rem2_eq]; exact rem1_nodup)).2.2 a ha a hb rfl)

theorem p3_nodup : p3.Nodup :=
  (List.nodup_append.mp (by rw [p3_rem3_eq]; exact rem2_nodup)).1
theorem rem3_nodup : rem3.Nodup :=
  (List.nodup_append.mp (by rw [p3_rem3_eq]; exact rem2_nodup)).2.1
theorem p3_disj_rem3 : p3.Disjoint rem3 :=
  List.disjoint_left.mpr (fun a ha hb =>
    (List.nodup_append.mp (by rw [p3_rem3_eq]; exact rem2_nodup)).2.2 a ha a hb rfl)

theorem p4_nodup : p4.Nodup :=
  (List.nodup_append.mp (by rw [p4_p5_eq]; exact rem3_nodup)).1
theorem p5_nodup : p5.Nodup :=
  (List.nodup_append.mp (by rw [p4_p5_eq]; exact rem3_nodup)).2.1
theorem p4_disj_p5 : p4.Disjoint p5 :=
  List.disjoint_left.mpr (fun a ha hb =>
    (List.nodup_append.mp (by rw [p4_p5_eq]; exact rem3_nodup)).2.2 a ha a hb rfl)

theorem p1_sub_point {w} (h : w ∈ p1) : w ∈ pointLogicalWires := List.mem_of_mem_take h
theorem rem1_sub_point {w} (h : w ∈ rem1) : w ∈ pointLogicalWires := List.mem_of_mem_drop h
theorem p2_sub_rem1 {w} (h : w ∈ p2) : w ∈ rem1 := List.mem_of_mem_take h
theorem rem2_sub_rem1 {w} (h : w ∈ rem2) : w ∈ rem1 := List.mem_of_mem_drop h
theorem p3_sub_rem2 {w} (h : w ∈ p3) : w ∈ rem2 := List.mem_of_mem_take h
theorem rem3_sub_rem2 {w} (h : w ∈ rem3) : w ∈ rem2 := List.mem_of_mem_drop h
theorem p4_sub_rem3 {w} (h : w ∈ p4) : w ∈ rem3 := List.mem_of_mem_take h
theorem p5_sub_rem3 {w} (h : w ∈ p5) : w ∈ rem3 := List.mem_of_mem_drop h

def pass1 : Pass :=
  ⟨2, 393, s1, bits.take 2, bits.drop 2, List.range' 519 18, p1, (anc18 ++ rem1).take 1179⟩

def pass2 : Pass :=
  ⟨5, 37, s2, bits.take 5, bits.drop 5, List.range' 519 15, p2, (anc15 ++ rem2).take 1147⟩

def pass3 : Pass :=
  ⟨8, 4, s3, bits.take 8, bits.drop 8, List.range' 519 12, p3, anc12.take 1020⟩

def pass4 : Pass :=
  ⟨4, 71, s4, bits.take 4, bits.drop 4, List.range' 519 16, p4, (anc16 ++ rem4).take 1065⟩

def pass5 : Pass :=
  ⟨7, 8, s5, bits.take 7, bits.drop 7, List.range' 519 13, p5, anc13.take 1016⟩

theorem pass1_geo : pass1.Geo where
  hk := by decide
  hctrl_len := by decide
  hsel_len := by decide
  hpaths_len := by decide
  hbits := List.take_append_drop 2 bits
  hslots_len := s1_len
  hout_len := p1_len
  hgarb_len := by simp [pass1, anc18_length, rem1_len]
  hsel_nodup := by decide
  hregs_nodup := by
    change (p1 ++ (anc18 ++ rem1).take 1179).Nodup
    have hfull : (p1 ++ (anc18 ++ rem1)).Nodup := by
      refine List.nodup_append.mpr ⟨p1_nodup, List.nodup_append.mpr ⟨anc18_nodup, rem1_nodup, ?_⟩, ?_⟩
      · intro a ha b hb he; subst he
        exact List.disjoint_left.mp anc18_disj_point ha (rem1_sub_point hb)
      · intro a ha b hb he; subst he
        rcases List.mem_append.mp hb with hb | hb
        · exact List.disjoint_left.mp anc18_disj_point hb (p1_sub_point ha)
        · exact List.disjoint_left.mp p1_disj_rem1 ha hb
    exact hfull.sublist (List.Sublist.append (List.Sublist.refl _) (List.take_sublist _ _))
  hdisj_sel := by
    apply List.disjoint_left.mpr
    intro w h1 h2
    simp only [pass1, bits, List.mem_cons, List.mem_append, List.mem_range'_1] at h1
    rcases List.mem_append.mp h2 with hp | hg
    · have := First18.mem_point (p1_sub_point hp); (try dsimp only [Wire] at *); omega
    · rcases List.mem_append.mp (List.mem_of_mem_take hg) with ha | hr
      · have := mem_anc18.mp ha; (try dsimp only [Wire] at *); omega
      · have := First18.mem_point (rem1_sub_point hr); (try dsimp only [Wire] at *); omega
  hsupp := by
    intro w hw
    rw [List.mem_range]
    simp only [pass1, bits, List.mem_cons, List.mem_append, List.mem_range'_1] at hw
    rcases hw with (((rfl | h) | h) | hp) | hg
    · decide
    · (try dsimp only [Wire] at *); omega
    · (try dsimp only [Wire] at *); omega
    · have := First18.mem_point (p1_sub_point hp); (try dsimp only [Wire] at *); omega
    · rcases List.mem_append.mp (List.mem_of_mem_take hg) with ha | hr
      · have := mem_anc18.mp ha; (try dsimp only [Wire] at *); omega
      · have := First18.mem_point (rem1_sub_point hr); (try dsimp only [Wire] at *); omega

theorem pass2_geo : pass2.Geo where
  hk := by decide
  hctrl_len := by decide
  hsel_len := by decide
  hpaths_len := by decide
  hbits := List.take_append_drop 5 bits
  hslots_len := s2_len
  hout_len := p2_len
  hgarb_len := by simp [pass2, anc15, anc18_length, rem2_len]
  hsel_nodup := by decide
  hregs_nodup := by
    change (p2 ++ (anc15 ++ rem2).take 1147).Nodup
    have ha_pt : anc15.Disjoint pointLogicalWires := by
      apply List.disjoint_left.mpr
      intro w ha hp
      have h1 := mem_anc15.mp ha; have h2 := First18.mem_point hp; (try dsimp only [Wire] at *); omega
    have hfull : (p2 ++ (anc15 ++ rem2)).Nodup := by
      refine List.nodup_append.mpr ⟨p2_nodup, List.nodup_append.mpr ⟨anc15_nodup, rem2_nodup, ?_⟩, ?_⟩
      · intro a ha b hb he; subst he
        exact List.disjoint_left.mp ha_pt ha (rem1_sub_point (rem2_sub_rem1 hb))
      · intro a ha b hb he; subst he
        rcases List.mem_append.mp hb with hb | hb
        · exact List.disjoint_left.mp ha_pt hb (rem1_sub_point (p2_sub_rem1 ha))
        · exact List.disjoint_left.mp p2_disj_rem2 ha hb
    exact hfull.sublist (List.Sublist.append (List.Sublist.refl _) (List.take_sublist _ _))
  hdisj_sel := by
    apply List.disjoint_left.mpr
    intro w h1 h2
    simp only [pass2, bits, List.mem_cons, List.mem_append, List.mem_range'_1] at h1
    rcases List.mem_append.mp h2 with hp | hg
    · have := First18.mem_point (rem1_sub_point (p2_sub_rem1 hp)); (try dsimp only [Wire] at *); omega
    · rcases List.mem_append.mp (List.mem_of_mem_take hg) with ha | hr
      · have := mem_anc15.mp ha; (try dsimp only [Wire] at *); omega
      · have := First18.mem_point (rem1_sub_point (rem2_sub_rem1 hr)); (try dsimp only [Wire] at *); omega
  hsupp := by
    intro w hw
    rw [List.mem_range]
    simp only [pass2, bits, List.mem_cons, List.mem_append, List.mem_range'_1] at hw
    rcases hw with (((rfl | h) | h) | hp) | hg
    · decide
    · (try dsimp only [Wire] at *); omega
    · (try dsimp only [Wire] at *); omega
    · have := First18.mem_point (rem1_sub_point (p2_sub_rem1 hp)); (try dsimp only [Wire] at *); omega
    · rcases List.mem_append.mp (List.mem_of_mem_take hg) with ha | hr
      · have := mem_anc15.mp ha; (try dsimp only [Wire] at *); omega
      · have := First18.mem_point (rem1_sub_point (rem2_sub_rem1 hr)); (try dsimp only [Wire] at *); omega

theorem pass3_geo : pass3.Geo where
  hk := by decide
  hctrl_len := by decide
  hsel_len := by decide
  hpaths_len := by decide
  hbits := List.take_append_drop 8 bits
  hslots_len := s3_len
  hout_len := p3_len
  hgarb_len := by simp [pass3, anc12, anc18_length]
  hsel_nodup := by decide
  hregs_nodup := by
    change (p3 ++ anc12.take 1020).Nodup
    refine List.nodup_append.mpr ⟨p3_nodup, anc12_nodup.sublist (List.take_sublist _ _), ?_⟩
    intro a ha b hb he; subst he
    have h1 := First18.mem_point (rem1_sub_point (rem2_sub_rem1 (p3_sub_rem2 ha)))
    have h2 := mem_anc12.mp (List.mem_of_mem_take hb)
    (try dsimp only [Wire] at *); omega
  hdisj_sel := by
    apply List.disjoint_left.mpr
    intro w h1 h2
    simp only [pass3, bits, List.mem_cons, List.mem_append, List.mem_range'_1] at h1
    rcases List.mem_append.mp h2 with hp | hg
    · have := First18.mem_point (rem1_sub_point (rem2_sub_rem1 (p3_sub_rem2 hp)))
      (try dsimp only [Wire] at *); omega
    · have := mem_anc12.mp (List.mem_of_mem_take hg); (try dsimp only [Wire] at *); omega
  hsupp := by
    intro w hw
    rw [List.mem_range]
    simp only [pass3, bits, List.mem_cons, List.mem_append, List.mem_range'_1] at hw
    rcases hw with (((rfl | h) | h) | hp) | hg
    · decide
    · (try dsimp only [Wire] at *); omega
    · (try dsimp only [Wire] at *); omega
    · have := First18.mem_point (rem1_sub_point (rem2_sub_rem1 (p3_sub_rem2 hp)))
      (try dsimp only [Wire] at *); omega
    · have := mem_anc12.mp (List.mem_of_mem_take hg); (try dsimp only [Wire] at *); omega

theorem pass4_geo : pass4.Geo where
  hk := by decide
  hctrl_len := by decide
  hsel_len := by decide
  hpaths_len := by decide
  hbits := List.take_append_drop 4 bits
  hslots_len := s4_len
  hout_len := p4_len
  hgarb_len := by simp [pass4, anc16, anc18_length, rem4_len]
  hsel_nodup := by decide
  hregs_nodup := by
    change (p4 ++ (anc16 ++ rem4).take 1065).Nodup
    have ha_pt : anc16.Disjoint pointLogicalWires := by
      apply List.disjoint_left.mpr
      intro w ha hp
      have h1 := mem_anc16.mp ha; have h2 := First18.mem_point hp; (try dsimp only [Wire] at *); omega
    have hfull : (p4 ++ (anc16 ++ p5)).Nodup := by
      refine List.nodup_append.mpr ⟨p4_nodup, List.nodup_append.mpr ⟨anc16_nodup, p5_nodup, ?_⟩, ?_⟩
      · intro a ha b hb he; subst he
        exact List.disjoint_left.mp ha_pt ha (rem1_sub_point (rem2_sub_rem1 (rem3_sub_rem2 (p5_sub_rem3 hb))))
      · intro a ha b hb he; subst he
        rcases List.mem_append.mp hb with hb | hb
        · exact List.disjoint_left.mp ha_pt hb (rem1_sub_point (rem2_sub_rem1 (rem3_sub_rem2 (p4_sub_rem3 ha))))
        · exact List.disjoint_left.mp p4_disj_p5 ha hb
    exact hfull.sublist (List.Sublist.append (List.Sublist.refl _) (List.take_sublist _ _))
  hdisj_sel := by
    apply List.disjoint_left.mpr
    intro w h1 h2
    simp only [pass4, bits, List.mem_cons, List.mem_append, List.mem_range'_1] at h1
    rcases List.mem_append.mp h2 with hp | hg
    · have := First18.mem_point (rem1_sub_point (rem2_sub_rem1 (rem3_sub_rem2 (p4_sub_rem3 hp))))
      (try dsimp only [Wire] at *); omega
    · rcases List.mem_append.mp (List.mem_of_mem_take hg) with ha | hr
      · have := mem_anc16.mp ha; (try dsimp only [Wire] at *); omega
      · have := First18.mem_point (rem1_sub_point (rem2_sub_rem1 (rem3_sub_rem2 (p5_sub_rem3 hr))))
        (try dsimp only [Wire] at *); omega
  hsupp := by
    intro w hw
    rw [List.mem_range]
    simp only [pass4, bits, List.mem_cons, List.mem_append, List.mem_range'_1] at hw
    rcases hw with (((rfl | h) | h) | hp) | hg
    · decide
    · (try dsimp only [Wire] at *); omega
    · (try dsimp only [Wire] at *); omega
    · have := First18.mem_point (rem1_sub_point (rem2_sub_rem1 (rem3_sub_rem2 (p4_sub_rem3 hp))))
      (try dsimp only [Wire] at *); omega
    · rcases List.mem_append.mp (List.mem_of_mem_take hg) with ha | hr
      · have := mem_anc16.mp ha; (try dsimp only [Wire] at *); omega
      · have := First18.mem_point (rem1_sub_point (rem2_sub_rem1 (rem3_sub_rem2 (p5_sub_rem3 hr))))
        (try dsimp only [Wire] at *); omega

theorem pass5_geo : pass5.Geo where
  hk := by decide
  hctrl_len := by decide
  hsel_len := by decide
  hpaths_len := by decide
  hbits := List.take_append_drop 7 bits
  hslots_len := s5_len
  hout_len := p5_len
  hgarb_len := by simp [pass5, anc13, anc18_length]
  hsel_nodup := by decide
  hregs_nodup := by
    change (p5 ++ anc13.take 1016).Nodup
    refine List.nodup_append.mpr ⟨p5_nodup, anc13_nodup.sublist (List.take_sublist _ _), ?_⟩
    intro a ha b hb he; subst he
    have h1 := First18.mem_point (rem1_sub_point (rem2_sub_rem1 (rem3_sub_rem2 (p5_sub_rem3 ha))))
    have h2 := mem_anc13.mp (List.mem_of_mem_take hb)
    (try dsimp only [Wire] at *); omega
  hdisj_sel := by
    apply List.disjoint_left.mpr
    intro w h1 h2
    simp only [pass5, bits, List.mem_cons, List.mem_append, List.mem_range'_1] at h1
    rcases List.mem_append.mp h2 with hp | hg
    · have := First18.mem_point (rem1_sub_point (rem2_sub_rem1 (rem3_sub_rem2 (p5_sub_rem3 hp))))
      (try dsimp only [Wire] at *); omega
    · have := mem_anc13.mp (List.mem_of_mem_take hg); (try dsimp only [Wire] at *); omega
  hsupp := by
    intro w hw
    rw [List.mem_range]
    simp only [pass5, bits, List.mem_cons, List.mem_append, List.mem_range'_1] at hw
    rcases hw with (((rfl | h) | h) | hp) | hg
    · decide
    · (try dsimp only [Wire] at *); omega
    · (try dsimp only [Wire] at *); omega
    · have := First18.mem_point (rem1_sub_point (rem2_sub_rem1 (rem3_sub_rem2 (p5_sub_rem3 hp))))
      (try dsimp only [Wire] at *); omega
    · have := mem_anc13.mp (List.mem_of_mem_take hg); (try dsimp only [Wire] at *); omega

/-! ### Part 5: Chained 5-pass program + fused 9-bit fixup + root seeding -/

def tree11 : UnaryActionTree := tableAddressTree high 0 1

def fixRec9 : Nat :=
  MeasuredClear.recordMeasurements (MeasuredClear.recordUnaryOps tree11 836 clearPaths) + 511

theorem fixRec9_eq : fixRec9 = 2558 := by
  rw [fixRec9, tree11, clear_measurements]

def allData : List (MeasuredClear.ClearPort 1048576) :=
  pass1.clearData ++ pass2.clearData ++ pass3.clearData ++ pass4.clearData ++ pass5.clearData

theorem pass1_nums : pass1.k = 2 ∧ pass1.m = 393 ∧ pass1.selMeas = 262143 ∧ pass1.garbLen = 1179 := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> simp [Pass.selMeas, Pass.garbLen, pass1]
theorem pass2_nums : pass2.k = 5 ∧ pass2.m = 37 ∧ pass2.selMeas = 32767 ∧ pass2.garbLen = 1147 := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> simp [Pass.selMeas, Pass.garbLen, pass2]
theorem pass3_nums : pass3.k = 8 ∧ pass3.m = 4 ∧ pass3.selMeas = 4095 ∧ pass3.garbLen = 1020 := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> simp [Pass.selMeas, Pass.garbLen, pass3]
theorem pass4_nums : pass4.k = 4 ∧ pass4.m = 71 ∧ pass4.selMeas = 65535 ∧ pass4.garbLen = 1065 := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> simp [Pass.selMeas, Pass.garbLen, pass4]
theorem pass5_nums : pass5.k = 7 ∧ pass5.m = 8 ∧ pass5.selMeas = 8191 ∧ pass5.garbLen = 1016 := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> simp [Pass.selMeas, Pass.garbLen, pass5]

theorem allData_length : allData.length = 5427 := by
  simp only [allData, List.length_append, pass1.clearData_length pass1_geo,
    pass2.clearData_length pass2_geo, pass3.clearData_length pass3_geo,
    pass4.clearData_length pass4_geo, pass5.clearData_length pass5_geo,
    pass1_nums.2.2.2, pass2_nums.2.2.2, pass3_nums.2.2.2, pass4_nums.2.2.2, pass5_nums.2.2.2]

attribute [local irreducible] pass1 pass2 pass3 pass4 pass5 allData tree11

def stepFix (c : Nat) (rs : List (Fin c)) : Straight 1048576 c (c + fixRec9) :=
  castFinish (by rw [fixRec9]; exact Nat.add_assoc c _ 511)
    (MeasuredClear.fixupProgram9 allData rs low hot tree11 836 scratch clearPaths)

def step5 (c : Nat) (rs : List (Fin c)) :
    Straight 1048576 c (c + (pass5.selMeas + (pass5.garbLen + fixRec9))) :=
  pass5.stepProg pass5_geo stepFix c rs

def step45 (c : Nat) (rs : List (Fin c)) :
    Straight 1048576 c (c + (pass4.selMeas + (pass4.garbLen + (pass5.selMeas + (pass5.garbLen + fixRec9))))) :=
  pass4.stepProg pass4_geo step5 c rs

def step345 (c : Nat) (rs : List (Fin c)) :
    Straight 1048576 c (c + (pass3.selMeas + (pass3.garbLen +
      (pass4.selMeas + (pass4.garbLen + (pass5.selMeas + (pass5.garbLen + fixRec9))))))) :=
  pass3.stepProg pass3_geo step45 c rs

def step2345 (c : Nat) (rs : List (Fin c)) :
    Straight 1048576 c (c + (pass2.selMeas + (pass2.garbLen +
      (pass3.selMeas + (pass3.garbLen +
        (pass4.selMeas + (pass4.garbLen + (pass5.selMeas + (pass5.garbLen + fixRec9))))))))) :=
  pass2.stepProg pass2_geo step345 c rs

theorem total_rec_eq :
    pass1.selMeas + (pass1.garbLen + (pass2.selMeas + (pass2.garbLen +
      (pass3.selMeas + (pass3.garbLen + (pass4.selMeas + (pass4.garbLen +
        (pass5.selMeas + (pass5.garbLen + fixRec9))))))))) = 380716 := by
  rw [fixRec9_eq, pass1_nums.2.2.1, pass1_nums.2.2.2, pass2_nums.2.2.1, pass2_nums.2.2.2,
    pass3_nums.2.2.1, pass3_nums.2.2.2, pass4_nums.2.2.1, pass4_nums.2.2.2,
    pass5_nums.2.2.1, pass5_nums.2.2.2]

def rawProgram (start : Nat) : Straight 1048576 start (start + 380716) :=
  castFinish (by rw [total_rec_eq])
    (pass1.stepProg pass1_geo step2345 start ([] : List (Fin start)))

def program (start : Nat) : Straight 1048576 start (start + 380716) :=
  RootPass.seedProgram 836 (rawProgram start)

attribute [local irreducible] stepFix step5 step45 step345 step2345 rawProgram program

def stepFixSrc (read : ConstantBit 1048576 → Bool) (o : List Bool) : AdaptiveCircuit :=
  MeasuredClear.fixupSource9 allData o read low hot tree11 836 scratch clearPaths

def step5Src (read : ConstantBit 1048576 → Bool) (o : List Bool) : AdaptiveCircuit :=
  pass5.stepSrc read (stepFixSrc read) o

def step45Src (read : ConstantBit 1048576 → Bool) (o : List Bool) : AdaptiveCircuit :=
  pass4.stepSrc read (step5Src read) o

def step345Src (read : ConstantBit 1048576 → Bool) (o : List Bool) : AdaptiveCircuit :=
  pass3.stepSrc read (step45Src read) o

def step2345Src (read : ConstantBit 1048576 → Bool) (o : List Bool) : AdaptiveCircuit :=
  pass2.stepSrc read (step345Src read) o

def rawSource (read : ConstantBit 1048576 → Bool) : AdaptiveCircuit :=
  pass1.stepSrc read (step2345Src read) List.nil

theorem rawProgram_run (read : ConstantBit 1048576 → Bool) (start : Nat) (h : Fin start → Bool) :
    ((rawProgram start).instantiate read h).run = (rawSource read).run := by
  have hFix : ∀ c rs hh, ((stepFix c rs).instantiate read hh).run = (stepFixSrc read (rs.map hh)).run := by
    intro c rs hh; rw [stepFix, castFinish_instantiate, MeasuredClear.fixupProgram_run9]; rfl
  have h5 : ∀ c rs hh, ((step5 c rs).instantiate read hh).run = (step5Src read (rs.map hh)).run :=
    fun c rs hh => by rw [step5]; exact pass5.stepProg_run pass5_geo stepFix (stepFixSrc read) read hFix c rs hh
  have h45 : ∀ c rs hh, ((step45 c rs).instantiate read hh).run = (step45Src read (rs.map hh)).run :=
    fun c rs hh => by rw [step45]; exact pass4.stepProg_run pass4_geo step5 (step5Src read) read h5 c rs hh
  have h345 : ∀ c rs hh, ((step345 c rs).instantiate read hh).run = (step345Src read (rs.map hh)).run :=
    fun c rs hh => by rw [step345]; exact pass3.stepProg_run pass3_geo step45 (step45Src read) read h45 c rs hh
  have h2345 : ∀ c rs hh, ((step2345 c rs).instantiate read hh).run = (step2345Src read (rs.map hh)).run :=
    fun c rs hh => by rw [step2345]; exact pass2.stepProg_run pass2_geo step345 (step345Src read) read h345 c rs hh
  rw [rawProgram, castFinish_instantiate]
  exact pass1.stepProg_run pass1_geo step2345 (step2345Src read) read h2345 start List.nil h

/-! ### Semantics: 5-pass coherent simulation -/

theorem rawSource_coherent (coeffs : Fin 1048576 → PointCoeff) (Q : Point) :
    CoherentlyImplementsOn (rawSource (readConstant coeffs Q))
      (Finsupp.lmapDomain ℂ ℂ (fun s => pointWrite (tablePoint coeffs Q
        (tableAddressValue bits s)) s)) Input := by
  let read := readConstant coeffs Q
  let st1 (s : BasisState) := pass1.afterReset read s
  let st2 (s : BasisState) := pass2.afterReset read (st1 s)
  let st3 (s : BasisState) := pass3.afterReset read (st2 s)
  let st4 (s : BasisState) := pass4.afterReset read (st3 s)
  let st5 (s : BasisState) := pass5.afterReset read (st4 s)
  let tgt (s : BasisState) := pointWrite (tablePoint coeffs Q (tableAddressValue bits s)) s
  have h_out1 : pass1.out = p1 := by unfold pass1; rfl
  have h_out2 : pass2.out = p2 := by unfold pass2; rfl
  have h_out3 : pass3.out = p3 := by unfold pass3; rfl
  have h_out4 : pass4.out = p4 := by unfold pass4; rfl
  have h_out5 : pass5.out = p5 := by unfold pass5; rfl
  have h_s1 : pass1.sliceSlots = s1 := by unfold pass1; rfl
  have h_s2 : pass2.sliceSlots = s2 := by unfold pass2; rfl
  have h_s3 : pass3.sliceSlots = s3 := by unfold pass3; rfl
  have h_s4 : pass4.sliceSlots = s4 := by unfold pass4; rfl
  have h_s5 : pass5.sliceSlots = s5 := by unfold pass5; rfl
  have h_in_519 (s : BasisState) (hs : Input s) (w : Wire) (hw : 519 ≤ w ∧ w < 537) : s w = false :=
    input_clean s hs w (by (try dsimp only [Wire] at *); omega) (by (try dsimp only [Wire] at *); omega)
  have h_paths1 (s : BasisState) (hs : Input s) : Clean pass1.selPaths s := fun w hw => by
    have : 519 ≤ w ∧ w < 537 := by unfold pass1 at hw; dsimp only at hw; simp only [List.mem_range'_1] at hw; (try dsimp only [Wire] at *); omega
    exact h_in_519 s hs w this
  have h_paths2_s (s : BasisState) (hs : Input s) : Clean pass2.selPaths s := fun w hw => by
    have : 519 ≤ w ∧ w < 537 := by unfold pass2 at hw; dsimp only at hw; simp only [List.mem_range'_1] at hw; (try dsimp only [Wire] at *); omega
    exact h_in_519 s hs w this
  have h_paths3_s (s : BasisState) (hs : Input s) : Clean pass3.selPaths s := fun w hw => by
    have : 519 ≤ w ∧ w < 537 := by unfold pass3 at hw; dsimp only at hw; simp only [List.mem_range'_1] at hw; (try dsimp only [Wire] at *); omega
    exact h_in_519 s hs w this
  have h_paths4_s (s : BasisState) (hs : Input s) : Clean pass4.selPaths s := fun w hw => by
    have : 519 ≤ w ∧ w < 537 := by unfold pass4 at hw; dsimp only at hw; simp only [List.mem_range'_1] at hw; (try dsimp only [Wire] at *); omega
    exact h_in_519 s hs w this
  have h_paths5_s (s : BasisState) (hs : Input s) : Clean pass5.selPaths s := fun w hw => by
    have : 519 ≤ w ∧ w < 537 := by unfold pass5 at hw; dsimp only at hw; simp only [List.mem_range'_1] at hw; (try dsimp only [Wire] at *); omega
    exact h_in_519 s hs w this
  have h_clean_reg (P : Pass) (g : P.Geo) (s : BasisState) (hs : Input s) :
      Clean (P.out ++ P.garb) s := fun w hw => by
    have hn : w ∉ 836 :: bits ++ P.selPaths := fun hm => List.disjoint_left.mp g.hdisj_sel hm hw
    exact hs.2 w (fun e => hn (by simp [e])) (fun hm => hn (by simp [hm]))
  -- Pairwise disjointness among p1..p5
  have hp1_not_p2 : p1.Disjoint p2 := List.disjoint_left.mpr (fun w h1 h2 =>
    List.disjoint_left.mp p1_disj_rem1 h1 (p2_sub_rem1 h2))
  have hp1_not_p3 : p1.Disjoint p3 := List.disjoint_left.mpr (fun w h1 h3 =>
    List.disjoint_left.mp p1_disj_rem1 h1 (rem2_sub_rem1 (p3_sub_rem2 h3)))
  have hp1_not_p4 : p1.Disjoint p4 := List.disjoint_left.mpr (fun w h1 h4 =>
    List.disjoint_left.mp p1_disj_rem1 h1 (rem2_sub_rem1 (rem3_sub_rem2 (p4_sub_rem3 h4))))
  have hp1_not_p5 : p1.Disjoint p5 := List.disjoint_left.mpr (fun w h1 h5 =>
    List.disjoint_left.mp p1_disj_rem1 h1 (rem2_sub_rem1 (rem3_sub_rem2 (p5_sub_rem3 h5))))
  have hp2_not_p3 : p2.Disjoint p3 := List.disjoint_left.mpr (fun w h2 h3 =>
    List.disjoint_left.mp p2_disj_rem2 h2 (p3_sub_rem2 h3))
  have hp2_not_p4 : p2.Disjoint p4 := List.disjoint_left.mpr (fun w h2 h4 =>
    List.disjoint_left.mp p2_disj_rem2 h2 (rem3_sub_rem2 (p4_sub_rem3 h4)))
  have hp2_not_p5 : p2.Disjoint p5 := List.disjoint_left.mpr (fun w h2 h5 =>
    List.disjoint_left.mp p2_disj_rem2 h2 (rem3_sub_rem2 (p5_sub_rem3 h5)))
  have hp3_not_p4 : p3.Disjoint p4 := List.disjoint_left.mpr (fun w h3 h4 =>
    List.disjoint_left.mp p3_disj_rem3 h3 (p4_sub_rem3 h4))
  have hp3_not_p5 : p3.Disjoint p5 := List.disjoint_left.mpr (fun w h3 h5 =>
    List.disjoint_left.mp p3_disj_rem3 h3 (p5_sub_rem3 h5))
  -- Disjointness between earlier outputs and later garbage pools
  have hp1_not_garb2 : p1.Disjoint pass2.garb := by
    apply List.disjoint_left.mpr; intro w h1 hg
    unfold pass2 at hg
    rcases List.mem_append.mp (List.mem_of_mem_take hg) with ha | hr
    · have := mem_anc15.mp ha; have := First18.mem_point (p1_sub_point h1); (try dsimp only [Wire] at *); omega
    · exact List.disjoint_left.mp p1_disj_rem1 h1 (rem2_sub_rem1 hr)
  have hp_not_garb3 (w : Wire) (hw : w ∈ pointLogicalWires) (hg : w ∈ pass3.garb) : False := by
    unfold pass3 at hg
    have := mem_anc12.mp (List.mem_of_mem_take hg); have := First18.mem_point hw
    (try dsimp only [Wire] at *); omega
  have hp123_not_garb4 (w : Wire) (h123 : w ∈ p1 ∨ w ∈ p2 ∨ w ∈ p3) (hg : w ∈ pass4.garb) : False := by
    unfold pass4 at hg
    rcases List.mem_append.mp (List.mem_of_mem_take hg) with ha | hr
    · have hpt : w ∈ pointLogicalWires := (p_mem_point w).mp (by tauto)
      have := mem_anc16.mp ha; have := First18.mem_point hpt; (try dsimp only [Wire] at *); omega
    · rcases h123 with h1 | h2 | h3
      · exact List.disjoint_left.mp hp1_not_p5 h1 hr
      · exact List.disjoint_left.mp hp2_not_p5 h2 hr
      · exact List.disjoint_left.mp hp3_not_p5 h3 hr
  have hp_not_garb5 (w : Wire) (hw : w ∈ pointLogicalWires) (hg : w ∈ pass5.garb) : False := by
    unfold pass5 at hg
    have := mem_anc13.mp (List.mem_of_mem_take hg); have := First18.mem_point hw
    (try dsimp only [Wire] at *); omega
  -- Per-pass preconditions, frames, loaded words, and clearData facts
  have hpre1 : ∀ s, Input s → Clean pass1.selPaths s ∧ s 836 = true ∧ Clean (pass1.out ++ pass1.garb) s :=
    fun s hs => ⟨h_paths1 s hs, hs.1, h_clean_reg pass1 pass1_geo s hs⟩
  have hfr1 : ∀ s, Input s → ∀ w, w ∉ p1 → st1 s w = s w := fun s hs w hw =>
    (pass1.afterReset_facts pass1_geo read s hs.1 (h_clean_reg pass1 pass1_geo s hs)).1 w (by rwa [h_out1])
  have hval1 : ∀ s, Input s → wireValues p1 (st1 s) = sliceWord s1 read (tableAddressValue bits s) := fun s hs => by
    have h := (pass1.afterReset_facts pass1_geo read s hs.1 (h_clean_reg pass1 pass1_geo s hs)).2
    rwa [h_out1, h_s1] at h
  have hclr1 : ∀ s, Input s → ∀ q ∈ pass1.clearData,
      (pass1.afterSwap read s) q.target = (true && decide (read (q.ref (tableAddressValue bits s)) = q.value)) :=
    fun s hs => (pass1.afterSwap_facts pass1_geo read s hs.1 (h_clean_reg pass1 pass1_geo s hs)).2.2
  have haddr1 (s : BasisState) (hs : Input s) : tableAddressValue bits (st1 s) = tableAddressValue bits s :=
    tableAddressValue_congr _ _ _ (fun w hw => hfr1 s hs w (fun h1 => bits_not_point w hw (p1_sub_point h1)))
  have hpre2 : ∀ s, Input s → Clean pass2.selPaths (st1 s) ∧ st1 s 836 = true ∧ Clean (pass2.out ++ pass2.garb) (st1 s) := by
    intro s hs
    refine ⟨fun w hw => ?_, ?_, fun w hw => ?_⟩
    · rw [hfr1 s hs w (fun h1 => by
        have := First18.mem_point (p1_sub_point h1); unfold pass2 at hw; simp only [List.mem_range'_1] at hw
        (try dsimp only [Wire] at *); omega)]
      exact h_paths2_s s hs w hw
    · rw [hfr1 s hs 836 (fun h1 => by have := First18.mem_point (p1_sub_point h1); (try dsimp only [Wire] at *); omega)]
      exact hs.1
    · rw [hfr1 s hs w (fun h1 => by
        rcases List.mem_append.mp hw with h2 | hg2
        · rw [h_out2] at h2; exact List.disjoint_left.mp hp1_not_p2 h1 h2
        · exact List.disjoint_left.mp hp1_not_garb2 h1 hg2)]
      exact h_clean_reg pass2 pass2_geo s hs w hw
  have hfr2 : ∀ s, Input s → ∀ w, w ∉ p2 → st2 s w = st1 s w := fun s hs w hw =>
    (pass2.afterReset_facts pass2_geo read (st1 s) (hpre2 s hs).2.1 (hpre2 s hs).2.2).1 w (by rwa [h_out2])
  have hval2 : ∀ s, Input s → wireValues p2 (st2 s) = sliceWord s2 read (tableAddressValue bits s) := fun s hs => by
    have h := (pass2.afterReset_facts pass2_geo read (st1 s) (hpre2 s hs).2.1 (hpre2 s hs).2.2).2
    rwa [h_out2, h_s2, haddr1 s hs] at h
  have hclr2 : ∀ s, Input s → ∀ q ∈ pass2.clearData,
      (pass2.afterSwap read (st1 s)) q.target = (true && decide (read (q.ref (tableAddressValue bits s)) = q.value)) := fun s hs => by
    have h := (pass2.afterSwap_facts pass2_geo read (st1 s) (hpre2 s hs).2.1 (hpre2 s hs).2.2).2.2
    rwa [haddr1 s hs] at h
  have haddr2 (s : BasisState) (hs : Input s) : tableAddressValue bits (st2 s) = tableAddressValue bits s :=
    (tableAddressValue_congr _ _ _ (fun w hw => hfr2 s hs w (fun h2 =>
      bits_not_point w hw (rem1_sub_point (p2_sub_rem1 h2))))).trans (haddr1 s hs)
  have hnp12 (s : BasisState) (hs : Input s) (w : Wire) (h1 : w ∉ p1) (h2 : w ∉ p2) : st2 s w = s w :=
    (hfr2 s hs w h2).trans (hfr1 s hs w h1)
  have hpre3 : ∀ s, Input s → Clean pass3.selPaths (st2 s) ∧ st2 s 836 = true ∧ Clean (pass3.out ++ pass3.garb) (st2 s) := by
    intro s hs
    refine ⟨fun w hw => ?_, ?_, fun w hw => ?_⟩
    · have hnp : w ∉ pointLogicalWires := fun hp => by
        have := First18.mem_point hp; unfold pass3 at hw; simp only [List.mem_range'_1] at hw
        (try dsimp only [Wire] at *); omega
      rw [hnp12 s hs w (fun h => hnp (p1_sub_point h)) (fun h => hnp (rem1_sub_point (p2_sub_rem1 h)))]
      exact h_paths3_s s hs w hw
    · have hnp : (836 : Wire) ∉ pointLogicalWires := fun hp => by have := First18.mem_point hp; (try dsimp only [Wire] at *); omega
      rw [hnp12 s hs 836 (fun h => hnp (p1_sub_point h)) (fun h => hnp (rem1_sub_point (p2_sub_rem1 h)))]
      exact hs.1
    · rw [hnp12 s hs w
        (fun h1 => by rcases List.mem_append.mp hw with h3 | hg3
                      · rw [h_out3] at h3; exact List.disjoint_left.mp hp1_not_p3 h1 h3
                      · exact hp_not_garb3 w (p1_sub_point h1) hg3)
        (fun h2 => by rcases List.mem_append.mp hw with h3 | hg3
                      · rw [h_out3] at h3; exact List.disjoint_left.mp hp2_not_p3 h2 h3
                      · exact hp_not_garb3 w (rem1_sub_point (p2_sub_rem1 h2)) hg3)]
      exact h_clean_reg pass3 pass3_geo s hs w hw
  have hfr3 : ∀ s, Input s → ∀ w, w ∉ p3 → st3 s w = st2 s w := fun s hs w hw =>
    (pass3.afterReset_facts pass3_geo read (st2 s) (hpre3 s hs).2.1 (hpre3 s hs).2.2).1 w (by rwa [h_out3])
  have hval3 : ∀ s, Input s → wireValues p3 (st3 s) = sliceWord s3 read (tableAddressValue bits s) := fun s hs => by
    have h := (pass3.afterReset_facts pass3_geo read (st2 s) (hpre3 s hs).2.1 (hpre3 s hs).2.2).2
    rwa [h_out3, h_s3, haddr2 s hs] at h
  have hclr3 : ∀ s, Input s → ∀ q ∈ pass3.clearData,
      (pass3.afterSwap read (st2 s)) q.target = (true && decide (read (q.ref (tableAddressValue bits s)) = q.value)) := fun s hs => by
    have h := (pass3.afterSwap_facts pass3_geo read (st2 s) (hpre3 s hs).2.1 (hpre3 s hs).2.2).2.2
    rwa [haddr2 s hs] at h
  have haddr3 (s : BasisState) (hs : Input s) : tableAddressValue bits (st3 s) = tableAddressValue bits s :=
    (tableAddressValue_congr _ _ _ (fun w hw => hfr3 s hs w (fun h3 =>
      bits_not_point w hw (rem1_sub_point (rem2_sub_rem1 (p3_sub_rem2 h3)))))).trans (haddr2 s hs)
  have hnp123 (s : BasisState) (hs : Input s) (w : Wire) (h1 : w ∉ p1) (h2 : w ∉ p2) (h3 : w ∉ p3) : st3 s w = s w :=
    (hfr3 s hs w h3).trans (hnp12 s hs w h1 h2)
  have hpre4 : ∀ s, Input s → Clean pass4.selPaths (st3 s) ∧ st3 s 836 = true ∧ Clean (pass4.out ++ pass4.garb) (st3 s) := by
    intro s hs
    refine ⟨fun w hw => ?_, ?_, fun w hw => ?_⟩
    · have hnp : w ∉ pointLogicalWires := fun hp => by
        have := First18.mem_point hp; unfold pass4 at hw; simp only [List.mem_range'_1] at hw
        (try dsimp only [Wire] at *); omega
      rw [hnp123 s hs w (fun h => hnp (p1_sub_point h)) (fun h => hnp (rem1_sub_point (p2_sub_rem1 h)))
        (fun h => hnp (rem1_sub_point (rem2_sub_rem1 (p3_sub_rem2 h))))]
      exact h_paths4_s s hs w hw
    · have hnp : (836 : Wire) ∉ pointLogicalWires := fun hp => by have := First18.mem_point hp; (try dsimp only [Wire] at *); omega
      rw [hnp123 s hs 836 (fun h => hnp (p1_sub_point h)) (fun h => hnp (rem1_sub_point (p2_sub_rem1 h)))
        (fun h => hnp (rem1_sub_point (rem2_sub_rem1 (p3_sub_rem2 h))))]
      exact hs.1
    · rw [hnp123 s hs w
        (fun h1 => by rcases List.mem_append.mp hw with h4 | hg4
                      · rw [h_out4] at h4; exact List.disjoint_left.mp hp1_not_p4 h1 h4
                      · exact hp123_not_garb4 w (Or.inl h1) hg4)
        (fun h2 => by rcases List.mem_append.mp hw with h4 | hg4
                      · rw [h_out4] at h4; exact List.disjoint_left.mp hp2_not_p4 h2 h4
                      · exact hp123_not_garb4 w (Or.inr (Or.inl h2)) hg4)
        (fun h3 => by rcases List.mem_append.mp hw with h4 | hg4
                      · rw [h_out4] at h4; exact List.disjoint_left.mp hp3_not_p4 h3 h4
                      · exact hp123_not_garb4 w (Or.inr (Or.inr h3)) hg4)]
      exact h_clean_reg pass4 pass4_geo s hs w hw
  have hfr4 : ∀ s, Input s → ∀ w, w ∉ p4 → st4 s w = st3 s w := fun s hs w hw =>
    (pass4.afterReset_facts pass4_geo read (st3 s) (hpre4 s hs).2.1 (hpre4 s hs).2.2).1 w (by rwa [h_out4])
  have hval4 : ∀ s, Input s → wireValues p4 (st4 s) = sliceWord s4 read (tableAddressValue bits s) := fun s hs => by
    have h := (pass4.afterReset_facts pass4_geo read (st3 s) (hpre4 s hs).2.1 (hpre4 s hs).2.2).2
    rwa [h_out4, h_s4, haddr3 s hs] at h
  have hclr4 : ∀ s, Input s → ∀ q ∈ pass4.clearData,
      (pass4.afterSwap read (st3 s)) q.target = (true && decide (read (q.ref (tableAddressValue bits s)) = q.value)) := fun s hs => by
    have h := (pass4.afterSwap_facts pass4_geo read (st3 s) (hpre4 s hs).2.1 (hpre4 s hs).2.2).2.2
    rwa [haddr3 s hs] at h
  have haddr4 (s : BasisState) (hs : Input s) : tableAddressValue bits (st4 s) = tableAddressValue bits s :=
    (tableAddressValue_congr _ _ _ (fun w hw => hfr4 s hs w (fun h4 =>
      bits_not_point w hw (rem1_sub_point (rem2_sub_rem1 (rem3_sub_rem2 (p4_sub_rem3 h4))))))).trans (haddr3 s hs)
  have hnp1234 (s : BasisState) (hs : Input s) (w : Wire) (h1 : w ∉ p1) (h2 : w ∉ p2) (h3 : w ∉ p3) (h4 : w ∉ p4) :
      st4 s w = s w :=
    (hfr4 s hs w h4).trans (hnp123 s hs w h1 h2 h3)
  have hpre5 : ∀ s, Input s → Clean pass5.selPaths (st4 s) ∧ st4 s 836 = true ∧ Clean (pass5.out ++ pass5.garb) (st4 s) := by
    intro s hs
    refine ⟨fun w hw => ?_, ?_, fun w hw => ?_⟩
    · have hnp : w ∉ pointLogicalWires := fun hp => by
        have := First18.mem_point hp; unfold pass5 at hw; simp only [List.mem_range'_1] at hw
        (try dsimp only [Wire] at *); omega
      rw [hnp1234 s hs w (fun h => hnp (p1_sub_point h)) (fun h => hnp (rem1_sub_point (p2_sub_rem1 h)))
        (fun h => hnp (rem1_sub_point (rem2_sub_rem1 (p3_sub_rem2 h))))
        (fun h => hnp (rem1_sub_point (rem2_sub_rem1 (rem3_sub_rem2 (p4_sub_rem3 h)))))]
      exact h_paths5_s s hs w hw
    · have hnp : (836 : Wire) ∉ pointLogicalWires := fun hp => by have := First18.mem_point hp; (try dsimp only [Wire] at *); omega
      rw [hnp1234 s hs 836 (fun h => hnp (p1_sub_point h)) (fun h => hnp (rem1_sub_point (p2_sub_rem1 h)))
        (fun h => hnp (rem1_sub_point (rem2_sub_rem1 (p3_sub_rem2 h))))
        (fun h => hnp (rem1_sub_point (rem2_sub_rem1 (rem3_sub_rem2 (p4_sub_rem3 h)))))]
      exact hs.1
    · rw [hnp1234 s hs w
        (fun h1 => by rcases List.mem_append.mp hw with h5 | hg5
                      · rw [h_out5] at h5; exact List.disjoint_left.mp hp1_not_p5 h1 h5
                      · exact hp_not_garb5 w (p1_sub_point h1) hg5)
        (fun h2 => by rcases List.mem_append.mp hw with h5 | hg5
                      · rw [h_out5] at h5; exact List.disjoint_left.mp hp2_not_p5 h2 h5
                      · exact hp_not_garb5 w (rem1_sub_point (p2_sub_rem1 h2)) hg5)
        (fun h3 => by rcases List.mem_append.mp hw with h5 | hg5
                      · rw [h_out5] at h5; exact List.disjoint_left.mp hp3_not_p5 h3 h5
                      · exact hp_not_garb5 w (rem1_sub_point (rem2_sub_rem1 (p3_sub_rem2 h3))) hg5)
        (fun h4 => by rcases List.mem_append.mp hw with h5 | hg5
                      · rw [h_out5] at h5; exact List.disjoint_left.mp p4_disj_p5 h4 h5
                      · exact hp_not_garb5 w (rem1_sub_point (rem2_sub_rem1 (rem3_sub_rem2 (p4_sub_rem3 h4)))) hg5)]
      exact h_clean_reg pass5 pass5_geo s hs w hw
  have hfr5 : ∀ s, Input s → ∀ w, w ∉ p5 → st5 s w = st4 s w := fun s hs w hw =>
    (pass5.afterReset_facts pass5_geo read (st4 s) (hpre5 s hs).2.1 (hpre5 s hs).2.2).1 w (by rwa [h_out5])
  have hval5 : ∀ s, Input s → wireValues p5 (st5 s) = sliceWord s5 read (tableAddressValue bits s) := fun s hs => by
    have h := (pass5.afterReset_facts pass5_geo read (st4 s) (hpre5 s hs).2.1 (hpre5 s hs).2.2).2
    rwa [h_out5, h_s5, haddr4 s hs] at h
  have hclr5 : ∀ s, Input s → ∀ q ∈ pass5.clearData,
      (pass5.afterSwap read (st4 s)) q.target = (true && decide (read (q.ref (tableAddressValue bits s)) = q.value)) := fun s hs => by
    have h := (pass5.afterSwap_facts pass5_geo read (st4 s) (hpre5 s hs).2.1 (hpre5 s hs).2.2).2.2
    rwa [haddr4 s hs] at h
  -- Final basis state equality: st5 s = tgt s
  have hst5_out (s : BasisState) (hs : Input s) (w : Wire) (hw : w ∉ pointLogicalWires) : st5 s w = s w := by
    have h12345 : w ∉ p1 ∧ w ∉ p2 ∧ w ∉ p3 ∧ w ∉ p4 ∧ w ∉ p5 := by
      have hm := (p_mem_point w).not.mpr hw; tauto
    exact (hfr5 s hs w h12345.2.2.2.2).trans (hnp1234 s hs w h12345.1 h12345.2.1 h12345.2.2.1 h12345.2.2.2.1)
  have hst5_eq (s : BasisState) (hs : Input s) : st5 s = tgt s := by
    have hwp : wireValues pointLogicalWires (st5 s) = wireValues pointLogicalWires (tgt s) := by
      have hw1' : wireValues p1 (st5 s) = sliceWord s1 read (tableAddressValue bits s) := by
        rw [← hval1 s hs]
        exact List.map_congr_left (fun w hw => (hfr5 s hs w (List.disjoint_left.mp hp1_not_p5 hw)).trans
          ((hfr4 s hs w (List.disjoint_left.mp hp1_not_p4 hw)).trans
            ((hfr3 s hs w (List.disjoint_left.mp hp1_not_p3 hw)).trans
              (hfr2 s hs w (List.disjoint_left.mp hp1_not_p2 hw)))))
      have hw2' : wireValues p2 (st5 s) = sliceWord s2 read (tableAddressValue bits s) := by
        rw [← hval2 s hs]
        exact List.map_congr_left (fun w hw => (hfr5 s hs w (List.disjoint_left.mp hp2_not_p5 hw)).trans
          ((hfr4 s hs w (List.disjoint_left.mp hp2_not_p4 hw)).trans
            (hfr3 s hs w (List.disjoint_left.mp hp2_not_p3 hw))))
      have hw3' : wireValues p3 (st5 s) = sliceWord s3 read (tableAddressValue bits s) := by
        rw [← hval3 s hs]
        exact List.map_congr_left (fun w hw => (hfr5 s hs w (List.disjoint_left.mp hp3_not_p5 hw)).trans
          (hfr4 s hs w (List.disjoint_left.mp hp3_not_p4 hw)))
      have hw4' : wireValues p4 (st5 s) = sliceWord s4 read (tableAddressValue bits s) := by
        rw [← hval4 s hs]
        exact List.map_congr_left (fun w hw => hfr5 s hs w (List.disjoint_left.mp p4_disj_p5 hw))
      have hall : wireValues pointLogicalWires (st5 s) = word read (tableAddressValue bits s) := by
        rw [← point_split, wireValues, List.map_append, List.map_append, List.map_append, List.map_append]
        change wireValues p1 (st5 s) ++ wireValues p2 (st5 s) ++ wireValues p3 (st5 s) ++
          wireValues p4 (st5 s) ++ wireValues p5 (st5 s) = _
        rw [hw1', hw2', hw3', hw4', hval5 s hs]
        simp only [sliceWord, ← List.map_append, slots_split, word, pointRefs_slots, List.map_map]
        rfl
      rw [hall]
      dsimp only [tgt]
      rw [pointWrite_word, word, pointRefs_read]
      rfl
    funext w
    by_cases hp : w ∈ pointLogicalWires
    · exact List.map_inj_left.mp hwp w hp
    · rw [hst5_out s hs w hp]; dsimp only [tgt]; rw [pointWrite_frame _ _ w hp]
  -- Apply 5 nested stepSrc_sim + fixupSource_coherent9!
  have htree_lay : tree11.Layout 836 clearPaths := by unfold tree11; exact clear_layout
  have htree_hdisj : (MeasuredClear.hotBank9 hot).Disjoint
      (836 :: tree11.indexWires.dedup ++ clearPaths) := by unfold tree11; exact hot_disjoint
  have htree_scr : scratch ∉ 836 :: tree11.indexWires.dedup ++ clearPaths := by
    unfold tree11; exact scratch_not_tree
  have hst5_hot (s : BasisState) (hs : Input s) : MeasuredClear.HotClean9 hot (st5 s) := fun i => by
    have hhi : 876 ≤ hot i ∧ hot i < 1388 := by have := i.isLt; simp only [hot]; (try dsimp only [Wire] at *); omega
    rw [hst5_out s hs (hot i) (fun hp => by have := First18.mem_point hp; (try dsimp only [Wire] at *); omega)]
    exact input_clean s hs (hot i) (by (try dsimp only [Wire] at *); omega) (by (try dsimp only [Wire] at *); omega)
  have hst5_cpaths (s : BasisState) (hs : Input s) : Clean clearPaths (st5 s) := fun w hw => by
    simp only [clearPaths, List.mem_range'_1] at hw
    rw [hst5_out s hs w (fun hp => by have := First18.mem_point hp; (try dsimp only [Wire] at *); omega)]
    exact input_clean s hs w (by (try dsimp only [Wire] at *); omega) (by (try dsimp only [Wire] at *); omega)
  have hst5_836 (s : BasisState) (hs : Input s) : st5 s 836 = true := by
    rw [hst5_out s hs 836 (fun hp => by have := First18.mem_point hp; (try dsimp only [Wire] at *); omega)]; exact hs.1
  have hst5_addr (s : BasisState) (hs : Input s) :
      512 * tree11.routeLabel (st5 s) + MeasuredClear.hotAddress9 low (st5 s) = tableAddressValue bits s := by
    unfold tree11
    rw [MeasuredClear.splitAddress_value9, low_high_bits]
    exact tableAddressValue_congr _ _ _ (fun w hw => hst5_out s hs w (bits_not_point w hw))
  have hsim := pass1.stepSrc_sim pass1_geo read (step2345Src read) List.nil Input id tgt (fun _ => 1) hpre1
    (fun o1 ho1 =>
      pass2.stepSrc_sim pass2_geo read (step345Src read) (List.nil ++ o1) Input st1 tgt
        (fun s => 1 * registerXPhase pass1.targets o1 (pass1.afterSwap read s)) hpre2
        (fun o2 ho2 =>
          pass3.stepSrc_sim pass3_geo read (step45Src read) ((List.nil ++ o1) ++ o2) Input st2 tgt
            (fun s => (1 * registerXPhase pass1.targets o1 (pass1.afterSwap read s)) *
              registerXPhase pass2.targets o2 (pass2.afterSwap read (st1 s))) hpre3
            (fun o3 ho3 =>
              pass4.stepSrc_sim pass4_geo read (step5Src read) (((List.nil ++ o1) ++ o2) ++ o3) Input st3 tgt
                (fun s => ((1 * registerXPhase pass1.targets o1 (pass1.afterSwap read s)) *
                  registerXPhase pass2.targets o2 (pass2.afterSwap read (st1 s))) *
                  registerXPhase pass3.targets o3 (pass3.afterSwap read (st2 s))) hpre4
                (fun o4 ho4 =>
                  pass5.stepSrc_sim pass5_geo read (stepFixSrc read) ((((List.nil ++ o1) ++ o2) ++ o3) ++ o4) Input st4 tgt
                    (fun s => (((1 * registerXPhase pass1.targets o1 (pass1.afterSwap read s)) *
                      registerXPhase pass2.targets o2 (pass2.afterSwap read (st1 s))) *
                      registerXPhase pass3.targets o3 (pass3.afterSwap read (st2 s))) *
                      registerXPhase pass4.targets o4 (pass4.afterSwap read (st3 s))) hpre5
                    (fun o5 ho5 => by
                      have hfc := MeasuredClear.fixupSource_coherent9 allData
                        (((((List.nil ++ o1) ++ o2) ++ o3) ++ o4) ++ o5)
                        read low hot tree11 836 scratch clearPaths
                        htree_lay hot_injective low_ne_hot htree_hdisj htree_scr scratch_not_hot
                      obtain ⟨cs, al, ma⟩ := hfc
                      refine ⟨cs, al.imp (fun b c hb s hs => ?_), ma⟩
                      rw [hb (st5 s) ⟨hst5_hot s hs, hst5_cpaths s hs⟩, MeasuredClear.basisIdeal_ket]
                      simp only [id_eq, List.nil_append]
                      have hd1 : o1.length = pass1.clearData.length := by
                        rw [ho1, pass1.targets_length pass1_geo, pass1.clearData_length pass1_geo]
                      have hd2 : o2.length = pass2.clearData.length := by
                        rw [ho2, pass2.targets_length pass2_geo, pass2.clearData_length pass2_geo]
                      have hd3 : o3.length = pass3.clearData.length := by
                        rw [ho3, pass3.targets_length pass3_geo, pass3.clearData_length pass3_geo]
                      have hd4 : o4.length = pass4.clearData.length := by
                        rw [ho4, pass4.targets_length pass4_geo, pass4.clearData_length pass4_geo]
                      have hff : MeasuredClear.fixupFactor9 allData ((((o1 ++ o2) ++ o3) ++ o4) ++ o5) read
                          low hot tree11 836 (st5 s) =
                          registerXPhase pass1.targets o1 (pass1.afterSwap read s) *
                          registerXPhase pass2.targets o2 (pass2.afterSwap read (st1 s)) *
                          registerXPhase pass3.targets o3 (pass3.afterSwap read (st2 s)) *
                          registerXPhase pass4.targets o4 (pass4.afterSwap read (st3 s)) *
                          registerXPhase pass5.targets o5 (pass5.afterSwap read (st4 s)) := by
                        have ha : allData =
                            (((pass1.clearData ++ pass2.clearData) ++ pass3.clearData) ++ pass4.clearData) ++
                              pass5.clearData := by
                          unfold allData; rfl
                        rw [ha,
                          MeasuredClear.fixupFactor9_append _ pass5.clearData (((o1 ++ o2) ++ o3) ++ o4) o5
                            (by simp [hd1, hd2, hd3, hd4]),
                          MeasuredClear.fixupFactor9_append _ pass4.clearData ((o1 ++ o2) ++ o3) o4
                            (by simp [hd1, hd2, hd3]),
                          MeasuredClear.fixupFactor9_append _ pass3.clearData (o1 ++ o2) o3
                            (by simp [hd1, hd2]),
                          MeasuredClear.fixupFactor9_append pass1.clearData pass2.clearData o1 o2 hd1]
                        have hf1 := MeasuredClear.fixupFactor9_loaded pass1.clearData o1 read low hot
                          tree11 836 clearPaths hot_injective low_ne_hot htree_hdisj
                          (st5 s) (pass1.afterSwap read s) (hst5_hot s hs)
                          (fun q hq => by rw [hst5_836 s hs, hst5_addr s hs]; exact hclr1 s hs q hq)
                        have hf2 := MeasuredClear.fixupFactor9_loaded pass2.clearData o2 read low hot
                          tree11 836 clearPaths hot_injective low_ne_hot htree_hdisj
                          (st5 s) (pass2.afterSwap read (st1 s)) (hst5_hot s hs)
                          (fun q hq => by rw [hst5_836 s hs, hst5_addr s hs]; exact hclr2 s hs q hq)
                        have hf3 := MeasuredClear.fixupFactor9_loaded pass3.clearData o3 read low hot
                          tree11 836 clearPaths hot_injective low_ne_hot htree_hdisj
                          (st5 s) (pass3.afterSwap read (st2 s)) (hst5_hot s hs)
                          (fun q hq => by rw [hst5_836 s hs, hst5_addr s hs]; exact hclr3 s hs q hq)
                        have hf4 := MeasuredClear.fixupFactor9_loaded pass4.clearData o4 read low hot
                          tree11 836 clearPaths hot_injective low_ne_hot htree_hdisj
                          (st5 s) (pass4.afterSwap read (st3 s)) (hst5_hot s hs)
                          (fun q hq => by rw [hst5_836 s hs, hst5_addr s hs]; exact hclr4 s hs q hq)
                        have hf5 := MeasuredClear.fixupFactor9_loaded pass5.clearData o5 read low hot
                          tree11 836 clearPaths hot_injective low_ne_hot htree_hdisj
                          (st5 s) (pass5.afterSwap read (st4 s)) (hst5_hot s hs)
                          (fun q hq => by rw [hst5_836 s hs, hst5_addr s hs]; exact hclr5 s hs q hq)
                        rw [pass1.clearData_targets pass1_geo] at hf1
                        rw [pass2.clearData_targets pass2_geo] at hf2
                        rw [pass3.clearData_targets pass3_geo] at hf3
                        rw [pass4.clearData_targets pass4_geo] at hf4
                        rw [pass5.clearData_targets pass5_geo] at hf5
                        rw [hf1, hf2, hf3, hf4, hf5]
                      rw [hff, hst5_eq s hs, one_mul])))))
  obtain ⟨cs, al, ma⟩ := hsim
  refine ⟨cs, al.imp (fun b c hb s hs => ?_), ma⟩
  simpa only [id_eq, one_smul, First18.lmap_ket] using hb s hs

theorem rawProgram_coherent (coeffs : Fin 1048576 → PointCoeff) (Q : Point)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((rawProgram start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (fun s => pointWrite (tablePoint coeffs Q
        (tableAddressValue bits s)) s)) Input := by
  unfold CoherentlyImplementsOn
  rw [rawProgram_run]
  exact rawSource_coherent coeffs Q

/-! ### Resources, root-seeding, and window interface -/

theorem rawProgram_tCount (read : ConstantBit 1048576 → Bool) (start : Nat) (h : Fin start → Bool) :
    ((rawProgram start).instantiate read h).tCount = 7 * 380707 := by
  have hlay : tree11.Layout 836 clearPaths := by unfold tree11; exact clear_layout
  have hFix : ∀ c rs hh, ((stepFix c rs).instantiate read hh).tCount = 7 * 2549 := by
    intro c rs hh
    rw [stepFix, castFinish_instantiate,
      MeasuredClear.fixupProgram_tCount9 allData rs low hot tree11 836 scratch clearPaths hlay]
    have hn : tree11.internalNodes = 2047 := by unfold tree11; exact clear_nodes
    rw [hn]
  have h5 : ∀ c rs hh, ((step5 c rs).instantiate read hh).tCount = 7 * (pass5.selMeas + pass5.garbLen) + 7 * 2549 :=
    fun c rs hh => by rw [step5]; exact pass5.stepProg_tCount pass5_geo stepFix read hFix c rs hh
  have h45 : ∀ c rs hh, ((step45 c rs).instantiate read hh).tCount =
      7 * (pass4.selMeas + pass4.garbLen) + (7 * (pass5.selMeas + pass5.garbLen) + 7 * 2549) :=
    fun c rs hh => by rw [step45]; exact pass4.stepProg_tCount pass4_geo step5 read h5 c rs hh
  have h345 : ∀ c rs hh, ((step345 c rs).instantiate read hh).tCount =
      7 * (pass3.selMeas + pass3.garbLen) +
      (7 * (pass4.selMeas + pass4.garbLen) + (7 * (pass5.selMeas + pass5.garbLen) + 7 * 2549)) :=
    fun c rs hh => by rw [step345]; exact pass3.stepProg_tCount pass3_geo step45 read h45 c rs hh
  have h2345 : ∀ c rs hh, ((step2345 c rs).instantiate read hh).tCount =
      7 * (pass2.selMeas + pass2.garbLen) +
      (7 * (pass3.selMeas + pass3.garbLen) +
      (7 * (pass4.selMeas + pass4.garbLen) + (7 * (pass5.selMeas + pass5.garbLen) + 7 * 2549))) :=
    fun c rs hh => by rw [step2345]; exact pass2.stepProg_tCount pass2_geo step345 read h345 c rs hh
  rw [rawProgram, castFinish_instantiate, pass1.stepProg_tCount pass1_geo step2345 read h2345,
    pass1_nums.2.2.1, pass1_nums.2.2.2, pass2_nums.2.2.1, pass2_nums.2.2.2,
    pass3_nums.2.2.1, pass3_nums.2.2.2, pass4_nums.2.2.1, pass4_nums.2.2.2,
    pass5_nums.2.2.1, pass5_nums.2.2.2]

theorem rawProgram_residue (start : Nat) : residue (rawProgram start) = 0 := by
  have hFix : ∀ c rs, residue (stepFix c rs) = 0 := fun c rs => by
    rw [stepFix, residue_cast]; exact MeasuredClear.fixupProgram_residue9 _ _ _ _ _ _ _ _
  have h5 : ∀ c rs, residue (step5 c rs) = 0 := fun c rs => by
    rw [step5]; exact pass5.stepProg_residue pass5_geo stepFix hFix c rs
  have h45 : ∀ c rs, residue (step45 c rs) = 0 := fun c rs => by
    rw [step45]; exact pass4.stepProg_residue pass4_geo step5 h5 c rs
  have h345 : ∀ c rs, residue (step345 c rs) = 0 := fun c rs => by
    rw [step345]; exact pass3.stepProg_residue pass3_geo step45 h45 c rs
  have h2345 : ∀ c rs, residue (step2345 c rs) = 0 := fun c rs => by
    rw [step2345]; exact pass2.stepProg_residue pass2_geo step345 h345 c rs
  rw [rawProgram, residue_cast]
  exact pass1.stepProg_residue pass1_geo step2345 h2345 start List.nil

theorem rawProgram_added (start : Nat) : added (rawProgram start) = 380707 := by
  have h := exact_t (rawProgram start) (rawProgram_residue start) (fun _ => false) (fun _ => false)
  have ht := rawProgram_tCount (fun _ => false) start (fun _ => false)
  exact Nat.eq_of_mul_eq_mul_left (by decide) (h.symm.trans ht)

theorem rawProgram_slots (start : Nat) : (rawProgram start).gateSlots ≤ 23500000000 := by
  have hlay : tree11.Layout 836 clearPaths := by unfold tree11; exact clear_layout
  have hFix : ∀ c rs, (stepFix c rs).gateSlots ≤ 22770000000 := fun c rs => by
    rw [stepFix, castFinish_gateSlots,
      MeasuredClear.fixupProgram_slots9 allData rs low hot tree11 836 scratch clearPaths hlay]
    have hl : tree11.leaves = 2048 := by unfold tree11; exact clear_leaves
    have hn : tree11.internalNodes = 2047 := by unfold tree11; exact clear_nodes
    have hm : min allData.length rs.length ≤ 5427 := (Nat.min_le_left _ _).trans (by rw [allData_length])
    rw [hl, hn]
    omega
  have h5 : ∀ c rs, (step5 c rs).gateSlots ≤
      (2 ^ pass5.k * pass5.m) * (pass5.selMeas + 1) + 10 * pass5.selMeas + 3 * pass5.garbLen + 22770000000 :=
    fun c rs => by rw [step5]; exact pass5.stepProg_slots pass5_geo stepFix hFix c rs
  have h45 : ∀ c rs, (step45 c rs).gateSlots ≤
      (2 ^ pass4.k * pass4.m) * (pass4.selMeas + 1) + 10 * pass4.selMeas + 3 * pass4.garbLen +
      ((2 ^ pass5.k * pass5.m) * (pass5.selMeas + 1) + 10 * pass5.selMeas + 3 * pass5.garbLen + 22770000000) :=
    fun c rs => by rw [step45]; exact pass4.stepProg_slots pass4_geo step5 h5 c rs
  have h345 : ∀ c rs, (step345 c rs).gateSlots ≤
      (2 ^ pass3.k * pass3.m) * (pass3.selMeas + 1) + 10 * pass3.selMeas + 3 * pass3.garbLen +
      ((2 ^ pass4.k * pass4.m) * (pass4.selMeas + 1) + 10 * pass4.selMeas + 3 * pass4.garbLen +
      ((2 ^ pass5.k * pass5.m) * (pass5.selMeas + 1) + 10 * pass5.selMeas + 3 * pass5.garbLen + 22770000000)) :=
    fun c rs => by rw [step345]; exact pass3.stepProg_slots pass3_geo step45 h45 c rs
  have h2345 : ∀ c rs, (step2345 c rs).gateSlots ≤
      (2 ^ pass2.k * pass2.m) * (pass2.selMeas + 1) + 10 * pass2.selMeas + 3 * pass2.garbLen +
      ((2 ^ pass3.k * pass3.m) * (pass3.selMeas + 1) + 10 * pass3.selMeas + 3 * pass3.garbLen +
      ((2 ^ pass4.k * pass4.m) * (pass4.selMeas + 1) + 10 * pass4.selMeas + 3 * pass4.garbLen +
      ((2 ^ pass5.k * pass5.m) * (pass5.selMeas + 1) + 10 * pass5.selMeas + 3 * pass5.garbLen + 22770000000))) :=
    fun c rs => by rw [step2345]; exact pass2.stepProg_slots pass2_geo step345 h345 c rs
  rw [rawProgram, castFinish_gateSlots]
  refine (pass1.stepProg_slots pass1_geo step2345 h2345 start List.nil).trans ?_
  rw [pass1_nums.1, pass1_nums.2.1, pass1_nums.2.2.1, pass1_nums.2.2.2,
    pass2_nums.1, pass2_nums.2.1, pass2_nums.2.2.1, pass2_nums.2.2.2,
    pass3_nums.1, pass3_nums.2.1, pass3_nums.2.2.1, pass3_nums.2.2.2,
    pass4_nums.1, pass4_nums.2.1, pass4_nums.2.2.1, pass4_nums.2.2.2,
    pass5_nums.1, pass5_nums.2.1, pass5_nums.2.2.1, pass5_nums.2.2.2]
  norm_num

theorem rawProgram_wellFormed (start : Nat) : (rawProgram start).WellFormed := by
  have hlay : tree11.Layout 836 clearPaths := by unfold tree11; exact clear_layout
  have hscr : scratch ∉ 836 :: tree11.indexWires.dedup ++ clearPaths := by
    unfold tree11; exact scratch_not_tree
  have hFix : ∀ c rs, (stepFix c rs).WellFormed := fun c rs => by
    rw [stepFix, castFinish_wellFormed]
    exact MeasuredClear.fixupProgram_wellFormed9 allData rs low hot tree11 836 scratch
      clearPaths hlay hot_injective low_ne_hot hscr scratch_not_hot
  have h5 : ∀ c rs, (step5 c rs).WellFormed := fun c rs => by
    rw [step5]; exact pass5.stepProg_wellFormed pass5_geo stepFix hFix c rs
  have h45 : ∀ c rs, (step45 c rs).WellFormed := fun c rs => by
    rw [step45]; exact pass4.stepProg_wellFormed pass4_geo step5 h5 c rs
  have h345 : ∀ c rs, (step345 c rs).WellFormed := fun c rs => by
    rw [step345]; exact pass3.stepProg_wellFormed pass3_geo step45 h45 c rs
  have h2345 : ∀ c rs, (step2345 c rs).WellFormed := fun c rs => by
    rw [step2345]; exact pass2.stepProg_wellFormed pass2_geo step345 h345 c rs
  rw [rawProgram, castFinish_wellFormed]
  exact pass1.stepProg_wellFormed pass1_geo step2345 h2345 start List.nil

theorem rawProgram_support (start : Nat) : straightWires (rawProgram start) ⊆ List.range 1613 := by
  have hFix : ∀ c rs, straightWires (stepFix c rs) ⊆ List.range 1613 := fun c rs => by
    rw [stepFix, straightWires_castFinish, RootPass.straightWires_eq_naive]
    apply MeasuredClear.fixupProgram_within9
    · decide
    · decide
    · intro i; rw [List.mem_range]; have := i.isLt; simp only [low]; (try dsimp only [Wire] at *); omega
    · intro i; rw [List.mem_range]; have := i.isLt; simp only [hot]; (try dsimp only [Wire] at *); omega
    · intro w hw
      have hi : w ∈ high := by unfold tree11 at hw; exact (tableAddressTree_mem_index high 0 1 w).mp hw
      rw [List.mem_range]; simp only [high, List.mem_range'_1] at hi; (try dsimp only [Wire] at *); omega
    · intro w hw
      rw [List.mem_range]; simp only [clearPaths, List.mem_range'_1] at hw; (try dsimp only [Wire] at *); omega
  have h5 : ∀ c rs, straightWires (step5 c rs) ⊆ List.range 1613 := fun c rs => by
    rw [step5]; exact pass5.stepProg_support pass5_geo stepFix hFix c rs
  have h45 : ∀ c rs, straightWires (step45 c rs) ⊆ List.range 1613 := fun c rs => by
    rw [step45]; exact pass4.stepProg_support pass4_geo step5 h5 c rs
  have h345 : ∀ c rs, straightWires (step345 c rs) ⊆ List.range 1613 := fun c rs => by
    rw [step345]; exact pass3.stepProg_support pass3_geo step45 h45 c rs
  have h2345 : ∀ c rs, straightWires (step2345 c rs) ⊆ List.range 1613 := fun c rs => by
    rw [step2345]; exact pass2.stepProg_support pass2_geo step345 h345 c rs
  rw [rawProgram, straightWires_castFinish]
  exact pass1.stepProg_support pass1_geo step2345 h2345 start List.nil

theorem rawProgram_safe836 (start : Nat) : RootPass.safeProgram 836 (rawProgram start) := by
  have hlay : tree11.Layout 836 clearPaths := by unfold tree11; exact clear_layout
  obtain ⟨hb, hp⟩ := RootPass.layout_avoids hlay
  have hFix : ∀ c rs, RootPass.safeProgram 836 (stepFix c rs) := fun c rs => by
    rw [stepFix, RootPass.safeProgram_cast]
    exact RootPass.fixupProgram9_safe 836 allData rs low hot tree11 836 scratch
      clearPaths low_ne_836 hot_ne_836 (by decide) hb hp
  have h5 : ∀ c rs, RootPass.safeProgram 836 (step5 c rs) := fun c rs => by
    rw [step5]; exact pass5.stepProg_safe836 pass5_geo stepFix hFix c rs
  have h45 : ∀ c rs, RootPass.safeProgram 836 (step45 c rs) := fun c rs => by
    rw [step45]; exact pass4.stepProg_safe836 pass4_geo step5 h5 c rs
  have h345 : ∀ c rs, RootPass.safeProgram 836 (step345 c rs) := fun c rs => by
    rw [step345]; exact pass3.stepProg_safe836 pass3_geo step45 h45 c rs
  have h2345 : ∀ c rs, RootPass.safeProgram 836 (step2345 c rs) := fun c rs => by
    rw [step2345]; exact pass2.stepProg_safe836 pass2_geo step345 h345 c rs
  rw [rawProgram, RootPass.safeProgram_cast]
  exact pass1.stepProg_safe836 pass1_geo step2345 h2345 start List.nil

theorem rawProgram_hits836 (start : Nat) : RootPass.literalHits 836 (rawProgram start) = 6 := by
  have hlay : tree11.Layout 836 clearPaths := by unfold tree11; exact clear_layout
  have hnodes : tree11.internalNodes = 2047 := by unfold tree11; exact clear_nodes
  have hFix : ∀ c rs, RootPass.literalHits 836 (stepFix c rs) = 1 := fun c rs => by
    rw [stepFix, RootPass.literalHits_cast,
      RootPass.fixupProgram9_hits 836 allData rs low hot tree11 836 scratch
        clearPaths low_ne_836 hot_ne_836]
    exact RootPass.recordUnaryOps_root_hits 836 tree11 clearPaths hlay (by rw [hnodes]; decide)
  have h5 : ∀ c rs, RootPass.literalHits 836 (step5 c rs) = 2 := fun c rs => by
    rw [step5]; exact pass5.stepProg_hits836 pass5_geo stepFix hFix c rs
  have h45 : ∀ c rs, RootPass.literalHits 836 (step45 c rs) = 3 := fun c rs => by
    rw [step45]; exact pass4.stepProg_hits836 pass4_geo step5 h5 c rs
  have h345 : ∀ c rs, RootPass.literalHits 836 (step345 c rs) = 4 := fun c rs => by
    rw [step345]; exact pass3.stepProg_hits836 pass3_geo step45 h45 c rs
  have h2345 : ∀ c rs, RootPass.literalHits 836 (step2345 c rs) = 5 := fun c rs => by
    rw [step2345]; exact pass2.stepProg_hits836 pass2_geo step345 h345 c rs
  rw [rawProgram, RootPass.literalHits_cast]
  exact pass1.stepProg_hits836 pass1_geo step2345 h2345 start List.nil

theorem program_coherent (coeffs : Fin 1048576 → PointCoeff) (Q : Point)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((program start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (fun s => pointWrite (tablePoint coeffs Q
        (tableAddressValue bits s)) s)) Input := by
  rw [program]
  exact RootPass.seedProgram_coherent 836 (rawProgram start) _ history _ _
    (rawProgram_safe836 start) (fun _ hs => hs.1) (rawProgram_coherent coeffs Q start history)

theorem program_residue (start : Nat) : residue (program start) = 0 := by
  have h := RootPass.seedProgram_residue_le 836 (rawProgram start)
  rw [rawProgram_residue] at h
  rw [program]
  exact Nat.eq_zero_of_le_zero h

theorem program_added (start : Nat) : added (program start) = 380701 := by
  have h := RootPass.seedProgram_added 836 (rawProgram start)
  rw [rawProgram_added, rawProgram_hits836] at h
  rw [program]
  omega

theorem program_slots (start : Nat) : (program start).gateSlots ≤ 23500000000 := by
  rw [program, RootPass.seedProgram_slots]
  exact rawProgram_slots start

theorem program_support (start : Nat) : straightWires (program start) ⊆ List.range 1613 := by
  rw [program]
  exact (RootPass.seedProgram_wires 836 _).trans (rawProgram_support start)

theorem program_wellFormed (start : Nat) : (program start).WellFormed := by
  rw [program]
  exact RootPass.seedProgram_wellFormed 836 _ (rawProgram_wellFormed start)

def windowGeneric {n : Nat} (rows : Fin 1048576 → Fin n) : Single.Window n :=
  ⟨bits.reverse, 380716, fun start => reindexStraight rows (program start)⟩

theorem window_law_generic {n : Nat} (coeffs : Fin n → PointCoeff) (rows : Fin 1048576 → Fin n)
    (init : Point → Nat → Point)
    (hcoeff : ∀ Q, order • Q = 0 → ∀ a : Fin 1048576,
      constantPoint Q (coeffs (rows a)) = init Q a.val) :
    Single.WindowLaw coeffs (windowGeneric rows) (update init) Input := by
  intro Q hQ hn start history
  have hvalid := program_coherent (fun a => coeffs (rows a)) Q start history
  have hupdate : (fun s => pointWrite
      (tablePoint (fun a => coeffs (rows a)) Q (tableAddressValue bits s)) s) = update init Q := by
    funext s
    unfold tablePoint update
    have hbound : tableAddressValue bits s < 1048576 := by
      have hb := tableAddressValue_lt bits s
      simpa only [bits_length] using hb
    simp only [Nat.mod_eq_of_lt hbound]
    rw [hcoeff Q hQ]
  rw [hupdate] at hvalid
  unfold windowGeneric
  rw [reindexStraight_instantiate,
    readConstant_reindex rows (fun a => coeffs (rows a)) coeffs Q (fun _ => rfl)]
  exact hvalid

theorem window_wellFormed {n : Nat} (rows : Fin 1048576 → Fin n) (start : Nat) :
    ((windowGeneric rows).program start).WellFormed := by
  unfold windowGeneric
  exact (reindexStraight_wellFormed rows (program start)).mpr (program_wellFormed start)

theorem window_slots {n : Nat} (rows : Fin 1048576 → Fin n) (start : Nat) :
    ((windowGeneric rows).program start).gateSlots ≤ 23500000000 := by
  unfold windowGeneric
  rw [reindexStraight_gateSlots]
  exact program_slots start

theorem window_support {n : Nat} (rows : Fin 1048576 → Fin n) (start : Nat) :
    straightWires ((windowGeneric rows).program start) ⊆ List.range 1613 := by
  unfold windowGeneric
  rw [straightWires_reindex]
  exact program_support start

theorem window_credit {n : Nat} (_coeffs : Fin n → PointCoeff) (rows : Fin 1048576 → Fin n)
    (_Q : Point) (start : Nat) (_history : Fin start → Bool) :
    added ((windowGeneric rows).program start) = 380701 := by
  unfold windowGeneric
  rw [added_reindex]
  exact program_added start

#print axioms program_coherent
#print axioms program_added
#print axioms window_law_generic

end
end ShorECDLP.Entrant.First20Split
