import ShorECDLP.Submission.Naive.Arithmetic.Secp256k1Instance
import ShorECDLP.Submission.Naive.Challenge.NumericLengths


namespace ShorECDLP
namespace Secp256k1
namespace V2
namespace InvChain

open Arithmetic
open Secp256k1Instance (reg regBlock bitBlock Block blocksWires mulWork mulProgram mulCost
  mulWorkBlocks fieldWidth)


def squarings (cur : Nat) : Nat → List (Nat × Nat)
  | 0 => []
  | n + 1 => (cur, cur) :: squarings (cur + 1) n

def expand : Nat → List (Nat × Nat) → List (Nat × Nat)
  | _, [] => []
  | cur, (n, m) :: rest => squarings cur n ++ (cur + n, m) :: expand (cur + n + 1) rest

def chainBlocks : List (Nat × Nat) :=
  [(1, 0), (1, 0), (3, 4), (3, 4), (2, 2), (11, 15), (22, 27), (44, 50), (88, 95), (44, 50),
    (3, 4), (23, 27), (5, 0), (3, 2), (2, 0)]

def chain : List (Nat × Nat) := expand 0 chainBlocks

def validB : Nat → List (Nat × Nat) → Bool
  | _, [] => true
  | k, (i, j) :: rest => (decide (i < k) && decide (j < k)) && validB (k + 1) rest

def expsAux : List Nat → List (Nat × Nat) → List Nat
  | acc, [] => acc
  | acc, (i, j) :: rest => expsAux (acc ++ [acc.getD i 0 + acc.getD j 0]) rest

theorem chain_length : chain.length = 270 := by decide +kernel

theorem chain_valid : validB 1 chain = true := by decide +kernel

theorem chain_exp : (expsAux [1] chain).getD 270 0 = p - 2 := by decide +kernel

theorem expsAux_length :
    ∀ (acc : List Nat) (steps : List (Nat × Nat)),
      (expsAux acc steps).length = acc.length + steps.length
  | _, [] => rfl
  | acc, (i, j) :: rest => by
      rw [expsAux, expsAux_length]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega


def mulW : List Wire := mulWork 273 274

theorem reg_disjoint {u v : Nat} (h : u ≠ v) {w : Wire} (hu : w ∈ (reg u).wires) :
    w ∉ (reg v).wires := fun hv =>
  List.disjoint_left.mp
    (Secp256k1Instance.Block.disjoint_of_id_ne (left := regBlock u) (right := regBlock v) h)
    hu hv

theorem reg_not_mulW {u : Nat} (h : u < 273) {w : Wire} (hu : w ∈ (reg u).wires) :
    w ∉ mulW := by
  rw [mulW, Secp256k1Instance.mulWork_eq_blocksWires]
  apply Secp256k1Instance.not_mem_blocksWires_of_source (regBlock u) _ w hu
  simp only [Secp256k1Instance.mulWorkBlocks_ids, Secp256k1Instance.regBlock_id,
    List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem reg_pair_nodup {u v : Nat} (h : u ≠ v) : ((reg u).wires ++ (reg v).wires).Nodup :=
  List.nodup_append.mpr ⟨(regBlock u).wires_nodup, (regBlock v).wires_nodup,
    fun _ hx _ hy e => reg_disjoint h hx (e ▸ hy)⟩

theorem mul_valid {a b c : Nat} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a < 273) (hb : b < 273) (hc : c < 273) :
    ({ lhs := (reg a).wires, rhs := (reg b).wires, out := (reg c).wires,
       work := mulWork 273 274 } : RegisterLayout).Valid := by
  refine ⟨(reg a).length_eq.trans (reg b).length_eq.symm,
    (reg a).length_eq.trans (reg c).length_eq.symm, ?_⟩
  have hids := Secp256k1Instance.append_mulWorkBlocks_ids_nodup
    [regBlock a, regBlock b, regBlock c] 273 274
    (by
      simp only [List.map_cons, List.map_nil, Secp256k1Instance.regBlock_id, List.nodup_cons,
        List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨⟨hab, hac⟩, hbc, not_false, List.nodup_nil⟩)
    (by
      simp only [List.map_cons, List.map_nil, Secp256k1Instance.regBlock_id, List.mem_cons,
        List.not_mem_nil, or_false]
      omega)
    (by omega)
  have h := Secp256k1Instance.blocksWires_nodup _ hids
  rw [RegisterLayout.allWires, Secp256k1Instance.mulWork_eq_blocksWires]
  simpa only [blocksWires, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.append_assoc, Secp256k1Instance.reg_wires] using h


def stepCircuit (a b c : Nat) : Circuit :=
  if a = b then
    copyReg (reg a).wires (reg 272).wires ++ mulProgram a 272 c 273 274 ++
      (copyReg (reg a).wires (reg 272).wires).reverse
  else mulProgram a b c 273 274

theorem step_spec (a b c : Nat) (ha : a < 272) (hb : b < 272) (hc : c < 272)
    (hac : a ≠ c) (hbc : b ≠ c) (st : BasisState)
    (hva : regValue (reg a).wires st < p) (hvb : regValue (reg b).wires st < p)
    (hcleanC : Clean (reg c).wires st) (hcleanD : Clean (reg 272).wires st)
    (hcleanW : Clean mulW st) :
    regValue (reg c).wires (Classical.run (stepCircuit a b c) st) =
        regValue (reg a).wires st * regValue (reg b).wires st % p ∧
      Clean mulW (Classical.run (stepCircuit a b c) st) ∧
      ∀ w, w ∉ (reg c).wires → w ∉ mulW →
        Classical.run (stepCircuit a b c) st w = st w := by
  by_cases hab : a = b
  · subst hab
    rw [stepCircuit, if_pos rfl]
    let copy := copyReg (reg a).wires (reg 272).wires
    have hnd : ((reg a).wires ++ (reg 272).wires).Nodup := reg_pair_nodup (by omega)
    have hcopyUses : CircuitUsesOnly ((reg a).wires ++ (reg 272).wires) copy :=
      copyReg_usesOnly _ _ _ (fun w hw => List.mem_append_left _ hw)
        (fun w hw => List.mem_append_right _ hw)
    have hcopyWf : CircuitWellFormed copy := copyReg_wellFormed _ _ hnd
    let st1 := Classical.run copy st
    let st2 := Classical.run (mulProgram a 272 c 273 274) st1
    let st3 := Classical.run copy.reverse st2
    have hrun : Classical.run (copy ++ mulProgram a 272 c 273 274 ++ copy.reverse) st = st3 := by
      simp only [Classical.run_append, st3, st2, st1]
    rw [hrun]
    have h1out : ∀ w, w ∉ (reg 272).wires → st1 w = st w :=
      fun w hw => copyReg_other w _ _ st hw
    have h1dup : regValue (reg 272).wires st1 = regValue (reg a).wires st :=
      copyReg_correct _ _ st (by rw [(reg 272).length_eq, (reg a).length_eq]) hnd hcleanD
    have h1a : regValue (reg a).wires st1 = regValue (reg a).wires st :=
      regValue_congr _ _ _ (fun w hw => h1out w (reg_disjoint (by omega) hw))
    have hclean1 : Clean ((reg c).wires ++ mulWork 273 274) st1 := by
      intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · rw [h1out w (reg_disjoint (by omega) hw)]
        exact hcleanC w hw
      · rw [h1out w (fun hd => reg_not_mulW (by omega) hd hw)]
        exact hcleanW w hw
    have hcon := Secp256k1Instance.mul_contract a 272 c 273 274 (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
    obtain ⟨h2a, h2d, h2c, h2w⟩ := Secp256k1Instance.mulProgram_correct a 272 c 273 274
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) st1
      (mul_valid (by omega) hac (by omega) (by omega) (by omega) (by omega))
      (by rw [h1a]; exact hva) (by rw [h1dup]; exact hva) hclean1
    have hcancel : Classical.run copy.reverse st1 = st :=
      run_reverse_cancel copy st (copyReg_HPFree _ _) hcopyWf
    have h3in : ∀ w ∈ (reg a).wires ++ (reg 272).wires, st3 w = st w := by
      intro w hw
      have hagree : ∀ v ∈ (reg a).wires ++ (reg 272).wires, st2 v = st1 v := by
        intro v hv
        rcases List.mem_append.mp hv with hv | hv
        · exact h2a v hv
        · exact h2d v hv
      calc
        st3 w = Classical.run copy.reverse st1 w :=
          CircuitUsesOnly.run_congr (usesOnly_reverse hcopyUses) hagree w hw
        _ = st w := by rw [hcancel]
    have h3out : ∀ w, w ∉ (reg a).wires ++ (reg 272).wires → st3 w = st2 w :=
      fun w hw => (usesOnly_reverse hcopyUses).preservesOutside st2 w hw
    have hnotC : ∀ w ∈ (reg c).wires, w ∉ (reg a).wires ++ (reg 272).wires := by
      intro w hw hm
      rcases List.mem_append.mp hm with hm | hm
      · exact reg_disjoint hac hm hw
      · exact reg_disjoint (by omega) hm hw
    have hnotW : ∀ w ∈ mulW, w ∉ (reg a).wires ++ (reg 272).wires := by
      intro w hw hm
      rcases List.mem_append.mp hm with hm | hm
      · exact reg_not_mulW (by omega) hm hw
      · exact reg_not_mulW (by omega) hm hw
    refine ⟨?_, ?_, ?_⟩
    · rw [regValue_congr _ st3 st2 (fun w hw => h3out w (hnotC w hw)), h2c, h1a, h1dup]
    · intro w hw
      rw [h3out w (hnotW w hw)]
      exact h2w w hw
    · intro w hwc hww
      by_cases hin : w ∈ (reg a).wires ++ (reg 272).wires
      · exact h3in w hin
      · rw [h3out w hin]
        have hout : w ∉ RegisterLayout.allWires
            { lhs := (reg a).wires, rhs := (reg 272).wires, out := (reg c).wires,
              work := mulWork 273 274 } := by
          simp only [RegisterLayout.allWires, List.mem_append, not_or] at hin ⊢
          exact ⟨⟨⟨hin.1, hin.2⟩, hwc⟩, hww⟩
        change Classical.run (mulProgram a 272 c 273 274) st1 w = st w
        rw [hcon.usesOnly.preservesOutside st1 w hout]
        exact h1out w (fun h => hin (List.mem_append_right _ h))
  · rw [stepCircuit, if_neg hab]
    have hcon := Secp256k1Instance.mul_contract a b c 273 274 (by omega) (by omega)
      (by omega) hab (by omega) (by omega)
    have hclean : Clean ((reg c).wires ++ mulWork 273 274) st := by
      intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · exact hcleanC w hw
      · exact hcleanW w hw
    obtain ⟨hA, hB, hC, hW⟩ := Secp256k1Instance.mulProgram_correct a b c 273 274
      (by omega) (by omega) (by omega) hab (by omega) (by omega) st
      (mul_valid hab hac hbc (by omega) (by omega) (by omega)) hva hvb hclean
    refine ⟨hC, hW, ?_⟩
    intro w hwc hww
    by_cases hwa : w ∈ (reg a).wires
    · exact hA w hwa
    by_cases hwb : w ∈ (reg b).wires
    · exact hB w hwb
    apply hcon.usesOnly.preservesOutside
    simp only [RegisterLayout.allWires, List.mem_append, not_or]
    exact ⟨⟨⟨hwa, hwb⟩, hwc⟩, hww⟩


theorem step_facts (a b c : Nat) (ha : a < 272) (hb : b < 272) (hc : c < 272)
    (hac : a ≠ c) (hbc : b ≠ c) :
    Classical.HPFree (stepCircuit a b c) ∧ CircuitWellFormed (stepCircuit a b c) ∧
      tCount (stepCircuit a b c) = mulCost ∧
      ∀ S : List Wire, (∀ w ∈ (reg a).wires, w ∈ S) →
        (∀ w ∈ (reg b).wires, w ∈ S) → (∀ w ∈ (reg c).wires, w ∈ S) →
        (∀ w ∈ (reg 272).wires, w ∈ S) → (∀ w ∈ mulW, w ∈ S) →
        CircuitUsesOnly S (stepCircuit a b c) := by
  by_cases hab : a = b
  · subst hab
    rw [stepCircuit, if_pos rfl]
    have hcon := Secp256k1Instance.mul_contract a 272 c 273 274 (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
    have hnd : ((reg a).wires ++ (reg 272).wires).Nodup := reg_pair_nodup (by omega)
    have hcopyWf := copyReg_wellFormed (reg a).wires (reg 272).wires hnd
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [Classical.hpFree_append]
      exact ⟨⟨copyReg_HPFree _ _, hcon.hpFree⟩,
        Arithmetic.hpFree_reverse (copyReg_HPFree _ _)⟩
    · simp only [circuitWellFormed_append]
      exact ⟨⟨hcopyWf, hcon.wellFormed
        (mul_valid (by omega) hac (by omega) (by omega) (by omega) (by omega))⟩,
        Arithmetic.wellFormed_reverse hcopyWf⟩
    · rw [tCount_append, tCount_append, tCount_reverse, copyReg_tCount, hcon.counted]
      omega
    · intro S hA _ hC hD hW
      have hcopy := copyReg_usesOnly (reg a).wires (reg 272).wires S hA hD
      have hmul : CircuitUsesOnly S (mulProgram a 272 c 273 274) := by
        apply usesOnly_mono hcon.usesOnly
        intro w hw
        simp only [RegisterLayout.allWires, List.mem_append] at hw
        rcases hw with ((hw | hw) | hw) | hw
        · exact hA w hw
        · exact hD w hw
        · exact hC w hw
        · exact hW w hw
      exact usesOnly_append (usesOnly_append hcopy hmul) (usesOnly_reverse hcopy)
  · rw [stepCircuit, if_neg hab]
    have hcon := Secp256k1Instance.mul_contract a b c 273 274 (by omega) (by omega)
      (by omega) hab (by omega) (by omega)
    refine ⟨hcon.hpFree,
      hcon.wellFormed (mul_valid hab hac hbc (by omega) (by omega) (by omega)),
      hcon.counted, ?_⟩
    intro S hA hB hC _ hW
    apply usesOnly_mono hcon.usesOnly
    intro w hw
    simp only [RegisterLayout.allWires, List.mem_append] at hw
    rcases hw with ((hw | hw) | hw) | hw
    · exact hA w hw
    · exact hB w hw
    · exact hC w hw
    · exact hW w hw


def chainCircuit : Nat → List (Nat × Nat) → Circuit
  | _, [] => []
  | k, (i, j) :: rest => stepCircuit i j k ++ chainCircuit (k + 1) rest

theorem chain_facts (B : Nat) (hB : B ≤ 270) :
    ∀ (steps : List (Nat × Nat)) (k : Nat), validB k steps = true →
      k + steps.length ≤ B + 1 →
      Classical.HPFree (chainCircuit k steps) ∧ CircuitWellFormed (chainCircuit k steps) ∧
        tCount (chainCircuit k steps) = steps.length * mulCost ∧
        ∀ S : List Wire, (∀ m ≤ B, ∀ w ∈ (reg m).wires, w ∈ S) →
          (∀ w ∈ (reg 272).wires, w ∈ S) → (∀ w ∈ mulW, w ∈ S) →
          CircuitUsesOnly S (chainCircuit k steps)
  | [], _, _, _ =>
      ⟨by simp [chainCircuit], by simp [chainCircuit], by simp [chainCircuit],
        fun _ _ _ _ => by simp [chainCircuit, CircuitUsesOnly]⟩
  | (i, j) :: rest, k, hv, hlen => by
      simp only [validB, Bool.and_eq_true, decide_eq_true_eq] at hv
      obtain ⟨⟨hi, hj⟩, hrest⟩ := hv
      simp only [List.length_cons] at hlen
      obtain ⟨hf1, hw1, ht1, hu1⟩ := step_facts i j k (by omega) (by omega) (by omega)
        (by omega) (by omega)
      obtain ⟨hf2, hw2, ht2, hu2⟩ := chain_facts B hB rest (k + 1) hrest (by omega)
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [chainCircuit, Classical.hpFree_append]
        exact ⟨hf1, hf2⟩
      · simp only [chainCircuit, circuitWellFormed_append]
        exact ⟨hw1, hw2⟩
      · rw [chainCircuit, tCount_append, ht1, ht2, List.length_cons]
        ring
      · intro S hR hD hW
        rw [chainCircuit]
        exact usesOnly_append
          (hu1 S (hR i (by omega)) (hR j (by omega)) (hR k (by omega)) hD hW)
          (hu2 S hR hD hW)

def Inv (L x : Nat) (acc : List Nat) (st : BasisState) : Prop :=
  (∀ m < acc.length, regValue (reg m).wires st = x ^ acc.getD m 0 % p) ∧
    (∀ m, acc.length ≤ m → m ≤ L → Clean (reg m).wires st) ∧
    Clean (reg 272).wires st ∧ Clean mulW st

theorem getD_append_lt (acc l : List Nat) (m : Nat) (h : m < acc.length) :
    (acc ++ l).getD m 0 = acc.getD m 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_length (acc : List Nat) (e : Nat) :
    (acc ++ [e]).getD acc.length 0 = e := by
  simp [List.getD_eq_getElem?_getD]

theorem pow_add_mod (x a b : Nat) : x ^ (a + b) % p = (x ^ a % p) * (x ^ b % p) % p := by
  rw [pow_add, Nat.mul_mod]

theorem chain_correct (L x : Nat) (hL : L < 272) :
    ∀ (steps : List (Nat × Nat)) (acc : List Nat) (st : BasisState),
      validB acc.length steps = true → acc.length + steps.length ≤ L + 1 →
      Inv L x acc st →
      Inv L x (expsAux acc steps) (Classical.run (chainCircuit acc.length steps) st)
  | [], _, _, _, _, h => h
  | (i, j) :: rest, acc, st, hv, hlen, hinv => by
      obtain ⟨hval, hclean, hdup, hwork⟩ := hinv
      simp only [validB, Bool.and_eq_true, decide_eq_true_eq] at hv
      obtain ⟨⟨hi, hj⟩, hrest⟩ := hv
      simp only [List.length_cons] at hlen
      have hpos : 0 < p := Secp256k1Instance.p_pos
      obtain ⟨hC, hW, hF⟩ := step_spec i j acc.length (by omega) (by omega) (by omega)
        (by omega) (by omega) st
        (by rw [hval i hi]; exact Nat.mod_lt _ hpos)
        (by rw [hval j hj]; exact Nat.mod_lt _ hpos)
        (hclean _ le_rfl (by omega)) hdup hwork
      let st1 := Classical.run (stepCircuit i j acc.length) st
      have hframe : ∀ m, m ≠ acc.length → m < 273 → ∀ w ∈ (reg m).wires, st1 w = st w :=
        fun m hm hm' w hw => hF w (reg_disjoint hm hw) (reg_not_mulW hm' hw)
      have hinv1 : Inv L x (acc ++ [acc.getD i 0 + acc.getD j 0]) st1 := by
        refine ⟨?_, ?_, ?_, hW⟩
        · intro m hm
          simp only [List.length_append, List.length_singleton] at hm
          by_cases hlt : m < acc.length
          · rw [getD_append_lt _ _ _ hlt,
              regValue_congr _ st1 st (hframe m (by omega) (by omega)), hval m hlt]
          · obtain rfl : m = acc.length := by omega
            rw [getD_append_length, hC, hval i hi, hval j hj, pow_add_mod]
        · intro m hm hmL w hw
          simp only [List.length_append, List.length_singleton] at hm
          rw [hframe m (by omega) (by omega) w hw]
          exact hclean m (by omega) hmL w hw
        · intro w hw
          rw [hframe 272 (by omega) (by omega) w hw]
          exact hdup w hw
      have hrec := chain_correct L x hL rest (acc ++ [acc.getD i 0 + acc.getD j 0]) st1
        (by simpa only [List.length_append, List.length_singleton] using hrest)
        (by simp only [List.length_append, List.length_singleton]; omega) hinv1
      simp only [List.length_append, List.length_singleton] at hrec
      rw [chainCircuit, Classical.run_append, expsAux]
      exact hrec


def base : List Wire := (reg 0).wires

def out : List Wire := (reg 271).wires

def history : List Wire := blocksWires ((List.range' 1 270).map regBlock)

def work : List Wire := history ++ (reg 272).wires ++ mulW

def allBlocks : List Block :=
  [regBlock 0, regBlock 271] ++ (List.range' 1 270).map regBlock ++ [regBlock 272] ++
    mulWorkBlocks 273 274

theorem all_eq_blocksWires : base ++ out ++ work = blocksWires allBlocks := by
  rw [base, out, work, history, mulW, Secp256k1Instance.mulWork_eq_blocksWires, allBlocks]
  simp only [blocksWires, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.append_assoc, Secp256k1Instance.reg_wires]

theorem allBlocks_ids :
    allBlocks.map Block.id =
      [0, 271] ++ List.range' 1 270 ++ [272] ++ [276, 273, 274, 275, 277] := by
  simp [allBlocks, Secp256k1Instance.mulWorkBlocks_ids, List.map_map, Function.comp_def]

theorem allBlocks_ids_nodup : (allBlocks.map Block.id).Nodup := by
  rw [allBlocks_ids]
  refine List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨List.nodup_append.mpr
    ⟨by decide, List.nodup_range', ?_⟩, by decide, ?_⟩, by decide, ?_⟩
  · intro a ha b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1] at ha hb
    omega
  · intro a ha b hb
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_range'_1] at ha hb
    omega
  · intro a ha b hb
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_range'_1] at ha hb
    omega

theorem all_nodup : (base ++ out ++ work).Nodup := by
  rw [all_eq_blocksWires]
  exact Secp256k1Instance.blocksWires_nodup _ allBlocks_ids_nodup

theorem all_lt : ∀ w ∈ base ++ out ++ work, w < 257 * 278 := by
  intro w hw
  rw [all_eq_blocksWires, blocksWires, List.mem_flatMap] at hw
  obtain ⟨b, hb, hwb⟩ := hw
  have hid : b.id < 278 := by
    have hmem : b.id ∈ allBlocks.map Block.id := List.mem_map_of_mem hb
    rw [allBlocks_ids] at hmem
    simp only [List.mem_cons, List.not_mem_nil, List.mem_append, List.mem_range'_1,
      or_false] at hmem
    omega
  have hbound : w < 257 * (b.id + 1) := (Secp256k1Instance.Block.mem_bounds hwb).2
  have hle : 257 * (b.id + 1) ≤ 257 * 278 := Nat.mul_le_mul_left _ (by omega)
  exact Nat.lt_of_lt_of_le hbound hle

theorem base_length : base.length = 257 := (reg 0).length_eq

theorem out_length : out.length = 257 := (reg 271).length_eq

theorem blocksWires_map_regBlock_length :
    ∀ l : List Nat, (blocksWires (l.map regBlock)).length = l.length * 257
  | [] => rfl
  | a :: l => by
      rw [List.map_cons, blocksWires, List.flatMap_cons, List.length_append, ← blocksWires,
        blocksWires_map_regBlock_length l, Secp256k1Instance.Block.wires_length,
        List.length_cons]
      change 257 + l.length * 257 = (l.length + 1) * 257
      ring

theorem mulW_length : mulW.length = 517 := by
  rw [mulW, Secp256k1Instance.mulWork, LowSpaceModMul.work_length, (reg 273).length_eq,
    (reg 274).length_eq]
  rfl

theorem work_length : work.length = 70164 := by
  rw [work, history, List.length_append, List.length_append, mulW_length,
    blocksWires_map_regBlock_length, List.length_range', (reg 272).length_eq]
  rfl

theorem reg_mem_work {m : Nat} (h1 : 1 ≤ m) (h2 : m ≤ 270) :
    ∀ w ∈ (reg m).wires, w ∈ work := by
  intro w hw
  show w ∈ history ++ (reg 272).wires ++ mulW
  apply List.mem_append_left
  apply List.mem_append_left
  rw [history, blocksWires, List.mem_flatMap]
  exact ⟨regBlock m, List.mem_map_of_mem (List.mem_range'_1.mpr ⟨h1, by omega⟩), hw⟩

theorem dup_mem_work : ∀ w ∈ (reg 272).wires, w ∈ work := fun _ hw =>
  List.mem_append_left _ (List.mem_append_right _ hw)

theorem mulW_mem_work : ∀ w ∈ mulW, w ∈ work := fun _ hw => List.mem_append_right _ hw

theorem reg_mem_active {m : Nat} (hm : m ≤ 270) :
    ∀ w ∈ (reg m).wires, w ∈ base ++ work := by
  intro w hw
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · exact List.mem_append_left _ hw
  · exact List.mem_append_right _ (reg_mem_work hpos hm w hw)

theorem active_out_disjoint : ∀ x ∈ base ++ work, ∀ y ∈ out, x ≠ y := by
  obtain ⟨hbo, _, hcross⟩ := List.nodup_append.mp all_nodup
  obtain ⟨_, _, hcross2⟩ := List.nodup_append.mp hbo
  intro x hx y hy
  rcases List.mem_append.mp hx with hx | hx
  · exact hcross2 x hx y hy
  · exact (hcross y (List.mem_append_right _ hy) x hx).symm


def forward : Circuit := chainCircuit 1 chain

def invProgram : Circuit := forward ++ copyReg (reg 270).wires out ++ forward.reverse

theorem forward_facts :
    Classical.HPFree forward ∧ CircuitWellFormed forward ∧ tCount forward = 270 * mulCost ∧
      CircuitUsesOnly (base ++ work) forward := by
  obtain ⟨h1, h2, h3, h4⟩ :=
    chain_facts 270 le_rfl chain 1 chain_valid (by have := chain_length; omega)
  refine ⟨h1, h2, ?_, h4 _ (fun m hm => reg_mem_active hm)
    (fun w hw => List.mem_append_right _ (dup_mem_work w hw))
    (fun w hw => List.mem_append_right _ (mulW_mem_work w hw))⟩
  rw [forward, h3, chain_length]

theorem forward_value (st : BasisState) (hbase : regValue base st < p)
    (hclean : Clean work st) :
    regValue (reg 270).wires (Classical.run forward st) = regValue base st ^ (p - 2) % p := by
  have hinv0 : Inv 270 (regValue base st) ([1] : List Nat) st := by
    refine ⟨?_, ?_, fun w hw => hclean w (dup_mem_work w hw),
      fun w hw => hclean w (mulW_mem_work w hw)⟩
    · intro m hm
      simp only [List.length_singleton, Nat.lt_one_iff] at hm
      subst hm
      rw [List.getD_cons_zero, pow_one, Nat.mod_eq_of_lt hbase]
      rfl
    · intro m hm hmL w hw
      simp only [List.length_singleton] at hm
      exact hclean w (reg_mem_work hm hmL w hw)
  have hfin := chain_correct 270 (regValue base st) (by omega) chain ([1] : List Nat) st chain_valid
    (by have := chain_length; simp only [List.length_singleton]; omega) hinv0
  have h270 := hfin.1 270 (by rw [expsAux_length, chain_length]; decide)
  rw [chain_exp] at h270
  exact h270

theorem invProgram_correct (st : BasisState) (hbase : regValue base st < p)
    (hclean : Clean (out ++ work) st) :
    let after := Classical.run invProgram st
    AgreesOn base st after ∧ regValue out after = regValue base st ^ (p - 2) % p ∧
      Clean work after := by
  obtain ⟨hfree, hwf, _, huses⟩ := forward_facts
  have hcleanOut : Clean out st := fun w hw => hclean w (List.mem_append_left _ hw)
  have hcleanWork : Clean work st := fun w hw => hclean w (List.mem_append_right _ hw)
  obtain ⟨hagree, hval⟩ := ModExp.bennett_cleanup_copyOut forward (base ++ work)
    (reg 270).wires out st huses hfree hwf active_out_disjoint
    ((reg 271).length_eq.trans (reg 270).length_eq.symm) (reg_pair_nodup (by omega)) hcleanOut
  have hagree' : AgreesOn (base ++ work) st (Classical.run invProgram st) := hagree
  have hval' : regValue out (Classical.run invProgram st) =
      regValue (reg 270).wires (Classical.run forward st) := hval
  refine ⟨fun w hw => hagree' w (List.mem_append_left _ hw),
    hval'.trans (forward_value st hbase hcleanWork), fun w hw => ?_⟩
  rw [hagree' w (List.mem_append_right _ hw)]
  exact hcleanWork w hw

theorem invProgram_usesOnly : CircuitUsesOnly (base ++ out ++ work) invProgram := by
  obtain ⟨_, _, _, huses⟩ := forward_facts
  have hf : CircuitUsesOnly (base ++ out ++ work) forward := usesOnly_mono huses (by
    intro w hw
    rcases List.mem_append.mp hw with h | h
    · exact List.mem_append_left _ (List.mem_append_left _ h)
    · exact List.mem_append_right _ h)
  have hc : CircuitUsesOnly (base ++ out ++ work) (copyReg (reg 270).wires out) := by
    apply copyReg_usesOnly
    · intro w hw
      rcases List.mem_append.mp (reg_mem_active (le_refl 270) w hw) with h | h
      · exact List.mem_append_left _ (List.mem_append_left _ h)
      · exact List.mem_append_right _ h
    · intro w hw
      exact List.mem_append_left _ (List.mem_append_right _ hw)
  exact usesOnly_append (usesOnly_append hf hc) (usesOnly_reverse hf)

theorem invProgram_HPFree : Classical.HPFree invProgram := by
  obtain ⟨hfree, _, _, _⟩ := forward_facts
  rw [invProgram, Classical.hpFree_append, Classical.hpFree_append]
  exact ⟨⟨hfree, copyReg_HPFree _ _⟩, Arithmetic.hpFree_reverse hfree⟩

theorem invProgram_wellFormed : CircuitWellFormed invProgram := by
  obtain ⟨_, hwf, _, _⟩ := forward_facts
  rw [invProgram, circuitWellFormed_append, circuitWellFormed_append]
  exact ⟨⟨hwf, copyReg_wellFormed _ _ (reg_pair_nodup (by omega))⟩,
    Arithmetic.wellFormed_reverse hwf⟩

theorem invProgram_tCount_mulCost : tCount invProgram = 540 * mulCost := by
  obtain ⟨_, _, ht, _⟩ := forward_facts
  rw [invProgram, tCount_append, tCount_append, tCount_reverse, copyReg_tCount, ht]
  omega

theorem invProgram_tCount : tCount invProgram = 5492634840 := by
  rw [invProgram_tCount_mulCost, Secp256k1Instance.mulCost_eq]



theorem bennett_mid (compute middle : Circuit) (active : List Wire) (st : BasisState)
    (huses : CircuitUsesOnly active compute) (hfree : Classical.HPFree compute)
    (hwf : CircuitWellFormed compute)
    (hmid : ∀ w ∈ active,
      Classical.run middle (Classical.run compute st) w = Classical.run compute st w) :
    AgreesOn active st (Classical.run (compute ++ middle ++ compute.reverse) st) ∧
      ∀ w, w ∉ active →
        Classical.run (compute ++ middle ++ compute.reverse) st w =
          Classical.run middle (Classical.run compute st) w := by
  have hrun : Classical.run (compute ++ middle ++ compute.reverse) st =
      Classical.run compute.reverse (Classical.run middle (Classical.run compute st)) := by
    simp only [Classical.run_append]
  rw [hrun]
  have hcancel : Classical.run compute.reverse (Classical.run compute st) = st :=
    run_reverse_cancel compute st hfree hwf
  refine ⟨fun w hw => ?_, fun w hw => (usesOnly_reverse huses).preservesOutside _ w hw⟩
  calc
    Classical.run compute.reverse (Classical.run middle (Classical.run compute st)) w =
        Classical.run compute.reverse (Classical.run compute st) w :=
      CircuitUsesOnly.run_congr (usesOnly_reverse huses) hmid w hw
    _ = st w := by rw [hcancel]

def chainFused : List (Nat × Nat) := chain.dropLast

theorem chainFused_length : chainFused.length = 269 := by decide +kernel

theorem chainFused_valid : validB 1 chainFused = true := by decide +kernel

theorem chainFused_exp0 : (expsAux [1] chainFused).getD 0 0 = 1 := by decide +kernel

theorem chainFused_exp : (expsAux [1] chainFused).getD 269 0 + 1 = p - 2 := by decide +kernel

def outFused : List Wire := (reg 270).wires

def historyFused : List Wire := blocksWires ((List.range' 1 269).map regBlock)

def workFused : List Wire := historyFused ++ (reg 272).wires ++ mulW

def allBlocksFused : List Block :=
  [regBlock 0, regBlock 270] ++ (List.range' 1 269).map regBlock ++ [regBlock 272] ++
    mulWorkBlocks 273 274

theorem allFused_eq_blocksWires :
    base ++ outFused ++ workFused = blocksWires allBlocksFused := by
  rw [base, outFused, workFused, historyFused, mulW, Secp256k1Instance.mulWork_eq_blocksWires,
    allBlocksFused]
  simp only [blocksWires, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.append_assoc, Secp256k1Instance.reg_wires]

theorem allBlocksFused_ids :
    allBlocksFused.map Block.id =
      [0, 270] ++ List.range' 1 269 ++ [272] ++ [276, 273, 274, 275, 277] := by
  simp [allBlocksFused, Secp256k1Instance.mulWorkBlocks_ids, List.map_map, Function.comp_def]

theorem allBlocksFused_ids_nodup : (allBlocksFused.map Block.id).Nodup := by
  rw [allBlocksFused_ids]
  refine List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨List.nodup_append.mpr
    ⟨by decide, List.nodup_range', ?_⟩, by decide, ?_⟩, by decide, ?_⟩
  · intro a ha b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1] at ha hb
    omega
  · intro a ha b hb
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_range'_1] at ha hb
    omega
  · intro a ha b hb
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_range'_1] at ha hb
    omega

theorem allFused_nodup : (base ++ outFused ++ workFused).Nodup := by
  rw [allFused_eq_blocksWires]
  exact Secp256k1Instance.blocksWires_nodup _ allBlocksFused_ids_nodup

theorem allFused_lt : ∀ w ∈ base ++ outFused ++ workFused, w < 257 * 278 := by
  intro w hw
  rw [allFused_eq_blocksWires, blocksWires, List.mem_flatMap] at hw
  obtain ⟨b, hb, hwb⟩ := hw
  have hid : b.id < 278 := by
    have hmem : b.id ∈ allBlocksFused.map Block.id := List.mem_map_of_mem hb
    rw [allBlocksFused_ids] at hmem
    simp only [List.mem_cons, List.not_mem_nil, List.mem_append, List.mem_range'_1,
      or_false] at hmem
    omega
  have hbound : w < 257 * (b.id + 1) := (Secp256k1Instance.Block.mem_bounds hwb).2
  have hle : 257 * (b.id + 1) ≤ 257 * 278 := Nat.mul_le_mul_left _ (by omega)
  exact Nat.lt_of_lt_of_le hbound hle

theorem outFused_length : outFused.length = 257 := (reg 270).length_eq

theorem workFused_length : workFused.length = 69907 := by
  rw [workFused, historyFused, List.length_append, List.length_append, mulW_length,
    blocksWires_map_regBlock_length, List.length_range', (reg 272).length_eq]
  rfl

theorem reg_mem_workFused {m : Nat} (h1 : 1 ≤ m) (h2 : m ≤ 269) :
    ∀ w ∈ (reg m).wires, w ∈ workFused := by
  intro w hw
  show w ∈ historyFused ++ (reg 272).wires ++ mulW
  apply List.mem_append_left
  apply List.mem_append_left
  rw [historyFused, blocksWires, List.mem_flatMap]
  exact ⟨regBlock m, List.mem_map_of_mem (List.mem_range'_1.mpr ⟨h1, by omega⟩), hw⟩

theorem dup_mem_workFused : ∀ w ∈ (reg 272).wires, w ∈ workFused := fun _ hw =>
  List.mem_append_left _ (List.mem_append_right _ hw)

theorem mulW_mem_workFused : ∀ w ∈ mulW, w ∈ workFused := fun _ hw =>
  List.mem_append_right _ hw

theorem reg_mem_activeFused {m : Nat} (hm : m ≤ 269) :
    ∀ w ∈ (reg m).wires, w ∈ base ++ workFused := by
  intro w hw
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · exact List.mem_append_left _ hw
  · exact List.mem_append_right _ (reg_mem_workFused hpos hm w hw)

theorem activeFused_out_disjoint : ∀ x ∈ base ++ workFused, x ∉ outFused := by
  obtain ⟨hbo, _, hcross⟩ := List.nodup_append.mp allFused_nodup
  obtain ⟨_, _, hcross2⟩ := List.nodup_append.mp hbo
  intro x hx hy
  rcases List.mem_append.mp hx with hx | hx
  · exact hcross2 x hx x hy rfl
  · exact hcross x (List.mem_append_right _ hy) x hx rfl

def forwardFused : Circuit := chainCircuit 1 chainFused

def lastStep : Circuit := stepCircuit 269 0 270

def invProgramFused : Circuit := forwardFused ++ lastStep ++ forwardFused.reverse

theorem forwardFused_facts :
    Classical.HPFree forwardFused ∧ CircuitWellFormed forwardFused ∧
      tCount forwardFused = 269 * mulCost ∧ CircuitUsesOnly (base ++ workFused) forwardFused := by
  obtain ⟨h1, h2, h3, h4⟩ := chain_facts 269 (by omega) chainFused 1 chainFused_valid
    (by have := chainFused_length; omega)
  refine ⟨h1, h2, ?_, h4 _ (fun m hm => reg_mem_activeFused hm)
    (fun w hw => List.mem_append_right _ (dup_mem_workFused w hw))
    (fun w hw => List.mem_append_right _ (mulW_mem_workFused w hw))⟩
  rw [forwardFused, h3, chainFused_length]

theorem invProgramFused_correct (st : BasisState) (hbase : regValue base st < p)
    (hclean : Clean (outFused ++ workFused) st) :
    let after := Classical.run invProgramFused st
    AgreesOn base st after ∧ regValue outFused after = regValue base st ^ (p - 2) % p ∧
      Clean workFused after := by
  obtain ⟨hfree, hwf, _, huses⟩ := forwardFused_facts
  have hcleanOut : Clean outFused st := fun w hw => hclean w (List.mem_append_left _ hw)
  have hcleanWork : Clean workFused st := fun w hw => hclean w (List.mem_append_right _ hw)
  have hpos : 0 < p := Secp256k1Instance.p_pos
  let x := regValue base st
  have hinv0 : Inv 270 x ([1] : List Nat) st := by
    refine ⟨?_, ?_, fun w hw => hcleanWork w (dup_mem_workFused w hw),
      fun w hw => hcleanWork w (mulW_mem_workFused w hw)⟩
    · intro m hm
      simp only [List.length_singleton, Nat.lt_one_iff] at hm
      subst hm
      rw [List.getD_cons_zero, pow_one, Nat.mod_eq_of_lt hbase]
      rfl
    · intro m hm hmL w hw
      simp only [List.length_singleton] at hm
      rcases Nat.lt_or_ge m 270 with hlt | hge
      · exact hcleanWork w (reg_mem_workFused hm (by omega) w hw)
      · obtain rfl : m = 270 := by omega
        exact hcleanOut w hw
  have hmidInv := chain_correct 270 x (by omega) chainFused ([1] : List Nat) st
    chainFused_valid (by have := chainFused_length; simp only [List.length_singleton]; omega)
    hinv0
  obtain ⟨hval, hcleanReg, hdup, hwork⟩ := hmidInv
  have hlen : (expsAux ([1] : List Nat) chainFused).length = 270 := by
    rw [expsAux_length, chainFused_length]
    rfl
  let mid := Classical.run forwardFused st
  have h269 : regValue (reg 269).wires mid = x ^ (expsAux [1] chainFused).getD 269 0 % p :=
    hval 269 (by omega)
  have h0 : regValue (reg 0).wires mid = x ^ 1 % p := by
    rw [← chainFused_exp0]
    exact hval 0 (by omega)
  obtain ⟨hC, hW, hF⟩ := step_spec 269 0 270 (by omega) (by omega) (by omega) (by omega)
    (by omega) mid (by rw [h269]; exact Nat.mod_lt _ hpos) (by rw [h0]; exact Nat.mod_lt _ hpos)
    (hcleanReg 270 (by omega) le_rfl) hdup hwork
  have hmid : ∀ w ∈ base ++ workFused,
      Classical.run lastStep mid w = mid w := by
    intro w hw
    by_cases hwW : w ∈ mulW
    · exact (hW w hwW).trans (hwork w hwW).symm
    · exact hF w (activeFused_out_disjoint w hw) hwW
  obtain ⟨hagree, hout⟩ := bennett_mid forwardFused lastStep (base ++ workFused) st huses
    hfree hwf hmid
  have hagree' : AgreesOn (base ++ workFused) st (Classical.run invProgramFused st) := hagree
  have hval' : regValue outFused (Classical.run invProgramFused st) =
      regValue (reg 270).wires (Classical.run lastStep mid) :=
    regValue_congr _ _ _ (fun w hw => hout w (fun ha => activeFused_out_disjoint w ha hw))
  have hfinal : regValue (reg 270).wires (Classical.run lastStep mid) = x ^ (p - 2) % p := by
    rw [lastStep, hC, h269, h0, ← pow_add_mod, chainFused_exp]
  refine ⟨fun w hw => hagree' w (List.mem_append_left _ hw), hval'.trans hfinal,
    fun w hw => ?_⟩
  rw [hagree' w (List.mem_append_right _ hw)]
  exact hcleanWork w hw

theorem lastStep_facts :
    Classical.HPFree lastStep ∧ CircuitWellFormed lastStep ∧ tCount lastStep = mulCost ∧
      CircuitUsesOnly (base ++ outFused ++ workFused) lastStep := by
  obtain ⟨h1, h2, h3, h4⟩ := step_facts 269 0 270 (by omega) (by omega) (by omega) (by omega)
    (by omega)
  refine ⟨h1, h2, h3, h4 _ ?_ ?_ ?_ ?_ ?_⟩
  · intro w hw
    exact List.mem_append_right _ (reg_mem_workFused (by omega) le_rfl w hw)
  · intro w hw
    exact List.mem_append_left _ (List.mem_append_left _ hw)
  · intro w hw
    exact List.mem_append_left _ (List.mem_append_right _ hw)
  · intro w hw
    exact List.mem_append_right _ (dup_mem_workFused w hw)
  · intro w hw
    exact List.mem_append_right _ (mulW_mem_workFused w hw)

theorem invProgramFused_usesOnly :
    CircuitUsesOnly (base ++ outFused ++ workFused) invProgramFused := by
  obtain ⟨_, _, _, huses⟩ := forwardFused_facts
  have hf : CircuitUsesOnly (base ++ outFused ++ workFused) forwardFused :=
    usesOnly_mono huses (by
      intro w hw
      rcases List.mem_append.mp hw with h | h
      · exact List.mem_append_left _ (List.mem_append_left _ h)
      · exact List.mem_append_right _ h)
  exact usesOnly_append (usesOnly_append hf lastStep_facts.2.2.2) (usesOnly_reverse hf)

theorem invProgramFused_HPFree : Classical.HPFree invProgramFused := by
  obtain ⟨hfree, _, _, _⟩ := forwardFused_facts
  rw [invProgramFused, Classical.hpFree_append, Classical.hpFree_append]
  exact ⟨⟨hfree, lastStep_facts.1⟩, Arithmetic.hpFree_reverse hfree⟩

theorem invProgramFused_wellFormed : CircuitWellFormed invProgramFused := by
  obtain ⟨_, hwf, _, _⟩ := forwardFused_facts
  rw [invProgramFused, circuitWellFormed_append, circuitWellFormed_append]
  exact ⟨⟨hwf, lastStep_facts.2.1⟩, Arithmetic.wellFormed_reverse hwf⟩

theorem invProgramFused_tCount_mulCost : tCount invProgramFused = 539 * mulCost := by
  obtain ⟨_, _, ht, _⟩ := forwardFused_facts
  rw [invProgramFused, tCount_append, tCount_append, tCount_reverse, ht, lastStep_facts.2.2.1]
  omega

theorem invProgramFused_tCount : tCount invProgramFused = 5482463294 := by
  rw [invProgramFused_tCount_mulCost, Secp256k1Instance.mulCost_eq]



def invLayout : RegisterLayout :=
  { lhs := base, rhs := (reg 271).wires, out := outFused, work := workFused }

def layoutBlocks : List Block :=
  [regBlock 0, regBlock 271, regBlock 270] ++ (List.range' 1 269).map regBlock ++
    [regBlock 272] ++ mulWorkBlocks 273 274

theorem invLayout_allWires_eq : invLayout.allWires = blocksWires layoutBlocks := by
  rw [RegisterLayout.allWires, invLayout, base, outFused, workFused, historyFused, mulW,
    Secp256k1Instance.mulWork_eq_blocksWires, layoutBlocks]
  simp only [blocksWires, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.append_assoc, Secp256k1Instance.reg_wires]

theorem layoutBlocks_ids :
    layoutBlocks.map Block.id =
      [0, 271, 270] ++ List.range' 1 269 ++ [272] ++ [276, 273, 274, 275, 277] := by
  simp [layoutBlocks, Secp256k1Instance.mulWorkBlocks_ids, List.map_map, Function.comp_def]

theorem layoutBlocks_ids_nodup : (layoutBlocks.map Block.id).Nodup := by
  rw [layoutBlocks_ids]
  refine List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨List.nodup_append.mpr
    ⟨by decide, List.nodup_range', ?_⟩, by decide, ?_⟩, by decide, ?_⟩
  · intro a ha b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1] at ha hb
    omega
  · intro a ha b hb
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_range'_1] at ha hb
    omega
  · intro a ha b hb
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_range'_1] at ha hb
    omega

theorem invLayout_valid : invLayout.Valid := by
  refine ⟨(reg 0).length_eq.trans (reg 271).length_eq.symm,
    (reg 0).length_eq.trans (reg 270).length_eq.symm, ?_⟩
  rw [invLayout_allWires_eq]
  exact Secp256k1Instance.blocksWires_nodup _ layoutBlocks_ids_nodup

theorem invLayout_allWires_lt : ∀ w ∈ invLayout.allWires, w < 257 * 278 := by
  intro w hw
  rw [invLayout_allWires_eq, blocksWires, List.mem_flatMap] at hw
  obtain ⟨b, hb, hwb⟩ := hw
  have hid : b.id < 278 := by
    have hmem : b.id ∈ layoutBlocks.map Block.id := List.mem_map_of_mem hb
    rw [layoutBlocks_ids] at hmem
    simp only [List.mem_cons, List.not_mem_nil, List.mem_append, List.mem_range'_1,
      or_false] at hmem
    omega
  have hbound : w < 257 * (b.id + 1) := (Secp256k1Instance.Block.mem_bounds hwb).2
  have hle : 257 * (b.id + 1) ≤ 257 * 278 := Nat.mul_le_mul_left _ (by omega)
  exact Nat.lt_of_lt_of_le hbound hle

theorem rhs_not_mem_fusedSupport : ∀ w ∈ (reg 271).wires, w ∉ base ++ outFused ++ workFused := by
  have hnd := invLayout_valid.2.2
  rw [RegisterLayout.allWires] at hnd
  intro w hw hmem
  obtain ⟨hfront, _, hcross⟩ := List.nodup_append.mp
    (show (base ++ (reg 271).wires ++ outFused ++ workFused).Nodup from hnd)
  obtain ⟨hbr, _, hcross2⟩ := List.nodup_append.mp hfront
  obtain ⟨_, _, hcross3⟩ := List.nodup_append.mp hbr
  rcases List.mem_append.mp hmem with h | h
  · rcases List.mem_append.mp h with h | h
    · exact hcross3 w h w hw rfl
    · exact hcross2 w (List.mem_append_right _ hw) w h rfl
  · exact hcross w (List.mem_append_left _ (List.mem_append_right _ hw)) w h rfl

theorem inv_contract :
    CleanBinaryContract invProgramFused invLayout ShorECDLP.p
      (fun a _ => a ^ (ShorECDLP.p - 2)) 5482463294 where
  correct := by
    intro st _ hlhs _ hclean
    obtain ⟨hbase, hout, hwork⟩ := invProgramFused_correct st hlhs hclean
    refine ⟨hbase, fun w hw => ?_, hout, hwork⟩
    exact invProgramFused_usesOnly.preservesOutside st w (rhs_not_mem_fusedSupport w hw)
  usesOnly := by
    apply usesOnly_mono invProgramFused_usesOnly
    intro w hw
    simp only [invLayout, RegisterLayout.allWires, List.mem_append] at hw ⊢
    rcases hw with (h | h) | h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  counted := invProgramFused_tCount
  hpFree := invProgramFused_HPFree
  wellFormed := fun _ => invProgramFused_wellFormed


theorem step_length_le (a b c : Nat) : (stepCircuit a b c).length ≤ 4037727 := by
  have hmul := NaiveChallenge.secpMulProgram_length_le
  rw [stepCircuit]
  split
  · have hcopy := NaiveChallenge.copyReg_length_le (reg a).wires (reg 272).wires
    rw [(reg a).length_eq] at hcopy
    have hm := hmul a 272 c 273 274
    simp only [List.length_append, List.length_reverse]
    change _ ≤ 257 at hcopy
    omega
  · exact (hmul a b c 273 274).trans (by norm_num)

theorem chainCircuit_length_le :
    ∀ (steps : List (Nat × Nat)) (k : Nat),
      (chainCircuit k steps).length ≤ steps.length * 4037727
  | [], _ => by simp [chainCircuit]
  | (i, j) :: rest, k => by
      have h1 := step_length_le i j k
      have h2 := chainCircuit_length_le rest (k + 1)
      rw [chainCircuit, List.length_append, List.length_cons]
      omega

theorem invProgramFused_length_le : invProgramFused.length ≤ 2176334853 := by
  have hf : forwardFused.length ≤ 269 * 4037727 := by
    have h := chainCircuit_length_le chainFused 1
    rw [chainFused_length] at h
    exact h
  have hl : lastStep.length ≤ 4037727 := step_length_le 269 0 270
  rw [invProgramFused, List.length_append, List.length_append, List.length_reverse]
  change forwardFused.length + lastStep.length + forwardFused.length ≤ 2176334853
  omega

theorem invProgram_length_le : invProgram.length ≤ 2180372837 := by
  have hf : forward.length ≤ 270 * 4037727 := by
    have h := chainCircuit_length_le chain 1
    rw [chain_length] at h
    exact h
  have hc := NaiveChallenge.copyReg_length_le (reg 270).wires out
  rw [(reg 270).length_eq] at hc
  change _ ≤ 257 at hc
  rw [invProgram, List.length_append, List.length_append, List.length_reverse]
  omega

end InvChain
end V2
end Secp256k1
end ShorECDLP
