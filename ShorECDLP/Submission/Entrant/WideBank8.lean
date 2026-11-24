import ShorECDLP.Submission.Entrant.Prefix

/-! ### Consolidated from `ParityBank.lean` -/
section
/-! Parity-derived one-hot preparation, following the construction described in public Yukon submission 614eec20-ddf3-45e9-9fc1-e733b9dc098e. The proof below derives each level from the inherited level_partial invariant. -/
namespace ShorECDLP.Entrant.ParityBank
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration MeasuredClear
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

def xorScan (hotN : Nat → Wire) (offset : Nat) (target : Wire) : Nat → Circuit
  | 0 => []
  | m+1 => xorScan hotN offset target m ++ [.CX (hotN (m+offset)) target]

theorem xorScan_frame (hotN : Nat → Wire) (offset : Nat) (target w : Wire) (m : Nat)
    (s : BasisState) (hw : w≠target) :
    Classical.run (xorScan hotN offset target m) s w=s w := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [xorScan,Classical.run_append]
    simpa [Classical.run,Classical.applyGate,upd,hw] using ih

theorem cx_target (c t : Wire) (s : BasisState) :
    Classical.run [.CX c t] s t=Bool.xor (s t) (s c) := by
  simp [Classical.run,Classical.applyGate,upd]

theorem xorScan_value (hotN : Nat → Wire) (offset : Nat) (target : Wire)
    (m a : Nat) (b : Bool) (s : BasisState)
    (hd : ∀ i,i<m → hotN (i+offset)≠target)
    (hv : ∀ i,i<m → s (hotN (i+offset))=(decide (i=a) && b)) :
    Classical.run (xorScan hotN offset target m) s target =
      Bool.xor (s target) (decide (a<m) && b) := by
  induction m with
  | zero => simp [xorScan,Classical.run]
  | succ m ih =>
    have hi := ih (fun i h => hd i (by omega)) (fun i h => hv i (by omega))
    have hc := xorScan_frame hotN offset target (hotN (m+offset)) m s (hd m (by omega))
    rw [xorScan,Classical.run_append]
    rw [cx_target,hi,hc,hv m (by omega)]
    by_cases ha : a<m
    · have hm : m≠a := by omega
      have ha' : a<m+1 := by omega
      simp [ha,hm,ha']
    · by_cases hm : m=a
      · have ha' : a<m+1 := by omega
        simp [ha,hm,ha']
      · have ha' : ¬a<m+1 := by omega
        simp [ha,hm,ha']

theorem xorScan_tCount (hotN : Nat → Wire) (offset : Nat) (target : Wire) (m : Nat) :
    ShorECDLP.tCount (xorScan hotN offset target m)=0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [xorScan,ShorECDLP.tCount_append,ih]
    simp [ShorECDLP.tCount,ShorECDLP.tCost]

theorem xorScan_length (hotN : Nat → Wire) (offset : Nat) (target : Wire) (m : Nat) :
    (xorScan hotN offset target m).length=m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [xorScan,ih]


def prefixCells (bitsN hotN : Nat → Wire) (j : Nat) : List SplitCell :=
  (List.range (2^j-1)).map fun i => ⟨bitsN j,hotN i,hotN (i+2^j)⟩

def parityLevel (bitsN hotN : Nat → Wire) (j : Nat) : Circuit :=
  splitNetwork (prefixCells bitsN hotN j) ++
    [.CX (bitsN j) (hotN ((2^j-1)+2^j))] ++
    xorScan hotN (2^j) (hotN ((2^j-1)+2^j)) (2^j-1) ++
    [.CX (hotN ((2^j-1)+2^j)) (hotN (2^j-1))]

theorem old_level_last (bitsN hotN : Nat → Wire) (j : Nat) :
    splitNetwork (hotLevelN bitsN hotN j) = splitNetwork (prefixCells bitsN hotN j) ++
      [Gate.CCX (bitsN j) (hotN (2^j-1)) (hotN ((2^j-1)+2^j)),
       Gate.CX (hotN ((2^j-1)+2^j)) (hotN (2^j-1))] := by
  have hp : 0<(2:Nat)^j := by positivity
  have he : 2^j=(2^j-1)+1 := by omega
  unfold hotLevelN
  conv_lhs => rw [he,List.range_succ,List.map_append,splitNetwork_append]
  simp only [List.map_cons,List.map_nil,splitNetwork,List.append_nil,←he]
  rfl

theorem parityLevel_eq (b : Nat) (bitsN hotN : Nat → Wire) (hL : HotLayout b bitsN hotN)
    (j : Nat) (hj : j<b) (a : Nat) (ha : a<2^j) (t : BasisState)
    (ht : ∀ x,x<2^b → t (hotN x)=decide (x=a)) :
    Classical.run (parityLevel bitsN hotN j) t = Classical.run (splitNetwork (hotLevelN bitsN hotN j)) t := by
  have hp : 0<(2:Nat)^j := by positivity
  let m := 2^j-1
  have hm : m<2^j := by dsimp [m]; omega
  have hm' : m+1=2^j := by dsimp [m]; omega
  have hmb : m<2^b := by have := pow_level_lt hj m hm; omega
  have hcb : m+2^j<2^b := pow_level_lt hj m hm
  let target := hotN (m+2^j)
  let parent := hotN m
  let bit := bitsN j
  let u := Classical.run (splitNetwork (prefixCells bitsN hotN j)) t
  let v := Classical.run [.CX bit target] u
  let q := Classical.run (xorScan hotN (2^j) target m) v
  let z := Classical.run [.CCX bit parent target] u
  have hpart := level_partial b bitsN hotN hL j hj a ha t ht m (by omega)
  change (∀ x,x<2^b → u (hotN x)=_) ∧ _ at hpart
  have hubit : u bit=t bit := hpart.2.1 bit (fun x hx => hL.disj j x hj hx)
  have huparent : u parent=decide (m=a) := by
    have h := hpart.1 m hmb
    simpa only [if_neg (show ¬m<m by omega),if_neg (show ¬(2^j≤m ∧ m<2^j+m) by omega)] using h
  have hutarget : u target=false := by
    have h := hpart.1 (m+2^j) hcb
    have h0 : ¬m+2^j<m := by omega
    have h1 : ¬(2^j≤m+2^j ∧ m+2^j<2^j+m) := by omega
    have h2 : ¬m+2^j=a := by omega
    simpa only [if_neg h0,if_neg h1,decide_eq_false h2] using h
  have hparentne : parent≠target := by
    intro he
    have h := hL.inj m (m+2^j) hmb hcb he
    omega
  have hctrl (i : Nat) (hi : i<m) : hotN (i+2^j)≠target := by
    intro he
    have hib := pow_level_lt hj i (by omega : i<2^j)
    have h := hL.inj (i+2^j) (m+2^j) hib hcb he
    omega
  have hchildren (i : Nat) (hi : i<m) : v (hotN (i+2^j))=(decide (i=a) && t bit) := by
    have hib := pow_level_lt hj i (by omega : i<2^j)
    have h := hpart.1 (i+2^j) hib
    have h0 : ¬i+2^j<m := by omega
    have h1 : 2^j ≤ i+2^j ∧ i+2^j<2^j+m := by omega
    have hsub : i+2^j-2^j=i := by omega
    rw [if_neg h0,if_pos h1,hsub] at h
    have he : v (hotN (i+2^j))=u (hotN (i+2^j)) := by
      simp [v,Classical.run,Classical.applyGate,upd,hctrl i hi]
    exact he.trans h
  have hvtarget : v target=t bit := by
    change Classical.run [.CX bit target] u target=t bit
    simp [cx_target,hubit,hutarget]
  have hqtarget : q target=(t bit && decide (m=a)) := by
    have h := xorScan_value hotN (2^j) target m a (t bit) v hctrl hchildren
    change q target=_ at h
    rw [hvtarget] at h
    rw [h]
    by_cases he : m=a
    · have hnot : ¬a<m := by omega
      simp [he,hnot]
    · have hlt : a<m := by omega
      simp [he,hlt]
  have hqz : q=z := by
    funext w
    by_cases hw : w=target
    · subst w
      rw [hqtarget]
      have hz : z target=Bool.xor (u target) (u bit && u parent) := by
        simp [z,Classical.run,Classical.applyGate,upd]
      rw [hz,hutarget,hubit,huparent]
      simp
    · have hq : q w=v w := xorScan_frame hotN (2^j) target w m v hw
      rw [hq]
      simp [v,z,Classical.run,Classical.applyGate,upd,hw]
  have hn : Classical.run (parityLevel bitsN hotN j) t=Classical.run [.CX target parent] q := by
    simp only [parityLevel,Classical.run_append]
    rfl
  have ho : Classical.run (splitNetwork (hotLevelN bitsN hotN j)) t=Classical.run [.CX target parent] z := by
    rw [old_level_last,Classical.run_append]
    rfl
  rw [hn,ho,hqz]


def parityNet (bitsN hotN : Nat → Wire) : Nat → Circuit
  | 0 => []
  | J+1 => parityNet bitsN hotN J ++ parityLevel bitsN hotN J

theorem parityNet_eq (b : Nat) (bitsN hotN : Nat → Wire) (hL : HotLayout b bitsN hotN)
    (t : BasisState) (ht : ∀ x,x<2^b → t (hotN x)=decide (x=0)) :
    ∀ J,J≤b → Classical.run (parityNet bitsN hotN J) t=Classical.run (splitNetwork (hotNetN bitsN hotN J)) t := by
  intro J
  induction J with
  | zero => intro _; rfl
  | succ J ih =>
    intro hJ
    have hi := ih (by omega)
    rw [parityNet,Classical.run_append,hi,hotNetN,splitNetwork_append,Classical.run_append]
    exact parityLevel_eq b bitsN hotN hL J (by omega) (addrN bitsN t J) (addrN_lt bitsN t J)
      _ (net_run b bitsN hotN hL t ht J (by omega)).1

theorem parityLevel_tCount (bitsN hotN : Nat → Wire) (j : Nat) :
    ShorECDLP.tCount (parityLevel bitsN hotN j)=7*(2^j-1) := by
  simp only [parityLevel,ShorECDLP.tCount_append,splitNetwork_tCount,prefixCells,
    List.length_map,List.length_range,xorScan_tCount]
  simp [ShorECDLP.tCount,ShorECDLP.tCost]

theorem parityLevel_length (bitsN hotN : Nat → Wire) (j : Nat) :
    (parityLevel bitsN hotN j).length=3*(2^j-1)+2 := by
  simp only [parityLevel,List.length_append,splitNetwork_length,prefixCells,
    List.length_map,List.length_range,xorScan_length,List.length_cons,List.length_nil]
  omega

theorem parityNet_tCount (bitsN hotN : Nat → Wire) (J : Nat) :
    ShorECDLP.tCount (parityNet bitsN hotN J)+7*J+7=7*2^J := by
  induction J with
  | zero => rfl
  | succ J ih =>
    rw [parityNet,ShorECDLP.tCount_append,parityLevel_tCount,pow_succ]
    have hp : 0<(2:Nat)^J := by positivity
    omega

theorem parityNet_length (bitsN hotN : Nat → Wire) (J : Nat) :
    (parityNet bitsN hotN J).length+J+3=3*2^J := by
  induction J with
  | zero => rfl
  | succ J ih =>
    rw [parityNet,List.length_append,parityLevel_length,pow_succ]
    have hp : 0<(2:Nat)^J := by positivity
    omega

theorem xorScan_hp (hotN : Nat → Wire) (offset : Nat) (target : Wire) (m : Nat) :
    Classical.HPFree (xorScan hotN offset target m) := by
  induction m with
  | zero => simp [xorScan]
  | succ m ih => simp [xorScan,ih]

theorem parityLevel_hp (bitsN hotN : Nat → Wire) (j : Nat) : Classical.HPFree (parityLevel bitsN hotN j) := by
  simp [parityLevel,splitNetwork_hp,xorScan_hp]

theorem parityNet_hp (bitsN hotN : Nat → Wire) (J : Nat) : Classical.HPFree (parityNet bitsN hotN J) := by
  induction J with
  | zero => simp [parityNet]
  | succ J ih => simp [parityNet,ih,parityLevel_hp]

theorem cx_frame (c target w : Wire) (s : BasisState) (hw : w≠target) :
    Classical.run [.CX c target] s w=s w := by
  simp [Classical.run,Classical.applyGate,upd,hw]

theorem parityLevel_frame (b : Nat) (bitsN hotN : Nat → Wire) (j : Nat) (hj : j<b)
    (s : BasisState) (w : Wire) (hw : ∀ x,x<2^b → w≠hotN x) :
    Classical.run (parityLevel bitsN hotN j) s w=s w := by
  have hp : 0<(2:Nat)^j := by positivity
  have hm : 2^j-1<2^j := by omega
  have hchild := pow_level_lt hj (2^j-1) hm
  have hparent : 2^j-1<2^b := by omega
  simp only [parityLevel,Classical.run_append]
  rw [cx_frame _ _ _ _ (hw _ hparent),xorScan_frame _ _ _ _ _ _ (hw _ hchild),cx_frame _ _ _ _ (hw _ hchild)]
  apply splitNetwork_frame
  intro c hc
  simp only [prefixCells,List.mem_map,List.mem_range] at hc
  obtain ⟨i,hi,rfl⟩ := hc
  have hic := pow_level_lt hj i (by omega : i<2^j)
  have hip : i<2^b := by omega
  exact ⟨hw i hip,hw (i+2^j) hic⟩

theorem parityNet_frame (b : Nat) (bitsN hotN : Nat → Wire) (J : Nat) (hJ : J≤b)
    (s : BasisState) (w : Wire) (hw : ∀ x,x<2^b → w≠hotN x) :
    Classical.run (parityNet bitsN hotN J) s w=s w := by
  induction J with
  | zero => rfl
  | succ J ih =>
    rw [parityNet,Classical.run_append,parityLevel_frame b bitsN hotN J (by omega) _ w hw]
    exact ih (by omega)


theorem xorScan_wellFormed (hotN : Nat → Wire) (offset : Nat) (target : Wire) (m : Nat)
    (hd : ∀ i,i<m → hotN (i+offset)≠target) : CircuitWellFormed (xorScan hotN offset target m) := by
  induction m with
  | zero => simp [xorScan,CircuitWellFormed]
  | succ m ih =>
    rw [xorScan,circuitWellFormed_append]
    exact ⟨ih (fun i hi => hd i (by omega)),by simp [CircuitWellFormed,Gate.WellFormed,hd m (by omega)]⟩

theorem parityLevel_wellFormed (b : Nat) (bitsN hotN : Nat → Wire) (hL : HotLayout b bitsN hotN)
    (j : Nat) (hj : j<b) : CircuitWellFormed (parityLevel bitsN hotN j) := by
  have hp : 0<(2:Nat)^j := by positivity
  let m := 2^j-1
  have hm : m<2^j := by dsimp [m]; omega
  have hchild := pow_level_lt hj m hm
  have hparent : m<2^b := by omega
  have hprefix : ∀ c∈prefixCells bitsN hotN j,c.Physical := by
    intro c hc
    simp only [prefixCells,List.mem_map,List.mem_range] at hc
    obtain ⟨i,hi,rfl⟩ := hc
    have hic := pow_level_lt hj i (by omega : i<2^j)
    have hip : i<2^b := by omega
    exact ⟨hL.disj j i hj hip,hL.disj j (i+2^j) hj hic,fun he => by
      have h := hL.inj i (i+2^j) hip hic he
      omega⟩
  have hpc : hotN m≠hotN (m+2^j) := by
    intro he
    have h := hL.inj m (m+2^j) hparent hchild he
    omega
  have hxor : ∀ i,i<m → hotN (i+2^j)≠hotN (m+2^j) := by
    intro i hi he
    have hic := pow_level_lt hj i (by omega : i<2^j)
    have h := hL.inj (i+2^j) (m+2^j) hic hchild he
    omega
  simp only [parityLevel,circuitWellFormed_append]
  exact ⟨⟨⟨splitNetwork_wellFormed _ hprefix,
    by simpa [CircuitWellFormed,Gate.WellFormed] using hL.disj j (m+2^j) hj hchild⟩,
    xorScan_wellFormed hotN (2^j) (hotN (m+2^j)) m hxor⟩,
    by simpa [CircuitWellFormed,Gate.WellFormed] using Ne.symm hpc⟩

theorem parityNet_wellFormed (b : Nat) (bitsN hotN : Nat → Wire) (hL : HotLayout b bitsN hotN)
    (J : Nat) (hJ : J≤b) : CircuitWellFormed (parityNet bitsN hotN J) := by
  induction J with
  | zero => simp [parityNet,CircuitWellFormed]
  | succ J ih =>
    rw [parityNet,circuitWellFormed_append]
    exact ⟨ih (by omega),parityLevel_wellFormed b bitsN hotN hL J (by omega)⟩

theorem cx_within (c target : Wire) (S : List Wire) (hc : c∈S) (ht : target∈S) :
    circuitWires [.CX c target] ⊆ S := by
  intro w hw
  simp [circuitWires,gateWires] at hw
  rcases hw with rfl | rfl
  · exact hc
  · exact ht

theorem xorScan_within (hotN : Nat → Wire) (offset : Nat) (target : Wire) (m : Nat) (S : List Wire)
    (hc : ∀ i,i<m → hotN (i+offset)∈S) (ht : target∈S) :
    circuitWires (xorScan hotN offset target m) ⊆ S := by
  induction m with
  | zero => simp [xorScan,circuitWires]
  | succ m ih =>
    rw [xorScan,circuitWires_append]
    exact List.append_subset.mpr ⟨ih (fun i hi => hc i (by omega)),cx_within _ _ S (hc m (by omega)) ht⟩

theorem parityLevel_within (b : Nat) (bitsN hotN : Nat → Wire) (j : Nat) (hj : j<b) (S : List Wire)
    (hb : ∀ i,i<b → bitsN i∈S) (hh : ∀ x,x<2^b → hotN x∈S) :
    circuitWires (parityLevel bitsN hotN j) ⊆ S := by
  have hp : 0<(2:Nat)^j := by positivity
  let m := 2^j-1
  have hm : m<2^j := by dsimp [m]; omega
  have hchild := pow_level_lt hj m hm
  have hparent : m<2^b := by omega
  have hprefix : circuitWires (splitNetwork (prefixCells bitsN hotN j)) ⊆ S := by
    apply splitNetwork_within
    intro c hc
    simp only [prefixCells,List.mem_map,List.mem_range] at hc
    obtain ⟨i,hi,rfl⟩ := hc
    have hic := pow_level_lt hj i (by omega : i<2^j)
    have hip : i<2^b := by omega
    exact ⟨hb j hj,hh i hip,hh (i+2^j) hic⟩
  simp only [parityLevel,circuitWires_append,List.append_subset]
  exact ⟨⟨⟨hprefix,cx_within _ _ S (hb j hj) (hh _ hchild)⟩,
    xorScan_within hotN (2^j) (hotN (m+2^j)) m S
      (fun i hi => hh _ (pow_level_lt hj i (by omega))) (hh _ hchild)⟩,
    cx_within _ _ S (hh _ hchild) (hh _ hparent)⟩

theorem parityNet_within (b : Nat) (bitsN hotN : Nat → Wire) (J : Nat) (hJ : J≤b) (S : List Wire)
    (hb : ∀ i,i<b → bitsN i∈S) (hh : ∀ x,x<2^b → hotN x∈S) :
    circuitWires (parityNet bitsN hotN J) ⊆ S := by
  induction J with
  | zero => simp [parityNet,circuitWires]
  | succ J ih =>
    rw [parityNet,circuitWires_append]
    exact List.append_subset.mpr ⟨ih (by omega),parityLevel_within b bitsN hotN J (by omega) S hb hh⟩

#print axioms parityNet_eq
#print axioms parityNet_wellFormed
#print axioms parityNet_within
end
end ShorECDLP.Entrant.ParityBank
end

/-! ### Consolidated from `Bank9.lean` -/
section
/-! Nine-bit instance of the recycled measured-clear bank.

The shipped `MeasuredClear` bank is instantiated at seven low address bits (128 unary wires,
127 split cells). For a measured clear over a `k`-bit address it costs
`(2^7 - 1) + (2^(k-7) - 1)` CCX. This file instantiates the same generic split network
(`hotNetN`, `net_run`, `HotLayout`) at nine low bits (512 unary wires, 511 cells), costing
`(2^9 - 2) + (2^(k-9) - 1)` CCX after specializing the known-one first split. Every declaration is the seven-bit one with the bank
width changed; the generic network, phase lookup and record machinery are shared. -/

namespace ShorECDLP.Entrant.MeasuredClear
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

/-- Replace the first split's known-one control by a Clifford copy. -/
def seededSplitNetwork : List SplitCell → Circuit
  | [] => []
  | c :: cs => [.CX c.bit c.child, .CX c.child c.parent] ++ splitNetwork cs

theorem seededSplitNetwork_run (c : SplitCell) (cs : List SplitCell) (s : BasisState)
    (hp : s c.parent = true) :
    Classical.run (seededSplitNetwork (c :: cs)) s =
      Classical.run (splitNetwork (c :: cs)) s := by
  simp only [seededSplitNetwork,splitNetwork,SplitCell.circuit,splitCircuit,Classical.run_append]
  congr 1
  funext w
  simp [Classical.run,Classical.applyGate,upd,hp]

theorem hotNetN_first (bitsN hotN : Nat → Wire) (j : Nat) :
    ∃ cs, hotNetN bitsN hotN (j+1) = ⟨bitsN 0,hotN 0,hotN 1⟩ :: cs := by
  induction j with
  | zero => exact ⟨[], by simp [hotNetN,hotLevelN]⟩
  | succ j ih =>
    obtain ⟨cs,he⟩ := ih
    exact ⟨cs ++ hotLevelN bitsN hotN (j+1), by rw [hotNetN,he,List.cons_append]⟩

theorem seededHotNet_run (bitsN hotN : Nat → Wire) (j : Nat) (s : BasisState)
    (hp : s (hotN 0) = true) :
    Classical.run (seededSplitNetwork (hotNetN bitsN hotN (j+1))) s =
    Classical.run (splitNetwork (hotNetN bitsN hotN (j+1))) s := by
  obtain ⟨cs,he⟩ := hotNetN_first bitsN hotN j
  rw [he]
  exact seededSplitNetwork_run _ _ _ hp

theorem seededSplitNetwork_hp (cs : List SplitCell) :
    Classical.HPFree (seededSplitNetwork cs) := by
  cases cs <;> simp [seededSplitNetwork,splitNetwork_hp]

theorem seededSplitNetwork_tCount (cs : List SplitCell) :
    ShorECDLP.tCount (seededSplitNetwork cs) = 7 * (cs.length-1) := by
  cases cs with
  | nil => rfl
  | cons c cs =>
    rw [seededSplitNetwork,ShorECDLP.tCount_append,splitNetwork_tCount]
    simp [ShorECDLP.tCount,ShorECDLP.tCost]

theorem seededSplitNetwork_length (cs : List SplitCell) :
    (seededSplitNetwork cs).length = 2 * cs.length := by
  cases cs with
  | nil => rfl
  | cons c cs =>
    simp only [seededSplitNetwork,List.length_append,List.length_cons,List.length_nil,splitNetwork_length]
    omega

theorem seededSplitNetwork_frame (cs : List SplitCell) (s : BasisState) (w : Wire)
    (hw : ∀ c ∈ cs, w ≠ c.parent ∧ w ≠ c.child) :
    Classical.run (seededSplitNetwork cs) s w = s w := by
  cases cs with
  | nil => rfl
  | cons c cs =>
    have hc := hw c (by simp)
    rw [seededSplitNetwork,Classical.run_append,
      splitNetwork_frame cs _ w (fun d hd => hw d (by simp [hd]))]
    simp [Classical.run,Classical.applyGate,upd,hc.1,hc.2]

theorem seededSplitNetwork_wellFormed (cs : List SplitCell)
    (hp : ∀ c ∈ cs, c.Physical) : CircuitWellFormed (seededSplitNetwork cs) := by
  cases cs with
  | nil => simp [seededSplitNetwork,CircuitWellFormed]
  | cons c cs =>
    have hc := hp c (by simp)
    rw [seededSplitNetwork,circuitWellFormed_append]
    exact ⟨by simp [CircuitWellFormed,Gate.WellFormed,hc.2.1,Ne.symm hc.2.2],
      splitNetwork_wellFormed cs (fun d hd => hp d (by simp [hd]))⟩

theorem seededSplitNetwork_within (cs : List SplitCell) (S : List Wire)
    (hp : ∀ c ∈ cs, c.bit ∈ S ∧ c.parent ∈ S ∧ c.child ∈ S) :
    circuitWires (seededSplitNetwork cs) ⊆ S := by
  cases cs with
  | nil => simp [seededSplitNetwork,circuitWires]
  | cons c cs =>
    have hc := hp c (by simp)
    rw [seededSplitNetwork,circuitWires_append]
    refine List.append_subset.mpr ⟨?_,splitNetwork_within cs S (fun d hd => hp d (by simp [hd]))⟩
    intro w hw
    simp [circuitWires,gateWires] at hw
    rcases hw with rfl | rfl | rfl
    · exact hc.1
    · exact hc.2.2
    · exact hc.2.1

/-- Nat-indexed views of the nine low address wires and the 512 unary wires. -/
def lowN9 (low : Fin 9 → Wire) (j : Nat) : Wire := if h : j < 9 then low ⟨j, h⟩ else low 0

def hotNat9 (hot : Fin 512 → Wire) (x : Nat) : Wire := if h : x < 512 then hot ⟨x, h⟩ else hot 0

/-- The low-address bank: nine address bits split into 512 unary wires. -/
def hotNetwork9 (low : Fin 9 → Wire) (hot : Fin 512 → Wire) : List SplitCell :=
  hotNetN (lowN9 low) (hotNat9 hot) 9

def slowHotPrepare9 (low : Fin 9 → Wire) (hot : Fin 512 → Wire) : Circuit :=
  [.X (hot 0)] ++ splitNetwork (hotNetwork9 low hot)

def hotPrepare9 (low : Fin 9 → Wire) (hot : Fin 512 → Wire) : Circuit :=
  [.X (hot 0)] ++ ParityBank.parityNet (lowN9 low) (hotNat9 hot) 9

def hotAddress9 (low : Fin 9 → Wire) (s : BasisState) : Nat := addrN (lowN9 low) s 9

def HotClean9 (hot : Fin 512 → Wire) (s : BasisState) : Prop := ∀ i, s (hot i) = false

theorem hotNetwork_length9 (low : Fin 9 → Wire) (hot : Fin 512 → Wire) :
    (hotNetwork9 low hot).length = 511 := by
  simp [hotNetwork9, hotNetN_length]

theorem hotLayout_of9 (low : Fin 9 → Wire) (hot : Fin 512 → Wire)
    (hi : Function.Injective hot) (hd : ∀ i j, low i ≠ hot j) :
    HotLayout 9 (lowN9 low) (hotNat9 hot) := by
  constructor
  · intro x y hx hy he
    have hx' : x < 512 := by simpa using hx
    have hy' : y < 512 := by simpa using hy
    simp only [hotNat9, hx', hy', dite_true] at he
    exact congrArg Fin.val (hi he)
  · intro j x hj hx
    have hx' : x < 512 := by simpa using hx
    simp only [lowN9, hotNat9, hj, hx', dite_true]
    exact hd _ _

theorem mem_hotNetwork9 (low : Fin 9 → Wire) (hot : Fin 512 → Wire) (c : SplitCell)
    (hc : c ∈ hotNetwork9 low hot) :
    ∃ j : Fin 9, ∃ x y : Fin 512, c = ⟨low j, hot x, hot y⟩ ∧ x ≠ y := by
  obtain ⟨j, i, hj, hi, rfl⟩ := mem_hotNetN _ _ 9 c hc
  have h2 : i + 2^j < 2^9 := pow_level_lt hj i hi
  have h2' : i + 2^j < 512 := by simpa using h2
  have h1 : i < 512 := by omega
  refine ⟨⟨j, hj⟩, ⟨i, h1⟩, ⟨i + 2^j, h2'⟩, ?_, ?_⟩
  · simp [lowN9, hotNat9, hj, h1, h2']
  · intro he
    have := congrArg Fin.val he
    have hp : 0 < 2^j := by positivity
    simp at this

theorem hotNetwork_physical9 (low : Fin 9 → Wire) (hot : Fin 512 → Wire)
    (hi : Function.Injective hot) (hd : ∀ i j, low i ≠ hot j) :
    ∀ c ∈ hotNetwork9 low hot, c.Physical := by
  intro c hc
  obtain ⟨j, x, y, rfl, hxy⟩ := mem_hotNetwork9 low hot c hc
  exact ⟨hd j x, hd j y, fun he => hxy (hi he)⟩

theorem hotStart9 (hot : Fin 512 → Wire) (hi : Function.Injective hot)
    (s : BasisState) (hs : HotClean9 hot s) :
    ∀ x, x < 2^9 → Classical.run [.X (hot 0)] s (hotNat9 hot x) = decide (x = 0) := by
  intro x hx
  have hx' : x < 512 := by simpa using hx
  simp only [hotNat9, hx', dite_true]
  by_cases h0 : x = 0
  · subst h0
    simp [Classical.run, Classical.applyGate, upd, hs 0]
  · have hne : hot ⟨x, hx'⟩ ≠ hot 0 := fun he => h0 (congrArg Fin.val (hi he))
    simp [Classical.run, Classical.applyGate, upd, hne, hs ⟨x, hx'⟩, h0]

theorem hotPrepare_eq9 (low : Fin 9 → Wire) (hot : Fin 512 → Wire)
    (hi : Function.Injective hot) (hd : ∀ i j,low i≠hot j)
    (s : BasisState) (hs : HotClean9 hot s) :
    Classical.run (hotPrepare9 low hot) s=Classical.run (slowHotPrepare9 low hot) s := by
  rw [hotPrepare9,slowHotPrepare9,Classical.run_append,Classical.run_append,hotNetwork9]
  exact ParityBank.parityNet_eq 9 (lowN9 low) (hotNat9 hot) (hotLayout_of9 low hot hi hd)
    _ (hotStart9 hot hi s hs) 9 le_rfl

theorem hotNetwork_ready9 (low : Fin 9 → Wire) (hot : Fin 512 → Wire)
    (hi : Function.Injective hot) (hd : ∀ i j, low i ≠ hot j)
    (s : BasisState) (hs : HotClean9 hot s) :
    NetworkReady (hotNetwork9 low hot) (Classical.run [.X (hot 0)] s) :=
  (net_run 9 (lowN9 low) (hotNat9 hot) (hotLayout_of9 low hot hi hd) _ (hotStart9 hot hi s hs) 9 le_rfl).2.2

theorem hotPrepare_marker9 (low : Fin 9 → Wire) (hot : Fin 512 → Wire)
    (hi : Function.Injective hot) (hd : ∀ i j, low i ≠ hot j)
    (s : BasisState) (hs : HotClean9 hot s) (i : Fin 512) :
    Classical.run (hotPrepare9 low hot) s (hot i) = decide (i.val = hotAddress9 low s) := by
  have h := (net_run 9 (lowN9 low) (hotNat9 hot) (hotLayout_of9 low hot hi hd) _ (hotStart9 hot hi s hs) 9 le_rfl).1
    i.val (by simp)
  have hhot : hotNat9 hot i.val = hot i := by simp [hotNat9, i.isLt]
  rw [hhot] at h
  rw [hotPrepare_eq9 low hot hi hd s hs, slowHotPrepare9, Classical.run_append, hotNetwork9, h, hotAddress9]
  congr 2
  apply addrN_congr
  intro j hj
  have hj' : j < 9 := hj
  simp only [lowN9, hj', dite_true]
  have hne : low ⟨j, hj'⟩ ≠ hot 0 := hd _ _
  simp [Classical.run, Classical.applyGate, upd, hne]

theorem hotPrepare_frame9 (low : Fin 9 → Wire) (hot : Fin 512 → Wire)
    (s : BasisState) (w : Wire) (hw : ∀ i,w≠hot i) :
    Classical.run (hotPrepare9 low hot) s w=s w := by
  rw [hotPrepare9,Classical.run_append,ParityBank.parityNet_frame 9 _ _ 9 le_rfl _ w (by
    intro x hx
    have hx' : x<512 := by simpa using hx
    simpa only [hotNat9,hx',dite_true] using hw ⟨x,hx'⟩)]
  simp [Classical.run,Classical.applyGate,upd,hw]

theorem hotAddress_bound9 (low : Fin 9 → Wire) (s : BasisState) : hotAddress9 low s < 512 := by
  have h := addrN_lt (lowN9 low) s 9
  simpa [hotAddress9] using h

attribute [irreducible] hotNetwork9

def phasePorts9 {n base : Nat} (hot : Fin 512 → Wire)
    (items : List (ClearPort n × Fin base)) : List (RecordPort n base) :=
  items.flatMap fun item => List.ofFn fun i : Fin 512 =>
    ⟨fun h => item.1.ref (512 * h + i.val), item.1.value, item.2, hot i⟩

def logicalPorts9 {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (hot : Fin 512 → Wire) : List (RecordPort n 2) :=
  phasePorts9 hot (data.zip (outcomes.map boolRecord))

def hotBank9 (hot : Fin 512 → Wire) : List Wire := List.ofFn hot

def fixupSource9 {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (read : ConstantBit n → Bool) (low : Fin 9 → Wire) (hot : Fin 512 → Wire)
    (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire) : AdaptiveCircuit :=
  (AdaptiveCircuit.unitary (hotPrepare9 low hot) .done).seq
    ((phaseLookupSource (logicalPorts9 data outcomes hot) scratch read boolHistory
      tree root paths (hotBank9 hot)).seq
      ((eraseNetworkSource (hotNetwork9 low hot)).seq (.unitary [.X (hot 0)] .done)))

def fixupProgram9 {n base : Nat} (data : List (ClearPort n)) (refs : List (Fin base))
    (low : Fin 9 → Wire) (hot : Fin 512 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire) :
    Straight n base (base + recordMeasurements (recordUnaryOps tree root paths) + 511) :=
  (literalProgram (hotPrepare9 low hot)).append
    ((literalProgram ((hotBank9 hot).map Gate.H)).append
      ((recordLookupProgram (phasePorts9 hot (data.zip refs)) scratch
        (recordUnaryOps tree root paths) base (Nat.le_refl base)).append
        ((literalProgram (Circuit.adjoint ((hotBank9 hot).map Gate.H))).append
          (castFinish (by simp [hotNetwork_length9])
            ((eraseNetwork n (hotNetwork9 low hot)
              (base + recordMeasurements (recordUnaryOps tree root paths))).append
              (literalProgram [.X (hot 0)]))))))

def measuredClear9 {n : Nat} (data : List (ClearPort n)) (low : Fin 9 → Wire) (hot : Fin 512 → Wire)
    (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire) (start : Nat) :
    Straight n start (start + data.length + (recordMeasurements (recordUnaryOps tree root paths) + 511)) :=
  castFinish (by simp) (measureThen (R := recordMeasurements (recordUnaryOps tree root paths) + 511)
    (fun cursor refs => castFinish (by omega) (fixupProgram9 data refs low hot tree root scratch paths))
    (data.map ClearPort.target) start ([] : List (Fin start)))

def LoadedClear9 {n : Nat} (data : List (ClearPort n)) (read : ConstantBit n → Bool)
    (low : Fin 9 → Wire) (tree : UnaryActionTree) (root : Wire) (s : BasisState) : Prop :=
  ∀ p ∈ data, s p.target = (s root && decide (read (p.ref (512 * tree.routeLabel s + hotAddress9 low s)) = p.value))

theorem phasePorts_targets9 {n base : Nat} (hot : Fin 512 → Wire)
    (items : List (ClearPort n × Fin base)) :
    ∀ p ∈ phasePorts9 hot items, p.target ∈ hotBank9 hot := by
  intro p hp
  obtain ⟨item, _, hi⟩ := List.mem_flatMap.mp hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hi
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

theorem hotPrepare_hp9 (low : Fin 9 → Wire) (hot : Fin 512 → Wire) :
    Classical.HPFree (hotPrepare9 low hot) := by
  simp [hotPrepare9, ParityBank.parityNet_hp]

def fixupFactor9 {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (read : ConstantBit n → Bool) (low : Fin 9 → Wire) (hot : Fin 512 → Wire)
    (tree : UnaryActionTree) (root : Wire) (s : BasisState) : ℂ :=
  phaseLookupFactor (logicalPorts9 data outcomes hot) read boolHistory tree root
    (Classical.run (hotPrepare9 low hot) s)

theorem fixupSource_coherent9 {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (read : ConstantBit n → Bool) (low : Fin 9 → Wire) (hot : Fin 512 → Wire)
    (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire)
    (hl : tree.Layout root paths) (hi : Function.Injective hot)
    (hdlow : ∀ i j, low i ≠ hot j)
    (hbank : (hotBank9 hot).Disjoint (root :: tree.indexWires.dedup ++ paths))
    (hs : scratch ∉ root :: tree.indexWires.dedup ++ paths)
    (hshot : scratch ∉ hotBank9 hot) :
    CoherentlyImplementsOn (fixupSource9 data outcomes read low hot tree root scratch paths)
      (basisIdeal id (fixupFactor9 data outcomes read low hot tree root))
      (fun s => HotClean9 hot s ∧ Clean paths s) := by
  have hp := phasePorts_targets9 hot (data.zip (outcomes.map boolRecord))
  have htarget : ∀ p ∈ logicalPorts9 data outcomes hot, scratch ≠ p.target := by
    intro p hpp he
    exact hshot (he.symm ▸ hp p hpp)
  have hq := phaseLookup_coherent (logicalPorts9 data outcomes hot) scratch read boolHistory
    tree root paths (hotBank9 hot) hl (List.nodup_ofFn.mpr hi) hbank hs hp htarget
  have hpre := (CoherentlyImplementsOn.unitary (hotPrepare9 low hot)
    (fun s => HotClean9 hot s ∧ Clean paths s)).seq hq (by
      intro s hvalid
      rw [run_ket_agrees_classical _ _ (hotPrepare_hp9 low hot)]
      apply supportedOn_ket
      intro w hw
      rw [hotPrepare_frame9 low hot s w (by
        intro i he
        exact List.disjoint_left.mp hbank (List.mem_ofFn.mpr ⟨i, he.symm⟩) (by simp [hw]))]
      exact hvalid.2 w hw)
  have hn := eraseNetwork_coherent (hotNetwork9 low hot) (hotNetwork_physical9 low hot hi hdlow)
  have hpost := hn.seq (CoherentlyImplementsOn.unitary [.X (hot 0)] (fun _ => True)) (by
    intro s hvalid v hv
    trivial)
  have htotal := hpre.seq hpost (by
    intro s hvalid
    simp only [LinearMap.comp_apply]
    rw [run_ket_agrees_classical _ _ (hotPrepare_hp9 low hot), basisIdeal_ket]
    apply supported_smul_state
    apply supportedOn_ket
    exact ⟨Classical.run [.X (hot 0)] s, hotNetwork_ready9 low hot hi hdlow s hvalid.1,
      by rw [hotPrepare_eq9 low hot hi hdlow s hvalid.1]; rfl⟩)
  rw [fixupSource9, ← adaptive_seq_assoc]
  apply htotal.congrIdeal
  intro s hvalid
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  rw [run_ket_agrees_classical _ _ (hotPrepare_hp9 low hot), basisIdeal_ket]
  simp only [map_smul, id_eq]
  rw [run_ket_agrees_classical _ _ (inverseNetwork_hp (hotNetwork9 low hot))]
  rw [hotPrepare_eq9 low hot hi hdlow s hvalid.1, slowHotPrepare9, Classical.run_append,
    inverseNetwork_correct (hotNetwork9 low hot) (hotNetwork_physical9 low hot hi hdlow) _
      (hotNetwork_ready9 low hot hi hdlow s hvalid.1),
    run_ket_agrees_classical _ _ (by simp), classical_x_twice]
  simp only [basisIdeal_ket, id_eq]
  rw [fixupFactor9, hotPrepare_eq9 low hot hi hdlow s hvalid.1, slowHotPrepare9, Classical.run_append]

theorem phasePorts_block9 (p : ClearPort n) (m : Bool) (hot : Fin 512 → Wire)
    (read : ConstantBit n → Bool) (row root : Nat) (s : BasisState) (selected : Fin 512)
    (hm : ∀ i, s (hot i) = decide (i = selected)) :
    xorPhase root (recordTargets (phasePorts9 hot ([(p, boolRecord m)])) row read boolHistory) s =
      if m && (s root && decide (read (p.ref (512 * row + selected.val)) = p.value)) then (-1 : ℂ) else 1 := by
  rw [xorPhase_recordTargets]
  simp only [phasePorts9, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_ofFn,
    List.prod_ofFn, Function.comp_def]
  rw [Finset.prod_eq_single selected]
  · rw [hm selected]
    cases hm0 : m <;> cases hr : s root <;>
      by_cases hrd : read (p.ref (12128 * row + selected.val)) = p.value <;>
      simp [boolHistory, boolRecord]
  · intro i _ hi
    rw [hm i]
    simp [hi]
  · simp

theorem logicalPorts_cons9 (p : ClearPort n) (ps : List (ClearPort n)) (m : Bool)
    (ms : List Bool) (hot : Fin 512 → Wire) :
    logicalPorts9 (p :: ps) (m :: ms) hot = phasePorts9 hot ([(p, boolRecord m)]) ++ logicalPorts9 ps ms hot := by
  simp only [logicalPorts9, List.map_cons, List.zip_cons_cons, phasePorts9, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]

theorem phaseFactor_loaded9 {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (read : ConstantBit n → Bool) (hot : Fin 512 → Wire) (tree : UnaryActionTree) (root : Wire)
    (original prepared : BasisState) (selected : Fin 512)
    (hm : ∀ i, prepared (hot i) = decide (i = selected))
    (hw : ∀ p ∈ data, original p.target =
      (prepared root && decide (read (p.ref (512 * tree.routeLabel prepared + selected.val)) = p.value))) :
    phaseLookupFactor (logicalPorts9 data outcomes hot) read boolHistory tree root prepared =
      registerXPhase (data.map ClearPort.target) outcomes original := by
  unfold phaseLookupFactor
  induction data generalizing outcomes with
  | nil =>
    simp only [logicalPorts9, List.zip_nil_left, phasePorts9, List.flatMap_nil]
    simp [recordTargets, xorPhase, registerXPhase]
  | cons p ps ih =>
    cases outcomes with
    | nil =>
      simp only [logicalPorts9, List.map_nil, List.zip_nil_right, phasePorts9, List.flatMap_nil]
      simp [recordTargets, xorPhase, registerXPhase]
    | cons m ms =>
      rw [logicalPorts_cons9, recordTargets_append, xorPhase_append, phasePorts_block9 p m hot read _ root prepared selected hm,
        ih ms (fun q hq => hw q (by simp [hq]))]
      simp only [List.map_cons, registerXPhase, hw p (by simp)]

theorem phasePorts_cons9 {n base : Nat} (hot : Fin 512 → Wire)
    (item : ClearPort n × Fin base) (items : List (ClearPort n × Fin base)) :
    phasePorts9 hot (item :: items) = phasePorts9 hot ([item]) ++ phasePorts9 hot items := by
  simp only [phasePorts9, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem phasePorts_resolve9 {n base : Nat} (data : List (ClearPort n)) (refs : List (Fin base))
    (hot : Fin 512 → Wire) (scratch row control : Nat) (read : ConstantBit n → Bool) (saved : Fin base → Bool) :
    recordLeafCircuit (phasePorts9 hot (data.zip refs)) scratch row control read saved =
      recordLeafCircuit (logicalPorts9 data (refs.map saved) hot) scratch row control read boolHistory := by
  induction data generalizing refs with
  | nil => rfl
  | cons p ps ih =>
    cases refs with
    | nil => rfl
    | cons r rs =>
      simp only [List.zip_cons_cons, List.map_cons]
      rw [phasePorts_cons9, logicalPorts_cons9, recordLeafCircuit_append, recordLeafCircuit_append]
      rw [ih rs]
      congr 1
      simp only [phasePorts9, List.flatMap_cons, List.flatMap_nil, List.append_nil, recordLeafCircuit]
      apply flatMap_ofFn_congr
      intro i
      cases hm : saved r <;> simp [boolRecord, boolHistory]

theorem recordSource_resolve9 {n base : Nat} (data : List (ClearPort n)) (refs : List (Fin base))
    (hot : Fin 512 → Wire) (scratch : Wire) (read : ConstantBit n → Bool) (saved : Fin base → Bool)
    (ops : List RecordLookupOp) :
    recordLookupSource (phasePorts9 hot (data.zip refs)) scratch read saved ops =
      recordLookupSource (logicalPorts9 data (refs.map saved) hot) scratch read boolHistory ops := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | gates gs => simp only [recordLookupSource, ih]
    | leaf row control => simp only [recordLookupSource, phasePorts_resolve9, ih]
    | erase a b t => simp only [recordLookupSource, ih]

theorem fixupProgram_run9 {n base : Nat} (data : List (ClearPort n)) (refs : List (Fin base))
    (read : ConstantBit n → Bool) (low : Fin 9 → Wire) (hot : Fin 512 → Wire)
    (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire) (history : Fin base → Bool) :
    ((fixupProgram9 data refs low hot tree root scratch paths).instantiate read history).run =
      (fixupSource9 data (refs.map history) read low hot tree root scratch paths).run := by
  have hpost (cursor : Nat) (h : Fin cursor → Bool) :
      (((eraseNetwork n (hotNetwork9 low hot) cursor).append
        (literalProgram [.X (hot 0)])).instantiate read h).run =
      ((eraseNetworkSource (hotNetwork9 low hot)).seq (.unitary [.X (hot 0)] .done)).run := by
    rw [append_run_fixed _ _ _ _ _ (fun h => literalProgram_run [.X (hot 0)] read h),
      AdaptiveCircuit.run_seq, eraseNetwork_source, ← AdaptiveCircuit.run_seq]
  have htail (cursor : Nat) (h : Fin cursor → Bool) :
      (((literalProgram (Circuit.adjoint ((hotBank9 hot).map Gate.H))).append
        (castFinish (f := cursor + 511) (by simp [hotNetwork_length9])
          ((eraseNetwork n (hotNetwork9 low hot) cursor).append
            (literalProgram [.X (hot 0)])))).instantiate read h).run =
      (AdaptiveCircuit.unitary (Circuit.adjoint ((hotBank9 hot).map Gate.H))
        ((eraseNetworkSource (hotNetwork9 low hot)).seq (.unitary [.X (hot 0)] .done))).run := by
    rw [literalProgram_append_run]
    apply unitary_run_congr
    rw [castFinish_instantiate, hpost]
  have hsource : fixupSource9 data (refs.map history) read low hot tree root scratch paths =
      .unitary (hotPrepare9 low hot) (.unitary ((hotBank9 hot).map Gate.H)
        ((recordLookupSource (logicalPorts9 data (refs.map history) hot) scratch read boolHistory
          (recordUnaryOps tree root paths)).seq
          (.unitary (Circuit.adjoint ((hotBank9 hot).map Gate.H))
            ((eraseNetworkSource (hotNetwork9 low hot)).seq (.unitary [.X (hot 0)] .done))))) := by
    simp only [fixupSource9, phaseLookupSource, adaptive_seq_assoc, AdaptiveCircuit.seq]
  rw [hsource, fixupProgram9, literalProgram_append_run]
  apply unitary_run_congr
  rw [literalProgram_append_run]
  apply unitary_run_congr
  rw [append_run_fixed _ _ _ _ _ (fun h => htail _ h),
    AdaptiveCircuit.run_seq, recordLookup_run]
  have hh : historyPrefix (Nat.le_refl base) history = history := rfl
  rw [hh, recordSource_resolve9, ← AdaptiveCircuit.run_seq]

theorem measuredClear_run9 {n : Nat} (data : List (ClearPort n))
    (read : ConstantBit n → Bool) (low : Fin 9 → Wire) (hot : Fin 512 → Wire)
    (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire) (start : Nat) (history : Fin start → Bool) :
    ((measuredClear9 data low hot tree root scratch paths start).instantiate read history).run =
      (measureResetThen (data.map ClearPort.target)
        (fun outcomes => fixupSource9 data outcomes read low hot tree root scratch paths)).run := by
  rw [measuredClear9, castFinish_instantiate,
    measureThen_run _ (fun outcomes => fixupSource9 data outcomes read low hot tree root scratch paths) read
      (by intro cursor refs h; rw [castFinish_instantiate, fixupProgram_run9])]
  rfl

theorem fixupSource_wellFormed9 {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (read : ConstantBit n → Bool) (low : Fin 9 → Wire) (hot : Fin 512 → Wire)
    (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire)
    (hl : tree.Layout root paths) (hi : Function.Injective hot) (hdlow : ∀ i j, low i ≠ hot j)
    (hs : scratch ∉ root :: tree.indexWires.dedup ++ paths) (hshot : scratch ∉ hotBank9 hot) :
    (fixupSource9 data outcomes read low hot tree root scratch paths).WellFormed := by
  rw [fixupSource9]
  apply AdaptiveCircuit.WellFormed.seq
  · refine ⟨?_, trivial⟩
    rw [hotPrepare9, circuitWellFormed_append]
    exact ⟨by simp [CircuitWellFormed, Gate.WellFormed],
      ParityBank.parityNet_wellFormed 9 (lowN9 low) (hotNat9 hot) (hotLayout_of9 low hot hi hdlow) 9 le_rfl⟩
  · apply AdaptiveCircuit.WellFormed.seq
    · apply phaseLookupSource_wellFormed _ _ _ _ _ _ _ _ hl hs
      intro p hp he
      exact hshot (he.symm ▸ phasePorts_targets9 hot _ p hp)
    · apply AdaptiveCircuit.WellFormed.seq
      · exact eraseNetworkSource_wellFormed _ (hotNetwork_physical9 low hot hi hdlow)
      · exact ⟨by simp [CircuitWellFormed, Gate.WellFormed], trivial⟩

theorem hotPrepare_tCount9 (low : Fin 9 → Wire) (hot : Fin 512 → Wire) :
    ShorECDLP.tCount (hotPrepare9 low hot)=3514 := by
  have h := ParityBank.parityNet_tCount (lowN9 low) (hotNat9 hot) 9
  rw [hotPrepare9,ShorECDLP.tCount_append]
  change 0+ShorECDLP.tCount (ParityBank.parityNet (lowN9 low) (hotNat9 hot) 9)=3514
  norm_num at h
  omega

theorem hotPrepare_length9 (low : Fin 9 → Wire) (hot : Fin 512 → Wire) :
    (hotPrepare9 low hot).length=1525 := by
  have h := ParityBank.parityNet_length (lowN9 low) (hotNat9 hot) 9
  rw [hotPrepare9,List.length_append]
  simp only [List.length_cons,List.length_nil]
  norm_num at h
  omega

theorem phasePorts_length9 {n base : Nat} (hot : Fin 512 → Wire) (items : List (ClearPort n × Fin base)) :
    (phasePorts9 hot items).length = 512 * items.length := by
  induction items with
  | nil => rfl
  | cons item items ih =>
    rw [phasePorts_cons9, List.length_append, ih]
    simp only [phasePorts9, List.flatMap_cons, List.flatMap_nil, List.length_append,
      List.length_ofFn, List.length_nil, List.length_cons]
    omega

theorem fixupProgram_tCount9 {n base : Nat} (data : List (ClearPort n)) (refs : List (Fin base))
    (low : Fin 9 → Wire) (hot : Fin 512 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire) (hl : tree.Layout root paths)
    (read : ConstantBit n → Bool) (history : Fin base → Bool) :
    ((fixupProgram9 data refs low hot tree root scratch paths).instantiate read history).tCount =
      7 * tree.internalNodes + 3514 := by
  have hpost (cursor : Nat) (h : Fin cursor → Bool) :
      (((eraseNetwork n (hotNetwork9 low hot) cursor).append
        (literalProgram [.X (hot 0)])).instantiate read h).tCount = 0 := by
    rw [append_tCount_fixed _ _ _ _ _ (fun h => literalProgram_tCount [.X (hot 0)] read h), eraseNetwork_tCount]
    rfl
  have htail (cursor : Nat) (h : Fin cursor → Bool) :
      (((literalProgram (Circuit.adjoint ((hotBank9 hot).map Gate.H))).append
        (castFinish (f := cursor + 511) (by simp [hotNetwork_length9])
          ((eraseNetwork n (hotNetwork9 low hot) cursor).append
            (literalProgram [.X (hot 0)])))).instantiate read h).tCount = 0 := by
    rw [literalProgram_append_tCount, castFinish_instantiate, hpost, ShorECDLP.tCount_adjoint, hadamards_tCount]
  simp only [fixupProgram9, literalProgram_append_tCount]
  rw [append_tCount_fixed _ _ _ _ _ (fun h => htail _ h), recordLookup_tCount,
    (recordUnary_counts tree root paths hl 0).2.1, hotPrepare_tCount9, hadamards_tCount]
  omega

theorem measuredClear_tCount9 {n : Nat} (data : List (ClearPort n))
    (low : Fin 9 → Wire) (hot : Fin 512 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire) (hl : tree.Layout root paths)
    (read : ConstantBit n → Bool) (start : Nat) (history : Fin start → Bool) :
    ((measuredClear9 data low hot tree root scratch paths start).instantiate read history).tCount =
      7 * (tree.internalNodes + 502) := by
  rw [measuredClear9, castFinish_instantiate, measureThen_tCount _ read (by
    intro cursor refs h
    rw [castFinish_instantiate, fixupProgram_tCount9 data refs low hot tree root scratch paths hl])]
  omega

theorem fixupProgram_slots9 {n base : Nat} (data : List (ClearPort n)) (refs : List (Fin base))
    (low : Fin 9 → Wire) (hot : Fin 512 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire) (hl : tree.Layout root paths) :
    (fixupProgram9 data refs low hot tree root scratch paths).gateSlots =
      2048 * min data.length refs.length * tree.leaves + 10 * tree.internalNodes + 4594 := by
  simp only [fixupProgram9, Straight.gateSlots_append, literalProgram_slots, castFinish_gateSlots]
  rw [recordLookup_slots, (recordUnary_counts tree root paths hl _).2.2, eraseNetwork_slots]
  simp only [phasePorts_length9, List.length_zip, hotPrepare_length9, hotBank9,
    List.length_ofFn, List.length_map, Circuit.adjoint, List.length_reverse,
    hotNetwork_length9, List.length_cons, List.length_nil]
  ring

theorem measuredClear_slots9 {n : Nat} (data : List (ClearPort n))
    (low : Fin 9 → Wire) (hot : Fin 512 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire) (hl : tree.Layout root paths) (start : Nat) :
    (measuredClear9 data low hot tree root scratch paths start).gateSlots =
      2048 * data.length * tree.leaves + 10 * tree.internalNodes + 4594 := by
  rw [measuredClear9, castFinish_gateSlots, measureThen_slots _
    (fun k => 2048 * min data.length k * tree.leaves + 10 * tree.internalNodes + 4594)
    (by intro cursor refs; rw [castFinish_gateSlots, fixupProgram_slots9 data refs low hot tree root scratch paths hl])]
  simp

def clearSupport9 {n : Nat} (data : List (ClearPort n)) (low : Fin 9 → Wire) (hot : Fin 512 → Wire)
    (tree : UnaryActionTree) (root : Wire) (paths : List Wire) : List Wire :=
  data.map ClearPort.target ++ List.ofFn low ++ hotBank9 hot ++ (root :: tree.indexWires.dedup ++ paths)

theorem hotNetwork_within9 (low : Fin 9 → Wire) (hot : Fin 512 → Wire) (S : List Wire)
    (hl : ∀ i, low i ∈ S) (hh : ∀ i, hot i ∈ S) :
    ∀ c ∈ hotNetwork9 low hot, c.bit ∈ S ∧ c.parent ∈ S ∧ c.child ∈ S := by
  intro c hc
  obtain ⟨j, x, y, rfl, _⟩ := mem_hotNetwork9 low hot c hc
  exact ⟨hl _, hh _, hh _⟩

theorem hotPrepare_within9 (low : Fin 9 → Wire) (hot : Fin 512 → Wire) (S : List Wire)
    (hl : ∀ i, low i ∈ S) (hh : ∀ i, hot i ∈ S) : circuitWires (hotPrepare9 low hot) ⊆ S := by
  rw [hotPrepare9, circuitWires_append]
  exact List.append_subset.mpr ⟨by simpa [circuitWires, gateWires] using hh 0,
    ParityBank.parityNet_within 9 (lowN9 low) (hotNat9 hot) 9 le_rfl S
      (by intro j hj; simpa [lowN9,hj] using hl ⟨j,hj⟩)
      (by
        intro x hx
        have hx' : x<512 := by simpa using hx
        simpa [hotNat9,hx'] using hh ⟨x,hx'⟩)⟩

theorem fixupProgram_within9 {n base : Nat} (data : List (ClearPort n)) (refs : List (Fin base))
    (low : Fin 9 → Wire) (hot : Fin 512 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths S : List Wire)
    (hr : root ∈ S) (hs : scratch ∈ S) (hl : ∀ i, low i ∈ S) (hh : ∀ i, hot i ∈ S)
    (hi : tree.indexWires ⊆ S) (ha : paths ⊆ S) :
    NaiveChallenge.straightWires (fixupProgram9 data refs low hot tree root scratch paths) ⊆ S := by
  have hb : hotBank9 hot ⊆ S := by
    intro w hw
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
    exact hh i
  unfold fixupProgram9
  apply static_within_append
  · rw [literal_static]
    exact hotPrepare_within9 low hot S hl hh
  · apply static_within_append
    · rw [literal_static, hadamards_wires]
      exact hb
    · apply static_within_append
      · rw [recordLookup_static]
        apply recordWireList_within
        exact recordUnary_within _ scratch tree root paths S hr hs hi ha
          (fun p hp => hb (phasePorts_targets9 hot _ p hp))
      · apply static_within_append
        · rw [literal_static, hadamards_adjoint_wires]
          intro w hw
          exact hb (List.mem_reverse.mp hw)
        · rw [static_cast]
          apply static_within_append (eraseNetwork_within n _ _ S (hotNetwork_within9 low hot S hl hh))
          rw [literal_static]
          simpa [circuitWires, gateWires] using hh 0

/-- The generic row reference is exactly the physical little-endian address. -/
theorem splitAddress_value9 (low : Fin 9 → Wire) (high : List Wire) (s : BasisState) :
    512 * (tableAddressTree high 0 1).routeLabel s + hotAddress9 low s =
      tableAddressValue ([lowN9 low 0, lowN9 low 1, lowN9 low 2, lowN9 low 3, lowN9 low 4, lowN9 low 5,
        lowN9 low 6, lowN9 low 7, lowN9 low 8] ++ high) s := by
  simp only [tableAddressTree_route, zero_add, one_mul, List.cons_append, List.nil_append,
    tableAddressValue, hotAddress9, addrN]
  ring

/-- The measured data bank is available to the phase fixup after reset. -/
theorem fixupFactor_recycled9 {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (read : ConstantBit n → Bool) (low : Fin 9 → Wire) (hot : Fin 512 → Wire)
    (tree : UnaryActionTree) (root : Wire) (paths : List Wire)
    (hi : Function.Injective hot) (hdlow : ∀ i j, low i ≠ hot j)
    (hbank : (hotBank9 hot).Disjoint (root :: tree.indexWires.dedup ++ paths))
    (ha : ∀ w ∈ root :: List.ofFn low ++ tree.indexWires.dedup ++ paths,
      w ∉ data.map ClearPort.target)
    (hh : ∀ i, hot i ∈ data.map ClearPort.target)
    (s : BasisState) (hs : Clean paths s ∧ LoadedClear9 data read low tree root s) :
    fixupFactor9 data outcomes read low hot tree root (clearRegister (data.map ClearPort.target) s) =
      registerXPhase (data.map ClearPort.target) outcomes s := by
  let cleared := clearRegister (data.map ClearPort.target) s
  let prepared := Classical.run (hotPrepare9 low hot) cleared
  have hhot : HotClean9 hot cleared := by
    intro i
    change clearRegister (data.map ClearPort.target) s (hot i) = false
    exact clearRegister_clean _ s _ (hh i)
  have hlow : ∀ i, cleared (low i) = s (low i) := by
    intro i
    have hw : low i ∈ List.ofFn low := List.mem_ofFn.mpr ⟨i, rfl⟩
    exact clearRegister_frame _ _ _ (ha _ (by simp only [List.mem_cons, List.mem_append, hw, or_true, true_or]))
  have haddr : hotAddress9 low cleared = hotAddress9 low s :=
    addrN_congr _ _ _ 9 (fun j hj => by simp only [lowN9, hj, dite_true]; exact hlow _)
  have hframe (w : Wire) (hw : w ∈ root :: tree.indexWires.dedup ++ paths) : prepared w = s w := by
    change Classical.run (hotPrepare9 low hot) cleared w = s w
    rw [hotPrepare_frame9 low hot cleared w (by
      intro i he
      exact List.disjoint_left.mp hbank (List.mem_ofFn.mpr ⟨i, he.symm⟩) hw)]
    apply clearRegister_frame
    apply ha
    simp only [List.mem_cons, List.mem_append] at hw ⊢
    tauto
  have hroute : tree.routeLabel prepared = tree.routeLabel s := by
    apply tree.routeLabel_congr prepared s
    intro w hw
    exact hframe w (by simp [hw])
  let selected : Fin 512 := ⟨hotAddress9 low s, hotAddress_bound9 low s⟩
  apply phaseFactor_loaded9 data outcomes read hot tree root s prepared selected
  · intro i
    simpa only [Fin.ext_iff, haddr] using hotPrepare_marker9 low hot hi hdlow cleared hhot i
  · intro p hp
    rw [hframe root (by simp), hroute]
    exact hs.2 p hp

theorem measuredClear_recycled_coherent9 {n : Nat} (data : List (ClearPort n))
    (read : ConstantBit n → Bool) (low : Fin 9 → Wire) (hot : Fin 512 → Wire)
    (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire)
    (hl : tree.Layout root paths) (hi : Function.Injective hot) (hdlow : ∀ i j, low i ≠ hot j)
    (hbank : (hotBank9 hot).Disjoint (root :: tree.indexWires.dedup ++ paths))
    (hs : scratch ∉ root :: tree.indexWires.dedup ++ paths) (hshot : scratch ∉ hotBank9 hot)
    (hn : (data.map ClearPort.target).Nodup)
    (ha : ∀ w ∈ root :: List.ofFn low ++ tree.indexWires.dedup ++ paths,
      w ∉ data.map ClearPort.target)
    (hh : ∀ i, hot i ∈ data.map ClearPort.target)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((measuredClear9 data low hot tree root scratch paths start).instantiate read history)
      (Finsupp.lmapDomain ℂ ℂ (clearRegister (data.map ClearPort.target)))
      (fun s => Clean paths s ∧ LoadedClear9 data read low tree root s) := by
  unfold CoherentlyImplementsOn
  rw [measuredClear_run9]
  apply measureResetThen_coherent (data.map ClearPort.target)
    (fun outcomes => fixupSource9 data outcomes read low hot tree root scratch paths)
    (fun outcomes => basisIdeal id (fixupFactor9 data outcomes read low hot tree root))
    (fun _ s => HotClean9 hot s ∧ Clean paths s)
    (fun s => Clean paths s ∧ LoadedClear9 data read low tree root s)
    (clearRegister (data.map ClearPort.target)) hn (witness := zeroBasisState)
  · intro outcomes hout
    exact fixupSource_wellFormed9 data outcomes read low hot tree root scratch paths hl hi hdlow hs hshot
  · intro outcomes
    exact fixupSource_coherent9 data outcomes read low hot tree root scratch paths hl hi hdlow hbank hs hshot
  · intro outcomes hout s hvalid
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i
      exact clearRegister_clean _ s _ (hh i)
    · intro w hw
      rw [clearRegister_frame _ _ _ (ha w (by simp [hw]))]
      exact hvalid.1 w hw
    · rw [basisIdeal_ket, fixupFactor_recycled9 data outcomes read low hot tree root paths hi hdlow hbank ha hh s hvalid]
      rfl
  · simp [Clean, LoadedClear9, zeroBasisState]

end
end ShorECDLP.Entrant.MeasuredClear

namespace ShorECDLP.Entrant.MeasuredClear
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

theorem fixupProgram_wellFormed9 {n base} (data : List (ClearPort n)) (refs : List (Fin base))
    (low : Fin 9 → Wire) (hot : Fin 512 → Wire) (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire)
    (hl : tree.Layout root paths) (hi : Function.Injective hot) (hdlow : ∀ i j, low i ≠ hot j)
    (hs : scratch ∉ root :: tree.indexWires.dedup ++ paths) (hshot : scratch ∉ hotBank9 hot) :
    (fixupProgram9 data refs low hot tree root scratch paths).WellFormed := by
  have hp := hotNetwork_physical9 low hot hi hdlow
  have hH (ws : List Wire) : CircuitWellFormed (ws.map Gate.H) := by
    intro g hg; obtain ⟨w,_,rfl⟩ := List.mem_map.mp hg; trivial
  unfold fixupProgram9
  apply straight_append_wellFormed
  · apply literalProgram_wellFormed
    rw [hotPrepare9,circuitWellFormed_append]
    exact ⟨by simp [CircuitWellFormed,Gate.WellFormed],ParityBank.parityNet_wellFormed 9 (lowN9 low) (hotNat9 hot) (hotLayout_of9 low hot hi hdlow) 9 le_rfl⟩
  · apply straight_append_wellFormed
    · exact literalProgram_wellFormed _ (hH _)
    · apply straight_append_wellFormed
      · apply recordLookupProgram_wellFormed
        apply recordUnary_physical _ _ _ _ _ hl
        intro row c hc
        refine ⟨?_,?_⟩
        · intro he; apply hs; subst c; simp only [List.mem_cons,List.mem_append] at hc ⊢; tauto
        · intro p hpm he
          exact hshot (he.symm ▸ phasePorts_targets9 hot _ p hpm)
      · apply straight_append_wellFormed
        · exact literalProgram_wellFormed _ ((circuitWellFormed_adjoint _).mpr (hH _))
        · rw [castFinish_wellFormed]
          exact straight_append_wellFormed _ _ (eraseNetwork_wellFormed n _ hp _)
            (literalProgram_wellFormed _ (by simp [CircuitWellFormed,Gate.WellFormed]))

theorem measuredClear_wellFormed9 {n} (data : List (ClearPort n))
    (low : Fin 9 → Wire) (hot : Fin 512 → Wire) (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire)
    (hl : tree.Layout root paths) (hi : Function.Injective hot) (hdlow : ∀ i j, low i ≠ hot j)
    (hs : scratch ∉ root :: tree.indexWires.dedup ++ paths) (hshot : scratch ∉ hotBank9 hot) (start : Nat) :
    (measuredClear9 data low hot tree root scratch paths start).WellFormed := by
  rw [measuredClear9,castFinish_wellFormed]
  apply measureThen_wellFormed
  intro cursor refs
  rw [castFinish_wellFormed]
  exact fixupProgram_wellFormed9 data refs low hot tree root scratch paths hl hi hdlow hs hshot

open AndGadget in
 theorem fixupProgram_residue9 {n base} (data : List (ClearPort n)) (refs : List (Fin base))
    (low : Fin 9 → Wire) (hot : Fin 512 → Wire) (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire) :
    residue (fixupProgram9 data refs low hot tree root scratch paths) = 0 := by
  unfold fixupProgram9
  rw [residue_append,residue_literal_HPFree _ (hotPrepare_hp9 low hot)]
  simp only [residue_append,residue_literal,residue_cast,eraseNetwork_residue,
    recordLookup_residue _ _ _ _ _ (recordUnary_phaseFree tree root paths),Nat.zero_add]
  simp [List.map_map,Function.comp_def,primitivePhaseCost,Circuit.adjoint,List.map_reverse,Gate.adjoint]

open AndGadget in
 theorem measuredClear_residue9 {n} (data : List (ClearPort n))
    (low : Fin 9 → Wire) (hot : Fin 512 → Wire) (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire) (start : Nat) :
    residue (measuredClear9 data low hot tree root scratch paths start) = 0 := by
  rw [measuredClear9,residue_cast]
  apply measureThen_residue
  intro cursor refs
  rw [residue_cast]
  exact fixupProgram_residue9 data refs low hot tree root scratch paths

theorem measuredClear_static9 {n : Nat} (data : List (ClearPort n))
    (low : Fin 9 → Wire) (hot : Fin 512 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire) (hsc : scratch ∈ data.map ClearPort.target)
    (start : Nat) :
    NaiveChallenge.straightWires (measuredClear9 data low hot tree root scratch paths start) ⊆
      clearSupport9 data low hot tree root paths := by
  rw [measuredClear9, static_cast]
  apply measureThen_within _ _ (by
    intro cursor refs
    rw [static_cast]
    apply fixupProgram_within9
    · simp [clearSupport9]
    · simp [clearSupport9, hsc]
    · intro i
      have hm : low i ∈ List.ofFn low := List.mem_ofFn.mpr ⟨i, rfl⟩
      simp only [clearSupport9, List.mem_append, List.mem_cons, hm, true_or, or_true]
    · intro i
      have hm : hot i ∈ hotBank9 hot := List.mem_ofFn.mpr ⟨i, rfl⟩
      simp only [clearSupport9, List.mem_append, List.mem_cons, hm, true_or, or_true]
    · intro w hw
      simp [clearSupport9, hw]
    · intro w hw
      simp [clearSupport9, hw])
  intro w hw
  simp [clearSupport9, hw]

end
end ShorECDLP.Entrant.MeasuredClear
end

/-! ### Consolidated from `PoolHost.lean` -/
section
/-! Shared avoidance and cleanliness proofs for the thirty clean dialog-pool wires `14848..14877`.
None of these wires are touched by any lookup site, unit, corner block, or non-arithmetic helper
of `WEXUnlookup.rowC` or `WEXFast.rowCF`, and all thirty are clean (`false`) at every block
boundary. This simultaneously supports:
1. Replacing wire `10000` in the wide-row lookup path bank with `14848` (-1 qubit, 0 T-cost).
2. Hosting `14877, 14876, 14875, 14874` on untouched flag/finite wires during `arithS`/`SquareOB5`. -/

namespace ShorECDLP.Entrant.PoolHost
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup PathShare
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant ECDSAAdd.Arithmetic.CompressedPointDialog
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-- Dialog-pool positions 733..762 (`14848..14877`): clean pool wires unused outside `arithS`/`SquareOB5`. -/
def poolBand : List Wire := List.range' 14848 30

theorem mem_poolBand (w : Wire) : w ∈ poolBand ↔ 14848 ≤ w ∧ w < 14878 := by
  simp only [poolBand, List.mem_range'_1]

theorem poolBand_pool : InPool poolBand := by
  intro q hq
  rw [mem_poolBand] at hq
  have hp : streamLayout.dialogPool = ((List.range' 4115 5699).map streamWire).take 2613 := rfl
  rw [hp, List.mem_iff_getElem]
  refine ⟨q - 14115, by
    simp only [List.length_take, List.length_map, List.length_range']
    rw [Nat.min_eq_left (by norm_num)]
    dsimp only [Wire] at hq
    omega, ?_⟩
  simp only [List.getElem_take, List.getElem_map, List.getElem_range']
  unfold streamWire
  dsimp only [Wire] at *
  split_ifs <;> omega

def okBand (w : Wire) : Bool := Nat.blt w 14848 || Nat.ble 14878 w

theorem okBand_sound {w : Wire} (h : okBand w = true) : w ∉ poolBand := by
  rw [mem_poolBand]
  simp only [okBand, Bool.or_eq_true, Nat.blt_eq, Nat.ble_eq] at h
  dsimp only [Wire] at *
  omega

def progAvoidB (p : ECDSAAdd.Program) : Bool :=
  p.all fun i => (instrList i).all okBand

def avoidWB {n} : WInstr n → Bool
  | .literal p => progAvoidB p
  | .lookup c ps => (portTargets ps).all okBand && c.all okBand

theorem progAvoidB_sound (p : ECDSAAdd.Program) (h : progAvoidB p = true) :
    ∀ w ∈ poolBand, w ∉ ECDSAAdd.wires p := by
  intro w hw hm
  induction p with
  | nil => simp [ECDSAAdd.wires] at hm
  | cons i p ih =>
    simp only [progAvoidB, List.all_cons, Bool.and_eq_true] at h
    simp only [ECDSAAdd.wires, Finset.mem_union] at hm
    rcases hm with hm | hm
    · exact okBand_sound (List.all_eq_true.mp h.1 w (instr_mem i w hm)) hw
    · exact ih h.2 hm

theorem poolBand_not_of (L : List Wire) (hL : L.all okBand = true) :
    ∀ w ∈ poolBand, w ∉ L := by
  intro w hw hm
  exact okBand_sound (List.all_eq_true.mp hL w hm) hw

def AvoidsB (code : WCode 32768) : Prop :=
  (∀ w ∈ poolBand, ∀ p, WInstr.literal p ∈ code → w ∉ ECDSAAdd.wires p) ∧
    (∀ w ∈ poolBand, ∀ c ps, WInstr.lookup c ps ∈ code → w ∉ portTargets ps ∧ ∀ q ∈ c, q ≠ w)

theorem avoidsB_append {a b : WCode 32768} (ha : AvoidsB a) (hb : AvoidsB b) : AvoidsB (a ++ b) := by
  refine ⟨fun w hw p hp => ?_, fun w hw c ps hp => ?_⟩
  · rcases List.mem_append.mp hp with h | h
    · exact ha.1 w hw p h
    · exact hb.1 w hw p h
  · rcases List.mem_append.mp hp with h | h
    · exact ha.2 w hw c ps h
    · exact hb.2 w hw c ps h

theorem avoidsB_sub {a b : WCode 32768} (h : ∀ i ∈ a, i ∈ b) (hb : AvoidsB b) : AvoidsB a :=
  ⟨fun w hw p hp => hb.1 w hw p (h _ hp), fun w hw c ps hp => hb.2 w hw c ps (h _ hp)⟩

theorem avoidsB_lit (p : ECDSAAdd.Program) (h : ∀ w ∈ poolBand, w ∉ ECDSAAdd.wires p) :
    AvoidsB (wLiteral (n := 32768) p) := by
  refine ⟨fun w hw q hq => ?_, fun w hw c ps hp => ?_⟩
  · simp only [wLiteral, List.mem_singleton, WInstr.literal.injEq] at hq
    rw [hq]; exact h w hw
  · simp [wLiteral] at hp

theorem avoidsB_lookup {c : Option Wire} {ps : List (LookupPort 32768)}
    (ht : ∀ w ∈ poolBand, w ∉ portTargets ps) (hc : ∀ w ∈ poolBand, ∀ q ∈ c, q ≠ w) :
    AvoidsB [.lookup c ps] := by
  refine ⟨fun _ _ _ hp => by simp at hp, fun w hw c' ps' hp => ?_⟩
  simp only [List.mem_singleton, WInstr.lookup.injEq] at hp
  obtain ⟨rfl, rfl⟩ := hp
  exact ⟨ht w hw, hc w hw⟩

theorem avoidsB_of_all (code : WCode 32768) (h : code.all (avoidW poolBand) = true) : AvoidsB code := by
  refine ⟨fun w hw p hp => progAvoid_sound poolBand p (List.all_eq_true.mp h _ hp) w hw,
    fun w hw c ps hp => ?_⟩
  obtain ⟨h1, h2⟩ := avoidW_lookup poolBand c ps (List.all_eq_true.mp h _ hp)
  exact ⟨h1 w hw, fun q hq e => h2 q hq (e ▸ hw)⟩

theorem avoidsB_of_band (code : WCode 32768) (h : code.all avoidWB = true) : AvoidsB code := by
  refine ⟨fun w hw p hp => progAvoidB_sound p (List.all_eq_true.mp h _ hp) w hw,
    fun w hw c ps hp => ?_⟩
  have h0 := List.all_eq_true.mp h _ hp
  simp only [avoidWB, Bool.and_eq_true] at h0
  refine ⟨fun ht => okBand_sound (List.all_eq_true.mp h0.1 w ht) hw, fun q hq e => ?_⟩
  cases c with
  | none => simp at hq
  | some q' =>
    simp only [Option.mem_def, Option.some.injEq] at hq
    subst hq
    simp only [Option.all_some] at h0
    exact okBand_sound h0.2 (e ▸ hw)

theorem avoidsB_frame (read : ConstantBit 32768 → Bool) (a : Nat) (code : WCode 32768) (h : AvoidsB code)
    (m : List Bool) (st : ECDSAAdd.State) (w : Wire) (hw : w ∈ poolBand) :
    (ECDSAAdd.run ((specialize code a).instantiate read) m st).basis w = st.basis w := by
  induction code generalizing m st with
  | nil => simp [specialize, ECDSAAdd.ShorPort.Tmpl.instantiate, ECDSAAdd.run]
  | cons i code ih =>
    have ht : AvoidsB code := ⟨fun u hu p hp => h.1 u hu p (List.mem_cons_of_mem _ hp),
      fun u hu c ps hp => h.2 u hu c ps (List.mem_cons_of_mem _ hp)⟩
    rw [show i :: code = [i] ++ code from rfl, specialize_append, ECDSAAdd.ShorPort.Tmpl.instantiate_append,
      ECDSAAdd.run_append, ih ht]
    apply ECDSAAdd.run_preserves_outside _ _ _ w
    cases i with
    | literal p =>
      simp only [specialize, List.flatMap_cons, List.flatMap_nil, List.append_nil, WInstr.specialize,
        ECDSAAdd.ShorPort.Tmpl.instantiate_lit]
      exact h.1 w hw p (by simp)
    | lookup c ps =>
      simp only [specialize, List.flatMap_cons, List.flatMap_nil, List.append_nil, WInstr.specialize]
      obtain ⟨hT, hC⟩ := h.2 w hw c ps (by simp)
      exact lookup_frame read c ps a w hT hC

theorem poolBand_scrAll : ∀ w ∈ poolBand, w ∉ WEX.scrAllWires := by
  rw [WEX.scrAllWires, WEX.scrWires, pbPairWires_eq, pbShortWires_eq, pbExtraWires_eq]
  exact poolBand_not_of _ (by decide +kernel)

theorem poolBand_yWires : ∀ w ∈ poolBand, w ∉ WEX.yWires := by
  intro w hw h
  have h1 := (WEX.yWires_bounds w h).2
  rw [mem_poolBand] at hw
  dsimp only [Wire] at *
  omega

theorem root_ne_poolBand : ∀ w ∈ poolBand, ∀ q ∈ (some windowRoot : Option Wire), q ≠ w := by
  intro w hw q hq
  rw [Option.mem_def, Option.some.injEq] at hq
  subst hq
  rw [mem_poolBand] at hw
  unfold windowRoot
  dsimp only [Wire] at *
  omega

theorem scrDLookup_avoidsB : AvoidsB [WInstr.lookup (some windowRoot) (WEX.scrDPorts probeRows)] :=
  avoidsB_lookup (by rw [WEX.scrDPorts_targets]; exact poolBand_scrAll) root_ne_poolBand

theorem siteLookup_avoidsB : AvoidsB [WInstr.lookup (some windowRoot) (sitePorts probeRows)] :=
  avoidsB_lookup (by rw [sitePorts_targets]; exact poolBand_scrAll) root_ne_poolBand

theorem cornerLoad_avoidsB : AvoidsB [WInstr.lookup (some windowRoot) (WEX.cornerPorts probeRows)] := by
  refine avoidsB_lookup ?_ root_ne_poolBand
  rw [WEX.cornerPorts_targets]
  intro w hw hm
  rcases List.mem_append.mp hm with h | h
  · exact poolBand_scrAll w hw h
  · exact poolBand_yWires w hw h

theorem yLookup_avoidsB : AvoidsB [WInstr.lookup (some windowRoot) (WEX.yPorts probeRows)] :=
  avoidsB_lookup (by rw [WEX.yPorts_targets]; exact poolBand_yWires) root_ne_poolBand

theorem scrNegP_avoidB : ∀ w ∈ poolBand, w ∉ ECDSAAdd.wires WEX.scrNegP :=
  WEX.neg_disjoint (negateYLayout streamLayout) streamLayout.core.equalNegY ECDSAAdd.p SquareReduction.c
    (negateYLayout_widths streamLayout streamLayout_widths).2 poolBand (poolBand_not_of _ (by decide +kernel))

theorem sfxCC_avoidsB : AvoidsB WEX.sfxCC := by
  simp only [WEX.sfxCC, WEX.scrDWires, pbShortWires_eq, pbExtraWires_eq]
  exact avoidsB_of_band _ (by decide +kernel)

theorem streamLayout_infSel : streamLayout.infinitySelect = 19816 := rfl
theorem streamLayout_dblSel : streamLayout.doubleSelect = 19815 := rfl
theorem streamLayout_genSel : streamLayout.genericSelect = 19814 := rfl
theorem streamLayout_eqX : streamLayout.core.equalX = 14111 := rfl
theorem streamLayout_eqNegY : streamLayout.core.equalNegY = 14112 := rfl
theorem streamLayout_gen : streamLayout.core.generic = 14113 := rfl
theorem streamLayout_dbl : streamLayout.core.double = 14114 := rfl
theorem streamLayout_fin : streamLayout.point.finite = 838 := rfl
theorem streamLayout_yLow : yLow streamLayout = 580 := rfl

private theorem zeroPorts_mem (xs ws : List Wire) (b : ZeroBit) (h : b ∈ zeroPorts xs ws) :
    b.input ∈ xs ∧ b.work ∈ ws := by
  induction xs generalizing ws with
  | nil => simp [zeroPorts] at h
  | cons x xs ih =>
    cases ws with
    | nil => simp [zeroPorts] at h
    | cons w ws =>
      simp only [zeroPorts, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨List.mem_cons_self, List.mem_cons_self⟩
      · obtain ⟨h1, h2⟩ := ih ws h
        exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩

private theorem poolBand_dialogPool_take (k : Nat) (hk : k ≤ 733) :
    ∀ w ∈ poolBand, w ∉ streamLayout.dialogPool.take k := by
  intro w hw hm
  have hp : streamLayout.dialogPool = ((List.range' 4115 5699).map streamWire).take 2613 := rfl
  rw [hp, List.take_take, List.mem_iff_getElem] at hm
  obtain ⟨i, hi, rfl⟩ := hm
  simp only [List.length_take, List.length_map, List.length_range'] at hi
  simp only [List.getElem_take, List.getElem_map, List.getElem_range'] at hw
  rw [mem_poolBand] at hw
  unfold streamWire at hw
  dsimp only [Wire] at *
  split_ifs at hw <;> omega

private theorem poolBand_point_x : ∀ w ∈ poolBand, w ∉ streamLayout.point.x := by
  intro w hw hm
  rw [streamLayout_point] at hm
  simp only [List.mem_range'_1] at hm
  rw [mem_poolBand] at hw
  dsimp only [Wire] at *
  omega

private theorem poolBand_point_y : ∀ w ∈ poolBand, w ∉ streamLayout.point.y := by
  intro w hw hm
  rw [streamLayout_point] at hm
  simp only [List.mem_range'_1] at hm
  rw [mem_poolBand] at hw
  dsimp only [Wire] at *
  omega

private theorem wZeroWith_avoidsB (tail : Wire → WCode 32768) (ht : ∀ u, u ∉ poolBand → AvoidsB (tail u))
    (c : Wire) (hc : c ∉ poolBand) (bs : List ZeroBit)
    (hbs : ∀ b ∈ bs, b.input ∉ poolBand ∧ b.work ∉ poolBand) :
    AvoidsB (wZeroWith tail c bs) := by
  induction bs generalizing c with
  | nil => exact ht c hc
  | cons b bs ih =>
    obtain ⟨hbi, hbw⟩ := hbs b List.mem_cons_self
    have hbs' : ∀ b' ∈ bs, b'.input ∉ poolBand ∧ b'.work ∉ poolBand :=
      fun b' hb' => hbs b' (List.mem_cons_of_mem _ hb')
    rw [wZeroWith]
    refine avoidsB_append (avoidsB_append ?_ (ih b.work hbw hbs')) ?_
    · refine avoidsB_lit _ fun w hw hm => ?_
      simp only [chainAnd, ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton, Finset.notMem_empty, or_false] at hm
      rcases hm with rfl | (rfl | rfl | rfl) | rfl
      · exact hbi hw
      · exact hc hw
      · exact hbi hw
      · exact hbw hw
      · exact hbi hw
    · refine avoidsB_lit _ fun w hw hm => ?_
      simp only [chainErase, ECDSAAdd.wires, ECDSAAdd.Instr.wires, ECDSAAdd.correctionWires,
        Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, or_false] at hm
      rcases hm with rfl | (rfl | rfl | rfl) | rfl
      · exact hbi hw
      · exact hbw hw
      · exact hc hw
      · exact hbi hw
      · exact hbi hw

theorem scrDMiddle_avoidsB : AvoidsB WEX.scrDMiddle := by
  have hPairW : ∀ w ∈ poolBand, w ∉ WEX.scrPairWires := fun w hw h =>
    poolBand_scrAll w hw (by simp [WEX.scrAllWires, WEX.scrWires, h])
  have hShortW : ∀ w ∈ poolBand, w ∉ WEX.scrShortWires := fun w hw h =>
    poolBand_scrAll w hw (by simp [WEX.scrAllWires, WEX.scrWires, h])
  have hPairT : ∀ w ∈ poolBand, w ∉ WEX.scrPairTargets := by
    intro w hw h
    simp only [WEX.scrPairTargets, List.mem_cons, List.mem_append, List.mem_singleton,
      List.not_mem_nil, or_false, streamLayout_fin, streamLayout_yLow] at h
    rcases h with (rfl | h) | rfl
    · rw [mem_poolBand] at hw; dsimp only [Wire] at *; omega
    · exact poolBand_point_x w hw h
    · rw [mem_poolBand] at hw; dsimp only [Wire] at *; omega
  have hShortT : ∀ w ∈ poolBand, w ∉ WEX.scrShortTargets := by
    intro w hw h
    simp only [WEX.scrShortTargets, List.mem_cons, List.mem_append, streamLayout_fin] at h
    rcases h with (rfl | h) | h
    · rw [mem_poolBand] at hw; dsimp only [Wire] at *; omega
    · exact poolBand_point_x w hw h
    · exact poolBand_point_y w hw (List.mem_of_mem_take h)
  have hCxPair : ∀ w ∈ poolBand, w ∉ ECDSAAdd.wires (cxList WEX.scrPairWires WEX.scrPairTargets) := by
    intro w hw h
    rcases cxList_wires _ _ _ h with h | h
    · exact hPairW w hw h
    · exact hPairT w hw h
  have hCxShort : ∀ w ∈ poolBand, w ∉ ECDSAAdd.wires (cxList WEX.scrShortWires WEX.scrShortTargets) := by
    intro w hw h
    rcases cxList_wires _ _ _ h with h | h
    · exact hShortW w hw h
    · exact hShortT w hw h
  have hZW : AvoidsB (wZeroWith (wPairTailBare (yLow streamLayout) streamLayout.infinitySelect streamLayout.core.equalNegY)
      streamLayout.control (pairPorts streamLayout)) := by
    refine wZeroWith_avoidsB _ ?_ _ ?_ _ ?_
    · intro u hu
      refine avoidsB_lit _ fun w hw hm => ?_
      simp only [wPairTailBare, ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton, Finset.notMem_empty, or_false, streamLayout_yLow, streamLayout_infSel,
        streamLayout_eqNegY] at hm
      rw [mem_poolBand] at hw
      dsimp only [Wire, ECDSAAdd.Wire] at *
      rcases hm with (rfl | rfl | rfl) | rfl | (rfl | rfl | rfl)
      · exact hu ((mem_poolBand w).mpr hw)
      · omega
      · omega
      · omega
      · exact hu ((mem_poolBand w).mpr hw)
      · omega
      · omega
    · rw [mem_poolBand, streamLayout_control]; dsimp only [Wire]; omega
    · intro b hb
      obtain ⟨h1, h2⟩ := zeroPorts_mem _ _ b hb
      refine ⟨fun hm => ?_, fun hm => poolBand_dialogPool_take 257 (by omega) _ hm h2⟩
      simp only [ECDSAAdd.Entrant.pairSrc, List.mem_cons, streamLayout_fin] at h1
      rcases h1 with h1 | h1
      · rw [h1, mem_poolBand] at hm; dsimp only [Wire] at *; omega
      · exact poolBand_point_x _ hm h1
  have hScrP2 : ∀ w ∈ poolBand, w ∉ ECDSAAdd.wires WEX.scrP2 := by
    intro w hw hm
    rw [WEX.scrP2, zeroControlled_wires] at hm
    simp only [List.mem_toFinset, List.mem_cons, List.mem_flatMap, streamLayout_dbl, streamLayout_dblSel] at hm
    rcases hm with rfl | rfl | ⟨b, hb, hbw⟩
    · rw [mem_poolBand] at hw; dsimp only [Wire] at *; omega
    · rw [mem_poolBand] at hw; dsimp only [Wire] at *; omega
    · obtain ⟨h1, h2⟩ := zeroPorts_mem _ _ b hb
      simp only [ZeroBit.wires, List.mem_cons, List.not_mem_nil, or_false] at hbw
      rcases hbw with rfl | rfl
      · simp only [shortSrc, List.mem_cons, List.mem_append, streamLayout_fin] at h1
        rcases h1 with (h1 | h1) | h1
        · rw [h1, mem_poolBand] at hw; dsimp only [Wire] at *; omega
        · exact poolBand_point_x _ hw h1
        · exact poolBand_point_y _ hw (List.mem_of_mem_take h1)
      · exact poolBand_dialogPool_take 258 (by omega) _ hw h2
  rw [WEX.scrDMiddle]
  refine avoidsB_append (avoidsB_append (avoidsB_append (avoidsB_append (avoidsB_append
    (avoidsB_lit _ hCxPair) hZW) ?_) (avoidsB_lit _ hCxShort)) (avoidsB_lit _ hScrP2)) (avoidsB_lit _ hCxShort)
  refine avoidsB_lit _ fun w hw hm => ?_
  simp only [ECDSAAdd.wires_append, ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.mem_union,
    Finset.mem_singleton, Finset.notMem_empty, or_false, streamLayout_yLow] at hm
  rcases hm with hm | rfl
  · exact hCxPair w hw hm
  · rw [mem_poolBand] at hw; dsimp only [Wire] at *; omega

theorem gf_avoidB : ∀ w ∈ poolBand, w ∉ ECDSAAdd.wires (pointDialogGenericFlag streamLayout) :=
  progAvoidB_sound _ (by decide +kernel)

theorem scrD_avoidsB : AvoidsB scrDSite.code := by
  have hP : AvoidsB (wLiteral (n := 32768) WEX.scrNegP) := avoidsB_lit _ scrNegP_avoidB
  have hNegE : AvoidsB (wLiteral (n := 32768) WEX.scrNegE) := avoidsB_lit _ fun w hw hm => by
    simp only [WEX.scrNegE, ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, Finset.notMem_empty, or_false, streamLayout_genSel, streamLayout_eqNegY] at hm
    rw [mem_poolBand] at hw; dsimp only [Wire] at *; omega
  have hSw1 : AvoidsB (wLiteral (n := 32768) WEX.scrSw1) := avoidsB_lit _ fun w hw hm => by
    simp only [WEX.scrSw1, ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, Finset.notMem_empty, or_false, streamLayout_dblSel, streamLayout_eqNegY] at hm
    rw [mem_poolBand] at hw; dsimp only [Wire] at *; omega
  have hW1 : AvoidsB (wLiteral (n := 32768) WEX.scrW1) := avoidsB_lit _ fun w hw hm => by
    simp only [WEX.scrW1, ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, Finset.notMem_empty, or_false, streamLayout_infSel, streamLayout_dblSel,
      streamLayout_genSel, streamLayout_eqNegY] at hm
    rw [mem_poolBand] at hw; dsimp only [Wire] at *; omega
  have hW2 : AvoidsB (wLiteral (n := 32768) WEX.scrW2) := avoidsB_lit _ fun w hw hm => by
    simp only [WEX.scrW2, ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, Finset.notMem_empty, or_false, streamLayout_infSel, streamLayout_dblSel,
      streamLayout_genSel, streamLayout_eqNegY] at hm
    rw [mem_poolBand] at hw; dsimp only [Wire] at *; omega
  have hCP : AvoidsB [WInstr.lookup (some streamLayout.doubleSelect) (WEX.scrCPorts probeRows)] := by
    refine avoidsB_lookup ?_ ?_
    · intro w hw hm
      simp only [WEX.scrCPorts, portTargets, List.map_cons, List.map_append, List.mem_cons, List.mem_append,
        streamLayout_fin] at hm
      rcases hm with (rfl | hm) | hm
      · rw [mem_poolBand] at hw; dsimp only [Wire] at *; omega
      · exact poolBand_point_x w hw (by
          change w ∈ portTargets (indexedPorts streamLayout.point.x (wFields probeRows .x) true) at hm
          rwa [indexed_targets] at hm)
      · exact poolBand_point_y w hw (by
          change w ∈ portTargets (indexedPorts streamLayout.point.y (wFields probeRows .y) true) at hm
          rwa [indexed_targets] at hm)
    · intro w hw q hq
      rw [Option.mem_def, Option.some.injEq] at hq
      subst hq; rw [streamLayout_dblSel, mem_poolBand] at *; dsimp only [Wire] at *; omega
  have hGF : AvoidsB (wLiteral (n := 32768) (pointDialogGenericFlag streamLayout)) := avoidsB_lit _ gf_avoidB
  rw [scrDSite_code, WEX.sfxMidF, WEX.cornersE_split]
  repeat' (with_reducible apply avoidsB_append)
  all_goals first
    | (with_reducible exact hP)
    | exact scrDLookup_avoidsB
    | exact sfxCC_avoidsB
    | exact scrDMiddle_avoidsB
    | (with_reducible exact hNegE)
    | (with_reducible exact hSw1)
    | (with_reducible exact hW1)
    | (with_reducible exact hW2)
    | exact hCP
    | (with_reducible exact hGF)

theorem cornerNeg_avoidsB : AvoidsB WEX.cornerNeg :=
  avoidsB_sub (fun i hi => sfxMid_in_scrD _ (WEX.cornerNeg_sub i hi)) scrD_avoidsB

theorem scrCWrite_avoidB : ∀ w ∈ poolBand, w ∉ ECDSAAdd.wires WEX.scrCWrite := by
  have h1 : ∀ w ∈ poolBand, w ∉ [streamLayout.doubleSelect] := by
    intro w hw hm; simp only [streamLayout_dblSel, List.mem_singleton] at hm
    subst hm; rw [mem_poolBand] at hw; dsimp only [Wire] at *; omega
  have h2 : ∀ w ∈ poolBand, w ∉ WEX.cSources := by
    rw [WEX.cSources, pbPairWires_eq, WEX.yWires]
    exact poolBand_not_of _ (by decide +kernel)
  have h3 : ∀ w ∈ poolBand, w ∉ WEX.scrDTargets := poolBand_not_of _ (by decide +kernel)
  intro w hw hm
  rcases ccxList_wires _ _ _ _ hm with h | h | h
  · exact h1 w hw (by simp [h])
  · exact h2 w hw h
  · exact h3 w hw h

theorem unit1_avoidsB : AvoidsB WEXUnlookup.cornerUnit₁.code := by
  rw [WEXUnlookup.cornerUnit₁_code, WEX.cornerUnit₁, WEX.cornerPre₁]
  refine avoidsB_append (avoidsB_append cornerLoad_avoidsB ?_) yLookup_avoidsB
  refine ⟨fun w hw p hp => ?_, fun w hw c ps hp => ?_⟩
  · rcases WEX.cornerA1_mem _ hp with h | h
    · exact scrD_avoidsB.1 w hw p (sfxMid_in_scrD _ h)
    · cases h
      exact scrCWrite_avoidB w hw
  · rcases WEX.cornerA1_mem _ hp with h | h
    · exact scrD_avoidsB.2 w hw c ps (sfxMid_in_scrD _ h)
    · cases h

theorem unit2_avoidsB : AvoidsB WEXUnlookup.cornerUnit₂.code := by
  apply avoidsB_sub _ scrD_avoidsB
  intro i hi
  rw [WEXUnlookup.cornerUnit₂_code, WEX.cornerUnit₂] at hi
  rcases List.mem_append.mp hi with h | h
  · exact sfxMid_in_scrD _ (WEX.cornerA2_sub _ h)
  · rw [List.mem_singleton.mp h]
    exact WEXUnlookup.scrD_unload_mem

theorem poolBand_flip : ∀ w ∈ poolBand, w ∉ ECDSAAdd.wires ([.X 838] : ECDSAAdd.Program) := by
  intro w hw hm
  simp [ECDSAAdd.wires, ECDSAAdd.Instr.wires] at hm
  subst hm
  rw [mem_poolBand] at hw
  dsimp only [Wire] at *
  omega

theorem poolBand_head : ∀ w ∈ poolBand, w ∉ ECDSAAdd.wires scrHeadProgram := by
  intro w hw hm
  have hs : scrHeadProgram = [.CX streamLayout.control streamLayout.core.double] ++
      [.CX streamLayout.control streamLayout.core.equalX] ++
      zeroFlag streamLayout.point.finite streamLayout.control streamLayout.infinitySelect := rfl
  rw [hs, zeroFlag] at hm
  simp only [ECDSAAdd.wires_append, ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.mem_union,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, or_false,
    streamLayout_control, streamLayout_dbl, streamLayout_eqX, streamLayout_fin, streamLayout_infSel] at hm
  rw [mem_poolBand] at hw; dsimp only [Wire, ECDSAAdd.Wire] at *; omega

attribute [local irreducible] Arith.padding in
theorem sfxTailF_avoidsB : AvoidsB WEX.sfxTailF := by
  rw [WEX.sfxTailF]
  refine avoidsB_append (avoidsB_append (avoidsB_append ?_ ?_) ?_) ?_
  · refine avoidsB_lit _ fun w hw hm => ?_
    simp only [zeroFlag, ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, Finset.notMem_empty, or_false, streamLayout_fin, streamLayout_control,
      streamLayout_genSel] at hm
    rw [mem_poolBand] at hw; dsimp only [Wire] at *; omega
  · refine avoidsB_lit _ fun w hw hm => ?_
    simp only [ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, Finset.notMem_empty, or_false, streamLayout_control, streamLayout_eqX] at hm
    rw [mem_poolBand] at hw; dsimp only [Wire] at *; omega
  · refine avoidsB_lit _ fun w hw hm => ?_
    simp only [ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, Finset.notMem_empty, or_false, streamLayout_control, streamLayout_dbl] at hm
    rw [mem_poolBand] at hw; dsimp only [Wire] at *; omega
  · refine avoidsB_lit _ fun w hw hm => ?_
    have hq : w = streamLayout.core.poolWire 0 :=
      Finset.mem_singleton.mp (Arith.padding_support (streamLayout.core.poolWire 0) 50694 hm)
    rw [streamPool_at 0 (by omega)] at hq
    rw [mem_poolBand] at hw; dsimp only [Wire] at *; omega

theorem flip_avoidsB : AvoidsB (wLiteral (n := 32768) [.X 838]) := avoidsB_lit _ poolBand_flip

theorem band_not_poolBand (w : Nat) (h : newBand w) : w ∉ poolBand := by
  rw [mem_poolBand]
  unfold newBand at h
  dsimp only [Wire] at *
  omega

theorem pair1Prog_avoidB : ∀ w ∈ poolBand, w ∉ ECDSAAdd.wires pair1Prog :=
  wires_avoid_of pair1Prog_subset (fun w hw h => band_not_poolBand w (lists_band.1 w h) hw)

theorem pair2Prog_avoidB : ∀ w ∈ poolBand, w ∉ ECDSAAdd.wires pair2Prog :=
  wires_avoid_of pair2Prog_subset (fun w hw h => band_not_poolBand w (lists_band.2.1 w h) hw)

theorem zrep_avoidB : ∀ w ∈ poolBand, w ∉ ECDSAAdd.wires (ECDSAAdd.Frontier.zrep streamLayout) := by
  intro w hw hm
  rcases ECDSAAdd.Frontier.zrep_wires streamLayout _ hm with h | h
  · rw [streamLayout_fin] at h; subst h; rw [mem_poolBand] at hw; dsimp only [Wire] at *; omega
  · simp only [streamLayout_point, List.mem_range'_1] at h
    rw [mem_poolBand] at hw
    dsimp only [Wire] at *
    omega

private theorem avoidsB_litConcat (code : WCode 32768) (h : AvoidsB code) :
    ∀ w ∈ poolBand, w ∉ ECDSAAdd.wires (WEX.litConcat code) := by
  induction code with
  | nil => intro w _ hm; simp [WEX.litConcat, ECDSAAdd.wires] at hm
  | cons i code ih =>
    have ht : AvoidsB code := ⟨fun u hu p hp => h.1 u hu p (List.mem_cons_of_mem _ hp),
      fun u hu c ps hp => h.2 u hu c ps (List.mem_cons_of_mem _ hp)⟩
    cases i with
    | literal p =>
      intro w hw hm
      simp only [WEX.litConcat, ECDSAAdd.wires_append, Finset.mem_union] at hm
      rcases hm with hm | hm
      · exact h.1 w hw p List.mem_cons_self hm
      · exact ih ht w hw hm
    | lookup c ps =>
      intro w hw hm
      exact ih ht w hw hm

theorem scrInArith_avoidB : ∀ w ∈ poolBand, w ∉ ECDSAAdd.wires scrInArith := by
  apply avoidsB_litConcat WEX.scrInMid
  have hPairW : ∀ w ∈ poolBand, w ∉ WEX.scrPairWires := fun w hw h =>
    poolBand_scrAll w hw (by simp [WEX.scrAllWires, WEX.scrWires, h])
  have hShortW : ∀ w ∈ poolBand, w ∉ WEX.scrShortWires := fun w hw h =>
    poolBand_scrAll w hw (by simp [WEX.scrAllWires, WEX.scrWires, h])
  have hPairT : ∀ w ∈ poolBand, w ∉ WEX.scrPairTargets := by
    intro w hw h
    simp only [WEX.scrPairTargets, List.mem_cons, List.mem_append, List.mem_singleton,
      List.not_mem_nil, or_false, streamLayout_fin, streamLayout_yLow] at h
    rcases h with (rfl | h) | rfl
    · rw [mem_poolBand] at hw; dsimp only [Wire] at *; omega
    · exact poolBand_point_x w hw h
    · rw [mem_poolBand] at hw; dsimp only [Wire] at *; omega
  have hShortT : ∀ w ∈ poolBand, w ∉ WEX.scrShortTargets := by
    intro w hw h
    simp only [WEX.scrShortTargets, List.mem_cons, List.mem_append, streamLayout_fin] at h
    rcases h with (rfl | h) | h
    · rw [mem_poolBand] at hw; dsimp only [Wire] at *; omega
    · exact poolBand_point_x w hw h
    · exact poolBand_point_y w hw (List.mem_of_mem_take h)
  have hCxPair : ∀ w ∈ poolBand, w ∉ ECDSAAdd.wires (cxList WEX.scrPairWires WEX.scrPairTargets) := by
    intro w hw h
    rcases cxList_wires _ _ _ h with h | h
    · exact hPairW w hw h
    · exact hPairT w hw h
  have hCxShort : ∀ w ∈ poolBand, w ∉ ECDSAAdd.wires (cxList WEX.scrShortWires WEX.scrShortTargets) := by
    intro w hw h
    rcases cxList_wires _ _ _ h with h | h
    · exact hShortW w hw h
    · exact hShortT w hw h
  have hZW : AvoidsB (wZeroWith (wPairTailBare (yLow streamLayout) streamLayout.doubleSelect streamLayout.genericSelect)
      streamLayout.control (pairPorts streamLayout)) := by
    refine wZeroWith_avoidsB _ ?_ _ ?_ _ ?_
    · intro u hu
      refine avoidsB_lit _ fun w hw hm => ?_
      simp only [wPairTailBare, ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton, Finset.notMem_empty, or_false, streamLayout_yLow, streamLayout_dblSel,
        streamLayout_genSel] at hm
      rw [mem_poolBand] at hw
      dsimp only [Wire, ECDSAAdd.Wire] at *
      rcases hm with (rfl | rfl | rfl) | rfl | (rfl | rfl | rfl)
      · exact hu ((mem_poolBand w).mpr hw)
      · omega
      · omega
      · omega
      · exact hu ((mem_poolBand w).mpr hw)
      · omega
      · omega
    · rw [mem_poolBand, streamLayout_control]; dsimp only [Wire]; omega
    · intro b hb
      obtain ⟨h1, h2⟩ := zeroPorts_mem _ _ b hb
      refine ⟨fun hm => ?_, fun hm => poolBand_dialogPool_take 257 (by omega) _ hm h2⟩
      simp only [ECDSAAdd.Entrant.pairSrc, List.mem_cons, streamLayout_fin] at h1
      rcases h1 with h1 | h1
      · rw [h1, mem_poolBand] at hm; dsimp only [Wire] at *; omega
      · exact poolBand_point_x _ hm h1
  have hScrInP2 : ∀ w ∈ poolBand, w ∉ ECDSAAdd.wires WEX.scrInP2 := by
    intro w hw hm
    rw [WEX.scrInP2, zeroControlled_wires] at hm
    simp only [List.mem_toFinset, List.mem_cons, List.mem_flatMap, streamLayout_eqX, streamLayout_eqNegY] at hm
    rcases hm with rfl | rfl | ⟨b, hb, hbw⟩
    · rw [mem_poolBand] at hw; dsimp only [Wire] at *; omega
    · rw [mem_poolBand] at hw; dsimp only [Wire] at *; omega
    · obtain ⟨h1, h2⟩ := zeroPorts_mem _ _ b hb
      simp only [ZeroBit.wires, List.mem_cons, List.not_mem_nil, or_false] at hbw
      rcases hbw with rfl | rfl
      · simp only [shortSrc, List.mem_cons, List.mem_append, streamLayout_fin] at h1
        rcases h1 with (h1 | h1) | h1
        · rw [h1, mem_poolBand] at hw; dsimp only [Wire] at *; omega
        · exact poolBand_point_x _ hw h1
        · exact poolBand_point_y _ hw (List.mem_of_mem_take h1)
      · exact poolBand_dialogPool_take 258 (by omega) _ hw h2
  rw [WEX.scrInMid]
  refine avoidsB_append (avoidsB_append (avoidsB_append (avoidsB_append (avoidsB_append
    (avoidsB_lit _ hCxPair) hZW) ?_) (avoidsB_lit _ hCxShort)) (avoidsB_lit _ hScrInP2)) (avoidsB_lit _ hCxShort)
  refine avoidsB_lit _ fun w hw hm => ?_
  simp only [ECDSAAdd.wires_append, ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.mem_union,
    Finset.mem_singleton, Finset.notMem_empty, or_false, streamLayout_yLow] at hm
  rcases hm with hm | rfl
  · exact hCxPair w hw hm
  · rw [mem_poolBand] at hw; dsimp only [Wire] at *; omega

theorem site1Arith_avoidB : ∀ w ∈ poolBand, w ∉ ECDSAAdd.wires site1Arith := by
  intro w hw
  simp only [site1Arith, ECDSAAdd.wires_append, Finset.mem_union, not_or]
  exact ⟨⟨⟨scrInArith_avoidB w hw, gf_avoidB w hw⟩, zrep_avoidB w hw⟩, pair1Prog_avoidB w hw⟩

theorem site1_avoidsB : AvoidsB (site1 probeRows).code := by
  rw [site1_code]
  exact avoidsB_append (a := [_]) siteLookup_avoidsB
    (avoidsB_append (a := [_]) (avoidsB_lit site1Arith site1Arith_avoidB) siteLookup_avoidsB)

theorem site2Lookup_avoidsB : AvoidsB [WInstr.lookup (some windowRoot) (site2Ports probeRows)] :=
  avoidsB_lookup (by rw [site2Ports_targets]; exact fun w hw h => poolBand_scrAll w hw (site2_sub _ h)) root_ne_poolBand

theorem site2_avoidsB : AvoidsB (site2 probeRows).code := by
  rw [site2_code]
  exact avoidsB_append (a := [_]) site2Lookup_avoidsB
    (avoidsB_append (a := [_]) (avoidsB_lit pair2Prog pair2Prog_avoidB) site2Lookup_avoidsB)

theorem triple_avoidsB : AvoidsB (constSite streamLayout streamLayout.point.x (wFields probeRows .tripleX)).code := by
  have hw : ∀ w ∈ poolBand, w ∉ (streamLayout.recoveryConstant streamLayout.point.x).wires :=
    poolBand_not_of _ (by decide +kernel)
  have ht : ∀ w ∈ poolBand, w ∉ (streamLayout.recoveryConstant streamLayout.point.x).src :=
    poolBand_not_of _ (by decide +kernel)
  have hg : ∀ w ∈ poolBand, streamLayout.core.generic ≠ w := fun w hwm h =>
    poolBand_not_of [streamLayout.core.generic] (by decide +kernel) w hwm (by simp [h])
  rw [constSite_code]
  refine ⟨fun w hwm p hp => ?_, fun w hwm c ps hp => ?_⟩
  · rcases List.mem_cons.mp hp with h | h
    · cases h
    rcases List.mem_cons.mp h with h | h
    · cases h
      exact wires_avoid_of (MeasuredCanonicalModLayout.program_wires_subset _ _ _) hw w hwm
    · cases List.mem_singleton.mp h
  · have hp' : c = some streamLayout.core.generic ∧
        ps = indexedPorts (streamLayout.recoveryConstant streamLayout.point.x).src (wFields probeRows .tripleX) true := by
      rcases List.mem_cons.mp hp with h | h
      · exact WInstr.lookup.inj h
      rcases List.mem_cons.mp h with h | h
      · cases h
      · exact WInstr.lookup.inj (List.mem_singleton.mp h)
    obtain ⟨rfl, rfl⟩ := hp'
    refine ⟨fun hm => ht w hwm (by rw [indexed_targets] at hm; exact hm), fun q hq => ?_⟩
    rw [Option.mem_def, Option.some.injEq] at hq
    subst hq
    exact hg w hwm

theorem rowC_unit_avoidsB (u : UnitSite 32768) (hu : Block2.unit u ∈ WEXUnlookup.rowC) : AvoidsB u.code := by
  rcases List.mem_append.mp hu with h | h
  · obtain ⟨c, hc, he⟩ := List.mem_map.mp h
    cases c with
    | plain code => cases he
    | masked site =>
      cases he
      rcases rowL_masked_cases site (WEXUnlookup.rowHead_sub _ hc) with rfl | rfl | rfl | rfl
      · exact site1_avoidsB
      · exact triple_avoidsB
      · exact site2_avoidsB
      · exact scrD_avoidsB
  · simp only [WEXUnlookup.rowPost3, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or,
      Block2.unit.injEq] at h
    rcases h with rfl | rfl
    · exact unit1_avoidsB
    · exact unit2_avoidsB

theorem rowPost3_cleanB (read : ConstantBit 32768 → Bool) (a : Nat) (t : ECDSAAdd.State)
    (ht : Clean poolBand t.basis) : CodeClean2 read poolBand a WEXUnlookup.rowPost3 t := by
  rw [WEXUnlookup.rowPost3]
  refine ⟨trivial, fun m₁ _ => ⟨?_, fun m₂ _ => ⟨?_, fun _ _ => ⟨trivial, fun _ _ => ⟨trivial, fun _ _ => trivial⟩⟩⟩⟩⟩
  · intro w hw
    rw [blockReference2, Block2.code, avoidsB_frame read a WEX.cornerNeg cornerNeg_avoidsB m₁ t w hw]
    exact ht w hw
  · intro w hw
    rw [blockReference2, Block2.code, avoidsB_frame read a WEXUnlookup.cornerUnit₁.code unit1_avoidsB m₂ _ w hw,
      blockReference2, Block2.code, avoidsB_frame read a WEX.cornerNeg cornerNeg_avoidsB m₁ t w hw]
    exact ht w hw

theorem rowC_clean_poolBand (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (a : Nat) (s : BasisState) (hs : liveReady s) :
    CodeClean2 (readConstant coeffs Q) poolBand a WEXUnlookup.rowC ⟨false, s⟩ := by
  have h := rowL_clean poolBand poolBand_pool poolBand_flip poolBand_head coeffs Q hQ hn a s hs
  rw [WEXUnlookup.rowL_eq] at h
  obtain ⟨h1, h2⟩ := clean_split _ _ _ _ _ _ h
  rw [WEXUnlookup.rowC]
  apply clean2_append _ _ _ _ _ _ (clean_map _ _ _ _ _ h1)
  intro m hm
  rw [reference2_map] at hm ⊢
  have h3 := h2 m hm
  rw [WEXUnlookup.rowPost] at h3
  exact rowPost3_cleanB _ _ _ h3.1

theorem poolBand_clean_in_rowCF (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (a : Nat) (s : BasisState) (hs : liveReady s) :
    CodeClean2 (readConstant coeffs Q) poolBand a (WEXFast.fforget WEXFast.rowCF) ⟨false, s⟩ := by
  rw [WEXFast.fforget_rowCF]
  exact rowC_clean_poolBand coeffs Q hQ hn a s hs

/-! ### Extending 15-bit placed instructions to 16-bit bank with extra path wire `14848` -/

def wideBits : List Wire := WEX.windowBits ++ [871]
def widePathBank : List Wire := PathShare.pathBank ++ [14848]

theorem mem_14848_poolBand : (14848 : Wire) ∈ poolBand := by
  decide

theorem wide_bits_paths_nodup : (wideBits ++ widePathBank).Nodup := by decide +kernel

theorem wide_root_nodup (q : Wire) (hq : q ∈ newSource) (h14848 : q ≠ 14848)
    (hold : (q :: WEX.windowBits ++ PathShare.pathBank).Nodup) :
    (q :: wideBits ++ widePathBank).Nodup := by
  rw [List.cons_append, List.nodup_cons]
  refine ⟨?_, wide_bits_paths_nodup⟩
  intro hm
  have hn := (List.nodup_cons.mp hold).1
  have ha := (WideSigned.Geometry.newSource_away .w16 q hq).1
  simp only [wideBits, widePathBank, List.mem_append, List.mem_singleton] at hm
  rcases hm with (h | h) | h | h
  · exact hn (List.mem_append_left _ h)
  · exact ha (by simpa [WideSigned.Geometry.extra, WideSigned.Geometry.Width.bits] using h)
  · exact hn (List.mem_append_right _ h)
  · exact h14848 h

theorem extend_literal_wide (p : ECDSAAdd.Program)
    (hs : ECDSAAdd.wires p ⊆ newSource.toFinset)
    (h14848 : (14848 : Wire) ∉ ECDSAAdd.wires p)
    (hp : PlacedPair WEX.windowBits PathShare.pathBank windowRoot (WInstr.literal (n := 32768) p)) :
    PlacedPair wideBits widePathBank windowRoot (WInstr.literal (n := 32768) p) := by
  intro v hv hm
  have ha := (WideSigned.Geometry.newSource_away .w16 v (List.mem_toFinset.mp (hs hm))).1
  rcases List.mem_cons.mp hv with rfl | hv
  · exact hp _ (by simp) hm
  rcases List.mem_append.mp hv with hb | hp'
  · rcases List.mem_append.mp hb with h | h
    · exact hp v (by simp [h]) hm
    · exact ha (by simpa [WideSigned.Geometry.extra, WideSigned.Geometry.Width.bits] using h)
  · rcases List.mem_append.mp hp' with h | h
    · exact hp v (by simp [h]) hm
    · rw [List.mem_singleton.mp h] at hm
      exact h14848 hm

theorem extend_lookup_wide (c : Option Wire) (ps : List (LookupPort 32768))
    (hs : (∀ q ∈ c, q ∈ newSource) ∧ portTargets ps ⊆ newSource)
    (h14848 : (14848 : Wire) ∉ portTargets ps ∧ ∀ q ∈ c, q ≠ 14848)
    (hp : PlacedPair WEX.windowBits PathShare.pathBank windowRoot (WInstr.lookup c ps)) :
    PlacedPair wideBits widePathBank windowRoot (WInstr.lookup c ps) := by
  have hq : lookupRoot windowRoot c ∈ newSource := by
    cases c with
    | none =>
      change windowRoot ∈ newSource
      exact newSource_of_bounds [windowRoot] (by decide) (by simp)
    | some q => exact hs.1 q rfl
  have hq48 : lookupRoot windowRoot c ≠ 14848 := by
    cases c with
    | none => decide
    | some q => exact h14848.2 q rfl
  refine ⟨wide_root_nodup _ hq hq48 hp.1, hp.2.1, hp.2.2.1, ?_⟩
  intro v hv ht
  have ha := (WideSigned.Geometry.newSource_away .w16 v (hs.2 ht)).1
  rcases List.mem_cons.mp hv with rfl | hv
  · exact List.disjoint_left.mp hp.2.2.2 (by simp) ht
  rcases List.mem_cons.mp hv with rfl | hv
  · exact List.disjoint_left.mp hp.2.2.2 (by simp) ht
  rcases List.mem_append.mp hv with hb | hp'
  · rcases List.mem_append.mp hb with h | h
    · exact List.disjoint_left.mp hp.2.2.2 (by simp [h]) ht
    · exact ha (by simpa [WideSigned.Geometry.extra, WideSigned.Geometry.Width.bits] using h)
  · rcases List.mem_append.mp hp' with h | h
    · exact List.disjoint_left.mp hp.2.2.2 (by simp [h]) ht
    · rw [List.mem_singleton.mp h] at ht
      exact h14848.1 ht

theorem extend_site_wide (B : PathShare.Bank) (hbits : B.bits = wideBits) (hpaths : B.paths = widePathBank)
    (u : UnitSite 32768) (hu : Block2.unit u ∈ WEXUnlookup.rowC)
    (hg : SiteGeoP PathShare.bank15 u.clear) :
    SiteGeoP B (WideSigned.Rows.site (WideSigned.Geometry.rows .w16) u.clear) := by
  have hsup := WideSigned.Geometry.site_support u hu hg.kind
  have hav := rowC_unit_avoidsB u hu
  have hclr : ∀ i ∈ u.clear.code, i ∈ u.code := by
    intro i hi
    rcases List.mem_append.mp hu with h | h
    · obtain ⟨b, _, he⟩ := List.mem_map.mp h
      cases b with
      | plain _ => cases he
      | masked s => cases he; exact hi
    · simp only [WEXUnlookup.rowPost3, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq,
        Block2.unit.injEq, false_or, or_false] at h
      rcases h with rfl | rfl <;>
      · simp only [WEXUnlookup.cornerUnit₁, WEXUnlookup.cornerUnit₂, WEXUnlookup.ySite,
          WEXUnlookup.scrDClear, MaskedSite.code, MaskedSite.prefix, UnitSite.code,
          List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
        rcases hi with rfl | rfl <;> simp
  refine ⟨?_, WideSigned.Rows.kind _ _ hg.kind⟩
  intro i hi
  rw [WideSigned.Rows.site_code] at hi
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hi
  have hp := hg.placed old ho
  have hmem := hclr old ho
  cases old with
  | literal p =>
    rw [hbits, hpaths]
    exact extend_literal_wide p (hsup.1 p ho) (hav.1 14848 mem_14848_poolBand p hmem) hp
  | lookup c ps =>
    have he := extend_lookup_wide c ps (hsup.2 c ps ho) (hav.2 14848 mem_14848_poolBand c ps hmem)
      (placed_implies_pair WEX.windowBits PathShare.pathBank windowRoot _ hp)
    have ht : portTargets (WideSigned.Rows.ports (WideSigned.Geometry.rows .w16) ps) = portTargets ps :=
      WideSigned.Rows.targets _ _
    rw [hbits, hpaths]
    exact ⟨he.1, ht ▸ hp.2.1, ht ▸ he.2.2.2⟩

theorem extend_unit_wide (B : PathShare.Bank) (hbits : B.bits = wideBits) (hpaths : B.paths = widePathBank)
    (u : UnitSite 32768) (hu : Block2.unit u ∈ WEXUnlookup.rowC)
    (hg : UnitGeoP PathShare.bank15 u) :
    UnitGeoP B (WideSigned.Rows.unit (WideSigned.Geometry.rows .w16) u) := by
  have hav := rowC_unit_avoidsB u hu
  refine ⟨?_, extend_site_wide B hbits hpaths u hu hg.site⟩
  intro i hi
  rw [WideSigned.Rows.unit_code] at hi
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hi
  have hp := hg.placed old ho
  have hmem : old ∈ erase2 WEXUnlookup.rowC := List.mem_flatMap.mpr ⟨.unit u, hu, ho⟩
  have hext : PlacedPair wideBits widePathBank windowRoot old := by
    cases old with
    | literal p =>
      exact extend_literal_wide p (W15C.rowC_lit_new p hmem) (hav.1 14848 mem_14848_poolBand p ho) hp
    | lookup c ps =>
      exact extend_lookup_wide c ps (W15C.rowC_look_new c ps hmem) (hav.2 14848 mem_14848_poolBand c ps ho) hp
  rw [hbits, hpaths]
  exact WideSigned.Geometry.placed_lift (WideSigned.Geometry.rows .w16) wideBits widePathBank old hext

/-! ### Four-wire flag hosting (`14874..14877` on `14111, 19816, 838, 14112`) -/

def hostWire4 : Wire := 14877
def hostWire5 : Wire := 14876
def hostWire6 : Wire := 14875
def hostWire7 : Wire := 14874

def hostCtl4 : Wire := 14111
def hostCtl5 : Wire := 19816
def hostCtl6 : Wire := 838
def hostCtl7 : Wire := 14112

def perm4 (w : Wire) : Wire :=
  if w = 14877 then 14111
  else if w = 14111 then 14877
  else if w = 14876 then 19816
  else if w = 19816 then 14876
  else if w = 14875 then 838
  else if w = 838 then 14875
  else if w = 14874 then 14112
  else if w = 14112 then 14874
  else w

theorem perm4_involutive : Function.Involutive perm4 := by
  intro w
  dsimp only [Wire] at w
  unfold perm4
  by_cases h1 : w = 14877; · simp [h1]
  by_cases h2 : w = 14111; · simp [h2]
  by_cases h3 : w = 14876; · simp [h3]
  by_cases h4 : w = 19816; · simp [h4]
  by_cases h5 : w = 14875; · simp [h5]
  by_cases h6 : w = 838; · simp [h6]
  by_cases h7 : w = 14874; · simp [h7]
  by_cases h8 : w = 14112; · simp [h8]
  simp [h1, h2, h3, h4, h5, h6, h7, h8]

theorem perm4_injective : Function.Injective perm4 := perm4_involutive.injective

def enc4 : ECDSAAdd.Program :=
  [.X 14111,
   .CX 838 19816, .X 19816,
   .CX 14113 838, .CX 19815 838, .CX 19814 838, .CX 14112 838,
   .CX 14112 19815, .CX 14112 19814,
   .CCX 19815 19814 14112]

def dec4 : ECDSAAdd.Program :=
  [.CCX 19815 19814 14112,
   .CX 14112 19814, .CX 14112 19815,
   .CX 14112 838, .CX 19814 838, .CX 19815 838, .CX 14113 838,
   .X 19816, .CX 838 19816,
   .X 14111]

def host4Set (p : ECDSAAdd.Program) : Prop :=
  (14877 ∈ ECDSAAdd.wires p ∨ 14876 ∈ ECDSAAdd.wires p ∨
    14875 ∈ ECDSAAdd.wires p ∨ 14874 ∈ ECDSAAdd.wires p) ∧
  14111 ∉ ECDSAAdd.wires p ∧ 19816 ∉ ECDSAAdd.wires p ∧
  838 ∉ ECDSAAdd.wires p ∧ 14112 ∉ ECDSAAdd.wires p ∧
  19815 ∉ ECDSAAdd.wires p ∧ 19814 ∉ ECDSAAdd.wires p

instance (p : ECDSAAdd.Program) : Decidable (host4Set p) :=
  inferInstanceAs (Decidable
    ((14877 ∈ ECDSAAdd.wires p ∨ 14876 ∈ ECDSAAdd.wires p ∨
      14875 ∈ ECDSAAdd.wires p ∨ 14874 ∈ ECDSAAdd.wires p) ∧
    14111 ∉ ECDSAAdd.wires p ∧ 19816 ∉ ECDSAAdd.wires p ∧
    838 ∉ ECDSAAdd.wires p ∧ 14112 ∉ ECDSAAdd.wires p ∧
    19815 ∉ ECDSAAdd.wires p ∧ 19814 ∉ ECDSAAdd.wires p))

def hostBlock7 (p : ECDSAAdd.Program) : ECDSAAdd.Program :=
  if host4Set p then
    enc4 ++ progRelabel perm4 (hostBlock3 p) ++ dec4
  else hostBlock3 p

def hostExtra (p : ECDSAAdd.Program) : Nat :=
  if host4Set p then 2 else 0

theorem hostExtra_le (p : ECDSAAdd.Program) : hostExtra p ≤ 2 := by
  unfold hostExtra; split_ifs <;> omega

theorem hostExtra_zero_of (p : ECDSAAdd.Program)
    (h : ∀ w ∈ poolBand, w ∉ ECDSAAdd.wires p) : hostExtra p = 0 := by
  have hn : ¬host4Set p := by
    rintro ⟨h1 | h2 | h3 | h4, -⟩
    · exact h 14877 (by decide) h1
    · exact h 14876 (by decide) h2
    · exact h 14875 (by decide) h3
    · exact h 14874 (by decide) h4
  simp [hostExtra, hn]

theorem hostBlock7_meas (p : ECDSAAdd.Program) :
    ECDSAAdd.measurementCount (hostBlock7 p) = ECDSAAdd.measurementCount p := by
  unfold hostBlock7
  split_ifs
  · simp [ECDSAAdd.measurementCount_append, enc4, dec4, ECDSAAdd.measurementCount,
      relabel_meas, hostBlock3_meas]
  · exact hostBlock3_meas p

theorem hostBlock7_toffoli (p : ECDSAAdd.Program) :
    ECDSAAdd.toffoliCount (hostBlock7 p) = ECDSAAdd.toffoliCount p + hostExtra p := by
  unfold hostBlock7 hostExtra
  split_ifs
  · simp only [ECDSAAdd.toffoliCount_append, relabel_toffoli, hostBlock3_toffoli]
    have h1 : ECDSAAdd.toffoliCount enc4 = 1 := rfl
    have h2 : ECDSAAdd.toffoliCount dec4 = 1 := rfl
    omega
  · simp [hostBlock3_toffoli]

theorem hostBlock7_slots {n : Nat} (p : ECDSAAdd.Program) :
    Bridge.tmplSlots (WEX.literalT (n := n) (hostBlock7 p)) ≤
      Bridge.tmplSlots (WEX.literalT (n := n) p) + 26 := by
  have h3 := hostBlock3_slots (n := n) p
  unfold hostBlock7
  split_ifs
  · have hr := relabel_slots (n := n) perm4 (hostBlock3 p)
    simp only [Bridge.tmplSlots, WEX.literalT, List.map_append, List.sum_append] at h3 hr ⊢
    rw [hr]
    have h1 : (List.map Bridge.TInstr.slots (List.map (Bridge.TInstr.lit (n := n)) enc4)).sum = 10 := by
      simp [enc4, Bridge.TInstr.slots]
    have h2 : (List.map Bridge.TInstr.slots (List.map (Bridge.TInstr.lit (n := n)) dec4)).sum = 10 := by
      simp [dec4, Bridge.TInstr.slots]
    omega
  · omega

theorem enc4_valid : ∀ i ∈ enc4, ECDSAAdd.Challenge.instructionValid i := by
  intro i hi
  simp only [enc4, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [ECDSAAdd.Challenge.instructionValid]

theorem dec4_valid : ∀ i ∈ dec4, ECDSAAdd.Challenge.instructionValid i := by
  intro i hi
  simp only [dec4, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [ECDSAAdd.Challenge.instructionValid]

theorem hostBlock7_valid (p : ECDSAAdd.Program) (h : ∀ i ∈ p, ECDSAAdd.Challenge.instructionValid i) :
    ∀ i ∈ hostBlock7 p, ECDSAAdd.Challenge.instructionValid i := by
  unfold hostBlock7
  split_ifs
  · intro i hi
    simp only [List.mem_append] at hi
    rcases hi with (hi | hi) | hi
    · exact enc4_valid i hi
    · exact relabel_valid perm4 perm4_injective _ (hostBlock3_valid p h) i hi
    · exact dec4_valid i hi
  · exact hostBlock3_valid p h

def FlagInv7 (b : BasisState) : Prop :=
  b 14111 = true ∧
  b 19816 = !b 838 ∧
  b 838 = (b 14113 ^^ b 19815 ^^ b 19814 ^^ b 14112) ∧
  (b 19815 = true → b 19814 = false) ∧
  (b 14112 = true → b 19815 = false ∧ b 19814 = false)

def Clean4 (b : BasisState) : Prop :=
  b 14877 = false ∧ b 14876 = false ∧ b 14875 = false ∧ b 14874 = false

def encBasis (b : BasisState) : BasisState :=
  ECDSAAdd.writeBit
    (ECDSAAdd.writeBit
      (ECDSAAdd.writeBit
        (ECDSAAdd.writeBit
          (ECDSAAdd.writeBit
            (ECDSAAdd.writeBit b 14111 false)
            19816 false)
          838 false)
        14112 false)
      19815 (b 19815 ^^ b 14112))
    19814 (b 19814 ^^ b 14112)

private theorem enc4_step_eq (ph : Bool) (b : BasisState) (m : List Bool) :
    ECDSAAdd.run enc4 m ⟨ph, b⟩ =
      let b1 := ECDSAAdd.writeBit b 14111 (!b 14111)
      let b2 := ECDSAAdd.writeBit b1 19816 (b1 19816 ^^ b1 838)
      let b3 := ECDSAAdd.writeBit b2 19816 (!b2 19816)
      let b4 := ECDSAAdd.writeBit b3 838 (b3 838 ^^ b3 14113)
      let b5 := ECDSAAdd.writeBit b4 838 (b4 838 ^^ b4 19815)
      let b6 := ECDSAAdd.writeBit b5 838 (b5 838 ^^ b5 19814)
      let b7 := ECDSAAdd.writeBit b6 838 (b6 838 ^^ b6 14112)
      let b8 := ECDSAAdd.writeBit b7 19815 (b7 19815 ^^ b7 14112)
      let b9 := ECDSAAdd.writeBit b8 19814 (b8 19814 ^^ b8 14112)
      let b10 := ECDSAAdd.writeBit b9 14112 (b9 14112 ^^ (b9 19815 && b9 19814))
      ⟨ph, b10⟩ := rfl

private theorem dec4_step_eq (ph : Bool) (b : BasisState) (m : List Bool) :
    ECDSAAdd.run dec4 m ⟨ph, b⟩ =
      let b1 := ECDSAAdd.writeBit b 14112 (b 14112 ^^ (b 19815 && b 19814))
      let b2 := ECDSAAdd.writeBit b1 19814 (b1 19814 ^^ b1 14112)
      let b3 := ECDSAAdd.writeBit b2 19815 (b2 19815 ^^ b2 14112)
      let b4 := ECDSAAdd.writeBit b3 838 (b3 838 ^^ b3 14112)
      let b5 := ECDSAAdd.writeBit b4 838 (b4 838 ^^ b4 19814)
      let b6 := ECDSAAdd.writeBit b5 838 (b5 838 ^^ b5 19815)
      let b7 := ECDSAAdd.writeBit b6 838 (b6 838 ^^ b6 14113)
      let b8 := ECDSAAdd.writeBit b7 19816 (!b7 19816)
      let b9 := ECDSAAdd.writeBit b8 19816 (b8 19816 ^^ b8 838)
      let b10 := ECDSAAdd.writeBit b9 14111 (!b9 14111)
      ⟨ph, b10⟩ := rfl

private theorem wb_hit (b : BasisState) (k : Wire) (v : Bool) : ECDSAAdd.writeBit b k v k = v := by
  simp [ECDSAAdd.writeBit]

private theorem wb_miss (b : BasisState) {k w : Wire} (v : Bool) (h : w ≠ k) :
    ECDSAAdd.writeBit b k v w = b w := by
  simp [ECDSAAdd.writeBit, h]

theorem enc4_run (s : ECDSAAdd.State) (hf : FlagInv7 s.basis) (m : List Bool) :
    ECDSAAdd.run enc4 m s = ⟨s.phase, encBasis s.basis⟩ := by
  obtain ⟨h11, h16, h838, hDI, hH⟩ := hf
  cases s with
  | mk ph b =>
    dsimp only at h11 h16 h838 hDI hH
    rw [enc4_step_eq]
    dsimp only
    congr 1
    funext w
    set b1 := ECDSAAdd.writeBit b 14111 (!b 14111)
    set b2 := ECDSAAdd.writeBit b1 19816 (b1 19816 ^^ b1 838)
    set b3 := ECDSAAdd.writeBit b2 19816 (!b2 19816)
    set b4 := ECDSAAdd.writeBit b3 838 (b3 838 ^^ b3 14113)
    set b5 := ECDSAAdd.writeBit b4 838 (b4 838 ^^ b4 19815)
    set b6 := ECDSAAdd.writeBit b5 838 (b5 838 ^^ b5 19814)
    set b7 := ECDSAAdd.writeBit b6 838 (b6 838 ^^ b6 14112)
    set b8 := ECDSAAdd.writeBit b7 19815 (b7 19815 ^^ b7 14112)
    set b9 := ECDSAAdd.writeBit b8 19814 (b8 19814 ^^ b8 14112)
    have e1_11 : b1 14111 = false := by simp only [b1, wb_hit, h11]; rfl
    have e1_o : ∀ k, k ≠ 14111 → b1 k = b k := fun k hk => wb_miss b _ hk
    have e2_16 : b2 19816 = true := by
      simp only [b2, wb_hit, e1_o 19816 (by decide), e1_o 838 (by decide), h16]; cases b 838 <;> rfl
    have e3_16 : b3 19816 = false := by simp only [b3, wb_hit, e2_16]; rfl
    have e3_o : ∀ k, k ≠ 19816 → b3 k = b1 k := fun k hk =>
      (wb_miss b2 _ hk).trans (wb_miss b1 _ hk)
    have e4_838 : b4 838 = (b 838 ^^ b 14113) := by
      have c1 : b3 838 = b 838 := (e3_o 838 (by decide)).trans (e1_o 838 (by decide))
      have c2 : b3 14113 = b 14113 := (e3_o 14113 (by decide)).trans (e1_o 14113 (by decide))
      simp only [b4, wb_hit, c1, c2]
    have e5_838 : b5 838 = (b 838 ^^ b 14113 ^^ b 19815) := by
      have c3 : b4 19815 = b 19815 := (wb_miss b3 _ (by decide)).trans ((e3_o 19815 (by decide)).trans (e1_o 19815 (by decide)))
      simp only [b5, wb_hit, e4_838, c3]
    have e6_838 : b6 838 = (b 838 ^^ b 14113 ^^ b 19815 ^^ b 19814) := by
      have c4 : b5 19814 = b 19814 := (wb_miss b4 _ (by decide)).trans ((wb_miss b3 _ (by decide)).trans ((e3_o 19814 (by decide)).trans (e1_o 19814 (by decide))))
      simp only [b6, wb_hit, e5_838, c4]
    have e7_838 : b7 838 = false := by
      have c5 : b6 14112 = b 14112 := (wb_miss b5 _ (by decide)).trans ((wb_miss b4 _ (by decide)).trans ((wb_miss b3 _ (by decide)).trans ((e3_o 14112 (by decide)).trans (e1_o 14112 (by decide)))))
      simp only [b7, wb_hit, e6_838, c5, h838]
      cases b 14113 <;> cases b 19815 <;> cases b 19814 <;> cases b 14112 <;> rfl
    have e7_o : ∀ k, k ≠ 838 → b7 k = b3 k := fun k hk =>
      (wb_miss b6 _ hk).trans ((wb_miss b5 _ hk).trans ((wb_miss b4 _ hk).trans (wb_miss b3 _ hk)))
    have e8_15 : b8 19815 = (b 19815 ^^ b 14112) := by
      simp only [b8, wb_hit, e7_o 19815 (by decide), e3_o 19815 (by decide), e1_o 19815 (by decide),
        e7_o 14112 (by decide), e3_o 14112 (by decide), e1_o 14112 (by decide)]
    have e9_14 : b9 19814 = (b 19814 ^^ b 14112) := by
      have d1 : b8 19814 = b7 19814 := wb_miss b7 _ (by decide)
      have d2 : b8 14112 = b7 14112 := wb_miss b7 _ (by decide)
      simp only [b9, wb_hit, d1, d2,
        e7_o 19814 (by decide), e3_o 19814 (by decide), e1_o 19814 (by decide),
        e7_o 14112 (by decide), e3_o 14112 (by decide), e1_o 14112 (by decide)]
    have e9_15 : b9 19815 = (b 19815 ^^ b 14112) := (wb_miss b8 _ (by decide)).trans e8_15
    have e9_12 : b9 14112 = b 14112 :=
      (wb_miss b8 _ (by decide)).trans ((wb_miss b7 _ (by decide)).trans
        ((e7_o 14112 (by decide)).trans ((e3_o 14112 (by decide)).trans (e1_o 14112 (by decide)))))
    have e10_12 : ECDSAAdd.writeBit b9 14112 (b9 14112 ^^ (b9 19815 && b9 19814)) 14112 = false := by
      rw [wb_hit, e9_12, e9_15, e9_14]
      cases hD : b 19815 <;> cases hI : b 19814 <;> cases hQ : b 14112 <;> simp_all
    by_cases w12 : w = 14112
    · subst w12; rw [e10_12]; simp [encBasis, ECDSAAdd.writeBit]
    rw [wb_miss b9 _ w12]
    by_cases w14 : w = 19814
    · subst w14; rw [e9_14]; simp [encBasis, ECDSAAdd.writeBit]
    change b9 w = _; simp only [b9, wb_miss b8 _ w14]
    by_cases w15 : w = 19815
    · subst w15; rw [e8_15]; simp [encBasis, ECDSAAdd.writeBit]
    change b8 w = _; simp only [b8, wb_miss b7 _ w15]
    by_cases w838 : w = 838
    · subst w838; rw [e7_838]; simp [encBasis, ECDSAAdd.writeBit]
    rw [e7_o w w838]
    by_cases w16 : w = 19816
    · subst w16; rw [e3_16]; simp [encBasis, ECDSAAdd.writeBit]
    rw [e3_o w w16]
    by_cases w11 : w = 14111
    · subst w11; rw [e1_11]; simp [encBasis, ECDSAAdd.writeBit]
    rw [e1_o w w11]
    simp [encBasis, ECDSAAdd.writeBit, w14, w15, w12, w838, w16, w11]

theorem dec4_run (t : ECDSAAdd.State) (hf : FlagInv7 t.basis) (m : List Bool) :
    ECDSAAdd.run dec4 m ⟨t.phase, encBasis t.basis⟩ = t := by
  obtain ⟨h11, h16, h838, hDI, hH⟩ := hf
  cases t with
  | mk ph b =>
    dsimp only at h11 h16 h838 hDI hH
    rw [dec4_step_eq]
    dsimp only
    congr 1
    funext w
    set b0 := encBasis b
    set b1 := ECDSAAdd.writeBit b0 14112 (b0 14112 ^^ (b0 19815 && b0 19814))
    set b2 := ECDSAAdd.writeBit b1 19814 (b1 19814 ^^ b1 14112)
    set b3 := ECDSAAdd.writeBit b2 19815 (b2 19815 ^^ b2 14112)
    set b4 := ECDSAAdd.writeBit b3 838 (b3 838 ^^ b3 14112)
    set b5 := ECDSAAdd.writeBit b4 838 (b4 838 ^^ b4 19814)
    set b6 := ECDSAAdd.writeBit b5 838 (b5 838 ^^ b5 19815)
    set b7 := ECDSAAdd.writeBit b6 838 (b6 838 ^^ b6 14113)
    set b8 := ECDSAAdd.writeBit b7 19816 (!b7 19816)
    set b9 := ECDSAAdd.writeBit b8 19816 (b8 19816 ^^ b8 838)
    have f14 : b0 19814 = (b 19814 ^^ b 14112) := by simp [b0, encBasis, ECDSAAdd.writeBit]
    have f15 : b0 19815 = (b 19815 ^^ b 14112) := by simp [b0, encBasis, ECDSAAdd.writeBit]
    have f12 : b0 14112 = false := by simp [b0, encBasis, ECDSAAdd.writeBit]
    have f838 : b0 838 = false := by simp [b0, encBasis, ECDSAAdd.writeBit]
    have f16 : b0 19816 = false := by simp [b0, encBasis, ECDSAAdd.writeBit]
    have f11 : b0 14111 = false := by simp [b0, encBasis, ECDSAAdd.writeBit]
    have f13 : b0 14113 = b 14113 := by simp [b0, encBasis, ECDSAAdd.writeBit]
    have e1_12 : b1 14112 = b 14112 := by
      simp only [b1, wb_hit, f12, f15, f14]
      cases hD : b 19815 <;> cases hI : b 19814 <;> cases hQ : b 14112 <;> simp_all
    have e2_14 : b2 19814 = b 19814 := by
      have d0 : b1 19814 = b0 19814 := wb_miss b0 _ (by decide)
      simp only [b2, wb_hit, d0, f14, e1_12]
      cases b 19814 <;> cases b 14112 <;> rfl
    have e3_15 : b3 19815 = b 19815 := by
      have c1 : b2 19815 = b0 19815 := (wb_miss b1 _ (by decide)).trans (wb_miss b0 _ (by decide))
      have c2 : b2 14112 = b1 14112 := wb_miss b1 _ (by decide)
      simp only [b3, wb_hit, c1, f15, c2, e1_12]
      cases b 19815 <;> cases b 14112 <;> rfl
    have e3_14 : b3 19814 = b 19814 := (wb_miss b2 _ (by decide)).trans e2_14
    have e3_12 : b3 14112 = b 14112 := (wb_miss b2 _ (by decide)).trans ((wb_miss b1 _ (by decide)).trans e1_12)
    have e3_838 : b3 838 = false :=
      (wb_miss b2 _ (by decide)).trans ((wb_miss b1 _ (by decide)).trans ((wb_miss b0 _ (by decide)).trans f838))
    have e3_13 : b3 14113 = b 14113 :=
      (wb_miss b2 _ (by decide)).trans ((wb_miss b1 _ (by decide)).trans ((wb_miss b0 _ (by decide)).trans f13))
    have e4_838 : b4 838 = (false ^^ b 14112) := by simp only [b4, wb_hit, e3_838, e3_12]
    have e5_838 : b5 838 = (false ^^ b 14112 ^^ b 19814) := by
      have c4 : b4 19814 = b 19814 := (wb_miss b3 _ (by decide)).trans e3_14
      simp only [b5, wb_hit, e4_838, c4]
    have e6_838 : b6 838 = (false ^^ b 14112 ^^ b 19814 ^^ b 19815) := by
      have c5 : b5 19815 = b 19815 := (wb_miss b4 _ (by decide)).trans ((wb_miss b3 _ (by decide)).trans e3_15)
      simp only [b6, wb_hit, e5_838, c5]
    have e7_838 : b7 838 = b 838 := by
      have c6 : b6 14113 = b 14113 := (wb_miss b5 _ (by decide)).trans ((wb_miss b4 _ (by decide)).trans ((wb_miss b3 _ (by decide)).trans e3_13))
      simp only [b7, wb_hit, e6_838, c6, h838]
      cases b 14113 <;> cases b 19815 <;> cases b 19814 <;> cases b 14112 <;> rfl
    have e7_o : ∀ k, k ≠ 838 → b7 k = b3 k := fun k hk =>
      (wb_miss b6 _ hk).trans ((wb_miss b5 _ hk).trans ((wb_miss b4 _ hk).trans (wb_miss b3 _ hk)))
    have e8_16 : b8 19816 = true := by
      have c7 : b7 19816 = false :=
        (e7_o 19816 (by decide)).trans ((wb_miss b2 _ (by decide)).trans ((wb_miss b1 _ (by decide)).trans ((wb_miss b0 _ (by decide)).trans f16)))
      simp only [b8, wb_hit, c7]; rfl
    have e9_16 : b9 19816 = b 19816 := by
      have c8 : b8 838 = b 838 := (wb_miss b7 _ (by decide)).trans e7_838
      simp only [b9, wb_hit, e8_16, c8, h16]
      cases b 838 <;> rfl
    have e10_11 : ECDSAAdd.writeBit b9 14111 (!b9 14111) 14111 = b 14111 := by
      have c9 : b9 14111 = false :=
        (wb_miss b8 _ (by decide)).trans ((wb_miss b7 _ (by decide)).trans
          ((e7_o 14111 (by decide)).trans ((wb_miss b2 _ (by decide)).trans ((wb_miss b1 _ (by decide)).trans ((wb_miss b0 _ (by decide)).trans f11)))))
      rw [wb_hit, c9, h11]; rfl
    by_cases w11 : w = 14111
    · subst w11; exact e10_11
    rw [wb_miss b9 _ w11]
    by_cases w16 : w = 19816
    · subst w16; exact e9_16
    change b9 w = _; simp only [b9, wb_miss b8 _ w16]; simp only [b8, wb_miss b7 _ w16]
    by_cases w838 : w = 838
    · subst w838; exact e7_838
    rw [e7_o w w838]
    by_cases w15 : w = 19815
    · subst w15; exact e3_15
    change b3 w = _; simp only [b3, wb_miss b2 _ w15]
    by_cases w14 : w = 19814
    · subst w14; exact e2_14
    change b2 w = _; simp only [b2, wb_miss b1 _ w14]
    by_cases w12 : w = 14112
    · subst w12; exact e1_12
    change b1 w = _; simp only [b1, wb_miss b0 _ w12]
    simp [b0, encBasis, ECDSAAdd.writeBit, w14, w15, w12, w838, w16, w11]

theorem hostBlock3_avoid_extra (p : ECDSAAdd.Program) (w : Wire)
    (hw : w ∉ ECDSAAdd.wires p)
    (h1 : w ≠ windowRoot) (h2 : w ≠ hostWire)
    (h3 : w ≠ hostCtl) (h4 : w ≠ hostWire2)
    (h5 : w ≠ hostCtl3) (h6 : w ≠ hostWire3) :
    w ∉ ECDSAAdd.wires (hostBlock3 p) := by
  have hb0 : w ∉ ECDSAAdd.wires (hostP hostWire windowRoot p) := by
    intro hm
    rcases hostP_wires_mem _ _ _ _ hm with e | e | e
    · exact h1 e
    · exact h2 e
    · exact hw e
  have hb1 : w ∉ ECDSAAdd.wires (hostBlock p) := by
    unfold hostBlock
    split
    · intro hm
      rcases hostP_wires_mem _ _ _ _ hm with e | e | e
      · exact h3 e
      · exact h4 e
      · exact hb0 e
    · exact hb0
  unfold hostBlock3
  split
  · intro hm
    rcases hostP_wires_mem _ _ _ _ hm with e | e | e
    · exact h5 e
    · exact h6 e
    · exact hb1 e
  · exact hb1

theorem pullS_perm4_encBasis (ph : Bool) (b : BasisState) (hc : Clean4 b) :
    pullS perm4 ⟨ph, encBasis b⟩ = ⟨ph, encBasis b⟩ := by
  obtain ⟨c7, c6, c5, c4⟩ := hc
  simp only [pullS, ECDSAAdd.State.mk.injEq, true_and]
  funext w
  unfold perm4
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8
  · subst h1; simp [encBasis, ECDSAAdd.writeBit, Function.update, c7]
  · subst h2; simp [encBasis, ECDSAAdd.writeBit, Function.update, c7]
  · subst h3; simp [encBasis, ECDSAAdd.writeBit, Function.update, c6]
  · subst h4; simp [encBasis, ECDSAAdd.writeBit, Function.update, c6]
  · subst h5; simp [encBasis, ECDSAAdd.writeBit, Function.update, c5]
  · subst h6; simp [encBasis, ECDSAAdd.writeBit, Function.update, c5]
  · subst h7; simp [encBasis, ECDSAAdd.writeBit, Function.update, c4]
  · subst h8; simp [encBasis, ECDSAAdd.writeBit, Function.update, c4]
  · rfl

theorem hostBlock7_run (p : ECDSAAdd.Program) (hR : windowRoot ∉ ECDSAAdd.wires p) (m : List Bool)
    (s : ECDSAAdd.State) (h1 : s.basis windowRoot = true) (h2 : s.basis hostWire = false)
    (h3 : (ECDSAAdd.run p m s).basis hostWire = false)
    (h4 : hostWire2 ∈ ECDSAAdd.wires p → hostCtl ∉ ECDSAAdd.wires p →
      s.basis hostCtl = true ∧ s.basis hostWire2 = false ∧ (ECDSAAdd.run p m s).basis hostWire2 = false)
    (h5 : hostWire3 ∈ ECDSAAdd.wires p → hostCtl3 ∉ ECDSAAdd.wires p →
      s.basis hostCtl3 = true ∧ s.basis hostWire3 = false ∧ (ECDSAAdd.run p m s).basis hostWire3 = false)
    (h7 : host4Set p → FlagInv7 s.basis ∧ Clean4 s.basis ∧ Clean4 (ECDSAAdd.run p m s).basis ∧
      (ECDSAAdd.run p m s).basis 14113 = s.basis 14113) :
    ECDSAAdd.run (hostBlock7 p) m s = ECDSAAdd.run p m s := by
  have inner := hostBlock3_run p hR m s h1 h2 h3 h4 h5
  unfold hostBlock7
  split_ifs with hcond
  · obtain ⟨hf, hc0, hc1, hG⟩ := h7 hcond
    let q := hostBlock3 p
    have hq11 : (14111 : Wire) ∉ ECDSAAdd.wires q :=
      hostBlock3_avoid_extra p 14111 hcond.2.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hq16 : (19816 : Wire) ∉ ECDSAAdd.wires q :=
      hostBlock3_avoid_extra p 19816 hcond.2.2.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hq838 : (838 : Wire) ∉ ECDSAAdd.wires q :=
      hostBlock3_avoid_extra p 838 hcond.2.2.2.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hq12 : (14112 : Wire) ∉ ECDSAAdd.wires q :=
      hostBlock3_avoid_extra p 14112 hcond.2.2.2.2.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hq15 : (19815 : Wire) ∉ ECDSAAdd.wires q :=
      hostBlock3_avoid_extra p 19815 hcond.2.2.2.2.2.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hq14 : (19814 : Wire) ∉ ECDSAAdd.wires q :=
      hostBlock3_avoid_extra p 19814 hcond.2.2.2.2.2.2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hme : ECDSAAdd.measurementCount enc4 = 0 := rfl
    have hmc : ECDSAAdd.measurementCount (enc4 ++ progRelabel perm4 q) = ECDSAAdd.measurementCount (progRelabel perm4 q) := by
      rw [ECDSAAdd.measurementCount_append, hme, Nat.zero_add]
    rw [ECDSAAdd.run_append, ECDSAAdd.run_append, hmc, hme, List.take_zero, List.drop_zero,
      enc4_run s hf List.nil, run_relabel perm4 perm4_involutive q,
      pullS_perm4_encBasis s.phase s.basis hc0]
    have hqrun : ECDSAAdd.run q (m.take (ECDSAAdd.measurementCount (progRelabel perm4 q)))
        ⟨s.phase, encBasis s.basis⟩ = ⟨(ECDSAAdd.run p m s).phase, encBasis (ECDSAAdd.run p m s).basis⟩ := by
      have hupd (ph : Bool) (b : BasisState) (w : Wire) (v : Bool) (hw : w ∉ ECDSAAdd.wires q) :
          ECDSAAdd.run q m ⟨ph, ECDSAAdd.writeBit b w v⟩ =
            ⟨(ECDSAAdd.run q m ⟨ph, b⟩).phase, ECDSAAdd.writeBit (ECDSAAdd.run q m ⟨ph, b⟩).basis w v⟩ :=
        run_update_outside q m ⟨ph, b⟩ w v hw
      rw [relabel_meas, ECDSAAdd.run_take]
      unfold encBasis
      rw [hupd _ _ 19814 _ hq14, hupd _ _ 19815 _ hq15, hupd _ _ 14112 _ hq12,
          hupd _ _ 838 _ hq838, hupd _ _ 19816 _ hq16, hupd _ _ 14111 _ hq11]
      have hp12 : (ECDSAAdd.run q m s).basis 14112 = s.basis 14112 := ECDSAAdd.run_preserves_outside q m s 14112 hq12
      have hp15 : (ECDSAAdd.run q m s).basis 19815 = s.basis 19815 := ECDSAAdd.run_preserves_outside q m s 19815 hq15
      have hp14 : (ECDSAAdd.run q m s).basis 19814 = s.basis 19814 := ECDSAAdd.run_preserves_outside q m s 19814 hq14
      rw [inner] at hp12 hp15 hp14 ⊢
      rw [hp12, hp15, hp14]
    have hf' : FlagInv7 (ECDSAAdd.run p m s).basis := by
      have p11 : (ECDSAAdd.run p m s).basis 14111 = s.basis 14111 := by
        rw [← inner]; exact ECDSAAdd.run_preserves_outside q m s 14111 hq11
      have p16 : (ECDSAAdd.run p m s).basis 19816 = s.basis 19816 := by
        rw [← inner]; exact ECDSAAdd.run_preserves_outside q m s 19816 hq16
      have p838 : (ECDSAAdd.run p m s).basis 838 = s.basis 838 := by
        rw [← inner]; exact ECDSAAdd.run_preserves_outside q m s 838 hq838
      have p12 : (ECDSAAdd.run p m s).basis 14112 = s.basis 14112 := by
        rw [← inner]; exact ECDSAAdd.run_preserves_outside q m s 14112 hq12
      have p15 : (ECDSAAdd.run p m s).basis 19815 = s.basis 19815 := by
        rw [← inner]; exact ECDSAAdd.run_preserves_outside q m s 19815 hq15
      have p14 : (ECDSAAdd.run p m s).basis 19814 = s.basis 19814 := by
        rw [← inner]; exact ECDSAAdd.run_preserves_outside q m s 19814 hq14
      rw [FlagInv7, p11, p16, p838, p12, p15, p14, hG]
      exact hf
    rw [hqrun, pullS_perm4_encBasis (ECDSAAdd.run p m s).phase (ECDSAAdd.run p m s).basis hc1]
    exact dec4_run (ECDSAAdd.run p m s) hf' _
  · exact inner

theorem hostBlock7_wires (p : ECDSAAdd.Program) (S : List Wire)
    (hroot : windowRoot ∈ S) (hctl : hostCtl ∈ S) (hctl3 : hostCtl3 ∈ S)
    (hc11 : (14111 : Wire) ∈ S) (hc16 : (19816 : Wire) ∈ S) (hc838 : (838 : Wire) ∈ S)
    (hc12 : (14112 : Wire) ∈ S) (hc15 : (19815 : Wire) ∈ S) (hc14 : (19814 : Wire) ∈ S)
    (hc13 : (14113 : Wire) ∈ S)
    (hR : windowRoot ∉ ECDSAAdd.wires p)
    (h : ∀ w ∈ ECDSAAdd.wires p,
      w = hostWire ∨ w = hostWire2 ∨ w = hostWire3 ∨
      w = hostWire4 ∨ w = hostWire5 ∨ w = hostWire6 ∨ w = hostWire7 ∨ w ∈ S)
    (hc : hostWire2 ∈ ECDSAAdd.wires p → hostCtl ∉ ECDSAAdd.wires p)
    (hc3 : hostWire3 ∈ ECDSAAdd.wires p → hostCtl3 ∉ ECDSAAdd.wires p)
    (hc4 : (14877 ∈ ECDSAAdd.wires p ∨ 14876 ∈ ECDSAAdd.wires p ∨
        14875 ∈ ECDSAAdd.wires p ∨ 14874 ∈ ECDSAAdd.wires p) →
      14111 ∉ ECDSAAdd.wires p ∧ 19816 ∉ ECDSAAdd.wires p ∧
      838 ∉ ECDSAAdd.wires p ∧ 14112 ∉ ECDSAAdd.wires p ∧
      19815 ∉ ECDSAAdd.wires p ∧ 19814 ∉ ECDSAAdd.wires p) :
    ECDSAAdd.wires (hostBlock7 p) ⊆ S.toFinset := by
  unfold hostBlock7
  split_ifs with hcond
  · have henc_sub : ECDSAAdd.wires enc4 ⊆ ({14111, 19816, 838, 14112, 19815, 19814, 14113} : Finset Wire) := by
      decide
    have hdec_sub : ECDSAAdd.wires dec4 ⊆ ({14111, 19816, 838, 14112, 19815, 19814, 14113} : Finset Wire) := by
      decide
    have h7S : ({14111, 19816, 838, 14112, 19815, 19814, 14113} : Finset Wire) ⊆ S.toFinset := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      apply List.mem_toFinset.mpr
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    have henc : ECDSAAdd.wires enc4 ⊆ S.toFinset := henc_sub.trans h7S
    have hdec : ECDSAAdd.wires dec4 ⊆ S.toFinset := hdec_sub.trans h7S
    have hin : ECDSAAdd.wires (hostBlock3 p) ⊆ (14877 :: 14876 :: 14875 :: 14874 :: S).toFinset := by
      apply hostBlock3_wires p (14877 :: 14876 :: 14875 :: 14874 :: S)
        (by simp [hroot]) (by simp [hctl]) (by simp [hctl3]) hR _ hc hc3
      intro w hw
      rcases h w hw with e | e | e | e | e | e | e | e
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr (Or.inl e))
      · exact Or.inr (Or.inr (Or.inr (by simp [e, hostWire4])))
      · exact Or.inr (Or.inr (Or.inr (by simp [e, hostWire5])))
      · exact Or.inr (Or.inr (Or.inr (by simp [e, hostWire6])))
      · exact Or.inr (Or.inr (Or.inr (by simp [e, hostWire7])))
      · exact Or.inr (Or.inr (Or.inr (by simp [e])))
    have hq11 : (14111 : Wire) ∉ ECDSAAdd.wires (hostBlock3 p) :=
      hostBlock3_avoid_extra p 14111 hcond.2.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hq16 : (19816 : Wire) ∉ ECDSAAdd.wires (hostBlock3 p) :=
      hostBlock3_avoid_extra p 19816 hcond.2.2.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hq838 : (838 : Wire) ∉ ECDSAAdd.wires (hostBlock3 p) :=
      hostBlock3_avoid_extra p 838 hcond.2.2.2.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hq12 : (14112 : Wire) ∉ ECDSAAdd.wires (hostBlock3 p) :=
      hostBlock3_avoid_extra p 14112 hcond.2.2.2.2.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hmid : ECDSAAdd.wires (progRelabel perm4 (hostBlock3 p)) ⊆ S.toFinset := by
      rw [relabel_wires]
      intro w hw
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      have hvs := List.mem_toFinset.mp (hin hv)
      apply List.mem_toFinset.mpr
      simp only [List.mem_cons] at hvs
      rcases hvs with rfl | rfl | rfl | rfl | hvs
      · simpa [perm4] using hc11
      · simpa [perm4] using hc16
      · simpa [perm4] using hc838
      · simpa [perm4] using hc12
      · unfold perm4
        split_ifs with e1 e2 e3 e4 e5 e6 e7 e8
        · exact hc11
        · exact absurd (e2 ▸ hv) hq11
        · exact hc16
        · exact absurd (e4 ▸ hv) hq16
        · exact hc838
        · exact absurd (e6 ▸ hv) hq838
        · exact hc12
        · exact absurd (e8 ▸ hv) hq12
        · exact hvs
    simp only [ECDSAAdd.wires_append, Finset.union_subset_iff]
    exact ⟨⟨henc, hmid⟩, hdec⟩
  · have hno : ¬(14877 ∈ ECDSAAdd.wires p ∨ 14876 ∈ ECDSAAdd.wires p ∨
        14875 ∈ ECDSAAdd.wires p ∨ 14874 ∈ ECDSAAdd.wires p) :=
      fun h0 => hcond ⟨h0, hc4 h0⟩
    apply hostBlock3_wires p S hroot hctl hctl3 hR _ hc hc3
    intro w hw
    rcases h w hw with e | e | e | e | e | e | e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Or.inl e))
    · rw [hostWire4] at e; subst e; exact absurd (Or.inl hw) hno
    · rw [hostWire5] at e; subst e; exact absurd (Or.inr (Or.inl hw)) hno
    · rw [hostWire6] at e; subst e; exact absurd (Or.inr (Or.inr (Or.inl hw))) hno
    · rw [hostWire7] at e; subst e; exact absurd (Or.inr (Or.inr (Or.inr hw))) hno
    · exact Or.inr (Or.inr (Or.inr e))

/-! ### `hostCode7`, `HostOK7`, `CodeHost7`, and `rowC_host7` -/

def hostCode7 {n} (code : WCode n) : WCode n :=
  if code.all isLit then
    [.literal (hostBlock7 (ECDSAAdd.Baselines.normalizeProgram (litProg code)))]
  else normalizeW code

def hostCodeExtra {n} (code : WCode n) : Nat :=
  if code.all isLit then
    hostExtra (ECDSAAdd.Baselines.normalizeProgram (litProg code))
  else 0

theorem hostCode7_eq_host {n} {code : WCode n} (h : code.all isLit = true) :
    hostCode7 code = [.literal (hostBlock7 (ECDSAAdd.Baselines.normalizeProgram (litProg code)))] := by
  simp [hostCode7, h]

theorem hostCode7_eq_norm {n} {code : WCode n} (h : ¬ code.all isLit = true) :
    hostCode7 code = normalizeW code := by
  simp [hostCode7, h]

theorem hostCode7_layouts {n} (bits paths : List Wire) (root : Wire) (code : WCode n)
    (hl : LookupLayouts bits paths root (normalizeW code)) : LookupLayouts bits paths root (hostCode7 code) := by
  by_cases h : code.all isLit = true
  · rw [hostCode7_eq_host h]
    exact ⟨hl.1, fun c ps hm => by simp at hm⟩
  · rw [hostCode7_eq_norm h]
    exact hl

theorem hostCode7_counts {n} (bits paths : List Wire) (root : Wire) (code : WCode n) :
    codeRecords bits paths root (hostCode7 code) = codeRecords bits paths root (normalizeW code) ∧
    literalToffolis (hostCode7 code) = literalToffolis (normalizeW code) + hostCodeExtra code ∧
    traversals (hostCode7 code) = traversals code := by
  by_cases h : code.all isLit = true
  · rw [hostCode7_eq_host h]
    obtain ⟨h1, h2, -, h4⟩ := litProg_counts bits paths root code ((allLit_iff code).mp h)
    refine ⟨?_, ?_, ?_⟩
    · simp only [codeRecords, h1, hostBlock7_meas, ECDSAAdd.Baselines.normalize_measurements, Nat.add_zero]
    · simp only [literalToffolis, hostCodeExtra, h, ↓reduceIte, h2, hostBlock7_toffoli, Nat.add_zero]
    · simp only [traversals, h4]
  · rw [hostCode7_eq_norm h]
    refine ⟨rfl, ?_, traversals_normalize code⟩
    simp [hostCodeExtra, h]

theorem hostCode7_slots {n} (bits : List Wire) (code : WCode n) :
    codeSlots bits (hostCode7 code) ≤ codeSlots bits (normalizeW code) + 26 := by
  by_cases h : code.all isLit = true
  · rw [hostCode7_eq_host h]
    obtain ⟨-, -, h3, -⟩ := litProg_counts bits ([] : List Wire) 0 code ((allLit_iff code).mp h)
    rw [h3]
    have hs := hostBlock7_slots (n := n) (ECDSAAdd.Baselines.normalizeProgram (litProg code))
    simp only [codeSlots]
    omega
  · rw [hostCode7_eq_norm h]
    omega

theorem hostCodeExtra_zero_of_avoidsB (code : WCode 32768) (hav : AvoidsB code) :
    hostCodeExtra code = 0 := by
  unfold hostCodeExtra
  split_ifs
  · apply hostExtra_zero_of
    intro w hw hm
    rw [ECDSAAdd.Baselines.normalize_wires] at hm
    obtain ⟨p, hp, hwp⟩ := litProg_wires code w hm
    exact hav.1 w hw p hp hwp
  · rfl

theorem hostCodeExtra_le {n} (code : WCode n) : hostCodeExtra code ≤ 2 := by
  unfold hostCodeExtra
  split_ifs
  · exact hostExtra_le _
  · omega

def HostOK4 {n} : Block2 n → ECDSAAdd.State → Prop
  | .plain code, st =>
      host4Set (litProg code) →
        FlagInv7 st.basis ∧ Clean4 st.basis ∧
        ∀ m, Clean4 (ECDSAAdd.run (litProg code) m st).basis ∧
          (ECDSAAdd.run (litProg code) m st).basis 14113 = st.basis 14113
  | .unit _, _ => True

def HostOK7 {n} (b : Block2 n) (st : ECDSAAdd.State) : Prop :=
  HostOK b st ∧ HostOK4 b st

def CodeHost4 {n} (read : ConstantBit n → Bool) (address : Nat) : Code n → ECDSAAdd.State → Prop
  | [], _ => True
  | b :: code, st => HostOK4 (toBlock2 b) st ∧
      ∀ m, m.length = ECDSAAdd.measurementCount (blockReference read address b) →
        CodeHost4 read address code (ECDSAAdd.run (blockReference read address b) m st)

def CodeHost4_2 {n} (read : ConstantBit n → Bool) (address : Nat) : Code2 n → ECDSAAdd.State → Prop
  | [], _ => True
  | b :: code, st => HostOK4 b st ∧
      ∀ m, m.length = ECDSAAdd.measurementCount (blockReference2 read address b) →
        CodeHost4_2 read address code (ECDSAAdd.run (blockReference2 read address b) m st)

def CodeHost7 {n} (read : ConstantBit n → Bool) (address : Nat) : Code2 n → ECDSAAdd.State → Prop
  | [], _ => True
  | b :: code, st => HostOK7 b st ∧
      ∀ m, m.length = ECDSAAdd.measurementCount (blockReference2 read address b) →
        CodeHost7 read address code (ECDSAAdd.run (blockReference2 read address b) m st)

theorem codeHost7_of_pair {n} (read : ConstantBit n → Bool) (address : Nat) (code : Code2 n)
    (st : ECDSAAdd.State) (h1 : CodeHost2 read address code st) (h2 : CodeHost4_2 read address code st) :
    CodeHost7 read address code st := by
  induction code generalizing st with
  | nil => trivial
  | cons b code ih =>
    exact ⟨⟨h1.1, h2.1⟩, fun m hm => ih _ (h1.2 m hm) (h2.2 m hm)⟩

theorem host4_append {n} (read : ConstantBit n → Bool) (address : Nat) (a b : Code n)
    (st : ECDSAAdd.State) (ha : CodeHost4 read address a st)
    (hb : ∀ m, m.length = ECDSAAdd.measurementCount (reference read address a) →
      CodeHost4 read address b (ECDSAAdd.run (reference read address a) m st)) :
    CodeHost4 read address (a ++ b) st := by
  induction a generalizing st with
  | nil => simpa [CodeHost4, ECDSAAdd.run] using hb [] rfl
  | cons x xs ih =>
    refine ⟨ha.1, ?_⟩
    intro m hm
    apply ih _ (ha.2 m hm)
    intro tail ht
    have hc := hb (m ++ tail) (by simp [ECDSAAdd.measurementCount_append, hm, ht])
    rw [reference_cons, run_append_records _ _ m tail st hm] at hc
    exact hc

theorem host4_split {n} (read : ConstantBit n → Bool) (address : Nat) (a b : Code n)
    (st : ECDSAAdd.State) (h : CodeHost4 read address (a ++ b) st) :
    CodeHost4 read address a st ∧ ∀ m, m.length = ECDSAAdd.measurementCount (reference read address a) →
      CodeHost4 read address b (ECDSAAdd.run (reference read address a) m st) := by
  induction a generalizing st with
  | nil =>
    exact ⟨trivial, fun m _ => by
      simpa [reference, erase, specialize, ECDSAAdd.ShorPort.Tmpl.instantiate, ECDSAAdd.run] using h⟩
  | cons x xs ih =>
    rw [List.cons_append] at h
    refine ⟨⟨h.1, fun m hm => (ih _ (h.2 m hm)).1⟩, fun m hm => ?_⟩
    rw [reference_cons, ECDSAAdd.measurementCount_append] at hm
    rw [reference_cons, ECDSAAdd.run_append]
    exact (ih _ (h.2 _ (by rw [List.length_take]; omega))).2 _ (by rw [List.length_drop]; omega)

theorem host4_2_append {n} (read : ConstantBit n → Bool) (address : Nat) (a b : Code2 n)
    (st : ECDSAAdd.State) (ha : CodeHost4_2 read address a st)
    (hb : ∀ m, m.length = ECDSAAdd.measurementCount (reference2 read address a) →
      CodeHost4_2 read address b (ECDSAAdd.run (reference2 read address a) m st)) :
    CodeHost4_2 read address (a ++ b) st := by
  induction a generalizing st with
  | nil => simpa [CodeHost4_2, ECDSAAdd.run] using hb [] rfl
  | cons x xs ih =>
    refine ⟨ha.1, ?_⟩
    intro m hm
    apply ih _ (ha.2 m hm)
    intro tail ht
    have hc := hb (m ++ tail) (by simp [ECDSAAdd.measurementCount_append, hm, ht])
    rw [reference2_cons, run_append_records _ _ m tail st hm] at hc
    exact hc

theorem host4_map {n} (read : ConstantBit n → Bool) (address : Nat) (code : Code n)
    (st : ECDSAAdd.State) (h : CodeHost4 read address code st) :
    CodeHost4_2 read address (code.map toBlock2) st := by
  induction code generalizing st with
  | nil => trivial
  | cons b code ih =>
    rw [List.map_cons]
    refine ⟨h.1, fun m hm => ?_⟩
    rw [blockReference2_map] at hm ⊢
    exact ih _ (h.2 m hm)

theorem head_avoidsB : AvoidsB scrHead := by
  rw [scrHead]
  refine avoidsB_append (avoidsB_append ?_ ?_) ?_
  · refine avoidsB_lit _ fun w hw hm => ?_
    simp only [ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, Finset.notMem_empty, or_false, streamLayout_control, streamLayout_dbl] at hm
    rw [mem_poolBand] at hw; dsimp only [Wire] at *; rcases hm with rfl | rfl <;> omega
  · refine avoidsB_lit _ fun w hw hm => ?_
    simp only [ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, Finset.notMem_empty, or_false, streamLayout_control, streamLayout_eqX] at hm
    rw [mem_poolBand] at hw; dsimp only [Wire] at *; rcases hm with rfl | rfl <;> omega
  · refine avoidsB_lit _ fun w hw hm => ?_
    simp only [zeroFlag, ECDSAAdd.wires, ECDSAAdd.Instr.wires, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, Finset.notMem_empty, or_false, streamLayout_fin, streamLayout_control,
      streamLayout_infSel] at hm
    rw [mem_poolBand] at hw; dsimp only [Wire] at *; omega

theorem guard5_avoidsB : AvoidsB (wLiteral (n := 32768) guard5) :=
  avoidsB_lit _ (wires_avoid_of guard5_subset (fun w hw h => band_not_poolBand w (lists_band.2.2.1 w h) hw))

theorem negXReg_avoidsB : AvoidsB (wLiteral (n := 32768) negXReg) :=
  avoidsB_lit _ (wires_avoid_of negXReg_subset (fun w hw h => band_not_poolBand w (lists_band.2.2.2 w h) hw))

theorem zrep_avoidsB : AvoidsB (wLiteral (n := 32768) (ECDSAAdd.Frontier.zrep streamLayout)) :=
  avoidsB_lit _ zrep_avoidB

theorem hostOK4_avoid (code : WCode 32768) (hav : AvoidsB code) (st : ECDSAAdd.State) :
    HostOK4 (.plain code) st := by
  rintro ⟨h1 | h2 | h3 | h4, -⟩
  · obtain ⟨p, hp, hw⟩ := litProg_wires code 14877 h1
    exact absurd hw (hav.1 14877 (by decide) p hp)
  · obtain ⟨p, hp, hw⟩ := litProg_wires code 14876 h2
    exact absurd hw (hav.1 14876 (by decide) p hp)
  · obtain ⟨p, hp, hw⟩ := litProg_wires code 14875 h3
    exact absurd hw (hav.1 14875 (by decide) p hp)
  · obtain ⟨p, hp, hw⟩ := litProg_wires code 14874 h4
    exact absurd hw (hav.1 14874 (by decide) p hp)

theorem values_clean4 {X Y : ECDSAAdd.Fp} {G : Bool} {base s : BasisState}
    (h : PointDialogValues streamLayout X Y G base s) : Clean4 s := by
  have hc : ∀ q ∈ poolBand, s q = false := fun q hq =>
    (regValue_zero _ _).mp h.clean q (poolBand_pool q hq)
  exact ⟨hc 14877 (by decide), hc 14876 (by decide), hc 14875 (by decide), hc 14874 (by decide)⟩

theorem values_flagInv7 {X Y : ECDSAAdd.Fp} {G : Bool} {base s : BasisState}
    (h : PointDialogValues streamLayout X Y G base s) (_hG : base 14113 = G)
    (hf : FlagInv7 base) : FlagInv7 s := by
  have hout : ∀ q, q ∈ ([14111, 19816, 838, 14112, 19815, 19814, 14113] : List Wire) → s q = base q := by
    intro q hq
    apply h.rest q
    intro hm
    simp only [streamLayout_point, List.mem_append, List.mem_range'_1] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hm with hm | hm
    · rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    · rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  rw [FlagInv7, hout 14111 (by simp), hout 19816 (by simp), hout 838 (by simp),
    hout 14112 (by simp), hout 19815 (by simp), hout 19814 (by simp), hout 14113 (by simp)]
  exact hf

structure CheckedH4 {n} (read : ConstantBit n → Bool) (address : Nat)
    (Pre : BasisState → Prop) (code : Code n) (Post : BasisState → Prop) : Prop where
  checked : Checked read address Pre code Post
  host4 : ∀ st, Pre st.basis → CodeHost4 read address code st

namespace CheckedH4
variable {n : Nat} {read : ConstantBit n → Bool} {address : Nat}
variable {A B C : BasisState → Prop} {a b : Code n}

theorem seq (ha : CheckedH4 read address A a B) (hb : CheckedH4 read address B b C) :
    CheckedH4 read address A (a ++ b) C :=
  ⟨ha.checked.seq hb.checked, fun st hs => host4_append read address a b st (ha.host4 st hs)
    (fun m _ => hb.host4 _ (ha.checked.correct st m hs).2)⟩

theorem masked {site : MaskedSite n} (h : Checked read address A ([.masked site] : Code n) B) :
    CheckedH4 read address A ([.masked site] : Code n) B :=
  ⟨h, fun _ _ => ⟨trivial, fun _ _ => trivial⟩⟩

theorem plainV {p : ECDSAAdd.Program} {X Y X' Y' : ECDSAAdd.Fp} {G : Bool} {base : BasisState}
    (hG : base 14113 = G) (hf : FlagInv7 base)
    (h : Checked read address (PointDialogValues streamLayout X Y G base) ([.plain (wLiteral p)] : Code n)
      (PointDialogValues streamLayout X' Y' G base)) :
    CheckedH4 read address (PointDialogValues streamLayout X Y G base) ([.plain (wLiteral p)] : Code n)
      (PointDialogValues streamLayout X' Y' G base) := by
  refine ⟨h, fun st hs => ⟨fun _ => ?_, fun _ _ => trivial⟩⟩
  refine ⟨values_flagInv7 hs hG hf, values_clean4 hs, fun m => ?_⟩
  have post : PointDialogValues streamLayout X' Y' G base (ECDSAAdd.run (litProg (wLiteral (n := n) p)) m st).basis := by
    have e := (h.correct st m hs).2
    simp only [reference, erase_plain] at e
    rw [litProg_inst read (wLiteral (n := n) p) address (by simp [wLiteral])] at e
    exact e
  refine ⟨values_clean4 post, ?_⟩
  have g1 := hs.generic
  have g2 := post.generic
  rw [streamLayout_gen] at g1 g2
  exact g2.trans g1.symm

end CheckedH4

theorem literal_checkedV4 {n} (read : ConstantBit n → Bool) (address : Nat) (p : ECDSAAdd.Program)
    {X Y X' Y' : ECDSAAdd.Fp} {G : Bool} {base : BasisState}
    (hG : base 14113 = G) (hf : FlagInv7 base)
    (h : ECDSAAdd.Triple (PointDialogValues streamLayout X Y G base) p
      (PointDialogValues streamLayout X' Y' G base)) :
    CheckedH4 read address (PointDialogValues streamLayout X Y G base) ([.plain (wLiteral p)] : Code n)
      (PointDialogValues streamLayout X' Y' G base) :=
  CheckedH4.plainV hG hf (literal_checked read address p _ _ h)

attribute [local irreducible] ECDSAAdd.run

theorem chainH4_plain (read : ConstantBit 32768 → Bool) (address : Nat)
    (rows : Nat → Fin 32768)
    {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy) (hr : RowReads read (rows address) (.some hc))
    (X Y : ECDSAAdd.Fp) (G : Bool) (base : BasisState)
    (hroot : base windowRoot = true) (hctl : base streamLayout.control = true)
    (hG : base 14113 = G) (hf : FlagInv7 base)
    (hD : base streamLayout.doubleSelect = false) (hI : base streamLayout.genericSelect = false)
    (X0 X1 a X3 X5 X6 Y6 : ECDSAAdd.Fp)
    (hX0 : X0.val = X.val ^^^ (if base streamLayout.point.finite then 0 else 5))
    (hX1d : X1 = X0 - cx) (hX1 : X1 ≠ 0) (ha : a = (Y - cy)/X1)
    (hX3d : X3 = X1 - (if G then a*a else 0) + (if G then 3*cx else 0)) (hX3 : X3 ≠ 0)
    (hX5 : X5 = (if G then -X3 else X3) + cx)
    (hX6 : X6.val = X5.val ^^^ (if base streamLayout.point.finite then 0 else 5))
    (hY6 : Y6 = a * X3 + (if G then -cy else cy)) :
    CheckedH4 read address (PointDialogValues streamLayout X Y G base) (generic3' rows)
      (PointDialogValues streamLayout X6 Y6 G base) := by
  have hw := streamLayout_widths
  have hn := streamLayout_nodup
  have hex : ¬ (base streamLayout.doubleSelect = true ∧ base streamLayout.genericSelect = true) := by
    rw [hD]; simp
  have gid : ∀ (Z : ECDSAAdd.Fp), Z.val = (Z.val ^^^ (if base streamLayout.doubleSelect then 5 else 0)) ^^^
      (if base streamLayout.genericSelect then 5 else 0) := by
    intro Z; rw [hD, hI]; simp
  have z1 := literal_checkedV4 read address _ hG hf (ECDSAAdd.Frontier.zrep_step streamLayout hw hn X X0 Y G base hX0)
  have p1 := CheckedH4.masked (pair1_checked read address rows hc hr X0 Y G base hroot hctl)
  rw [← hX1d] at p1
  have g1 := CheckedH4.plainV hG hf (guard5_checked read address X1 X1 (Y - cy) G base hex (gid X1))
  have d1 := literal_checkedV4 read address _ hG hf
    (ECDSAAdd.Frontier.arith3F_step streamLayout hw hn X1 (Y - cy) G base false hX1)
  simp only [Bool.false_eq_true, if_false] at d1
  rw [← ha] at d1
  have g2 := CheckedH4.plainV hG hf (guard5_checked read address X1 X1 a G base hex (gid X1))
  have sq := literal_checkedV4 read address _ hG hf
    (ECDSAAdd.Frontier.GenericOB5.square_step streamLayout hw hn X1 a G base)
  have t3 := CheckedH4.masked (addX_checked read address streamLayout hw hn (X1 - (if G then a * a else 0)) a G base (3*cx)
    (wFields rows .tripleX) (row_bits hc hr .tripleX (3*cx) (field_some_tripleX hc)))
  rw [← hX3d] at t3
  have g3 := CheckedH4.plainV hG hf (guard5_checked read address X3 X3 a G base hex (gid X3))
  have m1 := literal_checkedV4 read address _ hG hf
    (ECDSAAdd.Frontier.arith3F_step streamLayout hw hn X3 a G base true hX3)
  simp only [if_true] at m1
  have g4 := CheckedH4.plainV hG hf (guard5_checked read address X3 X3 (a * X3) G base hex (gid X3))
  have ng := literal_checkedV4 read address _ hG hf (negXReg_step X3 (a * X3) G base (fun _ => hX3))
  have p2 := CheckedH4.masked (pair2_checked read address rows hc hr (if G then -X3 else X3) (a * X3) G base hroot hctl)
  rw [← hX5, ← hY6] at p2
  have z2 := literal_checkedV4 read address _ hG hf (ECDSAAdd.Frontier.zrep_step streamLayout hw hn X5 X6 Y6 G base hX6)
  have h := (((((((((((z1.seq p1).seq g1).seq d1).seq g2).seq sq).seq t3).seq g3).seq m1).seq g4).seq ng).seq p2).seq z2
  simpa only [generic3', preBlock, generic3, constAdd, List.append_assoc, List.cons_append, List.nil_append] using h

theorem chainH4_toggle (read : ConstantBit 32768 → Bool) (address : Nat)
    (rows : Nat → Fin 32768)
    {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy) (hr : RowReads read (rows address) (.some hc))
    (X Y : ECDSAAdd.Fp) (base : BasisState)
    (hroot : base windowRoot = true) (hctl : base streamLayout.control = true)
    (hG : base 14113 = false) (hf : FlagInv7 base)
    (hfin : base streamLayout.point.finite = true)
    (hex : ¬ (base streamLayout.doubleSelect = true ∧ base streamLayout.genericSelect = true))
    (hD : base streamLayout.doubleSelect = true → X = cx) (hI : base streamLayout.genericSelect = true → X = cx)
    (hX1 : base streamLayout.doubleSelect = false → base streamLayout.genericSelect = false → X - cx ≠ 0) :
    CheckedH4 read address (PointDialogValues streamLayout X Y false base) (generic3' rows)
      (PointDialogValues streamLayout X Y false base) := by
  have hw := streamLayout_widths
  have hn := streamLayout_nodup
  set E := (base streamLayout.doubleSelect || base streamLayout.genericSelect) with hE
  let xg : ECDSAAdd.Fp := if E then 5 else X - cx
  have hxg0 : xg ≠ 0 := by
    simp only [xg]
    split
    · exact ECDSAAdd.Frontier.finFive_ne_zero
    · rename_i hne
      simp only [hE, Bool.or_eq_true, not_or, Bool.not_eq_true] at hne
      exact hX1 hne.1 hne.2
  have hzero : E = true → X - cx = 0 := by
    intro h
    simp only [hE, Bool.or_eq_true] at h
    rcases h with h | h
    · rw [hD h, sub_self]
    · rw [hI h, sub_self]
  have fwd : xg.val = ((X - cx).val ^^^ (if base streamLayout.doubleSelect then 5 else 0)) ^^^
      (if base streamLayout.genericSelect then 5 else 0) := by
    simp only [xg]
    cases hd : base streamLayout.doubleSelect <;> cases hi : base streamLayout.genericSelect
    · simp [hE, hd, hi]
    · have : E = true := by simp [hE, hd, hi]
      simp only [this, if_true, hd, hi, if_false]
      rw [hzero this, ZMod.val_zero, ECDSAAdd.Frontier.finFive_val]; simp
    · have : E = true := by simp [hE, hd, hi]
      simp only [this, if_true, hd, hi, if_false]
      rw [hzero this, ZMod.val_zero, ECDSAAdd.Frontier.finFive_val]; simp
    · exact absurd ⟨hd, hi⟩ hex
  have back : (X - cx).val = (xg.val ^^^ (if base streamLayout.doubleSelect then 5 else 0)) ^^^
      (if base streamLayout.genericSelect then 5 else 0) := by
    simp only [xg]
    cases hd : base streamLayout.doubleSelect <;> cases hi : base streamLayout.genericSelect
    · simp [hE, hd, hi]
    · have : E = true := by simp [hE, hd, hi]
      simp only [this, if_true, hd, hi, if_false]
      rw [hzero this, ZMod.val_zero, ECDSAAdd.Frontier.finFive_val]; simp
    · have : E = true := by simp [hE, hd, hi]
      simp only [this, if_true, hd, hi, if_false]
      rw [hzero this, ZMod.val_zero, ECDSAAdd.Frontier.finFive_val]; simp
    · exact absurd ⟨hd, hi⟩ hex
  have zid : X.val = X.val ^^^ (if base streamLayout.point.finite then 0 else 5) := by rw [hfin]; simp
  have z1 := literal_checkedV4 read address _ hG hf (ECDSAAdd.Frontier.zrep_step streamLayout hw hn X X Y false base zid)
  have p1 := CheckedH4.masked (pair1_checked read address rows hc hr X Y false base hroot hctl)
  have g1 := CheckedH4.plainV hG hf (guard5_checked read address (X - cx) xg (Y - cy) false base hex fwd)
  have d1 := literal_checkedV4 read address _ hG hf (ECDSAAdd.Frontier.arith3F_step streamLayout hw hn xg (Y - cy) false base false hxg0)
  simp only [Bool.false_eq_true, if_false] at d1
  have g2 := CheckedH4.plainV hG hf (guard5_checked read address xg (X - cx) ((Y - cy)/xg) false base hex back)
  have sq := literal_checkedV4 read address _ hG hf (ECDSAAdd.Frontier.GenericOB5.square_step streamLayout hw hn (X - cx) ((Y - cy)/xg) false base)
  simp only [Bool.false_eq_true, if_false, sub_zero] at sq
  have t3 := CheckedH4.masked (addX_checked read address streamLayout hw hn (X - cx) ((Y - cy)/xg) false base (3*cx) (wFields rows .tripleX)
    (row_bits hc hr .tripleX (3*cx) (field_some_tripleX hc)))
  simp only [Bool.false_eq_true, if_false, add_zero] at t3
  have g3 := CheckedH4.plainV hG hf (guard5_checked read address (X - cx) xg ((Y - cy)/xg) false base hex fwd)
  have m1 := literal_checkedV4 read address _ hG hf (ECDSAAdd.Frontier.arith3F_step streamLayout hw hn xg ((Y - cy)/xg) false base true hxg0)
  simp only [if_true, div_mul_cancel₀ _ hxg0] at m1
  have g4 := CheckedH4.plainV hG hf (guard5_checked read address xg (X - cx) (Y - cy) false base hex back)
  have ng := literal_checkedV4 read address _ hG hf (negXReg_step (X - cx) (Y - cy) false base (fun h => by cases h))
  simp only [Bool.false_eq_true, if_false] at ng
  have p2 := CheckedH4.masked (pair2_checked read address rows hc hr (X - cx) (Y - cy) false base hroot hctl)
  simp only [Bool.false_eq_true, if_false, sub_add_cancel] at p2
  have z2 := literal_checkedV4 read address _ hG hf (ECDSAAdd.Frontier.zrep_step streamLayout hw hn X X Y false base zid)
  have h := (((((((((((z1.seq p1).seq g1).seq d1).seq g2).seq sq).seq t3).seq g3).seq m1).seq g4).seq ng).seq p2).seq z2
  simpa only [generic3', preBlock, generic3, constAdd, List.append_assoc, List.cons_append, List.nil_append] using h

theorem generic3_host4 (read : ConstantBit 32768 → Bool) (address : Nat)
    (rows : Nat → Fin 32768)
    (R : Point) {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (hr : RowReads read (rows address) (.some hc)) (h₁ : cy ≠ -cy)
    (h₂ : dialogExceptionEnabled (.some hc))
    (st : ECDSAAdd.State)
    (hs : PointDialogBoundary streamLayout R true (flags streamLayout R (.some hc) true cy) st.basis)
    (hroot : st.basis windowRoot = true) :
    CodeHost4 read address (generic3' rows) st := by
  classical
  have hp := (point_holds _ _ _).mp hs.point
  have hctl : st.basis streamLayout.control = true := hs.control
  have hCneg := some_ne_neg hc h₁
  have hC0 : (.some hc : Point) ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  have rd := dialogFlagState_read streamLayout streamLayout_nodup (dialogInfinity true R)
    (dialogDouble true R (.some hc)) (dialogInversePoint true R (.some hc)) (dialogOrdinary true R (.some hc))
    (true && decide (dialogExceptionEnabled (.some hc))) (dialogException true R (.some hc))
    (true && decide (cy ≠ -cy))
  have sO : st.basis 19816 = dialogInfinity true R := by
    rw [← streamLayout_infSel]
    exact (hs.flags _ (by simp [inPlaceFlags])).trans rd.1
  have sD : st.basis 19815 = dialogDouble true R (.some hc) := by
    rw [← streamLayout_dblSel]
    exact (hs.flags _ (by simp [inPlaceFlags])).trans rd.2.1
  have sI : st.basis 19814 = dialogInversePoint true R (.some hc) := by
    rw [← streamLayout_genSel]
    exact (hs.flags _ (by simp [inPlaceFlags])).trans rd.2.2.1
  have sG : st.basis 14113 = dialogOrdinary true R (.some hc) := by
    rw [← streamLayout_gen]
    exact (hs.flags _ (by simp [inPlaceFlags])).trans rd.2.2.2.1
  have sE : st.basis 14111 = (true && decide (dialogExceptionEnabled (.some hc))) := by
    rw [← streamLayout_eqX]
    exact (hs.flags _ (by simp [inPlaceFlags])).trans rd.2.2.2.2.1
  have sH : st.basis 14112 = dialogException true R (.some hc) := by
    rw [← streamLayout_eqNegY]
    exact (hs.flags _ (by simp [inPlaceFlags])).trans rd.2.2.2.2.2.1
  have sD' : st.basis 19815 = decide (R = (.some hc : Point)) := by
    rw [sD, dialogDouble, decide_eq_true hCneg]; simp
  have sI' : st.basis 19814 = decide (R = -(.some hc : Point)) := by
    rw [sI]; simp [dialogInversePoint]
  have h11 : st.basis 14111 = true := by
    rw [sE, decide_eq_true h₂]; rfl
  have hfin_eq : st.basis 838 = !dialogInfinity true R := by
    rw [← streamLayout_fin]
    cases R with
    | zero =>
      have hp0 : st.basis streamLayout.point.finite = false := ((point_holds _ _ _).mp hs.point).1
      rw [hp0, dialogInfinity, show (WeierstrassCurve.Affine.Point.zero : Point) = 0 from rfl]
      simp
    | some hrp =>
      have hp1 := (point_holds _ _ _).mp hs.point
      rw [hp1.1, dialogInfinity, decide_eq_false (WeierstrassCurve.Affine.Point.some_ne_zero hrp)]
      rfl
  have h16 : st.basis 19816 = !st.basis 838 := by
    rw [sO, hfin_eq, Bool.not_not]
  have h838 : st.basis 838 = (st.basis 14113 ^^ st.basis 19815 ^^ st.basis 19814 ^^ st.basis 14112) := by
    rw [hfin_eq, sG, sD, sI, sH, dialogOrdinary]
    cases dialogInfinity true R <;> cases dialogDouble true R (.some hc) <;>
      cases dialogInversePoint true R (.some hc) <;> cases dialogException true R (.some hc) <;> rfl
  have hex : ¬ (st.basis 19815 = true ∧ st.basis 19814 = true) := by
    rw [sD', sI']
    simp only [decide_eq_true_eq, not_and]
    intro h1 h2
    exact hCneg (h1.symm.trans h2)
  have hDI : st.basis 19815 = true → st.basis 19814 = false := by
    intro hD1
    cases hI1 : st.basis 19814
    · rfl
    · exact absurd ⟨hD1, hI1⟩ hex
  have hH_ex : st.basis 14112 = true → st.basis 19815 = false ∧ st.basis 19814 = false := by
    intro hh
    rw [sH] at hh
    constructor
    · cases hD1 : st.basis 19815
      · rfl
      · rw [sD', decide_eq_true_eq] at hD1
        rw [hD1, dialogException_self] at hh; cases hh
    · cases hI1 : st.basis 19814
      · rfl
      · rw [sI', decide_eq_true_eq] at hI1
        rw [hI1, dialogException_neg] at hh; cases hh
  have hf : FlagInv7 st.basis := ⟨h11, h16, h838, hDI, hH_ex⟩
  cases R with
  | zero =>
    have hG : st.basis 14113 = false := by
      rw [sG]
      cases h : dialogOrdinary true 0 (.some hc)
      · rfl
      · exact absurd rfl ((dialogOrdinary_true true 0 _ hC0).mp h).2.1
    have hD0 : st.basis streamLayout.doubleSelect = false := by
      rw [streamLayout_dblSel, sD']; simp [hC0.symm]
    have hI0 : st.basis streamLayout.genericSelect = false := by
      rw [streamLayout_genSel, sI']; simp [(neg_ne_zero.mpr hC0).symm]
    have values : PointDialogValues streamLayout 0 0 false st.basis st.basis :=
      ⟨hp.2.1, hp.2.2, by rw [streamLayout_gen]; exact hG, hs.clean, fun _ _ => rfl⟩
    have hfin : st.basis streamLayout.point.finite = false := hp.1
    have hX1 : (5 : ECDSAAdd.Fp) - cx ≠ 0 := sub_ne_zero.mpr (ECDSAAdd.Frontier.x_ne_five hc).symm
    have new := chainH4_plain read address rows hc hr 0 0 false st.basis hroot hctl hG hf hD0 hI0
      5 (5 - cx) ((0 - cy)/(5 - cx)) (5 - cx) 5 0 0
      (by rw [hfin, ECDSAAdd.Frontier.finFive_val, ZMod.val_zero]; decide) rfl hX1 rfl (by simp) hX1 (by simp)
      (by rw [hfin, ECDSAAdd.Frontier.finFive_val, ZMod.val_zero]; decide)
      (by simp [div_mul_cancel₀ _ hX1])
    exact new.host4 st values
  | @some x y hrp =>
    have hfin : st.basis streamLayout.point.finite = true := hp.1
    cases hG : dialogOrdinary true (.some hrp) (.some hc) with
    | false =>
      have sG' : st.basis 14113 = false := sG.trans hG
      have values : PointDialogValues streamLayout x y false st.basis st.basis :=
        ⟨hp.2.1, hp.2.2, by rw [streamLayout_gen]; exact sG', hs.clean, fun _ _ => rfl⟩
      have hD : st.basis streamLayout.doubleSelect = true → x = cx := by
        rw [streamLayout_dblSel, sD']; intro h
        have := of_decide_eq_true h
        exact (WeierstrassCurve.Affine.Point.some.inj this).1
      have hI : st.basis streamLayout.genericSelect = true → x = cx := by
        rw [streamLayout_genSel, sI']; intro h
        have := of_decide_eq_true h
        rw [WeierstrassCurve.Affine.Point.neg_some] at this
        exact (WeierstrassCurve.Affine.Point.some.inj this).1
      have hX1 : st.basis streamLayout.doubleSelect = false → st.basis streamLayout.genericSelect = false →
          x - cx ≠ 0 := by
        rw [streamLayout_dblSel, streamLayout_genSel, sD', sI']
        intro h1 h2 hz
        rcases (sameX_iff_eq_or_neg hrp hc).mp (sub_eq_zero.mp hz) with h | h
        · exact absurd (decide_eq_true h) (by rw [h1]; decide)
        · exact absurd (decide_eq_true h) (by rw [h2]; decide)
      have new := chainH4_toggle read address rows hc hr x y st.basis hroot hctl sG' hf hfin
        (by rw [streamLayout_dblSel, streamLayout_genSel]; exact hex) hD hI hX1
      exact new.host4 st values
    | true =>
      have he := ((dialogOrdinary_true true _ _ hC0).mp hG).2
      have den := dialog_denominators_ne_zero hrp hc he.2.1 he.2.2.1 he.2.2.2
      have sG' : st.basis 14113 = true := sG.trans hG
      have values : PointDialogValues streamLayout x y true st.basis st.basis :=
        ⟨hp.2.1, hp.2.2, by rw [streamLayout_gen]; exact sG', hs.clean, fun _ _ => rfl⟩
      have hD0 : st.basis streamLayout.doubleSelect = false := by
        rw [streamLayout_dblSel, sD']; exact decide_eq_false he.2.1
      have hI0 : st.basis streamLayout.genericSelect = false := by
        rw [streamLayout_genSel, sI']; exact decide_eq_false he.2.2.1
      let a := genericSlope x y cx cy
      let d := cx - genericX x y cx cy
      have hv := generic_inplace_values x y cx cy den.1
      have ha : (y - cy)/(x - cx) = a := rfl
      have new := chainH4_plain read address rows hc hr x y true st.basis hroot hctl sG' hf hD0 hI0
        x (x - cx) a d (-d + cx) (genericX x y cx cy) (genericY x y cx cy)
        (by rw [hfin]; simp) rfl (sub_ne_zero.mpr den.1) ha
        (by simp only [if_true]; exact hv.2.1.symm) den.2 (by simp only [if_true])
        (by rw [hfin]; simp only [if_true, Nat.xor_zero]; congr 1; simp only [d]; ring)
        (by simp only [if_true]; rw [← sub_eq_add_neg]; exact hv.2.2.symm)
      exact new.host4 st values

theorem rowPost3_host4 (read : ConstantBit 32768 → Bool) (a : Nat) (t : ECDSAAdd.State) :
    CodeHost4_2 read a WEXUnlookup.rowPost3 t := by
  rw [WEXUnlookup.rowPost3]
  exact ⟨hostOK4_avoid _ cornerNeg_avoidsB t, fun _ _ =>
    ⟨trivial, fun _ _ => ⟨trivial, fun _ _ =>
      ⟨hostOK4_avoid _ sfxTailF_avoidsB _, fun _ _ =>
        ⟨hostOK4_avoid _ flip_avoidsB _, fun _ _ => trivial⟩⟩⟩⟩⟩

local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨ShorECDLP.Secp256k1.p_prime⟩

theorem rowC_host4 (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (a : Nat) (s : BasisState) (hs : liveReady s) :
    CodeHost4_2 (readConstant coeffs Q) a WEXUnlookup.rowC ⟨false, s⟩ := by
  let C := Single.Physical.tablePoint coeffs Q a
  have hC : C ≠ 0 := hn _
  have hord : ShorECDLP.order • C = 0 := Single.Physical.tablePoint_order coeffs Q hQ a
  obtain ⟨P0, hP0⟩ := hs.1.2
  have work : ECDSAAdd.regValue streamLayout.work s = 0 :=
    (regValue_zero _ _).mpr (fun w hw => hs.2.1 w (List.mem_append_left _ hw))
  have h838 : (838 : Wire) ∉ streamLayout.work := by
    intro hm; have h := streamWork_lower _ hm; norm_num at h
  have pool : ECDSAAdd.regValue streamLayout.work (flipInfinity s) = 0 :=
    (reg_update_outside _ _ _ _ h838).trans work
  have clean (w : Wire) (hw : w ∈ streamLayout.inPlaceFlags ++ streamLayout.dialogPool) :
      flipInfinity s w = false := (regValue_zero _ _).mp pool w (one_boundary_work_subset streamLayout hw)
  have initial : PointDialogBoundary streamLayout (Bridge.toB P0) true (fun _ => false) (flipInfinity s) := by
    refine ⟨flipInfinity_holds s (Bridge.toB P0) (StreamPoint.of_coordinates s P0 hs.1.1.1.1 hP0), ?_, ?_, ?_⟩
    · simpa [streamLayout_control, flipInfinity, ECDSAAdd.writeBit] using hs.1.1.1.2
    · intro w hw; exact clean w (by simp [hw])
    · exact (regValue_zero _ _).mpr (fun w hw => clean w (by simp [hw]))
  have pre : CodeHost4 (readConstant coeffs Q) a rowPre3 ⟨false, s⟩ :=
    ⟨hostOK4_avoid _ flip_avoidsB _, fun _ _ =>
      ⟨hostOK4_avoid _ head_avoidsB _, fun _ _ => ⟨trivial, fun _ _ => trivial⟩⟩⟩
  have hhead : CodeHost4 (readConstant coeffs Q) a WEXUnlookup.rowHead ⟨false, s⟩ := by
    cases he : Bridge.toB C with
    | zero => exact (hC (congrArg ECDSAAdd.ShorPort.toA he)).elim
    | @some cx cy hc =>
      have ce : C = toA (.some hc) := congrArg toA he
      have hr : RowReads (readConstant coeffs Q) (probeRows a) (.some hc) :=
        readConstant_rowReads coeffs Q _ _ ce
      have ho : ShorECDLP.order • (.some hc : Point) = 0 := by rw [← he]; exact hord
      have hp2 := torsion_unit_remainder_ne_zero (.some hc) ShorECDLP.order 2
        (WeierstrassCurve.Affine.Point.some_ne_zero hc) ho (by norm_num [ShorECDLP.order])
      have hp3 := torsion_unit_remainder_ne_zero (.some hc) ShorECDLP.order 3
        (WeierstrassCurve.Affine.Point.some_ne_zero hc) ho (by norm_num [ShorECDLP.order])
      have hd : (.some hc : Point) + .some hc ≠ 0 := by simpa only [two_nsmul] using hp2
      have ht : (.some hc : Point) + .some hc + .some hc ≠ 0 := by
        simpa only [show (3 : Nat) = 2 + 1 from rfl, succ_nsmul, two_nsmul] using hp3
      have en := enables_true hc hd ht
      have hdo : ShorECDLP.order • ((.some hc : Point) + .some hc) = 0 := by rw [nsmul_add, ho, zero_add]
      have hen : dialogExceptionEnabled (.some hc) := by
        refine ⟨neg_ne_zero.mpr hd, ?_, ?_⟩
        · intro e
          unfold dialogExceptionPoint at e
          have h3 : ((.some hc : Point) + .some hc) + .some hc = 0 := by
            have h0 := add_neg_cancel ((.some hc : Point) + .some hc)
            rwa [e] at h0
          exact ht h3
        · intro e
          unfold dialogExceptionPoint at e
          have h2 : (.some hc : Point) + .some hc = .some hc := neg_inj.mp e
          have h1 : (.some hc : Point) = 0 := by
            have := congrArg (· - (.some hc : Point)) h2
            simpa using this
          exact WeierstrassCurve.Affine.Point.some_ne_zero hc h1
      have g := fun m => generic3_host4 (readConstant coeffs Q) a probeRows (Bridge.toB P0) hc hr en.1 hen _
        (rowPre_boundary (readConstant coeffs Q) a (Bridge.toB P0) hc hr en.1 en.2 hd hdo s initial hs.2.2 m)
        (WEX.root_preserves (readConstant coeffs Q) windowBits windowPaths windowRoot (erase rowPre) a rowPre_placed
          ⟨false, s⟩ hs.2.2 m)
      have hk : ECDSAAdd.measurementCount (reference (readConstant coeffs Q) a rowPre3) =
          ECDSAAdd.measurementCount (reference (readConstant coeffs Q) a rowPre) +
            ECDSAAdd.measurementCount (reference (readConstant coeffs Q) a (preBlock probeRows)) := by
        rw [rowPre3_records, reference_append, ECDSAAdd.measurementCount_append]
      have e1 (m : List Bool) : ECDSAAdd.run (reference (readConstant coeffs Q) a rowPre3) m ⟨false, s⟩ =
          ECDSAAdd.run (reference (readConstant coeffs Q) a (preBlock probeRows))
            (m.drop (ECDSAAdd.measurementCount (reference (readConstant coeffs Q) a rowPre)))
            (ECDSAAdd.run (reference (readConstant coeffs Q) a rowPre) m ⟨false, s⟩) := by
        rw [rowPre3_run, reference_append, run_meas_append]
      rw [WEXUnlookup.rowHead]
      apply host4_append _ _ rowPre3 _ _ pre
      intro m hm
      have gs := host4_split _ _ (preBlock probeRows) (generic3 probeRows) _ (g m)
      rw [e1]
      have hlen : (m.drop (ECDSAAdd.measurementCount (reference (readConstant coeffs Q) a rowPre))).length =
          ECDSAAdd.measurementCount (reference (readConstant coeffs Q) a (preBlock probeRows)) := by
        rw [List.length_drop, hm, hk]; omega
      exact gs.2 _ hlen
  rw [WEXUnlookup.rowC]
  exact host4_2_append _ _ _ _ _ (host4_map _ _ _ _ hhead) (fun _ _ => rowPost3_host4 _ _ _)

theorem rowC_host7 (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (a : Nat) (s : BasisState) (hs : liveReady s) :
    CodeHost7 (readConstant coeffs Q) a WEXUnlookup.rowC ⟨false, s⟩ :=
  codeHost7_of_pair _ _ _ _ (PathShare.rowC_host coeffs Q hQ hn a s hs) (rowC_host4 coeffs Q hQ hn a s hs)

/-! ### Support retirement and compaction for the 4 newly hosted wires (`1612` narrow, `1613` wide) -/

def retiredH7 (w : Nat) : Prop :=
  retiredH w ∨ w = 14877 ∨ w = 14876 ∨ w = 14875 ∨ w = 14874
instance : DecidablePred retiredH7 := fun w =>
  inferInstanceAs (Decidable (retiredH w ∨ w = 14877 ∨ w = 14876 ∨ w = 14875 ∨ w = 14874))

def newSourceH7 : List Wire := sourceSupport.filter (fun w => decide (¬retiredH7 w))

theorem newSourceH7_mem (w : Nat) : w ∈ newSourceH7 ↔ (fixedPort w ∨ oldWork w) ∧ ¬retiredH7 w := by
  rw [newSourceH7, List.mem_filter, sourceSupport_mem, decide_eq_true_eq]

theorem newSourceH7_of_bounds (xs : List Wire) (h : ∀ w ∈ xs, (fixedPort w ∨ oldWork w) ∧ ¬retiredH7 w) :
    xs ⊆ newSourceH7 :=
  fun w hw => (newSourceH7_mem w).mpr (h w hw)

theorem newSourceH7_of_newH (w : Nat) (h : w ∈ newSourceH)
    (h4 : w ≠ 14877) (h5 : w ≠ 14876) (h6 : w ≠ 14875) (h7 : w ≠ 14874) : w ∈ newSourceH7 := by
  obtain ⟨h1, h2⟩ := (newSourceH_mem w).mp h
  exact (newSourceH7_mem w).mpr ⟨h1, fun hr => hr.elim h2 (fun a => a.elim h4 (fun b => b.elim h5 (fun c => c.elim h6 h7)))⟩

theorem newSourceH7_sub_newSourceH : newSourceH7 ⊆ newSourceH := by
  intro w hw
  obtain ⟨h1, h2⟩ := (newSourceH7_mem w).mp hw
  exact (newSourceH_mem w).mpr ⟨h1, fun hr => h2 (Or.inl hr)⟩

theorem relaxed7_of_new (w : Nat) (h : w ∈ newSource) :
    w = hostWire ∨ w = hostWire2 ∨ w = hostWire3 ∨
    w = hostWire4 ∨ w = hostWire5 ∨ w = hostWire6 ∨ w = hostWire7 ∨ w ∈ newSourceH7 := by
  rcases relaxed_of_new w h with e | e | e | e
  · exact Or.inl e
  · exact Or.inr (Or.inl e)
  · exact Or.inr (Or.inr (Or.inl e))
  · by_cases h4 : w = 14877
    · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
    by_cases h5 : w = 14876
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))
    by_cases h6 : w = 14875
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6)))))
    by_cases h7 : w = 14874
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h7))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (newSourceH7_of_newH w e h4 h5 h6 h7)))))))

def tau4Wire (w : Nat) : Nat :=
  if w = 14877 then 15640
  else if w = 15640 then 14877
  else if w = 14876 then 15639
  else if w = 15639 then 14876
  else if w = 14875 then 15638
  else if w = 15638 then 14875
  else if w = 14874 then 15637
  else if w = 15637 then 14874
  else w

theorem tau4Wire_involutive : Function.Involutive tau4Wire := by
  intro w
  unfold tau4Wire
  by_cases h1 : w = 14877; · simp [h1]
  by_cases h2 : w = 15640; · simp [h2]
  by_cases h3 : w = 14876; · simp [h3]
  by_cases h4 : w = 15639; · simp [h4]
  by_cases h5 : w = 14875; · simp [h5]
  by_cases h6 : w = 15638; · simp [h6]
  by_cases h7 : w = 14874; · simp [h7]
  by_cases h8 : w = 15637; · simp [h8]
  simp [h1, h2, h3, h4, h5, h6, h7, h8]

def tau4 : Wire ≃ Wire := ⟨tau4Wire, tau4Wire, tau4Wire_involutive, tau4Wire_involutive⟩

def tauH7 : Wire ≃ Wire := tau4.trans tauH

def piH7 : Wire ≃ Wire := tauH7.trans compactPerm

theorem piH7_apply (w : Wire) : piH7 w = compactWire (tauWireH (tau4Wire w)) := rfl

theorem piH7_fixed (w : Wire) (h : fixedPort w) : piH7 w = w := by
  have h4 : tau4Wire w = w := by
    unfold tau4Wire fixedPort at *
    dsimp only [Wire] at w h ⊢
    have hne : w ≠ 14877 ∧ w ≠ 15640 ∧ w ≠ 14876 ∧ w ≠ 15639 ∧ w ≠ 14875 ∧ w ≠ 15638 ∧ w ≠ 14874 ∧ w ≠ 15637 := by omega
    simp [hne.1, hne.2.1, hne.2.2.1, hne.2.2.2.1, hne.2.2.2.2.1, hne.2.2.2.2.2.1, hne.2.2.2.2.2.2.1, hne.2.2.2.2.2.2.2]
  rw [piH7_apply, h4]
  exact PathShare.piH_fixed w h

theorem piH7_hot (i : Fin 128) : piH7 (hot i) = hot i := by
  have h4 : ∀ j : Fin 128, tau4Wire (hot j) = hot j := by decide
  rw [piH7_apply, h4 i]
  exact PathShare.piH_hot i

theorem piH7_point (w : Wire) (hw : w ∈ pointLogicalWires) : piH7 w = w := by
  have h4 : tau4Wire w = w := by
    have hlt : (w : Nat) < 1000 := by
      simp only [pointLogicalWires, pointCorrectionX, pointCorrectionYInf, List.mem_append,
        List.mem_range'_1, List.mem_singleton, List.not_mem_nil, or_false] at hw
      dsimp only [Wire] at *; omega
    unfold tau4Wire
    dsimp only [Wire] at w hlt ⊢
    have hne : w ≠ 14877 ∧ w ≠ 15640 ∧ w ≠ 14876 ∧ w ≠ 15639 ∧ w ≠ 14875 ∧ w ≠ 15638 ∧ w ≠ 14874 ∧ w ≠ 15637 := by omega
    simp [hne.1, hne.2.1, hne.2.2.1, hne.2.2.2.1, hne.2.2.2.2.1, hne.2.2.2.2.2.1, hne.2.2.2.2.2.2.1, hne.2.2.2.2.2.2.2]
  rw [piH7_apply, h4]
  exact PathShare.piH_point w hw

private theorem freeAt_lt_1612 (i : Nat) (hi : i < 1082) : freeAt i < 1612 := by
  unfold freeAt; split_ifs <;> omega

theorem piH7_bound (w : Nat) (hw : w ∈ newSourceH7) : (piH7 w : Nat) < 1612 := by
  obtain ⟨h1, h2⟩ := (newSourceH7_mem w).mp hw
  unfold retiredH7 retiredH retired at h2
  by_cases hD : w = 15640 ∨ w = 15639 ∨ w = 15638 ∨ w = 15637
  · rcases hD with rfl | rfl | rfl | rfl <;>
    · rw [piH7_apply]; unfold tau4Wire tauWireH compactWire oldWork freeAt oldRank; decide
  · have h4 : tau4Wire w = w := by
      unfold tau4Wire
      have hne : w ≠ 14877 ∧ w ≠ 15640 ∧ w ≠ 14876 ∧ w ≠ 15639 ∧ w ≠ 14875 ∧ w ≠ 15638 ∧ w ≠ 14874 ∧ w ≠ 15637 := by omega
      simp [hne.1, hne.2.1, hne.2.2.1, hne.2.2.2.1, hne.2.2.2.2.1, hne.2.2.2.2.2.1, hne.2.2.2.2.2.2.1, hne.2.2.2.2.2.2.2]
    rw [piH7_apply, h4]
    by_cases hA : 15644 ≤ w ∧ w < 15655
    · have ht : tauWireH w = w - 5644 := by unfold tauWireH; split_ifs <;> omega
      have ho : oldWork (w - 5644) := by unfold oldWork; omega
      rw [ht, compactWire, if_pos ho]
      exact freeAt_lt_1612 _ (by unfold oldRank; split_ifs <;> omega)
    by_cases hC : w = 15643 ∨ w = 15642 ∨ w = 15641
    · rcases hC with rfl | rfl | rfl <;>
      · unfold tauWireH compactWire oldWork freeAt oldRank; decide
    by_cases hB : 19814 ≤ w ∧ w < 19817
    · have ht : tauWireH w = w - 9802 := by unfold tauWireH; split_ifs <;> omega
      have ho : oldWork (w - 9802) := by unfold oldWork; omega
      rw [ht, compactWire, if_pos ho]
      exact freeAt_lt_1612 _ (by unfold oldRank; split_ifs <;> omega)
    · have ht : tauWireH w = w := by unfold tauWireH; split_ifs <;> omega
      rw [ht]
      rcases h1 with hf | ho
      · have he : compactWire w = w := compactPerm_fixed w hf
        show compactWire w < 1612
        rw [he]; unfold fixedPort at hf; omega
      · rw [compactWire, if_pos ho]
        unfold oldWork at ho
        exact freeAt_lt_1612 _ (by unfold oldRank; split_ifs <;> omega)

theorem relabelH7_support {n s e} (p : Straight n s e) (hp : straightWires p ⊆ newSourceH7) :
    straightWires (relabelStraight piH7 p) ⊆ List.range 1612 := by
  rw [straightWires_relabel]
  intro w hw
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
  exact List.mem_range.mpr (piH7_bound v (hp hv))

theorem ctl4_sites_not :
    ∀ w ∈ ([14111, 19816, 838, 14112, 19815, 19814] : List Wire),
      w ∉ ECDSAAdd.Frontier.OB5Support.sites streamLayout := by
  intro w hw h
  simp only [ECDSAAdd.Frontier.OB5Support.sites, List.mem_cons, List.mem_append] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases h with ((h | h) | h) | h
  · rw [streamLayout_gen] at h
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> exact absurd h (by decide)
  · rw [streamLayout_point] at h; simp only [List.mem_range'_1] at h
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · rw [streamLayout_point] at h; simp only [List.mem_range'_1] at h
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · obtain ⟨i, hi, e⟩ := ECDSAAdd.Frontier.OB5Support.pool_index streamLayout _ h
    rw [streamPool_at i (by omega)] at e
    (try dsimp only [ShorECDLP.Wire, ECDSAAdd.Wire] at e)
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

theorem ctl4_arithS (b : Bool) :
    14111 ∉ ECDSAAdd.wires (ECDSAAdd.Frontier.arithS streamLayout b) ∧
    19816 ∉ ECDSAAdd.wires (ECDSAAdd.Frontier.arithS streamLayout b) ∧
    838 ∉ ECDSAAdd.wires (ECDSAAdd.Frontier.arithS streamLayout b) ∧
    14112 ∉ ECDSAAdd.wires (ECDSAAdd.Frontier.arithS streamLayout b) ∧
    19815 ∉ ECDSAAdd.wires (ECDSAAdd.Frontier.arithS streamLayout b) ∧
    19814 ∉ ECDSAAdd.wires (ECDSAAdd.Frontier.arithS streamLayout b) := by
  have h := wires_avoid_of
    ((ECDSAAdd.Frontier.arithS_sub streamLayout streamLayout_widths streamLayout_nodup b).wires_sub.trans
      (ECDSAAdd.Frontier.ArithmeticOB5.arith_support streamLayout streamLayout_widths b))
    ctl4_sites_not
  exact ⟨h 14111 (by simp), h 19816 (by simp), h 838 (by simp),
    h 14112 (by simp), h 19815 (by simp), h 19814 (by simp)⟩

theorem ctl4_square :
    14111 ∉ ECDSAAdd.wires (ECDSAAdd.Frontier.SquareOB5.program streamLayout) ∧
    19816 ∉ ECDSAAdd.wires (ECDSAAdd.Frontier.SquareOB5.program streamLayout) ∧
    838 ∉ ECDSAAdd.wires (ECDSAAdd.Frontier.SquareOB5.program streamLayout) ∧
    14112 ∉ ECDSAAdd.wires (ECDSAAdd.Frontier.SquareOB5.program streamLayout) ∧
    19815 ∉ ECDSAAdd.wires (ECDSAAdd.Frontier.SquareOB5.program streamLayout) ∧
    19814 ∉ ECDSAAdd.wires (ECDSAAdd.Frontier.SquareOB5.program streamLayout) := by
  have h := wires_avoid_of
    (ECDSAAdd.Frontier.SquareOB5.support streamLayout streamLayout_widths streamLayout_nodup)
    ctl4_sites_not
  exact ⟨h 14111 (by simp), h 19816 (by simp), h 838 (by simp),
    h 14112 (by simp), h 19815 (by simp), h 19814 (by simp)⟩

theorem code_avoid4 (c : WCode 32768) (hav : AvoidsB c) :
    (14877 ∈ ECDSAAdd.wires (litProg c) ∨ 14876 ∈ ECDSAAdd.wires (litProg c) ∨
      14875 ∈ ECDSAAdd.wires (litProg c) ∨ 14874 ∈ ECDSAAdd.wires (litProg c)) →
    14111 ∉ ECDSAAdd.wires (litProg c) ∧ 19816 ∉ ECDSAAdd.wires (litProg c) ∧
    838 ∉ ECDSAAdd.wires (litProg c) ∧ 14112 ∉ ECDSAAdd.wires (litProg c) ∧
    19815 ∉ ECDSAAdd.wires (litProg c) ∧ 19814 ∉ ECDSAAdd.wires (litProg c) := by
  intro h0
  exfalso
  rcases h0 with h1 | h2 | h3 | h4
  · obtain ⟨p, hp, hw⟩ := litProg_wires c 14877 h1; exact hav.1 14877 (by decide) p hp hw
  · obtain ⟨p, hp, hw⟩ := litProg_wires c 14876 h2; exact hav.1 14876 (by decide) p hp hw
  · obtain ⟨p, hp, hw⟩ := litProg_wires c 14875 h3; exact hav.1 14875 (by decide) p hp hw
  · obtain ⟨p, hp, hw⟩ := litProg_wires c 14874 h4; exact hav.1 14874 (by decide) p hp hw

theorem lit_ctl4 (p : ECDSAAdd.Program)
    (h : 14111 ∉ ECDSAAdd.wires p ∧ 19816 ∉ ECDSAAdd.wires p ∧
      838 ∉ ECDSAAdd.wires p ∧ 14112 ∉ ECDSAAdd.wires p ∧
      19815 ∉ ECDSAAdd.wires p ∧ 19814 ∉ ECDSAAdd.wires p) :
    (14877 ∈ ECDSAAdd.wires (litProg (wLiteral (n := 32768) p)) ∨
      14876 ∈ ECDSAAdd.wires (litProg (wLiteral (n := 32768) p)) ∨
      14875 ∈ ECDSAAdd.wires (litProg (wLiteral (n := 32768) p)) ∨
      14874 ∈ ECDSAAdd.wires (litProg (wLiteral (n := 32768) p))) →
    14111 ∉ ECDSAAdd.wires (litProg (wLiteral (n := 32768) p)) ∧
    19816 ∉ ECDSAAdd.wires (litProg (wLiteral (n := 32768) p)) ∧
    838 ∉ ECDSAAdd.wires (litProg (wLiteral (n := 32768) p)) ∧
    14112 ∉ ECDSAAdd.wires (litProg (wLiteral (n := 32768) p)) ∧
    19815 ∉ ECDSAAdd.wires (litProg (wLiteral (n := 32768) p)) ∧
    19814 ∉ ECDSAAdd.wires (litProg (wLiteral (n := 32768) p)) := by
  intro _; rw [litProg_wLiteral]; exact h

theorem rowC_plain_ctl4 (code : WCode 32768) (hb : Block2.plain code ∈ WEXUnlookup.rowC) :
    (14877 ∈ ECDSAAdd.wires (litProg code) ∨ 14876 ∈ ECDSAAdd.wires (litProg code) ∨
      14875 ∈ ECDSAAdd.wires (litProg code) ∨ 14874 ∈ ECDSAAdd.wires (litProg code)) →
    14111 ∉ ECDSAAdd.wires (litProg code) ∧ 19816 ∉ ECDSAAdd.wires (litProg code) ∧
    838 ∉ ECDSAAdd.wires (litProg code) ∧ 14112 ∉ ECDSAAdd.wires (litProg code) ∧
    19815 ∉ ECDSAAdd.wires (litProg code) ∧ 19814 ∉ ECDSAAdd.wires (litProg code) := by
  have key : ∀ b ∈ WEXUnlookup.rowC, ∀ c, b = Block2.plain c →
      (14877 ∈ ECDSAAdd.wires (litProg c) ∨ 14876 ∈ ECDSAAdd.wires (litProg c) ∨
        14875 ∈ ECDSAAdd.wires (litProg c) ∨ 14874 ∈ ECDSAAdd.wires (litProg c)) →
      14111 ∉ ECDSAAdd.wires (litProg c) ∧ 19816 ∉ ECDSAAdd.wires (litProg c) ∧
      838 ∉ ECDSAAdd.wires (litProg c) ∧ 14112 ∉ ECDSAAdd.wires (litProg c) ∧
      19815 ∉ ECDSAAdd.wires (litProg c) ∧ 19814 ∉ ECDSAAdd.wires (litProg c) := by
    rw [WEXUnlookup.rowC, WEXUnlookup.rowHead, WEXUnlookup.rowPre3, generic3_list, WEXUnlookup.rowPost3]
    simp only [List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.forall_mem_cons, List.forall_mem_nil, List.not_mem_nil, toBlock2, Block2.plain.injEq, reduceCtorEq,
      false_implies, implies_true, forall_eq', forall_const, and_true, true_and]
    exact ⟨code_avoid4 _ flip_avoidsB, code_avoid4 _ head_avoidsB, code_avoid4 _ guard5_avoidsB,
      lit_ctl4 _ (ctl4_arithS false), code_avoid4 _ guard5_avoidsB, lit_ctl4 _ ctl4_square,
      code_avoid4 _ guard5_avoidsB, lit_ctl4 _ (ctl4_arithS true), code_avoid4 _ guard5_avoidsB,
      code_avoid4 _ negXReg_avoidsB, code_avoid4 _ zrep_avoidsB, code_avoid4 _ cornerNeg_avoidsB,
      code_avoid4 _ sfxTailF_avoidsB, code_avoid4 _ flip_avoidsB⟩
  exact key _ hb code rfl

theorem rowC_unit_no4 (u : UnitSite 32768) (hu : Block2.unit u ∈ WEXUnlookup.rowC) :
    (∀ p, WInstr.literal p ∈ u.code → ∀ w ∈ ECDSAAdd.wires p,
      w ≠ 14877 ∧ w ≠ 14876 ∧ w ≠ 14875 ∧ w ≠ 14874) ∧
    (∀ c ps, WInstr.lookup c ps ∈ u.code →
      (∀ q ∈ c, q ≠ 14877 ∧ q ≠ 14876 ∧ q ≠ 14875 ∧ q ≠ 14874) ∧
      (∀ w ∈ portTargets ps, w ≠ 14877 ∧ w ≠ 14876 ∧ w ≠ 14875 ∧ w ≠ 14874)) := by
  have hav := rowC_unit_avoidsB u hu
  refine ⟨fun p hp w hw => ⟨fun e => hav.1 14877 (by decide) p hp (e ▸ hw),
    fun e => hav.1 14876 (by decide) p hp (e ▸ hw),
    fun e => hav.1 14875 (by decide) p hp (e ▸ hw),
    fun e => hav.1 14874 (by decide) p hp (e ▸ hw)⟩, fun c ps hp => ⟨fun q hq =>
      ⟨(hav.2 14877 (by decide) c ps hp).2 q hq, (hav.2 14876 (by decide) c ps hp).2 q hq,
       (hav.2 14875 (by decide) c ps hp).2 q hq, (hav.2 14874 (by decide) c ps hp).2 q hq⟩,
      fun w hw => ⟨fun e => (hav.2 14877 (by decide) c ps hp).1 (e ▸ hw),
        fun e => (hav.2 14876 (by decide) c ps hp).1 (e ▸ hw),
        fun e => (hav.2 14875 (by decide) c ps hp).1 (e ▸ hw),
        fun e => (hav.2 14874 (by decide) c ps hp).1 (e ▸ hw)⟩⟩⟩

theorem rowC_look_newH7 (c : Option Wire) (ps : List (LookupPort 32768))
    (hm : WInstr.lookup c ps ∈ erase2 WEXUnlookup.rowC) :
    (∀ q ∈ c, q ∈ newSourceH7) ∧ portTargets ps ⊆ newSourceH7 := by
  have h0 := PathShare.rowC_look_newH c ps hm
  obtain ⟨b, hb, hbi⟩ := List.mem_flatMap.mp hm
  cases b with
  | plain code =>
    obtain ⟨p, hp⟩ := PathShare.rowC_plain_lit code hb _ hbi
    cases hp
  | unit u =>
    have hu := (rowC_unit_no4 u hb).2 c ps hbi
    exact ⟨fun q hq => newSourceH7_of_newH q (h0.1 q hq) (hu.1 q hq).1 (hu.1 q hq).2.1 (hu.1 q hq).2.2.1 (hu.1 q hq).2.2.2,
      fun w hw => newSourceH7_of_newH w (h0.2 hw) (hu.2 w hw).1 (hu.2 w hw).2.1 (hu.2 w hw).2.2.1 (hu.2 w hw).2.2.2⟩

theorem rowC_lit_relaxed7 (p : ECDSAAdd.Program) (hm : WInstr.literal p ∈ erase2 WEXUnlookup.rowC) :
    ∀ w ∈ ECDSAAdd.wires p,
      w = hostWire ∨ w = hostWire2 ∨ w = hostWire3 ∨
      w = hostWire4 ∨ w = hostWire5 ∨ w = hostWire6 ∨ w = hostWire7 ∨ w ∈ newSourceH7 :=
  fun w hw => relaxed7_of_new w (List.mem_toFinset.mp (W15C.rowC_lit_new p hm hw))

def blockExtra {n} : Block2 n → Nat
  | .plain code => hostCodeExtra code
  | .unit _ => 0

def codeExtra {n} : Code2 n → Nat
  | [] => 0
  | b :: code => blockExtra b + codeExtra code

theorem codeExtra_append {n} (a b : Code2 n) : codeExtra (a ++ b) = codeExtra a + codeExtra b := by
  induction a with
  | nil => simp [codeExtra]
  | cons x a ih => simp [codeExtra, ih, Nat.add_assoc]

private theorem codeExtra_cons_le {n} (b : Block2 n) (bs : Code2 n) (k m : Nat)
    (hb : blockExtra b ≤ k) (hbs : codeExtra bs ≤ m) : codeExtra (b :: bs) ≤ k + m := by
  simp only [codeExtra]; omega

theorem rowC_codeExtra_le : codeExtra WEXUnlookup.rowC ≤ 6 := by
  have h0 (c : WCode 32768) (hav : AvoidsB c) : blockExtra (.plain c) ≤ 0 :=
    Nat.le_of_eq (hostCodeExtra_zero_of_avoidsB c hav)
  have hu (u : UnitSite 32768) : blockExtra (.unit u) ≤ 0 := Nat.le_refl 0
  have h2 (p : ECDSAAdd.Program) : blockExtra (.plain (wLiteral (n := 32768) p)) ≤ 2 :=
    hostCodeExtra_le _
  rw [WEXUnlookup.rowC, WEXUnlookup.rowHead, WEXUnlookup.rowPre3, generic3_list, WEXUnlookup.rowPost3]
  simp only [List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append, toBlock2]
  refine codeExtra_cons_le _ _ 0 6 (h0 _ flip_avoidsB) ?_
  refine codeExtra_cons_le _ _ 0 6 (h0 _ head_avoidsB) ?_
  refine codeExtra_cons_le _ _ 0 6 (hu _) ?_
  refine codeExtra_cons_le _ _ 0 6 (h0 _ guard5_avoidsB) ?_
  refine codeExtra_cons_le _ _ 2 4 (h2 _) ?_
  refine codeExtra_cons_le _ _ 0 4 (h0 _ guard5_avoidsB) ?_
  refine codeExtra_cons_le _ _ 2 2 (h2 _) ?_
  refine codeExtra_cons_le _ _ 0 2 (hu _) ?_
  refine codeExtra_cons_le _ _ 0 2 (h0 _ guard5_avoidsB) ?_
  refine codeExtra_cons_le _ _ 2 0 (h2 _) ?_
  refine codeExtra_cons_le _ _ 0 0 (h0 _ guard5_avoidsB) ?_
  refine codeExtra_cons_le _ _ 0 0 (h0 _ negXReg_avoidsB) ?_
  refine codeExtra_cons_le _ _ 0 0 (hu _) ?_
  refine codeExtra_cons_le _ _ 0 0 (h0 _ zrep_avoidsB) ?_
  refine codeExtra_cons_le _ _ 0 0 (h0 _ cornerNeg_avoidsB) ?_
  refine codeExtra_cons_le _ _ 0 0 (hu _) ?_
  refine codeExtra_cons_le _ _ 0 0 (hu _) ?_
  refine codeExtra_cons_le _ _ 0 0 (h0 _ sfxTailF_avoidsB) ?_
  refine codeExtra_cons_le _ _ 0 0 (h0 _ flip_avoidsB) ?_
  exact Nat.le_refl 0

theorem hostCodeExtra_rows {m} (f : Nat → Fin m) (c : WCode 32768) :
    hostCodeExtra (WideSigned.Rows.code f c) = hostCodeExtra c := by
  have hall : (WideSigned.Rows.code f c).all isLit = c.all isLit := by
    induction c with
    | nil => rfl
    | cons i c ih =>
      cases i with
      | literal p =>
        change (isLit (WInstr.literal p) && (WideSigned.Rows.code f c).all isLit) =
          (isLit (WInstr.literal p) && c.all isLit)
        rw [ih]; rfl
      | lookup ctrl ps => rfl
  have hlit : litProg (WideSigned.Rows.code f c) = litProg c := by
    clear hall
    induction c with
    | nil => rfl
    | cons i c ih =>
      cases i with
      | literal p =>
        change p ++ litProg (WideSigned.Rows.code f c) = p ++ litProg c
        rw [ih]
      | lookup ctrl ps =>
        change litProg (WideSigned.Rows.code f c) = litProg c
        exact ih
  simp only [hostCodeExtra, hall, hlit]

theorem codeExtra_rows {m} (f : Nat → Fin m) (code : Code2 32768) :
    codeExtra (code.map (WideSigned.Rows.block f)) = codeExtra code := by
  induction code with
  | nil => rfl
  | cons b code ih =>
    cases b with
    | plain c => simp [WideSigned.Rows.block, codeExtra, blockExtra, hostCodeExtra_rows, ih]
    | unit u => simp [WideSigned.Rows.block, codeExtra, blockExtra, ih]

/-! ### Hosted narrow blocks (`PathShare.Bank`) using `hostCode7` -/

def blockProgH7 {n} (B : PathShare.Bank) (b : Block2 n) (start : Nat) :
    Straight n start (start + blockRecP2 B b) :=
  match b with
  | .plain code => castFinish (congrArg (fun k => start + k) (hostCode7_counts B.bits B.paths windowRoot code).1)
      (compile B.bits B.paths windowRoot (hostCode7 code) start)
  | .unit u => blockProgP2 B (.unit u) start

def blockSourceH7 {n} (B : PathShare.Bank) (read : ConstantBit n → Bool) : Block2 n → AdaptiveCircuit
  | .plain code => source read B.bits B.paths windowRoot (hostCode7 code)
  | .unit u => blockSourceP2 B read (.unit u)

def blockTP7 {n} (B : PathShare.Bank) : Block2 n → Nat
  | .plain code => blockTP2 B (.plain code) + hostCodeExtra code
  | .unit u => blockTP2 B (.unit u)

def BlockSimH7 {n} (read : ConstantBit n → Bool) (B : PathShare.Bank) (block : Block2 n)
    (branch : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords block.code ∧
    ∀ address st, AddrValid B.bits windowRoot address st → BlockClean2 B.paths block st → HostOK7 block st →
      BlockSafe2 read address block st →
      branch.kraus (Bridge.signedKet st) =
        c • Bridge.signedKet (ECDSAAdd.run (blockReference2 read address block) m st)

theorem blockProgH7_run {n} (B : PathShare.Bank) (read : ConstantBit n → Bool) (b : Block2 n)
    (start : Nat) (history : Fin start → Bool) :
    ((blockProgH7 B b start).instantiate read history).run = (blockSourceH7 B read b).run := by
  cases b with
  | plain code =>
    rw [blockProgH7, castFinish_instantiate]
    exact compile_run read _ _ _ _ _ _
  | unit u => exact blockProgP2_run B read (.unit u) start history

theorem block_simulationH7 {n} (read : ConstantBit n → Bool) (B : PathShare.Bank) (hB : BankOK B)
    (block : Block2 n) (hg : BlockGeoP2 B block) :
    ∃ cs : List ℂ, List.Forall₂ (BlockSimH7 read B block) (blockSourceH7 B read block).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  cases block with
  | plain code =>
    have hg' : LitAvoid B.bits code := hg
    have hlit : ∀ i ∈ code, ∃ p, i = .literal p := fun i hi => by
      obtain ⟨p, rfl, -⟩ := hg' i hi; exact ⟨p, rfl⟩
    let P := ECDSAAdd.Baselines.normalizeProgram (litProg code)
    have hc : hostCode7 code = [.literal (hostBlock7 P)] :=
      hostCode7_eq_host ((allLit_iff code).mpr hlit)
    have hRP : windowRoot ∉ ECDSAAdd.wires P := by
      intro hw
      rw [ECDSAAdd.Baselines.normalize_wires] at hw
      obtain ⟨p, hp, hw⟩ := litProg_wires code windowRoot hw
      obtain ⟨q, he, hq⟩ := hg' _ hp
      cases he
      exact hq windowRoot (by simp) hw
    show ∃ cs : List ℂ, List.Forall₂ (BlockSimH7 read B (.plain code))
      (source read B.bits B.paths windowRoot (hostCode7 code)).run cs ∧ (cs.map Complex.normSq).sum = 1
    rw [hc]
    obtain ⟨cs, aligned, mass⟩ := lit_simulation read B.bits B.paths windowRoot
      ([.literal (hostBlock7 P)] : WCode n) (by simp)
    refine ⟨cs, aligned.imp ?_, mass⟩
    intro b c hb
    obtain ⟨m, hm, hb⟩ := hb
    refine ⟨m, ?_, fun address st hs _ hh _ => ?_⟩
    · rw [hm]
      simp only [literalRecords, hostBlock7_meas, P, ECDSAAdd.Baselines.normalize_measurements, Nat.add_zero]
      exact litProg_meas code hlit
    · rw [hb address st]
      have e1 : (specialize ([.literal (hostBlock7 P)] : WCode n) address).instantiate read = hostBlock7 P := by
        rw [show ([.literal (hostBlock7 P)] : WCode n) = wLiteral (hostBlock7 P) from rfl,
          specialize_literal, ECDSAAdd.ShorPort.Tmpl.instantiate_lit]
      have e2 : blockReference2 read address (.plain code : Block2 n) = litProg code := by
        simp only [blockReference2, Block2.code]
        exact litProg_inst read code address hlit
      have hrun : ECDSAAdd.run P m st = ECDSAAdd.run (litProg code) m st :=
        ECDSAAdd.Baselines.normalize_run _ m st
      have hwP : ECDSAAdd.wires P = ECDSAAdd.wires (litProg code) := ECDSAAdd.Baselines.normalize_wires _
      have hh3 := hh.1
      have hh4 := hh.2
      rw [e1, e2, hostBlock7_run P hRP m st hs.2 hh3.1.1.1 (by rw [hrun]; exact hh3.1.1.2 m)
        (fun c1 c2 => by
          rw [hwP] at c1 c2
          obtain ⟨d1, d2, d3⟩ := hh3.1.2 c1 c2
          exact ⟨d1, d2, by rw [hrun]; exact d3 m⟩)
        (fun c1 c2 => by
          rw [hwP] at c1 c2
          obtain ⟨d1, d2, d3⟩ := hh3.2 c1 c2
          exact ⟨d1, d2, by rw [hrun]; exact d3 m⟩)
        (fun c4 => by
          have c4' : host4Set (litProg code) := by simpa [host4Set, hwP] using c4
          obtain ⟨f1, f2, f3⟩ := hh4 c4'
          exact ⟨f1, f2, by rw [hrun]; exact (f3 m).1, by rw [hrun]; exact (f3 m).2⟩), hrun]
  | unit u =>
    obtain ⟨cs, aligned, mass⟩ := block_simulationP2 read B hB (.unit u) hg
    refine ⟨cs, aligned.imp ?_, mass⟩
    intro b c hb
    obtain ⟨m, hm, hb⟩ := hb
    exact ⟨m, hm, fun address st hs hc _ hsafe => hb address st hs hc hsafe⟩

theorem blockH7_wellFormed {n} (B : PathShare.Bank) (hB : BankOK B) (b : Block2 n) (hgb : BlockGeoP2 B b)
    (hpb : ∀ p, WInstr.literal p ∈ b.code → ECDSAAdd.Arithmetic.GatePhysical p) (start : Nat) :
    (blockProgH7 B b start).WellFormed := by
  cases b with
  | plain code =>
    have hg' : LitAvoid B.bits code := hgb
    have hlit : ∀ i ∈ code, ∃ p, i = .literal p := fun i hi => by
      obtain ⟨p, rfl, -⟩ := hg' i hi; exact ⟨p, rfl⟩
    rw [blockProgH7, castFinish_wellFormed, hostCode7_eq_host ((allLit_iff code).mpr hlit)]
    apply compile_wellFormedLit _ _ _ _ (by simp)
    intro p hp
    rw [List.mem_singleton, WInstr.literal.injEq] at hp
    subst hp
    apply hostBlock7_valid
    apply ECDSAAdd.Baselines.normalize_physical
    intro i hi
    obtain ⟨q, hq, hi⟩ := litProg_mem code i hi
    exact hpb q hq i hi
  | unit u =>
    exact blockH_wellFormed B hB (.unit u) hgb hpb start

theorem blockH7_tCount {n} (read : ConstantBit n → Bool) (B : PathShare.Bank) (b : Block2 n) (hl : BlockLay2 B b)
    (start : Nat) (history : Fin start → Bool) :
    ((blockProgH7 B b start).instantiate read history).tCount = 7 * blockTP7 B b := by
  cases b with
  | plain code =>
    have hl' : LookupLayouts B.bits B.paths windowRoot (normalizeW code) := hl
    obtain ⟨-, e2, e3⟩ := hostCode7_counts B.bits B.paths windowRoot code
    rw [blockProgH7, castFinish_instantiate,
      WEX.compile_tCount read _ _ _ _ (hostCode7_layouts _ _ _ code hl') start history, e2, e3]
    simp only [blockTP7, blockTP2]; ring
  | unit u => exact blockProgP2_tCount read B (.unit u) hl start history

theorem blockH7_slots {n} (B : PathShare.Bank) (b : Block2 n) (hl : BlockLay2 B b) (start : Nat) :
    (blockProgH7 B b start).gateSlots ≤ blockSP2 B b + 26 := by
  cases b with
  | plain code =>
    have hl' : LookupLayouts B.bits B.paths windowRoot (normalizeW code) := hl
    rw [blockProgH7, castFinish_gateSlots, WEX.compile_slots _ _ _ _ (hostCode7_layouts _ _ _ code hl') start]
    exact hostCode7_slots B.bits code
  | unit u =>
    have h := blockProgP2_slots B (.unit u) hl start
    change (blockProgP2 B (.unit u) start).gateSlots ≤ _
    omega

theorem blockH7_residue {n} (B : PathShare.Bank) (b : Block2 n) (start : Nat) :
    AndGadget.residue (blockProgH7 B b start) = 0 := by
  cases b with
  | plain code =>
    rw [blockProgH7, AndGadget.residue_cast]
    exact WEXCredit.compile_residue _ _ _ _ _
  | unit u => exact blockH_residue B (.unit u) start

theorem blockH7_support (B : PathShare.Bank) (hB : BankOK B) (b : Block2 32768) (hg : BlockGeoP2 B b)
    (S : List Wire) (hroot : windowRoot ∈ S) (hctl : hostCtl ∈ S) (hctl3 : hostCtl3 ∈ S)
    (hc11 : (14111 : Wire) ∈ S) (hc16 : (19816 : Wire) ∈ S) (hc838 : (838 : Wire) ∈ S)
    (hc12 : (14112 : Wire) ∈ S) (hc15 : (19815 : Wire) ∈ S) (hc14 : (19814 : Wire) ∈ S)
    (hc13 : (14113 : Wire) ∈ S)
    (hbits : B.bits ⊆ S) (hpaths : B.paths ⊆ S) (hlow : ∀ i, WEXUnlookup.low i ∈ S) (hhigh : B.high ⊆ S)
    (hlit : ∀ p, WInstr.literal p ∈ b.code → ∀ w ∈ ECDSAAdd.wires p,
      w = hostWire ∨ w = hostWire2 ∨ w = hostWire3 ∨
      w = hostWire4 ∨ w = hostWire5 ∨ w = hostWire6 ∨ w = hostWire7 ∨ w ∈ S)
    (hstrict : ∀ p, WInstr.literal p ∈ b.code →
      (hostWire ∈ ECDSAAdd.wires p ∨ hostWire2 ∈ ECDSAAdd.wires p ∨ hostWire3 ∈ ECDSAAdd.wires p ∨
       hostWire4 ∈ ECDSAAdd.wires p ∨ hostWire5 ∈ ECDSAAdd.wires p ∨ hostWire6 ∈ ECDSAAdd.wires p ∨
       hostWire7 ∈ ECDSAAdd.wires p) → ∃ c, b = .plain c)
    (hctl2 : ∀ c, b = .plain c → hostWire2 ∈ ECDSAAdd.wires (litProg c) → hostCtl ∉ ECDSAAdd.wires (litProg c))
    (hctl3' : ∀ c, b = .plain c → hostWire3 ∈ ECDSAAdd.wires (litProg c) → hostCtl3 ∉ ECDSAAdd.wires (litProg c))
    (hctl4 : ∀ c, b = .plain c →
      (14877 ∈ ECDSAAdd.wires (litProg c) ∨ 14876 ∈ ECDSAAdd.wires (litProg c) ∨
        14875 ∈ ECDSAAdd.wires (litProg c) ∨ 14874 ∈ ECDSAAdd.wires (litProg c)) →
      14111 ∉ ECDSAAdd.wires (litProg c) ∧ 19816 ∉ ECDSAAdd.wires (litProg c) ∧
      838 ∉ ECDSAAdd.wires (litProg c) ∧ 14112 ∉ ECDSAAdd.wires (litProg c) ∧
      19815 ∉ ECDSAAdd.wires (litProg c) ∧ 19814 ∉ ECDSAAdd.wires (litProg c))
    (hlook : ∀ c ps, WInstr.lookup c ps ∈ b.code → (∀ q ∈ c, q ∈ S) ∧ portTargets ps ⊆ S)
    (start : Nat) : ChallengeMigration.straightWires (blockProgH7 B b start) ⊆ S := by
  cases b with
  | plain code =>
    have hg' : LitAvoid B.bits code := hg
    have hlit' : ∀ i ∈ code, ∃ p, i = .literal p := fun i hi => by
      obtain ⟨p, rfl, -⟩ := hg' i hi; exact ⟨p, rfl⟩
    rw [blockProgH7, support_cast, hostCode7_eq_host ((allLit_iff code).mpr hlit')]
    apply compile_support B.bits B.paths windowRoot _ S hroot hbits hpaths _ (fun c ps hm => by simp at hm) start
    intro p hp
    rw [List.mem_singleton, WInstr.literal.injEq] at hp
    subst hp
    let P := ECDSAAdd.Baselines.normalizeProgram (litProg code)
    have hwP : ECDSAAdd.wires P = ECDSAAdd.wires (litProg code) := ECDSAAdd.Baselines.normalize_wires _
    have hRP : windowRoot ∉ ECDSAAdd.wires P := by
      intro hw
      rw [hwP] at hw
      obtain ⟨q, hq, hqw⟩ := litProg_wires code windowRoot hw
      obtain ⟨q', he, hq'⟩ := hg' _ hq
      cases he; exact hq' windowRoot (by simp) hqw
    exact hostBlock7_wires P S hroot hctl hctl3 hc11 hc16 hc838 hc12 hc15 hc14 hc13 hRP
      (fun w hw => by
        rw [hwP] at hw
        obtain ⟨q, hq, hqw⟩ := litProg_wires code w hw
        exact hlit q hq w hqw)
      (fun hm => by rw [hwP] at hm ⊢; exact hctl2 code rfl hm)
      (fun hm => by rw [hwP] at hm ⊢; exact hctl3' code rfl hm)
      (fun hm => by rw [hwP] at hm ⊢; exact hctl4 code rfl hm)
  | unit u =>
    have hlitU : ∀ p, WInstr.literal p ∈ (Block2.unit u).code → ECDSAAdd.wires p ⊆ S.toFinset := by
      intro p hp w hw
      rcases hlit p hp w hw with e | e | e | e | e | e | e | e
      · obtain ⟨c, hc⟩ := hstrict p hp (Or.inl (e ▸ hw)); cases hc
      · obtain ⟨c, hc⟩ := hstrict p hp (Or.inr (Or.inl (e ▸ hw))); cases hc
      · obtain ⟨c, hc⟩ := hstrict p hp (Or.inr (Or.inr (Or.inl (e ▸ hw)))); cases hc
      · obtain ⟨c, hc⟩ := hstrict p hp (Or.inr (Or.inr (Or.inr (Or.inl (e ▸ hw))))); cases hc
      · obtain ⟨c, hc⟩ := hstrict p hp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (e ▸ hw)))))); cases hc
      · obtain ⟨c, hc⟩ := hstrict p hp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (e ▸ hw))))))); cases hc
      · obtain ⟨c, hc⟩ := hstrict p hp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (e ▸ hw))))))); cases hc
      · exact List.mem_toFinset.mpr e
    have hg' : UnitGeoP B u := hg
    have hpl : ∀ p, WInstr.literal p ∈ u.pre → ECDSAAdd.wires p ⊆ S.toFinset :=
      fun p hm => hlitU p (List.mem_append_left _ hm)
    have hpk : ∀ c ps, WInstr.lookup c ps ∈ u.pre → (∀ q ∈ c, q ∈ S) ∧ portTargets ps ⊆ S :=
      fun c ps hm => hlook c ps (List.mem_append_left _ hm)
    have hlast := hlook (some u.clear.guard) u.clear.ports (by simp [Block2.code, UnitSite.code])
    show ChallengeMigration.straightWires (blockProgP2 B (.unit u) start) ⊆ S
    rw [blockProgP2, support_cast, straightWires_append]
    exact List.append_subset.mpr ⟨compile_support _ _ _ _ S hroot hbits hpaths
      (normalized_lit_support _ S hpl) (normalized_look_support _ S hpk) start,
      clearP_support B hB u.clear hg'.site.kind S hlast.2 (hlast.1 u.clear.guard (Option.mem_def.mpr rfl))
        hlow hhigh hpaths _⟩

end
end ShorECDLP.Entrant.PoolHost
end

/-! ### Consolidated from `TightSupport.lean` -/
section
namespace ShorECDLP.Entrant.TightSupport
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare WideSigned WideSigned.Fast16
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
attribute [local irreducible] List.ofFn WEX.codeRecords lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps WEX.compile Bridge.translate
  MeasuredClear.measuredClear ECDSAAdd.Baselines.normalizeProgram
def support : List Wire := PathShare.newSourceH ++ [871, 10000]
theorem old_cover : PathShare.newSourceH ⊆ support := List.subset_append_left _ _
theorem support_length : support.length = 1618 := by decide
theorem root_new : windowRoot ∈ support := by decide
theorem bits_new : WideSigned.Fast16.windowBits ⊆ support := by decide
theorem bank_new : WideSigned.Fast16.pathBank ⊆ support := by decide
theorem high_new : WideSigned.Fast16.high ⊆ support := by decide
theorem low_new (i : Fin 7) : WEXUnlookup.low i ∈ support := by
  apply old_cover
  rw [newSourceH_mem]
  have hi := i.isLt
  simp only [WEXUnlookup.low, fixedPort, oldWork, retiredH, retired]
  omega
theorem selBits_new : WideSigned.Fast16.selBits ⊆ support := by decide
theorem selBits1_new : WideSigned.Fast16.selBits1 ⊆ support := by decide
theorem selPaths_new : WideSigned.Fast16.selPaths ⊆ support := by decide
theorem selPaths1_new : WideSigned.Fast16.selPaths1 ⊆ support := by decide
theorem bankHp_new : WideSigned.Fast16.bankHp ⊆ support := by decide
theorem work_new (w : Wire) (h : 14115 ≤ w ∧ oldWork w)
    (hw : w ≠ hostWire) (hw2 : w ≠ hostWire2) (hw3 : w ≠ hostWire3) : w ∈ support := by
  apply old_cover
  rw [newSourceH_mem]
  refine ⟨Or.inr h.2, ?_⟩
  unfold retiredH retired
  dsimp only [Wire] at *
  unfold hostWire hostWire2 hostWire3 at *
  omega
theorem guard_new (g : Wire) (h : g = 14113 ∨ g = 10015) : g ∈ support := by
  rcases h with rfl | rfl <;> decide
abbrev clearP_support := @WideSigned.Bank.clearP_support

theorem gclear_new_of {n : Nat} (data : List (MeasuredClear.ClearPort n)) (hot : Fin 128 → Wire) (guard sc : Wire)
    (hdata : ∀ w ∈ data.map MeasuredClear.ClearPort.target, w ∈ support)
    (hhot : ∀ i, hot i ∈ support) (hguard : guard ∈ support)
    (hsc : sc ∈ data.map MeasuredClear.ClearPort.target) (start : Nat) :
    ChallengeMigration.straightWires (MeasuredClear.measuredClear data WEXUnlookup.low hot (tableAddressTree WideSigned.Fast16.high 0 1)
      guard sc WideSigned.Fast16.bankHp start) ⊆ support := by
  have hindex := tableAddressTree_index WideSigned.Fast16.high 0 1 (by decide +kernel)
  rw [support_agrees]
  apply List.Subset.trans (MeasuredClear.measuredClear_static _ _ _ _ _ _ _ hsc start)
  intro w hw
  simp only [MeasuredClear.clearSupport, hindex, List.mem_append, List.mem_cons, or_assoc] at hw
  rcases hw with hs | hl | hh | hr | hb | hp
  · exact hdata w hs
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
    exact low_new i
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hh
    exact hhot i
  · rw [hr]; exact hguard
  · exact high_new hb
  · exact bankHp_new hp

namespace FastSite
open WideSigned.Fast16.FastSite
variable {n : Nat} (f : FastSite n)

theorem regs_new (hg : FastGeometry f) (hgarb : ∀ w ∈ f.garb, w ≠ hostWire ∧ w ≠ hostWire2 ∧ w ≠ hostWire3) :
    ∀ w ∈ portTargets f.site.ports ++ f.garb, w ∈ support := by
  intro w hw
  have hk : w ≠ hostWire ∧ w ≠ hostWire2 ∧ w ≠ hostWire3 := by
    rcases List.mem_append.mp hw with h | h
    · exact ⟨fun e => kind_nohost f.site hg.site.kind (e ▸ h), fun e => kind_nohost2 f.site hg.site.kind (e ▸ h), fun e => PathShare.kind_nohost3 f.site hg.site.kind (e ▸ h)⟩
    · exact hgarb w h
  exact work_new w ((facts f hg).2.2.2.2.2.2 w hw) hk.1 hk.2.1 hk.2.2

theorem fast_support_new (hg : FastGeometry f)
    (hlit : ∀ p, WInstr.literal p ∈ f.site.code → ECDSAAdd.wires p ⊆ support.toFinset)
    (hlook : ∀ c ps, WInstr.lookup c ps ∈ f.site.code → (∀ q ∈ c, q ∈ support) ∧ portTargets ps ⊆ support)
    (hgarb : ∀ w ∈ f.garb, w ≠ hostWire ∧ w ≠ hostWire2 ∧ w ≠ hostWire3)
    (start : Nat) : ChallengeMigration.straightWires (f.fastProgram start) ⊆ support := by
  have hreg := regs_new f hg hgarb
  have hg0 := guard_new _ (facts f hg).2.2.1
  have hlast := hlook (some f.site.guard) f.site.ports (by simp [MaskedSite.code])
  rw [fastProgram, support_cast]
  simp only [straightWires_append, List.append_subset]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · refine compile_support WideSigned.Fast16.selBits WideSigned.Fast16.selPaths windowRoot f.selCode support root_new selBits_new selPaths_new
      (fun p hp => by simp [FastSite.selCode] at hp) ?_ start
    intro c ports hm
    simp only [FastSite.selCode, List.mem_singleton, WInstr.lookup.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    refine ⟨fun q hq => ?_, ?_⟩
    · rw [Option.mem_def, Option.some_inj] at hq
      rw [← hq]; exact hg0
    · rw [selPorts_targets f hg]; exact hreg
  · refine literalFixed_support _ _ _ support ?_ _
    intro w hw
    have h := swapNet_wires f hw
    simp only [List.mem_toFinset, List.cons_append, List.mem_cons] at h ⊢
    rcases h with rfl | rfl | h
    · exact bits_new (by simp [WideSigned.Fast16.windowBits])
    · exact bits_new (by simp [WideSigned.Fast16.windowBits])
    · exact hreg _ h
  · unfold gclearProgram
    apply gclear_new_of
    · rw [clearData_targets, garbPorts_targets f hg]
      exact fun w hw => hreg w (List.mem_append_right _ hw)
    · intro i; exact hreg _ (List.mem_append_right _ (g1_sub f _ (hg.bank i)))
    · exact hg0
    · rw [clearData_targets, garbPorts_targets f hg]; exact g1_sub f _ hg.head
  · exact compile_support _ _ _ _ support root_new bits_new bank_new
      (normalized_lit_support _ support (fun p hm => hlit p (List.mem_append_left _ (List.mem_cons_of_mem _ hm))))
      (normalized_look_support _ support (fun c ps hm => hlook c ps (List.mem_append_left _ (List.mem_cons_of_mem _ hm))))
      _
  · exact clearP_support WideSigned.Fast16.bank15 bank15_ok f.site hg.site.kind support hlast.2 (hlast.1 _ (Option.mem_def.mpr rfl))
      low_new high_new bank_new _

end FastSite

namespace FastSite1
open WideSigned.Fast16.FastSite1
variable {n : Nat} (f : FastSite1 n)

theorem regs_new (hg : FastGeometry1 f) (hgarb : ∀ w ∈ f.garb, w ≠ hostWire ∧ w ≠ hostWire2 ∧ w ≠ hostWire3) :
    ∀ w ∈ portTargets f.site.ports ++ f.garb, w ∈ support := by
  intro w hw
  have hk : w ≠ hostWire ∧ w ≠ hostWire2 ∧ w ≠ hostWire3 := by
    rcases List.mem_append.mp hw with h | h
    · exact ⟨fun e => kind_nohost f.site hg.site.kind (e ▸ h), fun e => kind_nohost2 f.site hg.site.kind (e ▸ h), fun e => PathShare.kind_nohost3 f.site hg.site.kind (e ▸ h)⟩
    · exact hgarb w h
  exact work_new w ((facts f hg).2.2.2.2.2.2 w hw) hk.1 hk.2.1 hk.2.2

theorem fast_support_new (hg : FastGeometry1 f)
    (hlit : ∀ p, WInstr.literal p ∈ f.site.code → ECDSAAdd.wires p ⊆ support.toFinset)
    (hlook : ∀ c ps, WInstr.lookup c ps ∈ f.site.code → (∀ q ∈ c, q ∈ support) ∧ portTargets ps ⊆ support)
    (hgarb : ∀ w ∈ f.garb, w ≠ hostWire ∧ w ≠ hostWire2 ∧ w ≠ hostWire3)
    (start : Nat) : ChallengeMigration.straightWires (f.fastProgram start) ⊆ support := by
  have hreg := regs_new f hg hgarb
  have hg0 := guard_new _ (facts f hg).2.2.1
  have hlast := hlook (some f.site.guard) f.site.ports (by simp [MaskedSite.code])
  rw [fastProgram, support_cast]
  simp only [straightWires_append, List.append_subset]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · refine compile_support WideSigned.Fast16.selBits1 WideSigned.Fast16.selPaths1 windowRoot f.selCode support root_new selBits1_new selPaths1_new
      (fun p hp => by simp [FastSite1.selCode] at hp) ?_ start
    intro c ports hm
    simp only [FastSite1.selCode, List.mem_singleton, WInstr.lookup.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    refine ⟨fun q hq => ?_, ?_⟩
    · rw [Option.mem_def, Option.some_inj] at hq
      rw [← hq]; exact hg0
    · rw [selPorts_targets f hg]; exact hreg
  · refine literalFixed_support _ _ _ support ?_ _
    intro w hw
    have h := swapNet_wires f hw
    simp only [List.mem_toFinset, List.cons_append, List.mem_cons] at h ⊢
    rcases h with rfl | h
    · exact bits_new (by simp [WideSigned.Fast16.windowBits])
    · exact hreg _ h
  · unfold gclearProgram
    apply gclear_new_of
    · rw [clearData_targets, garbPorts_targets f hg]
      exact fun w hw => hreg w (List.mem_append_right _ hw)
    · intro i; exact hreg _ (List.mem_append_right _ (hg.bank i))
    · exact hg0
    · rw [clearData_targets, garbPorts_targets f hg]; exact hg.head
  · exact compile_support _ _ _ _ support root_new bits_new bank_new
      (normalized_lit_support _ support (fun p hm => hlit p (List.mem_append_left _ (List.mem_cons_of_mem _ hm))))
      (normalized_look_support _ support (fun c ps hm => hlook c ps (List.mem_append_left _ (List.mem_cons_of_mem _ hm))))
      _
  · exact clearP_support WideSigned.Fast16.bank15 bank15_ok f.site hg.site.kind support hlast.2 (hlast.1 _ (Option.mem_def.mpr rfl))
      low_new high_new bank_new _

end FastSite1



def NoHost3 {n} : FBlock2 n → Prop
  | .std _ => True
  | .fast f => ∀ w ∈ f.garb, w ≠ hostWire ∧ w ≠ hostWire2 ∧ w ≠ hostWire3
  | .fast1 f => ∀ w ∈ f.garb, w ≠ hostWire ∧ w ≠ hostWire2 ∧ w ≠ hostWire3
theorem ctl_newH : hostCtl ∈ support := by decide
theorem ctl3_newH : hostCtl3 ∈ support := by decide
theorem fblock_support (b : FBlock2 65536) (hg : FBlockGeo b)
    (hlit : ∀ p, WInstr.literal p ∈ b.forget.code → ∀ w ∈ ECDSAAdd.wires p,
      w = hostWire ∨ w = hostWire2 ∨ w = hostWire3 ∨ w ∈ support)
    (hstrict : ∀ p, WInstr.literal p ∈ b.forget.code →
      (hostWire ∈ ECDSAAdd.wires p ∨ hostWire2 ∈ ECDSAAdd.wires p ∨ hostWire3 ∈ ECDSAAdd.wires p) →
      ∃ c, b = .std (.plain c))
    (hctl : ∀ c, b = .std (.plain c) → hostWire2 ∈ ECDSAAdd.wires (litProg c) → hostCtl ∉ ECDSAAdd.wires (litProg c))
    (hctl3 : ∀ c, b = .std (.plain c) →
      hostWire3 ∈ ECDSAAdd.wires (litProg c) → hostCtl3 ∉ ECDSAAdd.wires (litProg c))
    (hlook : ∀ c ps, WInstr.lookup c ps ∈ b.forget.code → (∀ q ∈ c, q ∈ support) ∧ portTargets ps ⊆ support)
    (hgarb : NoHost3 b)
    (start : Nat) : ChallengeMigration.straightWires (fblockProg b start) ⊆ support := by
  have strict : (∀ c, b ≠ .std (.plain c)) → ∀ p, WInstr.literal p ∈ b.forget.code →
      ECDSAAdd.wires p ⊆ support.toFinset := by
    intro hb p hp w hw
    rcases hlit p hp w hw with e | e | e | e
    · obtain ⟨c, hc⟩ := hstrict p hp (Or.inl (e ▸ hw))
      exact absurd hc (hb c)
    · obtain ⟨c, hc⟩ := hstrict p hp (Or.inr (Or.inl (e ▸ hw)))
      exact absurd hc (hb c)
    · obtain ⟨c, hc⟩ := hstrict p hp (Or.inr (Or.inr (e ▸ hw)))
      exact absurd hc (hb c)
    · exact List.mem_toFinset.mpr e
  cases b with
  | std b =>
    cases b with
    | plain code =>
      exact plainH_support WideSigned.Fast16.bank15 code hg support root_new bits_new bank_new ctl_newH ctl3_newH
        (fun p hp w hw => hlit p hp w hw) (hctl code rfl) (hctl3 code rfl) start
    | unit u =>
      have h := WideSigned.Fast16.programP2_support WideSigned.Fast16.bank15 WideSigned.Fast16.bank15_ok (Block2.unit u :: []) (fun d hd => by
          simp only [List.mem_singleton] at hd; subst hd; exact hg) support root_new bits_new bank_new low_new high_new
        (fun p hm => strict (fun c e => by cases e) p (by simpa [erase2] using hm))
        (fun c ps hm => hlook c ps (by simpa [erase2] using hm)) start
      rw [programP2, support_cast, straightWires_append] at h
      exact fun w hw => h (List.mem_append_left _ hw)
  | fast f =>
    exact ShorECDLP.Entrant.TightSupport.FastSite.fast_support_new f hg
      (fun p hm => strict (fun c e => by cases e) p (by simpa [FBlock2.forget, siteUnit_code] using hm))
      (fun c ps hm => hlook c ps (by simpa [FBlock2.forget, siteUnit_code] using hm)) hgarb start
  | fast1 f =>
    exact ShorECDLP.Entrant.TightSupport.FastSite1.fast_support_new f hg
      (fun p hm => strict (fun c e => by cases e) p (by simpa [FBlock2.forget, siteUnit_code] using hm))
      (fun c ps hm => hlook c ps (by simpa [FBlock2.forget, siteUnit_code] using hm)) hgarb start

theorem fprog_support (code : FCode2 65536) (hg : ∀ b ∈ code, FBlockGeo b)
    (hlit : ∀ p, WInstr.literal p ∈ erase2 (fforget code) → ∀ w ∈ ECDSAAdd.wires p,
      w = hostWire ∨ w = hostWire2 ∨ w = hostWire3 ∨ w ∈ support)
    (hstrict : ∀ b ∈ code, ∀ p, WInstr.literal p ∈ b.forget.code →
      (hostWire ∈ ECDSAAdd.wires p ∨ hostWire2 ∈ ECDSAAdd.wires p ∨ hostWire3 ∈ ECDSAAdd.wires p) →
      ∃ c, b = .std (.plain c))
    (hctl : ∀ b ∈ code, ∀ c, b = .std (.plain c) →
      hostWire2 ∈ ECDSAAdd.wires (litProg c) → hostCtl ∉ ECDSAAdd.wires (litProg c))
    (hctl3 : ∀ b ∈ code, ∀ c, b = .std (.plain c) →
      hostWire3 ∈ ECDSAAdd.wires (litProg c) → hostCtl3 ∉ ECDSAAdd.wires (litProg c))
    (hlook : ∀ c ps, WInstr.lookup c ps ∈ erase2 (fforget code) →
      (∀ q ∈ c, q ∈ support) ∧ portTargets ps ⊆ support)
    (hgarb : ∀ b ∈ code, NoHost3 b)
    (start : Nat) : ChallengeMigration.straightWires (fprog code start) ⊆ support := by
  induction code generalizing start with
  | nil => simp [fprog, frecs, ChallengeMigration.straightWires]
  | cons b code ih =>
    rw [fprog, support_cast, straightWires_append]
    exact List.append_subset.mpr ⟨fblock_support b (hg b (by simp))
      (fun p hm => hlit p (by simp [erase2_cons, hm])) (hstrict b (by simp)) (hctl b (by simp)) (hctl3 b (by simp))
      (fun c ps hm => hlook c ps (by simp [erase2_cons, hm])) (hgarb b (by simp)) start,
      ih (fun d hd => hg d (by simp [hd])) (fun p hm => hlit p (by simp [erase2_cons, hm]))
        (fun d hd => hstrict d (by simp [hd])) (fun d hd => hctl d (by simp [hd])) (fun d hd => hctl3 d (by simp [hd]))
        (fun c ps hm => hlook c ps (by simp [erase2_cons, hm])) (fun d hd => hgarb d (by simp [hd])) _⟩



attribute [local irreducible] WideSigned.Row16.code WideSigned.Fast16.fprog
  Straight.instantiate AdaptiveCircuit.run

theorem row_literals (p : ECDSAAdd.Program)
    (hp : WInstr.literal p ∈ erase2 (WideSigned.Fast16.fforget WideSigned.Row16.code)) :
    ∀ v ∈ ECDSAAdd.wires p, v=hostWire ∨ v=hostWire2 ∨ v=hostWire3 ∨ v∈support := by
  rw [WideSigned.Row16.forget,WideSigned.Geometry.row,WideSigned.Rows.erase_blocks] at hp
  have hold := WideSigned.Row16.literal_back _ p hp
  intro v hv
  rcases PathShare.rowC_lit_relaxed p hold v hv with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (old_cover h)))

theorem row_lookups (ctl : Option Wire) (ps : List (LookupPort 65536))
    (hp : WInstr.lookup ctl ps ∈ erase2 (WideSigned.Fast16.fforget WideSigned.Row16.code)) :
    (∀ q∈ctl,q∈support) ∧ portTargets ps ⊆ support := by
  rw [WideSigned.Row16.forget,WideSigned.Geometry.row,WideSigned.Rows.erase_blocks] at hp
  obtain ⟨old,ho,rfl⟩ := WideSigned.Row16.lookup_back _ ctl ps hp
  have h := PathShare.rowC_look_newH ctl old ho
  rw [WideSigned.Rows.targets]
  exact ⟨fun q hq => old_cover (h.1 q hq),fun v hv => old_cover (h.2 hv)⟩

theorem row_nohost (b : WideSigned.Fast16.FBlock2 65536) (hb : b∈WideSigned.Row16.code) : NoHost3 b := by
  rw [WideSigned.Row16.code] at hb
  obtain ⟨old,ho,rfl⟩ := List.mem_map.mp hb
  have h := WEXFast.W15F.rowCF_nohost old ho
  cases old with
  | std b => trivial
  | fast f =>
    simpa only [WideSigned.Row16.lift,WideSigned.Row16.fast,NoHost3,WEXFast.FNoHost,
      WideSigned.Fast16.FastSite.garb,WEXFast.FastSite.garb] using h
  | fast1 f =>
    simpa only [WideSigned.Row16.lift,WideSigned.Row16.fast1,NoHost3,WEXFast.FNoHost,
      WideSigned.Fast16.FastSite1.garb,WEXFast.FastSite1.garb] using h

theorem row_program_support (start : Nat) :
    straightWires (WideSigned.Row16.program start) ⊆ support := by
  exact fprog_support WideSigned.Row16.code WideSigned.Row16.geometry row_literals
    WideSigned.Row16.strict WideSigned.Row16.ctl WideSigned.Row16.ctl3 row_lookups row_nohost start

theorem fixed_program_support (start : Nat) :
    straightWires (WideSigned.Row16.fixedProgram start) ⊆ support := by
  rw [WideSigned.Row16.fixedProgram,straightWires_castFinish]
  exact row_program_support start
theorem frame_support (r : Nat) (row : (j : Nat) → Straight 65536 j (j + r))
    (hrow : ∀ j, ChallengeMigration.straightWires (row j) ⊆ support)
    (start : Nat) : ChallengeMigration.straightWires (WideSigned.Frame16.program r row start) ⊆ support := by
  have cover : newSourceH ⊆ support := old_cover
  have hs (j : Nat) : ChallengeMigration.straightWires (WideSigned.Body.nProgram .w16 j) ⊆ support := by
    rw [WideSigned.Body.nProgram, straightWires_reindex]
    exact (nFast_newH j).trans cover
  have hp (j : Nat) : ChallengeMigration.straightWires (WideSigned.Body.prefixProgram .w16 j) ⊆ support := by
    rw [WideSigned.Body.prefixProgram, straightWires_append, literalProgram_support, literalProgram_support]
    decide
  have hpost (j : Nat) : ChallengeMigration.straightWires (WideSigned.Body.suffixProgram .w16 j) ⊆ support := by
    rw [WideSigned.Body.suffixProgram, straightWires_append, literalProgram_support, literalProgram_support]
    decide
  rw [WideSigned.Frame16.program, straightWires_castFinish]
  simp only [straightWires_append, List.append_subset]
  exact ⟨⟨⟨⟨hp start, hs start⟩, hrow _⟩, hs _⟩, hpost _⟩


theorem signed_support (start : Nat) :
    straightWires (WideSigned.Signed16.program start) ⊆ support := by
  rw [WideSigned.Signed16.program,straightWires_castFinish]
  exact frame_support _ WideSigned.Row16.fixedProgram fixed_program_support start

def compact : Wire ≃ Wire :=
  (PathShare.piH.trans (Equiv.swap 1619 1616)).trans (Equiv.swap 14436 1617)

theorem compact_bound (v : Wire) (hv : v∈support) : compact v < 1618 := by
  rcases List.mem_append.mp hv with h | h
  · have hp := (PathShare.piH_apply v).trans_lt (PathShare.piH_bound v h)
    simp only [compact,Equiv.trans_apply,Equiv.swap_apply_def]
    dsimp only [Wire] at hp ⊢
    split_ifs <;> omega
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl <;> decide

theorem compact_point (v : Wire) (hv : v∈pointLogicalWires) : compact v=v := by
  rw [compact,Equiv.trans_apply,Equiv.trans_apply,PathShare.piH_point v hv]
  have hb := point_wire_small v hv
  simp only [Equiv.swap_apply_def]
  dsimp only [Wire] at *
  split_ifs <;> omega

theorem compact_active : compact 836=836 := by decide
theorem compact_sign : compact 870=870 := by decide
theorem compact_extra : compact 871=1617 := by decide

theorem compact_address (v : Wire) (hv : v∈streamAddress) : compact v=v := by
  have hb : 855≤v ∧ v<871 := by simpa only [streamAddress,List.mem_range'_1] using hv
  have hf : fixedPort v := by unfold fixedPort; dsimp only [Wire] at *; omega
  rw [compact,Equiv.trans_apply,Equiv.trans_apply,PathShare.piH_fixed v hf]
  simp only [Equiv.swap_apply_def]
  dsimp only [Wire] at *
  split_ifs <;> omega

theorem packed_support (start : Nat) :
    straightWires (relabelStraight compact (WideSigned.Signed16.program start)) ⊆ List.range 1618 := by
  rw [straightWires_relabel]
  intro v hv
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv
  exact List.mem_range.mpr (compact_bound u (signed_support start hu))
theorem compact_pointWrite (P : Point) (s : BasisState) :
    relabelBasis compact (pointWrite P s) = pointWrite P (relabelBasis compact s) := by
  funext v
  by_cases hv : v ∈ pointLogicalWires
  · have he : compact.symm v = v := (Equiv.symm_apply_eq compact).mpr (compact_point v hv).symm
    simp only [relabelBasis, pointWrite, he, if_pos hv]
  · have hi : compact.symm v ∉ pointLogicalWires := by
      intro h
      have he := compact_point _ h
      rw [Equiv.apply_symm_apply] at he
      exact hv (he.symm ▸ h)
    simp only [relabelBasis, pointWrite, if_neg hv, if_neg hi]

/-- Tight support without wire `10000`: `PathShare.newSourceH` (1616 wires) plus wire `871`. -/
def support17 : List Wire := PathShare.newSourceH ++ [871]
theorem old_cover17 : PathShare.newSourceH ⊆ support17 := List.subset_append_left _ _
theorem support17_length : support17.length = 1617 := by decide

theorem frame_support17 (r : Nat) (row : (j : Nat) → Straight 65536 j (j + r))
    (hrow : ∀ j, ChallengeMigration.straightWires (row j) ⊆ support17)
    (start : Nat) : ChallengeMigration.straightWires (WideSigned.Frame16.program r row start) ⊆ support17 := by
  have cover : newSourceH ⊆ support17 := old_cover17
  have hs (j : Nat) : ChallengeMigration.straightWires (WideSigned.Body.nProgram .w16 j) ⊆ support17 := by
    rw [WideSigned.Body.nProgram, straightWires_reindex]
    exact (nFast_newH j).trans cover
  have hp (j : Nat) : ChallengeMigration.straightWires (WideSigned.Body.prefixProgram .w16 j) ⊆ support17 := by
    rw [WideSigned.Body.prefixProgram, straightWires_append, literalProgram_support, literalProgram_support]
    decide
  have hpost (j : Nat) : ChallengeMigration.straightWires (WideSigned.Body.suffixProgram .w16 j) ⊆ support17 := by
    rw [WideSigned.Body.suffixProgram, straightWires_append, literalProgram_support, literalProgram_support]
    decide
  rw [WideSigned.Frame16.program, straightWires_castFinish]
  simp only [straightWires_append, List.append_subset]
  exact ⟨⟨⟨⟨hp start, hs start⟩, hrow _⟩, hs _⟩, hpost _⟩

def compact17 : Wire ≃ Wire :=
  PathShare.piH.trans (Equiv.swap 14436 1616)

theorem compact17_bound (v : Wire) (hv : v ∈ support17) : compact17 v < 1617 := by
  rcases List.mem_append.mp hv with h | h
  · have hp := (PathShare.piH_apply v).trans_lt (PathShare.piH_bound v h)
    simp only [compact17, Equiv.trans_apply, Equiv.swap_apply_def]
    dsimp only [Wire] at hp ⊢
    split_ifs <;> omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst h
    decide

theorem compact17_point (v : Wire) (hv : v ∈ pointLogicalWires) : compact17 v = v := by
  rw [compact17, Equiv.trans_apply, PathShare.piH_point v hv]
  have hb := point_wire_small v hv
  simp only [Equiv.swap_apply_def]
  dsimp only [Wire] at *
  split_ifs <;> omega

theorem compact17_active : compact17 836 = 836 := by decide
theorem compact17_sign : compact17 870 = 870 := by decide
theorem compact17_extra : compact17 871 = 1616 := by decide

theorem compact17_address (v : Wire) (hv : v ∈ streamAddress) : compact17 v = v := by
  have hb : 855 ≤ v ∧ v < 871 := by simpa only [streamAddress, List.mem_range'_1] using hv
  have hf : fixedPort v := by unfold fixedPort; dsimp only [Wire] at *; omega
  rw [compact17, Equiv.trans_apply, PathShare.piH_fixed v hf]
  simp only [Equiv.swap_apply_def]
  dsimp only [Wire] at *
  split_ifs <;> omega

theorem compact17_pointWrite (P : Point) (s : BasisState) :
    relabelBasis compact17 (pointWrite P s) = pointWrite P (relabelBasis compact17 s) := by
  funext v
  by_cases hv : v ∈ pointLogicalWires
  · have he : compact17.symm v = v := (Equiv.symm_apply_eq compact17).mpr (compact17_point v hv).symm
    simp only [relabelBasis, pointWrite, he, if_pos hv]
  · have hi : compact17.symm v ∉ pointLogicalWires := by
      intro h
      have he := compact17_point _ h
      rw [Equiv.apply_symm_apply] at he
      exact hv (he.symm ▸ h)
    simp only [relabelBasis, pointWrite, if_neg hv, if_neg hi]

/-- Tight support with 4 flag-hosted pool wires retired (`14874..14877`): `PoolHost.newSourceH7` (1612 wires) plus wire `871`. -/
def support17_7 : List Wire := PoolHost.newSourceH7 ++ [871]
theorem old_cover17_7 : PoolHost.newSourceH7 ⊆ support17_7 := List.subset_append_left _ _
theorem support17_7_length : support17_7.length = 1613 := by decide

theorem nFast_newH7 (start : Nat) : ChallengeMigration.straightWires (nFastProgram start) ⊆ PoolHost.newSourceH7 := by
  apply literalFixed_support (n := 32768) (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram) 256
    ((literal_meas (n := 32768) _).trans fastWindowSign_normalized_counts.2) PoolHost.newSourceH7 (start := start)
  rw [ECDSAAdd.Baselines.normalize_wires]
  have hs := WEX.finiteSignMeasured_support (negateYLayout streamLayout) 870 838 streamLayout.core.generic ECDSAAdd.p
  have cover : 870 :: 838 :: (negateYLayout streamLayout).wires streamLayout.core.generic ⊆ PoolHost.newSourceH7 := by
    apply PoolHost.newSourceH7_of_bounds; decide +kernel
  have sub : ECDSAAdd.wires fastWindowSignProgram ⊆ ECDSAAdd.wires
      (WEX.finiteSignMeasured (negateYLayout streamLayout) 870 838 streamLayout.core.generic ECDSAAdd.p) := by
    simp only [fastWindowSignProgram, WEX.finiteSignMeasured, ECDSAAdd.wires_append]
    exact Finset.union_subset_union (Finset.union_subset_union (fun _ h => h) WEX.TrimmedSign.reflection_wires)
      (fun _ h => h)
  exact sub.trans (hs.trans (fun w hw => List.mem_toFinset.mpr (cover (List.mem_toFinset.mp hw))))

theorem frame_support17_7 (r : Nat) (row : (j : Nat) → Straight 65536 j (j + r))
    (hrow : ∀ j, ChallengeMigration.straightWires (row j) ⊆ support17_7)
    (start : Nat) : ChallengeMigration.straightWires (WideSigned.Frame16.program r row start) ⊆ support17_7 := by
  have cover : PoolHost.newSourceH7 ⊆ support17_7 := old_cover17_7
  have hs (j : Nat) : ChallengeMigration.straightWires (WideSigned.Body.nProgram .w16 j) ⊆ support17_7 := by
    rw [WideSigned.Body.nProgram, straightWires_reindex]
    exact (nFast_newH7 j).trans cover
  have hp (j : Nat) : ChallengeMigration.straightWires (WideSigned.Body.prefixProgram .w16 j) ⊆ support17_7 := by
    rw [WideSigned.Body.prefixProgram, straightWires_append, literalProgram_support, literalProgram_support]
    decide
  have hpost (j : Nat) : ChallengeMigration.straightWires (WideSigned.Body.suffixProgram .w16 j) ⊆ support17_7 := by
    rw [WideSigned.Body.suffixProgram, straightWires_append, literalProgram_support, literalProgram_support]
    decide
  rw [WideSigned.Frame16.program, straightWires_castFinish]
  simp only [straightWires_append, List.append_subset]
  exact ⟨⟨⟨⟨hp start, hs start⟩, hrow _⟩, hs _⟩, hpost _⟩

def compact17_7 : Wire ≃ Wire :=
  PoolHost.piH7.trans (Equiv.swap 14436 1612)

theorem compact17_7_bound (v : Wire) (hv : v ∈ support17_7) : (compact17_7 v : Nat) < 1613 := by
  rcases List.mem_append.mp hv with h | h
  · have hp := PoolHost.piH7_bound v h
    simp only [compact17_7, Equiv.trans_apply, Equiv.swap_apply_def]
    dsimp only [Wire] at hp ⊢
    split_ifs <;> omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst h
    decide

theorem compact17_7_point (v : Wire) (hv : v ∈ pointLogicalWires) : compact17_7 v = v := by
  rw [compact17_7, Equiv.trans_apply, PoolHost.piH7_point v hv]
  have hb := point_wire_small v hv
  simp only [Equiv.swap_apply_def]
  dsimp only [Wire] at *
  split_ifs <;> omega

theorem compact17_7_active : compact17_7 836 = 836 := by decide
theorem compact17_7_sign : compact17_7 870 = 870 := by decide
theorem compact17_7_extra : compact17_7 871 = 1612 := by decide

theorem compact17_7_address (v : Wire) (hv : v ∈ streamAddress) : compact17_7 v = v := by
  have hb : 855 ≤ v ∧ v < 871 := by simpa only [streamAddress, List.mem_range'_1] using hv
  have hf : fixedPort v := by unfold fixedPort; dsimp only [Wire] at *; omega
  rw [compact17_7, Equiv.trans_apply, PoolHost.piH7_fixed v hf]
  simp only [Equiv.swap_apply_def]
  dsimp only [Wire] at *
  split_ifs <;> omega

theorem compact17_7_pointWrite (P : Point) (s : BasisState) :
    relabelBasis compact17_7 (pointWrite P s) = pointWrite P (relabelBasis compact17_7 s) := by
  funext v
  by_cases hv : v ∈ pointLogicalWires
  · have he : compact17_7.symm v = v := (Equiv.symm_apply_eq compact17_7).mpr (compact17_7_point v hv).symm
    simp only [relabelBasis, pointWrite, he, if_pos hv]
  · have hi : compact17_7.symm v ∉ pointLogicalWires := by
      intro h
      have he := compact17_7_point _ h
      rw [Equiv.apply_symm_apply] at he
      exact hv (he.symm ▸ h)
    simp only [relabelBasis, pointWrite, if_neg hv, if_neg hi]

/-! ### Narrow-window compaction transport (`PoolHost.piH7`, `< 1612`) -/

theorem piH7_address (w : Wire) (h : w ∈ streamAddress) : PoolHost.piH7 w = w := by
  apply PoolHost.piH7_fixed
  exact Or.inr (Or.inr (Or.inr (by simpa [streamAddress] using h)))

def pullH7 (s : BasisState) : BasisState := relabelBasis PoolHost.piH7.symm s

theorem pullH7_at (s : BasisState) (w : Wire) (h : fixedPort w) : pullH7 s w = s w := by
  simp only [pullH7, relabelBasis, Equiv.symm_symm, PoolHost.piH7_fixed w h]

theorem pullH7_hot (s : BasisState) (i : Fin 128) : pullH7 s (hot i) = s (hot i) := by
  simp only [pullH7, relabelBasis, Equiv.symm_symm, PoolHost.piH7_hot]

theorem pullH7_write (P : Point) (s : BasisState) : pullH7 (pointWrite P s) = pointWrite P (pullH7 s) := by
  funext w
  by_cases hp : w ∈ pointLogicalWires
  · have h1 : PoolHost.piH7 w = w := PoolHost.piH7_point w hp
    simp only [pullH7, relabelBasis, Equiv.symm_symm, pointWrite, h1, if_pos hp]
  · have h2 : PoolHost.piH7 w ∉ pointLogicalWires := by
      intro hm
      have he := PoolHost.piH7_point _ hm
      exact hp (PoolHost.piH7.injective he ▸ hm)
    simp only [pullH7, relabelBasis, Equiv.symm_symm, pointWrite, if_neg hp, if_neg h2]

theorem pushH7_write (P : Point) (s : BasisState) :
    relabelBasis PoolHost.piH7 (pointWrite P (pullH7 s)) = pointWrite P s := by
  rw [← pullH7_write P s]
  funext w
  simp only [pullH7, relabelBasis, Equiv.symm_symm, Equiv.apply_symm_apply]

theorem pullH7_coordinates (s : BasisState) : pointStateCoordinates (pullH7 s) = pointStateCoordinates s := by
  have he (ws : List Wire) (h : ∀ w ∈ ws, w ∈ pointLogicalWires) : wireValues ws (pullH7 s) = wireValues ws s :=
    List.map_congr_left fun w hw => by
      simp only [pullH7, relabelBasis, Equiv.symm_symm, PoolHost.piH7_point w (h w hw)]
  have hx : wireValues (List.range' 263 256) (pullH7 s) = wireValues (List.range' 263 256) s :=
    he _ (fun w hw => List.mem_append_left _ hw)
  have hy : wireValues (List.range' 580 256) (pullH7 s) = wireValues (List.range' 580 256) s :=
    he _ (fun w hw => List.mem_append_right _ (List.mem_append_left _ hw))
  have h838 : pullH7 s 838 = s 838 := by
    simp only [pullH7, relabelBasis, Equiv.symm_symm,
      PoolHost.piH7_point 838 (by simp [pointLogicalWires, pointCorrectionYInf])]
  simp only [pointStateCoordinates, hx, hy, h838]

theorem pullH7_digit (s : BasisState) : windowRawDigit 0 (pullH7 s) = windowRawDigit 0 s := by
  have he : wireValues (windowAddressBits 0) (pullH7 s) = wireValues (windowAddressBits 0) s :=
    List.map_congr_left fun w hw => by
      have hfix : fixedPort w := by
        simp only [windowAddressBits, windowBankStart, List.mem_range'_1] at hw
        unfold fixedPort; omega
      exact pullH7_at s w hfix
  have h870 : pullH7 s (windowBankStart 0 + 15) = s (windowBankStart 0 + 15) :=
    pullH7_at s 870 (by decide +kernel)
  simp only [windowRawDigit, he, h870]

def readyH7 (s : BasisState) : Prop := windowReady (pullH7 s) ∧ MeasuredClear.HotClean hot s

theorem readyH7_active (s : BasisState) (h : readyH7 s) : s 836 = true := by
  simpa only [pullH7_at s 836 (by decide +kernel)] using windowReady_active (pullH7 s) h.1

theorem readyH7_write (P : Point) (s : BasisState) (h : readyH7 s) :
    readyH7 (pointWrite P s) := by
  refine ⟨?_, pointWrite_hot P s h.2⟩
  rw [pullH7_write]
  exact windowReady_write P (pullH7 s) h.1

theorem pullH7_address (s : BasisState) (v : Wire) (hv : v ∈ streamAddress) (b : Bool) :
    pullH7 (s[v ↦ b]) = (pullH7 s)[v ↦ b] := by
  have hh' : PoolHost.piH7.symm v = v := by
    rw [Equiv.symm_apply_eq]; exact (piH7_address v hv).symm
  simp only [pullH7, relabelBasis_upd, hh']

theorem readyH7_address (s : BasisState) (h : readyH7 s)
    (v : Wire) (hv : v ∈ streamAddress) (b : Bool) : readyH7 (s[v ↦ b]) := by
  refine ⟨?_, ?_⟩
  · rw [pullH7_address s v hv b]
    exact windowReady_address (pullH7 s) h.1 v hv b
  · intro i
    have hn : hot i ≠ v := fun he => hot_outside_address i (he.symm ▸ hv)
    exact (upd_other s v b hn).trans (h.2 i)

theorem pullH7_first (s : BasisState) (h : FirstWindowInput s) : FirstWindowInput (pullH7 s) := by
  constructor
  · simpa only [pullH7_at s 836 (by decide +kernel)] using h.1
  · intro w hw ha
    change s (PoolHost.piH7 w) = false
    apply h.2
    · intro hh
      have hfix : PoolHost.piH7 836 = 836 := PoolHost.piH7_fixed _ (by decide +kernel)
      exact hw (PoolHost.piH7.injective (hh.trans hfix.symm))
    · intro hh
      have hfix := piH7_address _ hh
      have he : PoolHost.piH7 w = w := PoolHost.piH7.injective hfix
      exact ha (he ▸ hh)

theorem readyH7_first (s : BasisState) (h : FirstWindowInput s) (P : Point) :
    readyH7 (pointWrite P s) := by
  refine ⟨?_, ?_⟩
  · rw [pullH7_write]
    exact windowReady_first (pullH7 s) (pullH7_first s h) P
  · apply pointWrite_hot P s
    intro i
    apply h.2
    · have hi := i.isLt
      simp only [hot]
      dsimp only [Wire] at *
      omega
    · exact hot_outside_address i

def stateH7 (coeffs : Fin 32768 → PointCoeff) (Q : Point) (s : BasisState) : BasisState :=
  relabelBasis PoolHost.piH7 (bodyState coeffs Q (pullH7 s))

theorem stateH7_correct (coeffs : Fin 32768 → PointCoeff) (Q : Point)
    (s : BasisState) (hs : readyH7 s) (P : Point)
    (hP : pointStateCoordinates s = fig14PointEncoding P) :
    stateH7 coeffs Q s = pointWrite
      (P + if s 836 then
        (if s 870 then constantPoint Q (coeffs ⟨signedTableAddress 32768
          (windowRawDigit 0 s), signedTableAddress_bound 32768 _ (windowRawDigit_bound 0 s)⟩)
         else -constantPoint Q (coeffs ⟨signedTableAddress 32768
          (windowRawDigit 0 s), signedTableAddress_bound 32768 _ (windowRawDigit_bound 0 s)⟩))
        else 0) s := by
  unfold stateH7
  rw [bodyState_correct coeffs Q (pullH7 s) hs.1 P ((pullH7_coordinates s).trans hP), pushH7_write]
  simp only [pullH7_at s 836 (by decide +kernel), pullH7_at s 870 (by decide +kernel), pullH7_digit]

theorem relabelH7_coherent {s e : Nat} (p : Straight 32768 s e) (coeffs : Fin 32768 → PointCoeff)
    (Q : Point) (history : Fin s → Bool)
    (hc : CoherentlyImplementsOn (p.instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)) Ready) :
    CoherentlyImplementsOn ((relabelStraight PoolHost.piH7 p).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (stateH7 coeffs Q))
      (fun s => readyH7 s ∧ ∃ P, pointStateCoordinates s = fig14PointEncoding P) := by
  have h := hc.relabel PoolHost.piH7
  have hr : CoherentlyImplementsOn
      ((p.instantiate (readConstant coeffs Q) history).relabel PoolHost.piH7)
      ((relabelState PoolHost.piH7).comp ((Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)).comp
        (relabelState PoolHost.piH7.symm)))
      (fun s => readyH7 s ∧ ∃ P, pointStateCoordinates s = fig14PointEncoding P) := by
    obtain ⟨cs, aligned, mass⟩ := h
    refine ⟨cs, aligned.imp ?_, mass⟩
    intro b c hb s hs
    apply hb s
    refine ⟨hs.1.1, ?_⟩
    intro i
    exact (pullH7_hot s i).trans (hs.1.2 i)
  have he := hr.congrIdeal (secondIdeal := Finsupp.lmapDomain ℂ ℂ (stateH7 coeffs Q))
    (by intro s _; simp [stateH7, pullH7, LinearMap.comp_apply, relabelState, ket])
  rw [relabelStraight_instantiate]
  exact he

end
end ShorECDLP.Entrant.TightSupport
end

/-! ### Consolidated from `WideBank8.lean` -/
section
/-! Balanced eight-bit bank for the sixteen-bit clears of the wide (seventeen-bit) window rows.

Every masked clear of a wide row is a recycled measured clear over the sixteen address bits
`855..869, 871`. The shipped bank splits them seven low / nine high, costing
`(2^7 - 1) + (2^9 - 1) = 638` CCX per clear. This file instantiates the generic split network at
eight low bits (256 unary wires, 255 cells) with an eight-wire high tree, costing `254 + 255 = 502` after specializing the known-one first split.

The 256 hot wires are the first 256 cleared targets (`headD + i`), and the phase scratch is the
ninth wire `14840` of the old clear path bank, which the eight-level tree no longer uses. The
scratch is only a dirty ancilla of `mixedCircuit`, so it need not be a cleared target.

Everything bank-independent (site geometry, swap networks, select code, frame, sign) is imported;
only the declarations whose definitions contain the clear are re-instantiated below. -/

namespace ShorECDLP.Entrant.MeasuredClear
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

/-- Nat-indexed views of the eight low address wires and the 256 unary wires. -/
def lowN8 (low : Fin 8 → Wire) (j : Nat) : Wire := if h : j < 8 then low ⟨j, h⟩ else low 0

def hotNat8 (hot : Fin 256 → Wire) (x : Nat) : Wire := if h : x < 256 then hot ⟨x, h⟩ else hot 0

/-- The low-address bank: eight address bits split into 256 unary wires. -/
def hotNetwork8 (low : Fin 8 → Wire) (hot : Fin 256 → Wire) : List SplitCell :=
  hotNetN (lowN8 low) (hotNat8 hot) 8

def slowHotPrepare8 (low : Fin 8 → Wire) (hot : Fin 256 → Wire) : Circuit :=
  [.X (hot 0)] ++ splitNetwork (hotNetwork8 low hot)

def hotPrepare8 (low : Fin 8 → Wire) (hot : Fin 256 → Wire) : Circuit :=
  [.X (hot 0)] ++ ParityBank.parityNet (lowN8 low) (hotNat8 hot) 8

def hotAddress8 (low : Fin 8 → Wire) (s : BasisState) : Nat := addrN (lowN8 low) s 8

def HotClean8 (hot : Fin 256 → Wire) (s : BasisState) : Prop := ∀ i, s (hot i) = false

theorem hotNetwork_length8 (low : Fin 8 → Wire) (hot : Fin 256 → Wire) :
    (hotNetwork8 low hot).length = 255 := by
  simp [hotNetwork8, hotNetN_length]

theorem hotLayout_of8 (low : Fin 8 → Wire) (hot : Fin 256 → Wire)
    (hi : Function.Injective hot) (hd : ∀ i j, low i ≠ hot j) :
    HotLayout 8 (lowN8 low) (hotNat8 hot) := by
  constructor
  · intro x y hx hy he
    have hx' : x < 256 := by simpa using hx
    have hy' : y < 256 := by simpa using hy
    simp only [hotNat8, hx', hy', dite_true] at he
    exact congrArg Fin.val (hi he)
  · intro j x hj hx
    have hx' : x < 256 := by simpa using hx
    simp only [lowN8, hotNat8, hj, hx', dite_true]
    exact hd _ _

theorem mem_hotNetwork8 (low : Fin 8 → Wire) (hot : Fin 256 → Wire) (c : SplitCell)
    (hc : c ∈ hotNetwork8 low hot) :
    ∃ j : Fin 8, ∃ x y : Fin 256, c = ⟨low j, hot x, hot y⟩ ∧ x ≠ y := by
  obtain ⟨j, i, hj, hi, rfl⟩ := mem_hotNetN _ _ 8 c hc
  have h2 : i + 2^j < 2^8 := pow_level_lt hj i hi
  have h2' : i + 2^j < 256 := by simpa using h2
  have h1 : i < 256 := by omega
  refine ⟨⟨j, hj⟩, ⟨i, h1⟩, ⟨i + 2^j, h2'⟩, ?_, ?_⟩
  · simp [lowN8, hotNat8, hj, h1, h2']
  · intro he
    have := congrArg Fin.val he
    have hp : 0 < 2^j := by positivity
    simp at this

theorem hotNetwork_physical8 (low : Fin 8 → Wire) (hot : Fin 256 → Wire)
    (hi : Function.Injective hot) (hd : ∀ i j, low i ≠ hot j) :
    ∀ c ∈ hotNetwork8 low hot, c.Physical := by
  intro c hc
  obtain ⟨j, x, y, rfl, hxy⟩ := mem_hotNetwork8 low hot c hc
  exact ⟨hd j x, hd j y, fun he => hxy (hi he)⟩

theorem hotStart8 (hot : Fin 256 → Wire) (hi : Function.Injective hot)
    (s : BasisState) (hs : HotClean8 hot s) :
    ∀ x, x < 2^8 → Classical.run [.X (hot 0)] s (hotNat8 hot x) = decide (x = 0) := by
  intro x hx
  have hx' : x < 256 := by simpa using hx
  simp only [hotNat8, hx', dite_true]
  by_cases h0 : x = 0
  · subst h0
    simp [Classical.run, Classical.applyGate, upd, hs 0]
  · have hne : hot ⟨x, hx'⟩ ≠ hot 0 := fun he => h0 (congrArg Fin.val (hi he))
    simp [Classical.run, Classical.applyGate, upd, hne, hs ⟨x, hx'⟩, h0]

theorem hotPrepare_eq8 (low : Fin 8 → Wire) (hot : Fin 256 → Wire)
    (hi : Function.Injective hot) (hd : ∀ i j,low i≠hot j)
    (s : BasisState) (hs : HotClean8 hot s) :
    Classical.run (hotPrepare8 low hot) s=Classical.run (slowHotPrepare8 low hot) s := by
  rw [hotPrepare8,slowHotPrepare8,Classical.run_append,Classical.run_append,hotNetwork8]
  exact ParityBank.parityNet_eq 8 (lowN8 low) (hotNat8 hot) (hotLayout_of8 low hot hi hd)
    _ (hotStart8 hot hi s hs) 8 le_rfl

theorem hotNetwork_ready8 (low : Fin 8 → Wire) (hot : Fin 256 → Wire)
    (hi : Function.Injective hot) (hd : ∀ i j, low i ≠ hot j)
    (s : BasisState) (hs : HotClean8 hot s) :
    NetworkReady (hotNetwork8 low hot) (Classical.run [.X (hot 0)] s) :=
  (net_run 8 (lowN8 low) (hotNat8 hot) (hotLayout_of8 low hot hi hd) _ (hotStart8 hot hi s hs) 8 le_rfl).2.2

theorem hotPrepare_marker8 (low : Fin 8 → Wire) (hot : Fin 256 → Wire)
    (hi : Function.Injective hot) (hd : ∀ i j, low i ≠ hot j)
    (s : BasisState) (hs : HotClean8 hot s) (i : Fin 256) :
    Classical.run (hotPrepare8 low hot) s (hot i) = decide (i.val = hotAddress8 low s) := by
  have h := (net_run 8 (lowN8 low) (hotNat8 hot) (hotLayout_of8 low hot hi hd) _ (hotStart8 hot hi s hs) 8 le_rfl).1
    i.val (by simp)
  have hhot : hotNat8 hot i.val = hot i := by simp [hotNat8, i.isLt]
  rw [hhot] at h
  rw [hotPrepare_eq8 low hot hi hd s hs, slowHotPrepare8, Classical.run_append, hotNetwork8, h, hotAddress8]
  congr 2
  apply addrN_congr
  intro j hj
  have hj' : j < 8 := hj
  simp only [lowN8, hj', dite_true]
  have hne : low ⟨j, hj'⟩ ≠ hot 0 := hd _ _
  simp [Classical.run, Classical.applyGate, upd, hne]

theorem hotPrepare_frame8 (low : Fin 8 → Wire) (hot : Fin 256 → Wire)
    (s : BasisState) (w : Wire) (hw : ∀ i,w≠hot i) :
    Classical.run (hotPrepare8 low hot) s w=s w := by
  rw [hotPrepare8,Classical.run_append,ParityBank.parityNet_frame 8 _ _ 8 le_rfl _ w (by
    intro x hx
    have hx' : x<256 := by simpa using hx
    simpa only [hotNat8,hx',dite_true] using hw ⟨x,hx'⟩)]
  simp [Classical.run,Classical.applyGate,upd,hw]

theorem hotAddress_bound8 (low : Fin 8 → Wire) (s : BasisState) : hotAddress8 low s < 256 := by
  have h := addrN_lt (lowN8 low) s 8
  simpa [hotAddress8] using h

attribute [irreducible] hotNetwork8

def phasePorts8 {n base : Nat} (hot : Fin 256 → Wire)
    (items : List (ClearPort n × Fin base)) : List (RecordPort n base) :=
  items.flatMap fun item => List.ofFn fun i : Fin 256 =>
    ⟨fun h => item.1.ref (256 * h + i.val), item.1.value, item.2, hot i⟩

def logicalPorts8 {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (hot : Fin 256 → Wire) : List (RecordPort n 2) :=
  phasePorts8 hot (data.zip (outcomes.map boolRecord))

def hotBank8 (hot : Fin 256 → Wire) : List Wire := List.ofFn hot

def fixupSource8 {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (read : ConstantBit n → Bool) (low : Fin 8 → Wire) (hot : Fin 256 → Wire)
    (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire) : AdaptiveCircuit :=
  (AdaptiveCircuit.unitary (hotPrepare8 low hot) .done).seq
    ((phaseLookupSource (logicalPorts8 data outcomes hot) scratch read boolHistory
      tree root paths (hotBank8 hot)).seq
      ((eraseNetworkSource (hotNetwork8 low hot)).seq (.unitary [.X (hot 0)] .done)))

def fixupProgram8 {n base : Nat} (data : List (ClearPort n)) (refs : List (Fin base))
    (low : Fin 8 → Wire) (hot : Fin 256 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire) :
    Straight n base (base + recordMeasurements (recordUnaryOps tree root paths) + 255) :=
  (literalProgram (hotPrepare8 low hot)).append
    ((literalProgram ((hotBank8 hot).map Gate.H)).append
      ((recordLookupProgram (phasePorts8 hot (data.zip refs)) scratch
        (recordUnaryOps tree root paths) base (Nat.le_refl base)).append
        ((literalProgram (Circuit.adjoint ((hotBank8 hot).map Gate.H))).append
          (castFinish (by simp [hotNetwork_length8])
            ((eraseNetwork n (hotNetwork8 low hot)
              (base + recordMeasurements (recordUnaryOps tree root paths))).append
              (literalProgram [.X (hot 0)]))))))

def measuredClear8 {n : Nat} (data : List (ClearPort n)) (low : Fin 8 → Wire) (hot : Fin 256 → Wire)
    (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire) (start : Nat) :
    Straight n start (start + data.length + (recordMeasurements (recordUnaryOps tree root paths) + 255)) :=
  castFinish (by simp) (measureThen (R := recordMeasurements (recordUnaryOps tree root paths) + 255)
    (fun cursor refs => castFinish (by omega) (fixupProgram8 data refs low hot tree root scratch paths))
    (data.map ClearPort.target) start ([] : List (Fin start)))

def LoadedClear8 {n : Nat} (data : List (ClearPort n)) (read : ConstantBit n → Bool)
    (low : Fin 8 → Wire) (tree : UnaryActionTree) (root : Wire) (s : BasisState) : Prop :=
  ∀ p ∈ data, s p.target = (s root && decide (read (p.ref (256 * tree.routeLabel s + hotAddress8 low s)) = p.value))

theorem phasePorts_targets8 {n base : Nat} (hot : Fin 256 → Wire)
    (items : List (ClearPort n × Fin base)) :
    ∀ p ∈ phasePorts8 hot items, p.target ∈ hotBank8 hot := by
  intro p hp
  obtain ⟨item, _, hi⟩ := List.mem_flatMap.mp hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hi
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

theorem hotPrepare_hp8 (low : Fin 8 → Wire) (hot : Fin 256 → Wire) :
    Classical.HPFree (hotPrepare8 low hot) := by
  simp [hotPrepare8, ParityBank.parityNet_hp]

def fixupFactor8 {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (read : ConstantBit n → Bool) (low : Fin 8 → Wire) (hot : Fin 256 → Wire)
    (tree : UnaryActionTree) (root : Wire) (s : BasisState) : ℂ :=
  phaseLookupFactor (logicalPorts8 data outcomes hot) read boolHistory tree root
    (Classical.run (hotPrepare8 low hot) s)

theorem fixupSource_coherent8 {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (read : ConstantBit n → Bool) (low : Fin 8 → Wire) (hot : Fin 256 → Wire)
    (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire)
    (hl : tree.Layout root paths) (hi : Function.Injective hot)
    (hdlow : ∀ i j, low i ≠ hot j)
    (hbank : (hotBank8 hot).Disjoint (root :: tree.indexWires.dedup ++ paths))
    (hs : scratch ∉ root :: tree.indexWires.dedup ++ paths)
    (hshot : scratch ∉ hotBank8 hot) :
    CoherentlyImplementsOn (fixupSource8 data outcomes read low hot tree root scratch paths)
      (basisIdeal id (fixupFactor8 data outcomes read low hot tree root))
      (fun s => HotClean8 hot s ∧ Clean paths s) := by
  have hp := phasePorts_targets8 hot (data.zip (outcomes.map boolRecord))
  have htarget : ∀ p ∈ logicalPorts8 data outcomes hot, scratch ≠ p.target := by
    intro p hpp he
    exact hshot (he.symm ▸ hp p hpp)
  have hq := phaseLookup_coherent (logicalPorts8 data outcomes hot) scratch read boolHistory
    tree root paths (hotBank8 hot) hl (List.nodup_ofFn.mpr hi) hbank hs hp htarget
  have hpre := (CoherentlyImplementsOn.unitary (hotPrepare8 low hot)
    (fun s => HotClean8 hot s ∧ Clean paths s)).seq hq (by
      intro s hvalid
      rw [run_ket_agrees_classical _ _ (hotPrepare_hp8 low hot)]
      apply supportedOn_ket
      intro w hw
      rw [hotPrepare_frame8 low hot s w (by
        intro i he
        exact List.disjoint_left.mp hbank (List.mem_ofFn.mpr ⟨i, he.symm⟩) (by simp [hw]))]
      exact hvalid.2 w hw)
  have hn := eraseNetwork_coherent (hotNetwork8 low hot) (hotNetwork_physical8 low hot hi hdlow)
  have hpost := hn.seq (CoherentlyImplementsOn.unitary [.X (hot 0)] (fun _ => True)) (by
    intro s hvalid v hv
    trivial)
  have htotal := hpre.seq hpost (by
    intro s hvalid
    simp only [LinearMap.comp_apply]
    rw [run_ket_agrees_classical _ _ (hotPrepare_hp8 low hot), basisIdeal_ket]
    apply supported_smul_state
    apply supportedOn_ket
    exact ⟨Classical.run [.X (hot 0)] s, hotNetwork_ready8 low hot hi hdlow s hvalid.1,
      by rw [hotPrepare_eq8 low hot hi hdlow s hvalid.1]; rfl⟩)
  rw [fixupSource8, ← adaptive_seq_assoc]
  apply htotal.congrIdeal
  intro s hvalid
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  rw [run_ket_agrees_classical _ _ (hotPrepare_hp8 low hot), basisIdeal_ket]
  simp only [map_smul, id_eq]
  rw [run_ket_agrees_classical _ _ (inverseNetwork_hp (hotNetwork8 low hot))]
  rw [hotPrepare_eq8 low hot hi hdlow s hvalid.1, slowHotPrepare8, Classical.run_append,
    inverseNetwork_correct (hotNetwork8 low hot) (hotNetwork_physical8 low hot hi hdlow) _
      (hotNetwork_ready8 low hot hi hdlow s hvalid.1),
    run_ket_agrees_classical _ _ (by simp), classical_x_twice]
  simp only [basisIdeal_ket, id_eq]
  rw [fixupFactor8, hotPrepare_eq8 low hot hi hdlow s hvalid.1, slowHotPrepare8, Classical.run_append]

theorem phasePorts_block8 (p : ClearPort n) (m : Bool) (hot : Fin 256 → Wire)
    (read : ConstantBit n → Bool) (row root : Nat) (s : BasisState) (selected : Fin 256)
    (hm : ∀ i, s (hot i) = decide (i = selected)) :
    xorPhase root (recordTargets (phasePorts8 hot ([(p, boolRecord m)])) row read boolHistory) s =
      if m && (s root && decide (read (p.ref (256 * row + selected.val)) = p.value)) then (-1 : ℂ) else 1 := by
  rw [xorPhase_recordTargets]
  simp only [phasePorts8, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_ofFn,
    List.prod_ofFn, Function.comp_def]
  rw [Finset.prod_eq_single selected]
  · rw [hm selected]
    cases hm0 : m <;> cases hr : s root <;>
      by_cases hrd : read (p.ref (256 * row + selected.val)) = p.value <;>
      simp [boolHistory, boolRecord]
  · intro i _ hi
    rw [hm i]
    simp [hi]
  · simp

theorem logicalPorts_cons8 (p : ClearPort n) (ps : List (ClearPort n)) (m : Bool)
    (ms : List Bool) (hot : Fin 256 → Wire) :
    logicalPorts8 (p :: ps) (m :: ms) hot = phasePorts8 hot ([(p, boolRecord m)]) ++ logicalPorts8 ps ms hot := by
  simp only [logicalPorts8, List.map_cons, List.zip_cons_cons, phasePorts8, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]

theorem phaseFactor_loaded8 {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (read : ConstantBit n → Bool) (hot : Fin 256 → Wire) (tree : UnaryActionTree) (root : Wire)
    (original prepared : BasisState) (selected : Fin 256)
    (hm : ∀ i, prepared (hot i) = decide (i = selected))
    (hw : ∀ p ∈ data, original p.target =
      (prepared root && decide (read (p.ref (256 * tree.routeLabel prepared + selected.val)) = p.value))) :
    phaseLookupFactor (logicalPorts8 data outcomes hot) read boolHistory tree root prepared =
      registerXPhase (data.map ClearPort.target) outcomes original := by
  unfold phaseLookupFactor
  induction data generalizing outcomes with
  | nil =>
    simp only [logicalPorts8, List.zip_nil_left, phasePorts8, List.flatMap_nil]
    simp [recordTargets, xorPhase, registerXPhase]
  | cons p ps ih =>
    cases outcomes with
    | nil =>
      simp only [logicalPorts8, List.map_nil, List.zip_nil_right, phasePorts8, List.flatMap_nil]
      simp [recordTargets, xorPhase, registerXPhase]
    | cons m ms =>
      rw [logicalPorts_cons8, recordTargets_append, xorPhase_append, phasePorts_block8 p m hot read _ root prepared selected hm,
        ih ms (fun q hq => hw q (by simp [hq]))]
      simp only [List.map_cons, registerXPhase, hw p (by simp)]

theorem phasePorts_cons8 {n base : Nat} (hot : Fin 256 → Wire)
    (item : ClearPort n × Fin base) (items : List (ClearPort n × Fin base)) :
    phasePorts8 hot (item :: items) = phasePorts8 hot ([item]) ++ phasePorts8 hot items := by
  simp only [phasePorts8, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem phasePorts_resolve8 {n base : Nat} (data : List (ClearPort n)) (refs : List (Fin base))
    (hot : Fin 256 → Wire) (scratch row control : Nat) (read : ConstantBit n → Bool) (saved : Fin base → Bool) :
    recordLeafCircuit (phasePorts8 hot (data.zip refs)) scratch row control read saved =
      recordLeafCircuit (logicalPorts8 data (refs.map saved) hot) scratch row control read boolHistory := by
  induction data generalizing refs with
  | nil => rfl
  | cons p ps ih =>
    cases refs with
    | nil => rfl
    | cons r rs =>
      simp only [List.zip_cons_cons, List.map_cons]
      rw [phasePorts_cons8, logicalPorts_cons8, recordLeafCircuit_append, recordLeafCircuit_append]
      rw [ih rs]
      congr 1
      simp only [phasePorts8, List.flatMap_cons, List.flatMap_nil, List.append_nil, recordLeafCircuit]
      apply flatMap_ofFn_congr
      intro i
      cases hm : saved r <;> simp [boolRecord, boolHistory]

theorem recordSource_resolve8 {n base : Nat} (data : List (ClearPort n)) (refs : List (Fin base))
    (hot : Fin 256 → Wire) (scratch : Wire) (read : ConstantBit n → Bool) (saved : Fin base → Bool)
    (ops : List RecordLookupOp) :
    recordLookupSource (phasePorts8 hot (data.zip refs)) scratch read saved ops =
      recordLookupSource (logicalPorts8 data (refs.map saved) hot) scratch read boolHistory ops := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | gates gs => simp only [recordLookupSource, ih]
    | leaf row control => simp only [recordLookupSource, phasePorts_resolve8, ih]
    | erase a b t => simp only [recordLookupSource, ih]

theorem fixupProgram_run8 {n base : Nat} (data : List (ClearPort n)) (refs : List (Fin base))
    (read : ConstantBit n → Bool) (low : Fin 8 → Wire) (hot : Fin 256 → Wire)
    (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire) (history : Fin base → Bool) :
    ((fixupProgram8 data refs low hot tree root scratch paths).instantiate read history).run =
      (fixupSource8 data (refs.map history) read low hot tree root scratch paths).run := by
  have hpost (cursor : Nat) (h : Fin cursor → Bool) :
      (((eraseNetwork n (hotNetwork8 low hot) cursor).append
        (literalProgram [.X (hot 0)])).instantiate read h).run =
      ((eraseNetworkSource (hotNetwork8 low hot)).seq (.unitary [.X (hot 0)] .done)).run := by
    rw [append_run_fixed _ _ _ _ _ (fun h => literalProgram_run [.X (hot 0)] read h),
      AdaptiveCircuit.run_seq, eraseNetwork_source, ← AdaptiveCircuit.run_seq]
  have htail (cursor : Nat) (h : Fin cursor → Bool) :
      (((literalProgram (Circuit.adjoint ((hotBank8 hot).map Gate.H))).append
        (castFinish (f := cursor + 255) (by simp [hotNetwork_length8])
          ((eraseNetwork n (hotNetwork8 low hot) cursor).append
            (literalProgram [.X (hot 0)])))).instantiate read h).run =
      (AdaptiveCircuit.unitary (Circuit.adjoint ((hotBank8 hot).map Gate.H))
        ((eraseNetworkSource (hotNetwork8 low hot)).seq (.unitary [.X (hot 0)] .done))).run := by
    rw [literalProgram_append_run]
    apply unitary_run_congr
    rw [castFinish_instantiate, hpost]
  have hsource : fixupSource8 data (refs.map history) read low hot tree root scratch paths =
      .unitary (hotPrepare8 low hot) (.unitary ((hotBank8 hot).map Gate.H)
        ((recordLookupSource (logicalPorts8 data (refs.map history) hot) scratch read boolHistory
          (recordUnaryOps tree root paths)).seq
          (.unitary (Circuit.adjoint ((hotBank8 hot).map Gate.H))
            ((eraseNetworkSource (hotNetwork8 low hot)).seq (.unitary [.X (hot 0)] .done))))) := by
    simp only [fixupSource8, phaseLookupSource, adaptive_seq_assoc, AdaptiveCircuit.seq]
  rw [hsource, fixupProgram8, literalProgram_append_run]
  apply unitary_run_congr
  rw [literalProgram_append_run]
  apply unitary_run_congr
  rw [append_run_fixed _ _ _ _ _ (fun h => htail _ h),
    AdaptiveCircuit.run_seq, recordLookup_run]
  have hh : historyPrefix (Nat.le_refl base) history = history := rfl
  rw [hh, recordSource_resolve8, ← AdaptiveCircuit.run_seq]

theorem measuredClear_run8 {n : Nat} (data : List (ClearPort n))
    (read : ConstantBit n → Bool) (low : Fin 8 → Wire) (hot : Fin 256 → Wire)
    (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire) (start : Nat) (history : Fin start → Bool) :
    ((measuredClear8 data low hot tree root scratch paths start).instantiate read history).run =
      (measureResetThen (data.map ClearPort.target)
        (fun outcomes => fixupSource8 data outcomes read low hot tree root scratch paths)).run := by
  rw [measuredClear8, castFinish_instantiate,
    MeasuredClear.measureThen_run _ (fun outcomes => fixupSource8 data outcomes read low hot tree root scratch paths) read
      (by intro cursor refs h; rw [castFinish_instantiate, fixupProgram_run8])]
  rfl

theorem fixupSource_wellFormed8 {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (read : ConstantBit n → Bool) (low : Fin 8 → Wire) (hot : Fin 256 → Wire)
    (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire)
    (hl : tree.Layout root paths) (hi : Function.Injective hot) (hdlow : ∀ i j, low i ≠ hot j)
    (hs : scratch ∉ root :: tree.indexWires.dedup ++ paths) (hshot : scratch ∉ hotBank8 hot) :
    (fixupSource8 data outcomes read low hot tree root scratch paths).WellFormed := by
  rw [fixupSource8]
  apply AdaptiveCircuit.WellFormed.seq
  · refine ⟨?_, trivial⟩
    rw [hotPrepare8, circuitWellFormed_append]
    exact ⟨by simp [CircuitWellFormed, Gate.WellFormed],
      ParityBank.parityNet_wellFormed 8 (lowN8 low) (hotNat8 hot) (hotLayout_of8 low hot hi hdlow) 8 le_rfl⟩
  · apply AdaptiveCircuit.WellFormed.seq
    · apply phaseLookupSource_wellFormed _ _ _ _ _ _ _ _ hl hs
      intro p hp he
      exact hshot (he.symm ▸ phasePorts_targets8 hot _ p hp)
    · apply AdaptiveCircuit.WellFormed.seq
      · exact eraseNetworkSource_wellFormed _ (hotNetwork_physical8 low hot hi hdlow)
      · exact ⟨by simp [CircuitWellFormed, Gate.WellFormed], trivial⟩

theorem hotPrepare_tCount8 (low : Fin 8 → Wire) (hot : Fin 256 → Wire) :
    ShorECDLP.tCount (hotPrepare8 low hot)=1729 := by
  have h := ParityBank.parityNet_tCount (lowN8 low) (hotNat8 hot) 8
  rw [hotPrepare8,ShorECDLP.tCount_append]
  change 0+ShorECDLP.tCount (ParityBank.parityNet (lowN8 low) (hotNat8 hot) 8)=1729
  norm_num at h
  omega

theorem hotPrepare_length8 (low : Fin 8 → Wire) (hot : Fin 256 → Wire) :
    (hotPrepare8 low hot).length=758 := by
  have h := ParityBank.parityNet_length (lowN8 low) (hotNat8 hot) 8
  rw [hotPrepare8,List.length_append]
  simp only [List.length_cons,List.length_nil]
  norm_num at h
  omega

theorem phasePorts_length8 {n base : Nat} (hot : Fin 256 → Wire) (items : List (ClearPort n × Fin base)) :
    (phasePorts8 hot items).length = 256 * items.length := by
  induction items with
  | nil => rfl
  | cons item items ih =>
    rw [phasePorts_cons8, List.length_append, ih]
    simp only [phasePorts8, List.flatMap_cons, List.flatMap_nil, List.length_append,
      List.length_ofFn, List.length_nil, List.length_cons]
    omega

theorem fixupProgram_tCount8 {n base : Nat} (data : List (ClearPort n)) (refs : List (Fin base))
    (low : Fin 8 → Wire) (hot : Fin 256 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire) (hl : tree.Layout root paths)
    (read : ConstantBit n → Bool) (history : Fin base → Bool) :
    ((fixupProgram8 data refs low hot tree root scratch paths).instantiate read history).tCount =
      7 * tree.internalNodes + 1729 := by
  have hpost (cursor : Nat) (h : Fin cursor → Bool) :
      (((eraseNetwork n (hotNetwork8 low hot) cursor).append
        (literalProgram [.X (hot 0)])).instantiate read h).tCount = 0 := by
    rw [append_tCount_fixed _ _ _ _ _ (fun h => literalProgram_tCount [.X (hot 0)] read h), eraseNetwork_tCount]
    rfl
  have htail (cursor : Nat) (h : Fin cursor → Bool) :
      (((literalProgram (Circuit.adjoint ((hotBank8 hot).map Gate.H))).append
        (castFinish (f := cursor + 255) (by simp [hotNetwork_length8])
          ((eraseNetwork n (hotNetwork8 low hot) cursor).append
            (literalProgram [.X (hot 0)])))).instantiate read h).tCount = 0 := by
    rw [literalProgram_append_tCount, castFinish_instantiate, hpost, ShorECDLP.tCount_adjoint, hadamards_tCount]
  simp only [fixupProgram8, literalProgram_append_tCount]
  rw [append_tCount_fixed _ _ _ _ _ (fun h => htail _ h), recordLookup_tCount,
    (recordUnary_counts tree root paths hl 0).2.1, hotPrepare_tCount8, hadamards_tCount]
  omega

theorem measuredClear_tCount8 {n : Nat} (data : List (ClearPort n))
    (low : Fin 8 → Wire) (hot : Fin 256 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire) (hl : tree.Layout root paths)
    (read : ConstantBit n → Bool) (start : Nat) (history : Fin start → Bool) :
    ((measuredClear8 data low hot tree root scratch paths start).instantiate read history).tCount =
      7 * (tree.internalNodes + 247) := by
  rw [measuredClear8, castFinish_instantiate, measureThen_tCount _ read (by
    intro cursor refs h
    rw [castFinish_instantiate, fixupProgram_tCount8 data refs low hot tree root scratch paths hl])]
  omega

theorem fixupProgram_slots8 {n base : Nat} (data : List (ClearPort n)) (refs : List (Fin base))
    (low : Fin 8 → Wire) (hot : Fin 256 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire) (hl : tree.Layout root paths) :
    (fixupProgram8 data refs low hot tree root scratch paths).gateSlots =
      1024 * min data.length refs.length * tree.leaves + 10 * tree.internalNodes + 2291 := by
  simp only [fixupProgram8, Straight.gateSlots_append, literalProgram_slots, castFinish_gateSlots]
  rw [recordLookup_slots, (recordUnary_counts tree root paths hl _).2.2, eraseNetwork_slots]
  simp only [phasePorts_length8, List.length_zip, hotPrepare_length8, hotBank8,
    List.length_ofFn, List.length_map, Circuit.adjoint, List.length_reverse,
    hotNetwork_length8, List.length_cons, List.length_nil]
  ring

theorem measuredClear_slots8 {n : Nat} (data : List (ClearPort n))
    (low : Fin 8 → Wire) (hot : Fin 256 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire) (hl : tree.Layout root paths) (start : Nat) :
    (measuredClear8 data low hot tree root scratch paths start).gateSlots =
      1024 * data.length * tree.leaves + 10 * tree.internalNodes + 2291 := by
  rw [measuredClear8, castFinish_gateSlots, measureThen_slots _
    (fun k => 1024 * min data.length k * tree.leaves + 10 * tree.internalNodes + 2291)
    (by intro cursor refs; rw [castFinish_gateSlots, fixupProgram_slots8 data refs low hot tree root scratch paths hl])]
  simp

/-- Unlike the seven- and nine-bit instances the scratch wire is not required to be a cleared
target: `mixedCircuit` uses it as a dirty ancilla, so it is listed separately. -/
def clearSupport8 {n : Nat} (data : List (ClearPort n)) (low : Fin 8 → Wire) (hot : Fin 256 → Wire)
    (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire) : List Wire :=
  data.map ClearPort.target ++ List.ofFn low ++ hotBank8 hot ++ (root :: tree.indexWires.dedup ++ paths) ++ [scratch]

theorem hotNetwork_within8 (low : Fin 8 → Wire) (hot : Fin 256 → Wire) (S : List Wire)
    (hl : ∀ i, low i ∈ S) (hh : ∀ i, hot i ∈ S) :
    ∀ c ∈ hotNetwork8 low hot, c.bit ∈ S ∧ c.parent ∈ S ∧ c.child ∈ S := by
  intro c hc
  obtain ⟨j, x, y, rfl, _⟩ := mem_hotNetwork8 low hot c hc
  exact ⟨hl _, hh _, hh _⟩

theorem hotPrepare_within8 (low : Fin 8 → Wire) (hot : Fin 256 → Wire) (S : List Wire)
    (hl : ∀ i, low i ∈ S) (hh : ∀ i, hot i ∈ S) : circuitWires (hotPrepare8 low hot) ⊆ S := by
  rw [hotPrepare8, circuitWires_append]
  exact List.append_subset.mpr ⟨by simpa [circuitWires, gateWires] using hh 0,
    ParityBank.parityNet_within 8 (lowN8 low) (hotNat8 hot) 8 le_rfl S
      (by intro j hj; simpa [lowN8,hj] using hl ⟨j,hj⟩)
      (by
        intro x hx
        have hx' : x<256 := by simpa using hx
        simpa [hotNat8,hx'] using hh ⟨x,hx'⟩)⟩

theorem fixupProgram_within8 {n base : Nat} (data : List (ClearPort n)) (refs : List (Fin base))
    (low : Fin 8 → Wire) (hot : Fin 256 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths S : List Wire)
    (hr : root ∈ S) (hs : scratch ∈ S) (hl : ∀ i, low i ∈ S) (hh : ∀ i, hot i ∈ S)
    (hi : tree.indexWires ⊆ S) (ha : paths ⊆ S) :
    NaiveChallenge.straightWires (fixupProgram8 data refs low hot tree root scratch paths) ⊆ S := by
  have hb : hotBank8 hot ⊆ S := by
    intro w hw
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
    exact hh i
  unfold fixupProgram8
  apply static_within_append
  · rw [literal_static]
    exact hotPrepare_within8 low hot S hl hh
  · apply static_within_append
    · rw [literal_static, hadamards_wires]
      exact hb
    · apply static_within_append
      · rw [recordLookup_static]
        apply recordWireList_within
        exact recordUnary_within _ scratch tree root paths S hr hs hi ha
          (fun p hp => hb (phasePorts_targets8 hot _ p hp))
      · apply static_within_append
        · rw [literal_static, hadamards_adjoint_wires]
          intro w hw
          exact hb (List.mem_reverse.mp hw)
        · rw [static_cast]
          apply static_within_append (eraseNetwork_within n _ _ S (hotNetwork_within8 low hot S hl hh))
          rw [literal_static]
          simpa [circuitWires, gateWires] using hh 0

/-- The generic row reference is exactly the physical little-endian address. -/
theorem splitAddress_value8 (low : Fin 8 → Wire) (high : List Wire) (s : BasisState) :
    256 * (tableAddressTree high 0 1).routeLabel s + hotAddress8 low s =
      tableAddressValue ([lowN8 low 0, lowN8 low 1, lowN8 low 2, lowN8 low 3, lowN8 low 4, lowN8 low 5,
        lowN8 low 6, lowN8 low 7] ++ high) s := by
  simp only [tableAddressTree_route, zero_add, one_mul, List.cons_append, List.nil_append,
    tableAddressValue, hotAddress8, addrN]
  ring

/-- The measured data bank is available to the phase fixup after reset. -/
theorem fixupFactor_recycled8 {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (read : ConstantBit n → Bool) (low : Fin 8 → Wire) (hot : Fin 256 → Wire)
    (tree : UnaryActionTree) (root : Wire) (paths : List Wire)
    (hi : Function.Injective hot) (hdlow : ∀ i j, low i ≠ hot j)
    (hbank : (hotBank8 hot).Disjoint (root :: tree.indexWires.dedup ++ paths))
    (ha : ∀ w ∈ root :: List.ofFn low ++ tree.indexWires.dedup ++ paths,
      w ∉ data.map ClearPort.target)
    (hh : ∀ i, hot i ∈ data.map ClearPort.target)
    (s : BasisState) (hs : Clean paths s ∧ LoadedClear8 data read low tree root s) :
    fixupFactor8 data outcomes read low hot tree root (clearRegister (data.map ClearPort.target) s) =
      registerXPhase (data.map ClearPort.target) outcomes s := by
  let cleared := clearRegister (data.map ClearPort.target) s
  let prepared := Classical.run (hotPrepare8 low hot) cleared
  have hhot : HotClean8 hot cleared := by
    intro i
    change clearRegister (data.map ClearPort.target) s (hot i) = false
    exact clearRegister_clean _ s _ (hh i)
  have hlow : ∀ i, cleared (low i) = s (low i) := by
    intro i
    have hw : low i ∈ List.ofFn low := List.mem_ofFn.mpr ⟨i, rfl⟩
    exact clearRegister_frame _ _ _ (ha _ (by simp only [List.mem_cons, List.mem_append, hw, or_true, true_or]))
  have haddr : hotAddress8 low cleared = hotAddress8 low s :=
    addrN_congr _ _ _ 8 (fun j hj => by simp only [lowN8, hj, dite_true]; exact hlow _)
  have hframe (w : Wire) (hw : w ∈ root :: tree.indexWires.dedup ++ paths) : prepared w = s w := by
    change Classical.run (hotPrepare8 low hot) cleared w = s w
    rw [hotPrepare_frame8 low hot cleared w (by
      intro i he
      exact List.disjoint_left.mp hbank (List.mem_ofFn.mpr ⟨i, he.symm⟩) hw)]
    apply clearRegister_frame
    apply ha
    simp only [List.mem_cons, List.mem_append] at hw ⊢
    tauto
  have hroute : tree.routeLabel prepared = tree.routeLabel s := by
    apply tree.routeLabel_congr prepared s
    intro w hw
    exact hframe w (by simp [hw])
  let selected : Fin 256 := ⟨hotAddress8 low s, hotAddress_bound8 low s⟩
  apply phaseFactor_loaded8 data outcomes read hot tree root s prepared selected
  · intro i
    simpa only [Fin.ext_iff, haddr] using hotPrepare_marker8 low hot hi hdlow cleared hhot i
  · intro p hp
    rw [hframe root (by simp), hroute]
    exact hs.2 p hp

theorem measuredClear_recycled_coherent8 {n : Nat} (data : List (ClearPort n))
    (read : ConstantBit n → Bool) (low : Fin 8 → Wire) (hot : Fin 256 → Wire)
    (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire)
    (hl : tree.Layout root paths) (hi : Function.Injective hot) (hdlow : ∀ i j, low i ≠ hot j)
    (hbank : (hotBank8 hot).Disjoint (root :: tree.indexWires.dedup ++ paths))
    (hs : scratch ∉ root :: tree.indexWires.dedup ++ paths) (hshot : scratch ∉ hotBank8 hot)
    (hn : (data.map ClearPort.target).Nodup)
    (ha : ∀ w ∈ root :: List.ofFn low ++ tree.indexWires.dedup ++ paths,
      w ∉ data.map ClearPort.target)
    (hh : ∀ i, hot i ∈ data.map ClearPort.target)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((measuredClear8 data low hot tree root scratch paths start).instantiate read history)
      (Finsupp.lmapDomain ℂ ℂ (clearRegister (data.map ClearPort.target)))
      (fun s => Clean paths s ∧ LoadedClear8 data read low tree root s) := by
  unfold CoherentlyImplementsOn
  rw [measuredClear_run8]
  apply measureResetThen_coherent (data.map ClearPort.target)
    (fun outcomes => fixupSource8 data outcomes read low hot tree root scratch paths)
    (fun outcomes => basisIdeal id (fixupFactor8 data outcomes read low hot tree root))
    (fun _ s => HotClean8 hot s ∧ Clean paths s)
    (fun s => Clean paths s ∧ LoadedClear8 data read low tree root s)
    (clearRegister (data.map ClearPort.target)) hn (witness := zeroBasisState)
  · intro outcomes hout
    exact fixupSource_wellFormed8 data outcomes read low hot tree root scratch paths hl hi hdlow hs hshot
  · intro outcomes
    exact fixupSource_coherent8 data outcomes read low hot tree root scratch paths hl hi hdlow hbank hs hshot
  · intro outcomes hout s hvalid
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i
      exact clearRegister_clean _ s _ (hh i)
    · intro w hw
      rw [clearRegister_frame _ _ _ (ha w (by simp [hw]))]
      exact hvalid.1 w hw
    · rw [basisIdeal_ket, fixupFactor_recycled8 data outcomes read low hot tree root paths hi hdlow hbank ha hh s hvalid]
      rfl
  · simp [Clean, LoadedClear8, zeroBasisState]

end
end ShorECDLP.Entrant.MeasuredClear

namespace ShorECDLP.Entrant.MeasuredClear
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

theorem fixupProgram_wellFormed8 {n base} (data : List (ClearPort n)) (refs : List (Fin base))
    (low : Fin 8 → Wire) (hot : Fin 256 → Wire) (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire)
    (hl : tree.Layout root paths) (hi : Function.Injective hot) (hdlow : ∀ i j, low i ≠ hot j)
    (hs : scratch ∉ root :: tree.indexWires.dedup ++ paths) (hshot : scratch ∉ hotBank8 hot) :
    (fixupProgram8 data refs low hot tree root scratch paths).WellFormed := by
  have hp := hotNetwork_physical8 low hot hi hdlow
  have hH (ws : List Wire) : CircuitWellFormed (ws.map Gate.H) := by
    intro g hg; obtain ⟨w,_,rfl⟩ := List.mem_map.mp hg; trivial
  unfold fixupProgram8
  apply straight_append_wellFormed
  · apply literalProgram_wellFormed
    rw [hotPrepare8,circuitWellFormed_append]
    exact ⟨by simp [CircuitWellFormed,Gate.WellFormed],ParityBank.parityNet_wellFormed 8 (lowN8 low) (hotNat8 hot) (hotLayout_of8 low hot hi hdlow) 8 le_rfl⟩
  · apply straight_append_wellFormed
    · exact literalProgram_wellFormed _ (hH _)
    · apply straight_append_wellFormed
      · apply recordLookupProgram_wellFormed
        apply recordUnary_physical _ _ _ _ _ hl
        intro row c hc
        refine ⟨?_,?_⟩
        · intro he; apply hs; subst c; simp only [List.mem_cons,List.mem_append] at hc ⊢; tauto
        · intro p hpm he
          exact hshot (he.symm ▸ phasePorts_targets8 hot _ p hpm)
      · apply straight_append_wellFormed
        · exact literalProgram_wellFormed _ ((circuitWellFormed_adjoint _).mpr (hH _))
        · rw [castFinish_wellFormed]
          exact straight_append_wellFormed _ _ (eraseNetwork_wellFormed n _ hp _)
            (literalProgram_wellFormed _ (by simp [CircuitWellFormed,Gate.WellFormed]))

theorem measuredClear_wellFormed8 {n} (data : List (ClearPort n))
    (low : Fin 8 → Wire) (hot : Fin 256 → Wire) (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire)
    (hl : tree.Layout root paths) (hi : Function.Injective hot) (hdlow : ∀ i j, low i ≠ hot j)
    (hs : scratch ∉ root :: tree.indexWires.dedup ++ paths) (hshot : scratch ∉ hotBank8 hot) (start : Nat) :
    (measuredClear8 data low hot tree root scratch paths start).WellFormed := by
  rw [measuredClear8,castFinish_wellFormed]
  apply measureThen_wellFormed
  intro cursor refs
  rw [castFinish_wellFormed]
  exact fixupProgram_wellFormed8 data refs low hot tree root scratch paths hl hi hdlow hs hshot

open AndGadget in
 theorem fixupProgram_residue8 {n base} (data : List (ClearPort n)) (refs : List (Fin base))
    (low : Fin 8 → Wire) (hot : Fin 256 → Wire) (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire) :
    residue (fixupProgram8 data refs low hot tree root scratch paths) = 0 := by
  unfold fixupProgram8
  rw [residue_append,residue_literal_HPFree _ (hotPrepare_hp8 low hot)]
  simp only [residue_append,residue_literal,residue_cast,eraseNetwork_residue,
    recordLookup_residue _ _ _ _ _ (recordUnary_phaseFree tree root paths),Nat.zero_add]
  simp [List.map_map,Function.comp_def,primitivePhaseCost,Circuit.adjoint,List.map_reverse,Gate.adjoint]

open AndGadget in
 theorem measuredClear_residue8 {n} (data : List (ClearPort n))
    (low : Fin 8 → Wire) (hot : Fin 256 → Wire) (tree : UnaryActionTree) (root scratch : Wire) (paths : List Wire) (start : Nat) :
    residue (measuredClear8 data low hot tree root scratch paths start) = 0 := by
  rw [measuredClear8,residue_cast]
  apply measureThen_residue
  intro cursor refs
  rw [residue_cast]
  exact fixupProgram_residue8 data refs low hot tree root scratch paths

theorem measuredClear_static8 {n : Nat} (data : List (ClearPort n))
    (low : Fin 8 → Wire) (hot : Fin 256 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire) (start : Nat) :
    NaiveChallenge.straightWires (measuredClear8 data low hot tree root scratch paths start) ⊆
      clearSupport8 data low hot tree root scratch paths := by
  rw [measuredClear8, static_cast]
  apply measureThen_within _ _ (by
    intro cursor refs
    rw [static_cast]
    apply fixupProgram_within8
    · simp [clearSupport8]
    · simp [clearSupport8]
    · intro i
      have hm : low i ∈ List.ofFn low := List.mem_ofFn.mpr ⟨i, rfl⟩
      simp only [clearSupport8, List.mem_append, List.mem_cons, hm, true_or, or_true]
    · intro i
      have hm : hot i ∈ hotBank8 hot := List.mem_ofFn.mpr ⟨i, rfl⟩
      simp only [clearSupport8, List.mem_append, List.mem_cons, hm, true_or, or_true]
    · intro w hw
      simp [clearSupport8, hw]
    · intro w hw
      simp [clearSupport8, hw])
  intro w hw
  simp [clearSupport8, hw]

end
end ShorECDLP.Entrant.MeasuredClear

/-! ### Deferred phase fixups: generic measurement lemma and fixup-factor algebra -/

namespace ShorECDLP.Entrant.MeasuredClear
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

theorem normSq_resetMagnitude (m : Nat) :
    Complex.normSq (registerXResetMagnitude m) = (1 / 2 : ℝ) ^ m := by
  rw [registerXResetMagnitude, map_pow, Complex.normSq_ofReal, ← mul_inv,
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem registerXPhase_square (targets : List Wire) (outcomes : List Bool) (s : BasisState) :
    registerXPhase targets outcomes s * registerXPhase targets outcomes s = 1 := by
  induction targets generalizing outcomes with
  | nil => simp [registerXPhase]
  | cons t ts ih =>
    cases outcomes with
    | nil => simp [registerXPhase]
    | cons o os =>
      rw [registerXPhase, mul_mul_mul_comm, ih]
      cases o <;> cases s t <;> norm_num

/-- A register measure/reset followed by an outcome-dependent continuation, in simulation form:
every continuation branch, prefixed by the register's Kraus map, satisfies `P` with coefficient
`2^(-m/2)` times its own input-independent coefficient. -/
theorem measureResetThen_sim (targets : List Wire) (next : List Bool → AdaptiveCircuit)
    (Q : List Bool → InstrumentBranch → ℂ → Prop) (P : InstrumentBranch → ℂ → Prop)
    (hn : ∀ o, o.length = targets.length →
      ∃ cs : List ℂ, List.Forall₂ (Q o) (next o).run cs ∧ (cs.map Complex.normSq).sum = 1)
    (hlift : ∀ o, o.length = targets.length → ∀ b c, Q o b c →
      P ⟨o ++ b.history, b.kraus.comp (xResetRegisterKraus targets o)⟩
        (registerXResetMagnitude targets.length * c)) :
    ∃ cs : List ℂ, List.Forall₂ P (measureResetThen targets next).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  have hrun : (measureResetThen targets next).run =
      (boolTranscripts targets.length).flatMap (fun o => (next o).run.map
        (fun b => (⟨o ++ b.history, b.kraus.comp (xResetRegisterKraus targets o)⟩ : InstrumentBranch))) :=
    run_measureResetThen targets next
  rw [hrun]
  have key : ∀ outs : List (List Bool), (∀ o ∈ outs, o.length = targets.length) →
      ∃ cs : List ℂ, List.Forall₂ P (outs.flatMap (fun o => (next o).run.map
          (fun b => (⟨o ++ b.history, b.kraus.comp (xResetRegisterKraus targets o)⟩ : InstrumentBranch)))) cs ∧
        (cs.map Complex.normSq).sum =
          (outs.length : ℝ) * Complex.normSq (registerXResetMagnitude targets.length) := by
    intro outs
    induction outs with
    | nil => intro _; exact ⟨[], .nil, by simp⟩
    | cons o os ih =>
      intro hall
      obtain ⟨c1, h1, m1⟩ := hn o (hall o (by simp))
      obtain ⟨c2, h2, m2⟩ := ih (fun v hv => hall v (by simp [hv]))
      refine ⟨c1.map (fun c => registerXResetMagnitude targets.length * c) ++ c2, ?_, ?_⟩
      · rw [List.flatMap_cons]
        apply List.rel_append _ h2
        apply List.forall₂_map_left_iff.mpr
        apply List.forall₂_map_right_iff.mpr
        exact h1.imp (fun b c hb => hlift o (hall o (by simp)) b c hb)
      · rw [List.map_append, List.sum_append, m2, List.map_map]
        have hm : (c1.map (Complex.normSq ∘ fun c => registerXResetMagnitude targets.length * c)) =
            c1.map (fun c => Complex.normSq (registerXResetMagnitude targets.length) * Complex.normSq c) := by
          apply List.map_congr_left
          intro c _
          simp [Complex.normSq_mul]
        rw [hm, List.sum_map_mul_left, m1, List.length_cons]
        push_cast
        ring
  obtain ⟨cs, h, m⟩ := key _ (fun o ho => mem_boolTranscripts_length ho)
  refine ⟨cs, h, ?_⟩
  rw [m, boolTranscripts_length, normSq_resetMagnitude, Nat.cast_pow, ← mul_pow]
  norm_num

theorem fixupFactor8_append {n : Nat} (d1 d2 : List (ClearPort n)) (o1 o2 : List Bool)
    (h : o1.length = d1.length) (read : ConstantBit n → Bool) (low : Fin 8 → Wire) (hot : Fin 256 → Wire)
    (tree : UnaryActionTree) (root : Wire) (s : BasisState) :
    fixupFactor8 (d1 ++ d2) (o1 ++ o2) read low hot tree root s =
      fixupFactor8 d1 o1 read low hot tree root s * fixupFactor8 d2 o2 read low hot tree root s := by
  have hz : (d1 ++ d2).zip ((o1 ++ o2).map boolRecord) = d1.zip (o1.map boolRecord) ++ d2.zip (o2.map boolRecord) := by
    rw [List.map_append]
    exact List.zip_append (by simp [h])
  simp only [fixupFactor8, phaseLookupFactor, logicalPorts8, hz, phasePorts8, List.flatMap_append,
    recordTargets_append, xorPhase_append]

/-- A deferred clear's phase, evaluated at a later state whose root and address agree. -/
theorem fixupFactor8_loaded {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (read : ConstantBit n → Bool) (low : Fin 8 → Wire) (hot : Fin 256 → Wire)
    (tree : UnaryActionTree) (root : Wire) (paths : List Wire)
    (hi : Function.Injective hot) (hdlow : ∀ i j, low i ≠ hot j)
    (hbank : (hotBank8 hot).Disjoint (root :: tree.indexWires.dedup ++ paths))
    (t u : BasisState) (hhot : HotClean8 hot t)
    (hw : ∀ p ∈ data, u p.target =
      (t root && decide (read (p.ref (256 * tree.routeLabel t + hotAddress8 low t)) = p.value))) :
    fixupFactor8 data outcomes read low hot tree root t =
      registerXPhase (data.map ClearPort.target) outcomes u := by
  let prepared := Classical.run (hotPrepare8 low hot) t
  have hframe (w : Wire) (hw : w ∈ root :: tree.indexWires.dedup ++ paths) : prepared w = t w :=
    hotPrepare_frame8 low hot t w (by
      intro i he
      exact List.disjoint_left.mp hbank (List.mem_ofFn.mpr ⟨i, he.symm⟩) hw)
  have hroute : tree.routeLabel prepared = tree.routeLabel t := by
    apply tree.routeLabel_congr prepared t
    intro w hw
    exact hframe w (by simp [hw])
  let selected : Fin 256 := ⟨hotAddress8 low t, hotAddress_bound8 low t⟩
  apply phaseFactor_loaded8 data outcomes read hot tree root u prepared selected
  · intro i
    simpa only [Fin.ext_iff] using hotPrepare_marker8 low hot hi hdlow t hhot i
  · intro p hp
    rw [hframe root (by simp), hroute]
    exact hw p hp

end
end ShorECDLP.Entrant.MeasuredClear

/-! ### The eight-bit clear on a sixteen-bit window bank -/

namespace ShorECDLP.Entrant.WideBank8
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-- The eight low address bits `855..862`. -/
def low8 (i : Fin 8) : Wire := 855 + i.val

theorem low8_lt (i : Fin 8) : low8 i < 863 := by
  have hi := i.isLt
  show 855 + i.val < 863
  omega

/-- The phase bank of a site: its first 256 cleared targets. -/
def hot8 {n} (site : MaskedSite n) : Fin 256 → Wire := fun i => scratch site + i.val

/-- The phase scratch of every eight-bit clear: the ninth wire of the old clear path bank. -/
def scratch8 : Wire := 14840

theorem kind_hot8 {n} (site : MaskedSite n) (hk : SiteKind site) (i : Fin 256) :
    hot8 site i ∈ portTargets site.ports := by
  have hi := i.isLt
  show scratch site + i.val ∈ portTargets site.ports
  rcases hk with ⟨ht,-⟩ | ⟨ht,-⟩ | ⟨ht,-⟩ | ⟨ht,-⟩ | ⟨ht,-⟩ | ⟨ht,-⟩
  · have hs : scratch site = 14115 := by rw [scratch,ht]; decide +kernel
    rw [hs, ht, List.mem_range'_1]
    dsimp only [Wire] at *
    omega
  · have hs : scratch site = 14373 := by rw [scratch,ht]; exact scrWires_head
    rw [hs, ht, scrWires_eq]
    simp only [List.mem_append, List.mem_cons, List.mem_range'_1, List.cons_append, List.not_mem_nil, or_false]
    dsimp only [Wire] at *
    omega
  · have hs : scratch site = 14115 := by rw [scratch,ht]; decide +kernel
    rw [hs, ht]
    simp only [List.mem_append, List.mem_range'_1]
    dsimp only [Wire] at *
    omega
  · have hs : scratch site = 14373 := by rw [scratch,ht,scrAllWires_eq,scrWires_eq]; rfl
    rw [hs, ht, scrAllWires_eq, scrWires_eq]
    simp only [List.mem_append, List.mem_cons, List.mem_range'_1, List.cons_append, List.not_mem_nil, or_false]
    dsimp only [Wire] at *
    omega
  · have hs : scratch site = 14115 := by rw [scratch,ht]; decide +kernel
    rw [hs, ht, List.mem_range'_1]
    dsimp only [Wire] at *
    omega
  · have hs : scratch site = 14374 := by rw [scratch,ht]; rfl
    rw [hs, ht]
    simp only [List.mem_append, List.mem_cons, List.mem_range'_1]
    dsimp only [Wire] at *
    omega

theorem hot8_injective {n} (site : MaskedSite n) : Function.Injective (hot8 site) := by
  intro i j he
  apply Fin.ext
  simp only [hot8] at he
  dsimp only [Wire] at he
  omega

structure BankOK (B : PathShare.Bank) : Prop where
  split : ∀ s : BasisState, 256 * (tableAddressTree B.high 0 1).routeLabel s + MeasuredClear.hotAddress8 low8 s =
    tableAddressValue B.bits s
  high : ∀ w ∈ B.high, 862 ≤ w ∧ w < 10000
  index : (tableAddressTree B.high 0 1).indexWires.dedup = B.high
  nodup : (B.high ++ B.hp).Nodup
  len : B.high.length ≤ B.hp.length
  sub : ∀ w ∈ B.hp, w ∈ B.paths
  out : ∀ w ∈ B.hp, 871 ≤ w
  bitsLen : B.bits.length ≤ B.paths.length
  scr : scratch8 ∈ B.paths ∧ scratch8 ∉ B.hp

-- WideSigned.Bank.clear_coherent_bank at eight low bits, with the dirty scratch `14840`.
theorem clear_coherent_bank {n} (read : ConstantBit n → Bool) (site : MaskedSite n) (hk : SiteKind site)
    (bitsW H P : List Wire)
    (hsplit : ∀ s : BasisState, 256 * (tableAddressTree H 0 1).routeLabel s + MeasuredClear.hotAddress8 low8 s =
      tableAddressValue bitsW s)
    (hH : ∀ w ∈ H, 862 ≤ w ∧ w < 10000) (hP : ∀ w ∈ P, 871 ≤ w ∧ w ∉ portTargets site.ports)
    (hPg : site.guard ∉ P) (hindex : (tableAddressTree H 0 1).indexWires.dedup = H)
    (hnd : (H ++ P).Nodup) (hhl : H.length ≤ P.length)
    (hsP : scratch8 ∉ P) (hsT : scratch8 ∉ portTargets site.ports)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((MeasuredClear.measuredClear8 (clearData site.ports) low8 (hot8 site)
        (tableAddressTree H 0 1) site.guard scratch8 P start).instantiate read history)
      (Finsupp.lmapDomain ℂ ℂ (clearRegister (portTargets site.ports)))
      (fun s => Clean P s ∧
        ∀ p ∈ site.ports, s p.target = (s site.guard && decide (read (p.ref (tableAddressValue bitsW s)) = p.value))) := by
  obtain ⟨hn,hbd,-,-,-,hg,-⟩ := kind_facts site hk
  have hmem := kind_hot8 site hk
  have hgl : site.guard < 14115 := by rcases hg with e | e <;> rw [e] <;> decide
  have notT : ∀ w ∈ site.guard :: List.ofFn low8 ++ H ++ P, w ∉ portTargets site.ports := by
    intro w hw ht
    have h2 := (hbd w ht).1
    simp only [List.mem_append,List.mem_cons] at hw
    rcases hw with ((h | h) | h) | h
    · rw [h] at h2; dsimp only [Wire] at *; omega
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
      have := low8_lt i
      dsimp only [Wire] at *; omega
    · have := hH w h
      dsimp only [Wire] at *; omega
    · exact (hP w h).2 ht
  have hgH : site.guard ∉ H := by
    intro h; have := hH _ h; dsimp only [Wire] at *; omega
  have hnodup : (site.guard :: H ++ P).Nodup := by
    rw [List.cons_append, List.nodup_cons]
    refine ⟨fun h => ?_, hnd⟩
    rcases List.mem_append.mp h with h | h
    · exact hgH h
    · exact hPg h
  have hl := tableAddressTree_layout H P site.guard 0 1 hhl hnodup
  have hc := MeasuredClear.measuredClear_recycled_coherent8 (clearData site.ports) read low8 (hot8 site)
    (tableAddressTree H 0 1) site.guard scratch8 P hl (hot8_injective site)
    (by
      intro i j he
      have h1 := (hbd _ (hmem j)).1
      have h2 := low8_lt i
      rw [← he] at h1
      dsimp only [Wire] at *
      omega)
    (by
      apply List.disjoint_left.mpr
      intro w hw hm
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
      rw [hindex] at hm
      exact notT _ (by simp only [List.mem_append,List.mem_cons] at hm ⊢; tauto) (hmem i))
    (by
      rw [hindex]
      intro hm
      simp only [List.mem_cons, List.mem_append] at hm
      rcases hm with (h | h) | h
      · have hne : site.guard ≠ scratch8 := by rcases hg with e | e <;> rw [e] <;> decide
        exact hne h.symm
      · exact absurd (hH _ h).2 (by decide)
      · exact hsP h)
    (by
      intro hm
      obtain ⟨i,hi⟩ := List.mem_ofFn.mp hm
      exact hsT (hi ▸ hmem i))
    (by simpa using hn)
    (by
      rw [clearData_targets,hindex]
      intro w hw hm
      exact notT w hw hm)
    (by rw [clearData_targets]; exact hmem)
    start history
  simp only [clearData_targets] at hc
  obtain ⟨cs,aligned,mass⟩ := hc
  refine ⟨cs,aligned.imp ?_,mass⟩
  intro b c hb s hs
  apply hb s
  refine ⟨hs.1,?_⟩
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  simpa [MeasuredClear.LoadedClear8,clearData,hsplit] using hs.2 q hq

def clearP {n} (B : Bank) (site : MaskedSite n) (start : Nat) :=
  MeasuredClear.measuredClear8 (clearData site.ports) low8 (hot8 site) (tableAddressTree B.high 0 1)
    site.guard scratch8 B.hp start

def clearSourceP {n} (B : Bank) (read : ConstantBit n → Bool) (site : MaskedSite n) : AdaptiveCircuit :=
  (clearP B site 0).instantiate read Fin.elim0

theorem clearP_run {n} (B : Bank) (read : ConstantBit n → Bool) (site : MaskedSite n)
    (start : Nat) (history : Fin start → Bool) :
    ((clearP B site start).instantiate read history).run = (clearSourceP B read site).run := by
  simp only [clearP,clearSourceP,MeasuredClear.measuredClear_run8]

theorem scratch8_not_targets {n} (B : Bank) (hB : BankOK B) (site : MaskedSite n) (hg : SiteGeoP B site) :
    scratch8 ∉ portTargets site.ports := by
  have hlast := hg.placed (.lookup (some site.guard) site.ports) (by simp [MaskedSite.code])
  dsimp only [Placed] at hlast
  intro ht
  exact List.disjoint_left.mp hlast.2.2
    (show scratch8 ∈ windowRoot :: lookupRoot windowRoot (some site.guard) :: B.bits ++ B.paths by
      simp [hB.scr.1]) ht

theorem clearP_coherent {n} (read : ConstantBit n → Bool) (B : Bank) (hB : BankOK B)
    (site : MaskedSite n) (hg : SiteGeoP B site) (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((clearP B site start).instantiate read history)
      (Finsupp.lmapDomain ℂ ℂ (clearRegister (portTargets site.ports)))
      (fun s => Clean B.hp s ∧
        ∀ p ∈ site.ports, s p.target = (s site.guard && decide (read (p.ref (tableAddressValue B.bits s)) = p.value))) := by
  have hlast := hg.placed (.lookup (some site.guard) site.ports) (by simp [MaskedSite.code])
  dsimp only [Placed] at hlast
  unfold clearP
  refine clear_coherent_bank read site hg.kind B.bits B.high B.hp hB.split hB.high ?_ ?_ hB.index hB.nodup hB.len
    hB.scr.2 (scratch8_not_targets B hB site hg) start history
  · intro w hw
    refine ⟨hB.out w hw, fun ht => ?_⟩
    exact List.disjoint_left.mp hlast.2.2
      (show w ∈ windowRoot :: lookupRoot windowRoot (some site.guard) :: B.bits ++ B.paths by
        simp [hB.sub w hw]) ht
  · intro hg'
    have hn := hlast.1
    simp only [lookupRoot, Option.getD_some, List.cons_append, List.nodup_cons] at hn
    exact hn.1 (List.mem_append_right _ (hB.sub _ hg'))

theorem site_tree_nodup {n} (B : Bank) (hB : BankOK B) (site : MaskedSite n) (hg : SiteGeoP B site) :
    (site.guard :: B.high ++ B.hp).Nodup := by
  have hlast := hg.placed (.lookup (some site.guard) site.ports) (by simp [MaskedSite.code])
  dsimp only [Placed] at hlast
  have hn := hlast.1
  simp only [lookupRoot, Option.getD_some, List.cons_append, List.nodup_cons] at hn
  have hgl := (kind_facts site hg.kind).2.2.2.2.2.1
  rw [List.cons_append, List.nodup_cons]
  refine ⟨fun h => ?_, hB.nodup⟩
  rcases List.mem_append.mp h with h | h
  · have := hB.high _ h
    rcases hgl with e | e <;> rw [e] at this <;> dsimp only [Wire] at this <;> omega
  · exact hn.1 (List.mem_append_right _ (hB.sub _ h))

theorem geo_lay {n} (B : Bank) (hB : BankOK B) (b : Block n) (hg : BlockGeoP B b) : BlockLay B b := by
  cases b with
  | plain code =>
    have hg' : LitAvoid B.bits code := hg
    refine ⟨hB.bitsLen, ?_⟩
    intro c ps hm
    obtain ⟨j, hj, he⟩ := List.mem_map.mp hm
    obtain ⟨p, rfl, -⟩ := hg' j hj
    simp [normalizeWInstr] at he
  | masked site =>
    have hg' : SiteGeoP B site := hg
    have hp : ∀ i ∈ site.prefix, PlacedPair B.bits B.paths windowRoot i := by
      intro i hi; exact placed_implies_pair _ _ _ _ (hg'.placed i (List.mem_append_left _ hi))
    exact ⟨pair_layouts_of_placed _ _ _ _ hB.bitsLen (pair_placed_normalize _ _ _ _ hp),
      tableAddressTree_layout B.high B.hp site.guard 0 1 hB.len (site_tree_nodup B hB site hg')⟩

theorem clearP_wellFormed {n} (B : Bank) (hB : BankOK B) (site : MaskedSite n) (hg : SiteGeoP B site)
    (start : Nat) : (clearP B site start).WellFormed := by
  obtain ⟨-,hbd,-,-,-,hgl,-⟩ := kind_facts site hg.kind
  have hmem := kind_hot8 site hg.kind
  unfold clearP
  apply MeasuredClear.measuredClear_wellFormed8
  · exact tableAddressTree_layout B.high B.hp site.guard 0 1 hB.len (site_tree_nodup B hB site hg)
  · exact hot8_injective site
  · intro i j he
    have h1 := (hbd _ (hmem j)).1
    have h2 := low8_lt i
    rw [← he] at h1
    dsimp only [Wire] at *
    omega
  · rw [hB.index]
    intro hm
    simp only [List.mem_cons, List.mem_append] at hm
    rcases hm with (h | h) | h
    · have hne : site.guard ≠ scratch8 := by rcases hgl with e | e <;> rw [e] <;> decide
      exact hne h.symm
    · exact absurd (hB.high _ h).2 (by decide)
    · exact hB.scr.2 h
  · intro hm
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hm
    exact scratch8_not_targets B hB site hg (hi ▸ hmem i)

theorem clearP_tCount {n} (read : ConstantBit n → Bool) (B : Bank) (site : MaskedSite n)
    (hl : (tableAddressTree B.high 0 1).Layout site.guard B.hp) (start : Nat) (history : Fin start → Bool) :
    ((clearP B site start).instantiate read history).tCount =
      7 * ((tableAddressTree B.high 0 1).internalNodes + 247) := by
  unfold clearP
  exact MeasuredClear.measuredClear_tCount8 _ _ _ _ _ _ _ hl read start history

theorem clearP_support {n} (B : Bank) (hB : BankOK B) (site : MaskedSite n) (hk : SiteKind site)
    (S : List Wire) (hS : portTargets site.ports ⊆ S) (hgS : site.guard ∈ S) (hlow : ∀ i, low8 i ∈ S)
    (hhigh : B.high ⊆ S) (hpaths : B.paths ⊆ S) (start : Nat) :
    ChallengeMigration.straightWires (clearP B site start) ⊆ S := by
  have hmem := kind_hot8 site hk
  unfold clearP
  rw [support_agrees]
  apply List.Subset.trans (MeasuredClear.measuredClear_static8 _ _ _ _ _ _ _ start)
  intro w hw
  simp only [MeasuredClear.clearSupport8,clearData_targets,hB.index,MeasuredClear.hotBank8,
    List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,or_assoc] at hw
  rcases hw with hs | hl | hh | hr | hb | hp | hsc
  · exact hS hs
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hl
    exact hlow i
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hh
    exact hS (hmem i)
  · rw [hr]; exact hgS
  · exact hhigh hb
  · exact hpaths (hB.sub _ hp)
  · rw [hsc]; exact hpaths hB.scr.1

theorem clearP_residue {n} (B : Bank) (site : MaskedSite n) (start : Nat) :
    AndGadget.residue (clearP B site start) = 0 :=
  MeasuredClear.measuredClear_residue8 _ _ _ _ _ _ _ start

/-! #### Units on the eight-bit bank -/

def blockRecP2 {n} (B : Bank) : Block2 n → Nat
  | .plain code => codeRecords B.bits B.paths windowRoot (normalizeW code)
  | .unit u => codeRecords B.bits B.paths windowRoot (normalizeW u.pre) +
      u.clear.ports.length + (MeasuredClear.recordMeasurements
        (MeasuredClear.recordUnaryOps (tableAddressTree B.high 0 1) u.clear.guard B.hp)+255)

def blockProgP2 {n} (B : Bank) (b : Block2 n) (start : Nat) : Straight n start (start+blockRecP2 B b) :=
  match b with
  | .plain code => compile B.bits B.paths windowRoot (normalizeW code) start
  | .unit u => castFinish (by simp [blockRecP2,clearData]; omega)
      ((compile B.bits B.paths windowRoot (normalizeW u.pre) start).append
        (clearP B u.clear (start+codeRecords B.bits B.paths windowRoot (normalizeW u.pre))))

def recordsP2 {n} (B : Bank) : Code2 n → Nat
  | [] => 0
  | b::code => blockRecP2 B b + recordsP2 B code

def programP2 {n} (B : Bank) : (code : Code2 n) → (start : Nat) → Straight n start (start+recordsP2 B code)
  | [], _ => .done
  | b::code, start => castFinish (by simp [recordsP2]; omega)
      ((blockProgP2 B b start).append (programP2 B code (start+blockRecP2 B b)))

def blockSourceP2 {n} (B : Bank) (read : ConstantBit n → Bool) : Block2 n → AdaptiveCircuit
  | .plain code => source read B.bits B.paths windowRoot (normalizeW code)
  | .unit u => (source read B.bits B.paths windowRoot (normalizeW u.pre)).seq (clearSourceP B read u.clear)

theorem blockProgP2_run {n} (B : Bank) (read : ConstantBit n → Bool) (b : Block2 n)
    (start : Nat) (history : Fin start → Bool) :
    ((blockProgP2 B b start).instantiate read history).run = (blockSourceP2 B read b).run := by
  cases b with
  | plain code => exact compile_run read _ _ _ _ _ _
  | unit u =>
    rw [blockProgP2,castFinish_instantiate,append_run_fixed _ _ _ _ _ (fun h => clearP_run B read u.clear _ h),
      AdaptiveCircuit.run_seq,compile_run]
    simp only [blockSourceP2,AdaptiveCircuit.run_seq]

theorem block_simulationP2 {n} (read : ConstantBit n → Bool) (B : Bank) (hB : BankOK B)
    (block : Block2 n) (hg : BlockGeoP2 B block) :
    ∃ cs : List ℂ, List.Forall₂ (BlockSimP2 read B block) (blockSourceP2 B read block).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  cases block with
  | plain code =>
    have hg' : LitAvoid B.bits code := hg
    obtain ⟨cs,aligned,mass⟩ := lnormalized_simulation read B.bits B.paths hB.bitsLen code
      (litAvoid_placed _ _ code hg')
    refine ⟨cs,aligned.imp ?_,mass⟩
    intro b c hb
    obtain ⟨m,hm,hb⟩ := hb
    exact ⟨m,hm,fun address st hs _ _ =>
      hb address st hs (litAvoid_pathsClean read B.bits B.paths code address hg' st)⟩
  | unit u =>
    have hg' : UnitGeoP B u := hg
    have hp : ∀ i ∈ u.pre, PlacedPair B.bits B.paths windowRoot i := by
      intro i hi; exact hg'.placed i (List.mem_append_left _ hi)
    obtain ⟨preCs,preAligned,preMass⟩ := lnormalized_simulation read B.bits B.paths hB.bitsLen u.pre
      (fun i hi => pair_of_placed_lit _ _ i (hp i hi))
    obtain ⟨cs,aligned,mass⟩ := clearP_coherent read B hB u.clear hg'.site 0 Fin.elim0
    refine ⟨coherentSeqCoefficients preCs cs,?_,?_⟩
    · rw [blockSourceP2,AdaptiveCircuit.run_seq]
      apply simulationAligned_seq preAligned aligned
      intro b₁ c₁ b₂ c₂ h₁ h₂
      obtain ⟨m,hm,h₁⟩ := h₁
      refine ⟨m,?_,?_⟩
      · simpa [Block2.code,UnitSite.code,literalRecords_append,literalRecords] using hm
      · intro a st hs hcl hsafe
        have hcl' : Clean B.paths st.basis := hcl
        have hsv : SimulationValid B.bits B.paths windowRoot a st := ⟨hcl',hs.1,hs.2⟩
        let next := ECDSAAdd.run ((specialize u.pre a).instantiate read) m st
        have hn := strict_preserves read B.bits B.paths u.pre a hp st hsv m
        have hrun := unit_runP read B u hg' a st m hsv
        have hclean : Clean (portTargets u.clear.ports)
            (tableXorState (portMask read u.clear.ports a) (next.basis u.clear.guard) next.basis) := by
          have h := hsafe m
          rw [hrun] at h
          exact h
        have hlast := hg'.site.placed (.lookup (some u.clear.guard) u.clear.ports) (by simp [MaskedSite.code])
        have hvalid : Clean B.hp next.basis ∧
            ∀ p ∈ u.clear.ports, next.basis p.target = (next.basis u.clear.guard &&
              decide (read (p.ref (tableAddressValue B.bits next.basis)) = p.value)) := by
          refine ⟨fun w hw => hn.1 w (hB.sub w hw),?_⟩
          rw [hn.2.1]
          exact loaded_of_clean_unload read u.clear.ports a u.clear.guard next.basis hlast.2.1 hclean
        have hclear : b₂.kraus (ket next.basis) =
            c₂ • ket (tableXorState (portMask read u.clear.ports a) (next.basis u.clear.guard) next.basis) := by
          rw [← clear_eq_unload read u.clear.ports a u.clear.guard next.basis hclean]
          simpa [ket] using h₂ next.basis hvalid
        have hsigned : b₂.kraus (Bridge.signedKet next) = c₂ •
            Bridge.signedKet (ECDSAAdd.run ((specialize u.code a).instantiate read) m st) := by
          rw [hrun]
          change b₂.kraus (Bridge.signedKet next) = c₂ • Bridge.signedKet
            ⟨next.phase,tableXorState (portMask read u.clear.ports a) (next.basis u.clear.guard) next.basis⟩
          cases hphase : next.phase <;> simp [Bridge.signedKet,hphase,hclear,map_neg]
        change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
        rw [h₁ a st hs (strict_pathsClean read B.bits B.paths u.pre a hp st hsv),map_smul,hsigned]
        simp [smul_smul,blockReference2,Block2.code]
    · rw [simulationCoefficients_mass,preMass,mass]
      norm_num

theorem geo_lay2 {n} (B : Bank) (hB : BankOK B) (b : Block2 n) (hg : BlockGeoP2 B b) : BlockLay2 B b := by
  cases b with
  | plain code => exact geo_lay B hB (.plain code) hg
  | unit u =>
    have hg' : UnitGeoP B u := hg
    have hp : ∀ i ∈ u.pre, PlacedPair B.bits B.paths windowRoot i := by
      intro i hi; exact hg'.placed i (List.mem_append_left _ hi)
    exact ⟨pair_layouts_of_placed _ _ _ _ hB.bitsLen (pair_placed_normalize _ _ _ _ hp),
      tableAddressTree_layout B.high B.hp u.clear.guard 0 1 hB.len (site_tree_nodup B hB u.clear hg'.site)⟩

def blockTP2 {n} (B : Bank) : Block2 n → Nat
  | .plain code => literalToffolis (normalizeW code) + traversals code * (2^B.bits.length - 1)
  | .unit u => literalToffolis (normalizeW u.pre) + traversals u.pre * (2^B.bits.length - 1) +
      ((tableAddressTree B.high 0 1).internalNodes + 247)

def codeTP2 {n} (B : Bank) : Code2 n → Nat
  | [] => 0
  | b::code => blockTP2 B b + codeTP2 B code

theorem blockProgP2_tCount {n} (read : ConstantBit n → Bool) (B : Bank) (b : Block2 n) (hl : BlockLay2 B b)
    (start : Nat) (history : Fin start → Bool) :
    ((blockProgP2 B b start).instantiate read history).tCount = 7 * blockTP2 B b := by
  cases b with
  | plain code =>
    have hl' : LookupLayouts B.bits B.paths windowRoot (normalizeW code) := hl
    rw [blockProgP2, WEX.compile_tCount read _ _ _ _ hl' start history, traversals_normalize]
    simp only [blockTP2]; ring
  | unit u =>
    obtain ⟨h1, h2⟩ := hl
    rw [blockProgP2, castFinish_instantiate,
      append_tCount_fixed _ _ _ _ _ (fun h => clearP_tCount read B u.clear h2 _ h),
      WEX.compile_tCount read _ _ _ _ h1 start history, traversals_normalize]
    simp only [blockTP2]; ring

def blockSP2 {n} (B : Bank) : Block2 n → Nat
  | .plain code => codeSlots B.bits (normalizeW code)
  | .unit u => codeSlots B.bits (normalizeW u.pre) +
      (1024 * u.clear.ports.length * (tableAddressTree B.high 0 1).leaves +
        10 * (tableAddressTree B.high 0 1).internalNodes + 2291)

def codeSP2 {n} (B : Bank) : Code2 n → Nat
  | [] => 0
  | b::code => blockSP2 B b + codeSP2 B code

theorem blockProgP2_slots {n} (B : Bank) (b : Block2 n) (hl : BlockLay2 B b) (start : Nat) :
    (blockProgP2 B b start).gateSlots = blockSP2 B b := by
  cases b with
  | plain code =>
    have hl' : LookupLayouts B.bits B.paths windowRoot (normalizeW code) := hl
    rw [blockProgP2, WEX.compile_slots _ _ _ _ hl' start]
    rfl
  | unit u =>
    obtain ⟨h1, h2⟩ := hl
    rw [blockProgP2, castFinish_gateSlots, Straight.gateSlots_append, WEX.compile_slots _ _ _ _ h1 start]
    have hc : (clearP B u.clear (start + codeRecords B.bits B.paths windowRoot (normalizeW u.pre))).gateSlots =
        1024 * u.clear.ports.length * (tableAddressTree B.high 0 1).leaves +
          10 * (tableAddressTree B.high 0 1).internalNodes + 2291 := by
      unfold clearP
      rw [MeasuredClear.measuredClear_slots8 _ _ _ _ _ _ _ h2]
      simp [clearData]
    rw [hc]
    rfl

theorem programP2_support {n} (B : Bank) (hB : BankOK B) (code : Code2 n) (hg : ∀ b ∈ code, BlockGeoP2 B b)
    (S : List Wire) (hroot : windowRoot ∈ S) (hbits : B.bits ⊆ S) (hpaths : B.paths ⊆ S)
    (hlow : ∀ i, low8 i ∈ S) (hhigh : B.high ⊆ S)
    (hlit : ∀ p, WInstr.literal p ∈ erase2 code → ECDSAAdd.wires p ⊆ S.toFinset)
    (hlook : ∀ c ps, WInstr.lookup c ps ∈ erase2 code → (∀ q ∈ c, q ∈ S) ∧ portTargets ps ⊆ S)
    (start : Nat) : ChallengeMigration.straightWires (programP2 B code start) ⊆ S := by
  induction code generalizing start with
  | nil => simp [programP2,recordsP2,ChallengeMigration.straightWires]
  | cons b code ih =>
    have hlb : ∀ p, WInstr.literal p ∈ b.code → ECDSAAdd.wires p ⊆ S.toFinset :=
      fun p hm => hlit p (by simp [erase2_cons,hm])
    have hkb : ∀ c ps, WInstr.lookup c ps ∈ b.code → (∀ q ∈ c, q ∈ S) ∧ portTargets ps ⊆ S :=
      fun c ps hm => hlook c ps (by simp [erase2_cons,hm])
    rw [programP2,support_cast,straightWires_append]
    refine List.append_subset.mpr ⟨?_, ih (fun d hd => hg d (by simp [hd]))
      (fun p hm => hlit p (by simp [erase2_cons,hm])) (fun c ps hm => hlook c ps (by simp [erase2_cons,hm])) _⟩
    cases b with
    | plain code =>
      exact compile_support _ _ _ _ S hroot hbits hpaths (normalized_lit_support code S hlb)
        (normalized_look_support code S hkb) start
    | unit u =>
      have hg' : UnitGeoP B u := hg (.unit u) (by simp)
      have hpl : ∀ p, WInstr.literal p ∈ u.pre → ECDSAAdd.wires p ⊆ S.toFinset :=
        fun p hm => hlb p (List.mem_append_left _ hm)
      have hpk : ∀ c ps, WInstr.lookup c ps ∈ u.pre → (∀ q ∈ c, q ∈ S) ∧ portTargets ps ⊆ S :=
        fun c ps hm => hkb c ps (List.mem_append_left _ hm)
      have hlast := hkb (some u.clear.guard) u.clear.ports (by simp [Block2.code,UnitSite.code])
      rw [blockProgP2,support_cast,straightWires_append]
      exact List.append_subset.mpr ⟨compile_support _ _ _ _ S hroot hbits hpaths
        (normalized_lit_support _ S hpl) (normalized_look_support _ S hpk) start,
        clearP_support B hB u.clear hg'.site.kind S hlast.2 (hlast.1 u.clear.guard (Option.mem_def.mpr rfl))
          hlow hhigh hpaths _⟩

/-! #### Hosted blocks on the eight-bit bank (with 7-wire hosting via `PoolHost.hostCode7`) -/

def blockProgH {n} (B : Bank) (b : Block2 n) (start : Nat) : Straight n start (start + blockRecP2 B b) :=
  match b with
  | .plain code => castFinish (congrArg (fun k => start + k) (PoolHost.hostCode7_counts B.bits B.paths windowRoot code).1)
      (compile B.bits B.paths windowRoot (PoolHost.hostCode7 code) start)
  | .unit u => blockProgP2 B (.unit u) start

def blockSourceH {n} (B : Bank) (read : ConstantBit n → Bool) : Block2 n → AdaptiveCircuit
  | .plain code => source read B.bits B.paths windowRoot (PoolHost.hostCode7 code)
  | .unit u => blockSourceP2 B read (.unit u)

def BlockSimH7 {n} (read : ConstantBit n → Bool) (B : Bank) (block : Block2 n)
    (branch : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords block.code ∧
    ∀ address st, AddrValid B.bits windowRoot address st → BlockClean2 B.paths block st → PoolHost.HostOK7 block st →
      BlockSafe2 read address block st →
      branch.kraus (Bridge.signedKet st) =
        c • Bridge.signedKet (ECDSAAdd.run (blockReference2 read address block) m st)

theorem blockProgH_run {n} (B : Bank) (read : ConstantBit n → Bool) (b : Block2 n)
    (start : Nat) (history : Fin start → Bool) :
    ((blockProgH B b start).instantiate read history).run = (blockSourceH B read b).run := by
  cases b with
  | plain code =>
    rw [blockProgH, castFinish_instantiate]
    exact compile_run read _ _ _ _ _ _
  | unit u => exact blockProgP2_run B read (.unit u) start history

theorem block_simulationH {n} (read : ConstantBit n → Bool) (B : Bank) (hB : BankOK B)
    (block : Block2 n) (hg : BlockGeoP2 B block) :
    ∃ cs : List ℂ, List.Forall₂ (BlockSimH7 read B block) (blockSourceH B read block).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  cases block with
  | plain code =>
    have hg' : LitAvoid B.bits code := hg
    have hlit : ∀ i ∈ code, ∃ p, i = .literal p := fun i hi => by
      obtain ⟨p, rfl, -⟩ := hg' i hi; exact ⟨p, rfl⟩
    let P := ECDSAAdd.Baselines.normalizeProgram (litProg code)
    have hc : PoolHost.hostCode7 code = [.literal (PoolHost.hostBlock7 P)] :=
      PoolHost.hostCode7_eq_host ((allLit_iff code).mpr hlit)
    have hRP : windowRoot ∉ ECDSAAdd.wires P := by
      intro hw
      rw [ECDSAAdd.Baselines.normalize_wires] at hw
      obtain ⟨p, hp, hw⟩ := litProg_wires code windowRoot hw
      obtain ⟨q, he, hq⟩ := hg' _ hp
      cases he
      exact hq windowRoot (by simp) hw
    show ∃ cs : List ℂ, List.Forall₂ (BlockSimH7 read B (.plain code))
      (source read B.bits B.paths windowRoot (PoolHost.hostCode7 code)).run cs ∧ (cs.map Complex.normSq).sum = 1
    rw [hc]
    obtain ⟨cs,aligned,mass⟩ := lit_simulation read B.bits B.paths windowRoot
      ([.literal (PoolHost.hostBlock7 P)] : WCode n) (by simp)
    refine ⟨cs,aligned.imp ?_,mass⟩
    intro b c hb
    obtain ⟨m,hm,hb⟩ := hb
    refine ⟨m, ?_, fun address st hs _ hh _ => ?_⟩
    · rw [hm]
      simp only [literalRecords, PoolHost.hostBlock7_meas, P, ECDSAAdd.Baselines.normalize_measurements, Nat.add_zero]
      exact litProg_meas code hlit
    · rw [hb address st]
      have e1 : (specialize ([.literal (PoolHost.hostBlock7 P)] : WCode n) address).instantiate read = PoolHost.hostBlock7 P := by
        rw [show ([.literal (PoolHost.hostBlock7 P)] : WCode n) = wLiteral (PoolHost.hostBlock7 P) from rfl,
          specialize_literal, ECDSAAdd.ShorPort.Tmpl.instantiate_lit]
      have e2 : blockReference2 read address (.plain code : Block2 n) = litProg code := by
        simp only [blockReference2, Block2.code]
        exact litProg_inst read code address hlit
      have hrun : ECDSAAdd.run P m st = ECDSAAdd.run (litProg code) m st :=
        ECDSAAdd.Baselines.normalize_run _ m st
      have hwP : ECDSAAdd.wires P = ECDSAAdd.wires (litProg code) := ECDSAAdd.Baselines.normalize_wires _
      have hh3 := hh.1
      have hh4 := hh.2
      rw [e1, e2, PoolHost.hostBlock7_run P hRP m st hs.2 hh3.1.1.1 (by rw [hrun]; exact hh3.1.1.2 m)
        (fun c1 c2 => by
          rw [hwP] at c1 c2
          obtain ⟨d1, d2, d3⟩ := hh3.1.2 c1 c2
          exact ⟨d1, d2, by rw [hrun]; exact d3 m⟩)
        (fun c1 c2 => by
          rw [hwP] at c1 c2
          obtain ⟨d1, d2, d3⟩ := hh3.2 c1 c2
          exact ⟨d1, d2, by rw [hrun]; exact d3 m⟩)
        (fun c4 => by
          have c4' : PoolHost.host4Set (litProg code) := by simpa [PoolHost.host4Set, hwP] using c4
          obtain ⟨f1, f2, f3⟩ := hh4 c4'
          exact ⟨f1, f2, by rw [hrun]; exact (f3 m).1, by rw [hrun]; exact (f3 m).2⟩), hrun]
  | unit u =>
    obtain ⟨cs,aligned,mass⟩ := block_simulationP2 read B hB (.unit u) hg
    refine ⟨cs, aligned.imp ?_, mass⟩
    intro b c hb
    obtain ⟨m, hm, hb⟩ := hb
    exact ⟨m, hm, fun address st hs hc _ hsafe => hb address st hs hc hsafe⟩

theorem blockH_wellFormed {n} (B : Bank) (hB : BankOK B) (b : Block2 n) (hgb : BlockGeoP2 B b)
    (hpb : ∀ p, WInstr.literal p ∈ b.code → ECDSAAdd.Arithmetic.GatePhysical p) (start : Nat) :
    (blockProgH B b start).WellFormed := by
  cases b with
  | plain code =>
    have hg' : LitAvoid B.bits code := hgb
    have hlit : ∀ i ∈ code, ∃ p, i = .literal p := fun i hi => by
      obtain ⟨p, rfl, -⟩ := hg' i hi; exact ⟨p, rfl⟩
    rw [blockProgH, castFinish_wellFormed, PoolHost.hostCode7_eq_host ((allLit_iff code).mpr hlit)]
    apply compile_wellFormedLit _ _ _ _ (by simp)
    intro p hp
    rw [List.mem_singleton, WInstr.literal.injEq] at hp
    subst hp
    apply PoolHost.hostBlock7_valid
    apply ECDSAAdd.Baselines.normalize_physical
    intro i hi
    obtain ⟨q, hq, hi⟩ := litProg_mem code i hi
    exact hpb q hq i hi
  | unit u =>
    have hg' : UnitGeoP B u := hgb
    have hpref : ∀ i ∈ u.pre, LPlaced B.bits B.paths windowRoot i := fun i hi =>
      pair_of_placed_lit _ _ i (hg'.placed i (List.mem_append_left _ hi))
    have hphys : ∀ p, WInstr.literal p ∈ u.pre → ECDSAAdd.Arithmetic.GatePhysical p := by
      intro p hm; exact hpb p (List.mem_append_left _ hm)
    show (blockProgP2 B (.unit u) start).WellFormed
    rw [blockProgP2, castFinish_wellFormed]
    exact straight_append_wellFormed _ _
      (compile_wellFormedL _ _ _ _ hB.bitsLen (lplaced_normalize _ _ _ _ hpref)
        (normalized_literals_valid u.pre hphys) start)
      (clearP_wellFormed B hB u.clear hg'.site _)

theorem blockH_tCount {n} (read : ConstantBit n → Bool) (B : Bank) (b : Block2 n) (hl : BlockLay2 B b)
    (start : Nat) (history : Fin start → Bool) :
    ((blockProgH B b start).instantiate read history).tCount = 7 * (blockTP2 B b + PoolHost.blockExtra b) := by
  cases b with
  | plain code =>
    have hl' : LookupLayouts B.bits B.paths windowRoot (normalizeW code) := hl
    obtain ⟨-, e2, e3⟩ := PoolHost.hostCode7_counts B.bits B.paths windowRoot code
    rw [blockProgH, castFinish_instantiate,
      WEX.compile_tCount read _ _ _ _ (PoolHost.hostCode7_layouts _ _ _ code hl') start history, e2, e3]
    simp only [blockTP2, PoolHost.blockExtra]; ring
  | unit u =>
    simpa [PoolHost.blockExtra] using blockProgP2_tCount read B (.unit u) hl start history

theorem blockH_slots {n} (B : Bank) (b : Block2 n) (hl : BlockLay2 B b) (start : Nat) :
    (blockProgH B b start).gateSlots ≤ blockSP2 B b + 26 := by
  cases b with
  | plain code =>
    have hl' : LookupLayouts B.bits B.paths windowRoot (normalizeW code) := hl
    rw [blockProgH, castFinish_gateSlots, WEX.compile_slots _ _ _ _ (PoolHost.hostCode7_layouts _ _ _ code hl') start]
    exact PoolHost.hostCode7_slots B.bits code
  | unit u =>
    have h := blockProgP2_slots B (.unit u) hl start
    change (blockProgP2 B (.unit u) start).gateSlots ≤ blockSP2 B (.unit u) + 26
    omega

theorem blockH_residue {n} (B : Bank) (b : Block2 n) (start : Nat) :
    AndGadget.residue (blockProgH B b start) = 0 := by
  cases b with
  | plain code =>
    rw [blockProgH, AndGadget.residue_cast]
    exact WEXCredit.compile_residue _ _ _ _ _
  | unit u =>
    show AndGadget.residue (blockProgP2 B (.unit u) start) = 0
    simp [blockProgP2, AndGadget.residue_cast, AndGadget.residue_append, WEXCredit.compile_residue,
      clearP_residue]

end
end ShorECDLP.Entrant.WideBank8

/-! ### The deferred tail of a fast site on the eight-bit bank -/

namespace ShorECDLP.Entrant.WideBank8
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare
open MeasuredClear (ClearPort)
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-- Records of one fixup on the bank. -/
def fuseRec {n} (B : Bank) (site : MaskedSite n) : Nat :=
  MeasuredClear.recordMeasurements (MeasuredClear.recordUnaryOps (tableAddressTree B.high 0 1) site.guard B.hp) + 255

/-- The site clear whose fixup also carries the deferred ports `gd`, read from records `refs`. -/
def fusedFix {n} (B : Bank) (site : MaskedSite n) (gd : List (ClearPort n)) (start : Nat)
    (refs : List (Fin start)) : Straight n start (start + site.ports.length + fuseRec B site) :=
  castFinish (by simp [clearData]) (MeasuredClear.measureThen (R := fuseRec B site)
    (fun cursor rs => castFinish (by simp only [fuseRec]; omega)
      (MeasuredClear.fixupProgram8 (gd ++ clearData site.ports) rs low8 (hot8 site)
        (tableAddressTree B.high 0 1) site.guard scratch8 B.hp))
    ((clearData site.ports).map ClearPort.target) start refs)

def tailRec {n} (B : Bank) (site : MaskedSite n) : Nat :=
  codeRecords B.bits B.paths windowRoot (normalizeW site.arithmetic) + (site.ports.length + fuseRec B site)

/-- Measure the deferred register `gd` now (it is reset for reuse); its phase is repaid by the
site clear after the arithmetic. -/
def deferTail {n} (B : Bank) (site : MaskedSite n) (gd : List (ClearPort n)) (start : Nat) :
    Straight n start (start + gd.length + tailRec B site) :=
  castFinish (by simp) (MeasuredClear.measureThen (R := tailRec B site)
    (fun cursor grefs => castFinish (by simp only [tailRec]; omega)
      ((compile B.bits B.paths windowRoot (normalizeW site.arithmetic) cursor).append
        (fusedFix B site gd (cursor + codeRecords B.bits B.paths windowRoot (normalizeW site.arithmetic))
          (grefs.map (Fin.castLE (Nat.le_add_right _ _))))))
    (gd.map ClearPort.target) start List.nil)

def fusedFixSource {n} (B : Bank) (read : ConstantBit n → Bool) (site : MaskedSite n)
    (gd : List (ClearPort n)) (og : List Bool) : AdaptiveCircuit :=
  measureResetThen ((clearData site.ports).map ClearPort.target) (fun os =>
    MeasuredClear.fixupSource8 (gd ++ clearData site.ports) (og ++ os) read low8 (hot8 site)
      (tableAddressTree B.high 0 1) site.guard scratch8 B.hp)

def deferSource {n} (B : Bank) (read : ConstantBit n → Bool) (site : MaskedSite n)
    (gd : List (ClearPort n)) : AdaptiveCircuit :=
  measureResetThen (gd.map ClearPort.target) (fun og =>
    (source read B.bits B.paths windowRoot (normalizeW site.arithmetic)).seq (fusedFixSource B read site gd og))

theorem fusedFix_run {n} (B : Bank) (read : ConstantBit n → Bool) (site : MaskedSite n)
    (gd : List (ClearPort n)) (start : Nat) (refs : List (Fin start)) (history : Fin start → Bool) :
    ((fusedFix B site gd start refs).instantiate read history).run =
      (fusedFixSource B read site gd (refs.map history)).run := by
  rw [fusedFix, castFinish_instantiate,
    MeasuredClear.measureThen_run _ (fun outcomes => MeasuredClear.fixupSource8 (gd ++ clearData site.ports) outcomes read
      low8 (hot8 site) (tableAddressTree B.high 0 1) site.guard scratch8 B.hp) read
      (by intro cursor rs h; rw [castFinish_instantiate, MeasuredClear.fixupProgram_run8])]
  rfl

theorem deferTail_run {n} (B : Bank) (read : ConstantBit n → Bool) (site : MaskedSite n)
    (gd : List (ClearPort n)) (start : Nat) (history : Fin start → Bool) :
    ((deferTail B site gd start).instantiate read history).run = (deferSource B read site gd).run := by
  rw [deferTail, castFinish_instantiate,
    MeasuredClear.measureThen_run _ (fun og => (source read B.bits B.paths windowRoot (normalizeW site.arithmetic)).seq
      (fusedFixSource B read site gd og)) read]
  · simp only [List.map_nil, List.nil_append]
    rfl
  · intro cursor grefs h
    rw [castFinish_instantiate,
      MeasuredClear.append_run_prefix _ _ read (Nat.le_refl cursor) h h rfl (fusedFixSource B read site gd (grefs.map h)),
      AdaptiveCircuit.run_seq, compile_run, ← AdaptiveCircuit.run_seq]
    intro h' hh'
    rw [fusedFix_run, List.map_map]
    congr 2
    rw [← hh']
    rfl

/-! #### Geometry of a site clear on a bank -/

theorem site_clear_facts {n} (B : Bank) (hB : BankOK B) (site : MaskedSite n) (hg : SiteGeoP B site) :
    (tableAddressTree B.high 0 1).Layout site.guard B.hp ∧
    (∀ i j, low8 i ≠ hot8 site j) ∧
    (MeasuredClear.hotBank8 (hot8 site)).Disjoint (site.guard :: (tableAddressTree B.high 0 1).indexWires.dedup ++ B.hp) ∧
    scratch8 ∉ site.guard :: (tableAddressTree B.high 0 1).indexWires.dedup ++ B.hp ∧
    scratch8 ∉ MeasuredClear.hotBank8 (hot8 site) ∧
    (∀ w ∈ site.guard :: List.ofFn low8 ++ (tableAddressTree B.high 0 1).indexWires.dedup ++ B.hp,
      w ∉ portTargets site.ports) ∧
    (∀ w ∈ B.bits, w ∉ portTargets site.ports) := by
  have hlast := hg.placed (.lookup (some site.guard) site.ports) (by simp [MaskedSite.code])
  dsimp only [Placed] at hlast
  obtain ⟨hn,hbd,-,-,-,hgd,-⟩ := kind_facts site hg.kind
  have hmem := kind_hot8 site hg.kind
  have hP : ∀ w ∈ B.hp, 871 ≤ w ∧ w ∉ portTargets site.ports := by
    intro w hw
    refine ⟨hB.out w hw, fun ht => ?_⟩
    exact List.disjoint_left.mp hlast.2.2
      (show w ∈ windowRoot :: lookupRoot windowRoot (some site.guard) :: B.bits ++ B.paths by
        simp [hB.sub w hw]) ht
  have hsT := scratch8_not_targets B hB site hg
  have notT : ∀ w ∈ site.guard :: List.ofFn low8 ++ B.high ++ B.hp, w ∉ portTargets site.ports := by
    intro w hw ht
    have h2 := (hbd w ht).1
    simp only [List.mem_append,List.mem_cons] at hw
    rcases hw with ((h | h) | h) | h
    · rw [h] at h2; rcases hgd with e | e <;> rw [e] at h2 <;> dsimp only [Wire] at * <;> omega
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
      have := low8_lt i
      dsimp only [Wire] at *; omega
    · have := hB.high w h
      dsimp only [Wire] at *; omega
    · exact (hP w h).2 ht
  refine ⟨tableAddressTree_layout B.high B.hp site.guard 0 1 hB.len (site_tree_nodup B hB site hg), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j he
    have h1 := (hbd _ (hmem j)).1
    have h2 := low8_lt i
    rw [← he] at h1
    dsimp only [Wire] at *
    omega
  · apply List.disjoint_left.mpr
    intro w hw hm
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    rw [hB.index] at hm
    exact notT _ (by simp only [List.mem_append,List.mem_cons] at hm ⊢; tauto) (hmem i)
  · rw [hB.index]
    intro hm
    simp only [List.mem_cons, List.mem_append] at hm
    rcases hm with (h | h) | h
    · have hne : site.guard ≠ scratch8 := by rcases hgd with e | e <;> rw [e] <;> decide
      exact hne h.symm
    · exact absurd (hB.high _ h).2 (by decide)
    · exact hB.scr.2 h
  · intro hm
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hm
    exact hsT (hi ▸ hmem i)
  · rw [hB.index]
    intro w hw hm
    exact notT w hw hm
  · intro w hw ht
    exact List.disjoint_left.mp hlast.2.2
      (show w ∈ windowRoot :: lookupRoot windowRoot (some site.guard) :: B.bits ++ B.paths by simp [hw]) ht

/-! #### Simulation of the fused fixup -/

/-- After the site measurement the fused fixup repays both the site's and the deferred register's
phases; the deferred phase is read from the root and address at fixup time. -/
def FixSim {n} (B : Bank) (read : ConstantBit n → Bool) (site : MaskedSite n) (gd : List (ClearPort n))
    (og : List Bool) (b : InstrumentBranch) (c : ℂ) : Prop :=
  ∀ (next : ECDSAAdd.State) (u : BasisState), Clean B.hp next.basis →
    (∀ p ∈ site.ports, next.basis p.target =
      (next.basis site.guard && decide (read (p.ref (tableAddressValue B.bits next.basis)) = p.value))) →
    (∀ p ∈ gd, u p.target =
      (next.basis site.guard && decide (read (p.ref (tableAddressValue B.bits next.basis)) = p.value))) →
    b.kraus (Bridge.signedKet next) =
      (c * registerXPhase (gd.map ClearPort.target) og u) •
        Bridge.signedKet ⟨next.phase, clearRegister (portTargets site.ports) next.basis⟩

theorem fusedFix_sim {n} (read : ConstantBit n → Bool) (B : Bank) (hB : BankOK B) (site : MaskedSite n)
    (hg : SiteGeoP B site) (gd : List (ClearPort n)) (og : List Bool) (hog : og.length = gd.length) :
    ∃ cs : List ℂ, List.Forall₂ (FixSim B read site gd og) (fusedFixSource B read site gd og).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  obtain ⟨hl, hdlow, hbank, hs, hshot, ha, hbits⟩ := site_clear_facts B hB site hg
  obtain ⟨hn,-,-,-,-,-,-⟩ := kind_facts site hg.kind
  have hmem := kind_hot8 site hg.kind
  unfold fusedFixSource
  apply MeasuredClear.measureResetThen_sim ((clearData site.ports).map ClearPort.target)
    (fun os => MeasuredClear.fixupSource8 (gd ++ clearData site.ports) (og ++ os) read low8 (hot8 site)
      (tableAddressTree B.high 0 1) site.guard scratch8 B.hp)
    (fun os => BranchCoherentOn (MeasuredClear.basisIdeal id
      (MeasuredClear.fixupFactor8 (gd ++ clearData site.ports) (og ++ os) read low8 (hot8 site)
        (tableAddressTree B.high 0 1) site.guard))
      (fun s => MeasuredClear.HotClean8 (hot8 site) s ∧ Clean B.hp s))
  · intro os _
    exact MeasuredClear.fixupSource_coherent8 (gd ++ clearData site.ports) (og ++ os) read low8 (hot8 site)
      (tableAddressTree B.high 0 1) site.guard scratch8 B.hp
      hl (hot8_injective site) hdlow hbank hs hshot
  · intro os hos b c hb next u hhp hsite hgarb
    rw [clearData_targets] at hos ⊢
    have hk := xResetRegisterKraus_ket (portTargets site.ports) os next.basis hos hn
    rw [registerXResetCoeff_eq_magnitude_mul_phase _ _ _ hos] at hk
    set t := clearRegister (portTargets site.ports) next.basis with ht
    have hfr : ∀ w, w ∉ portTargets site.ports → t w = next.basis w :=
      fun w hw => MeasuredClear.clearRegister_frame _ _ _ hw
    have hhot : MeasuredClear.HotClean8 (hot8 site) t := fun i => clearRegister_clean _ _ _ (hmem i)
    have hvalid : MeasuredClear.HotClean8 (hot8 site) t ∧ Clean B.hp t :=
      ⟨hhot, fun w hw => by rw [hfr w (ha w (by simp [hw]))]; exact hhp w hw⟩
    have hsplit : ∀ s : BasisState, 256 * (tableAddressTree B.high 0 1).routeLabel s +
        MeasuredClear.hotAddress8 low8 s = tableAddressValue B.bits s := hB.split
    have haddr : tableAddressValue B.bits t = tableAddressValue B.bits next.basis :=
      WEX.tableAddressValue_congr _ _ _ (fun w hw => hfr w (hbits w hw))
    have hguard : t site.guard = next.basis site.guard := hfr _ (ha _ (by simp))
    have hfac : MeasuredClear.fixupFactor8 (gd ++ clearData site.ports) (og ++ os) read low8 (hot8 site)
        (tableAddressTree B.high 0 1) site.guard t =
        registerXPhase (gd.map ClearPort.target) og u * registerXPhase (portTargets site.ports) os next.basis := by
      rw [MeasuredClear.fixupFactor8_append _ _ _ _ hog]
      congr 1
      · apply MeasuredClear.fixupFactor8_loaded gd og read low8 (hot8 site) _ site.guard B.hp
          (hot8_injective site) hdlow hbank t u hhot
        intro p hp
        rw [hsplit, haddr, hguard]
        exact hgarb p hp
      · have h := MeasuredClear.fixupFactor_recycled8 (clearData site.ports) os read low8 (hot8 site)
          (tableAddressTree B.high 0 1) site.guard B.hp (hot8_injective site) hdlow hbank
          (by rw [clearData_targets]; exact ha) (by rw [clearData_targets]; exact hmem) next.basis
          ⟨hhp, by
            intro q hq
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
            simpa [hsplit] using hsite p hp⟩
        simpa only [clearData_targets] using h
    have hsq := MeasuredClear.registerXPhase_square (portTargets site.ports) os next.basis
    change b.kraus (xResetRegisterKraus (portTargets site.ports) os (Bridge.signedKet next)) = _
    simp only [Bridge.signedKet, map_smul, hk, hb t hvalid, MeasuredClear.basisIdeal_ket, id_eq, hfac,
      smul_smul]
    congr 1
    linear_combination ((if next.phase = true then (-1 : ℂ) else 1) * registerXResetMagnitude (portTargets site.ports).length *
      c * registerXPhase (gd.map ClearPort.target) og u) * hsq

/-! #### Arithmetic, then the fused clear -/

/-- The site's guard survives its arithmetic: it is the window root, or the arithmetic is one
literal program that never touches it. -/
def GuardKept {n} (site : MaskedSite n) : Prop :=
  site.guard = windowRoot ∨ ∃ p, site.arithmetic = [.literal p] ∧ site.guard ∉ ECDSAAdd.wires p

theorem guardKept_run {n} (read : ConstantBit n → Bool) (B : Bank) (site : MaskedSite n) (hk : GuardKept site)
    (hp : ∀ i ∈ site.arithmetic, PlacedPair B.bits B.paths windowRoot i) (a : Nat) (st : ECDSAAdd.State)
    (hs : SimulationValid B.bits B.paths windowRoot a st) (m : List Bool) :
    (ECDSAAdd.run ((specialize site.arithmetic a).instantiate read) m st).basis site.guard = st.basis site.guard := by
  rcases hk with h | ⟨p, hp', hw⟩
  · rw [h, (strict_preserves read B.bits B.paths site.arithmetic a hp st hs m).2.2, hs.2.2]
  · rw [hp']
    show (ECDSAAdd.run ((specialize (wLiteral p) a).instantiate read) m st).basis site.guard = _
    rw [specialize_literal, ECDSAAdd.ShorPort.Tmpl.instantiate_lit]
    exact ECDSAAdd.run_preserves_outside p m st _ hw

def InnerSim {n} (B : Bank) (read : ConstantBit n → Bool) (site : MaskedSite n) (gd : List (ClearPort n))
    (og : List Bool) (b : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords site.arithmetic ∧
    ∀ a (st : ECDSAAdd.State) (u : BasisState), SimulationValid B.bits B.paths windowRoot a st →
      (∀ m, Clean (portTargets site.ports)
        (ECDSAAdd.run ((specialize site.code a).instantiate read) m st).basis) →
      (∀ p ∈ gd, u p.target = (st.basis site.guard && decide (read (p.ref a) = p.value))) →
      b.kraus (Bridge.signedKet ⟨st.phase, tableXorState (portMask read site.ports a) (st.basis site.guard) st.basis⟩) =
        (c * registerXPhase (gd.map ClearPort.target) og u) •
          Bridge.signedKet (ECDSAAdd.run ((specialize site.code a).instantiate read) m st)

theorem inner_sim {n} (read : ConstantBit n → Bool) (B : Bank) (hB : BankOK B) (site : MaskedSite n)
    (hg : SiteGeoP B site) (hk : GuardKept site) (gd : List (ClearPort n)) (og : List Bool)
    (hog : og.length = gd.length) :
    ∃ cs : List ℂ, List.Forall₂ (InnerSim B read site gd og)
      ((source read B.bits B.paths windowRoot (normalizeW site.arithmetic)).seq
        (fusedFixSource B read site gd og)).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
  have hpre : ∀ i ∈ site.prefix, PlacedPair B.bits B.paths windowRoot i := fun i hi =>
    placed_implies_pair _ _ _ _ (hg.placed i (List.mem_append_left _ hi))
  have harith : ∀ i ∈ site.arithmetic, PlacedPair B.bits B.paths windowRoot i := fun i hi =>
    hpre i (List.mem_cons_of_mem _ hi)
  obtain ⟨c1, a1, m1⟩ := lnormalized_simulation read B.bits B.paths hB.bitsLen site.arithmetic
    (fun i hi => pair_of_placed_lit _ _ i (harith i hi))
  obtain ⟨c2, a2, m2⟩ := fusedFix_sim read B hB site hg gd og hog
  refine ⟨coherentSeqCoefficients c1 c2, ?_, ?_⟩
  · rw [AdaptiveCircuit.run_seq]
    apply simulationAligned_seq a1 a2
    intro b₁ k₁ b₂ k₂ h₁ h₂
    obtain ⟨m, hm, h₁⟩ := h₁
    refine ⟨m, hm, ?_⟩
    intro a st u hs hun hu
    have hload := hg.placed (.lookup (some site.guard) site.ports)
      (by simp [MaskedSite.code, MaskedSite.prefix])
    have hL := lookup_preserves_simulation read (some site.guard) site.ports B.bits B.paths
      windowRoot a hload st hs
    simp only [lookupRoot, Option.getD_some] at hL
    have hroot : site.guard ∉ portTargets site.ports :=
      List.disjoint_left.mp hload.2.2 (by simp [lookupRoot])
    have e : ECDSAAdd.run ((specialize site.prefix a).instantiate read) m st =
        ECDSAAdd.run ((specialize site.arithmetic a).instantiate read) m
          ⟨st.phase, tableXorState (portMask read site.ports a) (st.basis site.guard) st.basis⟩ := by
      simp only [MaskedSite.prefix, specialize, List.flatMap_cons, WInstr.specialize,
        ECDSAAdd.ShorPort.Tmpl.instantiate_append, ECDSAAdd.run_append, (portTemplate_counts read _ _ _).2,
        List.take_zero, List.drop_zero]
      rw [portTemplate_run read (some site.guard) site.ports a windowRoot List.nil st hload.2.1 hroot hs.2.2]
      rfl
    have hn := strict_preserves read B.bits B.paths site.prefix a hpre st hs m
    have hrun := masked_runP read B site hg a st m hs
    set L : ECDSAAdd.State :=
      ⟨st.phase, tableXorState (portMask read site.ports a) (st.basis site.guard) st.basis⟩ with hLdef
    set next := ECDSAAdd.run ((specialize site.prefix a).instantiate read) m st with hnext
    have hclean : Clean (portTargets site.ports)
        (tableXorState (portMask read site.ports a) (next.basis site.guard) next.basis) := by
      have h := hun m
      rw [hrun] at h
      exact h
    have hlast := hg.placed (.lookup (some site.guard) site.ports) (by simp [MaskedSite.code])
    have hguard : next.basis site.guard = st.basis site.guard := by
      rw [e, guardKept_run read B site hk harith a L hL m]
      exact tableXorState_outside _ _ _ _ (fun hm => hroot (tableBitsMask_subset _ _ hm))
    have hsite : ∀ p ∈ site.ports, next.basis p.target = (next.basis site.guard &&
        decide (read (p.ref (tableAddressValue B.bits next.basis)) = p.value)) := by
      rw [hn.2.1]
      exact loaded_of_clean_unload read site.ports a site.guard next.basis hlast.2.1 hclean
    have h2 := h₂ next u (fun w hw => hn.1 w (hB.sub w hw)) hsite (by
      intro p hp
      rw [hn.2.1, hguard]
      exact hu p hp)
    have hfin : (⟨next.phase, clearRegister (portTargets site.ports) next.basis⟩ : ECDSAAdd.State) =
        ECDSAAdd.run ((specialize site.code a).instantiate read) m st := by
      rw [hrun, clear_eq_unload read site.ports a site.guard next.basis hclean]
    have h1 := h₁ a L ⟨hL.2.1, hL.2.2⟩ (strict_pathsClean read B.bits B.paths site.arithmetic a harith L hL)
    rw [← e] at h1
    change b₂.kraus (b₁.kraus (Bridge.signedKet L)) = _
    rw [h1, map_smul, h2, hfin, smul_smul, mul_assoc]
  · rw [simulationCoefficients_mass, m1, m2]
    norm_num

def TailSim {n} (B : Bank) (read : ConstantBit n → Bool) (site : MaskedSite n) (gd : List (ClearPort n))
    (b : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords site.arithmetic ∧
    ∀ a (st u : ECDSAAdd.State), SimulationValid B.bits B.paths windowRoot a st →
      (∀ m, Clean (portTargets site.ports)
        (ECDSAAdd.run ((specialize site.code a).instantiate read) m st).basis) →
      (∀ p ∈ gd, u.basis p.target = (st.basis site.guard && decide (read (p.ref a) = p.value))) →
      u.phase = st.phase →
      clearRegister (gd.map ClearPort.target) u.basis =
        tableXorState (portMask read site.ports a) (st.basis site.guard) st.basis →
      b.kraus (Bridge.signedKet u) =
        c • Bridge.signedKet (ECDSAAdd.run ((specialize site.code a).instantiate read) m st)

/-- Measurement of the deferred register, the arithmetic and the fused fixup, as one unit. -/
theorem tail_sim {n} (read : ConstantBit n → Bool) (B : Bank) (hB : BankOK B) (site : MaskedSite n)
    (hg : SiteGeoP B site) (hk : GuardKept site) (gd : List (ClearPort n))
    (hgn : (gd.map ClearPort.target).Nodup) :
    ∃ cs : List ℂ, List.Forall₂ (TailSim B read site gd) (deferSource B read site gd).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  unfold deferSource
  apply MeasuredClear.measureResetThen_sim (gd.map ClearPort.target)
    (fun og => (source read B.bits B.paths windowRoot (normalizeW site.arithmetic)).seq
      (fusedFixSource B read site gd og)) (fun og => InnerSim B read site gd og)
  · intro og hog
    exact inner_sim read B hB site hg hk gd og (by simpa using hog)
  · intro og hog b c hb
    obtain ⟨m, hm, hb⟩ := hb
    refine ⟨m, hm, ?_⟩
    intro a st u hs hun hu hph hclr
    have hk' := xResetRegisterKraus_ket (gd.map ClearPort.target) og u.basis hog hgn
    rw [registerXResetCoeff_eq_magnitude_mul_phase _ _ _ hog, hclr] at hk'
    have h := hb a st u.basis hs hun hu
    have hsq := MeasuredClear.registerXPhase_square (gd.map ClearPort.target) og u.basis
    change b.kraus (xResetRegisterKraus (gd.map ClearPort.target) og (Bridge.signedKet u)) = _
    have hstep : b.kraus (xResetRegisterKraus (gd.map ClearPort.target) og (Bridge.signedKet u)) =
        (registerXResetMagnitude (gd.map ClearPort.target).length *
          registerXPhase (gd.map ClearPort.target) og u.basis) •
          b.kraus (Bridge.signedKet ⟨st.phase,
            tableXorState (portMask read site.ports a) (st.basis site.guard) st.basis⟩) := by
      simp only [Bridge.signedKet, hph, map_smul, hk', smul_smul]
      congr 1
      ring
    rw [hstep, h, smul_smul]
    congr 1
    linear_combination (registerXResetMagnitude (gd.map ClearPort.target).length * c) * hsq

/-! #### Resources of the deferred tail -/

theorem fusedFix_tCount {n} (read : ConstantBit n → Bool) (B : Bank) (site : MaskedSite n)
    (gd : List (ClearPort n)) (hl : (tableAddressTree B.high 0 1).Layout site.guard B.hp)
    (start : Nat) (refs : List (Fin start)) (history : Fin start → Bool) :
    ((fusedFix B site gd start refs).instantiate read history).tCount =
      7 * (tableAddressTree B.high 0 1).internalNodes + 1729 := by
  rw [fusedFix, castFinish_instantiate, MeasuredClear.measureThen_tCount _ read (by
    intro cursor rs h
    rw [castFinish_instantiate, MeasuredClear.fixupProgram_tCount8 _ rs low8 (hot8 site) _ site.guard
      scratch8 B.hp hl])]

theorem deferTail_tCount {n} (read : ConstantBit n → Bool) (B : Bank) (site : MaskedSite n)
    (gd : List (ClearPort n)) (hl : (tableAddressTree B.high 0 1).Layout site.guard B.hp)
    (hal : LookupLayouts B.bits B.paths windowRoot (normalizeW site.arithmetic))
    (start : Nat) (history : Fin start → Bool) :
    ((deferTail B site gd start).instantiate read history).tCount =
      7 * literalToffolis (normalizeW site.arithmetic) +
        7 * traversals (normalizeW site.arithmetic) * (2 ^ B.bits.length - 1) +
        (7 * (tableAddressTree B.high 0 1).internalNodes + 1729) := by
  rw [deferTail, castFinish_instantiate, MeasuredClear.measureThen_tCount _ read (by
    intro cursor grefs h
    rw [castFinish_instantiate, append_tCount_fixed _ _ _ _ _ (fun h' => fusedFix_tCount read B site gd hl _ _ h'),
      compile_tCount read _ _ _ _ hal])]

theorem fusedFix_slots {n} (B : Bank) (site : MaskedSite n) (gd : List (ClearPort n))
    (hl : (tableAddressTree B.high 0 1).Layout site.guard B.hp) (start : Nat) (refs : List (Fin start)) :
    (fusedFix B site gd start refs).gateSlots =
      1024 * min (gd.length + site.ports.length) (refs.length + site.ports.length) *
        (tableAddressTree B.high 0 1).leaves + 10 * (tableAddressTree B.high 0 1).internalNodes + 2291 := by
  rw [fusedFix, castFinish_gateSlots, MeasuredClear.measureThen_slots _
    (fun k => 1024 * min (gd ++ clearData site.ports).length k * (tableAddressTree B.high 0 1).leaves +
      10 * (tableAddressTree B.high 0 1).internalNodes + 2291)
    (by intro cursor rs; rw [castFinish_gateSlots, MeasuredClear.fixupProgram_slots8 _ rs low8 (hot8 site) _
      site.guard scratch8 B.hp hl])]
  simp [clearData]

theorem deferTail_slots {n} (B : Bank) (site : MaskedSite n) (gd : List (ClearPort n))
    (hl : (tableAddressTree B.high 0 1).Layout site.guard B.hp)
    (hal : LookupLayouts B.bits B.paths windowRoot (normalizeW site.arithmetic)) (start : Nat) :
    (deferTail B site gd start).gateSlots = codeSlots B.bits (normalizeW site.arithmetic) +
      (1024 * (gd.length + site.ports.length) * (tableAddressTree B.high 0 1).leaves +
        10 * (tableAddressTree B.high 0 1).internalNodes + 2291) := by
  rw [deferTail, castFinish_gateSlots, MeasuredClear.measureThen_slots _
    (fun k => codeSlots B.bits (normalizeW site.arithmetic) +
      (1024 * min (gd.length + site.ports.length) (k + site.ports.length) * (tableAddressTree B.high 0 1).leaves +
        10 * (tableAddressTree B.high 0 1).internalNodes + 2291))
    (by intro cursor grefs; rw [castFinish_gateSlots, Straight.gateSlots_append, WEX.compile_slots _ _ _ _ hal,
      fusedFix_slots B site gd hl]; simp)]
  simp

theorem deferTail_wellFormed {n} (B : Bank) (hB : BankOK B) (site : MaskedSite n) (hg : SiteGeoP B site)
    (gd : List (ClearPort n))
    (hlit : ∀ p, WInstr.literal p ∈ site.arithmetic → ECDSAAdd.Arithmetic.GatePhysical p) (start : Nat) :
    (deferTail B site gd start).WellFormed := by
  obtain ⟨hl, hdlow, hbank, hs, hshot, -, -⟩ := site_clear_facts B hB site hg
  have harith : ∀ i ∈ site.arithmetic, PlacedPair B.bits B.paths windowRoot i := fun i hi =>
    placed_implies_pair _ _ _ _ (hg.placed i (List.mem_append_left _ (List.mem_cons_of_mem _ hi)))
  rw [deferTail, castFinish_wellFormed]
  apply MeasuredClear.measureThen_wellFormed
  intro cursor grefs
  rw [castFinish_wellFormed]
  apply straight_append_wellFormed
  · exact pair_compile_wellFormed _ _ _ _ hB.bitsLen (pair_placed_normalize _ _ _ _ harith)
      (normalized_literals_valid site.arithmetic hlit) _
  · rw [fusedFix, castFinish_wellFormed]
    apply MeasuredClear.measureThen_wellFormed
    intro c rs
    rw [castFinish_wellFormed]
    exact MeasuredClear.fixupProgram_wellFormed8 _ rs low8 (hot8 site) _ site.guard scratch8 B.hp hl
      (hot8_injective site) hdlow hs hshot

open AndGadget WEXCredit in
theorem deferTail_residue {n} (B : Bank) (site : MaskedSite n) (gd : List (ClearPort n)) (start : Nat) :
    residue (deferTail B site gd start) = 0 := by
  rw [deferTail, residue_cast]
  apply MeasuredClear.measureThen_residue
  intro cursor grefs
  rw [residue_cast, residue_append, compile_residue, fusedFix, residue_cast, Nat.zero_add]
  apply MeasuredClear.measureThen_residue
  intro c rs
  rw [residue_cast]
  exact MeasuredClear.fixupProgram_residue8 _ _ _ _ _ _ _ _

theorem deferTail_support {n} (B : Bank) (hB : BankOK B) (site : MaskedSite n) (hk : SiteKind site)
    (gd : List (ClearPort n)) (S : List Wire)
    (hS : portTargets site.ports ⊆ S) (hgS : site.guard ∈ S) (hlow : ∀ i, low8 i ∈ S)
    (hhigh : B.high ⊆ S) (hpaths : B.paths ⊆ S) (hroot : windowRoot ∈ S) (hbits : B.bits ⊆ S)
    (hgd : gd.map ClearPort.target ⊆ S)
    (hlit : ∀ p, WInstr.literal p ∈ site.arithmetic → ECDSAAdd.wires p ⊆ S.toFinset)
    (hlook : ∀ c ps, WInstr.lookup c ps ∈ site.arithmetic → (∀ q ∈ c, q ∈ S) ∧ portTargets ps ⊆ S)
    (start : Nat) : ChallengeMigration.straightWires (deferTail B site gd start) ⊆ S := by
  have hmem := kind_hot8 site hk
  rw [support_agrees, deferTail, MeasuredClear.static_cast]
  apply MeasuredClear.measureThen_within _ S _ _ _ _ hgd
  intro cursor grefs
  rw [MeasuredClear.static_cast, ← support_agrees, straightWires_append]
  refine List.append_subset.mpr ⟨compile_support _ _ _ _ S hroot hbits hpaths
    (normalized_lit_support _ S hlit) (normalized_look_support _ S hlook) _, ?_⟩
  rw [support_agrees, fusedFix, MeasuredClear.static_cast]
  apply MeasuredClear.measureThen_within _ S _ _ _ _ (by rw [clearData_targets]; exact hS)
  intro c rs
  rw [MeasuredClear.static_cast]
  apply MeasuredClear.fixupProgram_within8 _ _ _ _ _ _ _ _ S hgS (hpaths hB.scr.1) hlow
    (fun i => hS (hmem i)) _ (fun w hw => hpaths (hB.sub w hw))
  intro w hw
  apply hhigh
  rw [← hB.index]
  exact List.mem_dedup.mpr hw

/-- The triple site's arithmetic is one uncontrolled constant addition on the dialog pool, which
never touches its guard `generic`. -/
theorem guard_not_program (L : ECDSAAdd.Arithmetic.MeasuredCanonicalModLayout) (c p : Nat) (w : Wire)
    (hw : w ∉ L.wires) : w ∉ ECDSAAdd.wires (L.program c p) :=
  fun h => hw (List.mem_toFinset.mp (L.program_wires_subset c p h))

theorem triple_guardKept : GuardKept WEXFast.tripleSite := by
  have hw : streamLayout.core.generic ∉ (streamLayout.recoveryConstant streamLayout.point.x).wires := by
    decide +kernel
  exact Or.inr ⟨(streamLayout.recoveryConstant streamLayout.point.x).program
    ECDSAAdd.Arithmetic.SquareReduction.c ECDSAAdd.p, rfl, guard_not_program _ _ _ _ hw⟩

/-- The second fast site is guarded by the window root. -/
theorem site2_guardKept : GuardKept WEXFast.site2F.site := Or.inl rfl

/-! #### Deferring one unit clear into the next unit's clear

Two adjacent units whose clears are guarded by the window root share the guard and the address
of their phase fixups. The first unit's register is measured (and reset) where its clear used to
be, but its phase is repaid by the second unit's clear, after the second unit's prefix. -/

/-- A unit read as a site whose arithmetic is the unit's prefix. -/
def unitTail {n} (u : UnitSite n) : MaskedSite n := ⟨u.clear.guard, u.clear.ports, u.pre⟩

def UInnerSim {n} (B : Bank) (read : ConstantBit n → Bool) (u : UnitSite n) (gd : List (ClearPort n))
    (og : List Bool) (b : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords u.pre ∧
    ∀ a (st : ECDSAAdd.State) (v : BasisState), SimulationValid B.bits B.paths windowRoot a st →
      (∀ m, Clean (portTargets u.clear.ports)
        (ECDSAAdd.run ((specialize u.code a).instantiate read) m st).basis) →
      (∀ p ∈ gd, v p.target = (st.basis u.clear.guard && decide (read (p.ref a) = p.value))) →
      b.kraus (Bridge.signedKet st) =
        (c * registerXPhase (gd.map ClearPort.target) og v) •
          Bridge.signedKet (ECDSAAdd.run ((specialize u.code a).instantiate read) m st)

theorem uinner_sim {n} (read : ConstantBit n → Bool) (B : Bank) (hB : BankOK B) (u : UnitSite n)
    (hg : UnitGeoP B u) (hroot : u.clear.guard = windowRoot) (gd : List (ClearPort n)) (og : List Bool)
    (hog : og.length = gd.length) :
    ∃ cs : List ℂ, List.Forall₂ (UInnerSim B read u gd og)
      ((source read B.bits B.paths windowRoot (normalizeW u.pre)).seq
        (fusedFixSource B read u.clear gd og)).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
  have hp : ∀ i ∈ u.pre, PlacedPair B.bits B.paths windowRoot i := fun i hi =>
    hg.placed i (List.mem_append_left _ hi)
  obtain ⟨c1, a1, m1⟩ := lnormalized_simulation read B.bits B.paths hB.bitsLen u.pre
    (fun i hi => pair_of_placed_lit _ _ i (hp i hi))
  obtain ⟨c2, a2, m2⟩ := fusedFix_sim read B hB u.clear hg.site gd og hog
  refine ⟨coherentSeqCoefficients c1 c2, ?_, ?_⟩
  · rw [AdaptiveCircuit.run_seq]
    apply simulationAligned_seq a1 a2
    intro b₁ k₁ b₂ k₂ h₁ h₂
    obtain ⟨m, hm, h₁⟩ := h₁
    refine ⟨m, hm, ?_⟩
    intro a st v hs hun hv
    have hn := strict_preserves read B.bits B.paths u.pre a hp st hs m
    have hrun := unit_runP read B u hg a st m hs
    have h1 := h₁ a st ⟨hs.2.1, hs.2.2⟩ (strict_pathsClean read B.bits B.paths u.pre a hp st hs)
    set next := ECDSAAdd.run ((specialize u.pre a).instantiate read) m st with hnext
    have hclean : Clean (portTargets u.clear.ports)
        (tableXorState (portMask read u.clear.ports a) (next.basis u.clear.guard) next.basis) := by
      have h := hun m
      rw [hrun] at h
      exact h
    have hlast := hg.site.placed (.lookup (some u.clear.guard) u.clear.ports) (by simp [MaskedSite.code])
    have hguard : next.basis u.clear.guard = st.basis u.clear.guard := by
      rw [hroot, hn.2.2, hs.2.2]
    have hsite : ∀ p ∈ u.clear.ports, next.basis p.target = (next.basis u.clear.guard &&
        decide (read (p.ref (tableAddressValue B.bits next.basis)) = p.value)) := by
      rw [hn.2.1]
      exact loaded_of_clean_unload read u.clear.ports a u.clear.guard next.basis hlast.2.1 hclean
    have h2 := h₂ next v (fun w hw => hn.1 w (hB.sub w hw)) hsite (by
      intro p hp'
      rw [hn.2.1, hguard]
      exact hv p hp')
    have hfin : (⟨next.phase, clearRegister (portTargets u.clear.ports) next.basis⟩ : ECDSAAdd.State) =
        ECDSAAdd.run ((specialize u.code a).instantiate read) m st := by
      rw [hrun, clear_eq_unload read u.clear.ports a u.clear.guard next.basis hclean]
    change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
    rw [h1, map_smul, h2, hfin, smul_smul, mul_assoc]
  · rw [simulationCoefficients_mass, m1, m2]
    norm_num

def UTailSim {n} (B : Bank) (read : ConstantBit n → Bool) (u : UnitSite n) (gd : List (ClearPort n))
    (b : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords u.pre ∧
    ∀ a (st w : ECDSAAdd.State), SimulationValid B.bits B.paths windowRoot a st →
      (∀ m, Clean (portTargets u.clear.ports)
        (ECDSAAdd.run ((specialize u.code a).instantiate read) m st).basis) →
      (∀ p ∈ gd, w.basis p.target = (st.basis u.clear.guard && decide (read (p.ref a) = p.value))) →
      w.phase = st.phase →
      clearRegister (gd.map ClearPort.target) w.basis = st.basis →
      b.kraus (Bridge.signedKet w) =
        c • Bridge.signedKet (ECDSAAdd.run ((specialize u.code a).instantiate read) m st)

/-- Measurement of the deferred register, the unit prefix and the fused fixup, as one unit. -/
theorem utail_sim {n} (read : ConstantBit n → Bool) (B : Bank) (hB : BankOK B) (u : UnitSite n)
    (hg : UnitGeoP B u) (hroot : u.clear.guard = windowRoot) (gd : List (ClearPort n))
    (hgn : (gd.map ClearPort.target).Nodup) :
    ∃ cs : List ℂ, List.Forall₂ (UTailSim B read u gd) (deferSource B read (unitTail u) gd).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  unfold deferSource
  apply MeasuredClear.measureResetThen_sim (gd.map ClearPort.target)
    (fun og => (source read B.bits B.paths windowRoot (normalizeW u.pre)).seq
      (fusedFixSource B read u.clear gd og)) (fun og => UInnerSim B read u gd og)
  · intro og hog
    exact uinner_sim read B hB u hg hroot gd og (by simpa using hog)
  · intro og hog b c hb
    obtain ⟨m, hm, hb⟩ := hb
    refine ⟨m, hm, ?_⟩
    intro a st w hs hun hu hph hclr
    have hk' := xResetRegisterKraus_ket (gd.map ClearPort.target) og w.basis hog hgn
    rw [registerXResetCoeff_eq_magnitude_mul_phase _ _ _ hog, hclr] at hk'
    have h := hb a st w.basis hs hun hu
    have hsq := MeasuredClear.registerXPhase_square (gd.map ClearPort.target) og w.basis
    change b.kraus (xResetRegisterKraus (gd.map ClearPort.target) og (Bridge.signedKet w)) = _
    have hstep : b.kraus (xResetRegisterKraus (gd.map ClearPort.target) og (Bridge.signedKet w)) =
        (registerXResetMagnitude (gd.map ClearPort.target).length *
          registerXPhase (gd.map ClearPort.target) og w.basis) •
          b.kraus (Bridge.signedKet st) := by
      simp only [Bridge.signedKet, hph, map_smul, hk', smul_smul]
      congr 1
      ring
    rw [hstep, h, smul_smul]
    congr 1
    linear_combination (registerXResetMagnitude (gd.map ClearPort.target).length * c) * hsq

theorem unitTail_wellFormed {n} (B : Bank) (hB : BankOK B) (u : UnitSite n) (hg : UnitGeoP B u)
    (gd : List (ClearPort n))
    (hlit : ∀ p, WInstr.literal p ∈ u.pre → ECDSAAdd.Arithmetic.GatePhysical p) (start : Nat) :
    (deferTail B (unitTail u) gd start).WellFormed := by
  obtain ⟨hl, hdlow, hbank, hs, hshot, -, -⟩ := site_clear_facts B hB u.clear hg.site
  have harith : ∀ i ∈ u.pre, PlacedPair B.bits B.paths windowRoot i := fun i hi =>
    hg.placed i (List.mem_append_left _ hi)
  rw [deferTail, castFinish_wellFormed]
  apply MeasuredClear.measureThen_wellFormed
  intro cursor grefs
  rw [castFinish_wellFormed]
  apply straight_append_wellFormed
  · exact pair_compile_wellFormed _ _ _ _ hB.bitsLen (pair_placed_normalize _ _ _ _ harith)
      (normalized_literals_valid u.pre hlit) _
  · rw [fusedFix, castFinish_wellFormed]
    apply MeasuredClear.measureThen_wellFormed
    intro c rs
    rw [castFinish_wellFormed]
    exact MeasuredClear.fixupProgram_wellFormed8 _ rs low8 (hot8 u.clear) _ u.clear.guard scratch8 B.hp hl
      (hot8_injective u.clear) hdlow hs hshot

end
end ShorECDLP.Entrant.WideBank8

namespace ShorECDLP.Entrant.WideBank8.Fast16
open ShorECDLP.Entrant.WideSigned
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup PathShare
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
def windowBits : List Wire := List.range' 855 15 ++ [871]
def pathBank : List Wire := List.range' 14832 15 ++ [14848]
/-- The eight high address bits; the low eight `855..862` feed the hot bank. -/
def high : List Wire := List.range' 863 7 ++ [871]
/-- The clear path bank is the first eight bank wires; the ninth, `14840`, is the dirty scratch. -/
def bank15 : PathShare.Bank := ⟨windowBits, high, List.range' 14832 8, pathBank⟩
theorem high_nodes : (tableAddressTree high 0 1).internalNodes = 255 := by
  have h := tableAddressTree_nodes high 0 1
  rw [show high.length = 8 from rfl] at h
  omega
theorem slots_append_wide {n} (a b : WCode n) :
    codeSlots windowBits (a ++ b) = codeSlots windowBits a + codeSlots windowBits b := by
  induction a with
  | nil => simp [codeSlots]
  | cons i a ih => cases i <;> simp [codeSlots, ih, Nat.add_assoc]
theorem splitAddress (s : BasisState) :
    256 * (tableAddressTree high 0 1).routeLabel s + MeasuredClear.hotAddress8 low8 s =
      tableAddressValue windowBits s := by
  exact MeasuredClear.splitAddress_value8 low8 high s
theorem bank15_ok : BankOK bank15 where
  split := splitAddress
  high := by intro v hv; simp only [bank15, high, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_range'_1] at hv; dsimp only [Wire] at *; omega
  index := tableAddressTree_index _ _ _ (by decide)
  nodup := by decide
  len := by decide
  sub := by intro v hv; simp only [bank15, pathBank, List.mem_range'_1, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hv ⊢; dsimp only [Wire] at *; omega
  out := by intro v hv; simp only [bank15, List.mem_range'_1] at hv; dsimp only [Wire] at *; omega
  bitsLen := by decide
  scr := by
    refine ⟨?_, ?_⟩
    · simp only [bank15, pathBank, scratch8, List.mem_append, List.mem_range'_1]; omega
    · simp only [bank15, scratch8, List.mem_range'_1]; omega

theorem row16_geo (b : Block2 65536) (hb : b ∈ Geometry.row .w16) :
    BlockGeoP2 bank15 b := by
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hb
  cases old with
  | plain c =>
    exact Geometry.row_geometry .w16 _ (List.mem_map.mpr ⟨.plain c, ho, rfl⟩)
  | unit u =>
    exact PoolHost.extend_unit_wide bank15 rfl rfl u ho (PathShare.rowC_geo15 _ ho)
end
end ShorECDLP.Entrant.WideBank8.Fast16

section
namespace ShorECDLP.Entrant.WideBank8.Fast16
open ShorECDLP.Entrant.WideSigned
open AndGadget WEXCredit Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup PathShare
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-! ### Controlled swap layers -/

/-- Pairwise controlled swaps of two aligned registers. -/
def swapLayer (c : Wire) : List Wire → List Wire → ECDSAAdd.Program
  | a :: as, b :: bs => cswap c a b ++ swapLayer c as bs
  | _, _ => []

theorem swapLayer_meas (c : Wire) : ∀ as bs : List Wire, ECDSAAdd.measurementCount (swapLayer c as bs) = 0
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs => by
    rw [swapLayer, ECDSAAdd.measurementCount_append, swapLayer_meas c as bs]
    rfl

theorem swapLayer_toff (c : Wire) : ∀ as bs : List Wire,
    ECDSAAdd.toffoliCount (swapLayer c as bs) = min as.length bs.length
  | [], _ => by simp [swapLayer, ECDSAAdd.toffoliCount]
  | _ :: _, [] => by simp [swapLayer, ECDSAAdd.toffoliCount]
  | a :: as, b :: bs => by
    rw [swapLayer, ECDSAAdd.toffoliCount_append, swapLayer_toff c as bs]
    have h1 : ECDSAAdd.toffoliCount (cswap c a b) = 1 := rfl
    simp only [List.length_cons]
    omega

theorem swapLayer_slots (c : Wire) : ∀ as bs : List Wire,
    ECDSAAdd.Challenge.gateSlots (swapLayer c as bs) = 3 * min as.length bs.length
  | [], _ => by simp [swapLayer, ECDSAAdd.Challenge.gateSlots]
  | _ :: _, [] => by simp [swapLayer, ECDSAAdd.Challenge.gateSlots]
  | a :: as, b :: bs => by
    rw [swapLayer, ECDSAAdd.Challenge.gateSlots_append, swapLayer_slots c as bs]
    have h3 : ECDSAAdd.Challenge.gateSlots (cswap c a b) = 3 := rfl
    simp only [List.length_cons]
    omega

theorem swapLayer_wires (c : Wire) : ∀ as bs : List Wire,
    ECDSAAdd.wires (swapLayer c as bs) ⊆ (c :: as ++ bs).toFinset
  | [], _ => by simp [swapLayer, ECDSAAdd.wires]
  | _ :: _, [] => by simp [swapLayer, ECDSAAdd.wires]
  | a :: as, b :: bs => by
    rw [swapLayer, ECDSAAdd.wires_append]
    apply Finset.union_subset
    · have hw3 : ECDSAAdd.wires (cswap c a b) = [c,a,b].toFinset := by
        ext w; simp [cswap, ECDSAAdd.wires, ECDSAAdd.Instr.wires]; tauto
      rw [hw3]
      intro w hw
      simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hw
      simp only [List.cons_append, List.mem_toFinset, List.mem_cons, List.mem_append]
      rcases hw with rfl | rfl | rfl <;> simp
    · intro w hw
      have h := swapLayer_wires c as bs hw
      simp only [List.cons_append, List.mem_toFinset, List.mem_cons, List.mem_append] at h ⊢
      rcases h with h | h | h <;> simp [h]

theorem swapLayer_valid (c : Wire) : ∀ as bs : List Wire, c ∉ as ++ bs → (as ++ bs).Nodup →
    ∀ i ∈ swapLayer c as bs, ECDSAAdd.Challenge.instructionValid i
  | [], _, _, _ => by simp [swapLayer]
  | _ :: _, [], _, _ => by simp [swapLayer]
  | a :: as, b :: bs, hc, hn => by
    have hca : c ≠ a := fun h => hc (by simp [h])
    have hcb : c ≠ b := fun h => hc (by simp [h])
    have hc' : c ∉ as ++ bs := fun h => hc (by
      simp only [List.cons_append, List.mem_cons, List.mem_append] at h ⊢; tauto)
    have hn1 := List.nodup_cons.mp (by simpa only [List.cons_append] using hn)
    have hab : a ≠ b := fun h => hn1.1 (by simp [h])
    have hn' : (as ++ bs).Nodup := hn1.2.sublist ((List.sublist_cons_self b bs).append_left as)
    intro i hi
    rw [swapLayer, List.mem_append] at hi
    rcases hi with hi | hi
    · simp only [cswap, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl
      · exact Ne.symm hab
      · exact ⟨hca, hcb, hab⟩
      · exact Ne.symm hab
    · exact swapLayer_valid c as bs hc' hn' i hi

/-- Both registers of a layer are permuted in place; wires outside are untouched. -/
theorem swapLayer_run (c : Wire) : ∀ (as bs : List Wire), c ∉ as ++ bs → (as ++ bs).Nodup →
    as.length = bs.length → ∀ (s : ECDSAAdd.State) (m : List Bool),
    (ECDSAAdd.run (swapLayer c as bs) m s).phase = s.phase ∧
    (∀ w, w ∉ as → w ∉ bs → (ECDSAAdd.run (swapLayer c as bs) m s).basis w = s.basis w) ∧
    (∀ i (ha : i < as.length) (hb : i < bs.length),
      (ECDSAAdd.run (swapLayer c as bs) m s).basis (getElem as i ha) =
        (if s.basis c then s.basis (getElem bs i hb) else s.basis (getElem as i ha)) ∧
      (ECDSAAdd.run (swapLayer c as bs) m s).basis (getElem bs i hb) =
        (if s.basis c then s.basis (getElem as i ha) else s.basis (getElem bs i hb)))
  | [], bs, _, _, _, s, m => by
    refine ⟨rfl, fun _ _ _ => rfl, ?_⟩
    intro i ha
    simp at ha
  | a :: as, [], _, _, hl, _, _ => by simp at hl
  | a :: as, b :: bs, hc, hn, hl, s, m => by
    have hca : c ≠ a := fun h => hc (by simp [h])
    have hcb : c ≠ b := fun h => hc (by simp [h])
    have hc' : c ∉ as ++ bs := fun h => hc (by
      simp only [List.cons_append, List.mem_cons, List.mem_append] at h ⊢; tauto)
    have hn1 := List.nodup_cons.mp (by simpa only [List.cons_append] using hn)
    have hab : a ≠ b := fun h => hn1.1 (by simp [h])
    have ha_as : a ∉ as := fun h => hn1.1 (by simp [h])
    have ha_bs : a ∉ bs := fun h => hn1.1 (by simp [h])
    have hn2 := List.nodup_cons.mp (List.nodup_append_comm.mp hn1.2)
    have hb_bs : b ∉ bs := fun h => hn2.1 (by simp [h])
    have hb_as : b ∉ as := fun h => hn2.1 (by simp [h])
    have hn' : (as ++ bs).Nodup := hn1.2.sublist ((List.sublist_cons_self b bs).append_left as)
    have hl' : as.length = bs.length := by simpa using hl
    have hnd : [c, a, b].Nodup := by simp [hca, hcb, hab]
    rw [swapLayer, ECDSAAdd.run_append]
    have hm0 : ECDSAAdd.measurementCount (cswap c a b) = 0 := rfl
    rw [hm0, List.take_zero, List.drop_zero]
    obtain ⟨hp, hf, hA, hB⟩ := cswap_correct c a b hnd s List.nil
    obtain ⟨ihp, ihf, ihz⟩ := swapLayer_run c as bs hc' hn' hl' (ECDSAAdd.run (cswap c a b) List.nil s) m
    refine ⟨ihp.trans hp, ?_, ?_⟩
    · intro w hw1 hw2
      have hwa : w ≠ a := fun h => hw1 (by simp [h])
      have hwb : w ≠ b := fun h => hw2 (by simp [h])
      rw [ihf w (fun h => hw1 (by simp [h])) (fun h => hw2 (by simp [h])), hf w hwa hwb]
    · intro i ha hb
      cases i with
      | zero =>
        simp only [List.getElem_cons_zero]
        rw [ihf a ha_as ha_bs, ihf b hb_as hb_bs, hA, hB]
        exact ⟨rfl, rfl⟩
      | succ j =>
        simp only [List.getElem_cons_succ]
        have hja : j < as.length := by simpa using ha
        have hjb : j < bs.length := by simpa using hb
        obtain ⟨h1, h2⟩ := ihz j hja hjb
        have hma : getElem as j hja ∈ as := List.getElem_mem hja
        have hmb : getElem bs j hjb ∈ bs := List.getElem_mem hjb
        rw [h1, h2, hf c hca hcb, hf (getElem as j hja) (fun h => ha_as (h ▸ hma)) (fun h => hb_as (h ▸ hma)),
          hf (getElem bs j hjb) (fun h => ha_bs (h ▸ hmb)) (fun h => hb_bs (h ▸ hmb))]
        exact ⟨rfl, rfl⟩

/-! ### Fast sites -/

/-- A masked site with three garbage registers aligned with its ports. -/
structure FastSite (n : Nat) where
  site : MaskedSite n
  g1 : List Wire
  g2 : List Wire
  g3 : List Wire

/-- Ports of one register, reading row `rowOf a` at the compiled address `a`. -/
def regPorts {n} (rowOf : Nat → Nat) (ports : List (LookupPort n)) (g : List Wire) :
    List (LookupPort n) :=
  List.zipWith (fun (p : LookupPort n) (w : Wire) => ⟨fun a => p.ref (rowOf a), p.value, w⟩) ports g

theorem regPorts_targets {n} (rowOf : Nat → Nat) : ∀ (ports : List (LookupPort n)) (g : List Wire),
    g.length = ports.length → portTargets (regPorts rowOf ports g) = g
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | p :: ps, w :: g, h => by
    have e : regPorts rowOf (p :: ps) (w :: g) =
        ⟨fun a => p.ref (rowOf a), p.value, w⟩ :: regPorts rowOf ps g := rfl
    rw [e]
    simp only [portTargets, List.map_cons]
    exact congrArg (List.cons w) (regPorts_targets rowOf ps g (by simpa using h))

namespace FastSite
variable {n : Nat} (f : FastSite n)

def garb : List Wire := f.g1 ++ f.g2 ++ f.g3
def ghot (i : Fin 256) : Wire := f.g1.headD 0 + i.val

def rowOf1 (a : Nat) : Nat := 4 * (a / 4) + (1 - a % 2)
def rowOf2 (a : Nat) : Nat := 4 * (a / 4) + 2 * (1 - a / 2 % 2) + a % 2
def rowOf3 (a : Nat) : Nat := 4 * (a / 4) + 3 - a % 2

def selPorts : List (LookupPort n) :=
  f.site.ports.map (fun p => ⟨fun h => p.ref (4 * h), p.value, p.target⟩) ++
  regPorts (fun h => 4 * h + 1) f.site.ports f.g1 ++ regPorts (fun h => 4 * h + 2) f.site.ports f.g2 ++
  regPorts (fun h => 4 * h + 3) f.site.ports f.g3

def garbPorts : List (LookupPort n) :=
  regPorts rowOf1 f.site.ports f.g1 ++ regPorts rowOf2 f.site.ports f.g2 ++ regPorts rowOf3 f.site.ports f.g3

def swapNet : ECDSAAdd.Program :=
  swapLayer 855 (portTargets f.site.ports) f.g1 ++ swapLayer 855 f.g2 f.g3 ++
    swapLayer 856 (portTargets f.site.ports) f.g2

def selCode : WCode n := [.lookup (some f.site.guard) f.selPorts]

end FastSite

def selBits : List Wire := List.range' 857 13 ++ [871]
def selPaths : List Wire := List.range' 14834 13 ++ [14848]
/-- The clear path bank of the garbage clears: the first eight bank wires (`bank15.hp`). -/
def bankHp : List Wire := List.range' 14832 8

theorem windowBits_eq : windowBits = 855 :: 856 :: selBits := rfl

/-- Geometry of a fast site at width 15. -/
structure FastGeometry {n} (f : FastSite n) : Prop where
  site : SiteGeoP bank15 f.site
  len1 : f.g1.length = f.site.ports.length
  len2 : f.g2.length = f.site.ports.length
  len3 : f.g3.length = f.site.ports.length
  nodup : (portTargets f.site.ports ++ f.garb).Nodup
  bounds : ∀ w ∈ f.garb, 14115 ≤ w ∧ oldWork w
  free : ∀ w ∈ f.garb, (w < 14832 ∨ 14847 ≤ w) ∧ w ≠ 14848
  head : f.g1.headD 0 ∈ f.g1
  bank : ∀ i : Fin 256, f.ghot i ∈ f.g1

namespace FastSite
variable {n : Nat} (f : FastSite n)

@[simp] theorem portTargets_append (a b : List (LookupPort n)) : portTargets (a ++ b) = portTargets a ++ portTargets b := by
  simp [portTargets]

theorem selPorts_targets (hg : FastGeometry f) : portTargets f.selPorts = portTargets f.site.ports ++ f.garb := by
  simp only [selPorts, portTargets_append, regPorts_targets _ _ _ hg.len1, regPorts_targets _ _ _ hg.len2,
    regPorts_targets _ _ _ hg.len3, garb, List.append_assoc]
  congr 1
  simp [portTargets, List.map_map, Function.comp_def]

theorem garbPorts_targets (hg : FastGeometry f) : portTargets f.garbPorts = f.garb := by
  simp only [garbPorts, portTargets_append, regPorts_targets _ _ _ hg.len1, regPorts_targets _ _ _ hg.len2,
    regPorts_targets _ _ _ hg.len3, garb]

theorem garbPorts_length (hg : FastGeometry f) : f.garbPorts.length = f.garb.length := by
  have h := congrArg List.length (garbPorts_targets f hg)
  simpa [portTargets] using h

theorem selPorts_length (hg : FastGeometry f) : f.selPorts.length = 4 * f.site.ports.length := by
  have h := congrArg List.length (selPorts_targets f hg)
  simp only [portTargets, List.length_map, List.length_append, garb, hg.len1, hg.len2, hg.len3] at h
  omega

theorem garb_length (hg : FastGeometry f) : f.garb.length = 3 * f.site.ports.length := by
  simp only [garb, List.length_append, hg.len1, hg.len2, hg.len3]
  omega

theorem swapNet_meas : ECDSAAdd.measurementCount f.swapNet = 0 := by
  simp [swapNet, ECDSAAdd.measurementCount_append, swapLayer_meas]

theorem swapNet_toff (hg : FastGeometry f) : ECDSAAdd.toffoliCount f.swapNet = 3 * f.site.ports.length := by
  have ht : (portTargets f.site.ports).length = f.site.ports.length := by simp [portTargets]
  simp only [swapNet, ECDSAAdd.toffoliCount_append, swapLayer_toff, ht, hg.len1, hg.len2, hg.len3, Nat.min_self]
  omega

theorem swapNet_slots (hg : FastGeometry f) : ECDSAAdd.Challenge.gateSlots f.swapNet = 9 * f.site.ports.length := by
  have ht : (portTargets f.site.ports).length = f.site.ports.length := by simp [portTargets]
  simp only [swapNet, ECDSAAdd.Challenge.gateSlots_append, swapLayer_slots, ht, hg.len1, hg.len2, hg.len3, Nat.min_self]
  omega

theorem swapNet_wires : ECDSAAdd.wires f.swapNet ⊆ (855 :: 856 :: portTargets f.site.ports ++ f.garb).toFinset := by
  simp only [swapNet, ECDSAAdd.wires_append]
  refine Finset.union_subset (Finset.union_subset ?_ ?_) ?_
  · intro w hw
    have h := swapLayer_wires 855 _ _ hw
    simp only [List.cons_append, List.mem_toFinset, List.mem_cons, List.mem_append, garb] at h ⊢
    tauto
  · intro w hw
    have h := swapLayer_wires 855 _ _ hw
    simp only [List.cons_append, List.mem_toFinset, List.mem_cons, List.mem_append, garb] at h ⊢
    tauto
  · intro w hw
    have h := swapLayer_wires 856 _ _ hw
    simp only [List.cons_append, List.mem_toFinset, List.mem_cons, List.mem_append, garb] at h ⊢
    tauto

/-- Facts drawn from the geometry. -/
theorem facts (hg : FastGeometry f) :
    (portTargets f.site.ports).Nodup ∧ (∀ w ∈ portTargets f.site.ports, 14115 ≤ w ∧ oldWork w) ∧
    (f.site.guard = 14113 ∨ f.site.guard = 10015) ∧ f.site.ports.length ≤ 771 ∧
    f.garb.Nodup ∧ (∀ w ∈ f.garb, w ∉ portTargets f.site.ports) ∧
    (∀ w ∈ portTargets f.site.ports ++ f.garb, 14115 ≤ w ∧ oldWork w) := by
  obtain ⟨hn, hbd, -, -, -, hgd, hlen⟩ := kind_facts f.site hg.site.kind
  have hnd := List.nodup_append.mp hg.nodup
  refine ⟨hn, hbd, hgd, hlen, hnd.2.1, ?_, ?_⟩
  · intro w hw hm
    exact hnd.2.2 w hm w hw rfl
  · intro w hw
    rcases List.mem_append.mp hw with h | h
    · exact hbd w h
    · exact hg.bounds w h

theorem garb_nodup (hg : FastGeometry f) : f.garb.Nodup := (facts f hg).2.2.2.2.1

theorem g1_sub : ∀ w ∈ f.g1, w ∈ f.garb := fun w hw => by simp [garb, hw]
theorem g2_sub : ∀ w ∈ f.g2, w ∈ f.garb := fun w hw => by simp [garb, hw]
theorem g3_sub : ∀ w ∈ f.g3, w ∈ f.garb := fun w hw => by simp [garb, hw]

theorem guard_lt (hg : FastGeometry f) : f.site.guard < 14115 := by
  rcases (facts f hg).2.2.1 with h | h <;> rw [h] <;> decide

theorem bank_not_targets (hg : FastGeometry f) : ∀ w ∈ pathBank, w ∉ portTargets f.site.ports := by
  intro w hw ht
  have hlast := hg.site.placed (.lookup (some f.site.guard) f.site.ports) (by simp [MaskedSite.code])
  dsimp only [Placed] at hlast
  exact List.disjoint_left.mp hlast.2.2
    (show w ∈ windowRoot :: lookupRoot windowRoot (some f.site.guard) :: bank15.bits ++ bank15.paths by
      simp [bank15, hw]) ht

theorem bank_not_garb (hg : FastGeometry f) : ∀ w ∈ pathBank, w ∉ f.garb := by
  intro w hw hm
  have := hg.free w hm
  have hbd := (hg.bounds w hm).1
  simp only [pathBank, List.mem_range'_1, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
  dsimp only [Wire] at *
  omega

theorem sel_free (hg : FastGeometry f) : ∀ w ∈ portTargets f.site.ports ++ f.garb, (w < 14832 ∨ 14847 ≤ w) ∧ w ≠ 14848 := by
  intro w hw
  by_contra h
  have hb : w ∈ pathBank := by
    simp only [pathBank, List.mem_range'_1, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; dsimp only [Wire] at *; omega
  rcases List.mem_append.mp hw with h1 | h1
  · exact bank_not_targets f hg w hb h1
  · exact bank_not_garb f hg w hb h1

theorem site_bank_layout (hg : FastGeometry f) : (tableAddressTree high 0 1).Layout f.site.guard bankHp := by
  apply tableAddressTree_layout _ _ _ _ _ (by decide +kernel)
  rcases (facts f hg).2.2.1 with h | h <;> rw [h] <;> decide +kernel

end FastSite

/-! ### The compiled fast block -/

namespace FastSite
variable {n : Nat} (f : FastSite n)

def selProgram (start : Nat) := compile selBits selPaths windowRoot f.selCode start

def swapProgram (start : Nat) : Straight n start (start + 0) :=
  literalFixed f.swapNet 0 ((literal_meas (n := n) _).trans f.swapNet_meas) start

end FastSite

/-- A masked site with one garbage register aligned with its ports. -/
structure FastSite1 (n : Nat) where
  site : MaskedSite n
  g1 : List Wire

def selBits1 : List Wire := List.range' 856 14 ++ [871]
def selPaths1 : List Wire := List.range' 14833 14 ++ [14848]

theorem windowBits_eq1 : windowBits = 855 :: selBits1 := rfl

namespace FastSite1
variable {n : Nat} (f : FastSite1 n)

def garb : List Wire := f.g1
def ghot (i : Fin 256) : Wire := f.g1.headD 0 + i.val
def rowOf1 (a : Nat) : Nat := 2 * (a / 2) + (1 - a % 2)

def selPorts : List (LookupPort n) :=
  f.site.ports.map (fun p => ⟨fun h => p.ref (2 * h), p.value, p.target⟩) ++
  regPorts (fun h => 2 * h + 1) f.site.ports f.g1

def garbPorts : List (LookupPort n) := regPorts rowOf1 f.site.ports f.g1

def swapNet : ECDSAAdd.Program := swapLayer 855 (portTargets f.site.ports) f.g1

def selCode : WCode n := [.lookup (some f.site.guard) f.selPorts]

end FastSite1

/-- Geometry of a two-register fast site at width 15. -/
structure FastGeometry1 {n} (f : FastSite1 n) : Prop where
  site : SiteGeoP bank15 f.site
  len1 : f.g1.length = f.site.ports.length
  nodup : (portTargets f.site.ports ++ f.garb).Nodup
  bounds : ∀ w ∈ f.garb, 14115 ≤ w ∧ oldWork w
  free : ∀ w ∈ f.garb, (w < 14832 ∨ 14847 ≤ w) ∧ w ≠ 14848
  head : f.g1.headD 0 ∈ f.g1
  bank : ∀ i : Fin 256, f.ghot i ∈ f.g1

namespace FastSite1
variable {n : Nat} (f : FastSite1 n)

theorem selPorts_targets (hg : FastGeometry1 f) : portTargets f.selPorts = portTargets f.site.ports ++ f.garb := by
  simp only [selPorts, FastSite.portTargets_append, regPorts_targets _ _ _ hg.len1, garb]
  congr 1
  simp [portTargets, List.map_map, Function.comp_def]

theorem garbPorts_targets (hg : FastGeometry1 f) : portTargets f.garbPorts = f.garb := by
  simp only [garbPorts, regPorts_targets _ _ _ hg.len1, garb]

theorem garbPorts_length (hg : FastGeometry1 f) : f.garbPorts.length = f.garb.length := by
  have h := congrArg List.length (garbPorts_targets f hg)
  simpa [portTargets] using h

theorem selPorts_length (hg : FastGeometry1 f) : f.selPorts.length = 2 * f.site.ports.length := by
  have h := congrArg List.length (selPorts_targets f hg)
  simp only [portTargets, List.length_map, List.length_append, garb, hg.len1] at h
  omega

theorem garb_length (hg : FastGeometry1 f) : f.garb.length = f.site.ports.length := by
  simp only [garb, hg.len1]

theorem swapNet_meas : ECDSAAdd.measurementCount f.swapNet = 0 := by
  simp [swapNet, swapLayer_meas]

theorem swapNet_toff (hg : FastGeometry1 f) : ECDSAAdd.toffoliCount f.swapNet = f.site.ports.length := by
  have ht : (portTargets f.site.ports).length = f.site.ports.length := by simp [portTargets]
  simp only [swapNet, swapLayer_toff, ht, hg.len1, Nat.min_self]

theorem swapNet_slots (hg : FastGeometry1 f) : ECDSAAdd.Challenge.gateSlots f.swapNet = 3 * f.site.ports.length := by
  have ht : (portTargets f.site.ports).length = f.site.ports.length := by simp [portTargets]
  simp only [swapNet, swapLayer_slots, ht, hg.len1, Nat.min_self]

theorem swapNet_wires : ECDSAAdd.wires f.swapNet ⊆ (855 :: portTargets f.site.ports ++ f.garb).toFinset := by
  intro w hw
  have h := swapLayer_wires 855 _ _ hw
  simp only [List.cons_append, List.mem_toFinset, List.mem_cons, List.mem_append, garb] at h ⊢
  tauto

theorem facts (hg : FastGeometry1 f) :
    (portTargets f.site.ports).Nodup ∧ (∀ w ∈ portTargets f.site.ports, 14115 ≤ w ∧ oldWork w) ∧
    (f.site.guard = 14113 ∨ f.site.guard = 10015) ∧ f.site.ports.length ≤ 771 ∧
    f.garb.Nodup ∧ (∀ w ∈ f.garb, w ∉ portTargets f.site.ports) ∧
    (∀ w ∈ portTargets f.site.ports ++ f.garb, 14115 ≤ w ∧ oldWork w) := by
  obtain ⟨hn, hbd, -, -, -, hgd, hlen⟩ := kind_facts f.site hg.site.kind
  have hnd := List.nodup_append.mp hg.nodup
  refine ⟨hn, hbd, hgd, hlen, hnd.2.1, ?_, ?_⟩
  · intro w hw hm
    exact hnd.2.2 w hm w hw rfl
  · intro w hw
    rcases List.mem_append.mp hw with h | h
    · exact hbd w h
    · exact hg.bounds w h

theorem garb_nodup (hg : FastGeometry1 f) : f.garb.Nodup := (facts f hg).2.2.2.2.1

theorem guard_lt (hg : FastGeometry1 f) : f.site.guard < 14115 := by
  rcases (facts f hg).2.2.1 with h | h <;> rw [h] <;> decide

theorem bank_not_targets (hg : FastGeometry1 f) : ∀ w ∈ pathBank, w ∉ portTargets f.site.ports := by
  intro w hw ht
  have hlast := hg.site.placed (.lookup (some f.site.guard) f.site.ports) (by simp [MaskedSite.code])
  dsimp only [Placed] at hlast
  exact List.disjoint_left.mp hlast.2.2
    (show w ∈ windowRoot :: lookupRoot windowRoot (some f.site.guard) :: bank15.bits ++ bank15.paths by
      simp [bank15, hw]) ht

theorem bank_not_garb (hg : FastGeometry1 f) : ∀ w ∈ pathBank, w ∉ f.garb := by
  intro w hw hm
  have := hg.free w hm
  have hbd := (hg.bounds w hm).1
  simp only [pathBank, List.mem_range'_1, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
  dsimp only [Wire] at *
  omega

theorem sel_free (hg : FastGeometry1 f) : ∀ w ∈ portTargets f.site.ports ++ f.garb, (w < 14832 ∨ 14847 ≤ w) ∧ w ≠ 14848 := by
  intro w hw
  by_contra h
  have hb : w ∈ pathBank := by
    simp only [pathBank, List.mem_range'_1, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; dsimp only [Wire] at *; omega
  rcases List.mem_append.mp hw with h1 | h1
  · exact bank_not_targets f hg w hb h1
  · exact bank_not_garb f hg w hb h1

theorem site_bank_layout (hg : FastGeometry1 f) : (tableAddressTree high 0 1).Layout f.site.guard bankHp := by
  apply tableAddressTree_layout _ _ _ _ _ (by decide +kernel)
  rcases (facts f hg).2.2.1 with h | h <;> rw [h] <;> decide +kernel

def selProgram (start : Nat) := compile selBits1 selPaths1 windowRoot f.selCode start

def swapProgram (start : Nat) : Straight n start (start + 0) :=
  literalFixed f.swapNet 0 ((literal_meas (n := n) _).trans f.swapNet_meas) start

end FastSite1

end
end ShorECDLP.Entrant.WideBank8.Fast16
end
/-! ### Semantics of the fast load -/

section
namespace ShorECDLP.Entrant.WideBank8.Fast16
open ShorECDLP.Entrant.WideSigned
open AndGadget WEXCredit Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup PathShare
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

theorem mem_regPorts {n} (rowOf : Nat → Nat) (ports : List (LookupPort n)) (g : List Wire)
    (i : Nat) (hi : i < ports.length) (hgi : i < g.length) :
    (⟨fun a => (getElem ports i hi).ref (rowOf a), (getElem ports i hi).value, getElem g i hgi⟩ : LookupPort n) ∈
      regPorts rowOf ports g := by
  rw [List.mem_iff_getElem]
  refine ⟨i, by simp [regPorts]; omega, ?_⟩
  simp [regPorts, List.getElem_zipWith]

theorem of_mem_regPorts {n} (rowOf : Nat → Nat) (ports : List (LookupPort n)) (g : List Wire)
    (q : LookupPort n) (hq : q ∈ regPorts rowOf ports g) :
    ∃ i, ∃ (hi : i < ports.length) (hgi : i < g.length),
      q = ⟨fun a => (getElem ports i hi).ref (rowOf a), (getElem ports i hi).value, getElem g i hgi⟩ := by
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hq
  simp only [regPorts, List.length_zipWith] at hi
  refine ⟨i, by omega, by omega, ?_⟩
  rw [← he]
  simp [regPorts, List.getElem_zipWith]

namespace FastSite
variable {n : Nat} (f : FastSite n)

/-- Register `g`, aligned with `ports`, holds the word of row `r` under flag `flag`. -/
def Holds (read : ConstantBit n → Bool) (ports : List (LookupPort n)) (g : List Wire) (r : Nat)
    (flag : Bool) (s : BasisState) : Prop :=
  ∀ i (hi : i < ports.length) (hgi : i < g.length),
    s (getElem g i hgi) = (flag && decide (read ((getElem ports i hi).ref r) = (getElem ports i hi).value))

theorem holds_frame (read : ConstantBit n → Bool) (ports : List (LookupPort n)) (g : List Wire) (r : Nat)
    (flag : Bool) (s t : BasisState) (h : Holds read ports g r flag s) (hf : ∀ w ∈ g, t w = s w) :
    Holds read ports g r flag t := by
  intro i hi hgi
  rw [hf _ (List.getElem_mem hgi)]
  exact h i hi hgi

theorem holds_row (read : ConstantBit n → Bool) (ports : List (LookupPort n)) (g : List Wire) (r r' : Nat)
    (flag : Bool) (s : BasisState) (h : Holds read ports g r flag s) (he : r = r') :
    Holds read ports g r' flag s := he ▸ h

theorem holds_swap (read : ConstantBit n → Bool) (ports : List (LookupPort n)) (as bs : List Wire)
    (c : Wire) (r₁ r₂ : Nat) (flag : Bool) (s : ECDSAAdd.State) (m : List Bool)
    (hc : c ∉ as ++ bs) (hn : (as ++ bs).Nodup) (ha : as.length = ports.length) (hb : bs.length = ports.length)
    (h1 : Holds read ports as r₁ flag s.basis) (h2 : Holds read ports bs r₂ flag s.basis) :
    Holds read ports as (if s.basis c then r₂ else r₁) flag (ECDSAAdd.run (swapLayer c as bs) m s).basis ∧
    Holds read ports bs (if s.basis c then r₁ else r₂) flag (ECDSAAdd.run (swapLayer c as bs) m s).basis := by
  obtain ⟨-, -, hz⟩ := swapLayer_run c as bs hc hn (ha.trans hb.symm) s m
  constructor
  · intro i hi hai
    have hbi : i < bs.length := by omega
    rw [(hz i hai hbi).1]
    cases s.basis c
    · simpa using h1 i hi hai
    · simpa using h2 i hi hbi
  · intro i hi hbi
    have hai : i < as.length := by omega
    rw [(hz i hai hbi).2]
    cases s.basis c
    · simpa using h2 i hi hbi
    · simpa using h1 i hi hai

theorem sel_valid (a : Nat) (st : ECDSAAdd.State)
    (hs : SimulationValid windowBits pathBank windowRoot a st) :
    SimulationValid selBits selPaths windowRoot (tableAddressValue selBits st.basis) st := by
  refine ⟨?_, rfl, hs.2.2⟩
  intro w hw
  apply hs.1
  simp only [selPaths, pathBank, List.mem_range'_1, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
  dsimp only [Wire] at *
  omega

theorem address_split (st : BasisState) :
    tableAddressValue windowBits st = (st 855).toNat + 2 * ((st 856).toNat + 2 * tableAddressValue selBits st) := by
  simp only [windowBits_eq, tableAddressValue]

theorem swapNet_run (s : ECDSAAdd.State) :
    ECDSAAdd.run f.swapNet List.nil s =
      ECDSAAdd.run (swapLayer 856 (portTargets f.site.ports) f.g2) List.nil
        (ECDSAAdd.run (swapLayer 855 f.g2 f.g3) List.nil
          (ECDSAAdd.run (swapLayer 855 (portTargets f.site.ports) f.g1) List.nil s)) := by
  simp only [swapNet, ECDSAAdd.run_append, ECDSAAdd.measurementCount_append, swapLayer_meas,
    Nat.add_zero, List.take_zero, List.drop_zero, List.take_nil, List.drop_nil]

/-- Pairwise disjointness of the four registers. -/
theorem disjoints (hg : FastGeometry f) :
    (∀ w ∈ f.g1, w ∉ portTargets f.site.ports) ∧ (∀ w ∈ f.g2, w ∉ portTargets f.site.ports) ∧
    (∀ w ∈ f.g3, w ∉ portTargets f.site.ports) ∧ (∀ w ∈ f.g2, w ∉ f.g1) ∧ (∀ w ∈ f.g3, w ∉ f.g1) ∧
    (∀ w ∈ f.g3, w ∉ f.g2) := by
  have h := List.nodup_append.mp hg.nodup
  have hd : ∀ w ∈ f.garb, w ∉ portTargets f.site.ports := fun w hw hm => h.2.2 w hm w hw rfl
  have h' := List.nodup_append.mp h.2.1
  have h'' := List.nodup_append.mp h'.1
  refine ⟨fun w hw => hd w (g1_sub f w hw), fun w hw => hd w (g2_sub f w hw), fun w hw => hd w (g3_sub f w hw),
    fun w hw h1 => h''.2.2 w h1 w hw rfl, fun w hw h1 => ?_, fun w hw h2 => ?_⟩
  · exact h'.2.2 w (List.mem_append_left _ h1) w hw rfl
  · exact h'.2.2 w (List.mem_append_right _ h2) w hw rfl

/-- The state after the select traversal and the swap network. -/
theorem load_state (read : ConstantBit n → Bool) (hg : FastGeometry f) (a : Nat) (st : ECDSAAdd.State)
    (hs : SimulationValid windowBits pathBank windowRoot a st)
    (hc : Clean (portTargets f.site.ports ++ f.garb) st.basis) :
    let s₂ := ECDSAAdd.run f.swapNet List.nil
      (ECDSAAdd.run ((specialize f.selCode (tableAddressValue selBits st.basis)).instantiate read) List.nil st)
    s₂.phase = st.phase ∧
    (∀ w, w ∉ portTargets f.site.ports → w ∉ f.garb → s₂.basis w = st.basis w) ∧
    Holds read f.site.ports (portTargets f.site.ports) a (st.basis f.site.guard) s₂.basis ∧
    Holds read f.site.ports f.g1 (rowOf1 a) (st.basis f.site.guard) s₂.basis ∧
    Holds read f.site.ports f.g2 (rowOf2 a) (st.basis f.site.guard) s₂.basis ∧
    Holds read f.site.ports f.g3 (rowOf3 a) (st.basis f.site.guard) s₂.basis := by
  intro s₂
  obtain ⟨hn, hbd, hgd, hlen, hgn, hdisj, hall⟩ := facts f hg
  obtain ⟨d1, d2, d3, d21, d31, d32⟩ := disjoints f hg
  have hsel := selPorts_targets f hg
  have hselnd : (portTargets f.selPorts).Nodup := by rw [hsel]; exact hg.nodup
  have hglt := guard_lt f hg
  have hguard : f.site.guard ∉ portTargets f.selPorts := by
    rw [hsel]; intro h; have := (hall _ h).1; dsimp only [Wire] at *; omega
  have lt : (portTargets f.site.ports).length = f.site.ports.length := by simp [portTargets]
  have g1s := g1_sub f
  have g2s := g2_sub f
  have g3s := g3_sub f
  -- stage 1
  set h := tableAddressValue selBits st.basis with hh
  have e1 : specialize f.selCode h = portTemplate (some f.site.guard) f.selPorts h := by
    simp [FastSite.selCode, specialize, WInstr.specialize]
  set s₁ := ECDSAAdd.run ((specialize f.selCode h).instantiate read) List.nil st with hs₁
  have r1 : s₁ = ⟨st.phase, tableXorState (portMask read f.selPorts h) (st.basis f.site.guard) st.basis⟩ := by
    rw [hs₁, e1]
    exact portTemplate_run read (some f.site.guard) f.selPorts h windowRoot List.nil st hselnd hguard hs.2.2
  have sel_at : ∀ q ∈ f.selPorts, s₁.basis q.target =
      (st.basis f.site.guard && decide (read (q.ref h) = q.value)) := by
    intro q hq
    rw [r1]
    show tableXorState _ _ _ q.target = _
    simp only [tableXorState]
    rw [port_selected read f.selPorts h hselnd q hq]
    have hz : st.basis q.target = false := by
      have hm : q.target ∈ portTargets f.selPorts := List.mem_map.mpr ⟨q, hq, rfl⟩
      rw [hsel] at hm
      exact hc _ hm
    rw [hz]
    simp
  have frame1 : ∀ w, w ∉ portTargets f.site.ports → w ∉ f.garb → s₁.basis w = st.basis w := by
    intro w h1 h2
    rw [r1]
    show tableXorState _ _ _ w = _
    apply tableXorState_outside
    intro hm
    have hm' : w ∈ portTargets f.selPorts := tableBitsMask_subset _ _ hm
    rw [hsel] at hm'
    rcases List.mem_append.mp hm' with h | h
    · exact h1 h
    · exact h2 h
  have H0 : Holds read f.site.ports (portTargets f.site.ports) (4*h) (st.basis f.site.guard) s₁.basis := by
    intro i hi hgi
    have hq : (⟨fun h => (getElem f.site.ports i hi).ref (4*h), (getElem f.site.ports i hi).value,
        (getElem f.site.ports i hi).target⟩ : LookupPort n) ∈ f.selPorts := by
      simp only [FastSite.selPorts, List.mem_append]
      left; left; left
      exact List.mem_map.mpr ⟨getElem f.site.ports i hi, List.getElem_mem hi, rfl⟩
    have := sel_at _ hq
    simpa [portTargets, List.getElem_map] using this
  have H1 : Holds read f.site.ports f.g1 (4*h+1) (st.basis f.site.guard) s₁.basis := by
    intro i hi hgi
    have hq := mem_regPorts (fun h => 4*h+1) f.site.ports f.g1 i hi hgi
    exact sel_at _ (by simp only [FastSite.selPorts, List.mem_append]; left; left; right; exact hq)
  have H2 : Holds read f.site.ports f.g2 (4*h+2) (st.basis f.site.guard) s₁.basis := by
    intro i hi hgi
    have hq := mem_regPorts (fun h => 4*h+2) f.site.ports f.g2 i hi hgi
    exact sel_at _ (by simp only [FastSite.selPorts, List.mem_append]; left; right; exact hq)
  have H3 : Holds read f.site.ports f.g3 (4*h+3) (st.basis f.site.guard) s₁.basis := by
    intro i hi hgi
    have hq := mem_regPorts (fun h => 4*h+3) f.site.ports f.g3 i hi hgi
    exact sel_at _ (by simp only [FastSite.selPorts, List.mem_append]; right; exact hq)
  -- stage 2
  have c855 : (855 : Wire) ∉ portTargets f.site.ports ++ f.garb := fun h => by
    have := (hall _ h).1; dsimp only [Wire] at *; omega
  have c856 : (856 : Wire) ∉ portTargets f.site.ports ++ f.garb := fun h => by
    have := (hall _ h).1; dsimp only [Wire] at *; omega
  have sub1 : List.Sublist (portTargets f.site.ports ++ f.g1) (portTargets f.site.ports ++ f.garb) :=
    ((List.sublist_append_left f.g1 f.g2).trans (List.sublist_append_left (f.g1 ++ f.g2) f.g3)).append_left _
  have sub2 : List.Sublist (f.g2 ++ f.g3) (portTargets f.site.ports ++ f.garb) := by
    have h23 : List.Sublist (f.g2 ++ f.g3) f.garb := by
      simp only [garb, List.append_assoc]
      exact List.sublist_append_right f.g1 (f.g2 ++ f.g3)
    exact h23.trans (List.sublist_append_right _ _)
  have sub3 : List.Sublist (portTargets f.site.ports ++ f.g2) (portTargets f.site.ports ++ f.garb) :=
    ((List.sublist_append_right f.g1 f.g2).trans (List.sublist_append_left (f.g1 ++ f.g2) f.g3)).append_left _
  have nd1 := hg.nodup.sublist sub1
  have nd2 := hg.nodup.sublist sub2
  have nd3 := hg.nodup.sublist sub3
  have c1 : (855 : Wire) ∉ portTargets f.site.ports ++ f.g1 := fun h => c855 (sub1.subset h)
  have c2 : (855 : Wire) ∉ f.g2 ++ f.g3 := fun h => c855 (sub2.subset h)
  have c3 : (856 : Wire) ∉ portTargets f.site.ports ++ f.g2 := fun h => c856 (sub3.subset h)
  have n855t : (855 : Wire) ∉ portTargets f.site.ports := fun h => c855 (List.mem_append_left _ h)
  have n855g : (855 : Wire) ∉ f.garb := fun h => c855 (List.mem_append_right _ h)
  have n856t : (856 : Wire) ∉ portTargets f.site.ports := fun h => c856 (List.mem_append_left _ h)
  have n856g : (856 : Wire) ∉ f.garb := fun h => c856 (List.mem_append_right _ h)
  set t₁ := ECDSAAdd.run (swapLayer 855 (portTargets f.site.ports) f.g1) List.nil s₁ with ht₁
  set t₂ := ECDSAAdd.run (swapLayer 855 f.g2 f.g3) List.nil t₁ with ht₂
  have hs₂ : s₂ = ECDSAAdd.run (swapLayer 856 (portTargets f.site.ports) f.g2) List.nil t₂ := by
    show ECDSAAdd.run f.swapNet List.nil s₁ = _
    rw [swapNet_run]
  obtain ⟨p1, fr1, -⟩ := swapLayer_run 855 _ _ c1 nd1 (by rw [lt, hg.len1]) s₁ List.nil
  obtain ⟨p2, fr2, -⟩ := swapLayer_run 855 _ _ c2 nd2 (by rw [hg.len2, hg.len3]) t₁ List.nil
  obtain ⟨p3, fr3, -⟩ := swapLayer_run 856 _ _ c3 nd3 (by rw [lt, hg.len2]) t₂ List.nil
  have frame : ∀ w, w ∉ portTargets f.site.ports → w ∉ f.garb → s₂.basis w = st.basis w := by
    intro w h1 h2
    rw [hs₂, fr3 w h1 (fun h => h2 (g2s w h)), ht₂, fr2 w (fun h => h2 (g2s w h)) (fun h => h2 (g3s w h)),
      ht₁, fr1 w h1 (fun h => h2 (g1s w h)), frame1 w h1 h2]
  have b0_1 : s₁.basis 855 = st.basis 855 := frame1 _ n855t n855g
  have b0_2 : t₁.basis 855 = st.basis 855 := by
    rw [ht₁, fr1 855 n855t (fun h => n855g (g1s _ h)), b0_1]
  have b1_3 : t₂.basis 856 = st.basis 856 := by
    rw [ht₂, fr2 856 (fun h => n856g (g2s _ h)) (fun h => n856g (g3s _ h)),
      ht₁, fr1 856 n856t (fun h => n856g (g1s _ h)), frame1 856 n856t n856g]
  -- layer 1: targets and g1
  obtain ⟨T1, G1⟩ := holds_swap read f.site.ports _ _ 855 (4*h) (4*h+1) (st.basis f.site.guard) s₁ List.nil
    c1 nd1 lt hg.len1 H0 H1
  rw [b0_1] at T1 G1
  have H2' := holds_frame read f.site.ports f.g2 _ _ _ _ H2
    (fun w hw => fr1 w (d2 w hw) (d21 w hw))
  have H3' := holds_frame read f.site.ports f.g3 _ _ _ _ H3
    (fun w hw => fr1 w (d3 w hw) (d31 w hw))
  -- layer 2: g2 and g3
  obtain ⟨G2, G3⟩ := holds_swap read f.site.ports _ _ 855 (4*h+2) (4*h+3) (st.basis f.site.guard) t₁ List.nil
    c2 nd2 hg.len2 hg.len3 H2' H3'
  rw [b0_2] at G2 G3
  have T2 := holds_frame read f.site.ports _ _ _ _ _ T1
    (fun w hw => fr2 w (fun h => d2 _ h hw) (fun h => d3 _ h hw))
  have G1' := holds_frame read f.site.ports f.g1 _ _ _ _ G1
    (fun w hw => fr2 w (fun h => d21 _ h hw) (fun h => d31 _ h hw))
  -- layer 3: targets and g2
  obtain ⟨T3, G2'⟩ := holds_swap read f.site.ports _ _ 856 _ _ (st.basis f.site.guard) t₂ List.nil
    c3 nd3 lt hg.len2 T2 G2
  rw [b1_3] at T3 G2'
  have G1'' := holds_frame read f.site.ports f.g1 _ _ _ _ G1'
    (fun w hw => fr3 w (d1 w hw) (fun h => d21 _ h hw))
  have G3' := holds_frame read f.site.ports f.g3 _ _ _ _ G3
    (fun w hw => fr3 w (d3 w hw) (d32 w hw))
  rw [← hs₂] at T3 G2' G1'' G3'
  -- rows
  have ha : a = (st.basis 855).toNat + 2 * ((st.basis 856).toNat + 2 * h) := by
    rw [← hs.2.1, address_split, ← hh]
  have hp : s₂.phase = st.phase := by rw [hs₂, p3, ht₂, p2, ht₁, p1, r1]
  refine ⟨hp, frame, ?_, ?_, ?_, ?_⟩
  · refine holds_row read _ _ _ _ _ _ T3 ?_
    cases hb0 : st.basis 855 <;> cases hb1 : st.basis 856 <;> simp [hb0, hb1] at ha ⊢ <;> omega
  · refine holds_row read _ _ _ _ _ _ G1'' ?_
    cases hb0 : st.basis 855 <;> cases hb1 : st.basis 856 <;> simp [hb0, hb1, rowOf1] at ha ⊢ <;> omega
  · refine holds_row read _ _ _ _ _ _ G2' ?_
    cases hb0 : st.basis 855 <;> cases hb1 : st.basis 856 <;> simp [hb0, hb1, rowOf2] at ha ⊢ <;> omega
  · refine holds_row read _ _ _ _ _ _ G3' ?_
    cases hb0 : st.basis 855 <;> cases hb1 : st.basis 856 <;> simp [hb0, hb1, rowOf3] at ha ⊢ <;> omega

/-- Clearing the garbage leaves exactly the reference load. -/
theorem load_clear_eq (read : ConstantBit n → Bool) (hg : FastGeometry f) (a : Nat) (st : ECDSAAdd.State)
    (hs : SimulationValid windowBits pathBank windowRoot a st)
    (hc : Clean (portTargets f.site.ports ++ f.garb) st.basis) :
    let s₂ := ECDSAAdd.run f.swapNet List.nil
      (ECDSAAdd.run ((specialize f.selCode (tableAddressValue selBits st.basis)).instantiate read) List.nil st)
    clearRegister f.garb s₂.basis = tableXorState (portMask read f.site.ports a) (st.basis f.site.guard) st.basis := by
  intro s₂
  obtain ⟨hp, frame, T, G1, G2, G3⟩ := load_state f read hg a st hs hc
  obtain ⟨hn, hbd, hgd, hlen, hgn, hdisj, hall⟩ := facts f hg
  funext w
  by_cases hw : w ∈ f.garb
  · rw [clearRegister_clean _ _ w hw, tableXorState_outside]
    · exact (hc w (List.mem_append_right _ hw)).symm
    · intro hm
      exact hdisj w hw (tableBitsMask_subset _ _ hm)
  · rw [MeasuredClear.clearRegister_frame _ _ _ hw]
    by_cases ht : w ∈ portTargets f.site.ports
    · unfold portTargets at ht
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ht
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
      have hT := T i hi (by simpa [portTargets] using hi)
      simp only [portTargets, List.getElem_map] at hT
      rw [hT]
      simp only [tableXorState]
      rw [port_selected read f.site.ports a hn _ (List.getElem_mem hi),
        hc _ (List.mem_append_left _ ht)]
      simp
    · rw [frame w ht hw, tableXorState_outside]
      intro hm
      exact ht (tableBitsMask_subset _ _ hm)

end FastSite

namespace FastSite1
variable {n : Nat} (f : FastSite1 n)
/-! Semantics. -/

theorem sel_valid (a : Nat) (st : ECDSAAdd.State)
    (hs : SimulationValid windowBits pathBank windowRoot a st) :
    SimulationValid selBits1 selPaths1 windowRoot (tableAddressValue selBits1 st.basis) st := by
  refine ⟨?_, rfl, hs.2.2⟩
  intro w hw
  apply hs.1
  simp only [selPaths1, pathBank, List.mem_range'_1, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
  dsimp only [Wire] at *
  omega

theorem address_split (st : BasisState) :
    tableAddressValue windowBits st = (st 855).toNat + 2 * tableAddressValue selBits1 st := by
  simp only [windowBits_eq1, tableAddressValue]

theorem disjoints (hg : FastGeometry1 f) : ∀ w ∈ f.g1, w ∉ portTargets f.site.ports := by
  have h := List.nodup_append.mp hg.nodup
  exact fun w hw hm => h.2.2 w hm w hw rfl

/-- The state after the select traversal and the swap layer. -/
theorem load_state (read : ConstantBit n → Bool) (hg : FastGeometry1 f) (a : Nat) (st : ECDSAAdd.State)
    (hs : SimulationValid windowBits pathBank windowRoot a st)
    (hc : Clean (portTargets f.site.ports ++ f.garb) st.basis) :
    let s₂ := ECDSAAdd.run f.swapNet List.nil
      (ECDSAAdd.run ((specialize f.selCode (tableAddressValue selBits1 st.basis)).instantiate read) List.nil st)
    s₂.phase = st.phase ∧
    (∀ w, w ∉ portTargets f.site.ports → w ∉ f.garb → s₂.basis w = st.basis w) ∧
    FastSite.Holds read f.site.ports (portTargets f.site.ports) a (st.basis f.site.guard) s₂.basis ∧
    FastSite.Holds read f.site.ports f.g1 (rowOf1 a) (st.basis f.site.guard) s₂.basis := by
  intro s₂
  obtain ⟨hn, hbd, hgd, hlen, hgn, hdisj, hall⟩ := facts f hg
  have d1 := disjoints f hg
  have hsel := selPorts_targets f hg
  have hselnd : (portTargets f.selPorts).Nodup := by rw [hsel]; exact hg.nodup
  have hglt := guard_lt f hg
  have hguard : f.site.guard ∉ portTargets f.selPorts := by
    rw [hsel]; intro h; have := (hall _ h).1; dsimp only [Wire] at *; omega
  have lt : (portTargets f.site.ports).length = f.site.ports.length := by simp [portTargets]
  set h := tableAddressValue selBits1 st.basis with hh
  have e1 : specialize f.selCode h = portTemplate (some f.site.guard) f.selPorts h := by
    simp [FastSite1.selCode, specialize, WInstr.specialize]
  set s₁ := ECDSAAdd.run ((specialize f.selCode h).instantiate read) List.nil st with hs₁
  have r1 : s₁ = ⟨st.phase, tableXorState (portMask read f.selPorts h) (st.basis f.site.guard) st.basis⟩ := by
    rw [hs₁, e1]
    exact portTemplate_run read (some f.site.guard) f.selPorts h windowRoot List.nil st hselnd hguard hs.2.2
  have sel_at : ∀ q ∈ f.selPorts, s₁.basis q.target =
      (st.basis f.site.guard && decide (read (q.ref h) = q.value)) := by
    intro q hq
    rw [r1]
    show tableXorState _ _ _ q.target = _
    simp only [tableXorState]
    rw [port_selected read f.selPorts h hselnd q hq]
    have hz : st.basis q.target = false := by
      have hm : q.target ∈ portTargets f.selPorts := List.mem_map.mpr ⟨q, hq, rfl⟩
      rw [hsel] at hm
      exact hc _ hm
    rw [hz]
    simp
  have frame1 : ∀ w, w ∉ portTargets f.site.ports → w ∉ f.garb → s₁.basis w = st.basis w := by
    intro w h1 h2
    rw [r1]
    show tableXorState _ _ _ w = _
    apply tableXorState_outside
    intro hm
    have hm' : w ∈ portTargets f.selPorts := tableBitsMask_subset _ _ hm
    rw [hsel] at hm'
    rcases List.mem_append.mp hm' with h | h
    · exact h1 h
    · exact h2 h
  have H0 : FastSite.Holds read f.site.ports (portTargets f.site.ports) (2*h) (st.basis f.site.guard) s₁.basis := by
    intro i hi hgi
    have hq : (⟨fun h => (getElem f.site.ports i hi).ref (2*h), (getElem f.site.ports i hi).value,
        (getElem f.site.ports i hi).target⟩ : LookupPort n) ∈ f.selPorts := by
      simp only [FastSite1.selPorts, List.mem_append]
      left
      exact List.mem_map.mpr ⟨getElem f.site.ports i hi, List.getElem_mem hi, rfl⟩
    have := sel_at _ hq
    simpa [portTargets, List.getElem_map] using this
  have H1 : FastSite.Holds read f.site.ports f.g1 (2*h+1) (st.basis f.site.guard) s₁.basis := by
    intro i hi hgi
    have hq := mem_regPorts (fun h => 2*h+1) f.site.ports f.g1 i hi hgi
    exact sel_at _ (by simp only [FastSite1.selPorts, List.mem_append]; right; exact hq)
  have c855 : (855 : Wire) ∉ portTargets f.site.ports ++ f.garb := fun h => by
    have := (hall _ h).1; dsimp only [Wire] at *; omega
  have n855t : (855 : Wire) ∉ portTargets f.site.ports := fun h => c855 (List.mem_append_left _ h)
  have n855g : (855 : Wire) ∉ f.garb := fun h => c855 (List.mem_append_right _ h)
  have c1 : (855 : Wire) ∉ portTargets f.site.ports ++ f.g1 := c855
  have nd1 : (portTargets f.site.ports ++ f.g1).Nodup := hg.nodup
  have hs₂ : s₂ = ECDSAAdd.run (swapLayer 855 (portTargets f.site.ports) f.g1) List.nil s₁ := rfl
  obtain ⟨p1, fr1, -⟩ := swapLayer_run 855 (portTargets f.site.ports) f.g1 c1 nd1 (by rw [lt, hg.len1]) s₁ List.nil
  have frame : ∀ w, w ∉ portTargets f.site.ports → w ∉ f.garb → s₂.basis w = st.basis w := by
    intro w h1 h2
    rw [hs₂, fr1 w h1 h2, frame1 w h1 h2]
  have b0_1 : s₁.basis 855 = st.basis 855 := frame1 _ n855t n855g
  obtain ⟨T1, G1⟩ := FastSite.holds_swap read f.site.ports _ _ 855 (2*h) (2*h+1) (st.basis f.site.guard) s₁ List.nil
    c1 nd1 lt hg.len1 H0 H1
  rw [b0_1] at T1 G1
  rw [← hs₂] at T1 G1
  have ha : a = (st.basis 855).toNat + 2 * h := by
    rw [← hs.2.1, address_split, ← hh]
  have hp : s₂.phase = st.phase := by rw [hs₂, p1, r1]
  refine ⟨hp, frame, ?_, ?_⟩
  · refine FastSite.holds_row read _ _ _ _ _ _ T1 ?_
    cases hb0 : st.basis 855 <;> simp [hb0] at ha ⊢ <;> omega
  · refine FastSite.holds_row read _ _ _ _ _ _ G1 ?_
    cases hb0 : st.basis 855 <;> simp [hb0, rowOf1] at ha ⊢ <;> omega

theorem load_clear_eq (read : ConstantBit n → Bool) (hg : FastGeometry1 f) (a : Nat) (st : ECDSAAdd.State)
    (hs : SimulationValid windowBits pathBank windowRoot a st)
    (hc : Clean (portTargets f.site.ports ++ f.garb) st.basis) :
    let s₂ := ECDSAAdd.run f.swapNet List.nil
      (ECDSAAdd.run ((specialize f.selCode (tableAddressValue selBits1 st.basis)).instantiate read) List.nil st)
    clearRegister f.garb s₂.basis = tableXorState (portMask read f.site.ports a) (st.basis f.site.guard) st.basis := by
  intro s₂
  obtain ⟨hp, frame, T, G1⟩ := load_state f read hg a st hs hc
  obtain ⟨hn, hbd, hgd, hlen, hgn, hdisj, hall⟩ := facts f hg
  funext w
  by_cases hw : w ∈ f.garb
  · rw [clearRegister_clean _ _ w hw, tableXorState_outside]
    · exact (hc w (List.mem_append_right _ hw)).symm
    · intro hm
      exact hdisj w hw (tableBitsMask_subset _ _ hm)
  · rw [MeasuredClear.clearRegister_frame _ _ _ hw]
    by_cases ht : w ∈ portTargets f.site.ports
    · unfold portTargets at ht
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ht
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
      have hT := T i hi (by simpa [portTargets] using hi)
      simp only [portTargets, List.getElem_map] at hT
      rw [hT]
      simp only [tableXorState]
      rw [port_selected read f.site.ports a hn _ (List.getElem_mem hi),
        hc _ (List.mem_append_left _ ht)]
      simp
    · rw [frame w ht hw, tableXorState_outside]
      intro hm
      exact ht (tableBitsMask_subset _ _ hm)

end FastSite1

end
end ShorECDLP.Entrant.WideBank8.Fast16
end
/-! ### The garbage clear and the fast block simulation -/

section
namespace ShorECDLP.Entrant.WideBank8.Fast16
open ShorECDLP.Entrant.WideSigned
open AndGadget WEXCredit Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup PathShare
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

namespace FastSite
variable {n : Nat} (f : FastSite n)

theorem sel_placed (hg : FastGeometry f) :
    Placed selBits selPaths windowRoot (WInstr.lookup (n := n) (some f.site.guard) f.selPorts) := by
  obtain ⟨hn, hbd, hgd, hlen, hgn, hdisj, hall⟩ := facts f hg
  have hglt := guard_lt f hg
  refine ⟨?_, ?_, ?_⟩
  · show (f.site.guard :: selBits ++ selPaths).Nodup
    rcases hgd with e | e <;> rw [e] <;> decide +kernel
  · rw [selPorts_targets f hg]; exact hg.nodup
  · apply List.disjoint_left.mpr
    intro w hw hm
    rw [selPorts_targets f hg] at hm
    have h1 := (hall w hm).1
    have h2 := sel_free f hg w hm
    have hr : windowRoot = 10015 := rfl
    simp only [List.mem_cons, List.mem_append, selBits, selPaths, List.mem_range'_1, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, lookupRoot,
      Option.getD, hr] at hw
    dsimp only [Wire] at *
    omega

theorem sel_layouts (hg : FastGeometry f) : LookupLayouts selBits selPaths windowRoot f.selCode :=
  pair_layouts_of_placed selBits selPaths windowRoot f.selCode (by decide)
    (fun i hi => by
      simp only [FastSite.selCode, List.mem_singleton] at hi
      subst hi
      exact placed_implies_pair _ _ _ _ (sel_placed f hg))

theorem arith_pair (hg : FastGeometry f) :
    ∀ i ∈ f.site.arithmetic, PlacedPair windowBits pathBank windowRoot i := fun i hi =>
  placed_implies_pair _ _ _ _ (hg.site.placed i (List.mem_append_left _ (List.mem_cons_of_mem _ hi)))

theorem arith_layouts (hg : FastGeometry f) :
    LookupLayouts windowBits pathBank windowRoot (normalizeW f.site.arithmetic) :=
  pair_layouts_of_placed _ _ _ _ (by simp [windowBits, pathBank])
    (pair_placed_normalize _ _ _ _ (arith_pair f hg))

theorem sel_records (hg : FastGeometry f) : codeRecords selBits selPaths windowRoot f.selCode = 16383 := by
  have h := single_lookup_records selBits selPaths windowRoot (some f.site.guard) f.selPorts (by decide)
    (sel_placed f hg).1
  simpa [FastSite.selCode] using h

theorem layer_facts (hg : FastGeometry f) :
    ((855 : Wire) ∉ portTargets f.site.ports ++ f.g1 ∧ (portTargets f.site.ports ++ f.g1).Nodup) ∧
    ((855 : Wire) ∉ f.g2 ++ f.g3 ∧ (f.g2 ++ f.g3).Nodup) ∧
    ((856 : Wire) ∉ portTargets f.site.ports ++ f.g2 ∧ (portTargets f.site.ports ++ f.g2).Nodup) := by
  obtain ⟨hn, hbd, hgd, hlen, hgn, hdisj, hall⟩ := facts f hg
  have c855 : (855 : Wire) ∉ portTargets f.site.ports ++ f.garb := fun h => by
    have := (hall _ h).1; dsimp only [Wire] at *; omega
  have c856 : (856 : Wire) ∉ portTargets f.site.ports ++ f.garb := fun h => by
    have := (hall _ h).1; dsimp only [Wire] at *; omega
  have sub1 : List.Sublist (portTargets f.site.ports ++ f.g1) (portTargets f.site.ports ++ f.garb) :=
    ((List.sublist_append_left f.g1 f.g2).trans (List.sublist_append_left (f.g1 ++ f.g2) f.g3)).append_left _
  have sub2 : List.Sublist (f.g2 ++ f.g3) (portTargets f.site.ports ++ f.garb) := by
    have h23 : List.Sublist (f.g2 ++ f.g3) f.garb := by
      simp only [garb, List.append_assoc]
      exact List.sublist_append_right f.g1 (f.g2 ++ f.g3)
    exact h23.trans (List.sublist_append_right _ _)
  have sub3 : List.Sublist (portTargets f.site.ports ++ f.g2) (portTargets f.site.ports ++ f.garb) :=
    ((List.sublist_append_right f.g1 f.g2).trans (List.sublist_append_left (f.g1 ++ f.g2) f.g3)).append_left _
  exact ⟨⟨fun h => c855 (sub1.subset h), hg.nodup.sublist sub1⟩, ⟨fun h => c855 (sub2.subset h), hg.nodup.sublist sub2⟩,
    ⟨fun h => c856 (sub3.subset h), hg.nodup.sublist sub3⟩⟩

theorem swapNet_valid (hg : FastGeometry f) : ∀ i ∈ f.swapNet, ECDSAAdd.Challenge.instructionValid i := by
  obtain ⟨⟨c1, n1⟩, ⟨c2, n2⟩, ⟨c3, n3⟩⟩ := layer_facts f hg
  intro i hi
  simp only [swapNet, List.mem_append] at hi
  rcases hi with (hi | hi) | hi
  · exact swapLayer_valid 855 _ _ c1 n1 i hi
  · exact swapLayer_valid 855 _ _ c2 n2 i hi
  · exact swapLayer_valid 856 _ _ c3 n3 i hi

/-! The garbage clear. -/

attribute [local irreducible] WEX.codeRecords lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps in

attribute [local irreducible] MeasuredClear.measuredClear8 in

/-! The staged simulation. -/

def SwapSim (read : ConstantBit n → Bool) (b : InstrumentBranch) (c : ℂ) : Prop :=
  ∀ address st, SimulationValid windowBits pathBank windowRoot address st →
    Clean (portTargets f.site.ports ++ f.garb) st.basis →
    b.kraus (Bridge.signedKet st) = c • Bridge.signedKet (ECDSAAdd.run f.swapNet List.nil
      (ECDSAAdd.run ((specialize f.selCode (tableAddressValue selBits st.basis)).instantiate read) List.nil st))

theorem swap_simulation (read : ConstantBit n → Bool) (hg : FastGeometry f) :
    ∃ cs : List ℂ, List.Forall₂ (f.SwapSim read)
      ((source read selBits selPaths windowRoot f.selCode).seq (literalSource f.swapNet)).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  have hp1 : ∀ i ∈ f.selCode, PlacedPair selBits selPaths windowRoot i := by
    intro i hi
    simp only [FastSite.selCode, List.mem_singleton] at hi
    subst hi
    exact placed_implies_pair _ _ _ _ (sel_placed f hg)
  obtain ⟨c1, a1, m1⟩ := pair_source_simulation read selBits selPaths windowRoot (by decide) f.selCode hp1
  obtain ⟨c2, a2, m2⟩ := literal_simulation f.swapNet
  refine ⟨coherentSeqCoefficients c1 c2, ?_, ?_⟩
  · rw [AdaptiveCircuit.run_seq]
    apply simulationAligned_seq a1 a2
    intro b₁ k₁ b₂ k₂ h₁ h₂ address st hs hc
    obtain ⟨m, hm, h₁⟩ := h₁
    have hm0 : m = [] := List.eq_nil_of_length_eq_zero (by simpa [FastSite.selCode, literalRecords] using hm)
    have hh0 : b₂.history = [] := List.eq_nil_of_length_eq_zero (by rw [h₂.1]; exact f.swapNet_meas)
    change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
    rw [h₁ _ st (sel_valid address st hs), map_smul, h₂.2, hm0, hh0]
    simp [smul_smul]
  · rw [simulationCoefficients_mass, m1, m2]
    norm_num

def FastSim (read : ConstantBit n → Bool) (b : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords f.site.code ∧
    ∀ a st, SimulationValid windowBits pathBank windowRoot a st →
      Clean (portTargets f.site.ports ++ f.garb) st.basis →
      (∀ m, Clean (portTargets f.site.ports)
        (ECDSAAdd.run ((specialize f.site.code a).instantiate read) m st).basis) →
      b.kraus (Bridge.signedKet st) =
        c • Bridge.signedKet (ECDSAAdd.run ((specialize f.site.code a).instantiate read) m st)

end FastSite

namespace FastSite1
variable {n : Nat} (f : FastSite1 n)

theorem sel_placed (hg : FastGeometry1 f) :
    Placed selBits1 selPaths1 windowRoot (WInstr.lookup (n := n) (some f.site.guard) f.selPorts) := by
  obtain ⟨hn, hbd, hgd, hlen, hgn, hdisj, hall⟩ := facts f hg
  have hglt := guard_lt f hg
  refine ⟨?_, ?_, ?_⟩
  · show (f.site.guard :: selBits1 ++ selPaths1).Nodup
    rcases hgd with e | e <;> rw [e] <;> decide +kernel
  · rw [selPorts_targets f hg]; exact hg.nodup
  · apply List.disjoint_left.mpr
    intro w hw hm
    rw [selPorts_targets f hg] at hm
    have h1 := (hall w hm).1
    have h2 := sel_free f hg w hm
    have hr : windowRoot = 10015 := rfl
    simp only [List.mem_cons, List.mem_append, selBits1, selPaths1, List.mem_range'_1, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, lookupRoot,
      Option.getD, hr] at hw
    dsimp only [Wire] at *
    omega

theorem sel_layouts (hg : FastGeometry1 f) : LookupLayouts selBits1 selPaths1 windowRoot f.selCode :=
  pair_layouts_of_placed selBits1 selPaths1 windowRoot f.selCode (by decide)
    (fun i hi => by
      simp only [FastSite1.selCode, List.mem_singleton] at hi
      subst hi
      exact placed_implies_pair _ _ _ _ (sel_placed f hg))

theorem arith_pair (hg : FastGeometry1 f) :
    ∀ i ∈ f.site.arithmetic, PlacedPair windowBits pathBank windowRoot i := fun i hi =>
  placed_implies_pair _ _ _ _ (hg.site.placed i (List.mem_append_left _ (List.mem_cons_of_mem _ hi)))

theorem arith_layouts (hg : FastGeometry1 f) :
    LookupLayouts windowBits pathBank windowRoot (normalizeW f.site.arithmetic) :=
  pair_layouts_of_placed _ _ _ _ (by simp [windowBits, pathBank])
    (pair_placed_normalize _ _ _ _ (arith_pair f hg))

theorem sel_records (hg : FastGeometry1 f) : codeRecords selBits1 selPaths1 windowRoot f.selCode = 32767 := by
  have h := single_lookup_records selBits1 selPaths1 windowRoot (some f.site.guard) f.selPorts (by decide)
    (sel_placed f hg).1
  simpa [FastSite1.selCode] using h

theorem layer_facts (hg : FastGeometry1 f) :
    (855 : Wire) ∉ portTargets f.site.ports ++ f.g1 ∧ (portTargets f.site.ports ++ f.g1).Nodup := by
  obtain ⟨hn, hbd, hgd, hlen, hgn, hdisj, hall⟩ := facts f hg
  exact ⟨fun h => by have := (hall _ h).1; dsimp only [Wire] at *; omega, hg.nodup⟩

theorem swapNet_valid (hg : FastGeometry1 f) : ∀ i ∈ f.swapNet, ECDSAAdd.Challenge.instructionValid i := by
  obtain ⟨c1, n1⟩ := layer_facts f hg
  exact swapLayer_valid 855 _ _ c1 n1

attribute [local irreducible] WEX.codeRecords lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps in

attribute [local irreducible] MeasuredClear.measuredClear8 in

def SwapSim (read : ConstantBit n → Bool) (b : InstrumentBranch) (c : ℂ) : Prop :=
  ∀ address st, SimulationValid windowBits pathBank windowRoot address st →
    Clean (portTargets f.site.ports ++ f.garb) st.basis →
    b.kraus (Bridge.signedKet st) = c • Bridge.signedKet (ECDSAAdd.run f.swapNet List.nil
      (ECDSAAdd.run ((specialize f.selCode (tableAddressValue selBits1 st.basis)).instantiate read) List.nil st))

theorem swap_simulation (read : ConstantBit n → Bool) (hg : FastGeometry1 f) :
    ∃ cs : List ℂ, List.Forall₂ (f.SwapSim read)
      ((source read selBits1 selPaths1 windowRoot f.selCode).seq (literalSource f.swapNet)).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  have hp1 : ∀ i ∈ f.selCode, PlacedPair selBits1 selPaths1 windowRoot i := by
    intro i hi
    simp only [FastSite1.selCode, List.mem_singleton] at hi
    subst hi
    exact placed_implies_pair _ _ _ _ (sel_placed f hg)
  obtain ⟨c1, a1, m1⟩ := pair_source_simulation read selBits1 selPaths1 windowRoot (by decide) f.selCode hp1
  obtain ⟨c2, a2, m2⟩ := literal_simulation f.swapNet
  refine ⟨coherentSeqCoefficients c1 c2, ?_, ?_⟩
  · rw [AdaptiveCircuit.run_seq]
    apply simulationAligned_seq a1 a2
    intro b₁ k₁ b₂ k₂ h₁ h₂ address st hs hc
    obtain ⟨m, hm, h₁⟩ := h₁
    have hm0 : m = [] := List.eq_nil_of_length_eq_zero (by simpa [FastSite1.selCode, literalRecords] using hm)
    have hh0 : b₂.history = [] := List.eq_nil_of_length_eq_zero (by rw [h₂.1]; exact f.swapNet_meas)
    change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
    rw [h₁ _ st (sel_valid address st hs), map_smul, h₂.2, hm0, hh0]
    simp [smul_smul]
  · rw [simulationCoefficients_mass, m1, m2]
    norm_num

def FastSim (read : ConstantBit n → Bool) (b : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords f.site.code ∧
    ∀ a st, SimulationValid windowBits pathBank windowRoot a st →
      Clean (portTargets f.site.ports ++ f.garb) st.basis →
      (∀ m, Clean (portTargets f.site.ports)
        (ECDSAAdd.run ((specialize f.site.code a).instantiate read) m st).basis) →
      b.kraus (Bridge.signedKet st) =
        c • Bridge.signedKet (ECDSAAdd.run ((specialize f.site.code a).instantiate read) m st)

end FastSite1

end
end ShorECDLP.Entrant.WideBank8.Fast16
end

/-! ### Resources of one fast site on the pool bank, against the unit it replaces -/

section
namespace ShorECDLP.Entrant.WideBank8.Fast16
open ShorECDLP.Entrant.WideSigned
open AndGadget WEXCredit Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup PathShare
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
attribute [local irreducible] WEX.codeRecords lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps WEX.compile Bridge.translate
  MeasuredClear.measuredClear MeasuredClear.measuredClear8 ECDSAAdd.Baselines.normalizeProgram

/-- The unit a fast site replaces: the site's own load and arithmetic, then its measured clear. -/
def siteUnit {n} (site : MaskedSite n) : UnitSite n := ⟨site.prefix, site⟩

theorem siteUnit_code {n} (site : MaskedSite n) : (siteUnit site).code = site.code := rfl

theorem prefix_split {n} (site : MaskedSite n) :
    site.prefix = [WInstr.lookup (some site.guard) site.ports] ++ site.arithmetic := rfl

theorem bank_tree_nodes : (tableAddressTree bank15.high 0 1).internalNodes = 255 := high_nodes

theorem bank_tree_leaves : (tableAddressTree bank15.high 0 1).leaves = 256 := by
  rw [MeasuredClear.addressTree_leaves]; decide +kernel

theorem bank_pair_len : windowBits.length ≤ pathBank.length := by decide

theorem lookup_records_bank {n} (c : Option Wire) (ps : List (LookupPort n)) :
    literalRecords (normalizeW ([WInstr.lookup c ps] : WCode n)) = 0 ∧
      traversals (normalizeW ([WInstr.lookup c ps] : WCode n)) = 1 := by
  simp [normalizeW, normalizeWInstr, literalRecords, traversals]

namespace FastSite
variable {n : Nat} (f : FastSite n)

theorem site_layout_bank (hg : FastGeometry f) :
    (tableAddressTree bank15.high 0 1).Layout f.site.guard bank15.hp := site_bank_layout f hg

theorem prefix_layouts (hg : FastGeometry f) :
    LookupLayouts windowBits pathBank windowRoot (normalizeW f.site.prefix) :=
  pair_layouts_of_placed _ _ _ _ bank_pair_len
    (pair_placed_normalize _ _ _ _ (fun i hi =>
      placed_implies_pair _ _ _ _ (hg.site.placed i (List.mem_append_left _ hi))))

/-- Toffoli count of the fast block, in units of seven T gates. -/
def fastTP : Nat :=
  16383 + ECDSAAdd.toffoliCount f.swapNet + 502 +
    (literalToffolis (normalizeW f.site.arithmetic) + traversals f.site.arithmetic * 65535) + 502

theorem fast_tp_relation (hg : FastGeometry f) :
    f.fastTP + (48650 - ECDSAAdd.toffoliCount f.swapNet) = blockTP2 bank15 (.unit (siteUnit f.site)) := by
  have hsw := f.swapNet_toff hg
  have hpl := (facts f hg).2.2.2.1
  have hl : literalToffolis (normalizeW f.site.prefix) = literalToffolis (normalizeW f.site.arithmetic) := by
    rw [prefix_split, normalize_append, literalToffolis_append]
    simp [normalizeW, normalizeWInstr, literalToffolis]
  have ht : traversals f.site.prefix = traversals f.site.arithmetic + 1 := by
    rw [prefix_split, traversals_append]
    simp [traversals]
    omega
  have hb : 2 ^ bank15.bits.length - 1 = 65535 := by simp [bank15, windowBits]
  simp only [blockTP2, siteUnit, fastTP, hl, ht, hb, bank_tree_nodes]
  omega

theorem sel_slots (hg : FastGeometry f) : codeSlots selBits f.selCode = 65536 * f.site.ports.length + 163830 := by
  simp only [codeSlots, FastSite.selCode, selBits, List.length_range', List.length_append, List.length_cons, List.length_nil, selPorts_length f hg]
  norm_num
  try omega

theorem lookup_slots (c : Option Wire) (ps : List (LookupPort n)) :
    codeSlots windowBits (normalizeW ([WInstr.lookup c ps] : WCode n)) = 65536 * ps.length + 655350 := by
  simp [codeSlots, normalizeW, normalizeWInstr, windowBits]

def fastSlack : Nat := 262144 * f.garb.length + 3 * ECDSAAdd.Challenge.gateSlots f.swapNet

end FastSite

namespace FastSite1
variable {n : Nat} (f : FastSite1 n)

theorem site_layout_bank (hg : FastGeometry1 f) :
    (tableAddressTree bank15.high 0 1).Layout f.site.guard bank15.hp := site_bank_layout f hg

theorem prefix_layouts (hg : FastGeometry1 f) :
    LookupLayouts windowBits pathBank windowRoot (normalizeW f.site.prefix) :=
  pair_layouts_of_placed _ _ _ _ bank_pair_len
    (pair_placed_normalize _ _ _ _ (fun i hi =>
      placed_implies_pair _ _ _ _ (hg.site.placed i (List.mem_append_left _ hi))))

def fastTP : Nat :=
  32767 + ECDSAAdd.toffoliCount f.swapNet + 502 +
    (literalToffolis (normalizeW f.site.arithmetic) + traversals f.site.arithmetic * 65535) + 502

theorem fast_tp_relation (hg : FastGeometry1 f) :
    f.fastTP + (32266 - ECDSAAdd.toffoliCount f.swapNet) = blockTP2 bank15 (.unit (siteUnit f.site)) := by
  have hsw := f.swapNet_toff hg
  have hpl := (facts f hg).2.2.2.1
  have hl : literalToffolis (normalizeW f.site.prefix) = literalToffolis (normalizeW f.site.arithmetic) := by
    rw [prefix_split, normalize_append, literalToffolis_append]
    simp [normalizeW, normalizeWInstr, literalToffolis]
  have ht : traversals f.site.prefix = traversals f.site.arithmetic + 1 := by
    rw [prefix_split, traversals_append]
    simp [traversals]
    omega
  have hb : 2 ^ bank15.bits.length - 1 = 65535 := by simp [bank15, windowBits]
  simp only [blockTP2, siteUnit, fastTP, hl, ht, hb, bank_tree_nodes]
  omega

theorem sel_slots (hg : FastGeometry1 f) : codeSlots selBits1 f.selCode = 65536 * f.site.ports.length + 327670 := by
  simp only [codeSlots, FastSite1.selCode, selBits1, List.length_range', List.length_append, List.length_cons, List.length_nil, selPorts_length f hg]
  norm_num
  try omega

def fastSlack : Nat := 262144 * f.garb.length + 3 * ECDSAAdd.Challenge.gateSlots f.swapNet

end FastSite1

end
end ShorECDLP.Entrant.WideBank8.Fast16
end

/-! ### Fused fast sites on the eight-bit bank -/

namespace ShorECDLP.Entrant.WideBank8.Fast16
open ShorECDLP.Entrant.WideSigned
open AndGadget WEXCredit Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup PathShare
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant
open MeasuredClear (ClearPort)
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

namespace FastSite
variable {n : Nat} (f : FastSite n)

/-- Records of the fused fast block: select, swap, then the deferred tail. -/
def fusedRecords : Nat :=
  codeRecords selBits selPaths windowRoot f.selCode + 0 + (f.garbPorts.length + tailRec bank15 f.site)

def fusedProgram (start : Nat) : Straight n start (start + f.fusedRecords) :=
  castFinish (by simp only [fusedRecords, clearData, List.length_map]; omega)
    (((f.selProgram start).append
      (f.swapProgram (start + codeRecords selBits selPaths windowRoot f.selCode))).append
      (deferTail bank15 f.site (clearData f.garbPorts) (start + codeRecords selBits selPaths windowRoot f.selCode + 0)))

def fusedSource (read : ConstantBit n → Bool) : AdaptiveCircuit :=
  ((source read selBits selPaths windowRoot f.selCode).seq (literalSource f.swapNet)).seq
    (deferSource bank15 read f.site (clearData f.garbPorts))

theorem fusedProgram_run (read : ConstantBit n → Bool) (start : Nat) (history : Fin start → Bool) :
    ((f.fusedProgram start).instantiate read history).run = (f.fusedSource read).run := by
  rw [fusedProgram, castFinish_instantiate, swapProgram, selProgram,
    append_run_fixed _ _ _ _ _ (fun h => deferTail_run bank15 read f.site _ _ h), AdaptiveCircuit.run_seq,
    append_run_fixed _ _ _ _ _ (fun h => literalFixed_run (n := n) _ _ _ _ read h), AdaptiveCircuit.run_seq,
    compile_run]
  simp only [fusedSource, AdaptiveCircuit.run_seq]

/-- After select and swap, each garbage wire holds its row's word under the original guard. -/
theorem load_garb (read : ConstantBit n → Bool) (hg : FastGeometry f) (a : Nat) (st : ECDSAAdd.State)
    (hs : SimulationValid windowBits pathBank windowRoot a st)
    (hc : Clean (portTargets f.site.ports ++ f.garb) st.basis) :
    let s₂ := ECDSAAdd.run f.swapNet List.nil
      (ECDSAAdd.run ((specialize f.selCode (tableAddressValue selBits st.basis)).instantiate read) List.nil st)
    ∀ q ∈ clearData f.garbPorts, s₂.basis q.target = (st.basis f.site.guard && decide (read (q.ref a) = q.value)) := by
  intro s₂
  obtain ⟨hp, frame, T, G1, G2, G3⟩ := load_state f read hg a st hs hc
  intro q hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
  simp only [garbPorts, List.mem_append] at hp
  rcases hp with (hp | hp) | hp
  · obtain ⟨i, hi, hgi, rfl⟩ := of_mem_regPorts _ _ _ p hp
    exact G1 i hi hgi
  · obtain ⟨i, hi, hgi, rfl⟩ := of_mem_regPorts _ _ _ p hp
    exact G2 i hi hgi
  · obtain ⟨i, hi, hgi, rfl⟩ := of_mem_regPorts _ _ _ p hp
    exact G3 i hi hgi

theorem fused_simulation (read : ConstantBit n → Bool) (hg : FastGeometry f) (hk : GuardKept f.site) :
    ∃ cs : List ℂ, List.Forall₂ (f.FastSim read) (f.fusedSource read).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  obtain ⟨c1, a1, m1⟩ := swap_simulation f read hg
  obtain ⟨c2, a2, m2⟩ := tail_sim read bank15 bank15_ok f.site hg.site hk (clearData f.garbPorts)
    (by rw [clearData_targets, garbPorts_targets f hg]; exact garb_nodup f hg)
  refine ⟨coherentSeqCoefficients c1 c2, ?_, ?_⟩
  · rw [fusedSource, AdaptiveCircuit.run_seq]
    apply simulationAligned_seq a1 a2
    intro b₁ k₁ b₂ k₂ h₁ h₂
    obtain ⟨m, hm, h₂⟩ := h₂
    refine ⟨m, by simpa [MaskedSite.code, MaskedSite.prefix, literalRecords] using hm, ?_⟩
    intro a st hs hc hun
    have hgarb := load_garb f read hg a st hs hc
    have heq := load_clear_eq f read hg a st hs hc
    have hph := (load_state f read hg a st hs hc).1
    dsimp only at hgarb heq hph
    change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
    rw [h₁ a st hs hc, map_smul, h₂ a st _ hs hun hgarb hph
      (by rw [clearData_targets, garbPorts_targets f hg]; exact heq), smul_smul]
  · rw [simulationCoefficients_mass, m1, m2]
    norm_num

attribute [local irreducible] WEX.codeRecords lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps WEX.compile Bridge.translate
  MeasuredClear.measuredClear MeasuredClear.measuredClear8 ECDSAAdd.Baselines.normalizeProgram

def fusedTP : Nat :=
  16383 + ECDSAAdd.toffoliCount f.swapNet +
    (literalToffolis (normalizeW f.site.arithmetic) + traversals f.site.arithmetic * 65535) + 502

theorem fused_tCount (read : ConstantBit n → Bool) (hg : FastGeometry f) (start : Nat) (history : Fin start → Bool) :
    ((f.fusedProgram start).instantiate read history).tCount = 7 * f.fusedTP := by
  rw [fusedProgram, castFinish_instantiate, swapProgram, selProgram,
    append_tCount_fixed _ _ _ _ _ (fun h => deferTail_tCount read bank15 f.site _ (site_layout_bank f hg)
      (arith_layouts f hg) _ h),
    append_tCount_fixed _ _ _ _ _ (fun h => literalFixed_tCount (n := n) _ _ _ _ read h),
    compile_tCount read selBits selPaths windowRoot _ (sel_layouts f hg), traversals_normalize, bank_tree_nodes]
  simp only [fusedTP, FastSite.selCode, literalToffolis, traversals, selBits, bank15, windowBits,
    List.length_range', List.length_append, List.length_cons, List.length_nil]
  norm_num
  try ring

theorem fused_tp_relation (hg : FastGeometry f) :
    f.fusedTP + (49152 - ECDSAAdd.toffoliCount f.swapNet) = blockTP2 bank15 (.unit (siteUnit f.site)) := by
  have h := f.fast_tp_relation hg
  have hsw := f.swapNet_toff hg
  have hpl := (facts f hg).2.2.2.1
  simp only [fastTP, fusedTP] at h ⊢
  omega

theorem fused_records_relation (hg : FastGeometry f) :
    f.fusedRecords + (49152 - f.garb.length) = blockRecP2 bank15 (.unit (siteUnit f.site)) := by
  have hsel := sel_records f hg
  have hgl := garbPorts_length f hg
  have hlen := garb_length f hg
  have hpl := (facts f hg).2.2.2.1
  have hcr := (MeasuredClear.recordUnary_counts _ _ _ (site_layout_bank f hg) 0).1
  rw [bank_tree_nodes] at hcr
  have hcr' : MeasuredClear.recordMeasurements
      (MeasuredClear.recordUnaryOps (tableAddressTree high 0 1) f.site.guard bankHp) = 255 := hcr
  have hpre := codeRecords_eq _ _ _ _ (prefix_layouts f hg)
  have hari := codeRecords_eq _ _ _ _ (arith_layouts f hg)
  have hlr : literalRecords (normalizeW f.site.prefix) = literalRecords (normalizeW f.site.arithmetic) := by
    rw [prefix_split, normalize_append, literalRecords_append, (lookup_records_bank _ _).1, Nat.zero_add]
  have htr : traversals (normalizeW f.site.prefix) = traversals (normalizeW f.site.arithmetic) + 1 := by
    rw [prefix_split, normalize_append, traversals_append, (lookup_records_bank _ _).2]
    omega
  have hb : 2 ^ windowBits.length - 1 = 65535 := by simp [windowBits]
  simp only [blockRecP2, siteUnit, FastSite.fusedRecords, tailRec, fuseRec, hsel, hgl, hcr, hcr', hpre, hari, hlr, htr, hb]
  simp only [show bank15.bits = windowBits from rfl, show bank15.paths = pathBank from rfl, hb] at hpre hari ⊢
  omega

theorem fused_slots (hg : FastGeometry f) (start : Nat) :
    (f.fusedProgram start).gateSlots ≤ blockSP2 bank15 (.unit (siteUnit f.site)) + f.fastSlack := by
  rw [fusedProgram, castFinish_gateSlots]
  simp only [Straight.gateSlots_append]
  rw [deferTail_slots bank15 f.site _ (site_layout_bank f hg) (arith_layouts f hg), swapProgram, literalFixed_slots,
    selProgram, compile_slots _ _ _ _ (sel_layouts f hg), sel_slots f hg]
  have hsw := literal_slot_bound (n := n) f.swapNet
  have hd : (clearData f.garbPorts).length = f.garb.length := by
    rw [clearData, List.length_map, garbPorts_length f hg]
  have hpre : codeSlots windowBits (normalizeW f.site.prefix) =
      (65536 * f.site.ports.length + 655350) + codeSlots windowBits (normalizeW f.site.arithmetic) := by
    rw [prefix_split, normalize_append, slots_append_wide, lookup_slots]
  simp only [blockSP2, siteUnit, fastSlack, show bank15.bits = windowBits from rfl, hpre, hd, bank_tree_leaves,
    bank_tree_nodes]
  omega

theorem fused_wellFormed (hg : FastGeometry f) (hp : ∀ p, WInstr.literal p ∈ f.site.code → GatePhysical p)
    (start : Nat) : (f.fusedProgram start).WellFormed := by
  rw [fusedProgram, castFinish_wellFormed]
  refine straight_append_wellFormed _ _ (straight_append_wellFormed _ _ ?_ ?_) ?_
  · exact pair_compile_wellFormed _ _ _ _ (by decide)
      (fun i hi => by
        simp only [FastSite.selCode, List.mem_singleton] at hi
        subst hi
        exact placed_implies_pair _ _ _ _ (sel_placed f hg))
      (fun p hp => by simp [FastSite.selCode] at hp) start
  · exact literalFixed_wellFormed _ _ _ (f.swapNet_valid hg) _
  · exact deferTail_wellFormed bank15 bank15_ok f.site hg.site _
      (fun p hm => hp p (List.mem_append_left _ (List.mem_cons_of_mem _ hm))) _

theorem fused_residue (start : Nat) : residue (f.fusedProgram start) = 0 := by
  rw [fusedProgram, residue_cast]
  simp only [residue_append]
  rw [selProgram, compile_residue, swapProgram, literalFixed, residue_naive_cast, literal_residue,
    deferTail_residue]

end FastSite

namespace FastSite1
variable {n : Nat} (f : FastSite1 n)

def fusedRecords : Nat :=
  codeRecords selBits1 selPaths1 windowRoot f.selCode + 0 + (f.garbPorts.length + tailRec bank15 f.site)

def fusedProgram (start : Nat) : Straight n start (start + f.fusedRecords) :=
  castFinish (by simp only [fusedRecords, clearData, List.length_map]; omega)
    (((f.selProgram start).append
      (f.swapProgram (start + codeRecords selBits1 selPaths1 windowRoot f.selCode))).append
      (deferTail bank15 f.site (clearData f.garbPorts) (start + codeRecords selBits1 selPaths1 windowRoot f.selCode + 0)))

def fusedSource (read : ConstantBit n → Bool) : AdaptiveCircuit :=
  ((source read selBits1 selPaths1 windowRoot f.selCode).seq (literalSource f.swapNet)).seq
    (deferSource bank15 read f.site (clearData f.garbPorts))

theorem fusedProgram_run (read : ConstantBit n → Bool) (start : Nat) (history : Fin start → Bool) :
    ((f.fusedProgram start).instantiate read history).run = (f.fusedSource read).run := by
  rw [fusedProgram, castFinish_instantiate, swapProgram, selProgram,
    append_run_fixed _ _ _ _ _ (fun h => deferTail_run bank15 read f.site _ _ h), AdaptiveCircuit.run_seq,
    append_run_fixed _ _ _ _ _ (fun h => literalFixed_run (n := n) _ _ _ _ read h), AdaptiveCircuit.run_seq,
    compile_run]
  simp only [fusedSource, AdaptiveCircuit.run_seq]

theorem load_garb (read : ConstantBit n → Bool) (hg : FastGeometry1 f) (a : Nat) (st : ECDSAAdd.State)
    (hs : SimulationValid windowBits pathBank windowRoot a st)
    (hc : Clean (portTargets f.site.ports ++ f.garb) st.basis) :
    let s₂ := ECDSAAdd.run f.swapNet List.nil
      (ECDSAAdd.run ((specialize f.selCode (tableAddressValue selBits1 st.basis)).instantiate read) List.nil st)
    ∀ q ∈ clearData f.garbPorts, s₂.basis q.target = (st.basis f.site.guard && decide (read (q.ref a) = q.value)) := by
  intro s₂
  obtain ⟨hp, frame, T, G1⟩ := load_state f read hg a st hs hc
  intro q hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
  obtain ⟨i, hi, hgi, rfl⟩ := of_mem_regPorts _ _ _ p hp
  exact G1 i hi hgi

theorem fused_simulation (read : ConstantBit n → Bool) (hg : FastGeometry1 f) (hk : GuardKept f.site) :
    ∃ cs : List ℂ, List.Forall₂ (f.FastSim read) (f.fusedSource read).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  obtain ⟨c1, a1, m1⟩ := swap_simulation f read hg
  obtain ⟨c2, a2, m2⟩ := tail_sim read bank15 bank15_ok f.site hg.site hk (clearData f.garbPorts)
    (by rw [clearData_targets, garbPorts_targets f hg]; exact garb_nodup f hg)
  refine ⟨coherentSeqCoefficients c1 c2, ?_, ?_⟩
  · rw [fusedSource, AdaptiveCircuit.run_seq]
    apply simulationAligned_seq a1 a2
    intro b₁ k₁ b₂ k₂ h₁ h₂
    obtain ⟨m, hm, h₂⟩ := h₂
    refine ⟨m, by simpa [MaskedSite.code, MaskedSite.prefix, literalRecords] using hm, ?_⟩
    intro a st hs hc hun
    have hgarb := load_garb f read hg a st hs hc
    have heq := load_clear_eq f read hg a st hs hc
    have hph := (load_state f read hg a st hs hc).1
    dsimp only at hgarb heq hph
    change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
    rw [h₁ a st hs hc, map_smul, h₂ a st _ hs hun hgarb hph
      (by rw [clearData_targets, garbPorts_targets f hg]; exact heq), smul_smul]
  · rw [simulationCoefficients_mass, m1, m2]
    norm_num

attribute [local irreducible] WEX.codeRecords lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps WEX.compile Bridge.translate
  MeasuredClear.measuredClear MeasuredClear.measuredClear8 ECDSAAdd.Baselines.normalizeProgram

def fusedTP : Nat :=
  32767 + ECDSAAdd.toffoliCount f.swapNet +
    (literalToffolis (normalizeW f.site.arithmetic) + traversals f.site.arithmetic * 65535) + 502

theorem fused_tCount (read : ConstantBit n → Bool) (hg : FastGeometry1 f) (start : Nat) (history : Fin start → Bool) :
    ((f.fusedProgram start).instantiate read history).tCount = 7 * f.fusedTP := by
  rw [fusedProgram, castFinish_instantiate, swapProgram, selProgram,
    append_tCount_fixed _ _ _ _ _ (fun h => deferTail_tCount read bank15 f.site _ (site_layout_bank f hg)
      (arith_layouts f hg) _ h),
    append_tCount_fixed _ _ _ _ _ (fun h => literalFixed_tCount (n := n) _ _ _ _ read h),
    compile_tCount read selBits1 selPaths1 windowRoot _ (sel_layouts f hg), traversals_normalize, bank_tree_nodes]
  simp only [fusedTP, FastSite1.selCode, literalToffolis, traversals, selBits1, bank15, windowBits,
    List.length_range', List.length_append, List.length_cons, List.length_nil]
  norm_num
  try ring

theorem fused_tp_relation (hg : FastGeometry1 f) :
    f.fusedTP + (32768 - ECDSAAdd.toffoliCount f.swapNet) = blockTP2 bank15 (.unit (siteUnit f.site)) := by
  have h := f.fast_tp_relation hg
  have hsw := f.swapNet_toff hg
  have hpl := (facts f hg).2.2.2.1
  simp only [fastTP, fusedTP] at h ⊢
  omega

theorem fused_records_relation (hg : FastGeometry1 f) :
    f.fusedRecords + (32768 - f.garb.length) = blockRecP2 bank15 (.unit (siteUnit f.site)) := by
  have hsel := sel_records f hg
  have hgl := garbPorts_length f hg
  have hlen := garb_length f hg
  have hpl := (facts f hg).2.2.2.1
  have hcr := (MeasuredClear.recordUnary_counts _ _ _ (site_layout_bank f hg) 0).1
  rw [bank_tree_nodes] at hcr
  have hcr' : MeasuredClear.recordMeasurements
      (MeasuredClear.recordUnaryOps (tableAddressTree high 0 1) f.site.guard bankHp) = 255 := hcr
  have hpre := codeRecords_eq _ _ _ _ (prefix_layouts f hg)
  have hari := codeRecords_eq _ _ _ _ (arith_layouts f hg)
  have hlr : literalRecords (normalizeW f.site.prefix) = literalRecords (normalizeW f.site.arithmetic) := by
    rw [prefix_split, normalize_append, literalRecords_append, (lookup_records_bank _ _).1, Nat.zero_add]
  have htr : traversals (normalizeW f.site.prefix) = traversals (normalizeW f.site.arithmetic) + 1 := by
    rw [prefix_split, normalize_append, traversals_append, (lookup_records_bank _ _).2]
    omega
  have hb : 2 ^ windowBits.length - 1 = 65535 := by simp [windowBits]
  simp only [blockRecP2, siteUnit, FastSite1.fusedRecords, tailRec, fuseRec, hsel, hgl, hcr, hcr', hpre, hari, hlr, htr, hb]
  simp only [show bank15.bits = windowBits from rfl, show bank15.paths = pathBank from rfl, hb] at hpre hari ⊢
  omega

theorem fused_slots (hg : FastGeometry1 f) (start : Nat) :
    (f.fusedProgram start).gateSlots ≤ blockSP2 bank15 (.unit (siteUnit f.site)) + f.fastSlack := by
  rw [fusedProgram, castFinish_gateSlots]
  simp only [Straight.gateSlots_append]
  rw [deferTail_slots bank15 f.site _ (site_layout_bank f hg) (arith_layouts f hg), swapProgram, literalFixed_slots,
    selProgram, compile_slots _ _ _ _ (sel_layouts f hg), sel_slots f hg]
  have hsw := literal_slot_bound (n := n) f.swapNet
  have hd : (clearData f.garbPorts).length = f.garb.length := by
    rw [clearData, List.length_map, garbPorts_length f hg]
  have hpre : codeSlots windowBits (normalizeW f.site.prefix) =
      (65536 * f.site.ports.length + 655350) + codeSlots windowBits (normalizeW f.site.arithmetic) := by
    rw [prefix_split, normalize_append, slots_append_wide, FastSite.lookup_slots]
  simp only [blockSP2, siteUnit, fastSlack, show bank15.bits = windowBits from rfl, hpre, hd, bank_tree_leaves,
    bank_tree_nodes]
  omega

theorem fused_wellFormed (hg : FastGeometry1 f) (hp : ∀ p, WInstr.literal p ∈ f.site.code → GatePhysical p)
    (start : Nat) : (f.fusedProgram start).WellFormed := by
  rw [fusedProgram, castFinish_wellFormed]
  refine straight_append_wellFormed _ _ (straight_append_wellFormed _ _ ?_ ?_) ?_
  · exact pair_compile_wellFormed _ _ _ _ (by decide)
      (fun i hi => by
        simp only [FastSite1.selCode, List.mem_singleton] at hi
        subst hi
        exact placed_implies_pair _ _ _ _ (sel_placed f hg))
      (fun p hp => by simp [FastSite1.selCode] at hp) start
  · exact literalFixed_wellFormed _ _ _ (f.swapNet_valid hg) _
  · exact deferTail_wellFormed bank15 bank15_ok f.site hg.site _
      (fun p hm => hp p (List.mem_append_left _ (List.mem_cons_of_mem _ hm))) _

theorem fused_residue (start : Nat) : residue (f.fusedProgram start) = 0 := by
  rw [fusedProgram, residue_cast]
  simp only [residue_append]
  rw [selProgram, compile_residue, swapProgram, literalFixed, residue_naive_cast, literal_residue,
    deferTail_residue]

end FastSite1

end
end ShorECDLP.Entrant.WideBank8.Fast16

namespace ShorECDLP.Entrant.WideBank8.Fast16
open ShorECDLP.Entrant.WideSigned
end ShorECDLP.Entrant.WideBank8.Fast16

/-! ### A pair of adjacent units with one fused clear

The second unit's clear also repays the first unit's clear: the first register is still measured
and reset at its old position, but only one phase fixup runs, after the second prefix. -/
namespace ShorECDLP.Entrant.WideBank8.Fast16
open ShorECDLP.Entrant.WideSigned
open AndGadget WEXCredit Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup PathShare
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant
open MeasuredClear (ClearPort)
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

structure UnitPair (n : Nat) where
  u₁ : UnitSite n
  u₂ : UnitSite n

namespace UnitPair
variable {n : Nat} (q : UnitPair n)

/-- The first unit's register, whose phase is deferred. -/
def gd : List (ClearPort n) := clearData q.u₁.clear.ports

def Geo : Prop :=
  UnitGeoP bank15 q.u₁ ∧ UnitGeoP bank15 q.u₂ ∧ q.u₁.clear.guard = windowRoot ∧ q.u₂.clear.guard = windowRoot

def pairRecords : Nat :=
  codeRecords bank15.bits bank15.paths windowRoot (normalizeW q.u₁.pre) +
    (q.gd.length + tailRec bank15 (unitTail q.u₂))

def pairProgram (start : Nat) : Straight n start (start + q.pairRecords) :=
  castFinish (by simp only [pairRecords]; omega)
    ((compile bank15.bits bank15.paths windowRoot (normalizeW q.u₁.pre) start).append
      (deferTail bank15 (unitTail q.u₂) q.gd
        (start + codeRecords bank15.bits bank15.paths windowRoot (normalizeW q.u₁.pre))))

def pairSource (read : ConstantBit n → Bool) : AdaptiveCircuit :=
  (source read bank15.bits bank15.paths windowRoot (normalizeW q.u₁.pre)).seq
    (deferSource bank15 read (unitTail q.u₂) q.gd)

theorem pairProgram_run (read : ConstantBit n → Bool) (start : Nat) (history : Fin start → Bool) :
    ((q.pairProgram start).instantiate read history).run = (q.pairSource read).run := by
  rw [pairProgram, castFinish_instantiate,
    append_run_fixed _ _ _ _ _ (fun h => deferTail_run bank15 read (unitTail q.u₂) q.gd _ h),
    AdaptiveCircuit.run_seq, compile_run]
  simp only [pairSource, AdaptiveCircuit.run_seq]

theorem gd_nodup (hg : q.Geo) : (q.gd.map ClearPort.target).Nodup := by
  rw [gd, clearData_targets]
  exact (hg.1.site.placed (.lookup (some q.u₁.clear.guard) q.u₁.clear.ports)
    (by simp [MaskedSite.code])).2.1

theorem pair_sim (read : ConstantBit n → Bool) (hg : q.Geo) :
    ∃ cs : List ℂ, List.Forall₂ (fun (br : InstrumentBranch) (c : ℂ) =>
      ∃ m : List Bool, m.length = literalRecords (erase2 (Block2.unit q.u₁ :: Block2.unit q.u₂ :: [])) ∧
        ∀ address st, AddrValid windowBits windowRoot address st → Clean pathBank st.basis →
          Safe2 read address (Block2.unit q.u₁ :: Block2.unit q.u₂ :: []) st →
          br.kraus (Bridge.signedKet st) =
            c • Bridge.signedKet (ECDSAAdd.run (reference2 read address (Block2.unit q.u₁ :: Block2.unit q.u₂ :: [])) m st))
      (q.pairSource read).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
  have hgn := q.gd_nodup hg
  obtain ⟨g1, g2, r1, r2⟩ := hg
  have hp1 : ∀ i ∈ q.u₁.pre, PlacedPair bank15.bits bank15.paths windowRoot i := fun i hi =>
    g1.placed i (List.mem_append_left _ hi)
  obtain ⟨c1, a1, m1⟩ := lnormalized_simulation read bank15.bits bank15.paths bank15_ok.bitsLen q.u₁.pre
    (fun i hi => pair_of_placed_lit _ _ i (hp1 i hi))
  obtain ⟨c2, a2, m2⟩ := utail_sim read bank15 bank15_ok q.u₂ g2 r2 q.gd hgn
  refine ⟨coherentSeqCoefficients c1 c2, ?_, ?_⟩
  · rw [pairSource, AdaptiveCircuit.run_seq]
    apply simulationAligned_seq a1 a2
    intro b₁ k₁ b₂ k₂ h₁ h₂
    obtain ⟨m₁, hm₁, h₁⟩ := h₁
    obtain ⟨m₂, hm₂, h₂⟩ := h₂
    refine ⟨m₁ ++ m₂, ?_, ?_⟩
    · simp [erase2, Block2.code, UnitSite.code, literalRecords_append, literalRecords, hm₁, hm₂]
    · intro a st hs hcl hsafe
      have hsv : SimulationValid bank15.bits bank15.paths windowRoot a st := ⟨hcl, hs.1, hs.2⟩
      have hm1c : m₁.length = ECDSAAdd.measurementCount (blockReference2 read a (.unit q.u₁)) := by
        rw [hm₁, blockReference2, (specialize_counts read _ a).2]
        simp [Block2.code, UnitSite.code, literalRecords_append, literalRecords]
      have hsafe1 : ∀ m, Clean (portTargets q.u₁.clear.ports)
          (ECDSAAdd.run ((specialize q.u₁.code a).instantiate read) m st).basis := hsafe.1
      have hsafe2 : ∀ m, Clean (portTargets q.u₂.clear.ports)
          (ECDSAAdd.run ((specialize q.u₂.code a).instantiate read) m
            (ECDSAAdd.run ((specialize q.u₁.code a).instantiate read) m₁ st)).basis :=
        (hsafe.2 m₁ hm1c).1
      have hmidv := strict_preserves read bank15.bits bank15.paths q.u₁.code a g1.placed st hsv m₁
      have hn := strict_preserves read bank15.bits bank15.paths q.u₁.pre a hp1 st hsv m₁
      have hrun := unit_runP read bank15 q.u₁ g1 a st m₁ hsv
      have h1 := h₁ a st hs (strict_pathsClean read bank15.bits bank15.paths q.u₁.pre a hp1 st hsv)
      have hred : ECDSAAdd.run (reference2 read a (Block2.unit q.u₁ :: Block2.unit q.u₂ :: [])) (m₁ ++ m₂) st =
          ECDSAAdd.run ((specialize q.u₂.code a).instantiate read) m₂
            (ECDSAAdd.run ((specialize q.u₁.code a).instantiate read) m₁ st) := by
        rw [reference2_cons, reference2_cons, reference2_nil, List.append_nil,
          run_append_records _ _ m₁ m₂ st hm1c]
        rfl
      rw [hred]
      set next := ECDSAAdd.run ((specialize q.u₁.pre a).instantiate read) m₁ st with hnext
      have hclean : Clean (portTargets q.u₁.clear.ports)
          (tableXorState (portMask read q.u₁.clear.ports a) (next.basis q.u₁.clear.guard) next.basis) := by
        have h := hsafe1 m₁
        rw [hrun] at h
        exact h
      have hlast := g1.site.placed (.lookup (some q.u₁.clear.guard) q.u₁.clear.ports) (by simp [MaskedSite.code])
      have hfin : (⟨next.phase, clearRegister (portTargets q.u₁.clear.ports) next.basis⟩ : ECDSAAdd.State) =
          ECDSAAdd.run ((specialize q.u₁.code a).instantiate read) m₁ st := by
        rw [hrun, clear_eq_unload read q.u₁.clear.ports a q.u₁.clear.guard next.basis hclean]
      set mid := ECDSAAdd.run ((specialize q.u₁.code a).instantiate read) m₁ st with hmid
      have hgdv : ∀ p ∈ q.gd, next.basis p.target =
          (mid.basis q.u₂.clear.guard && decide (read (p.ref a) = p.value)) := by
        intro p hp
        simp only [gd, clearData] at hp
        obtain ⟨p0, hp0, rfl⟩ := List.mem_map.mp hp
        have hl := loaded_of_clean_unload read q.u₁.clear.ports a q.u₁.clear.guard next.basis
          hlast.2.1 hclean p0 hp0
        rw [r1, hn.2.2] at hl
        rw [r2, hmidv.2.2]
        exact hl
      have hph : next.phase = mid.phase := by rw [← hfin]
      have hclr : clearRegister (q.gd.map ClearPort.target) next.basis = mid.basis := by
        rw [gd, clearData_targets, ← hfin]
      have h2 := h₂ a mid next hmidv hsafe2 hgdv hph hclr
      change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
      rw [h1, map_smul, h2, smul_smul]
  · rw [simulationCoefficients_mass, m1, m2]
    norm_num

/-- Toffoli units of the pair: both prefixes and one clear. -/
def pairTP : Nat :=
  literalToffolis (normalizeW q.u₁.pre) + traversals q.u₁.pre * (2 ^ bank15.bits.length - 1) +
    blockTP2 bank15 (.unit q.u₂)

/-- The clear the pair saves. -/
def pairSave : Nat := (tableAddressTree bank15.high 0 1).internalNodes + 247

/-- The records the pair saves: the first clear's fixup ancillas. -/
def pairRSave : Nat :=
  MeasuredClear.recordMeasurements
    (MeasuredClear.recordUnaryOps (tableAddressTree bank15.high 0 1) q.u₁.clear.guard bank15.hp) + 255

theorem pair_tCount (read : ConstantBit n → Bool) (hg : q.Geo) (start : Nat) (history : Fin start → Bool) :
    ((q.pairProgram start).instantiate read history).tCount = 7 * q.pairTP := by
  obtain ⟨h1, -⟩ := geo_lay2 bank15 bank15_ok (.unit q.u₁) hg.1
  obtain ⟨h2, h2t⟩ := geo_lay2 bank15 bank15_ok (.unit q.u₂) hg.2.1
  rw [pairProgram, castFinish_instantiate,
    append_tCount_fixed _ _ _ _ _ (fun h => deferTail_tCount read bank15 (unitTail q.u₂) q.gd h2t h2 _ h),
    WEX.compile_tCount read _ _ _ _ h1 start history]
  simp only [pairTP, blockTP2, unitTail, traversals_normalize]
  ring

theorem pair_tp_relation : q.pairTP + UnitPair.pairSave = blockTP2 bank15 (.unit q.u₁) + blockTP2 bank15 (.unit q.u₂) := by
  simp only [pairTP, pairSave, blockTP2]
  omega

theorem pair_records_relation :
    q.pairRecords + q.pairRSave = blockRecP2 bank15 (.unit q.u₁) + blockRecP2 bank15 (.unit q.u₂) := by
  simp only [pairRecords, pairRSave, blockRecP2, tailRec, fuseRec, gd, clearData, List.length_map, unitTail]
  omega

theorem pair_slots (hg : q.Geo) (start : Nat) :
    (q.pairProgram start).gateSlots ≤ blockSP2 bank15 (.unit q.u₁) + blockSP2 bank15 (.unit q.u₂) + 12 := by
  obtain ⟨h1, -⟩ := geo_lay2 bank15 bank15_ok (.unit q.u₁) hg.1
  obtain ⟨h2, h2t⟩ := geo_lay2 bank15 bank15_ok (.unit q.u₂) hg.2.1
  rw [pairProgram, castFinish_gateSlots, Straight.gateSlots_append, WEX.compile_slots _ _ _ _ h1 start,
    deferTail_slots bank15 (unitTail q.u₂) q.gd h2t h2]
  simp only [blockSP2, gd, clearData, List.length_map, unitTail, bank_tree_leaves, bank_tree_nodes]
  omega

attribute [local irreducible] WEX.codeRecords lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps WEX.compile Bridge.translate
  MeasuredClear.measuredClear MeasuredClear.measuredClear8 ECDSAAdd.Baselines.normalizeProgram

theorem pair_wellFormed (hg : q.Geo)
    (hp : ∀ p, WInstr.literal p ∈ q.u₁.code ++ q.u₂.code → GatePhysical p) (start : Nat) :
    (q.pairProgram start).WellFormed := by
  have hpref1 : ∀ i ∈ q.u₁.pre, LPlaced bank15.bits bank15.paths windowRoot i := fun i hi =>
    pair_of_placed_lit _ _ i (hg.1.placed i (List.mem_append_left _ hi))
  have hl1 : ∀ p, WInstr.literal p ∈ q.u₁.pre → GatePhysical p := fun p hm =>
    hp p (List.mem_append_left _ (List.mem_append_left _ hm))
  have hl2 : ∀ p, WInstr.literal p ∈ q.u₂.pre → GatePhysical p := fun p hm =>
    hp p (List.mem_append_right _ (List.mem_append_left _ hm))
  rw [pairProgram, castFinish_wellFormed]
  exact straight_append_wellFormed _ _
    (compile_wellFormedL _ _ _ _ bank15_ok.bitsLen (lplaced_normalize _ _ _ _ hpref1)
      (normalized_literals_valid q.u₁.pre hl1) start)
    (unitTail_wellFormed bank15 bank15_ok q.u₂ hg.2.1 q.gd hl2 _)

theorem pair_residue (start : Nat) : AndGadget.residue (q.pairProgram start) = 0 := by
  simp [pairProgram, AndGadget.residue_cast, AndGadget.residue_append, WEXCredit.compile_residue,
    deferTail_residue]

end UnitPair

end
end ShorECDLP.Entrant.WideBank8.Fast16

namespace ShorECDLP.Entrant.WideBank8.Fast16
open ShorECDLP.Entrant.WideSigned
open Quantum Challenge AndGadget WEXCredit Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare
open ECDSAAdd.Arithmetic
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] WEX.codeRecords lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps WEX.compile Bridge.translate
  MeasuredClear.measuredClear MeasuredClear.measuredClear8 ECDSAAdd.Baselines.normalizeProgram

inductive FBlock2 (n : Nat) where
  | std (b : Block2 n)
  | fast (f : FastSite n)
  | fast1 (f : FastSite1 n)
  | pair (q : UnitPair n)
abbrev FCode2 (n : Nat) := List (FBlock2 n)

/-- The `Code2` blocks a fast block replaces. -/
def FBlock2.forgetL {n} : FBlock2 n → Code2 n
  | .std b => (b :: [])
  | .fast f => (Block2.unit (siteUnit f.site) :: [])
  | .fast1 f => (Block2.unit (siteUnit f.site) :: [])
  | .pair q => (Block2.unit q.u₁ :: Block2.unit q.u₂ :: [])

def fforget {n} (code : FCode2 n) : Code2 n := code.flatMap FBlock2.forgetL

@[simp] theorem fforget_cons {n} (b : FBlock2 n) (code : FCode2 n) :
    fforget (b :: code) = b.forgetL ++ fforget code := by
  simp [fforget]

@[simp] theorem fforget_append {n} (a b : FCode2 n) : fforget (a ++ b) = fforget a ++ fforget b := by
  simp [fforget, List.flatMap_append]

theorem erase2_single {n} (b : Block2 n) : erase2 (b :: []) = b.code := by
  simp [erase2]

theorem reference2_single {n} (read : ConstantBit n → Bool) (a : Nat) (b : Block2 n) :
    reference2 read a (b :: []) = blockReference2 read a b := by
  rw [reference2_cons, reference2_nil, List.append_nil]

theorem safe2_append_inv {n} (read : ConstantBit n → Bool) (address : Nat) (a b : Code2 n)
    (st : ECDSAAdd.State) (h : Safe2 read address (a ++ b) st) :
    Safe2 read address a st ∧ ∀ m, m.length = ECDSAAdd.measurementCount (reference2 read address a) →
      Safe2 read address b (ECDSAAdd.run (reference2 read address a) m st) := by
  induction a generalizing st with
  | nil =>
    refine ⟨trivial, fun m hm => ?_⟩
    have hm0 : m = [] := List.eq_nil_of_length_eq_zero (hm.trans rfl)
    subst hm0
    simpa [ECDSAAdd.run] using h
  | cons x xs ih =>
    refine ⟨⟨h.1, fun m hm => (ih _ (h.2 m hm)).1⟩, fun m hm => ?_⟩
    rw [reference2_cons, ECDSAAdd.measurementCount_append] at hm
    have hlen : (m.take (ECDSAAdd.measurementCount (blockReference2 read address x))).length =
        ECDSAAdd.measurementCount (blockReference2 read address x) := by
      rw [List.length_take]; omega
    have hrest := (ih _ (h.2 (m.take (ECDSAAdd.measurementCount (blockReference2 read address x))) hlen)).2 (m.drop (ECDSAAdd.measurementCount (blockReference2 read address x)))
      (by rw [List.length_drop]; omega)
    rw [reference2_cons, ← List.take_append_drop (ECDSAAdd.measurementCount (blockReference2 read address x)) m,
      run_append_records _ _ _ _ st hlen]
    exact hrest

theorem codeTP2_append {n} (B : Bank) (a b : Code2 n) : codeTP2 B (a ++ b) = codeTP2 B a + codeTP2 B b := by
  induction a with
  | nil => simp [codeTP2]
  | cons x a ih => simp [codeTP2, ih, Nat.add_assoc]

theorem recordsP2_append {n} (B : Bank) (a b : Code2 n) :
    recordsP2 B (a ++ b) = recordsP2 B a + recordsP2 B b := by
  induction a with
  | nil => simp [recordsP2]
  | cons x a ih => simp [recordsP2, ih, Nat.add_assoc]

theorem codeSP2_append {n} (B : Bank) (a b : Code2 n) : codeSP2 B (a ++ b) = codeSP2 B a + codeSP2 B b := by
  induction a with
  | nil => simp [codeSP2]
  | cons x a ih => simp [codeSP2, ih, Nat.add_assoc]

def fblockRec {n} : FBlock2 n → Nat
  | .std b => blockRecP2 bank15 b
  | .fast f => f.fusedRecords
  | .fast1 f => f.fusedRecords
  | .pair q => q.pairRecords

def fblockProg {n} : (b : FBlock2 n) → (start : Nat) → Straight n start (start + fblockRec b)
  | .std b, start => blockProgH bank15 b start
  | .fast f, start => f.fusedProgram start
  | .fast1 f, start => f.fusedProgram start
  | .pair q, start => q.pairProgram start

def frecs {n} : FCode2 n → Nat
  | [] => 0
  | b :: code => fblockRec b + frecs code

def fprog {n} : (code : FCode2 n) → (start : Nat) → Straight n start (start + frecs code)
  | [], _ => .done
  | b :: code, start => castFinish (by simp [frecs]; omega)
      ((fblockProg b start).append (fprog code (start + fblockRec b)))

def fblockSrc {n} (read : ConstantBit n → Bool) : FBlock2 n → AdaptiveCircuit
  | .std b => blockSourceH bank15 read b
  | .fast f => f.fusedSource read
  | .fast1 f => f.fusedSource read
  | .pair q => q.pairSource read

def fsrc {n} (read : ConstantBit n → Bool) : FCode2 n → AdaptiveCircuit
  | [] => .done
  | b :: code => (fblockSrc read b).seq (fsrc read code)

theorem fblockProg_run {n} (read : ConstantBit n → Bool) (b : FBlock2 n) (start : Nat)
    (history : Fin start → Bool) :
    ((fblockProg b start).instantiate read history).run = (fblockSrc read b).run := by
  cases b with
  | std b => exact blockProgH_run bank15 read b start history
  | fast f => exact f.fusedProgram_run read start history
  | fast1 f => exact f.fusedProgram_run read start history
  | pair q => exact q.pairProgram_run read start history

theorem fprog_run {n} (read : ConstantBit n → Bool) (code : FCode2 n) (start : Nat)
    (history : Fin start → Bool) :
    ((fprog code start).instantiate read history).run = (fsrc read code).run := by
  induction code generalizing start with
  | nil => rfl
  | cons b code ih =>
    rw [fprog, castFinish_instantiate, append_run_fixed _ _ _ _ _ (ih _), AdaptiveCircuit.run_seq, fblockProg_run]
    simp only [fsrc, AdaptiveCircuit.run_seq]

/-! Geometry, the clean-bank premise and the per-block simulation. -/

def FBlockGeo {n} : FBlock2 n → Prop
  | .std b => BlockGeoP2 bank15 b
  | .fast f => FastGeometry f ∧ GuardKept f.site
  | .fast1 f => FastGeometry1 f ∧ GuardKept f.site
  | .pair q => q.Geo

/-- At a fast block both the bank and the site's four registers are clean. -/
def FBlockClean {n} : FBlock2 n → ECDSAAdd.State → Prop
  | .std b, st => BlockClean2 pathBank b st ∧ PoolHost.HostOK7 b st
  | .fast f, st => Clean pathBank st.basis ∧ Clean (portTargets f.site.ports ++ f.garb) st.basis
  | .fast1 f, st => Clean pathBank st.basis ∧ Clean (portTargets f.site.ports ++ f.garb) st.basis
  | .pair _, st => Clean pathBank st.basis

def FCodeClean {n} (read : ConstantBit n → Bool) (address : Nat) : FCode2 n → ECDSAAdd.State → Prop
  | [], _ => True
  | b :: code, st => FBlockClean b st ∧
      ∀ m, m.length = ECDSAAdd.measurementCount (reference2 read address b.forgetL) →
        FCodeClean read address code (ECDSAAdd.run (reference2 read address b.forgetL) m st)

def FBlockSim {n} (read : ConstantBit n → Bool) (block : FBlock2 n)
    (branch : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords (erase2 block.forgetL) ∧
    ∀ address st, AddrValid windowBits windowRoot address st → FBlockClean block st →
      Safe2 read address block.forgetL st →
      branch.kraus (Bridge.signedKet st) =
        c • Bridge.signedKet (ECDSAAdd.run (reference2 read address block.forgetL) m st)

theorem single_sim {n} (read : ConstantBit n → Bool) (b : Block2 n) (C : ECDSAAdd.State → Prop)
    (br : InstrumentBranch) (c : ℂ)
    (h : ∃ m : List Bool, m.length = literalRecords b.code ∧
      ∀ address st, AddrValid windowBits windowRoot address st → C st → BlockSafe2 read address b st →
        br.kraus (Bridge.signedKet st) = c • Bridge.signedKet (ECDSAAdd.run (blockReference2 read address b) m st)) :
    ∃ m : List Bool, m.length = literalRecords (erase2 (b :: [])) ∧
      ∀ address st, AddrValid windowBits windowRoot address st → C st → Safe2 read address (b :: []) st →
        br.kraus (Bridge.signedKet st) = c • Bridge.signedKet (ECDSAAdd.run (reference2 read address (b :: [])) m st) := by
  obtain ⟨m, hm, h⟩ := h
  refine ⟨m, by rw [erase2_single]; exact hm, fun a st hs hc hsafe => ?_⟩
  rw [reference2_single]
  exact h a st hs hc hsafe.1

theorem fblock_sim {n} (read : ConstantBit n → Bool) (block : FBlock2 n) (hg : FBlockGeo block) :
    ∃ cs : List ℂ, List.Forall₂ (FBlockSim read block) (fblockSrc read block).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  cases block with
  | std b =>
    obtain ⟨cs, al, mass⟩ := block_simulationH read bank15 bank15_ok b hg
    refine ⟨cs, al.imp ?_, mass⟩
    intro br c h
    obtain ⟨m, hm, h⟩ := h
    exact single_sim read b (FBlockClean (.std b)) br c
      ⟨m, hm, fun a st hs hc hsafe => h a st hs hc.1 hc.2 hsafe⟩
  | fast f =>
    obtain ⟨cs, al, mass⟩ := f.fused_simulation read hg.1 hg.2
    refine ⟨cs, al.imp ?_, mass⟩
    intro br c h
    obtain ⟨m, hm, h⟩ := h
    exact single_sim read (.unit (siteUnit f.site)) (FBlockClean (.fast f)) br c
      ⟨m, hm, fun a st hs hc hsafe => h a st ⟨hc.1, hs.1, hs.2⟩ hc.2 hsafe⟩
  | fast1 f =>
    obtain ⟨cs, al, mass⟩ := f.fused_simulation read hg.1 hg.2
    refine ⟨cs, al.imp ?_, mass⟩
    intro br c h
    obtain ⟨m, hm, h⟩ := h
    exact single_sim read (.unit (siteUnit f.site)) (FBlockClean (.fast1 f)) br c
      ⟨m, hm, fun a st hs hc hsafe => h a st ⟨hc.1, hs.1, hs.2⟩ hc.2 hsafe⟩
  | pair q =>
    obtain ⟨cs, al, mass⟩ := q.pair_sim read hg
    exact ⟨cs, al.imp (fun _ _ h => h), mass⟩

theorem fblock_addr {n} (read : ConstantBit n → Bool) (b : FBlock2 n) (hg : FBlockGeo b)
    (a : Nat) (st : ECDSAAdd.State) (hs : AddrValid windowBits windowRoot a st)
    (hc : FBlockClean b st) (m : List Bool) :
    AddrValid windowBits windowRoot a (ECDSAAdd.run (reference2 read a b.forgetL) m st) := by
  cases b with
  | std b =>
    rw [show (FBlock2.std b).forgetL = (b :: []) from rfl, reference2_single]
    exact block_addr2 read bank15 b hg a st hs hc.1 m
  | fast f =>
    rw [show (FBlock2.fast f).forgetL = (Block2.unit (siteUnit f.site) :: []) from rfl, reference2_single]
    have hp : ∀ i ∈ f.site.code, PlacedPair windowBits pathBank windowRoot i := fun i hi =>
      placed_implies_pair _ _ _ _ (hg.1.site.placed i hi)
    have h := strict_preserves read windowBits pathBank f.site.code a hp st ⟨hc.1, hs.1, hs.2⟩ m
    exact ⟨h.2.1, h.2.2⟩
  | fast1 f =>
    rw [show (FBlock2.fast1 f).forgetL = (Block2.unit (siteUnit f.site) :: []) from rfl, reference2_single]
    have hp : ∀ i ∈ f.site.code, PlacedPair windowBits pathBank windowRoot i := fun i hi =>
      placed_implies_pair _ _ _ _ (hg.1.site.placed i hi)
    have h := strict_preserves read windowBits pathBank f.site.code a hp st ⟨hc.1, hs.1, hs.2⟩ m
    exact ⟨h.2.1, h.2.2⟩
  | pair q =>
    have hp : ∀ i ∈ erase2 (Block2.unit q.u₁ :: Block2.unit q.u₂ :: []), PlacedPair windowBits pathBank windowRoot i := by
      intro i hi
      rw [erase2_cons, erase2_cons, erase2_nil, List.append_nil, List.mem_append] at hi
      rcases hi with hi | hi
      · exact hg.1.placed i hi
      · exact hg.2.1.placed i hi
    have h := strict_preserves read windowBits pathBank (erase2 (Block2.unit q.u₁ :: Block2.unit q.u₂ :: [])) a hp st
      ⟨hc, hs.1, hs.2⟩ m
    exact ⟨h.2.1, h.2.2⟩

def FSim {n} (read : ConstantBit n → Bool) (code : FCode2 n) (b : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords (erase2 (fforget code)) ∧
    ∀ a st, AddrValid windowBits windowRoot a st → FCodeClean read a code st →
      Safe2 read a (fforget code) st →
      b.kraus (Bridge.signedKet st) = c • Bridge.signedKet (ECDSAAdd.run (reference2 read a (fforget code)) m st)

theorem fsrc_sim {n} (read : ConstantBit n → Bool) (code : FCode2 n) (hg : ∀ b ∈ code, FBlockGeo b) :
    ∃ cs : List ℂ, List.Forall₂ (FSim read code) (fsrc read code).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  induction code with
  | nil =>
    refine ⟨[1], .cons ?_ .nil, by simp⟩
    exact ⟨[], rfl, fun a st _ _ _ => by
      simp [reference2, erase2, fforget, specialize, ECDSAAdd.ShorPort.Tmpl.instantiate, ECDSAAdd.run]⟩
  | cons b code ih =>
    obtain ⟨cs₁, h₁, mass₁⟩ := fblock_sim read b (hg b (by simp))
    obtain ⟨cs₂, h₂, mass₂⟩ := ih (fun c hc => hg c (by simp [hc]))
    refine ⟨coherentSeqCoefficients cs₁ cs₂, ?_, ?_⟩
    · rw [fsrc, AdaptiveCircuit.run_seq]
      apply simulationAligned_seq h₁ h₂
      intro b₁ c₁ b₂ c₂ hb₁ hb₂
      obtain ⟨m₁, len₁, run₁⟩ := hb₁
      obtain ⟨m₂, len₂, run₂⟩ := hb₂
      refine ⟨m₁ ++ m₂, ?_, ?_⟩
      · simp [fforget_cons, erase2_append, List.length_append, len₁, len₂]
      · intro a st hs hc hsafe
        rw [fforget_cons] at hsafe ⊢
        have hm : m₁.length = ECDSAAdd.measurementCount (reference2 read a b.forgetL) :=
          len₁.trans (specialize_counts read (erase2 b.forgetL) a).2.symm
        have hsp := safe2_append_inv read a b.forgetL (fforget code) st hsafe
        have hn := fblock_addr read b (hg b (by simp)) a st hs hc.1 m₁
        change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
        rw [run₁ a st hs hc.1 hsp.1, map_smul,
          run₂ a (ECDSAAdd.run (reference2 read a b.forgetL) m₁ st) hn (hc.2 m₁ hm) (hsp.2 m₁ hm),
          reference2_append, run_append_records _ _ m₁ m₂ st hm]
        simp [smul_smul]
    · rw [simulationCoefficients_mass, mass₁, mass₂]
      norm_num

theorem fprog_coherent {n} (read : ConstantBit n → Bool) (code : FCode2 n) (hg : ∀ b ∈ code, FBlockGeo b)
    (Valid : BasisState → Prop) (result : BasisState → BasisState)
    (hsafe : ∀ s, Valid s → Safe2 read (tableAddressValue windowBits s) (fforget code) ⟨false,s⟩)
    (hclean : ∀ s, Valid s → FCodeClean read (tableAddressValue windowBits s) code ⟨false,s⟩)
    (hrun : ∀ s, Valid s → ∀ m,
      ECDSAAdd.run (reference2 read (tableAddressValue windowBits s) (fforget code)) m ⟨false,s⟩ = ⟨false,result s⟩)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((fprog code start).instantiate read history)
      (Finsupp.lmapDomain ℂ ℂ result) (fun s => s windowRoot = true ∧ Valid s) := by
  obtain ⟨cs, aligned, mass⟩ := fsrc_sim read code hg
  refine ⟨cs, ?_, mass⟩
  rw [fprog_run]
  apply aligned.imp
  intro b c hb s hs
  obtain ⟨m, _, h⟩ := hb
  have he := h (tableAddressValue windowBits s) ⟨false,s⟩ ⟨rfl, hs.1⟩ (hclean s hs.2) (hsafe s hs.2)
  rw [Bridge.signedKet_false, hrun s hs.2 m, Bridge.signedKet_false] at he
  simpa [ket] using he

/-! Resources against the forgotten `Code2` program. -/

def fblockTP {n} : FBlock2 n → Nat
  | .std b => blockTP2 bank15 b + PoolHost.blockExtra b
  | .fast f => f.fusedTP
  | .fast1 f => f.fusedTP
  | .pair q => q.pairTP

def fcodeTP {n} : FCode2 n → Nat
  | [] => 0
  | b :: code => fblockTP b + fcodeTP code

def fblockSave {n} : FBlock2 n → Nat
  | .std _ => 0
  | .fast f => 49152 - ECDSAAdd.toffoliCount f.swapNet
  | .fast1 f => 32768 - ECDSAAdd.toffoliCount f.swapNet
  | .pair _ => UnitPair.pairSave

def fsave {n} : FCode2 n → Nat
  | [] => 0
  | b :: code => fblockSave b + fsave code

def fblockRSave {n} : FBlock2 n → Nat
  | .std _ => 0
  | .fast f => 49152 - f.garb.length
  | .fast1 f => 32768 - f.garb.length
  | .pair q => q.pairRSave

def frsave {n} : FCode2 n → Nat
  | [] => 0
  | b :: code => fblockRSave b + frsave code

def fblockSlack {n} : FBlock2 n → Nat
  | .std _ => 26
  | .fast f => f.fastSlack
  | .fast1 f => f.fastSlack
  | .pair _ => 52

def fslack {n} : FCode2 n → Nat
  | [] => 0
  | b :: code => fblockSlack b + fslack code

theorem fblock_tCount {n} (read : ConstantBit n → Bool) (b : FBlock2 n) (hg : FBlockGeo b)
    (start : Nat) (history : Fin start → Bool) :
    ((fblockProg b start).instantiate read history).tCount = 7 * fblockTP b := by
  cases b with
  | std b => exact blockH_tCount read bank15 b (geo_lay2 bank15 bank15_ok b hg) start history
  | fast f => exact f.fused_tCount read hg.1 start history
  | fast1 f => exact f.fused_tCount read hg.1 start history
  | pair q => exact q.pair_tCount read hg start history

theorem fprog_tCount {n} (read : ConstantBit n → Bool) (code : FCode2 n) (hg : ∀ b ∈ code, FBlockGeo b)
    (start : Nat) (history : Fin start → Bool) :
    ((fprog code start).instantiate read history).tCount = 7 * fcodeTP code := by
  induction code generalizing start with
  | nil => simp [fprog, frecs, fcodeTP, Straight.instantiate, AdaptiveCircuit.tCount]
  | cons b code ih =>
    rw [fprog, castFinish_instantiate,
      append_tCount_fixed _ _ _ _ _ (fun h => ih (fun d hd => hg d (by simp [hd])) _ h),
      fblock_tCount read b (hg b (by simp))]
    simp only [fcodeTP]; ring

theorem fcodeTP_relation {n} (code : FCode2 n) (hg : ∀ b ∈ code, FBlockGeo b) :
    fcodeTP code + fsave code = codeTP2 bank15 (fforget code) + PoolHost.codeExtra (fforget code) := by
  induction code with
  | nil => rfl
  | cons b code ih =>
    have ih' := ih (fun d hd => hg d (by simp [hd]))
    have hb : fblockTP b + fblockSave b = codeTP2 bank15 b.forgetL + PoolHost.codeExtra b.forgetL := by
      have hgb := hg b (by simp)
      cases b with
      | std b => simp [fblockTP, fblockSave, FBlock2.forgetL, codeTP2, PoolHost.codeExtra]
      | fast f =>
        have h := f.fused_tp_relation hgb.1
        simp only [fblockTP, fblockSave, FBlock2.forgetL, codeTP2, PoolHost.codeExtra, PoolHost.blockExtra]
        omega
      | fast1 f =>
        have h := f.fused_tp_relation hgb.1
        simp only [fblockTP, fblockSave, FBlock2.forgetL, codeTP2, PoolHost.codeExtra, PoolHost.blockExtra]
        omega
      | pair q =>
        have h := q.pair_tp_relation
        simp only [fblockTP, fblockSave, FBlock2.forgetL, codeTP2, PoolHost.codeExtra, PoolHost.blockExtra]
        omega
    simp only [fcodeTP, fsave, fforget_cons, codeTP2_append, PoolHost.codeExtra_append]
    omega

theorem frecs_relation {n} (code : FCode2 n) (hg : ∀ b ∈ code, FBlockGeo b) :
    frecs code + frsave code = recordsP2 bank15 (fforget code) := by
  induction code with
  | nil => rfl
  | cons b code ih =>
    have ih' := ih (fun d hd => hg d (by simp [hd]))
    have hb : fblockRec b + fblockRSave b = recordsP2 bank15 b.forgetL := by
      have hgb := hg b (by simp)
      cases b with
      | std b => simp [fblockRec, fblockRSave, FBlock2.forgetL, recordsP2]
      | fast f =>
        have h := f.fused_records_relation hgb.1
        simp only [fblockRec, fblockRSave, FBlock2.forgetL, recordsP2]
        omega
      | fast1 f =>
        have h := f.fused_records_relation hgb.1
        simp only [fblockRec, fblockRSave, FBlock2.forgetL, recordsP2]
        omega
      | pair q =>
        have h := q.pair_records_relation
        simp only [fblockRec, fblockRSave, FBlock2.forgetL, recordsP2]
        omega
    simp only [frecs, frsave, fforget_cons, recordsP2_append]
    omega

theorem fprog_slots {n} (code : FCode2 n) (hg : ∀ b ∈ code, FBlockGeo b) (start : Nat) :
    (fprog code start).gateSlots ≤ codeSP2 bank15 (fforget code) + fslack code := by
  induction code generalizing start with
  | nil => simp [fprog, frecs, fslack, Straight.gateSlots, codeSP2]
  | cons b code ih =>
    have ih' := ih (fun d hd => hg d (by simp [hd])) (start + fblockRec b)
    have hb : (fblockProg b start).gateSlots ≤ codeSP2 bank15 b.forgetL + fblockSlack b := by
      have hgb := hg b (by simp)
      cases b with
      | std b =>
        rw [show fblockProg (.std b) start = blockProgH bank15 b start from rfl]
        have h := blockH_slots bank15 b (geo_lay2 bank15 bank15_ok b hgb) start
        simp only [FBlock2.forgetL, codeSP2, fblockSlack]
        omega
      | fast f =>
        have h := f.fused_slots hgb.1 start
        simp only [FBlock2.forgetL, codeSP2, fblockSlack]
        change (f.fusedProgram start).gateSlots ≤ _
        omega
      | fast1 f =>
        have h := f.fused_slots hgb.1 start
        simp only [FBlock2.forgetL, codeSP2, fblockSlack]
        change (f.fusedProgram start).gateSlots ≤ _
        omega
      | pair q =>
        have h := q.pair_slots hgb start
        simp only [FBlock2.forgetL, codeSP2, fblockSlack]
        change (q.pairProgram start).gateSlots ≤ _
        omega
    rw [fprog, castFinish_gateSlots, Straight.gateSlots_append]
    simp only [fforget_cons, codeSP2_append, fslack]
    omega

theorem fblock_wellFormed {n} (b : FBlock2 n) (hg : FBlockGeo b)
    (hp : ∀ p, WInstr.literal p ∈ erase2 b.forgetL → GatePhysical p) (start : Nat) :
    (fblockProg b start).WellFormed := by
  cases b with
  | std b =>
    show (blockProgH bank15 b start).WellFormed
    exact blockH_wellFormed bank15 bank15_ok b hg (fun p hm => hp p (by simpa [FBlock2.forgetL, erase2] using hm)) start
  | fast f =>
    exact f.fused_wellFormed hg.1
      (fun p hm => hp p (by simpa [FBlock2.forgetL, erase2, Block2.code, siteUnit_code] using hm)) start
  | fast1 f =>
    exact f.fused_wellFormed hg.1
      (fun p hm => hp p (by simpa [FBlock2.forgetL, erase2, Block2.code, siteUnit_code] using hm)) start
  | pair q =>
    exact q.pair_wellFormed hg
      (fun p hm => hp p (by simpa [FBlock2.forgetL, erase2, Block2.code] using hm)) start

theorem fprog_wellFormed {n} (code : FCode2 n) (hg : ∀ b ∈ code, FBlockGeo b)
    (hp : ∀ p, WInstr.literal p ∈ erase2 (fforget code) → GatePhysical p) (start : Nat) :
    (fprog code start).WellFormed := by
  induction code generalizing start with
  | nil => trivial
  | cons b code ih =>
    rw [fprog, castFinish_wellFormed]
    apply straight_append_wellFormed
    · exact fblock_wellFormed b (hg b (by simp))
        (fun p hm => hp p (by rw [fforget_cons, erase2_append]; exact List.mem_append_left _ hm)) start
    · exact ih (fun d hd => hg d (by simp [hd]))
        (fun p hm => hp p (by rw [fforget_cons, erase2_append]; exact List.mem_append_right _ hm)) _

theorem fprog_residue {n} (code : FCode2 n) (start : Nat) : AndGadget.residue (fprog code start) = 0 := by
  induction code generalizing start with
  | nil => simp [fprog, frecs]
  | cons b code ih =>
    have hb : AndGadget.residue (fblockProg b start) = 0 := by
      cases b with
      | std b => exact blockH_residue bank15 b start
      | fast f => exact f.fused_residue start
      | fast1 f => exact f.fused_residue start
      | pair q => exact q.pair_residue start
    simp [fprog, AndGadget.residue_cast, AndGadget.residue_append, hb, ih]

/-! Moving between a fused pair and its two standard units. -/

theorem fforget_pair {n} (pre post : FCode2 n) (q : UnitPair n) :
    fforget (pre ++ FBlock2.pair q :: post) =
      fforget (pre ++ FBlock2.std (.unit q.u₁) :: FBlock2.std (.unit q.u₂) :: post) := by
  simp [FBlock2.forgetL]

theorem clean_pair {n} (read : ConstantBit n → Bool) (a : Nat) (pre post : FCode2 n) (q : UnitPair n)
    (st : ECDSAAdd.State)
    (h : FCodeClean read a (pre ++ FBlock2.std (.unit q.u₁) :: FBlock2.std (.unit q.u₂) :: post) st) :
    FCodeClean read a (pre ++ FBlock2.pair q :: post) st := by
  induction pre generalizing st with
  | nil =>
    have hfl : (FBlock2.pair q).forgetL = (Block2.unit q.u₁ :: Block2.unit q.u₂ :: []) := rfl
    have hf1 : (FBlock2.std (Block2.unit q.u₁)).forgetL = (Block2.unit q.u₁ :: []) := rfl
    have hf2 : (FBlock2.std (Block2.unit q.u₂)).forgetL = (Block2.unit q.u₂ :: []) := rfl
    refine ⟨h.1.1, fun m hm => ?_⟩
    rw [hfl, reference2_cons, reference2_single, ECDSAAdd.measurementCount_append] at hm
    rw [hfl]
    set k := ECDSAAdd.measurementCount (blockReference2 read a (.unit q.u₁)) with hk
    have hlen : (m.take k).length = k := by rw [List.length_take]; omega
    have h1 := h.2 (m.take k) (by rw [hf1, reference2_single]; exact hlen)
    rw [hf1, reference2_single] at h1
    have h2 := h1.2 (m.drop k) (by rw [hf2, reference2_single, List.length_drop]; omega)
    rw [hf2, reference2_single] at h2
    rw [reference2_cons, reference2_single, ← List.take_append_drop k m, run_append_records _ _ _ _ st hlen]
    exact h2
  | cons x pre ih =>
    exact ⟨h.1, fun m hm => ih _ (h.2 m hm)⟩

theorem fcodeTP_pair {n} (pre post : FCode2 n) (q : UnitPair n) :
    fcodeTP (pre ++ FBlock2.pair q :: post) + UnitPair.pairSave =
      fcodeTP (pre ++ FBlock2.std (.unit q.u₁) :: FBlock2.std (.unit q.u₂) :: post) := by
  induction pre with
  | nil =>
    have h := q.pair_tp_relation
    simp only [List.nil_append, fcodeTP, fblockTP, PoolHost.blockExtra]
    omega
  | cons x pre ih =>
    simp only [List.cons_append, fcodeTP]
    omega

theorem frecs_pair {n} (pre post : FCode2 n) (q : UnitPair n) :
    frecs (pre ++ FBlock2.pair q :: post) + q.pairRSave =
      frecs (pre ++ FBlock2.std (.unit q.u₁) :: FBlock2.std (.unit q.u₂) :: post) := by
  induction pre with
  | nil =>
    have h := q.pair_records_relation
    simp only [List.nil_append, frecs, fblockRec]
    omega
  | cons x pre ih =>
    simp only [List.cons_append, frecs]
    omega

theorem fsave_pair {n} (pre post : FCode2 n) (q : UnitPair n) :
    fsave (pre ++ FBlock2.pair q :: post) =
      fsave (pre ++ FBlock2.std (.unit q.u₁) :: FBlock2.std (.unit q.u₂) :: post) + UnitPair.pairSave := by
  induction pre with
  | nil => simp only [List.nil_append, fsave, fblockSave]; omega
  | cons x pre ih => simp only [List.cons_append, fsave]; omega

theorem frsave_pair {n} (pre post : FCode2 n) (q : UnitPair n) :
    frsave (pre ++ FBlock2.pair q :: post) =
      frsave (pre ++ FBlock2.std (.unit q.u₁) :: FBlock2.std (.unit q.u₂) :: post) + q.pairRSave := by
  induction pre with
  | nil => simp only [List.nil_append, frsave, fblockRSave]; omega
  | cons x pre ih => simp only [List.cons_append, frsave]; omega

theorem fslack_pair {n} (pre post : FCode2 n) (q : UnitPair n) :
    fslack (pre ++ FBlock2.pair q :: post) =
      fslack (pre ++ FBlock2.std (.unit q.u₁) :: FBlock2.std (.unit q.u₂) :: post) := by
  induction pre with
  | nil => simp only [List.nil_append, fslack, fblockSlack]; omega
  | cons x pre ih => simp only [List.cons_append, fslack]; omega

end
end ShorECDLP.Entrant.WideBank8.Fast16

namespace ShorECDLP.Entrant.WideBank8.Row16
open ShorECDLP.Entrant.WideSigned
open Quantum Challenge Secp256k1 Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] WEXFast.rowCF WEXUnlookup.rowC Fast16.fprog
  Straight.WellFormed Straight.instantiate AdaptiveCircuit.run

def rows : Nat → Fin 65536 := Geometry.rows .w16
def fast (f : WEXFast.FastSite 32768) : Fast16.FastSite 65536 :=
  ⟨Rows.site rows f.site, f.g1, f.g2, f.g3⟩
def fast1 (f : WEXFast.FastSite1 32768) : Fast16.FastSite1 65536 :=
  ⟨Rows.site rows f.site, f.g1⟩
def lift : WEXFast.FBlock2 32768 → Fast16.FBlock2 65536
  | .std b => .std (Rows.block rows b)
  | .fast f => .fast (fast f)
  | .fast1 f => .fast1 (fast1 f)
/-- The row before the corner fusion: the narrow fast row lifted block by block. -/
def code₀ : Fast16.FCode2 65536 := WEXFast.rowCF.map lift

theorem forget_lift (b : WEXFast.FBlock2 32768) :
    (lift b).forgetL = (Rows.block rows b.forget :: []) := by
  cases b with
  | std b => rfl
  | fast f =>
    simp [lift, fast, Fast16.FBlock2.forgetL, WEXFast.FBlock2.forget, Fast16.siteUnit,
      WEXFast.siteUnit, Rows.block, Rows.unit, Rows.site, Rows.code, Rows.instr, MaskedSite.prefix]
  | fast1 f =>
    simp [lift, fast1, Fast16.FBlock2.forgetL, WEXFast.FBlock2.forget, Fast16.siteUnit,
      WEXFast.siteUnit, Rows.block, Rows.unit, Rows.site, Rows.code, Rows.instr, MaskedSite.prefix]

theorem fforget_lift (c : WEXFast.FCode2 32768) :
    Fast16.fforget (c.map lift) = Rows.blocks rows (WEXFast.fforget c) := by
  induction c with
  | nil => rfl
  | cons b c ih =>
    rw [List.map_cons, Fast16.fforget_cons, ih, forget_lift]
    rfl

theorem forget₀ : Fast16.fforget code₀ = Geometry.row .w16 := by
  rw [code₀, fforget_lift, WEXFast.fforget_rowCF]
  rfl

theorem tripleF_bank8 : ∀ i : Fin 256, WEXFast.tripleF.g1.headD 0 + i.val ∈ WEXFast.tripleF.g1 := by
  intro i
  have hi := i.isLt
  show (List.range' 14371 256).headD 0 + i.val ∈ List.range' 14371 256
  rw [show (List.range' 14371 256).headD 0 = 14371 from rfl, List.mem_range'_1]
  omega

theorem site2F_bank8 : ∀ i : Fin 256, WEXFast.site2F.g1.headD 0 + i.val ∈ WEXFast.site2F.g1 := by
  intro i
  have hi := i.isLt
  show (List.range' 14115 258 ++ List.range' 14884 254).headD 0 + i.val ∈
    List.range' 14115 258 ++ List.range' 14884 254
  rw [show (List.range' 14115 258 ++ List.range' 14884 254).headD 0 = 14115 from rfl, List.mem_append,
    List.mem_range'_1]
  left
  omega

theorem fast_geometry (f : WEXFast.FastSite 32768) (hg : WEXFast.FastGeometry f)
    (hm : Block2.unit (WEXFast.siteUnit f.site) ∈ WEXUnlookup.rowC)
    (h48 : ∀ w ∈ f.garb, w ≠ 14848)
    (hb8 : ∀ i : Fin 256, f.g1.headD 0 + i.val ∈ f.g1) : Fast16.FastGeometry (fast f) := by
  refine ⟨PoolHost.extend_site_wide Fast16.bank15 rfl rfl (WEXFast.siteUnit f.site) hm hg.site, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [fast, Rows.site, Rows.ports] using hg.len1
  · simpa [fast, Rows.site, Rows.ports] using hg.len2
  · simpa [fast, Rows.site, Rows.ports] using hg.len3
  · simpa only [fast, Rows.site, Rows.targets, Fast16.FastSite.garb, WEXFast.FastSite.garb] using hg.nodup
  · exact hg.bounds
  · exact fun w hw => ⟨hg.free w hw, h48 w hw⟩
  · exact hg.head
  · exact hb8

theorem fast1_geometry (f : WEXFast.FastSite1 32768) (hg : WEXFast.FastGeometry1 f)
    (hm : Block2.unit (WEXFast.siteUnit f.site) ∈ WEXUnlookup.rowC)
    (h48 : ∀ w ∈ f.garb, w ≠ 14848)
    (hb8 : ∀ i : Fin 256, f.g1.headD 0 + i.val ∈ f.g1) : Fast16.FastGeometry1 (fast1 f) := by
  refine ⟨PoolHost.extend_site_wide Fast16.bank15 rfl rfl (WEXFast.siteUnit f.site) hm hg.site, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [fast1, Rows.site, Rows.ports] using hg.len1
  · simpa only [fast1, Rows.site, Rows.targets, Fast16.FastSite1.garb, WEXFast.FastSite1.garb] using hg.nodup
  · exact hg.bounds
  · exact fun w hw => ⟨hg.free w hw, h48 w hw⟩
  · exact hg.head
  · exact hb8

/-- Lifting to sixteen-bit rows keeps the guard and the literal arithmetic. -/
theorem guardKept_lift (s : MaskedSite 32768) (h : GuardKept s) : GuardKept (Rows.site rows s) := by
  rcases h with h | ⟨p, hp, hw⟩
  · exact Or.inl h
  · exact Or.inr ⟨p, by simp only [Rows.site, Rows.code, hp, List.map_cons, List.map_nil, Rows.instr], hw⟩

theorem tripleF_no48 : ∀ w ∈ WEXFast.tripleF.garb, w ≠ 14848 := by
  intro w hw
  simp only [WEXFast.FastSite.garb, WEXFast.tripleF, List.mem_append, List.mem_range'_1] at hw
  dsimp only [Wire] at *
  omega

theorem site2F_no48 : ∀ w ∈ WEXFast.site2F.garb, w ≠ 14848 := by
  intro w hw
  simp only [WEXFast.FastSite1.garb, WEXFast.site2F, WEXFast.site2G, List.mem_append, List.mem_range'_1] at hw
  dsimp only [Wire] at *
  omega

theorem geometry₀ : ∀ b ∈ code₀, Fast16.FBlockGeo b := by
  intro b hb
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hb
  cases old with
  | std b =>
    have hm : b ∈ WEXUnlookup.rowC := by
      rw [← WEXFast.fforget_rowCF]
      exact List.mem_map.mpr ⟨.std b, ho, rfl⟩
    cases b with
    | plain c =>
      exact Geometry.row_geometry .w16 _ (List.mem_map.mpr ⟨.plain c, hm, rfl⟩)
    | unit u =>
      exact PoolHost.extend_unit_wide Fast16.bank15 rfl rfl u hm (PathShare.rowC_geo15 _ hm)
  | fast f =>
    have he := WEXFast.fast_mem_rowCF f ho
    subst f
    exact ⟨fast_geometry _ WEXFast.tripleF_geometry WEXFast.triple_unit_mem tripleF_no48 tripleF_bank8,
      guardKept_lift _ triple_guardKept⟩
  | fast1 f =>
    have he := WEXFast.fast1_mem_rowCF f ho
    subst f
    exact ⟨fast1_geometry _ WEXFast.site2F_geometry WEXFast.site2_unit_mem site2F_no48 site2F_bank8,
      guardKept_lift _ site2_guardKept⟩

theorem litProg_lift (c : WCode 32768) : litProg (Rows.code rows c) = litProg c := by
  induction c with
  | nil => rfl
  | cons i c ih =>
    simp only [Rows.code] at ih
    cases i <;> simp [Rows.code, Rows.instr, litProg, ih]

theorem host_lift (b : Block2 32768) (st : ECDSAAdd.State) (h : HostOK b st) : HostOK (Rows.block rows b) st := by
  cases b with
  | plain c => simpa only [Rows.block, HostOK, litProg_lift] using h
  | unit u => trivial

theorem host4_lift (b : Block2 32768) (st : ECDSAAdd.State) (h : PoolHost.HostOK4 b st) :
    PoolHost.HostOK4 (Rows.block rows b) st := by
  cases b with
  | plain c => simpa only [Rows.block, PoolHost.HostOK4, litProg_lift] using h
  | unit u => trivial

theorem old_instr_placed (b : WEXFast.FBlock2 32768) (hb : b ∈ WEXFast.rowCF) :
    ∀ i ∈ b.forget.code, PlacedPair windowBits windowPaths windowRoot i := by
  intro i hi
  apply WEXUnlookup.rowC_placed
  rw [← WEXFast.fforget_rowCF, WEXFast.fforget, erase2]
  exact List.mem_flatMap.mpr ⟨b.forget, List.mem_map.mpr ⟨b, hb, rfl⟩, hi⟩

theorem clean_lift (coeffs : Fin 65536 → PointCoeff) (Q : Point) (a : Nat)
    (c : WEXFast.FCode2 32768) (st : ECDSAAdd.State)
    (hold : WEXFast.FCodeClean (readConstant (fun _ : Fin 32768 => coeffs (rows a)) Q) a c st)
    (hextra : CodeClean2 (readConstant (fun _ : Fin 32768 => coeffs (rows a)) Q) PoolHost.poolBand a (WEXFast.fforget c) st)
    (hhost4 : PoolHost.CodeHost4_2 (readConstant (fun _ : Fin 32768 => coeffs (rows a)) Q) a (WEXFast.fforget c) st) :
    Fast16.FCodeClean (readConstant coeffs Q) a (c.map lift) st := by
  induction c generalizing st with
  | nil => trivial
  | cons b c ih =>
    have hbank (h : Clean PathShare.pathBank st.basis) (h48 : Clean PoolHost.poolBand st.basis) :
        Clean Fast16.pathBank st.basis := by
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact h v hv
      · have he : v = 14848 := by simpa using hv
        subst v
        exact h48 14848 PoolHost.mem_14848_poolBand
    refine ⟨?_, ?_⟩
    · cases b with
      | std b =>
        refine ⟨?_, ⟨host_lift b st hold.1.2, host4_lift b st hhost4.1⟩⟩
        cases b with
        | plain p => trivial
        | unit u => exact hbank hold.1.1 hextra.1
      | fast f =>
        refine ⟨hbank hold.1.1 hextra.1, ?_⟩
        simpa only [lift, fast, Rows.site, Rows.targets, Fast16.FastSite.garb,
          WEXFast.FastSite.garb] using hold.1.2
      | fast1 f =>
        refine ⟨hbank hold.1.1 hextra.1, ?_⟩
        simpa only [lift, fast1, Rows.site, Rows.targets, Fast16.FastSite1.garb,
          WEXFast.FastSite1.garb] using hold.1.2
    · intro m hm
      have he : reference2 (readConstant coeffs Q) a (lift b).forgetL =
          blockReference2 (readConstant (fun _ : Fin 32768 => coeffs (rows a)) Q) a b.forget := by
        rw [forget_lift, Fast16.reference2_single, Rows.block_reference]
      rw [he] at hm ⊢
      exact ih _ (hold.2 m hm) (hextra.2 m hm) (hhost4.2 m hm)

/-! The corner fusion: the corner's `y` clear is deferred into its comparison clear. -/

def corner : Fast16.UnitPair 65536 :=
  ⟨Rows.unit rows WEXUnlookup.cornerUnit₁, Rows.unit rows WEXUnlookup.cornerUnit₂⟩

def headF : WEXFast.FCode2 32768 :=
  (WEXUnlookup.rowPre3.map toBlock2).map WEXFast.FBlock2.std ++
    (WEXFast.fgeneric3 ++ (WEXFast.FBlock2.std (.plain WEX.cornerNeg) :: []))

def tailF : WEXFast.FCode2 32768 :=
  (WEXFast.FBlock2.std (.plain WEX.sfxTailF) :: WEXFast.FBlock2.std (.plain (wLiteral [.X 838])) :: [])

theorem code₀_split : code₀ = headF.map lift ++
    Fast16.FBlock2.std (.unit corner.u₁) :: Fast16.FBlock2.std (.unit corner.u₂) :: tailF.map lift := by
  rw [code₀, WEXFast.rowCF]
  simp [headF, tailF, corner, WEXUnlookup.rowPost3, lift, Rows.block]

def code : Fast16.FCode2 65536 := headF.map lift ++ Fast16.FBlock2.pair corner :: tailF.map lift

theorem mem_code₀ (b : Fast16.FBlock2 65536) (hb : b ∈ code) (hp : ∀ q, b ≠ .pair q) : b ∈ code₀ := by
  rw [code, List.mem_append, List.mem_cons] at hb
  rw [code₀_split, List.mem_append, List.mem_cons, List.mem_cons]
  rcases hb with hb | rfl | hb
  · exact Or.inl hb
  · exact absurd rfl (hp corner)
  · exact Or.inr (Or.inr (Or.inr hb))

theorem corner₁_mem : Fast16.FBlock2.std (.unit corner.u₁) ∈ code₀ := by
  rw [code₀_split]
  exact List.mem_append_right _ (List.mem_cons.mpr (Or.inl rfl))

theorem corner₂_mem : Fast16.FBlock2.std (.unit corner.u₂) ∈ code₀ := by
  rw [code₀_split]
  exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl rfl)))

theorem corner_geo : corner.Geo :=
  ⟨geometry₀ _ corner₁_mem, geometry₀ _ corner₂_mem, rfl, rfl⟩

theorem forget : Fast16.fforget code = Geometry.row .w16 := by
  rw [code, Fast16.fforget_pair, ← code₀_split, forget₀]

theorem geometry : ∀ b ∈ code, Fast16.FBlockGeo b := by
  intro b hb
  by_cases hp : ∀ q, b ≠ .pair q
  · exact geometry₀ b (mem_code₀ b hb hp)
  · push_neg at hp
    obtain ⟨q, rfl⟩ := hp
    rw [code, List.mem_append, List.mem_cons] at hb
    rcases hb with hb | hb | hb
    · obtain ⟨old, -, he⟩ := List.mem_map.mp hb
      cases old <;> cases he
    · cases hb
      exact corner_geo
    · obtain ⟨old, -, he⟩ := List.mem_map.mp hb
      cases old <;> cases he

theorem clean_fused (read : ConstantBit 65536 → Bool) (a : Nat) (st : ECDSAAdd.State)
    (h : Fast16.FCodeClean read a (WEXFast.rowCF.map lift) st) : Fast16.FCodeClean read a code st := by
  have h' : Fast16.FCodeClean read a code₀ st := h
  rw [code₀_split] at h'
  exact Fast16.clean_pair read a _ _ corner st h'

def program (start : Nat) := Fast16.fprog code start

theorem coherent (coeffs : Fin 65536 → PointCoeff) (Q : Point)
    (hQ : order • Q = 0) (hn : ∀ i, constantPoint Q (coeffs i) ≠ 0)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((program start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (Add.update .w16 coeffs Q)) liveReady := by
  have h := Fast16.fprog_coherent (readConstant coeffs Q) code geometry liveReady (Add.update .w16 coeffs Q)
    (fun s hs => by rw [forget]; exact Rows.row_safe _ _ _ hQ hn _ s hs)
    (fun s hs => clean_fused _ _ _ (clean_lift coeffs Q _ _ _
      (WEXFast.rowCF_clean (fun _ => coeffs (rows (tableAddressValue Fast16.windowBits s))) Q hQ
        (fun _ => hn _) _ s hs)
      (PoolHost.poolBand_clean_in_rowCF (fun _ => coeffs (rows (tableAddressValue Fast16.windowBits s))) Q hQ
        (fun _ => hn _) _ s hs)
      (by
        rw [WEXFast.fforget_rowCF]
        exact PoolHost.rowC_host4 (fun _ => coeffs (rows (tableAddressValue Fast16.windowBits s))) Q hQ
          (fun _ => hn _) _ s hs)))
    (fun s hs m => by rw [forget]; exact Rows.row_run _ _ _ hQ hn _ s hs m) start history
  obtain ⟨cs, aligned, mass⟩ := h
  exact ⟨cs, aligned.imp (fun b c hb s hs => hb s ⟨hs.2.2, hs⟩), mass⟩

theorem wellFormed (start : Nat) : (program start).WellFormed := by
  apply Fast16.fprog_wellFormed _ geometry
  rw [forget]
  exact Geometry.row_physical .w16

theorem tCount (read : ConstantBit 65536 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((program start).instantiate read history).tCount = 7 * Fast16.fcodeTP code :=
  Fast16.fprog_tCount read code geometry start history

end
end ShorECDLP.Entrant.WideBank8.Row16

namespace ShorECDLP.Entrant.WideBank8.Counts
open ShorECDLP.Entrant.WideSigned
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare Geometry
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount
  ECDSAAdd.Baselines.normalizeProgram literalToffolis literalRecords normalizeW

theorem lift_metrics {n} (r : Nat → Fin n) (c : WCode 32768) :
    literalToffolis (Rows.code r c) = literalToffolis c ∧
    literalRecords (Rows.code r c) = literalRecords c ∧
    traversals (Rows.code r c) = traversals c := by
  induction c with
  | nil => simp [Rows.code, literalToffolis, literalRecords, traversals]
  | cons i c ih =>
    cases i <;> simpa [Rows.code, Rows.instr, literalToffolis, literalRecords, traversals] using ih

theorem lift_normal_code {n} (r : Nat → Fin n) (c : WCode 32768) :
    normalizeW (Rows.code r c) = Rows.code r (normalizeW c) := by
  induction c with
  | nil => simp [normalizeW, Rows.code]
  | cons i c ih =>
    cases i <;> simpa [Rows.code, Rows.instr, normalizeW, normalizeWInstr] using ih

theorem lift_normal_metrics {n} (r : Nat → Fin n) (c : WCode 32768) :
    literalToffolis (normalizeW (Rows.code r c)) = literalToffolis (normalizeW c) := by
  rw [lift_normal_code, (lift_metrics r (normalizeW c)).1]

theorem lifted_credit {n} (r : Nat → Fin n) (B : PathShare.Bank) (c : Code2 32768) :
    codeTP2 B (Rows.blocks r c) + masks2 c * (2 ^ B.bits.length - 1) =
      literalToffolis (normalizeW (erase2 c)) + traversals (erase2 c) * (2 ^ B.bits.length - 1) +
        masks2 c * ((tableAddressTree B.high 0 1).internalNodes + 247) := by
  induction c with
  | nil => simp [Rows.blocks, codeTP2, masks2, erase2, normalizeW, literalToffolis, traversals]
  | cons b c ih =>
    have hb : blockTP2 B (Rows.block r b) + blockMasks2 b * (2 ^ B.bits.length - 1) =
        literalToffolis (normalizeW b.code) + traversals b.code * (2 ^ B.bits.length - 1) +
          blockMasks2 b * ((tableAddressTree B.high 0 1).internalNodes + 247) := by
      cases b with
      | plain p =>
        simp [Rows.block, blockTP2, blockMasks2, Block2.code, lift_normal_metrics, (lift_metrics r p).2.2]
      | unit u =>
        rw [show (Rows.block r (Block2.unit u)) = .unit (Rows.unit r u) from rfl]
        simp only [blockTP2, Rows.unit, lift_normal_metrics, (lift_metrics r u.pre).2.2,
          Block2.code, UnitSite.code, normalize_append, literalToffolis_append, traversals_append,
          blockMasks2, Nat.one_mul]
        simp [normalizeW, normalizeWInstr, literalToffolis, traversals]
        ring
    simp only [Rows.blocks, List.map_cons, codeTP2, masks2, erase2_cons, normalize_append,
      literalToffolis_append, traversals_append, Nat.add_mul] at ih ⊢
    omega

end
end ShorECDLP.Entrant.WideBank8.Counts

namespace ShorECDLP.Entrant.WideBank8.Counts
open ShorECDLP.Entrant.WideSigned
open Quantum Challenge Secp256k1
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
attribute [local irreducible] codeTP2 WEXUnlookup.ccx2 literalToffolis normalizeW

theorem credit_change {n} (r : Nat → Fin n) (B : PathShare.Bank) (c : Code2 32768)
    (hb : B.bits.length = 16) (hn : (tableAddressTree B.high 0 1).internalNodes = 255)
    (hm : masks2 c = 5) (ht : traversals (erase2 c) = 9) :
    codeTP2 B (Rows.blocks r c) = WEXUnlookup.ccx2 c + 131707 := by
  have hw := lifted_credit r B c
  have ho := WEXUnlookup.ccx2_relation c
  rw [hb, hn, hm, ht] at hw
  rw [hm, ht] at ho
  omega

end
end ShorECDLP.Entrant.WideBank8.Counts

namespace ShorECDLP.Entrant.WideBank8.Row16
open ShorECDLP.Entrant.WideSigned
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] code Fast16.fprog WEXFast.rowCF WEXUnlookup.rowC
  ECDSAAdd.toffoliCount ECDSAAdd.Baselines.normalizeProgram literalToffolis normalizeW
  Fast16.fcodeTP Fast16.fsave WEXFast.fcodeTP WEXUnlookup.ccx2 codeTP2

theorem saving₀ : Fast16.fsave code₀ = 80640 := by
  have hp : (fast WEXFast.tripleF).site.ports.length = 256 := by
    simpa [fast, Rows.site, Rows.ports, WEXFast.tripleF] using WEXFast.tripleSite_length
  have hp1 : (fast1 WEXFast.site2F).site.ports.length = 512 := by
    have hl := WEXFast.site2F_geometry.len1
    have hg := WEXFast.site2F_garb_length
    change WEXFast.site2F.g1.length = 512 at hg
    have h := hl.symm.trans hg
    simpa [fast1, Rows.site, Rows.ports] using h
  have hs := Fast16.FastSite.swapNet_toff (fast WEXFast.tripleF)
    (fast_geometry _ WEXFast.tripleF_geometry WEXFast.triple_unit_mem tripleF_no48 tripleF_bank8)
  have hs1 := Fast16.FastSite1.swapNet_toff (fast1 WEXFast.site2F)
    (fast1_geometry _ WEXFast.site2F_geometry WEXFast.site2_unit_mem site2F_no48 site2F_bank8)
  rw [hp] at hs
  rw [hp1] at hs1
  have hstd (c : WEXUnlookup.Code2 32768) : Fast16.fsave ((c.map WEXFast.FBlock2.std).map lift) = 0 := by
    induction c with
    | nil => simp [Fast16.fsave]
    | cons b c ih => simpa [Fast16.fsave, Fast16.fblockSave, lift] using ih
  have happ (a b : Fast16.FCode2 65536) : Fast16.fsave (a ++ b) = Fast16.fsave a + Fast16.fsave b := by
    induction a with
    | nil => simp [Fast16.fsave]
    | cons x a ih => simp [Fast16.fsave, ih, Nat.add_assoc]
  rw [code₀, WEXFast.rowCF, List.map_append, List.map_append, happ, happ, hstd, hstd]
  simp only [WEXFast.fgeneric3, List.map_cons, List.map_nil, lift, Fast16.fsave,
    Fast16.fblockSave, hs, hs1]

theorem saving : Fast16.fsave code = 81142 := by
  rw [code, Fast16.fsave_pair, ← code₀_split, saving₀, Fast16.UnitPair.pairSave, Fast16.bank_tree_nodes]

theorem cost_arith (fresh old wideStd oldStd extra : Nat)
    (hnew : fresh + 81142 = wideStd + extra) (hold : old + 38930 = oldStd)
    (hwide : wideStd = oldStd + 131707) (he : extra ≤ 6) : fresh ≤ old + 89501 := by omega

theorem fast_standard_relation :
    Fast16.fcodeTP code + 81142 = codeTP2 Fast16.bank15 (Geometry.row .w16) + PoolHost.codeExtra (Geometry.row .w16) := by
  have h := Fast16.fcodeTP_relation code geometry
  rw [saving, forget] at h
  exact h

theorem wide_standard_relation :
    codeTP2 Fast16.bank15 (Geometry.row .w16) = WEXUnlookup.ccx2 WEXUnlookup.rowC + 131707 :=
  Counts.credit_change rows Fast16.bank15 WEXUnlookup.rowC rfl Fast16.high_nodes
    WEXUnlookup.rowC_masks WEXUnlookup.rowC_measures.2.1

theorem credit_increment : Fast16.fcodeTP code ≤ WEXFast.fcodeTP WEXFast.rowCF + 89501 := by
  have he : PoolHost.codeExtra (Geometry.row .w16) ≤ 6 := by
    rw [Geometry.row, Rows.blocks, PoolHost.codeExtra_rows]
    exact PoolHost.rowC_codeExtra_le
  exact cost_arith _ _ _ _ _ fast_standard_relation WEXFast.W15F.rowCF_tp wide_standard_relation he

theorem body_credit_bound :
    2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram) +
      Fast16.fcodeTP code ≤ 2342691 := by
  have hi := credit_increment
  have h := WEXFast.W15F.fastCount_upper
  omega

end
end ShorECDLP.Entrant.WideBank8.Row16

namespace ShorECDLP.Entrant.WideBank8.Fast16
open ShorECDLP.Entrant.WideSigned
open Quantum Challenge AndGadget WEXCredit Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] WEX.codeRecords lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps WEX.compile Bridge.translate
  MeasuredClear.measuredClear MeasuredClear.measuredClear8 ECDSAAdd.Baselines.normalizeProgram

namespace FastSite
variable {n : Nat} (f : FastSite n)

end FastSite

namespace FastSite1
variable {n : Nat} (f : FastSite1 n)

end FastSite1

-- Conditional arithmetic only. The actual final bounds/certificate are required.
end
end ShorECDLP.Entrant.WideBank8.Fast16

namespace ShorECDLP.Entrant.WideBank8.Fast16
open ShorECDLP.Entrant.WideSigned
open Quantum Challenge AndGadget WEXCredit Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
attribute [local irreducible] WEX.codeRecords lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps WEX.compile Bridge.translate
  MeasuredClear.measuredClear MeasuredClear.measuredClear8 ECDSAAdd.Baselines.normalizeProgram

end
end ShorECDLP.Entrant.WideBank8.Fast16

namespace ShorECDLP.Entrant.WideBank8.Row16
open ShorECDLP.Entrant.WideSigned
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] code Fast16.fprog Straight.instantiate AdaptiveCircuit.run

theorem literal_back (c : WCode 32768) (p : ECDSAAdd.Program)
    (hp : WInstr.literal p ∈ Rows.code rows c) : WInstr.literal p ∈ c := by
  obtain ⟨i, hi, he⟩ := List.mem_map.mp hp
  cases i with
  | literal p' => cases he; exact hi
  | lookup ctl ps => cases he

theorem lookup_back (c : WCode 32768) (ctl : Option Wire) (ps : List (LookupPort 65536))
    (hp : WInstr.lookup ctl ps ∈ Rows.code rows c) :
    ∃ old, WInstr.lookup ctl old ∈ c ∧ ps = Rows.ports rows old := by
  obtain ⟨i, hi, he⟩ := List.mem_map.mp hp
  cases i with
  | literal p => cases he
  | lookup ctl' old => cases he; exact ⟨old, hi, rfl⟩

theorem strict₀ (b : Fast16.FBlock2 65536) (hb : b ∈ code₀) :
    ∀ p, WInstr.literal p ∈ erase2 b.forgetL →
      (hostWire ∈ ECDSAAdd.wires p ∨ hostWire2 ∈ ECDSAAdd.wires p ∨ hostWire3 ∈ ECDSAAdd.wires p ∨
       PoolHost.hostWire4 ∈ ECDSAAdd.wires p ∨ PoolHost.hostWire5 ∈ ECDSAAdd.wires p ∨
       PoolHost.hostWire6 ∈ ECDSAAdd.wires p ∨ PoolHost.hostWire7 ∈ ECDSAAdd.wires p) →
      ∃ c, b = .std (.plain c) := by
  rw [code₀] at hb
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hb
  intro p hp hh
  rw [forget_lift, Fast16.erase2_single, Rows.block_code] at hp
  have hback := literal_back _ p hp
  rcases hh with h3 | h3 | h3 | h4 | h5 | h6 | h7
  · obtain ⟨c, he⟩ := WEXFast.W15F.rowCF_strict old ho p hback (Or.inl h3)
    rw [he]; exact ⟨Rows.code rows c, rfl⟩
  · obtain ⟨c, he⟩ := WEXFast.W15F.rowCF_strict old ho p hback (Or.inr (Or.inl h3))
    rw [he]; exact ⟨Rows.code rows c, rfl⟩
  · obtain ⟨c, he⟩ := WEXFast.W15F.rowCF_strict old ho p hback (Or.inr (Or.inr h3))
    rw [he]; exact ⟨Rows.code rows c, rfl⟩
  all_goals
    have hmem : old.forget ∈ WEXUnlookup.rowC := by
      rw [← WEXFast.fforget_rowCF]; exact List.mem_map.mpr ⟨old, ho, rfl⟩
    cases old with
    | std ob =>
      cases ob with
      | plain c => exact ⟨Rows.code rows c, rfl⟩
      | unit u =>
        have hno := (PoolHost.rowC_unit_no4 u hmem).1 p hback
        first
        | exact absurd rfl (hno _ h4).1
        | exact absurd rfl (hno _ h5).2.1
        | exact absurd rfl (hno _ h6).2.2.1
        | exact absurd rfl (hno _ h7).2.2.2
    | fast f =>
      have hno := (PoolHost.rowC_unit_no4 _ hmem).1 p hback
      first
      | exact absurd rfl (hno _ h4).1
      | exact absurd rfl (hno _ h5).2.1
      | exact absurd rfl (hno _ h6).2.2.1
      | exact absurd rfl (hno _ h7).2.2.2
    | fast1 f =>
      have hno := (PoolHost.rowC_unit_no4 _ hmem).1 p hback
      first
      | exact absurd rfl (hno _ h4).1
      | exact absurd rfl (hno _ h5).2.1
      | exact absurd rfl (hno _ h6).2.2.1
      | exact absurd rfl (hno _ h7).2.2.2

theorem ctl₀ (b : Fast16.FBlock2 65536) (hb : b ∈ code₀) :
    ∀ c, b = .std (.plain c) → hostWire2 ∈ ECDSAAdd.wires (litProg c) → hostCtl ∉ ECDSAAdd.wires (litProg c) := by
  rw [code₀] at hb
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hb
  intro c he hh
  cases old with
  | std old =>
    cases old with
    | plain oldc =>
      change Fast16.FBlock2.std (.plain (Rows.code rows oldc)) = .std (.plain c) at he
      have hec := Block2.plain.inj (Fast16.FBlock2.std.inj he)
      subst c
      rw [litProg_lift] at hh ⊢
      exact WEXFast.W15F.rowCF_ctl _ ho oldc rfl hh
    | unit u => cases he
  | fast f => cases he
  | fast1 f => cases he

theorem ctl3₀ (b : Fast16.FBlock2 65536) (hb : b ∈ code₀) :
    ∀ c, b = .std (.plain c) → hostWire3 ∈ ECDSAAdd.wires (litProg c) → hostCtl3 ∉ ECDSAAdd.wires (litProg c) := by
  rw [code₀] at hb
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hb
  intro c he hh
  cases old with
  | std old =>
    cases old with
    | plain oldc =>
      change Fast16.FBlock2.std (.plain (Rows.code rows oldc)) = .std (.plain c) at he
      have hec := Block2.plain.inj (Fast16.FBlock2.std.inj he)
      subst c
      rw [litProg_lift] at hh ⊢
      exact WEXFast.W15F.rowCF_ctl3 _ ho oldc rfl hh
    | unit u => cases he
  | fast f => cases he
  | fast1 f => cases he

theorem ctl4₀ (b : Fast16.FBlock2 65536) (hb : b ∈ code₀) :
    ∀ c, b = .std (.plain c) →
      (14877 ∈ ECDSAAdd.wires (litProg c) ∨ 14876 ∈ ECDSAAdd.wires (litProg c) ∨
        14875 ∈ ECDSAAdd.wires (litProg c) ∨ 14874 ∈ ECDSAAdd.wires (litProg c)) →
      14111 ∉ ECDSAAdd.wires (litProg c) ∧ 19816 ∉ ECDSAAdd.wires (litProg c) ∧
      838 ∉ ECDSAAdd.wires (litProg c) ∧ 14112 ∉ ECDSAAdd.wires (litProg c) ∧
      19815 ∉ ECDSAAdd.wires (litProg c) ∧ 19814 ∉ ECDSAAdd.wires (litProg c) := by
  rw [code₀] at hb
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hb
  intro c he hh
  cases old with
  | std old =>
    cases old with
    | plain oldc =>
      change Fast16.FBlock2.std (.plain (Rows.code rows oldc)) = .std (.plain c) at he
      have hec := Block2.plain.inj (Fast16.FBlock2.std.inj he)
      subst c
      rw [litProg_lift] at hh ⊢
      have hmem : Block2.plain oldc ∈ WEXUnlookup.rowC := by
        rw [← WEXFast.fforget_rowCF]; exact List.mem_map.mpr ⟨.std (.plain oldc), ho, rfl⟩
      exact PoolHost.rowC_plain_ctl4 oldc hmem hh
    | unit u => cases he
  | fast f => cases he
  | fast1 f => cases he

theorem strict (b : Fast16.FBlock2 65536) (hb : b ∈ code) :
    ∀ p, WInstr.literal p ∈ erase2 b.forgetL →
      (hostWire ∈ ECDSAAdd.wires p ∨ hostWire2 ∈ ECDSAAdd.wires p ∨ hostWire3 ∈ ECDSAAdd.wires p ∨
       PoolHost.hostWire4 ∈ ECDSAAdd.wires p ∨ PoolHost.hostWire5 ∈ ECDSAAdd.wires p ∨
       PoolHost.hostWire6 ∈ ECDSAAdd.wires p ∨ PoolHost.hostWire7 ∈ ECDSAAdd.wires p) →
      ∃ c, b = .std (.plain c) := by
  intro p hp hh
  by_cases hq : ∀ q, b ≠ .pair q
  · exact strict₀ b (mem_code₀ b hb hq) p hp hh
  · push_neg at hq
    obtain ⟨q, rfl⟩ := hq
    rw [code, List.mem_append, List.mem_cons] at hb
    have hq : q = corner := by
      rcases hb with hb | hb | hb
      · obtain ⟨old, -, he⟩ := List.mem_map.mp hb
        cases old <;> cases he
      · cases hb; rfl
      · obtain ⟨old, -, he⟩ := List.mem_map.mp hb
        cases old <;> cases he
    subst hq
    exfalso
    rw [show (Fast16.FBlock2.pair corner).forgetL = (Block2.unit corner.u₁ :: Block2.unit corner.u₂ :: []) from rfl,
      erase2_cons, erase2_cons, erase2_nil, List.append_nil, List.mem_append] at hp
    rcases hp with hp | hp
    · obtain ⟨c, hc⟩ := strict₀ _ corner₁_mem p
        (by rw [show (Fast16.FBlock2.std (.unit corner.u₁)).forgetL = (Block2.unit corner.u₁ :: []) from rfl,
          Fast16.erase2_single]; exact hp) hh
      cases hc
    · obtain ⟨c, hc⟩ := strict₀ _ corner₂_mem p
        (by rw [show (Fast16.FBlock2.std (.unit corner.u₂)).forgetL = (Block2.unit corner.u₂ :: []) from rfl,
          Fast16.erase2_single]; exact hp) hh
      cases hc

theorem ctl (b : Fast16.FBlock2 65536) (hb : b ∈ code) :
    ∀ c, b = .std (.plain c) → hostWire2 ∈ ECDSAAdd.wires (litProg c) → hostCtl ∉ ECDSAAdd.wires (litProg c) := by
  intro c he
  exact ctl₀ b (mem_code₀ b hb (by rintro q rfl; cases he)) c he

theorem ctl3 (b : Fast16.FBlock2 65536) (hb : b ∈ code) :
    ∀ c, b = .std (.plain c) → hostWire3 ∈ ECDSAAdd.wires (litProg c) → hostCtl3 ∉ ECDSAAdd.wires (litProg c) := by
  intro c he
  exact ctl3₀ b (mem_code₀ b hb (by rintro q rfl; cases he)) c he

theorem ctl4 (b : Fast16.FBlock2 65536) (hb : b ∈ code) :
    ∀ c, b = .std (.plain c) →
      (14877 ∈ ECDSAAdd.wires (litProg c) ∨ 14876 ∈ ECDSAAdd.wires (litProg c) ∨
        14875 ∈ ECDSAAdd.wires (litProg c) ∨ 14874 ∈ ECDSAAdd.wires (litProg c)) →
      14111 ∉ ECDSAAdd.wires (litProg c) ∧ 19816 ∉ ECDSAAdd.wires (litProg c) ∧
      838 ∉ ECDSAAdd.wires (litProg c) ∧ 14112 ∉ ECDSAAdd.wires (litProg c) ∧
      19815 ∉ ECDSAAdd.wires (litProg c) ∧ 19814 ∉ ECDSAAdd.wires (litProg c) := by
  intro c he
  exact ctl4₀ b (mem_code₀ b hb (by rintro q rfl; cases he)) c he

end
end ShorECDLP.Entrant.WideBank8.Row16

namespace ShorECDLP.Entrant.WideBank8.Counts
open ShorECDLP.Entrant.WideSigned
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] codeRecords lookupMeasurements portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps
  ECDSAAdd.measurementCount ECDSAAdd.Baselines.normalizeProgram literalRecords normalizeW

theorem records_formula {n} (B : PathShare.Bank) (c : Code2 n)
    (hl : ∀ b ∈ c, BlockLay2 B b) :
    recordsP2 B c + masks2 c * (2 ^ B.bits.length - 1) =
      literalRecords (normalizeW (erase2 c)) + traversals (erase2 c) * (2 ^ B.bits.length - 1) +
        lens2 c + masks2 c * ((tableAddressTree B.high 0 1).internalNodes + 255) := by
  induction c with
  | nil => simp [recordsP2, masks2, erase2, normalizeW, literalRecords, traversals, lens2]
  | cons b c ih =>
    have hb : blockRecP2 B b + blockMasks2 b * (2 ^ B.bits.length - 1) =
        literalRecords (normalizeW b.code) + traversals b.code * (2 ^ B.bits.length - 1) +
          blockLen2 b + blockMasks2 b * ((tableAddressTree B.high 0 1).internalNodes + 255) := by
      have hlb := hl b (by simp)
      cases b with
      | plain p =>
        rw [blockRecP2, codeRecords_eq _ _ _ _ hlb, traversals_normalize]
        simp [blockMasks2, blockLen2, Block2.code]
      | unit u =>
        rcases hlb with ⟨hpre, hclear⟩
        rw [blockRecP2, codeRecords_eq _ _ _ _ hpre,
          (MeasuredClear.recordUnary_counts _ _ _ hclear 0).1, traversals_normalize]
        simp only [blockMasks2, blockLen2, Block2.code, UnitSite.code, normalize_append,
          literalRecords_append, traversals_append, Nat.one_mul]
        simp [normalizeW, normalizeWInstr, literalRecords, traversals]
        ring
    have hi := ih (fun d hd => hl d (List.mem_cons_of_mem _ hd))
    simp only [recordsP2, masks2, lens2, erase2_cons, normalize_append,
      literalRecords_append, traversals_append, Nat.add_mul]
    omega

theorem lift_record_metrics {n} (r : Nat → Fin n) (c : Code2 32768) :
    masks2 (Rows.blocks r c) = masks2 c ∧ lens2 (Rows.blocks r c) = lens2 c := by
  induction c with
  | nil => exact ⟨rfl, rfl⟩
  | cons b c ih =>
    cases b <;> simpa [Rows.blocks, Rows.block, Rows.unit, Rows.site, Rows.ports,
      masks2, lens2, blockMasks2, blockLen2] using ih

theorem lift_normal_records {n} (r : Nat → Fin n) (c : WCode 32768) :
    literalRecords (normalizeW (Rows.code r c)) = literalRecords (normalizeW c) := by
  rw [literalRecords_normalize, literalRecords_normalize, (lift_metrics r c).2.1]

theorem lifted_records {n} (r : Nat → Fin n) (B : PathShare.Bank) (c : Code2 32768)
    (hl : ∀ b ∈ Rows.blocks r c, BlockLay2 B b) :
    recordsP2 B (Rows.blocks r c) + masks2 c * (2 ^ B.bits.length - 1) =
      literalRecords (normalizeW (erase2 c)) + traversals (erase2 c) * (2 ^ B.bits.length - 1) +
        lens2 c + masks2 c * ((tableAddressTree B.high 0 1).internalNodes + 255) := by
  have h := records_formula B (Rows.blocks r c) hl
  rw [(lift_record_metrics r c).1, (lift_record_metrics r c).2, Rows.erase_blocks,
    lift_normal_records, (lift_metrics r (erase2 c)).2.2] at h
  exact h

theorem records_change {n} (r : Nat → Fin n) (B : PathShare.Bank) (c : Code2 32768)
    (hl : ∀ b ∈ Rows.blocks r c, BlockLay2 B b)
    (hold : ∀ b ∈ c, BlockLay2 PathShare.bank15 b)
    (hb : B.bits.length = 16) (hn : (tableAddressTree B.high 0 1).internalNodes = 255)
    (hm : masks2 c = 5) (ht : traversals (erase2 c) = 9) :
    recordsP2 B (Rows.blocks r c) = PathShare.recordsP2 PathShare.bank15 c + 131712 := by
  have hw := lifted_records r B c hl
  have ho := WideSigned.Counts.records_formula PathShare.bank15 c hold
  rw [hb, hn, hm, ht] at hw
  rw [hm, ht, show PathShare.bank15.bits.length = 15 from rfl,
    show (tableAddressTree PathShare.bank15.high 0 1).internalNodes = 255 from WEXUnlookup.high_nodes] at ho
  omega

end
end ShorECDLP.Entrant.WideBank8.Counts

namespace ShorECDLP.Entrant.WideBank8.Counts
open ShorECDLP.Entrant.WideSigned
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.Baselines.normalizeProgram Bridge.tmplSlots literalT

theorem slots_append {n} (bits : List Wire) (a b : WCode n) :
    codeSlots bits (a ++ b) = codeSlots bits a + codeSlots bits b := by
  induction a with
  | nil => simp [codeSlots]
  | cons i a ih => cases i <;> simp [codeSlots, ih, Nat.add_assoc]

theorem std_slots {n} (B : PathShare.Bank) (c : Code2 n) :
    codeSP2 B c ≤ codeSlots B.bits (normalizeW (erase2 c)) +
      1024 * lens2 c * (tableAddressTree B.high 0 1).leaves +
      masks2 c * (10 * (tableAddressTree B.high 0 1).internalNodes + 2291) := by
  induction c with
  | nil => simp [codeSP2, codeSlots, lens2, masks2, erase2, normalizeW]
  | cons b c ih =>
    have hb : blockSP2 B b ≤ codeSlots B.bits (normalizeW b.code) +
        1024 * blockLen2 b * (tableAddressTree B.high 0 1).leaves +
        blockMasks2 b * (10 * (tableAddressTree B.high 0 1).internalNodes + 2291) := by
      cases b with
      | plain p => simp [blockSP2, Block2.code, blockLen2, blockMasks2]
      | unit u =>
        simp only [blockSP2, Block2.code, UnitSite.code, normalize_append, slots_append,
          blockLen2, blockMasks2, Nat.one_mul]
        omega
    simp only [codeSP2, lens2, masks2, erase2_cons, normalize_append, slots_append,
      Nat.mul_add, Nat.add_mul] at ih hb ⊢
    omega

theorem lift_slot_metrics {n} (r : Nat → Fin n) (c : WCode 32768) :
    literalSlotSum (Rows.code r c) = literalSlotSum c ∧
      portTotal (Rows.code r c) = portTotal c := by
  induction c with
  | nil => exact ⟨rfl, rfl⟩
  | cons i c ih =>
    cases i <;> simpa [Rows.code, Rows.instr, Rows.ports, literalSlotSum, portTotal] using ih

theorem standard_wide_slots {n} (r : Nat → Fin n) (B : PathShare.Bank) (c : Code2 32768)
    (hb : B.bits.length = 16) (hleaf : (tableAddressTree B.high 0 1).leaves = 256)
    (hnode : (tableAddressTree B.high 0 1).internalNodes = 255)
    (hm : masks2 c = 5) (hlen : lens2 c = 2566) (ht : traversals (erase2 c) = 9)
    (hL : literalSlotSum (erase2 c) ≤ 50115160) (hP : portTotal (erase2 c) ≤ 20003) :
    codeSP2 B (Rows.blocks r c) ≤ 2139852392 := by
  have h := std_slots B (Rows.blocks r c)
  have hc := WEX.codeSlots_bound B.bits (normalizeW (Rows.code r (erase2 c)))
  rw [literalSlotSum_normalize, portTotal_normalize, traversals_normalize,
    (lift_slot_metrics r (erase2 c)).1, (lift_slot_metrics r (erase2 c)).2,
    (lift_metrics r (erase2 c)).2.2, hb, ht] at hc
  rw [(lift_record_metrics r c).1, (lift_record_metrics r c).2, Rows.erase_blocks,
    hm, hlen, hleaf, hnode] at h
  omega

end
end ShorECDLP.Entrant.WideBank8.Counts

namespace ShorECDLP.Entrant.WideBank8.Row16
open ShorECDLP.Entrant.WideSigned
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] code WEXFast.rowCF WEXUnlookup.rowC
  WEX.codeRecords lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps
  ECDSAAdd.measurementCount ECDSAAdd.Baselines.normalizeProgram literalRecords normalizeW
  Fast16.frecs Fast16.frsave recordsP2 masks2 lens2

theorem record_saving₀ : Fast16.frsave code₀ = 80640 := by
  have hstd (c : WEXUnlookup.Code2 32768) :
      Fast16.frsave ((c.map WEXFast.FBlock2.std).map lift) = 0 := by
    induction c with
    | nil => simp [Fast16.frsave]
    | cons b c ih => simpa [Fast16.frsave, Fast16.fblockRSave, lift] using ih
  have happ (a b : Fast16.FCode2 65536) :
      Fast16.frsave (a ++ b) = Fast16.frsave a + Fast16.frsave b := by
    induction a with
    | nil => simp [Fast16.frsave]
    | cons x a ih => simp [Fast16.frsave, ih, Nat.add_assoc]
  have h1 : (fast WEXFast.tripleF).garb.length = 768 := by
    simpa only [fast, Fast16.FastSite.garb, WEXFast.FastSite.garb] using WEXFast.tripleF_garb_length
  have h2 : (fast1 WEXFast.site2F).garb.length = 512 := by
    simpa only [fast1, Fast16.FastSite1.garb, WEXFast.FastSite1.garb] using WEXFast.site2F_garb_length
  rw [code₀, WEXFast.rowCF, List.map_append, List.map_append, happ, happ, hstd, hstd]
  simp only [WEXFast.fgeneric3, List.map_cons, List.map_nil, lift, Fast16.frsave,
    Fast16.fblockRSave, h1, h2]

theorem record_saving : Fast16.frsave code = 81150 := by
  rw [code, Fast16.frsave_pair, ← code₀_split, record_saving₀]
  have hcr := (MeasuredClear.recordUnary_counts _ _ _
    (geo_lay2 Fast16.bank15 Fast16.bank15_ok (.unit corner.u₁) corner_geo.1).2 0).1
  rw [Fast16.bank_tree_nodes] at hcr
  simp only [Fast16.UnitPair.pairRSave]
  omega

theorem record_arith (fresh standard old : Nat)
    (hfast : fresh + 81150 = standard)
    (hnew : standard = old + 131712) (hold : old = 1692440) :
    fresh = 1743002 := by omega

theorem row_records : Fast16.frecs code = 1743002 := by
  have hf := Fast16.frecs_relation code geometry
  rw [record_saving, forget] at hf
  have hn := Counts.records_change rows Fast16.bank15 WEXUnlookup.rowC
    (fun b hb => geo_lay2 Fast16.bank15 Fast16.bank15_ok b (Fast16.row16_geo b hb))
    W15C.lay15 rfl Fast16.high_nodes WEXUnlookup.rowC_masks WEXUnlookup.rowC_measures.2.1
  exact record_arith _ _ _ hf hn W15C.rowC_recordsP

end
end ShorECDLP.Entrant.WideBank8.Row16

namespace ShorECDLP.Entrant.WideBank8.Row16
open ShorECDLP.Entrant.WideSigned
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] code WEXFast.rowCF WEXUnlookup.rowC
  codeSlots literalSlotSum portTotal traversals normalizeW ECDSAAdd.Baselines.normalizeProgram
  Fast16.fprog Fast16.fslack codeSP2 masks2 lens2

theorem slack₀ : Fast16.fslack code₀ = 335556282 := by
  have hp : (fast WEXFast.tripleF).site.ports.length = 256 := by
    simpa [fast, Rows.site, Rows.ports, WEXFast.tripleF] using WEXFast.tripleSite_length
  have hp1 : (fast1 WEXFast.site2F).site.ports.length = 512 := by
    have hl := WEXFast.site2F_geometry.len1
    have hg := WEXFast.site2F_garb_length
    change WEXFast.site2F.g1.length = 512 at hg
    simpa [fast1, Rows.site, Rows.ports] using hl.symm.trans hg
  have hs := Fast16.FastSite.swapNet_slots (fast WEXFast.tripleF)
    (fast_geometry _ WEXFast.tripleF_geometry WEXFast.triple_unit_mem tripleF_no48 tripleF_bank8)
  have hs1 := Fast16.FastSite1.swapNet_slots (fast1 WEXFast.site2F)
    (fast1_geometry _ WEXFast.site2F_geometry WEXFast.site2_unit_mem site2F_no48 site2F_bank8)
  rw [hp] at hs
  rw [hp1] at hs1
  have hstd (c : WEXUnlookup.Code2 32768) :
      Fast16.fslack ((c.map WEXFast.FBlock2.std).map lift) = 26 * c.length := by
    induction c with
    | nil => simp [Fast16.fslack]
    | cons b c ih =>
      simp only [List.map_map] at ih
      simp [Fast16.fslack, Fast16.fblockSlack, lift, ih, Nat.mul_add, Nat.add_comm]
  have happ (a b : Fast16.FCode2 65536) :
      Fast16.fslack (a ++ b) = Fast16.fslack a + Fast16.fslack b := by
    induction a with
    | nil => simp [Fast16.fslack]
    | cons x a ih => simp [Fast16.fslack, ih, Nat.add_assoc]
  have h1 : (fast WEXFast.tripleF).garb.length = 768 := by
    simpa only [fast, Fast16.FastSite.garb, WEXFast.FastSite.garb] using WEXFast.tripleF_garb_length
  have h2 : (fast1 WEXFast.site2F).garb.length = 512 := by
    simpa only [fast1, Fast16.FastSite1.garb, WEXFast.FastSite1.garb] using WEXFast.site2F_garb_length
  have l1 : (WEXUnlookup.rowPre3.map toBlock2).length = 3 := rfl
  have l2 : WEXUnlookup.rowPost3.length = 5 := rfl
  rw [code₀, WEXFast.rowCF, List.map_append, List.map_append, happ, happ, hstd, hstd, l1, l2]
  simp only [WEXFast.fgeneric3, List.map_cons, List.map_nil, lift, Fast16.fslack,
    Fast16.fblockSlack, Fast16.FastSite.fastSlack, Fast16.FastSite1.fastSlack, h1, h2, hs, hs1]

theorem slack : Fast16.fslack code = 335556282 := by
  rw [code, Fast16.fslack_pair, ← code₀_split, slack₀]

theorem standard_slots : codeSP2 Fast16.bank15 (Geometry.row .w16) ≤ 2139852392 := by
  have lit_arith (L L0 : Nat) (h : L ≤ L0 + 93082 + 513) (h0 : L0 ≤ 50021565) :
      L ≤ 50115160 := by omega
  have port_arith (P P0 : Nat) (h : P ≤ P0 + 3) (h0 : P0 ≤ 20000) : P ≤ 20003 := by omega
  exact Counts.standard_wide_slots rows Fast16.bank15 WEXUnlookup.rowC rfl
    Fast16.bank_tree_leaves Fast16.high_nodes WEXUnlookup.rowC_masks WEXUnlookup.rowC_lens
    WEXUnlookup.rowC_measures.2.1
    (lit_arith _ _ WEXUnlookup.rowC_measures.2.2.1 WEX.clearReferenceRow_literal_slots_bound)
    (port_arith _ _ WEXUnlookup.rowC_measures.2.2.2.1 WEX.clearReferenceRow_portTotal)

theorem slots (start : Nat) : (program start).gateSlots ≤ 2475408674 := by
  have h := Fast16.fprog_slots code geometry start
  rw [forget, slack] at h
  have hn := standard_slots
  change (program start).gateSlots ≤ _ at h
  omega

end
end ShorECDLP.Entrant.WideBank8.Row16

namespace ShorECDLP.Entrant.WideBank8.Row16
open ShorECDLP.Entrant.WideSigned
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
attribute [local irreducible] program Fast16.fprog code Fast16.frecs Fast16.fcodeTP
  ECDSAAdd.Baselines.normalizeProgram WEX.codeRecords Nat.add Nat.mul

def fixedProgram (start : Nat) : Straight 65536 start (start + 1743002) :=
  castFinish (congrArg (fun m => start + m) row_records) (program start)

attribute [local irreducible] fixedProgram

theorem fixed_run (read : ConstantBit 65536 → Bool) (start : Nat) (hist : Fin start → Bool) :
    ((fixedProgram start).instantiate read hist).run = ((program start).instantiate read hist).run := by
  rw [fixedProgram, castFinish_instantiate]

theorem fixed_wellFormed (start : Nat) : (fixedProgram start).WellFormed := by
  rw [fixedProgram, castFinish_wellFormed]
  exact wellFormed start

theorem fixed_credit (start : Nat) : ProgramCredit (fixedProgram start) (Fast16.fcodeTP code) := by
  rw [fixedProgram]
  apply credit_cast
  have hz : residue (program start) = 0 := by rw [program]; exact Fast16.fprog_residue _ _
  refine ⟨hz, ?_⟩
  have ht := tCount (fun _ => false) start (fun _ => false)
  have he := exact_t (program start) hz (fun _ => false) (fun _ => false)
  omega

theorem fixed_slots (start : Nat) : (fixedProgram start).gateSlots ≤ 2475408674 := by
  rw [fixedProgram, castFinish_gateSlots]
  exact slots start

end
end ShorECDLP.Entrant.WideBank8.Row16

namespace ShorECDLP.Entrant.WideBank8.Signed16
open ShorECDLP.Entrant.WideSigned
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] Straight.instantiate Straight.WellFormed AdaptiveCircuit.run
  Frame16.program Fast16.fprog Row16.program Row16.code Fast16.frecs Fast16.fcodeTP WEXFast.rowCF WEXUnlookup.rowC
  WEX.codeRecords lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps WEX.compile Bridge.translate
  MeasuredClear.measuredClear MeasuredClear.measuredClear8 ECDSAAdd.Baselines.normalizeProgram Nat.add Nat.mul

local notation "signedCredit16" => (2 * Body.signCredit + Fast16.fcodeTP Row16.code)

def program (start : Nat) : Straight 65536 start (start + 1743514) :=
  castFinish (congrArg (fun m => start + m) (by decide : 512 + 1743002 = 1743514))
    (Frame16.program 1743002 Row16.fixedProgram start)

attribute [local irreducible] program

def rowSource (coeffs : Fin 65536 → PointCoeff) (Q : Point) : AdaptiveCircuit :=
  Fast16.fsrc (readConstant coeffs Q) Row16.code
def source (coeffs : Fin 65536 → PointCoeff) (Q : Point) : AdaptiveCircuit :=
  (Body.prefixSource .w16).seq ((Body.signSource.seq ((rowSource coeffs Q).seq Body.signSource)).seq
    (Body.suffixSource .w16))

theorem row_coherent (coeffs : Fin 65536 → PointCoeff) (Q : Point)
    (hQ : order • Q = 0) (hn : ∀ i, constantPoint Q (coeffs i) ≠ 0) :
    CoherentlyImplementsOn (rowSource coeffs Q)
      (Finsupp.lmapDomain ℂ ℂ (Add.update .w16 coeffs Q)) liveReady := by
  obtain ⟨cs, aligned, mass⟩ := Row16.coherent coeffs Q hQ hn 0 Fin.elim0
  refine ⟨cs, ?_, mass⟩
  simpa only [Row16.program, Fast16.fprog_run, rowSource] using aligned

theorem source_coherent (coeffs : Fin 65536 → PointCoeff) (Q : Point)
    (hQ : order • Q = 0) (hn : ∀ i, constantPoint Q (coeffs i) ≠ 0) :
    CoherentlyImplementsOn (source coeffs Q)
      (Finsupp.lmapDomain ℂ ℂ (Body.state .w16 coeffs Q)) windowReady := by
  have hs : CoherentlyImplementsOn Body.signSource (Finsupp.lmapDomain ℂ ℂ signPointState) liveReady :=
    fastWindowSign_coherent
  have ha := composeCoherent hs (row_coherent coeffs Q hQ hn) (fun s h => liveReady_write _ s h)
  have hb := composeCoherent ha hs (fun s h => liveReady_write _ _ (liveReady_write _ s h))
  have hc := composeCoherent (Body.prefix_coherent .w16) hb
    (fun s h => Body.prepare_live .w16 _ (rootFlip_live s h))
  have hd := composeCoherent hc (Body.suffix_coherent .w16) (fun _ _ => trivial)
  simpa only [source, Body.state, adaptive_seq_assoc] using hd

theorem run (coeffs : Fin 65536 → PointCoeff) (Q : Point) (start : Nat) (history : Fin start → Bool) :
    ((program start).instantiate (readConstant coeffs Q) history).run = (source coeffs Q).run := by
  rw [program, castFinish_instantiate]
  have hr (j : Nat) (hist : Fin j → Bool) :
      ((Row16.fixedProgram j).instantiate (readConstant coeffs Q) hist).run = (rowSource coeffs Q).run := by
    rw [Row16.fixed_run, Row16.program, Fast16.fprog_run]
    rfl
  simpa only [source] using Frame16.run 1743002 Row16.fixedProgram (rowSource coeffs Q)
    (readConstant coeffs Q) hr start history

theorem coherent (coeffs : Fin 65536 → PointCoeff) (Q : Point)
    (hQ : order • Q = 0) (hn : ∀ i, constantPoint Q (coeffs i) ≠ 0)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((program start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (Body.state .w16 coeffs Q)) windowReady := by
  unfold CoherentlyImplementsOn
  rw [run]
  exact source_coherent coeffs Q hQ hn

def window : Single.Window 65536 := ⟨(Body.logicalBank .w16).reverse, 1743514, program⟩
def model (coeffs : Fin 65536 → PointCoeff) (Q : Point) (hQ : order • Q = 0)
    (hn : ∀ i, constantPoint Q (coeffs i) ≠ 0) : Single.Distribution.WindowModel (readConstant coeffs Q) where
  physical := window
  point := fun a => if a < 2 ^ Geometry.Width.w16.bits then
    -constantPoint Q (coeffs (Geometry.rows .w16 (2 ^ Geometry.Width.w16.bits - 1 - a)))
    else constantPoint Q (coeffs (Geometry.rows .w16 (a - 2 ^ Geometry.Width.w16.bits)))
  bias := 0
  ideal := Finsupp.lmapDomain ℂ ℂ (Body.state .w16 coeffs Q)
  valid := windowReady
  nodup := by change (Body.logicalBank .w16).reverse.Nodup; exact List.nodup_reverse.mpr (by decide)
  coherent := coherent coeffs Q hQ hn

theorem program_credit (start : Nat) : ProgramCredit (program start) signedCredit16 := by
  rw [program]
  apply credit_cast
  exact Frame16.credit _ _ Row16.fixedProgram Row16.fixed_credit start

theorem wellFormed (start : Nat) : (program start).WellFormed := by
  rw [program, castFinish_wellFormed]
  exact Frame16.wellFormed _ Row16.fixedProgram Row16.fixed_wellFormed start

theorem sign_credit_bound (s t r : Nat) (hs : s = t) (hb : 2 * t + r ≤ 2342691) :
    2 * s + r ≤ 2342691 := by omega

theorem credit_bound : signedCredit16 ≤ 2342691 :=
  sign_credit_bound Body.signCredit
    (ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram))
    (Fast16.fcodeTP Row16.code) rfl Row16.body_credit_bound

end
end ShorECDLP.Entrant.WideBank8.Signed16

/-! ### Tight support of the re-balanced wide window -/

namespace ShorECDLP.Entrant.WideBank8.Fast16.Tight
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare WideSigned
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
attribute [local irreducible] List.ofFn WEX.codeRecords lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps WEX.compile Bridge.translate
  MeasuredClear.measuredClear MeasuredClear.measuredClear8 ECDSAAdd.Baselines.normalizeProgram
abbrev support : List Wire := TightSupport.support17_7
theorem old_cover : PoolHost.newSourceH7 ⊆ support := List.subset_append_left _ _
private theorem mem_sup (w : Wire) (h : ((fixedPort w ∨ oldWork w) ∧ ¬PoolHost.retiredH7 w) ∨ w = 871) :
    w ∈ support := by
  rcases h with h | rfl
  · exact old_cover ((PoolHost.newSourceH7_mem w).mpr h)
  · exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
private theorem wire_sup (w : Wire) (h : (fixedPort w ∨ oldWork w) ∧ ¬PoolHost.retiredH7 w) :
    w ∈ support := mem_sup w (Or.inl h)
theorem root_new : windowRoot ∈ support :=
  wire_sup _ (by simp only [windowRoot, fixedPort, oldWork, PoolHost.retiredH7, retiredH, retired]; omega)
theorem bits_new : windowBits ⊆ support := by
  intro w hw; simp only [windowBits, List.mem_append, List.mem_range'_1, List.mem_singleton] at hw
  exact mem_sup w (by simp only [fixedPort, oldWork, PoolHost.retiredH7, retiredH, retired]; dsimp only [Wire] at *; omega)
theorem bank_new : pathBank ⊆ support := by
  intro w hw; simp only [pathBank, List.mem_append, List.mem_range'_1, List.mem_singleton] at hw
  exact wire_sup w (by simp only [fixedPort, oldWork, PoolHost.retiredH7, retiredH, retired]; dsimp only [Wire] at *; omega)
theorem high_new : high ⊆ support := by
  intro w hw; simp only [high, List.mem_append, List.mem_range'_1, List.mem_singleton] at hw
  exact mem_sup w (by simp only [fixedPort, oldWork, PoolHost.retiredH7, retiredH, retired]; dsimp only [Wire] at *; omega)
theorem low8_new (i : Fin 8) : low8 i ∈ support := by
  apply bits_new
  have hi := i.isLt
  simp only [windowBits, low8, List.mem_append, List.mem_range'_1, List.mem_singleton]
  omega
theorem selBits_new : selBits ⊆ support := by
  intro w hw; simp only [selBits, List.mem_append, List.mem_range'_1, List.mem_singleton] at hw
  exact mem_sup w (by simp only [fixedPort, oldWork, PoolHost.retiredH7, retiredH, retired]; dsimp only [Wire] at *; omega)
theorem selBits1_new : selBits1 ⊆ support := by
  intro w hw; simp only [selBits1, List.mem_append, List.mem_range'_1, List.mem_singleton] at hw
  exact mem_sup w (by simp only [fixedPort, oldWork, PoolHost.retiredH7, retiredH, retired]; dsimp only [Wire] at *; omega)
theorem selPaths_new : selPaths ⊆ support := by
  intro w hw; simp only [selPaths, List.mem_append, List.mem_range'_1, List.mem_singleton] at hw
  exact wire_sup w (by simp only [fixedPort, oldWork, PoolHost.retiredH7, retiredH, retired]; dsimp only [Wire] at *; omega)
theorem selPaths1_new : selPaths1 ⊆ support := by
  intro w hw; simp only [selPaths1, List.mem_append, List.mem_range'_1, List.mem_singleton] at hw
  exact wire_sup w (by simp only [fixedPort, oldWork, PoolHost.retiredH7, retiredH, retired]; dsimp only [Wire] at *; omega)
theorem work_new (w : Wire) (h : 14115 ≤ w ∧ oldWork w)
    (hw : w ≠ hostWire) (hw2 : w ≠ hostWire2) (hw3 : w ≠ hostWire3)
    (hw4 : w ≠ 14877) (hw5 : w ≠ 14876) (hw6 : w ≠ 14875) (hw7 : w ≠ 14874) : w ∈ support := by
  apply old_cover
  rw [PoolHost.newSourceH7_mem]
  refine ⟨Or.inr h.2, ?_⟩
  unfold PoolHost.retiredH7 retiredH retired
  dsimp only [Wire] at *
  unfold hostWire hostWire2 hostWire3 at *
  omega
theorem guard_new (g : Wire) (h : g = 14113 ∨ g = 10015) : g ∈ support :=
  wire_sup g (by simp only [fixedPort, oldWork, PoolHost.retiredH7, retiredH, retired]; dsimp only [Wire] at *; omega)

theorem kind_no4 {n} (site : MaskedSite n) (hk : SiteKind site) (w : Wire) (hw : w ∈ portTargets site.ports) :
    w ≠ 14877 ∧ w ≠ 14876 ∧ w ≠ 14875 ∧ w ≠ 14874 := by
  have hnot (L : List Wire) (hL : (L.all fun b => decide (b < 14848 ∨ 14878 ≤ b)) = true) (h : w ∈ L) :
      w ≠ 14877 ∧ w ≠ 14876 ∧ w ≠ 14875 ∧ w ≠ 14874 := by
    have h1 := List.all_eq_true.mp hL w h
    simp only [decide_eq_true_eq] at h1
    dsimp only [Wire] at *; omega
  rcases hk with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ <;> rw [ht] at hw
  · simp only [List.mem_range'_1] at hw; dsimp only [Wire] at *; omega
  · rw [WEX.scrWires, pbPairWires_eq, pbShortWires_eq] at hw
    exact hnot _ (by decide +kernel) hw
  · simp only [List.mem_append, List.mem_range'_1] at hw; dsimp only [Wire] at *; omega
  · have h := PoolHost.poolBand_scrAll
    exact ⟨fun e => h 14877 (by decide) (e ▸ hw), fun e => h 14876 (by decide) (e ▸ hw),
      fun e => h 14875 (by decide) (e ▸ hw), fun e => h 14874 (by decide) (e ▸ hw)⟩
  · simp only [List.mem_range'_1] at hw; dsimp only [Wire] at *; omega
  · simp only [List.mem_append, List.mem_cons, List.mem_range'_1] at hw
    dsimp only [Wire] at *; omega

namespace FastSite
open ShorECDLP.Entrant.WideBank8.Fast16.FastSite
variable {n : Nat} (f : FastSite n)

theorem regs_new (hg : FastGeometry f)
    (hgarb : ∀ w ∈ f.garb, w ≠ hostWire ∧ w ≠ hostWire2 ∧ w ≠ hostWire3 ∧
      w ≠ 14877 ∧ w ≠ 14876 ∧ w ≠ 14875 ∧ w ≠ 14874) :
    ∀ w ∈ portTargets f.site.ports ++ f.garb, w ∈ support := by
  intro w hw
  have hk : w ≠ hostWire ∧ w ≠ hostWire2 ∧ w ≠ hostWire3 ∧ w ≠ 14877 ∧ w ≠ 14876 ∧ w ≠ 14875 ∧ w ≠ 14874 := by
    rcases List.mem_append.mp hw with h | h
    · have h4 := kind_no4 f.site hg.site.kind w h
      exact ⟨fun e => kind_nohost f.site hg.site.kind (e ▸ h), fun e => kind_nohost2 f.site hg.site.kind (e ▸ h),
        fun e => PathShare.kind_nohost3 f.site hg.site.kind (e ▸ h), h4.1, h4.2.1, h4.2.2.1, h4.2.2.2⟩
    · exact hgarb w h
  exact work_new w ((facts f hg).2.2.2.2.2.2 w hw) hk.1 hk.2.1 hk.2.2.1 hk.2.2.2.1 hk.2.2.2.2.1 hk.2.2.2.2.2.1 hk.2.2.2.2.2.2

theorem fused_support_new (hg : FastGeometry f)
    (hlit : ∀ p, WInstr.literal p ∈ f.site.code → ECDSAAdd.wires p ⊆ support.toFinset)
    (hlook : ∀ c ps, WInstr.lookup c ps ∈ f.site.code → (∀ q ∈ c, q ∈ support) ∧ portTargets ps ⊆ support)
    (hgarb : ∀ w ∈ f.garb, w ≠ hostWire ∧ w ≠ hostWire2 ∧ w ≠ hostWire3 ∧
      w ≠ 14877 ∧ w ≠ 14876 ∧ w ≠ 14875 ∧ w ≠ 14874)
    (start : Nat) : ChallengeMigration.straightWires (f.fusedProgram start) ⊆ support := by
  have hreg := regs_new f hg hgarb
  have hg0 := guard_new _ (facts f hg).2.2.1
  have hlast := hlook (some f.site.guard) f.site.ports (by simp [MaskedSite.code])
  rw [fusedProgram, support_cast]
  simp only [straightWires_append, List.append_subset]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine compile_support selBits selPaths windowRoot f.selCode support root_new selBits_new selPaths_new
      (fun p hp => by simp [FastSite.selCode] at hp) ?_ start
    intro c ports hm
    simp only [FastSite.selCode, List.mem_singleton, WInstr.lookup.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    refine ⟨fun q hq => ?_, ?_⟩
    · rw [Option.mem_def, Option.some_inj] at hq
      rw [← hq]; exact hg0
    · rw [selPorts_targets f hg]; exact hreg
  · refine literalFixed_support _ _ _ support ?_ _
    intro w hw
    have h := swapNet_wires f hw
    simp only [List.mem_toFinset, List.cons_append, List.mem_cons] at h ⊢
    rcases h with rfl | rfl | h
    · exact bits_new (by simp [windowBits])
    · exact bits_new (by simp [windowBits])
    · exact hreg _ h
  · exact deferTail_support bank15 bank15_ok f.site hg.site.kind _ support hlast.2
      (hlast.1 _ (Option.mem_def.mpr rfl)) low8_new high_new bank_new root_new bits_new
      (by rw [clearData_targets, garbPorts_targets f hg]; exact fun w hw => hreg w (List.mem_append_right _ hw))
      (fun p hm => hlit p (List.mem_append_left _ (List.mem_cons_of_mem _ hm)))
      (fun c ps hm => hlook c ps (List.mem_append_left _ (List.mem_cons_of_mem _ hm))) _
end FastSite

namespace FastSite1
open ShorECDLP.Entrant.WideBank8.Fast16.FastSite1
variable {n : Nat} (f : FastSite1 n)

theorem regs_new (hg : FastGeometry1 f)
    (hgarb : ∀ w ∈ f.garb, w ≠ hostWire ∧ w ≠ hostWire2 ∧ w ≠ hostWire3 ∧
      w ≠ 14877 ∧ w ≠ 14876 ∧ w ≠ 14875 ∧ w ≠ 14874) :
    ∀ w ∈ portTargets f.site.ports ++ f.garb, w ∈ support := by
  intro w hw
  have hk : w ≠ hostWire ∧ w ≠ hostWire2 ∧ w ≠ hostWire3 ∧ w ≠ 14877 ∧ w ≠ 14876 ∧ w ≠ 14875 ∧ w ≠ 14874 := by
    rcases List.mem_append.mp hw with h | h
    · have h4 := kind_no4 f.site hg.site.kind w h
      exact ⟨fun e => kind_nohost f.site hg.site.kind (e ▸ h), fun e => kind_nohost2 f.site hg.site.kind (e ▸ h),
        fun e => PathShare.kind_nohost3 f.site hg.site.kind (e ▸ h), h4.1, h4.2.1, h4.2.2.1, h4.2.2.2⟩
    · exact hgarb w h
  exact work_new w ((facts f hg).2.2.2.2.2.2 w hw) hk.1 hk.2.1 hk.2.2.1 hk.2.2.2.1 hk.2.2.2.2.1 hk.2.2.2.2.2.1 hk.2.2.2.2.2.2

theorem fused_support_new (hg : FastGeometry1 f)
    (hlit : ∀ p, WInstr.literal p ∈ f.site.code → ECDSAAdd.wires p ⊆ support.toFinset)
    (hlook : ∀ c ps, WInstr.lookup c ps ∈ f.site.code → (∀ q ∈ c, q ∈ support) ∧ portTargets ps ⊆ support)
    (hgarb : ∀ w ∈ f.garb, w ≠ hostWire ∧ w ≠ hostWire2 ∧ w ≠ hostWire3 ∧
      w ≠ 14877 ∧ w ≠ 14876 ∧ w ≠ 14875 ∧ w ≠ 14874)
    (start : Nat) : ChallengeMigration.straightWires (f.fusedProgram start) ⊆ support := by
  have hreg := regs_new f hg hgarb
  have hg0 := guard_new _ (facts f hg).2.2.1
  have hlast := hlook (some f.site.guard) f.site.ports (by simp [MaskedSite.code])
  rw [fusedProgram, support_cast]
  simp only [straightWires_append, List.append_subset]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine compile_support selBits1 selPaths1 windowRoot f.selCode support root_new selBits1_new selPaths1_new
      (fun p hp => by simp [FastSite1.selCode] at hp) ?_ start
    intro c ports hm
    simp only [FastSite1.selCode, List.mem_singleton, WInstr.lookup.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    refine ⟨fun q hq => ?_, ?_⟩
    · rw [Option.mem_def, Option.some_inj] at hq
      rw [← hq]; exact hg0
    · rw [selPorts_targets f hg]; exact hreg
  · refine literalFixed_support _ _ _ support ?_ _
    intro w hw
    have h := swapNet_wires f hw
    simp only [List.mem_toFinset, List.cons_append, List.mem_cons] at h ⊢
    rcases h with rfl | h
    · exact bits_new (by simp [windowBits])
    · exact hreg _ h
  · exact deferTail_support bank15 bank15_ok f.site hg.site.kind _ support hlast.2
      (hlast.1 _ (Option.mem_def.mpr rfl)) low8_new high_new bank_new root_new bits_new
      (by rw [clearData_targets, garbPorts_targets f hg]; exact fun w hw => hreg w (List.mem_append_right _ hw))
      (fun p hm => hlit p (List.mem_append_left _ (List.mem_cons_of_mem _ hm)))
      (fun c ps hm => hlook c ps (List.mem_append_left _ (List.mem_cons_of_mem _ hm))) _
end FastSite1

theorem pair_support_new (q : UnitPair 65536) (hg : q.Geo)
    (hlit : ∀ p, WInstr.literal p ∈ q.u₁.code ++ q.u₂.code → ECDSAAdd.wires p ⊆ support.toFinset)
    (hlook : ∀ c ps, WInstr.lookup c ps ∈ q.u₁.code ++ q.u₂.code →
      (∀ x ∈ c, x ∈ support) ∧ portTargets ps ⊆ support)
    (start : Nat) : ChallengeMigration.straightWires (q.pairProgram start) ⊆ support := by
  obtain ⟨g1, g2, -, -⟩ := hg
  have hl1 := hlook (some q.u₁.clear.guard) q.u₁.clear.ports
    (List.mem_append_left _ (by simp [UnitSite.code]))
  have hl2 := hlook (some q.u₂.clear.guard) q.u₂.clear.ports
    (List.mem_append_right _ (by simp [UnitSite.code]))
  rw [UnitPair.pairProgram, support_cast, straightWires_append]
  refine List.append_subset.mpr ⟨?_, ?_⟩
  · exact compile_support _ _ _ _ support root_new bits_new bank_new
      (normalized_lit_support _ support
        (fun p hm => hlit p (List.mem_append_left _ (List.mem_append_left _ hm))))
      (normalized_look_support _ support
        (fun c ps hm => hlook c ps (List.mem_append_left _ (List.mem_append_left _ hm)))) start
  · exact deferTail_support bank15 bank15_ok (unitTail q.u₂) g2.site.kind _ support hl2.2
      (hl2.1 _ (Option.mem_def.mpr rfl)) low8_new high_new bank_new root_new bits_new
      (by rw [UnitPair.gd, clearData_targets]; exact hl1.2)
      (fun p hm => hlit p (List.mem_append_right _ (List.mem_append_left _ (show _ ∈ q.u₂.pre from hm))))
      (fun c ps hm => hlook c ps (List.mem_append_right _ (List.mem_append_left _ (show _ ∈ q.u₂.pre from hm)))) _

def NoHost3 {n} : FBlock2 n → Prop
  | .std _ => True
  | .fast f => ∀ w ∈ f.garb, w ≠ hostWire ∧ w ≠ hostWire2 ∧ w ≠ hostWire3 ∧
      w ≠ 14877 ∧ w ≠ 14876 ∧ w ≠ 14875 ∧ w ≠ 14874
  | .fast1 f => ∀ w ∈ f.garb, w ≠ hostWire ∧ w ≠ hostWire2 ∧ w ≠ hostWire3 ∧
      w ≠ 14877 ∧ w ≠ 14876 ∧ w ≠ 14875 ∧ w ≠ 14874
  | .pair _ => True
theorem ctl_newH : hostCtl ∈ support :=
  wire_sup _ (by simp only [hostCtl, fixedPort, oldWork, PoolHost.retiredH7, retiredH, retired]; omega)
theorem ctl3_newH : hostCtl3 ∈ support :=
  wire_sup _ (by simp only [hostCtl3, fixedPort, oldWork, PoolHost.retiredH7, retiredH, retired]; omega)
theorem fblock_support (b : FBlock2 65536) (hg : FBlockGeo b)
    (hlit : ∀ p, WInstr.literal p ∈ erase2 b.forgetL → ∀ w ∈ ECDSAAdd.wires p,
      w = hostWire ∨ w = hostWire2 ∨ w = hostWire3 ∨
      w = PoolHost.hostWire4 ∨ w = PoolHost.hostWire5 ∨ w = PoolHost.hostWire6 ∨ w = PoolHost.hostWire7 ∨ w ∈ support)
    (hstrict : ∀ p, WInstr.literal p ∈ erase2 b.forgetL →
      (hostWire ∈ ECDSAAdd.wires p ∨ hostWire2 ∈ ECDSAAdd.wires p ∨ hostWire3 ∈ ECDSAAdd.wires p ∨
       PoolHost.hostWire4 ∈ ECDSAAdd.wires p ∨ PoolHost.hostWire5 ∈ ECDSAAdd.wires p ∨
       PoolHost.hostWire6 ∈ ECDSAAdd.wires p ∨ PoolHost.hostWire7 ∈ ECDSAAdd.wires p) →
      ∃ c, b = .std (.plain c))
    (hctl : ∀ c, b = .std (.plain c) → hostWire2 ∈ ECDSAAdd.wires (litProg c) → hostCtl ∉ ECDSAAdd.wires (litProg c))
    (hctl3 : ∀ c, b = .std (.plain c) →
      hostWire3 ∈ ECDSAAdd.wires (litProg c) → hostCtl3 ∉ ECDSAAdd.wires (litProg c))
    (hctl4 : ∀ c, b = .std (.plain c) →
      (14877 ∈ ECDSAAdd.wires (litProg c) ∨ 14876 ∈ ECDSAAdd.wires (litProg c) ∨
        14875 ∈ ECDSAAdd.wires (litProg c) ∨ 14874 ∈ ECDSAAdd.wires (litProg c)) →
      14111 ∉ ECDSAAdd.wires (litProg c) ∧ 19816 ∉ ECDSAAdd.wires (litProg c) ∧
      838 ∉ ECDSAAdd.wires (litProg c) ∧ 14112 ∉ ECDSAAdd.wires (litProg c) ∧
      19815 ∉ ECDSAAdd.wires (litProg c) ∧ 19814 ∉ ECDSAAdd.wires (litProg c))
    (hlook : ∀ c ps, WInstr.lookup c ps ∈ erase2 b.forgetL → (∀ q ∈ c, q ∈ support) ∧ portTargets ps ⊆ support)
    (hgarb : NoHost3 b)
    (start : Nat) : ChallengeMigration.straightWires (fblockProg b start) ⊆ support := by
  have strict : (∀ c, b ≠ .std (.plain c)) → ∀ p, WInstr.literal p ∈ erase2 b.forgetL →
      ECDSAAdd.wires p ⊆ support.toFinset := by
    intro hb p hp w hw
    rcases hlit p hp w hw with e | e | e | e | e | e | e | e
    · obtain ⟨c, hc⟩ := hstrict p hp (Or.inl (e ▸ hw)); exact absurd hc (hb c)
    · obtain ⟨c, hc⟩ := hstrict p hp (Or.inr (Or.inl (e ▸ hw))); exact absurd hc (hb c)
    · obtain ⟨c, hc⟩ := hstrict p hp (Or.inr (Or.inr (Or.inl (e ▸ hw)))); exact absurd hc (hb c)
    · obtain ⟨c, hc⟩ := hstrict p hp (Or.inr (Or.inr (Or.inr (Or.inl (e ▸ hw))))); exact absurd hc (hb c)
    · obtain ⟨c, hc⟩ := hstrict p hp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (e ▸ hw)))))); exact absurd hc (hb c)
    · obtain ⟨c, hc⟩ := hstrict p hp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (e ▸ hw))))))); exact absurd hc (hb c)
    · obtain ⟨c, hc⟩ := hstrict p hp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (e ▸ hw))))))); exact absurd hc (hb c)
    · exact List.mem_toFinset.mpr e
  cases b with
  | std b =>
    cases b with
    | plain code =>
      have hg' : LitAvoid bank15.bits code := hg
      have hlit' : ∀ i ∈ code, ∃ p, i = .literal p := fun i hi => by
        obtain ⟨p, rfl, -⟩ := hg' i hi; exact ⟨p, rfl⟩
      show ChallengeMigration.straightWires (blockProgH bank15 (.plain code) start) ⊆ support
      rw [blockProgH, support_cast, PoolHost.hostCode7_eq_host ((allLit_iff code).mpr hlit')]
      apply compile_support bank15.bits bank15.paths windowRoot _ support root_new bits_new bank_new _
        (fun c ps hm => by simp at hm) start
      intro p hp
      rw [List.mem_singleton, WInstr.literal.injEq] at hp
      subst hp
      let P := ECDSAAdd.Baselines.normalizeProgram (litProg code)
      have hwP : ECDSAAdd.wires P = ECDSAAdd.wires (litProg code) := ECDSAAdd.Baselines.normalize_wires _
      have hRP : windowRoot ∉ ECDSAAdd.wires P := by
        intro hw; rw [hwP] at hw
        obtain ⟨q, hq, hqw⟩ := litProg_wires code windowRoot hw
        obtain ⟨q', he, hq'⟩ := hg' _ hq; cases he; exact hq' windowRoot (by simp) hqw
      exact PoolHost.hostBlock7_wires P support root_new ctl_newH ctl3_newH
        (wire_sup 14111 (by simp only [fixedPort, oldWork, PoolHost.retiredH7, retiredH, retired]; omega))
        (wire_sup 19816 (by simp only [fixedPort, oldWork, PoolHost.retiredH7, retiredH, retired]; omega))
        (wire_sup 838 (by decide))
        (wire_sup 14112 (by simp only [fixedPort, oldWork, PoolHost.retiredH7, retiredH, retired]; omega))
        (wire_sup 19815 (by simp only [fixedPort, oldWork, PoolHost.retiredH7, retiredH, retired]; omega))
        (wire_sup 19814 (by simp only [fixedPort, oldWork, PoolHost.retiredH7, retiredH, retired]; omega))
        (wire_sup 14113 (by simp only [fixedPort, oldWork, PoolHost.retiredH7, retiredH, retired]; omega)) hRP
        (fun w hw => by
          rw [hwP] at hw
          obtain ⟨q, hq, hqw⟩ := litProg_wires code w hw
          exact hlit q (by simpa [FBlock2.forgetL, erase2, Block2.code] using hq) w hqw)
        (fun hm => by rw [hwP] at hm ⊢; exact hctl code rfl hm)
        (fun hm => by rw [hwP] at hm ⊢; exact hctl3 code rfl hm)
        (fun hm => by rw [hwP] at hm ⊢; exact hctl4 code rfl hm)
    | unit u =>
      have h := programP2_support bank15 bank15_ok (Block2.unit u :: []) (fun d hd => by
          simp only [List.mem_singleton] at hd; subst hd; exact hg) support root_new bits_new bank_new low8_new high_new
        (fun p hm => strict (fun c e => by cases e) p (by simpa [FBlock2.forgetL] using hm))
        (fun c ps hm => hlook c ps (by simpa [FBlock2.forgetL] using hm)) start
      rw [programP2, support_cast, straightWires_append] at h
      exact fun w hw => h (List.mem_append_left _ hw)
  | fast f =>
    exact ShorECDLP.Entrant.WideBank8.Fast16.Tight.FastSite.fused_support_new f hg.1
      (fun p hm => strict (fun c e => by cases e) p
        (by simpa [FBlock2.forgetL, erase2, Block2.code, siteUnit_code] using hm))
      (fun c ps hm => hlook c ps (by simpa [FBlock2.forgetL, erase2, Block2.code, siteUnit_code] using hm))
      hgarb start
  | fast1 f =>
    exact ShorECDLP.Entrant.WideBank8.Fast16.Tight.FastSite1.fused_support_new f hg.1
      (fun p hm => strict (fun c e => by cases e) p
        (by simpa [FBlock2.forgetL, erase2, Block2.code, siteUnit_code] using hm))
      (fun c ps hm => hlook c ps (by simpa [FBlock2.forgetL, erase2, Block2.code, siteUnit_code] using hm))
      hgarb start
  | pair q =>
    exact pair_support_new q hg
      (fun p hm => strict (fun c e => by cases e) p (by simpa [FBlock2.forgetL, erase2, Block2.code] using hm))
      (fun c ps hm => hlook c ps (by simpa [FBlock2.forgetL, erase2, Block2.code] using hm)) start

theorem fprog_support (code : FCode2 65536) (hg : ∀ b ∈ code, FBlockGeo b)
    (hlit : ∀ p, WInstr.literal p ∈ erase2 (fforget code) → ∀ w ∈ ECDSAAdd.wires p,
      w = hostWire ∨ w = hostWire2 ∨ w = hostWire3 ∨
      w = PoolHost.hostWire4 ∨ w = PoolHost.hostWire5 ∨ w = PoolHost.hostWire6 ∨ w = PoolHost.hostWire7 ∨ w ∈ support)
    (hstrict : ∀ b ∈ code, ∀ p, WInstr.literal p ∈ erase2 b.forgetL →
      (hostWire ∈ ECDSAAdd.wires p ∨ hostWire2 ∈ ECDSAAdd.wires p ∨ hostWire3 ∈ ECDSAAdd.wires p ∨
       PoolHost.hostWire4 ∈ ECDSAAdd.wires p ∨ PoolHost.hostWire5 ∈ ECDSAAdd.wires p ∨
       PoolHost.hostWire6 ∈ ECDSAAdd.wires p ∨ PoolHost.hostWire7 ∈ ECDSAAdd.wires p) →
      ∃ c, b = .std (.plain c))
    (hctl : ∀ b ∈ code, ∀ c, b = .std (.plain c) →
      hostWire2 ∈ ECDSAAdd.wires (litProg c) → hostCtl ∉ ECDSAAdd.wires (litProg c))
    (hctl3 : ∀ b ∈ code, ∀ c, b = .std (.plain c) →
      hostWire3 ∈ ECDSAAdd.wires (litProg c) → hostCtl3 ∉ ECDSAAdd.wires (litProg c))
    (hctl4 : ∀ b ∈ code, ∀ c, b = .std (.plain c) →
      (14877 ∈ ECDSAAdd.wires (litProg c) ∨ 14876 ∈ ECDSAAdd.wires (litProg c) ∨
        14875 ∈ ECDSAAdd.wires (litProg c) ∨ 14874 ∈ ECDSAAdd.wires (litProg c)) →
      14111 ∉ ECDSAAdd.wires (litProg c) ∧ 19816 ∉ ECDSAAdd.wires (litProg c) ∧
      838 ∉ ECDSAAdd.wires (litProg c) ∧ 14112 ∉ ECDSAAdd.wires (litProg c) ∧
      19815 ∉ ECDSAAdd.wires (litProg c) ∧ 19814 ∉ ECDSAAdd.wires (litProg c))
    (hlook : ∀ c ps, WInstr.lookup c ps ∈ erase2 (fforget code) →
      (∀ q ∈ c, q ∈ support) ∧ portTargets ps ⊆ support)
    (hgarb : ∀ b ∈ code, NoHost3 b)
    (start : Nat) : ChallengeMigration.straightWires (fprog code start) ⊆ support := by
  induction code generalizing start with
  | nil => simp [fprog, frecs, ChallengeMigration.straightWires]
  | cons b code ih =>
    rw [fprog, support_cast, straightWires_append]
    exact List.append_subset.mpr ⟨fblock_support b (hg b (by simp))
      (fun p hm => hlit p (by rw [fforget_cons, erase2_append]; exact List.mem_append_left _ hm))
      (hstrict b (by simp)) (hctl b (by simp)) (hctl3 b (by simp)) (hctl4 b (by simp))
      (fun c ps hm => hlook c ps (by rw [fforget_cons, erase2_append]; exact List.mem_append_left _ hm))
      (hgarb b (by simp)) start,
      ih (fun d hd => hg d (by simp [hd]))
        (fun p hm => hlit p (by rw [fforget_cons, erase2_append]; exact List.mem_append_right _ hm))
        (fun d hd => hstrict d (by simp [hd])) (fun d hd => hctl d (by simp [hd])) (fun d hd => hctl3 d (by simp [hd]))
        (fun d hd => hctl4 d (by simp [hd]))
        (fun c ps hm => hlook c ps (by rw [fforget_cons, erase2_append]; exact List.mem_append_right _ hm))
        (fun d hd => hgarb d (by simp [hd])) _⟩

attribute [local irreducible] Row16.code fprog
  Straight.instantiate AdaptiveCircuit.run

theorem row_literals (p : ECDSAAdd.Program)
    (hp : WInstr.literal p ∈ erase2 (fforget Row16.code)) :
    ∀ v ∈ ECDSAAdd.wires p, v = hostWire ∨ v = hostWire2 ∨ v = hostWire3 ∨
      v = PoolHost.hostWire4 ∨ v = PoolHost.hostWire5 ∨ v = PoolHost.hostWire6 ∨ v = PoolHost.hostWire7 ∨ v ∈ support := by
  rw [Row16.forget, WideSigned.Geometry.row, WideSigned.Rows.erase_blocks] at hp
  have hold := Row16.literal_back _ p hp
  intro v hv
  rcases PoolHost.rowC_lit_relaxed7 p hold v hv with h | h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (old_cover h)))))))

theorem row_lookups (ctl : Option Wire) (ps : List (LookupPort 65536))
    (hp : WInstr.lookup ctl ps ∈ erase2 (fforget Row16.code)) :
    (∀ q ∈ ctl, q ∈ support) ∧ portTargets ps ⊆ support := by
  rw [Row16.forget, WideSigned.Geometry.row, WideSigned.Rows.erase_blocks] at hp
  obtain ⟨old, ho, rfl⟩ := Row16.lookup_back _ ctl ps hp
  have h := PoolHost.rowC_look_newH7 ctl old ho
  rw [WideSigned.Rows.targets]
  exact ⟨fun q hq => old_cover (h.1 q hq), fun v hv => old_cover (h.2 hv)⟩

theorem row_nohost (b : FBlock2 65536) (hb : b ∈ Row16.code) : NoHost3 b := by
  by_cases hq : ∀ q, b ≠ .pair q
  swap
  · push_neg at hq
    obtain ⟨q, rfl⟩ := hq
    trivial
  have hb0 := Row16.mem_code₀ b hb hq
  rw [Row16.code₀] at hb0
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hb0
  have h := WEXFast.W15F.rowCF_nohost old ho
  cases old with
  | std b => trivial
  | fast f =>
    have hf := WEXFast.fast_mem_rowCF f ho; subst f
    intro w hw
    have h3 := h w hw
    have h4 : ∀ v ∈ WEXFast.tripleF.garb, v ≠ 14877 ∧ v ≠ 14876 ∧ v ≠ 14875 ∧ v ≠ 14874 := by
      intro v hv
      simp only [WEXFast.FastSite.garb, WEXFast.tripleF, List.mem_append, List.mem_range'_1] at hv
      dsimp only [Wire] at *; omega
    exact ⟨h3.1, h3.2.1, h3.2.2, (h4 w hw).1, (h4 w hw).2.1, (h4 w hw).2.2.1, (h4 w hw).2.2.2⟩
  | fast1 f =>
    have hf := WEXFast.fast1_mem_rowCF f ho; subst f
    intro w hw
    have h3 := h w hw
    have h4 : ∀ v ∈ WEXFast.site2F.garb, v ≠ 14877 ∧ v ≠ 14876 ∧ v ≠ 14875 ∧ v ≠ 14874 := by
      intro v hv
      simp only [WEXFast.FastSite1.garb, WEXFast.site2F, WEXFast.site2G, List.mem_append, List.mem_range'_1] at hv
      dsimp only [Wire] at *; omega
    exact ⟨h3.1, h3.2.1, h3.2.2, (h4 w hw).1, (h4 w hw).2.1, (h4 w hw).2.2.1, (h4 w hw).2.2.2⟩

theorem row_program_support (start : Nat) :
    straightWires (Row16.program start) ⊆ support := by
  exact fprog_support Row16.code Row16.geometry row_literals
    Row16.strict Row16.ctl Row16.ctl3 Row16.ctl4 row_lookups row_nohost start

theorem fixed_program_support (start : Nat) :
    straightWires (Row16.fixedProgram start) ⊆ support := by
  rw [Row16.fixedProgram, straightWires_castFinish]
  exact row_program_support start
theorem signed_support (start : Nat) :
    straightWires (Signed16.program start) ⊆ support := by
  rw [Signed16.program, straightWires_castFinish]
  exact TightSupport.frame_support17_7 _ Row16.fixedProgram fixed_program_support start
theorem packed_support (start : Nat) :
    straightWires (relabelStraight TightSupport.compact17_7 (Signed16.program start)) ⊆ List.range 1613 := by
  rw [straightWires_relabel]
  intro v hv
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
  exact List.mem_range.mpr (TightSupport.compact17_7_bound u (signed_support start hu))

end
end ShorECDLP.Entrant.WideBank8.Fast16.Tight

namespace ShorECDLP.Entrant.WideBank8.Signed16
open ShorECDLP.Entrant.WideSigned
open Quantum Challenge Secp256k1
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare Single Single.Distribution
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false
attribute [local irreducible] program Row16.program fourierOutcomes AdaptiveCircuit.run

theorem pointRule (coeffs : Fin 65536 → PointCoeff) (Q : Point)
    (hQ : order • Q = 0) (hn : ∀ i, constantPoint Q (coeffs i) ≠ 0)
    (root : BasisState) (hactive : root 836 = true) (hz : Clean (Body.logicalBank .w16) root) :
    PointRule root (model coeffs Q hQ hn) := by
  intro prior output P
  simpa only [WindowModel.step, model, window, List.reverse_reverse, List.length_reverse, LinearMap.comp_apply] using
    Body.point_sum .w16 coeffs Q hQ hn root hactive hz prior output P

theorem prepared (coeffs : Fin 65536 → PointCoeff) (Q : Point)
    (hQ : order • Q = 0) (hn : ∀ i, constantPoint Q (coeffs i) ≠ 0)
    (root : BasisState) (hs : windowReady root) (hz : Clean (Body.logicalBank .w16) root)
    (ψ : State) (hψ : SupportedOn (pointFamily root) ψ) :
    SupportedOn (model coeffs Q hQ hn).valid
      (Quantum.run ((model coeffs Q hQ hn).physical.wires.reverse.map Gate.H) ψ) := by
  change SupportedOn (Body.model .w16 coeffs Q hQ hn).valid
    (Quantum.run ((Body.model .w16 coeffs Q hQ hn).physical.wires.reverse.map Gate.H) ψ)
  exact Body.prepared .w16 coeffs Q hQ hn root hs hz ψ hψ

end
end ShorECDLP.Entrant.WideBank8.Signed16

namespace ShorECDLP.Entrant.WideBank8.Signed16
open ShorECDLP.Entrant.WideSigned
open Quantum Challenge Secp256k1 AndGadget WEXCredit
open Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] program Row16.program ECDSAAdd.Baselines.normalizeProgram
  ECDSAAdd.Challenge.gateSlots literalT Bridge.tmplSlots Frame16.program Row16.code Fast16.frecs

theorem slots (start : Nat) : (program start).gateSlots ≤ 2500000000 := by
  have hrow := Row16.fixed_slots (start + 256)
  have hsign (j : Nat) : (Body.nProgram .w16 j).gateSlots ≤ 300000 := by
    rw [Body.nProgram, reindexStraight_gateSlots, nFastProgram_slots]
    have h := literal_slot_bound (n := 32768)
      (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)
    rw [ECDSAAdd.Baselines.normalize_slots] at h
    have hmax := fastWindowSign_slots
    omega
  rw [program, castFinish_gateSlots, Frame16.slots]
  have h1 := hsign start
  have h2 := hsign (start + 256 + 1743002)
  omega

end
end ShorECDLP.Entrant.WideBank8.Signed16

/-! # Deferred garbage fixups on the narrow (width-15) rows

Each narrow fast site measures its garbage register at once (the register is reset for reuse) but
repays that measurement's phase inside the site clear after the arithmetic: the clear's fixup carries
the garbage ports as well as its own. The measurement, the arithmetic and the fused fixup are proved
as one unit (`tail_sim7`); the deferred phase is read from the guard and the address at fixup time,
which the arithmetic leaves unchanged. -/

namespace ShorECDLP.Entrant.MeasuredClear
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

theorem fixupFactor7_append {n : Nat} (d1 d2 : List (ClearPort n)) (o1 o2 : List Bool)
    (h : o1.length = d1.length) (read : ConstantBit n → Bool) (low : Fin 7 → Wire) (hot : Fin 128 → Wire)
    (tree : UnaryActionTree) (root : Wire) (s : BasisState) :
    fixupFactor (d1 ++ d2) (o1 ++ o2) read low hot tree root s =
      fixupFactor d1 o1 read low hot tree root s * fixupFactor d2 o2 read low hot tree root s := by
  have hz : (d1 ++ d2).zip ((o1 ++ o2).map boolRecord) = d1.zip (o1.map boolRecord) ++ d2.zip (o2.map boolRecord) := by
    rw [List.map_append]
    exact List.zip_append (by simp [h])
  simp only [fixupFactor, phaseLookupFactor, logicalPorts, hz, phasePorts, List.flatMap_append,
    recordTargets_append, xorPhase_append]

theorem fixupFactor7_loaded {n : Nat} (data : List (ClearPort n)) (outcomes : List Bool)
    (read : ConstantBit n → Bool) (low : Fin 7 → Wire) (hot : Fin 128 → Wire)
    (tree : UnaryActionTree) (root : Wire) (paths : List Wire)
    (hi : Function.Injective hot) (hdlow : ∀ i j, low i ≠ hot j)
    (hbank : (hotBank hot).Disjoint (root :: tree.indexWires.dedup ++ paths))
    (t u : BasisState) (hhot : HotClean hot t)
    (hw : ∀ p ∈ data, u p.target =
      (t root && decide (read (p.ref (128 * tree.routeLabel t + hotAddress low t)) = p.value))) :
    fixupFactor data outcomes read low hot tree root t =
      registerXPhase (data.map ClearPort.target) outcomes u := by
  let prepared := Classical.run (hotPrepare low hot) t
  have hframe (w : Wire) (hw : w ∈ root :: tree.indexWires.dedup ++ paths) : prepared w = t w :=
    hotPrepare_frame low hot t w (by
      intro i he
      exact List.disjoint_left.mp hbank (List.mem_ofFn.mpr ⟨i, he.symm⟩) hw)
  have hroute : tree.routeLabel prepared = tree.routeLabel t := by
    apply tree.routeLabel_congr prepared t
    intro w hw
    exact hframe w (by simp [hw])
  let selected : Fin 128 := ⟨hotAddress low t, hotAddress_bound low t⟩
  apply phaseFactor_loaded data outcomes read hot tree root u prepared selected
  · intro i
    simpa only [Fin.ext_iff] using hotPrepare_marker low hot hi hdlow t hhot i
  · intro p hp
    rw [hframe root (by simp), hroute]
    exact hw p hp

end
end ShorECDLP.Entrant.MeasuredClear

/-! ### The deferred tail of a narrow fast site -/

namespace ShorECDLP.Entrant.WEXFast.Defer
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
open WEX WEXUnlookup PathShare
open MeasuredClear (ClearPort)
open WideBank8 (GuardKept guardKept_run)
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

def fuseRec {n} (B : Bank) (site : MaskedSite n) : Nat :=
  MeasuredClear.recordMeasurements (MeasuredClear.recordUnaryOps (tableAddressTree B.high 0 1) site.guard B.hp) + 127

def fusedFix {n} (B : Bank) (site : MaskedSite n) (gd : List (ClearPort n)) (start : Nat)
    (refs : List (Fin start)) : Straight n start (start + site.ports.length + fuseRec B site) :=
  castFinish (by simp [clearData]) (MeasuredClear.measureThen (R := fuseRec B site)
    (fun cursor rs => castFinish (by simp only [fuseRec]; omega)
      (MeasuredClear.fixupProgram (gd ++ clearData site.ports) rs low (clearHot site)
        (tableAddressTree B.high 0 1) site.guard (scratch site) B.hp))
    ((clearData site.ports).map ClearPort.target) start refs)

def tailRec {n} (B : Bank) (site : MaskedSite n) : Nat :=
  codeRecords B.bits B.paths windowRoot (normalizeW site.arithmetic) + (site.ports.length + fuseRec B site)

def deferTail {n} (B : Bank) (site : MaskedSite n) (gd : List (ClearPort n)) (start : Nat) :
    Straight n start (start + gd.length + tailRec B site) :=
  castFinish (by simp) (MeasuredClear.measureThen (R := tailRec B site)
    (fun cursor grefs => castFinish (by simp only [tailRec]; omega)
      ((compile B.bits B.paths windowRoot (normalizeW site.arithmetic) cursor).append
        (fusedFix B site gd (cursor + codeRecords B.bits B.paths windowRoot (normalizeW site.arithmetic))
          (grefs.map (Fin.castLE (Nat.le_add_right _ _))))))
    (gd.map ClearPort.target) start List.nil)

def fusedFixSource {n} (B : Bank) (read : ConstantBit n → Bool) (site : MaskedSite n)
    (gd : List (ClearPort n)) (og : List Bool) : AdaptiveCircuit :=
  measureResetThen ((clearData site.ports).map ClearPort.target) (fun os =>
    MeasuredClear.fixupSource (gd ++ clearData site.ports) (og ++ os) read low (clearHot site)
      (tableAddressTree B.high 0 1) site.guard (scratch site) B.hp)

def deferSource {n} (B : Bank) (read : ConstantBit n → Bool) (site : MaskedSite n)
    (gd : List (ClearPort n)) : AdaptiveCircuit :=
  measureResetThen (gd.map ClearPort.target) (fun og =>
    (source read B.bits B.paths windowRoot (normalizeW site.arithmetic)).seq (fusedFixSource B read site gd og))

theorem fusedFix_run {n} (B : Bank) (read : ConstantBit n → Bool) (site : MaskedSite n)
    (gd : List (ClearPort n)) (start : Nat) (refs : List (Fin start)) (history : Fin start → Bool) :
    ((fusedFix B site gd start refs).instantiate read history).run =
      (fusedFixSource B read site gd (refs.map history)).run := by
  rw [fusedFix, castFinish_instantiate,
    MeasuredClear.measureThen_run _ (fun outcomes => MeasuredClear.fixupSource (gd ++ clearData site.ports) outcomes
      read low (clearHot site) (tableAddressTree B.high 0 1) site.guard (scratch site) B.hp) read
      (by intro cursor rs h; rw [castFinish_instantiate, MeasuredClear.fixupProgram_run])]
  rfl

theorem deferTail_run {n} (B : Bank) (read : ConstantBit n → Bool) (site : MaskedSite n)
    (gd : List (ClearPort n)) (start : Nat) (history : Fin start → Bool) :
    ((deferTail B site gd start).instantiate read history).run = (deferSource B read site gd).run := by
  rw [deferTail, castFinish_instantiate,
    MeasuredClear.measureThen_run _ (fun og => (source read B.bits B.paths windowRoot (normalizeW site.arithmetic)).seq
      (fusedFixSource B read site gd og)) read]
  · simp only [List.map_nil, List.nil_append]
    rfl
  · intro cursor grefs h
    rw [castFinish_instantiate,
      MeasuredClear.append_run_prefix _ _ read (Nat.le_refl cursor) h h rfl
        (fusedFixSource B read site gd (grefs.map h)),
      AdaptiveCircuit.run_seq, compile_run, ← AdaptiveCircuit.run_seq]
    intro h' hh'
    rw [fusedFix_run, List.map_map]
    congr 2
    rw [← hh']
    rfl

theorem site_clear_facts {n} (B : Bank) (hB : BankOK B) (site : MaskedSite n) (hg : SiteGeoP B site) :
    (tableAddressTree B.high 0 1).Layout site.guard B.hp ∧
    Function.Injective (clearHot site) ∧
    (∀ i j, low i ≠ clearHot site j) ∧
    (MeasuredClear.hotBank (clearHot site)).Disjoint
      (site.guard :: (tableAddressTree B.high 0 1).indexWires.dedup ++ B.hp) ∧
    scratch site ∉ site.guard :: (tableAddressTree B.high 0 1).indexWires.dedup ++ B.hp ∧
    scratch site ∉ MeasuredClear.hotBank (clearHot site) ∧
    (∀ w ∈ site.guard :: List.ofFn low ++ (tableAddressTree B.high 0 1).indexWires.dedup ++ B.hp,
      w ∉ portTargets site.ports) ∧
    (∀ w ∈ B.bits, w ∉ portTargets site.ports) ∧
    (∀ i, clearHot site i ∈ portTargets site.ports) := by
  have hlast := hg.placed (.lookup (some site.guard) site.ports) (by simp [MaskedSite.code])
  dsimp only [Placed] at hlast
  obtain ⟨hn,hbd,hhot,hmem,hsm,hgd,-⟩ := kind_facts site hg.kind
  have hP : ∀ w ∈ B.hp, 871 ≤ w ∧ w ∉ portTargets site.ports := by
    intro w hw
    refine ⟨hB.out w hw, fun ht => ?_⟩
    exact List.disjoint_left.mp hlast.2.2
      (show w ∈ windowRoot :: lookupRoot windowRoot (some site.guard) :: B.bits ++ B.paths by
        simp [hB.sub w hw]) ht
  have notT : ∀ w ∈ site.guard :: List.ofFn low ++ B.high ++ B.hp, w ∉ portTargets site.ports := by
    intro w hw ht
    have h2 := (hbd w ht).1
    simp only [List.mem_append,List.mem_cons] at hw
    rcases hw with ((h | h) | h) | h
    · rw [h] at h2; rcases hgd with e | e <;> rw [e] at h2 <;> dsimp only [Wire] at * <;> omega
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
      have := low_lt i
      dsimp only [Wire] at *; omega
    · have := hB.high w h
      dsimp only [Wire] at *; omega
    · exact (hP w h).2 ht
  have hgH : site.guard ∉ B.high := by
    intro h; have := hB.high _ h; rcases hgd with e | e <;> rw [e] at this <;> dsimp only [Wire] at * <;> omega
  have hPg : site.guard ∉ B.hp := by
    intro hg'
    have hn := hlast.1
    simp only [lookupRoot, Option.getD_some, List.cons_append, List.nodup_cons] at hn
    exact hn.1 (List.mem_append_right _ (hB.sub _ hg'))
  have hnodup : (site.guard :: B.high ++ B.hp).Nodup := by
    rw [List.cons_append, List.nodup_cons]
    refine ⟨fun h => ?_, hB.nodup⟩
    rcases List.mem_append.mp h with h | h
    · exact hgH h
    · exact hPg h
  refine ⟨tableAddressTree_layout B.high B.hp site.guard 0 1 hB.len hnodup, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hmem⟩
  · intro i j he; apply Fin.ext; rw [hhot i,hhot j] at he; dsimp only [Wire] at he; omega
  · intro i j he
    have h1 := (hbd _ (hmem j)).1
    have h2 := low_lt i
    rw [← he] at h1
    dsimp only [Wire] at *
    omega
  · apply List.disjoint_left.mpr
    intro w hw hm
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    rw [hB.index] at hm
    exact notT _ (by simp only [List.mem_append,List.mem_cons] at hm ⊢; tauto) (hmem i)
  · rw [hB.index]
    intro hm
    exact notT _ (by simp only [List.mem_append,List.mem_cons] at hm ⊢; tauto) hsm
  · intro hm
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hm
    rw [hhot i] at hi
    dsimp only [Wire] at hi
    omega
  · rw [hB.index]
    intro w hw hm
    exact notT w hw hm
  · intro w hw ht
    exact List.disjoint_left.mp hlast.2.2
      (show w ∈ windowRoot :: lookupRoot windowRoot (some site.guard) :: B.bits ++ B.paths by simp [hw]) ht

def FixSim {n} (B : Bank) (read : ConstantBit n → Bool) (site : MaskedSite n) (gd : List (ClearPort n))
    (og : List Bool) (b : InstrumentBranch) (c : ℂ) : Prop :=
  ∀ (next : ECDSAAdd.State) (u : BasisState), Clean B.hp next.basis →
    (∀ p ∈ site.ports, next.basis p.target =
      (next.basis site.guard && decide (read (p.ref (tableAddressValue B.bits next.basis)) = p.value))) →
    (∀ p ∈ gd, u p.target =
      (next.basis site.guard && decide (read (p.ref (tableAddressValue B.bits next.basis)) = p.value))) →
    b.kraus (Bridge.signedKet next) =
      (c * registerXPhase (gd.map ClearPort.target) og u) •
        Bridge.signedKet ⟨next.phase, clearRegister (portTargets site.ports) next.basis⟩

theorem fusedFix_sim {n} (read : ConstantBit n → Bool) (B : Bank) (hB : BankOK B) (site : MaskedSite n)
    (hg : SiteGeoP B site) (gd : List (ClearPort n)) (og : List Bool) (hog : og.length = gd.length) :
    ∃ cs : List ℂ, List.Forall₂ (FixSim B read site gd og) (fusedFixSource B read site gd og).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  obtain ⟨hl, hi, hdlow, hbank, hs, hshot, ha, hbits, hmem⟩ := site_clear_facts B hB site hg
  obtain ⟨hn,-,-,-,-,-,-⟩ := kind_facts site hg.kind
  unfold fusedFixSource
  apply MeasuredClear.measureResetThen_sim ((clearData site.ports).map ClearPort.target)
    (fun os => MeasuredClear.fixupSource (gd ++ clearData site.ports) (og ++ os) read low (clearHot site)
      (tableAddressTree B.high 0 1) site.guard (scratch site) B.hp)
    (fun os => BranchCoherentOn (MeasuredClear.basisIdeal id
      (MeasuredClear.fixupFactor (gd ++ clearData site.ports) (og ++ os) read low (clearHot site)
        (tableAddressTree B.high 0 1) site.guard))
      (fun s => MeasuredClear.HotClean (clearHot site) s ∧ Clean B.hp s))
  · intro os _
    exact MeasuredClear.fixupSource_coherent (gd ++ clearData site.ports) (og ++ os) read low (clearHot site)
      (tableAddressTree B.high 0 1) site.guard (scratch site) B.hp
      hl hi hdlow hbank hs hshot
  · intro os hos b c hb next u hhp hsite hgarb
    rw [clearData_targets] at hos ⊢
    have hk := xResetRegisterKraus_ket (portTargets site.ports) os next.basis hos hn
    rw [registerXResetCoeff_eq_magnitude_mul_phase _ _ _ hos] at hk
    set t := clearRegister (portTargets site.ports) next.basis with ht
    have hfr : ∀ w, w ∉ portTargets site.ports → t w = next.basis w :=
      fun w hw => MeasuredClear.clearRegister_frame _ _ _ hw
    have hhot : MeasuredClear.HotClean (clearHot site) t := fun i => clearRegister_clean _ _ _ (hmem i)
    have hvalid : MeasuredClear.HotClean (clearHot site) t ∧ Clean B.hp t :=
      ⟨hhot, fun w hw => by rw [hfr w (ha w (by simp [hw]))]; exact hhp w hw⟩
    have hsplit : ∀ s : BasisState, 128 * (tableAddressTree B.high 0 1).routeLabel s +
        MeasuredClear.hotAddress low s = tableAddressValue B.bits s := hB.split
    have haddr : tableAddressValue B.bits t = tableAddressValue B.bits next.basis :=
      WEX.tableAddressValue_congr _ _ _ (fun w hw => hfr w (hbits w hw))
    have hguard : t site.guard = next.basis site.guard := hfr _ (ha _ (by simp))
    have hfac : MeasuredClear.fixupFactor (gd ++ clearData site.ports) (og ++ os) read low (clearHot site)
        (tableAddressTree B.high 0 1) site.guard t =
        registerXPhase (gd.map ClearPort.target) og u * registerXPhase (portTargets site.ports) os next.basis := by
      rw [MeasuredClear.fixupFactor7_append _ _ _ _ hog]
      congr 1
      · apply MeasuredClear.fixupFactor7_loaded gd og read low (clearHot site) _ site.guard B.hp
          hi hdlow hbank t u hhot
        intro p hp
        rw [hsplit, haddr, hguard]
        exact hgarb p hp
      · have h := MeasuredClear.fixupFactor_recycled (clearData site.ports) os read low (clearHot site)
          (tableAddressTree B.high 0 1) site.guard B.hp hi hdlow hbank
          (by rw [clearData_targets]; exact ha) (by rw [clearData_targets]; exact hmem) next.basis
          ⟨hhp, by
            intro q hq
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
            simpa [hsplit] using hsite p hp⟩
        simpa only [clearData_targets] using h
    have hsq := MeasuredClear.registerXPhase_square (portTargets site.ports) os next.basis
    change b.kraus (xResetRegisterKraus (portTargets site.ports) os (Bridge.signedKet next)) = _
    simp only [Bridge.signedKet, map_smul, hk, hb t hvalid, MeasuredClear.basisIdeal_ket, id_eq, hfac,
      smul_smul]
    congr 1
    linear_combination ((if next.phase then (-1 : ℂ) else 1) * registerXResetMagnitude (portTargets site.ports).length *
      c * registerXPhase (gd.map ClearPort.target) og u) * hsq

def InnerSim {n} (B : Bank) (read : ConstantBit n → Bool) (site : MaskedSite n) (gd : List (ClearPort n))
    (og : List Bool) (b : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords site.arithmetic ∧
    ∀ a (st : ECDSAAdd.State) (u : BasisState), SimulationValid B.bits B.paths windowRoot a st →
      (∀ m, Clean (portTargets site.ports)
        (ECDSAAdd.run ((specialize site.code a).instantiate read) m st).basis) →
      (∀ p ∈ gd, u p.target = (st.basis site.guard && decide (read (p.ref a) = p.value))) →
      b.kraus (Bridge.signedKet ⟨st.phase, tableXorState (portMask read site.ports a) (st.basis site.guard) st.basis⟩) =
        (c * registerXPhase (gd.map ClearPort.target) og u) •
          Bridge.signedKet (ECDSAAdd.run ((specialize site.code a).instantiate read) m st)

theorem inner_sim {n} (read : ConstantBit n → Bool) (B : Bank) (hB : BankOK B) (site : MaskedSite n)
    (hg : SiteGeoP B site) (hk : GuardKept site) (gd : List (ClearPort n)) (og : List Bool)
    (hog : og.length = gd.length) :
    ∃ cs : List ℂ, List.Forall₂ (InnerSim B read site gd og)
      ((source read B.bits B.paths windowRoot (normalizeW site.arithmetic)).seq
        (fusedFixSource B read site gd og)).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
  have hpre : ∀ i ∈ site.prefix, PlacedPair B.bits B.paths windowRoot i := fun i hi =>
    placed_implies_pair _ _ _ _ (hg.placed i (List.mem_append_left _ hi))
  have harith : ∀ i ∈ site.arithmetic, PlacedPair B.bits B.paths windowRoot i := fun i hi =>
    hpre i (List.mem_cons_of_mem _ hi)
  obtain ⟨c1, a1, m1⟩ := lnormalized_simulation read B.bits B.paths hB.bitsLen site.arithmetic
    (fun i hi => pair_of_placed_lit _ _ i (harith i hi))
  obtain ⟨c2, a2, m2⟩ := fusedFix_sim read B hB site hg gd og hog
  refine ⟨coherentSeqCoefficients c1 c2, ?_, ?_⟩
  · rw [AdaptiveCircuit.run_seq]
    apply simulationAligned_seq a1 a2
    intro b₁ k₁ b₂ k₂ h₁ h₂
    obtain ⟨m, hm, h₁⟩ := h₁
    refine ⟨m, hm, ?_⟩
    intro a st u hs hun hu
    have hload := hg.placed (.lookup (some site.guard) site.ports)
      (by simp [MaskedSite.code, MaskedSite.prefix])
    have hL := lookup_preserves_simulation read (some site.guard) site.ports B.bits B.paths
      windowRoot a hload st hs
    simp only [lookupRoot, Option.getD_some] at hL
    have hroot : site.guard ∉ portTargets site.ports :=
      List.disjoint_left.mp hload.2.2 (by simp [lookupRoot])
    have e : ECDSAAdd.run ((specialize site.prefix a).instantiate read) m st =
        ECDSAAdd.run ((specialize site.arithmetic a).instantiate read) m
          ⟨st.phase, tableXorState (portMask read site.ports a) (st.basis site.guard) st.basis⟩ := by
      simp only [MaskedSite.prefix, specialize, List.flatMap_cons, WInstr.specialize,
        ECDSAAdd.ShorPort.Tmpl.instantiate_append, ECDSAAdd.run_append, (portTemplate_counts read _ _ _).2,
        List.take_zero, List.drop_zero]
      rw [portTemplate_run read (some site.guard) site.ports a windowRoot List.nil st hload.2.1 hroot hs.2.2]
      rfl
    have hn := strict_preserves read B.bits B.paths site.prefix a hpre st hs m
    have hrun := masked_runP read B site hg a st m hs
    set L : ECDSAAdd.State :=
      ⟨st.phase, tableXorState (portMask read site.ports a) (st.basis site.guard) st.basis⟩ with hLdef
    set next := ECDSAAdd.run ((specialize site.prefix a).instantiate read) m st with hnext
    have hclean : Clean (portTargets site.ports)
        (tableXorState (portMask read site.ports a) (next.basis site.guard) next.basis) := by
      have h := hun m
      rw [hrun] at h
      exact h
    have hlast := hg.placed (.lookup (some site.guard) site.ports) (by simp [MaskedSite.code])
    have hguard : next.basis site.guard = st.basis site.guard := by
      rw [e, guardKept_run read B site hk harith a L hL m]
      exact tableXorState_outside _ _ _ _ (fun hm => hroot (tableBitsMask_subset _ _ hm))
    have hsite : ∀ p ∈ site.ports, next.basis p.target = (next.basis site.guard &&
        decide (read (p.ref (tableAddressValue B.bits next.basis)) = p.value)) := by
      rw [hn.2.1]
      exact loaded_of_clean_unload read site.ports a site.guard next.basis hlast.2.1 hclean
    have h2 := h₂ next u (fun w hw => hn.1 w (hB.sub w hw)) hsite (by
      intro p hp
      rw [hn.2.1, hguard]
      exact hu p hp)
    have hfin : (⟨next.phase, clearRegister (portTargets site.ports) next.basis⟩ : ECDSAAdd.State) =
        ECDSAAdd.run ((specialize site.code a).instantiate read) m st := by
      rw [hrun, clear_eq_unload read site.ports a site.guard next.basis hclean]
    have h1 := h₁ a L ⟨hL.2.1, hL.2.2⟩ (strict_pathsClean read B.bits B.paths site.arithmetic a harith L hL)
    rw [← e] at h1
    change b₂.kraus (b₁.kraus (Bridge.signedKet L)) = _
    rw [h1, map_smul, h2, hfin, smul_smul, mul_assoc]
  · rw [simulationCoefficients_mass, m1, m2]
    norm_num

def TailSim {n} (B : Bank) (read : ConstantBit n → Bool) (site : MaskedSite n) (gd : List (ClearPort n))
    (b : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords site.arithmetic ∧
    ∀ a (st u : ECDSAAdd.State), SimulationValid B.bits B.paths windowRoot a st →
      (∀ m, Clean (portTargets site.ports)
        (ECDSAAdd.run ((specialize site.code a).instantiate read) m st).basis) →
      (∀ p ∈ gd, u.basis p.target = (st.basis site.guard && decide (read (p.ref a) = p.value))) →
      u.phase = st.phase →
      clearRegister (gd.map ClearPort.target) u.basis =
        tableXorState (portMask read site.ports a) (st.basis site.guard) st.basis →
      b.kraus (Bridge.signedKet u) =
        c • Bridge.signedKet (ECDSAAdd.run ((specialize site.code a).instantiate read) m st)

/-- Measurement of the deferred register, the arithmetic and the fused fixup, as one unit. -/
theorem tail_sim {n} (read : ConstantBit n → Bool) (B : Bank) (hB : BankOK B) (site : MaskedSite n)
    (hg : SiteGeoP B site) (hk : GuardKept site) (gd : List (ClearPort n))
    (hgn : (gd.map ClearPort.target).Nodup) :
    ∃ cs : List ℂ, List.Forall₂ (TailSim B read site gd) (deferSource B read site gd).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  unfold deferSource
  apply MeasuredClear.measureResetThen_sim (gd.map ClearPort.target)
    (fun og => (source read B.bits B.paths windowRoot (normalizeW site.arithmetic)).seq
      (fusedFixSource B read site gd og)) (fun og => InnerSim B read site gd og)
  · intro og hog
    exact inner_sim read B hB site hg hk gd og (by simpa using hog)
  · intro og hog b c hb
    obtain ⟨m, hm, hb⟩ := hb
    refine ⟨m, hm, ?_⟩
    intro a st u hs hun hu hph hclr
    have hk' := xResetRegisterKraus_ket (gd.map ClearPort.target) og u.basis hog hgn
    rw [registerXResetCoeff_eq_magnitude_mul_phase _ _ _ hog, hclr] at hk'
    have h := hb a st u.basis hs hun hu
    have hsq := MeasuredClear.registerXPhase_square (gd.map ClearPort.target) og u.basis
    change b.kraus (xResetRegisterKraus (gd.map ClearPort.target) og (Bridge.signedKet u)) = _
    have hstep : b.kraus (xResetRegisterKraus (gd.map ClearPort.target) og (Bridge.signedKet u)) =
        (registerXResetMagnitude (gd.map ClearPort.target).length *
          registerXPhase (gd.map ClearPort.target) og u.basis) •
          b.kraus (Bridge.signedKet ⟨st.phase,
            tableXorState (portMask read site.ports a) (st.basis site.guard) st.basis⟩) := by
      simp only [Bridge.signedKet, hph, map_smul, hk', smul_smul]
      congr 1
      ring
    rw [hstep, h, smul_smul]
    congr 1
    linear_combination (registerXResetMagnitude (gd.map ClearPort.target).length * c) * hsq

theorem fusedFix_tCount {n} (read : ConstantBit n → Bool) (B : Bank) (site : MaskedSite n)
    (gd : List (ClearPort n)) (hl : (tableAddressTree B.high 0 1).Layout site.guard B.hp)
    (start : Nat) (refs : List (Fin start)) (history : Fin start → Bool) :
    ((fusedFix B site gd start refs).instantiate read history).tCount =
      7 * (tableAddressTree B.high 0 1).internalNodes + 840 := by
  rw [fusedFix, castFinish_instantiate, MeasuredClear.measureThen_tCount _ read (by
    intro cursor rs h
    rw [castFinish_instantiate, MeasuredClear.fixupProgram_tCount _ rs low (clearHot site) _ site.guard
      (scratch site) B.hp hl])]

theorem deferTail_tCount {n} (read : ConstantBit n → Bool) (B : Bank) (site : MaskedSite n)
    (gd : List (ClearPort n)) (hl : (tableAddressTree B.high 0 1).Layout site.guard B.hp)
    (hal : LookupLayouts B.bits B.paths windowRoot (normalizeW site.arithmetic))
    (start : Nat) (history : Fin start → Bool) :
    ((deferTail B site gd start).instantiate read history).tCount =
      7 * literalToffolis (normalizeW site.arithmetic) +
        7 * traversals (normalizeW site.arithmetic) * (2 ^ B.bits.length - 1) +
        (7 * (tableAddressTree B.high 0 1).internalNodes + 840) := by
  rw [deferTail, castFinish_instantiate, MeasuredClear.measureThen_tCount _ read (by
    intro cursor grefs h
    rw [castFinish_instantiate, append_tCount_fixed _ _ _ _ _ (fun h' => fusedFix_tCount read B site gd hl _ _ h'),
      compile_tCount read _ _ _ _ hal])]

theorem fusedFix_slots {n} (B : Bank) (site : MaskedSite n) (gd : List (ClearPort n))
    (hl : (tableAddressTree B.high 0 1).Layout site.guard B.hp) (start : Nat) (refs : List (Fin start)) :
    (fusedFix B site gd start refs).gateSlots =
      512 * min (gd.length + site.ports.length) (refs.length + site.ports.length) *
        (tableAddressTree B.high 0 1).leaves + 10 * (tableAddressTree B.high 0 1).internalNodes + 1140 := by
  rw [fusedFix, castFinish_gateSlots, MeasuredClear.measureThen_slots _
    (fun k => 512 * min (gd ++ clearData site.ports).length k * (tableAddressTree B.high 0 1).leaves +
      10 * (tableAddressTree B.high 0 1).internalNodes + 1140)
    (by intro cursor rs; rw [castFinish_gateSlots, MeasuredClear.fixupProgram_slots _ rs low (clearHot site) _
      site.guard (scratch site) B.hp hl])]
  simp [clearData]

theorem deferTail_slots {n} (B : Bank) (site : MaskedSite n) (gd : List (ClearPort n))
    (hl : (tableAddressTree B.high 0 1).Layout site.guard B.hp)
    (hal : LookupLayouts B.bits B.paths windowRoot (normalizeW site.arithmetic)) (start : Nat) :
    (deferTail B site gd start).gateSlots = codeSlots B.bits (normalizeW site.arithmetic) +
      (512 * (gd.length + site.ports.length) * (tableAddressTree B.high 0 1).leaves +
        10 * (tableAddressTree B.high 0 1).internalNodes + 1140) := by
  rw [deferTail, castFinish_gateSlots, MeasuredClear.measureThen_slots _
    (fun k => codeSlots B.bits (normalizeW site.arithmetic) +
      (512 * min (gd.length + site.ports.length) (k + site.ports.length) * (tableAddressTree B.high 0 1).leaves +
        10 * (tableAddressTree B.high 0 1).internalNodes + 1140))
    (by intro cursor grefs; rw [castFinish_gateSlots, Straight.gateSlots_append, WEX.compile_slots _ _ _ _ hal,
      fusedFix_slots B site gd hl]; simp)]
  simp

theorem deferTail_wellFormed {n} (B : Bank) (hB : BankOK B) (site : MaskedSite n) (hg : SiteGeoP B site)
    (gd : List (ClearPort n))
    (hlit : ∀ p, WInstr.literal p ∈ site.arithmetic → ECDSAAdd.Arithmetic.GatePhysical p) (start : Nat) :
    (deferTail B site gd start).WellFormed := by
  obtain ⟨hl, hi, hdlow, hbank, hs, hshot, -, -, -⟩ := site_clear_facts B hB site hg
  have harith : ∀ i ∈ site.arithmetic, PlacedPair B.bits B.paths windowRoot i := fun i hi =>
    placed_implies_pair _ _ _ _ (hg.placed i (List.mem_append_left _ (List.mem_cons_of_mem _ hi)))
  rw [deferTail, castFinish_wellFormed]
  apply MeasuredClear.measureThen_wellFormed
  intro cursor grefs
  rw [castFinish_wellFormed]
  apply straight_append_wellFormed
  · exact pair_compile_wellFormed _ _ _ _ hB.bitsLen (pair_placed_normalize _ _ _ _ harith)
      (normalized_literals_valid site.arithmetic hlit) _
  · rw [fusedFix, castFinish_wellFormed]
    apply MeasuredClear.measureThen_wellFormed
    intro c rs
    rw [castFinish_wellFormed]
    exact MeasuredClear.fixupProgram_wellFormed _ rs low (clearHot site) _ site.guard (scratch site) B.hp hl
      hi hdlow hs hshot

open AndGadget WEXCredit in
theorem deferTail_residue {n} (B : Bank) (site : MaskedSite n) (gd : List (ClearPort n)) (start : Nat) :
    residue (deferTail B site gd start) = 0 := by
  rw [deferTail, residue_cast]
  apply MeasuredClear.measureThen_residue
  intro cursor grefs
  rw [residue_cast, residue_append, compile_residue, fusedFix, residue_cast, Nat.zero_add]
  apply MeasuredClear.measureThen_residue
  intro c rs
  rw [residue_cast]
  exact MeasuredClear.fixupProgram_residue _ _ _ _ _ _ _ _

theorem deferTail_support {n} (B : Bank) (hB : BankOK B) (site : MaskedSite n) (hk : SiteKind site)
    (gd : List (ClearPort n)) (S : List Wire)
    (hS : portTargets site.ports ⊆ S) (hgS : site.guard ∈ S) (hlow : ∀ i, low i ∈ S)
    (hhigh : B.high ⊆ S) (hpaths : B.paths ⊆ S) (hroot : windowRoot ∈ S) (hbits : B.bits ⊆ S)
    (hgd : gd.map ClearPort.target ⊆ S)
    (hlit : ∀ p, WInstr.literal p ∈ site.arithmetic → ECDSAAdd.wires p ⊆ S.toFinset)
    (hlook : ∀ c ps, WInstr.lookup c ps ∈ site.arithmetic → (∀ q ∈ c, q ∈ S) ∧ portTargets ps ⊆ S)
    (start : Nat) : ChallengeMigration.straightWires (deferTail B site gd start) ⊆ S := by
  obtain ⟨-,-,-,hmem,hsm,-,-⟩ := kind_facts site hk
  rw [support_agrees, deferTail, MeasuredClear.static_cast]
  apply MeasuredClear.measureThen_within _ S _ _ _ _ hgd
  intro cursor grefs
  rw [MeasuredClear.static_cast, ← support_agrees, straightWires_append]
  refine List.append_subset.mpr ⟨compile_support _ _ _ _ S hroot hbits hpaths
    (normalized_lit_support _ S hlit) (normalized_look_support _ S hlook) _, ?_⟩
  rw [support_agrees, fusedFix, MeasuredClear.static_cast]
  apply MeasuredClear.measureThen_within _ S _ _ _ _ (by rw [clearData_targets]; exact hS)
  intro c rs
  rw [MeasuredClear.static_cast]
  apply MeasuredClear.fixupProgram_within _ _ _ _ _ _ _ _ S hgS (hS hsm) hlow
    (fun i => hS (hmem i)) _ (fun w hw => hpaths (hB.sub w hw))
  intro w hw
  apply hhigh
  rw [← hB.index]
  exact List.mem_dedup.mpr hw

/-! #### Deferring one unit clear into the next unit's clear (narrow bank) -/

theorem uinner_sim {n} (read : ConstantBit n → Bool) (B : Bank) (hB : BankOK B) (u : UnitSite n)
    (hg : UnitGeoP B u) (hroot : u.clear.guard = windowRoot) (gd : List (ClearPort n)) (og : List Bool)
    (hog : og.length = gd.length) :
    ∃ cs : List ℂ, List.Forall₂ (WideBank8.UInnerSim B read u gd og)
      ((source read B.bits B.paths windowRoot (normalizeW u.pre)).seq
        (fusedFixSource B read u.clear gd og)).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
  have hp : ∀ i ∈ u.pre, PlacedPair B.bits B.paths windowRoot i := fun i hi =>
    hg.placed i (List.mem_append_left _ hi)
  obtain ⟨c1, a1, m1⟩ := lnormalized_simulation read B.bits B.paths hB.bitsLen u.pre
    (fun i hi => pair_of_placed_lit _ _ i (hp i hi))
  obtain ⟨c2, a2, m2⟩ := fusedFix_sim read B hB u.clear hg.site gd og hog
  refine ⟨coherentSeqCoefficients c1 c2, ?_, ?_⟩
  · rw [AdaptiveCircuit.run_seq]
    apply simulationAligned_seq a1 a2
    intro b₁ k₁ b₂ k₂ h₁ h₂
    obtain ⟨m, hm, h₁⟩ := h₁
    refine ⟨m, hm, ?_⟩
    intro a st v hs hun hv
    have hn := strict_preserves read B.bits B.paths u.pre a hp st hs m
    have hrun := unit_runP read B u hg a st m hs
    have h1 := h₁ a st ⟨hs.2.1, hs.2.2⟩ (strict_pathsClean read B.bits B.paths u.pre a hp st hs)
    set next := ECDSAAdd.run ((specialize u.pre a).instantiate read) m st with hnext
    have hclean : Clean (portTargets u.clear.ports)
        (tableXorState (portMask read u.clear.ports a) (next.basis u.clear.guard) next.basis) := by
      have h := hun m
      rw [hrun] at h
      exact h
    have hlast := hg.site.placed (.lookup (some u.clear.guard) u.clear.ports) (by simp [MaskedSite.code])
    have hguard : next.basis u.clear.guard = st.basis u.clear.guard := by
      rw [hroot, hn.2.2, hs.2.2]
    have hsite : ∀ p ∈ u.clear.ports, next.basis p.target = (next.basis u.clear.guard &&
        decide (read (p.ref (tableAddressValue B.bits next.basis)) = p.value)) := by
      rw [hn.2.1]
      exact loaded_of_clean_unload read u.clear.ports a u.clear.guard next.basis hlast.2.1 hclean
    have h2 := h₂ next v (fun w hw => hn.1 w (hB.sub w hw)) hsite (by
      intro p hp'
      rw [hn.2.1, hguard]
      exact hv p hp')
    have hfin : (⟨next.phase, clearRegister (portTargets u.clear.ports) next.basis⟩ : ECDSAAdd.State) =
        ECDSAAdd.run ((specialize u.code a).instantiate read) m st := by
      rw [hrun, clear_eq_unload read u.clear.ports a u.clear.guard next.basis hclean]
    change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
    rw [h1, map_smul, h2, hfin, smul_smul, mul_assoc]
  · rw [simulationCoefficients_mass, m1, m2]
    norm_num

theorem utail_sim {n} (read : ConstantBit n → Bool) (B : Bank) (hB : BankOK B) (u : UnitSite n)
    (hg : UnitGeoP B u) (hroot : u.clear.guard = windowRoot) (gd : List (ClearPort n))
    (hgn : (gd.map ClearPort.target).Nodup) :
    ∃ cs : List ℂ, List.Forall₂ (WideBank8.UTailSim B read u gd) (deferSource B read (WideBank8.unitTail u) gd).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  unfold deferSource
  apply MeasuredClear.measureResetThen_sim (gd.map ClearPort.target)
    (fun og => (source read B.bits B.paths windowRoot (normalizeW u.pre)).seq
      (fusedFixSource B read u.clear gd og)) (fun og => WideBank8.UInnerSim B read u gd og)
  · intro og hog
    exact uinner_sim read B hB u hg hroot gd og (by simpa using hog)
  · intro og hog b c hb
    obtain ⟨m, hm, hb⟩ := hb
    refine ⟨m, hm, ?_⟩
    intro a st w hs hun hu hph hclr
    have hk' := xResetRegisterKraus_ket (gd.map ClearPort.target) og w.basis hog hgn
    rw [registerXResetCoeff_eq_magnitude_mul_phase _ _ _ hog, hclr] at hk'
    have h := hb a st w.basis hs hun hu
    have hsq := MeasuredClear.registerXPhase_square (gd.map ClearPort.target) og w.basis
    change b.kraus (xResetRegisterKraus (gd.map ClearPort.target) og (Bridge.signedKet w)) = _
    have hstep : b.kraus (xResetRegisterKraus (gd.map ClearPort.target) og (Bridge.signedKet w)) =
        (registerXResetMagnitude (gd.map ClearPort.target).length *
          registerXPhase (gd.map ClearPort.target) og w.basis) •
          b.kraus (Bridge.signedKet st) := by
      simp only [Bridge.signedKet, hph, map_smul, hk', smul_smul]
      congr 1
      ring
    rw [hstep, h, smul_smul]
    congr 1
    linear_combination (registerXResetMagnitude (gd.map ClearPort.target).length * c) * hsq

theorem unitTail_wellFormed {n} (B : Bank) (hB : BankOK B) (u : UnitSite n) (hg : UnitGeoP B u)
    (gd : List (ClearPort n))
    (hlit : ∀ p, WInstr.literal p ∈ u.pre → ECDSAAdd.Arithmetic.GatePhysical p) (start : Nat) :
    (deferTail B (WideBank8.unitTail u) gd start).WellFormed := by
  obtain ⟨hl, hi, hdlow, hbank, hs, hshot, -, -, -⟩ := site_clear_facts B hB u.clear hg.site
  have harith : ∀ i ∈ u.pre, PlacedPair B.bits B.paths windowRoot i := fun i hi =>
    hg.placed i (List.mem_append_left _ hi)
  rw [deferTail, castFinish_wellFormed]
  apply MeasuredClear.measureThen_wellFormed
  intro cursor grefs
  rw [castFinish_wellFormed]
  apply straight_append_wellFormed
  · exact pair_compile_wellFormed _ _ _ _ hB.bitsLen (pair_placed_normalize _ _ _ _ harith)
      (normalized_literals_valid u.pre hlit) _
  · rw [fusedFix, castFinish_wellFormed]
    apply MeasuredClear.measureThen_wellFormed
    intro c rs
    rw [castFinish_wellFormed]
    exact MeasuredClear.fixupProgram_wellFormed _ rs low (clearHot u.clear) _ u.clear.guard (scratch u.clear) B.hp hl
      hi hdlow hs hshot

end
end ShorECDLP.Entrant.WEXFast.Defer

/-! ### Fused narrow fast sites -/

section
namespace ShorECDLP.Entrant.WEXFast
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup PathShare
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant
open AndGadget WEXCredit
open MeasuredClear (ClearPort)
open WideBank8 (GuardKept)
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

private theorem h7_wire (w : Wire) (h : (fixedPort w ∨ oldWork w) ∧ ¬PoolHost.retiredH7 w) :
    w ∈ PoolHost.newSourceH7 := (PoolHost.newSourceH7_mem w).mpr h
private theorem h7_root : windowRoot ∈ PoolHost.newSourceH7 :=
  h7_wire _ (by simp only [windowRoot, fixedPort, oldWork, PoolHost.retiredH7, retiredH, retired]; omega)
private theorem h7_bits : windowBits ⊆ PoolHost.newSourceH7 := by
  intro w hw; simp only [windowBits, List.mem_range'_1] at hw
  exact h7_wire w (by simp only [fixedPort, oldWork, PoolHost.retiredH7, retiredH, retired]; omega)
private theorem h7_bank : pathBank ⊆ PoolHost.newSourceH7 := by
  intro w hw; simp only [pathBank, List.mem_range'_1] at hw
  exact h7_wire w (by simp only [fixedPort, oldWork, PoolHost.retiredH7, retiredH, retired]; omega)
private theorem h7_selBits : selBits ⊆ PoolHost.newSourceH7 := by
  intro w hw; simp only [selBits, List.mem_range'_1] at hw
  exact h7_wire w (by simp only [fixedPort, oldWork, PoolHost.retiredH7, retiredH, retired]; omega)
private theorem h7_selPaths : selPaths ⊆ PoolHost.newSourceH7 := by
  intro w hw; simp only [selPaths, List.mem_range'_1] at hw
  exact h7_wire w (by simp only [fixedPort, oldWork, PoolHost.retiredH7, retiredH, retired]; omega)
private theorem h7_selBits1 : selBits1 ⊆ PoolHost.newSourceH7 := by
  intro w hw; simp only [selBits1, List.mem_range'_1] at hw
  exact h7_wire w (by simp only [fixedPort, oldWork, PoolHost.retiredH7, retiredH, retired]; omega)
private theorem h7_selPaths1 : selPaths1 ⊆ PoolHost.newSourceH7 := by
  intro w hw; simp only [selPaths1, List.mem_range'_1] at hw
  exact h7_wire w (by simp only [fixedPort, oldWork, PoolHost.retiredH7, retiredH, retired]; omega)
private theorem h7_high : bank15.high ⊆ PoolHost.newSourceH7 := by
  intro w hw; simp only [bank15, WEXUnlookup.high, List.mem_range'_1] at hw
  exact h7_wire w (by simp only [fixedPort, oldWork, PoolHost.retiredH7, retiredH, retired]; omega)

namespace FastSite
variable {n : Nat} (f : FastSite n)

def fusedRecords : Nat :=
  codeRecords selBits selPaths windowRoot f.selCode + 0 + (f.garbPorts.length + Defer.tailRec bank15 f.site)

def fusedProgram (start : Nat) : Straight n start (start + f.fusedRecords) :=
  castFinish (by simp only [fusedRecords, clearData, List.length_map]; omega)
    (((f.selProgram start).append
      (f.swapProgram (start + codeRecords selBits selPaths windowRoot f.selCode))).append
      (Defer.deferTail bank15 f.site (clearData f.garbPorts)
        (start + codeRecords selBits selPaths windowRoot f.selCode + 0)))

def fusedSource (read : ConstantBit n → Bool) : AdaptiveCircuit :=
  ((source read selBits selPaths windowRoot f.selCode).seq (literalSource f.swapNet)).seq
    (Defer.deferSource bank15 read f.site (clearData f.garbPorts))

theorem fusedProgram_run (read : ConstantBit n → Bool) (start : Nat) (history : Fin start → Bool) :
    ((f.fusedProgram start).instantiate read history).run = (f.fusedSource read).run := by
  rw [fusedProgram, castFinish_instantiate, swapProgram, selProgram,
    append_run_fixed _ _ _ _ _ (fun h => Defer.deferTail_run bank15 read f.site _ _ h), AdaptiveCircuit.run_seq,
    append_run_fixed _ _ _ _ _ (fun h => literalFixed_run (n := n) _ _ _ _ read h), AdaptiveCircuit.run_seq,
    compile_run]
  simp only [fusedSource, AdaptiveCircuit.run_seq]

theorem load_garb (read : ConstantBit n → Bool) (hg : FastGeometry f) (a : Nat) (st : ECDSAAdd.State)
    (hs : SimulationValid windowBits pathBank windowRoot a st)
    (hc : Clean (portTargets f.site.ports ++ f.garb) st.basis) :
    let s₂ := ECDSAAdd.run f.swapNet List.nil
      (ECDSAAdd.run ((specialize f.selCode (tableAddressValue selBits st.basis)).instantiate read) List.nil st)
    ∀ q ∈ clearData f.garbPorts, s₂.basis q.target = (st.basis f.site.guard && decide (read (q.ref a) = q.value)) := by
  intro s₂
  obtain ⟨hp, frame, T, G1, G2, G3⟩ := load_state f read hg a st hs hc
  intro q hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
  simp only [garbPorts, List.mem_append] at hp
  rcases hp with (hp | hp) | hp
  · obtain ⟨i, hi, hgi, rfl⟩ := of_mem_regPorts _ _ _ p hp
    exact G1 i hi hgi
  · obtain ⟨i, hi, hgi, rfl⟩ := of_mem_regPorts _ _ _ p hp
    exact G2 i hi hgi
  · obtain ⟨i, hi, hgi, rfl⟩ := of_mem_regPorts _ _ _ p hp
    exact G3 i hi hgi

theorem fused_simulation (read : ConstantBit n → Bool) (hg : FastGeometry f) (hk : GuardKept f.site) :
    ∃ cs : List ℂ, List.Forall₂ (f.FastSim read) (f.fusedSource read).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  obtain ⟨c1, a1, m1⟩ := swap_simulation f read hg
  obtain ⟨c2, a2, m2⟩ := Defer.tail_sim read bank15 bank15_ok f.site hg.site hk (clearData f.garbPorts)
    (by rw [clearData_targets, garbPorts_targets f hg]; exact garb_nodup f hg)
  refine ⟨coherentSeqCoefficients c1 c2, ?_, ?_⟩
  · rw [fusedSource, AdaptiveCircuit.run_seq]
    apply simulationAligned_seq a1 a2
    intro b₁ k₁ b₂ k₂ h₁ h₂
    obtain ⟨m, hm, h₂⟩ := h₂
    refine ⟨m, by simpa [MaskedSite.code, MaskedSite.prefix, literalRecords] using hm, ?_⟩
    intro a st hs hc hun
    have hgarb := load_garb f read hg a st hs hc
    have heq := load_clear_eq f read hg a st hs hc
    have hph := (load_state f read hg a st hs hc).1
    dsimp only at hgarb heq hph
    change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
    rw [h₁ a st hs hc, map_smul, h₂ a st _ hs hun hgarb hph
      (by rw [clearData_targets, garbPorts_targets f hg]; exact heq), smul_smul]
  · rw [simulationCoefficients_mass, m1, m2]
    norm_num

attribute [local irreducible] WEX.codeRecords lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps WEX.compile Bridge.translate
  MeasuredClear.measuredClear ECDSAAdd.Baselines.normalizeProgram

def fusedTP : Nat :=
  8191 + ECDSAAdd.toffoliCount f.swapNet +
    (literalToffolis (normalizeW f.site.arithmetic) + traversals f.site.arithmetic * 32767) + 375

theorem fused_tCount (read : ConstantBit n → Bool) (hg : FastGeometry f) (start : Nat) (history : Fin start → Bool) :
    ((f.fusedProgram start).instantiate read history).tCount = 7 * f.fusedTP := by
  rw [fusedProgram, castFinish_instantiate, swapProgram, selProgram,
    append_tCount_fixed _ _ _ _ _ (fun h => Defer.deferTail_tCount read bank15 f.site _ (site_layout_bank f hg)
      (arith_layouts f hg) _ h),
    append_tCount_fixed _ _ _ _ _ (fun h => literalFixed_tCount (n := n) _ _ _ _ read h),
    compile_tCount read selBits selPaths windowRoot _ (sel_layouts f hg), traversals_normalize, bank_tree_nodes]
  simp only [fusedTP, FastSite.selCode, literalToffolis, traversals, selBits, bank15, windowBits, List.length_range']
  norm_num
  try ring

theorem fused_tp_relation (hg : FastGeometry f) :
    f.fusedTP + (24576 - ECDSAAdd.toffoliCount f.swapNet) = blockTP2 bank15 (.unit (siteUnit f.site)) := by
  have h := f.fast_tp_relation hg
  have hsw := f.swapNet_toff hg
  have hpl := (facts f hg).2.2.2.1
  simp only [fastTP, fusedTP] at h ⊢
  omega

theorem fused_records_relation (hg : FastGeometry f) :
    f.fusedRecords + (24576 - f.garb.length) = blockRecP2 bank15 (.unit (siteUnit f.site)) := by
  have hsel := sel_records f hg
  have hgl := garbPorts_length f hg
  have hlen := garb_length f hg
  have hpl := (facts f hg).2.2.2.1
  have hcr := (MeasuredClear.recordUnary_counts _ _ _ (site_layout_bank f hg) 0).1
  rw [bank_tree_nodes] at hcr
  have hcr' : MeasuredClear.recordMeasurements
      (MeasuredClear.recordUnaryOps (tableAddressTree high 0 1) f.site.guard bankHp) = 255 := hcr
  have hpre := codeRecords_eq _ _ _ _ (prefix_layouts f hg)
  have hari := codeRecords_eq _ _ _ _ (arith_layouts f hg)
  have hlr : literalRecords (normalizeW f.site.prefix) = literalRecords (normalizeW f.site.arithmetic) := by
    rw [prefix_split, normalize_append, literalRecords_append, (lookup_records_bank _ _).1, Nat.zero_add]
  have htr : traversals (normalizeW f.site.prefix) = traversals (normalizeW f.site.arithmetic) + 1 := by
    rw [prefix_split, normalize_append, traversals_append, (lookup_records_bank _ _).2]
    omega
  have hb : 2 ^ windowBits.length - 1 = 32767 := by simp [windowBits]
  simp only [blockRecP2, siteUnit, FastSite.fusedRecords, Defer.tailRec, Defer.fuseRec, hsel, hgl, hcr, hcr', hpre, hari, hlr, htr, hb]
  simp only [show bank15.bits = windowBits from rfl, show bank15.paths = pathBank from rfl, hb] at hpre hari ⊢
  omega

theorem fused_slots (hg : FastGeometry f) (start : Nat) :
    (f.fusedProgram start).gateSlots ≤ blockSP2 bank15 (.unit (siteUnit f.site)) + f.fastSlack := by
  rw [fusedProgram, castFinish_gateSlots]
  simp only [Straight.gateSlots_append]
  rw [Defer.deferTail_slots bank15 f.site _ (site_layout_bank f hg) (arith_layouts f hg), swapProgram,
    literalFixed_slots, selProgram, compile_slots _ _ _ _ (sel_layouts f hg), sel_slots f hg]
  have hsw := literal_slot_bound (n := n) f.swapNet
  have hd : (clearData f.garbPorts).length = f.garb.length := by
    rw [clearData, List.length_map, garbPorts_length f hg]
  have hpre : codeSlots windowBits (normalizeW f.site.prefix) =
      (32768 * f.site.ports.length + 327670) + codeSlots windowBits (normalizeW f.site.arithmetic) := by
    rw [prefix_split, normalize_append, old_slots_append, lookup_slots]
  simp only [blockSP2, siteUnit, fastSlack, show bank15.bits = windowBits from rfl, hpre, hd, bank_tree_leaves,
    bank_tree_nodes]
  omega

theorem fused_wellFormed (hg : FastGeometry f) (hp : ∀ p, WInstr.literal p ∈ f.site.code → GatePhysical p)
    (start : Nat) : (f.fusedProgram start).WellFormed := by
  rw [fusedProgram, castFinish_wellFormed]
  refine straight_append_wellFormed _ _ (straight_append_wellFormed _ _ ?_ ?_) ?_
  · exact pair_compile_wellFormed _ _ _ _ (by decide)
      (fun i hi => by
        simp only [FastSite.selCode, List.mem_singleton] at hi
        subst hi
        exact placed_implies_pair _ _ _ _ (sel_placed f hg))
      (fun p hp => by simp [FastSite.selCode] at hp) start
  · exact literalFixed_wellFormed _ _ _ (f.swapNet_valid hg) _
  · exact Defer.deferTail_wellFormed bank15 bank15_ok f.site hg.site _
      (fun p hm => hp p (List.mem_append_left _ (List.mem_cons_of_mem _ hm))) _

theorem fused_residue (start : Nat) : residue (f.fusedProgram start) = 0 := by
  rw [fusedProgram, residue_cast]
  simp only [residue_append]
  rw [selProgram, compile_residue, swapProgram, literalFixed, residue_naive_cast, literal_residue,
    Defer.deferTail_residue]

theorem fused_support_new (hg : FastGeometry f)
    (hlit : ∀ p, WInstr.literal p ∈ f.site.code → ECDSAAdd.wires p ⊆ PoolHost.newSourceH7.toFinset)
    (hlook : ∀ c ps, WInstr.lookup c ps ∈ f.site.code → (∀ q ∈ c, q ∈ PoolHost.newSourceH7) ∧ portTargets ps ⊆ PoolHost.newSourceH7)
    (hgarb : ∀ w ∈ f.garb, w ≠ hostWire ∧ w ≠ hostWire2 ∧ w ≠ hostWire3 ∧
      w ≠ 14877 ∧ w ≠ 14876 ∧ w ≠ 14875 ∧ w ≠ 14874)
    (start : Nat) : ChallengeMigration.straightWires (f.fusedProgram start) ⊆ PoolHost.newSourceH7 := by
  have hreg : ∀ w ∈ portTargets f.site.ports ++ f.garb, w ∈ PoolHost.newSourceH7 := by
    intro w hw
    have h0 := regs_new f hg (fun v hv => ⟨(hgarb v hv).1, (hgarb v hv).2.1, (hgarb v hv).2.2.1⟩) w hw
    rcases List.mem_append.mp hw with h | h
    · have h4 := WideBank8.Fast16.Tight.kind_no4 f.site hg.site.kind w h
      exact PoolHost.newSourceH7_of_newH w h0 h4.1 h4.2.1 h4.2.2.1 h4.2.2.2
    · exact PoolHost.newSourceH7_of_newH w h0 (hgarb w h).2.2.2.1 (hgarb w h).2.2.2.2.1 (hgarb w h).2.2.2.2.2.1 (hgarb w h).2.2.2.2.2.2
  have hg0 : f.site.guard ∈ PoolHost.newSourceH7 := by
    rcases (facts f hg).2.2.1 with h | h <;> rw [h] <;>
      exact h7_wire _ (by simp only [fixedPort, oldWork, PoolHost.retiredH7, retiredH, retired]; omega)
  have hlast := hlook (some f.site.guard) f.site.ports (by simp [MaskedSite.code])
  have hroot7 : windowRoot ∈ PoolHost.newSourceH7 := h7_root
  have hbits7 : windowBits ⊆ PoolHost.newSourceH7 := h7_bits
  have hbank7 : pathBank ⊆ PoolHost.newSourceH7 := h7_bank
  have hselBits7 : selBits ⊆ PoolHost.newSourceH7 := h7_selBits
  have hselPaths7 : selPaths ⊆ PoolHost.newSourceH7 := h7_selPaths
  have hhigh7 : bank15.high ⊆ PoolHost.newSourceH7 := h7_high
  have hlow7 : ∀ i : Fin 7, WEXUnlookup.low i ∈ PoolHost.newSourceH7 := by
    intro i; have hi := i.isLt
    rw [PoolHost.newSourceH7_mem]
    simp only [WEXUnlookup.low, fixedPort, oldWork, PoolHost.retiredH7, retiredH, retired]
    omega
  rw [fusedProgram, support_cast]
  simp only [straightWires_append, List.append_subset]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine compile_support selBits selPaths windowRoot f.selCode PoolHost.newSourceH7 hroot7 hselBits7 hselPaths7
      (fun p hp => by simp [FastSite.selCode] at hp) ?_ start
    intro c ports hm
    simp only [FastSite.selCode, List.mem_singleton, WInstr.lookup.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    refine ⟨fun q hq => ?_, ?_⟩
    · rw [Option.mem_def, Option.some_inj] at hq
      rw [← hq]; exact hg0
    · rw [selPorts_targets f hg]; exact hreg
  · refine literalFixed_support _ _ _ PoolHost.newSourceH7 ?_ _
    intro w hw
    have h := swapNet_wires f hw
    simp only [List.mem_toFinset, List.cons_append, List.mem_cons] at h ⊢
    rcases h with rfl | rfl | h
    · exact hbits7 (by simp [windowBits])
    · exact hbits7 (by simp [windowBits])
    · exact hreg _ h
  · exact Defer.deferTail_support bank15 bank15_ok f.site hg.site.kind _ PoolHost.newSourceH7 hlast.2
      (hlast.1 _ (Option.mem_def.mpr rfl)) hlow7 hhigh7 hbank7 hroot7 hbits7
      (by rw [clearData_targets, garbPorts_targets f hg]; exact fun w hw => hreg w (List.mem_append_right _ hw))
      (fun p hm => hlit p (List.mem_append_left _ (List.mem_cons_of_mem _ hm)))
      (fun c ps hm => hlook c ps (List.mem_append_left _ (List.mem_cons_of_mem _ hm))) _

end FastSite

namespace FastSite1
variable {n : Nat} (f : FastSite1 n)

def fusedRecords : Nat :=
  codeRecords selBits1 selPaths1 windowRoot f.selCode + 0 + (f.garbPorts.length + Defer.tailRec bank15 f.site)

def fusedProgram (start : Nat) : Straight n start (start + f.fusedRecords) :=
  castFinish (by simp only [fusedRecords, clearData, List.length_map]; omega)
    (((f.selProgram start).append
      (f.swapProgram (start + codeRecords selBits1 selPaths1 windowRoot f.selCode))).append
      (Defer.deferTail bank15 f.site (clearData f.garbPorts)
        (start + codeRecords selBits1 selPaths1 windowRoot f.selCode + 0)))

def fusedSource (read : ConstantBit n → Bool) : AdaptiveCircuit :=
  ((source read selBits1 selPaths1 windowRoot f.selCode).seq (literalSource f.swapNet)).seq
    (Defer.deferSource bank15 read f.site (clearData f.garbPorts))

theorem fusedProgram_run (read : ConstantBit n → Bool) (start : Nat) (history : Fin start → Bool) :
    ((f.fusedProgram start).instantiate read history).run = (f.fusedSource read).run := by
  rw [fusedProgram, castFinish_instantiate, swapProgram, selProgram,
    append_run_fixed _ _ _ _ _ (fun h => Defer.deferTail_run bank15 read f.site _ _ h), AdaptiveCircuit.run_seq,
    append_run_fixed _ _ _ _ _ (fun h => literalFixed_run (n := n) _ _ _ _ read h), AdaptiveCircuit.run_seq,
    compile_run]
  simp only [fusedSource, AdaptiveCircuit.run_seq]

theorem load_garb (read : ConstantBit n → Bool) (hg : FastGeometry1 f) (a : Nat) (st : ECDSAAdd.State)
    (hs : SimulationValid windowBits pathBank windowRoot a st)
    (hc : Clean (portTargets f.site.ports ++ f.garb) st.basis) :
    let s₂ := ECDSAAdd.run f.swapNet List.nil
      (ECDSAAdd.run ((specialize f.selCode (tableAddressValue selBits1 st.basis)).instantiate read) List.nil st)
    ∀ q ∈ clearData f.garbPorts, s₂.basis q.target = (st.basis f.site.guard && decide (read (q.ref a) = q.value)) := by
  intro s₂
  obtain ⟨hp, frame, T, G1⟩ := load_state f read hg a st hs hc
  intro q hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
  obtain ⟨i, hi, hgi, rfl⟩ := of_mem_regPorts _ _ _ p hp
  exact G1 i hi hgi

theorem fused_simulation (read : ConstantBit n → Bool) (hg : FastGeometry1 f) (hk : GuardKept f.site) :
    ∃ cs : List ℂ, List.Forall₂ (f.FastSim read) (f.fusedSource read).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  obtain ⟨c1, a1, m1⟩ := swap_simulation f read hg
  obtain ⟨c2, a2, m2⟩ := Defer.tail_sim read bank15 bank15_ok f.site hg.site hk (clearData f.garbPorts)
    (by rw [clearData_targets, garbPorts_targets f hg]; exact garb_nodup f hg)
  refine ⟨coherentSeqCoefficients c1 c2, ?_, ?_⟩
  · rw [fusedSource, AdaptiveCircuit.run_seq]
    apply simulationAligned_seq a1 a2
    intro b₁ k₁ b₂ k₂ h₁ h₂
    obtain ⟨m, hm, h₂⟩ := h₂
    refine ⟨m, by simpa [MaskedSite.code, MaskedSite.prefix, literalRecords] using hm, ?_⟩
    intro a st hs hc hun
    have hgarb := load_garb f read hg a st hs hc
    have heq := load_clear_eq f read hg a st hs hc
    have hph := (load_state f read hg a st hs hc).1
    dsimp only at hgarb heq hph
    change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
    rw [h₁ a st hs hc, map_smul, h₂ a st _ hs hun hgarb hph
      (by rw [clearData_targets, garbPorts_targets f hg]; exact heq), smul_smul]
  · rw [simulationCoefficients_mass, m1, m2]
    norm_num

attribute [local irreducible] WEX.codeRecords lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps WEX.compile Bridge.translate
  MeasuredClear.measuredClear ECDSAAdd.Baselines.normalizeProgram

def fusedTP : Nat :=
  16383 + ECDSAAdd.toffoliCount f.swapNet +
    (literalToffolis (normalizeW f.site.arithmetic) + traversals f.site.arithmetic * 32767) + 375

theorem fused_tCount (read : ConstantBit n → Bool) (hg : FastGeometry1 f) (start : Nat) (history : Fin start → Bool) :
    ((f.fusedProgram start).instantiate read history).tCount = 7 * f.fusedTP := by
  rw [fusedProgram, castFinish_instantiate, swapProgram, selProgram,
    append_tCount_fixed _ _ _ _ _ (fun h => Defer.deferTail_tCount read bank15 f.site _ (site_layout_bank f hg)
      (arith_layouts f hg) _ h),
    append_tCount_fixed _ _ _ _ _ (fun h => literalFixed_tCount (n := n) _ _ _ _ read h),
    compile_tCount read selBits1 selPaths1 windowRoot _ (sel_layouts f hg), traversals_normalize, bank_tree_nodes]
  simp only [fusedTP, FastSite1.selCode, literalToffolis, traversals, selBits1, bank15, windowBits, List.length_range']
  norm_num
  try ring

theorem fused_tp_relation (hg : FastGeometry1 f) :
    f.fusedTP + (16384 - ECDSAAdd.toffoliCount f.swapNet) = blockTP2 bank15 (.unit (siteUnit f.site)) := by
  have h := f.fast_tp_relation hg
  have hsw := f.swapNet_toff hg
  have hpl := (facts f hg).2.2.2.1
  simp only [fastTP, fusedTP] at h ⊢
  omega

theorem fused_records_relation (hg : FastGeometry1 f) :
    f.fusedRecords + (16384 - f.garb.length) = blockRecP2 bank15 (.unit (siteUnit f.site)) := by
  have hsel := sel_records f hg
  have hgl := garbPorts_length f hg
  have hlen := garb_length f hg
  have hpl := (facts f hg).2.2.2.1
  have hcr := (MeasuredClear.recordUnary_counts _ _ _ (site_layout_bank f hg) 0).1
  rw [bank_tree_nodes] at hcr
  have hcr' : MeasuredClear.recordMeasurements
      (MeasuredClear.recordUnaryOps (tableAddressTree high 0 1) f.site.guard bankHp) = 255 := hcr
  have hpre := codeRecords_eq _ _ _ _ (prefix_layouts f hg)
  have hari := codeRecords_eq _ _ _ _ (arith_layouts f hg)
  have hlr : literalRecords (normalizeW f.site.prefix) = literalRecords (normalizeW f.site.arithmetic) := by
    rw [prefix_split, normalize_append, literalRecords_append, (lookup_records_bank _ _).1, Nat.zero_add]
  have htr : traversals (normalizeW f.site.prefix) = traversals (normalizeW f.site.arithmetic) + 1 := by
    rw [prefix_split, normalize_append, traversals_append, (lookup_records_bank _ _).2]
    omega
  have hb : 2 ^ windowBits.length - 1 = 32767 := by simp [windowBits]
  simp only [blockRecP2, siteUnit, FastSite1.fusedRecords, Defer.tailRec, Defer.fuseRec, hsel, hgl, hcr, hcr', hpre, hari, hlr, htr, hb]
  simp only [show bank15.bits = windowBits from rfl, show bank15.paths = pathBank from rfl, hb] at hpre hari ⊢
  omega

theorem fused_slots (hg : FastGeometry1 f) (start : Nat) :
    (f.fusedProgram start).gateSlots ≤ blockSP2 bank15 (.unit (siteUnit f.site)) + f.fastSlack := by
  rw [fusedProgram, castFinish_gateSlots]
  simp only [Straight.gateSlots_append]
  rw [Defer.deferTail_slots bank15 f.site _ (site_layout_bank f hg) (arith_layouts f hg), swapProgram,
    literalFixed_slots, selProgram, compile_slots _ _ _ _ (sel_layouts f hg), sel_slots f hg]
  have hsw := literal_slot_bound (n := n) f.swapNet
  have hd : (clearData f.garbPorts).length = f.garb.length := by
    rw [clearData, List.length_map, garbPorts_length f hg]
  have hpre : codeSlots windowBits (normalizeW f.site.prefix) =
      (32768 * f.site.ports.length + 327670) + codeSlots windowBits (normalizeW f.site.arithmetic) := by
    rw [prefix_split, normalize_append, old_slots_append, FastSite.lookup_slots]
  simp only [blockSP2, siteUnit, fastSlack, show bank15.bits = windowBits from rfl, hpre, hd, bank_tree_leaves,
    bank_tree_nodes]
  omega

theorem fused_wellFormed (hg : FastGeometry1 f) (hp : ∀ p, WInstr.literal p ∈ f.site.code → GatePhysical p)
    (start : Nat) : (f.fusedProgram start).WellFormed := by
  rw [fusedProgram, castFinish_wellFormed]
  refine straight_append_wellFormed _ _ (straight_append_wellFormed _ _ ?_ ?_) ?_
  · exact pair_compile_wellFormed _ _ _ _ (by decide)
      (fun i hi => by
        simp only [FastSite1.selCode, List.mem_singleton] at hi
        subst hi
        exact placed_implies_pair _ _ _ _ (sel_placed f hg))
      (fun p hp => by simp [FastSite1.selCode] at hp) start
  · exact literalFixed_wellFormed _ _ _ (f.swapNet_valid hg) _
  · exact Defer.deferTail_wellFormed bank15 bank15_ok f.site hg.site _
      (fun p hm => hp p (List.mem_append_left _ (List.mem_cons_of_mem _ hm))) _

theorem fused_residue (start : Nat) : residue (f.fusedProgram start) = 0 := by
  rw [fusedProgram, residue_cast]
  simp only [residue_append]
  rw [selProgram, compile_residue, swapProgram, literalFixed, residue_naive_cast, literal_residue,
    Defer.deferTail_residue]

theorem fused_support_new (hg : FastGeometry1 f)
    (hlit : ∀ p, WInstr.literal p ∈ f.site.code → ECDSAAdd.wires p ⊆ PoolHost.newSourceH7.toFinset)
    (hlook : ∀ c ps, WInstr.lookup c ps ∈ f.site.code → (∀ q ∈ c, q ∈ PoolHost.newSourceH7) ∧ portTargets ps ⊆ PoolHost.newSourceH7)
    (hgarb : ∀ w ∈ f.garb, w ≠ hostWire ∧ w ≠ hostWire2 ∧ w ≠ hostWire3 ∧
      w ≠ 14877 ∧ w ≠ 14876 ∧ w ≠ 14875 ∧ w ≠ 14874)
    (start : Nat) : ChallengeMigration.straightWires (f.fusedProgram start) ⊆ PoolHost.newSourceH7 := by
  have hreg : ∀ w ∈ portTargets f.site.ports ++ f.garb, w ∈ PoolHost.newSourceH7 := by
    intro w hw
    have h0 := regs_new f hg (fun v hv => ⟨(hgarb v hv).1, (hgarb v hv).2.1, (hgarb v hv).2.2.1⟩) w hw
    rcases List.mem_append.mp hw with h | h
    · have h4 := WideBank8.Fast16.Tight.kind_no4 f.site hg.site.kind w h
      exact PoolHost.newSourceH7_of_newH w h0 h4.1 h4.2.1 h4.2.2.1 h4.2.2.2
    · exact PoolHost.newSourceH7_of_newH w h0 (hgarb w h).2.2.2.1 (hgarb w h).2.2.2.2.1 (hgarb w h).2.2.2.2.2.1 (hgarb w h).2.2.2.2.2.2
  have hg0 : f.site.guard ∈ PoolHost.newSourceH7 := by
    rcases (facts f hg).2.2.1 with h | h <;> rw [h] <;>
      exact h7_wire _ (by simp only [fixedPort, oldWork, PoolHost.retiredH7, retiredH, retired]; omega)
  have hlast := hlook (some f.site.guard) f.site.ports (by simp [MaskedSite.code])
  have hroot7 : windowRoot ∈ PoolHost.newSourceH7 := h7_root
  have hbits7 : windowBits ⊆ PoolHost.newSourceH7 := h7_bits
  have hbank7 : pathBank ⊆ PoolHost.newSourceH7 := h7_bank
  have hselBits7 : selBits1 ⊆ PoolHost.newSourceH7 := h7_selBits1
  have hselPaths7 : selPaths1 ⊆ PoolHost.newSourceH7 := h7_selPaths1
  have hhigh7 : bank15.high ⊆ PoolHost.newSourceH7 := h7_high
  have hlow7 : ∀ i : Fin 7, WEXUnlookup.low i ∈ PoolHost.newSourceH7 := by
    intro i; have hi := i.isLt
    rw [PoolHost.newSourceH7_mem]
    simp only [WEXUnlookup.low, fixedPort, oldWork, PoolHost.retiredH7, retiredH, retired]
    omega
  rw [fusedProgram, support_cast]
  simp only [straightWires_append, List.append_subset]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine compile_support selBits1 selPaths1 windowRoot f.selCode PoolHost.newSourceH7 hroot7 hselBits7 hselPaths7
      (fun p hp => by simp [FastSite1.selCode] at hp) ?_ start
    intro c ports hm
    simp only [FastSite1.selCode, List.mem_singleton, WInstr.lookup.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    refine ⟨fun q hq => ?_, ?_⟩
    · rw [Option.mem_def, Option.some_inj] at hq
      rw [← hq]; exact hg0
    · rw [selPorts_targets f hg]; exact hreg
  · refine literalFixed_support _ _ _ PoolHost.newSourceH7 ?_ _
    intro w hw
    have h := swapNet_wires f hw
    simp only [List.mem_toFinset, List.cons_append, List.mem_cons] at h ⊢
    rcases h with rfl | h
    · exact hbits7 (by simp [windowBits])
    · exact hreg _ h
  · exact Defer.deferTail_support bank15 bank15_ok f.site hg.site.kind _ PoolHost.newSourceH7 hlast.2
      (hlast.1 _ (Option.mem_def.mpr rfl)) hlow7 hhigh7 hbank7 hroot7 hbits7
      (by rw [clearData_targets, garbPorts_targets f hg]; exact fun w hw => hreg w (List.mem_append_right _ hw))
      (fun p hm => hlit p (List.mem_append_left _ (List.mem_cons_of_mem _ hm)))
      (fun c ps hm => hlook c ps (List.mem_append_left _ (List.mem_cons_of_mem _ hm))) _

end FastSite1

end
end ShorECDLP.Entrant.WEXFast
end

/-! ### Narrow rows with fused fast sites -/

section
namespace ShorECDLP.Entrant.WEXFast
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup PathShare
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant
open WideBank8 (GuardKept)
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
attribute [local irreducible] WEX.codeRecords lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps WEX.compile Bridge.translate
  MeasuredClear.measuredClear ECDSAAdd.Baselines.normalizeProgram

def gblockRec {n} : FBlock2 n → Nat
  | .std b => blockRecP2 bank15 b
  | .fast f => f.fusedRecords
  | .fast1 f => f.fusedRecords

def gblockProg {n} : (b : FBlock2 n) → (start : Nat) → Straight n start (start + gblockRec b)
  | .std b, start => PoolHost.blockProgH7 bank15 b start
  | .fast f, start => f.fusedProgram start
  | .fast1 f, start => f.fusedProgram start

def grecs {n} : FCode2 n → Nat
  | [] => 0
  | b :: code => gblockRec b + grecs code

def gprog {n} : (code : FCode2 n) → (start : Nat) → Straight n start (start + grecs code)
  | [], _ => .done
  | b :: code, start => castFinish (by simp [grecs]; omega)
      ((gblockProg b start).append (gprog code (start + gblockRec b)))

def gblockSrc {n} (read : ConstantBit n → Bool) : FBlock2 n → AdaptiveCircuit
  | .std b => PoolHost.blockSourceH7 bank15 read b
  | .fast f => f.fusedSource read
  | .fast1 f => f.fusedSource read

def gsrc {n} (read : ConstantBit n → Bool) : FCode2 n → AdaptiveCircuit
  | [] => .done
  | b :: code => (gblockSrc read b).seq (gsrc read code)

theorem gblockProg_run {n} (read : ConstantBit n → Bool) (b : FBlock2 n) (start : Nat)
    (history : Fin start → Bool) :
    ((gblockProg b start).instantiate read history).run = (gblockSrc read b).run := by
  cases b with
  | std b => exact PoolHost.blockProgH7_run bank15 read b start history
  | fast f => exact f.fusedProgram_run read start history
  | fast1 f => exact f.fusedProgram_run read start history

theorem gprog_run {n} (read : ConstantBit n → Bool) (code : FCode2 n) (start : Nat)
    (history : Fin start → Bool) :
    ((gprog code start).instantiate read history).run = (gsrc read code).run := by
  induction code generalizing start with
  | nil => rfl
  | cons b code ih =>
    rw [gprog, castFinish_instantiate, append_run_fixed _ _ _ _ _ (ih _), AdaptiveCircuit.run_seq, gblockProg_run]
    simp only [gsrc, AdaptiveCircuit.run_seq]

/-- Fused blocks additionally need the guard to survive the site arithmetic. -/
def GBlockGeo {n} : FBlock2 n → Prop
  | .std b => BlockGeoP2 bank15 b
  | .fast f => FastGeometry f ∧ GuardKept f.site
  | .fast1 f => FastGeometry1 f ∧ GuardKept f.site

theorem gblock_geo {n} (b : FBlock2 n) (hg : GBlockGeo b) : FBlockGeo b := by
  cases b with
  | std b => exact hg
  | fast f => exact hg.1
  | fast1 f => exact hg.1

def GBlockClean {n} : FBlock2 n → ECDSAAdd.State → Prop
  | .std b, st => BlockClean2 pathBank b st ∧ PoolHost.HostOK7 b st
  | .fast f, st => Clean pathBank st.basis ∧ Clean (portTargets f.site.ports ++ f.garb) st.basis
  | .fast1 f, st => Clean pathBank st.basis ∧ Clean (portTargets f.site.ports ++ f.garb) st.basis

def GCodeClean {n} (read : ConstantBit n → Bool) (address : Nat) : FCode2 n → ECDSAAdd.State → Prop
  | [], _ => True
  | b :: code, st => GBlockClean b st ∧
      ∀ m, m.length = ECDSAAdd.measurementCount (blockReference2 read address b.forget) →
        GCodeClean read address code (ECDSAAdd.run (blockReference2 read address b.forget) m st)

def GBlockSim {n} (read : ConstantBit n → Bool) (block : FBlock2 n)
    (branch : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords block.forget.code ∧
    ∀ address st, AddrValid windowBits windowRoot address st → GBlockClean block st →
      BlockSafe2 read address block.forget st →
      branch.kraus (Bridge.signedKet st) =
        c • Bridge.signedKet (ECDSAAdd.run (blockReference2 read address block.forget) m st)

def GSim {n} (read : ConstantBit n → Bool) (code : FCode2 n) (b : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords (erase2 (fforget code)) ∧
    ∀ a st, AddrValid windowBits windowRoot a st → GCodeClean read a code st →
      Safe2 read a (fforget code) st →
      b.kraus (Bridge.signedKet st) = c • Bridge.signedKet (ECDSAAdd.run (reference2 read a (fforget code)) m st)

theorem gblock_clean_to_fclean {n} (b : FBlock2 n) (st : ECDSAAdd.State) (h : GBlockClean b st) :
    FBlockClean b st := by
  cases b with
  | std b => exact ⟨h.1, h.2.1⟩
  | fast f => exact h
  | fast1 f => exact h

theorem gblock_sim {n} (read : ConstantBit n → Bool) (block : FBlock2 n) (hg : GBlockGeo block) :
    ∃ cs : List ℂ, List.Forall₂ (GBlockSim read block) (gblockSrc read block).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  cases block with
  | std b =>
    obtain ⟨cs, al, mass⟩ := PoolHost.block_simulationH7 read bank15 bank15_ok b hg
    refine ⟨cs, al.imp ?_, mass⟩
    intro br c h
    obtain ⟨m, hm, h⟩ := h
    exact ⟨m, hm, fun a st hs hc hsafe => h a st hs hc.1 hc.2 hsafe⟩
  | fast f =>
    obtain ⟨cs, al, mass⟩ := f.fused_simulation read hg.1 hg.2
    refine ⟨cs, al.imp ?_, mass⟩
    intro br c h
    obtain ⟨m, hm, h⟩ := h
    refine ⟨m, hm, fun a st hs hc hsafe => ?_⟩
    exact h a st ⟨hc.1, hs.1, hs.2⟩ hc.2 hsafe
  | fast1 f =>
    obtain ⟨cs, al, mass⟩ := f.fused_simulation read hg.1 hg.2
    refine ⟨cs, al.imp ?_, mass⟩
    intro br c h
    obtain ⟨m, hm, h⟩ := h
    refine ⟨m, hm, fun a st hs hc hsafe => ?_⟩
    exact h a st ⟨hc.1, hs.1, hs.2⟩ hc.2 hsafe

theorem gsrc_sim {n} (read : ConstantBit n → Bool) (code : FCode2 n) (hg : ∀ b ∈ code, GBlockGeo b) :
    ∃ cs : List ℂ, List.Forall₂ (GSim read code) (gsrc read code).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  induction code with
  | nil =>
    refine ⟨[1], .cons ?_ .nil, by simp⟩
    exact ⟨[], rfl, fun a st _ _ _ => by
      simp [reference2, erase2, fforget, specialize, ECDSAAdd.ShorPort.Tmpl.instantiate, ECDSAAdd.run]⟩
  | cons b code ih =>
    obtain ⟨cs₁, h₁, mass₁⟩ := gblock_sim read b (hg b (by simp))
    obtain ⟨cs₂, h₂, mass₂⟩ := ih (fun c hc => hg c (by simp [hc]))
    refine ⟨coherentSeqCoefficients cs₁ cs₂, ?_, ?_⟩
    · rw [gsrc, AdaptiveCircuit.run_seq]
      apply simulationAligned_seq h₁ h₂
      intro b₁ c₁ b₂ c₂ hb₁ hb₂
      obtain ⟨m₁, len₁, run₁⟩ := hb₁
      obtain ⟨m₂, len₂, run₂⟩ := hb₂
      refine ⟨m₁ ++ m₂, ?_, ?_⟩
      · simp [fforget_cons, erase2, List.length_append, len₁, len₂]
      · intro a st hs hc hsafe
        rw [fforget_cons] at hsafe ⊢
        have hm : m₁.length = ECDSAAdd.measurementCount (blockReference2 read a b.forget) :=
          len₁.trans (specialize_counts read b.forget.code a).2.symm
        have hn := fblock_addr read b (gblock_geo b (hg b (by simp))) a st hs (gblock_clean_to_fclean b st hc.1) m₁
        change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
        rw [run₁ a st hs hc.1 hsafe.1, map_smul,
          run₂ a (ECDSAAdd.run (blockReference2 read a b.forget) m₁ st) hn (hc.2 m₁ hm) (hsafe.2 m₁ hm),
          reference2_cons, run_append_records _ _ m₁ m₂ st hm]
        simp [smul_smul]
    · rw [simulationCoefficients_mass, mass₁, mass₂]
      norm_num

theorem gprog_coherent {n} (read : ConstantBit n → Bool) (code : FCode2 n) (hg : ∀ b ∈ code, GBlockGeo b)
    (Valid : BasisState → Prop) (result : BasisState → BasisState)
    (hsafe : ∀ s, Valid s → Safe2 read (tableAddressValue windowBits s) (fforget code) ⟨false,s⟩)
    (hclean : ∀ s, Valid s → GCodeClean read (tableAddressValue windowBits s) code ⟨false,s⟩)
    (hrun : ∀ s, Valid s → ∀ m,
      ECDSAAdd.run (reference2 read (tableAddressValue windowBits s) (fforget code)) m ⟨false,s⟩ = ⟨false,result s⟩)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((gprog code start).instantiate read history)
      (Finsupp.lmapDomain ℂ ℂ result) (fun s => s windowRoot = true ∧ Valid s) := by
  obtain ⟨cs, aligned, mass⟩ := gsrc_sim read code hg
  refine ⟨cs, ?_, mass⟩
  rw [gprog_run]
  apply aligned.imp
  intro b c hb s hs
  obtain ⟨m, _, h⟩ := hb
  have he := h (tableAddressValue windowBits s) ⟨false,s⟩ ⟨rfl, hs.1⟩ (hclean s hs.2) (hsafe s hs.2)
  rw [Bridge.signedKet_false, hrun s hs.2 m, Bridge.signedKet_false] at he
  simpa [ket] using he

def gblockTP {n} : FBlock2 n → Nat
  | .std b => PoolHost.blockTP7 bank15 b
  | .fast f => f.fusedTP
  | .fast1 f => f.fusedTP

def gcodeTP {n} : FCode2 n → Nat
  | [] => 0
  | b :: code => gblockTP b + gcodeTP code

def gblockSave {n} : FBlock2 n → Nat
  | .std _ => 0
  | .fast f => 24576 - ECDSAAdd.toffoliCount f.swapNet
  | .fast1 f => 16384 - ECDSAAdd.toffoliCount f.swapNet

def gsave {n} : FCode2 n → Nat
  | [] => 0
  | b :: code => gblockSave b + gsave code

def gblockRSave {n} : FBlock2 n → Nat
  | .std _ => 0
  | .fast f => 24576 - f.garb.length
  | .fast1 f => 16384 - f.garb.length

def grsave {n} : FCode2 n → Nat
  | [] => 0
  | b :: code => gblockRSave b + grsave code

def gblockSlack {n} : FBlock2 n → Nat
  | .std _ => 26
  | .fast f => fblockSlack (.fast f)
  | .fast1 f => fblockSlack (.fast1 f)

def gslack {n} : FCode2 n → Nat
  | [] => 0
  | b :: code => gblockSlack b + gslack code

theorem gblock_tCount {n} (read : ConstantBit n → Bool) (b : FBlock2 n) (hg : GBlockGeo b)
    (start : Nat) (history : Fin start → Bool) :
    ((gblockProg b start).instantiate read history).tCount = 7 * gblockTP b := by
  cases b with
  | std b => exact PoolHost.blockH7_tCount read bank15 b (geo_lay2 bank15 bank15_ok b hg) start history
  | fast f => exact f.fused_tCount read hg.1 start history
  | fast1 f => exact f.fused_tCount read hg.1 start history

theorem gprog_tCount {n} (read : ConstantBit n → Bool) (code : FCode2 n) (hg : ∀ b ∈ code, GBlockGeo b)
    (start : Nat) (history : Fin start → Bool) :
    ((gprog code start).instantiate read history).tCount = 7 * gcodeTP code := by
  induction code generalizing start with
  | nil => simp [gprog, grecs, gcodeTP, Straight.instantiate, AdaptiveCircuit.tCount]
  | cons b code ih =>
    rw [gprog, castFinish_instantiate,
      append_tCount_fixed _ _ _ _ _ (fun h => ih (fun d hd => hg d (by simp [hd])) _ h),
      gblock_tCount read b (hg b (by simp))]
    simp only [gcodeTP]; ring

theorem gcodeTP_relation {n} (code : FCode2 n) (hg : ∀ b ∈ code, GBlockGeo b) :
    gcodeTP code + gsave code = codeTP2 bank15 (fforget code) + PoolHost.codeExtra (fforget code) := by
  induction code with
  | nil => rfl
  | cons b code ih =>
    have ih' := ih (fun d hd => hg d (by simp [hd]))
    have hb : gblockTP b + gblockSave b = blockTP2 bank15 b.forget + PoolHost.blockExtra b.forget := by
      have hgb := hg b (by simp)
      cases b with
      | std b => cases b <;> simp [gblockTP, gblockSave, FBlock2.forget, PoolHost.blockTP7, PoolHost.blockExtra]
      | fast f =>
        have h := f.fused_tp_relation hgb.1
        simp only [gblockTP, gblockSave, FBlock2.forget, PoolHost.blockExtra]; omega
      | fast1 f =>
        have h := f.fused_tp_relation hgb.1
        simp only [gblockTP, gblockSave, FBlock2.forget, PoolHost.blockExtra]; omega
    simp only [gcodeTP, gsave, fforget_cons, codeTP2, PoolHost.codeExtra]
    omega

theorem grecs_relation {n} (code : FCode2 n) (hg : ∀ b ∈ code, GBlockGeo b) :
    grecs code + grsave code = recordsP2 bank15 (fforget code) := by
  induction code with
  | nil => rfl
  | cons b code ih =>
    have ih' := ih (fun d hd => hg d (by simp [hd]))
    have hb : gblockRec b + gblockRSave b = blockRecP2 bank15 b.forget := by
      have hgb := hg b (by simp)
      cases b with
      | std b => simp [gblockRec, gblockRSave, FBlock2.forget]
      | fast f => exact f.fused_records_relation hgb.1
      | fast1 f => exact f.fused_records_relation hgb.1
    simp only [grecs, grsave, fforget_cons, recordsP2]
    omega

theorem gprog_slots {n} (code : FCode2 n) (hg : ∀ b ∈ code, GBlockGeo b) (start : Nat) :
    (gprog code start).gateSlots ≤ codeSP2 bank15 (fforget code) + gslack code := by
  induction code generalizing start with
  | nil => simp [gprog, grecs, gslack, Straight.gateSlots, codeSP2]
  | cons b code ih =>
    have ih' := ih (fun d hd => hg d (by simp [hd])) (start + gblockRec b)
    have hb : (gblockProg b start).gateSlots ≤ blockSP2 bank15 b.forget + gblockSlack b := by
      have hgb := hg b (by simp)
      cases b with
      | std b =>
        rw [show gblockProg (.std b) start = PoolHost.blockProgH7 bank15 b start from rfl]
        exact PoolHost.blockH7_slots bank15 b (geo_lay2 bank15 bank15_ok b hgb) start
      | fast f => exact f.fused_slots hgb.1 start
      | fast1 f => exact f.fused_slots hgb.1 start
    rw [gprog, castFinish_gateSlots, Straight.gateSlots_append]
    simp only [fforget_cons, codeSP2, gslack]
    omega

theorem gblock_wellFormed {n} (b : FBlock2 n) (hg : GBlockGeo b)
    (hp : ∀ p, WInstr.literal p ∈ b.forget.code → GatePhysical p) (start : Nat) :
    (gblockProg b start).WellFormed := by
  cases b with
  | std b =>
    show (PoolHost.blockProgH7 bank15 b start).WellFormed
    exact PoolHost.blockH7_wellFormed bank15 bank15_ok b hg hp start
  | fast f =>
    exact f.fused_wellFormed hg.1 (fun p hm => hp p (by simpa [FBlock2.forget, siteUnit_code] using hm)) start
  | fast1 f =>
    exact f.fused_wellFormed hg.1 (fun p hm => hp p (by simpa [FBlock2.forget, siteUnit_code] using hm)) start

theorem gprog_wellFormed {n} (code : FCode2 n) (hg : ∀ b ∈ code, GBlockGeo b)
    (hp : ∀ p, WInstr.literal p ∈ erase2 (fforget code) → GatePhysical p) (start : Nat) :
    (gprog code start).WellFormed := by
  induction code generalizing start with
  | nil => trivial
  | cons b code ih =>
    rw [gprog, castFinish_wellFormed]
    apply straight_append_wellFormed
    · exact gblock_wellFormed b (hg b (by simp)) (fun p hm => hp p (by simp [erase2_cons, hm])) start
    · exact ih (fun d hd => hg d (by simp [hd])) (fun p hm => hp p (by simp [erase2_cons, hm])) _

theorem gprog_residue {n} (code : FCode2 n) (start : Nat) : AndGadget.residue (gprog code start) = 0 := by
  induction code generalizing start with
  | nil => simp [gprog, grecs]
  | cons b code ih =>
    have hb : AndGadget.residue (gblockProg b start) = 0 := by
      cases b with
      | std b => exact PoolHost.blockH7_residue bank15 b start
      | fast f => exact f.fused_residue start
      | fast1 f => exact f.fused_residue start
    simp [gprog, AndGadget.residue_cast, AndGadget.residue_append, hb, ih]

end
end ShorECDLP.Entrant.WEXFast
end

section
namespace ShorECDLP.Entrant.WEXFast
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup PathShare
open ECDSAAdd.Arithmetic ECDSAAdd.ShorPort ECDSAAdd.Entrant
open WideBank8 (GuardKept)
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
attribute [local irreducible] WEX.codeRecords lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps WEX.compile Bridge.translate
  MeasuredClear.measuredClear ECDSAAdd.Baselines.normalizeProgram

def GNoHost7 {n} : FBlock2 n → Prop
  | .std _ => True
  | .fast f => ∀ w ∈ f.garb, w ≠ hostWire ∧ w ≠ hostWire2 ∧ w ≠ hostWire3 ∧
      w ≠ 14877 ∧ w ≠ 14876 ∧ w ≠ 14875 ∧ w ≠ 14874
  | .fast1 f => ∀ w ∈ f.garb, w ≠ hostWire ∧ w ≠ hostWire2 ∧ w ≠ hostWire3 ∧
      w ≠ 14877 ∧ w ≠ 14876 ∧ w ≠ 14875 ∧ w ≠ 14874

theorem gblock_support (b : FBlock2 32768) (hg : GBlockGeo b)
    (hlit : ∀ p, WInstr.literal p ∈ b.forget.code → ∀ w ∈ ECDSAAdd.wires p,
      w = hostWire ∨ w = hostWire2 ∨ w = hostWire3 ∨
      w = PoolHost.hostWire4 ∨ w = PoolHost.hostWire5 ∨ w = PoolHost.hostWire6 ∨ w = PoolHost.hostWire7 ∨
      w ∈ PoolHost.newSourceH7)
    (hstrict : ∀ p, WInstr.literal p ∈ b.forget.code →
      (hostWire ∈ ECDSAAdd.wires p ∨ hostWire2 ∈ ECDSAAdd.wires p ∨ hostWire3 ∈ ECDSAAdd.wires p ∨
       PoolHost.hostWire4 ∈ ECDSAAdd.wires p ∨ PoolHost.hostWire5 ∈ ECDSAAdd.wires p ∨
       PoolHost.hostWire6 ∈ ECDSAAdd.wires p ∨ PoolHost.hostWire7 ∈ ECDSAAdd.wires p) →
      ∃ c, b = .std (.plain c))
    (hctl : ∀ c, b = .std (.plain c) → hostWire2 ∈ ECDSAAdd.wires (litProg c) → hostCtl ∉ ECDSAAdd.wires (litProg c))
    (hctl3 : ∀ c, b = .std (.plain c) →
      hostWire3 ∈ ECDSAAdd.wires (litProg c) → hostCtl3 ∉ ECDSAAdd.wires (litProg c))
    (hctl4 : ∀ c, b = .std (.plain c) →
      (14877 ∈ ECDSAAdd.wires (litProg c) ∨ 14876 ∈ ECDSAAdd.wires (litProg c) ∨
        14875 ∈ ECDSAAdd.wires (litProg c) ∨ 14874 ∈ ECDSAAdd.wires (litProg c)) →
      14111 ∉ ECDSAAdd.wires (litProg c) ∧ 19816 ∉ ECDSAAdd.wires (litProg c) ∧
      838 ∉ ECDSAAdd.wires (litProg c) ∧ 14112 ∉ ECDSAAdd.wires (litProg c) ∧
      19815 ∉ ECDSAAdd.wires (litProg c) ∧ 19814 ∉ ECDSAAdd.wires (litProg c))
    (hlook : ∀ c ps, WInstr.lookup c ps ∈ b.forget.code →
      (∀ q ∈ c, q ∈ PoolHost.newSourceH7) ∧ portTargets ps ⊆ PoolHost.newSourceH7)
    (hgarb : GNoHost7 b)
    (start : Nat) : ChallengeMigration.straightWires (gblockProg b start) ⊆ PoolHost.newSourceH7 := by
  have strict : (∀ c, b ≠ .std (.plain c)) → ∀ p, WInstr.literal p ∈ b.forget.code →
      ECDSAAdd.wires p ⊆ PoolHost.newSourceH7.toFinset := by
    intro hb p hp w hw
    rcases hlit p hp w hw with e | e | e | e | e | e | e | e
    · obtain ⟨c, hc⟩ := hstrict p hp (Or.inl (e ▸ hw)); exact absurd hc (hb c)
    · obtain ⟨c, hc⟩ := hstrict p hp (Or.inr (Or.inl (e ▸ hw))); exact absurd hc (hb c)
    · obtain ⟨c, hc⟩ := hstrict p hp (Or.inr (Or.inr (Or.inl (e ▸ hw)))); exact absurd hc (hb c)
    · obtain ⟨c, hc⟩ := hstrict p hp (Or.inr (Or.inr (Or.inr (Or.inl (e ▸ hw))))); exact absurd hc (hb c)
    · obtain ⟨c, hc⟩ := hstrict p hp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (e ▸ hw)))))); exact absurd hc (hb c)
    · obtain ⟨c, hc⟩ := hstrict p hp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (e ▸ hw))))))); exact absurd hc (hb c)
    · obtain ⟨c, hc⟩ := hstrict p hp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (e ▸ hw))))))); exact absurd hc (hb c)
    · exact List.mem_toFinset.mpr e
  cases b with
  | std b =>
    have hlow7 : ∀ i : Fin 7, WEXUnlookup.low i ∈ PoolHost.newSourceH7 := by
      intro i; have hi := i.isLt
      rw [PoolHost.newSourceH7_mem]
      simp only [WEXUnlookup.low, fixedPort, oldWork, PoolHost.retiredH7, retiredH, retired]
      omega
    exact PoolHost.blockH7_support bank15 bank15_ok b hg PoolHost.newSourceH7
      h7_root
      (h7_wire _ (by simp only [hostCtl, fixedPort, oldWork, PoolHost.retiredH7, retiredH, retired]; omega))
      (h7_wire _ (by simp only [hostCtl3, fixedPort, oldWork, PoolHost.retiredH7, retiredH, retired]; omega))
      (h7_wire 14111 (by simp only [fixedPort, oldWork, PoolHost.retiredH7, retiredH, retired]; omega))
      (h7_wire 19816 (by simp only [fixedPort, oldWork, PoolHost.retiredH7, retiredH, retired]; omega))
      (h7_wire 838 (by decide))
      (h7_wire 14112 (by simp only [fixedPort, oldWork, PoolHost.retiredH7, retiredH, retired]; omega))
      (h7_wire 19815 (by simp only [fixedPort, oldWork, PoolHost.retiredH7, retiredH, retired]; omega))
      (h7_wire 19814 (by simp only [fixedPort, oldWork, PoolHost.retiredH7, retiredH, retired]; omega))
      (h7_wire 14113 (by simp only [fixedPort, oldWork, PoolHost.retiredH7, retiredH, retired]; omega))
      h7_bits h7_bank hlow7 h7_high
      hlit
      (fun p hp hh => by obtain ⟨c, hc⟩ := hstrict p hp hh; exact ⟨c, FBlock2.std.inj hc⟩)
      (fun c hc => hctl c (congrArg FBlock2.std hc))
      (fun c hc => hctl3 c (congrArg FBlock2.std hc))
      (fun c hc => hctl4 c (congrArg FBlock2.std hc))
      hlook start
  | fast f =>
    exact f.fused_support_new hg.1
      (fun p hm => strict (fun c e => by cases e) p (by simpa [FBlock2.forget, siteUnit_code] using hm))
      (fun c ps hm => hlook c ps (by simpa [FBlock2.forget, siteUnit_code] using hm)) hgarb start
  | fast1 f =>
    exact f.fused_support_new hg.1
      (fun p hm => strict (fun c e => by cases e) p (by simpa [FBlock2.forget, siteUnit_code] using hm))
      (fun c ps hm => hlook c ps (by simpa [FBlock2.forget, siteUnit_code] using hm)) hgarb start

theorem gprog_support (code : FCode2 32768) (hg : ∀ b ∈ code, GBlockGeo b)
    (hlit : ∀ p, WInstr.literal p ∈ erase2 (fforget code) → ∀ w ∈ ECDSAAdd.wires p,
      w = hostWire ∨ w = hostWire2 ∨ w = hostWire3 ∨
      w = PoolHost.hostWire4 ∨ w = PoolHost.hostWire5 ∨ w = PoolHost.hostWire6 ∨ w = PoolHost.hostWire7 ∨
      w ∈ PoolHost.newSourceH7)
    (hstrict : ∀ b ∈ code, ∀ p, WInstr.literal p ∈ b.forget.code →
      (hostWire ∈ ECDSAAdd.wires p ∨ hostWire2 ∈ ECDSAAdd.wires p ∨ hostWire3 ∈ ECDSAAdd.wires p ∨
       PoolHost.hostWire4 ∈ ECDSAAdd.wires p ∨ PoolHost.hostWire5 ∈ ECDSAAdd.wires p ∨
       PoolHost.hostWire6 ∈ ECDSAAdd.wires p ∨ PoolHost.hostWire7 ∈ ECDSAAdd.wires p) →
      ∃ c, b = .std (.plain c))
    (hctl : ∀ b ∈ code, ∀ c, b = .std (.plain c) →
      hostWire2 ∈ ECDSAAdd.wires (litProg c) → hostCtl ∉ ECDSAAdd.wires (litProg c))
    (hctl3 : ∀ b ∈ code, ∀ c, b = .std (.plain c) →
      hostWire3 ∈ ECDSAAdd.wires (litProg c) → hostCtl3 ∉ ECDSAAdd.wires (litProg c))
    (hctl4 : ∀ b ∈ code, ∀ c, b = .std (.plain c) →
      (14877 ∈ ECDSAAdd.wires (litProg c) ∨ 14876 ∈ ECDSAAdd.wires (litProg c) ∨
        14875 ∈ ECDSAAdd.wires (litProg c) ∨ 14874 ∈ ECDSAAdd.wires (litProg c)) →
      14111 ∉ ECDSAAdd.wires (litProg c) ∧ 19816 ∉ ECDSAAdd.wires (litProg c) ∧
      838 ∉ ECDSAAdd.wires (litProg c) ∧ 14112 ∉ ECDSAAdd.wires (litProg c) ∧
      19815 ∉ ECDSAAdd.wires (litProg c) ∧ 19814 ∉ ECDSAAdd.wires (litProg c))
    (hlook : ∀ c ps, WInstr.lookup c ps ∈ erase2 (fforget code) →
      (∀ q ∈ c, q ∈ PoolHost.newSourceH7) ∧ portTargets ps ⊆ PoolHost.newSourceH7)
    (hgarb : ∀ b ∈ code, GNoHost7 b)
    (start : Nat) : ChallengeMigration.straightWires (gprog code start) ⊆ PoolHost.newSourceH7 := by
  induction code generalizing start with
  | nil => simp [gprog, grecs, ChallengeMigration.straightWires]
  | cons b code ih =>
    rw [gprog, support_cast, straightWires_append]
    exact List.append_subset.mpr ⟨gblock_support b (hg b (by simp))
      (fun p hm => hlit p (by simp [erase2_cons, hm])) (hstrict b (by simp))
      (hctl b (by simp)) (hctl3 b (by simp)) (hctl4 b (by simp))
      (fun c ps hm => hlook c ps (by simp [erase2_cons, hm])) (hgarb b (by simp)) start,
      ih (fun d hd => hg d (by simp [hd])) (fun p hm => hlit p (by simp [erase2_cons, hm]))
        (fun d hd => hstrict d (by simp [hd])) (fun d hd => hctl d (by simp [hd]))
        (fun d hd => hctl3 d (by simp [hd])) (fun d hd => hctl4 d (by simp [hd]))
        (fun c ps hm => hlook c ps (by simp [erase2_cons, hm])) (fun d hd => hgarb d (by simp [hd])) _⟩

theorem rowCF_ggeo : ∀ b ∈ rowCF, GBlockGeo b := by
  intro b hb
  have h := rowCF_geo b hb
  cases b with
  | std c => exact h
  | fast f => exact ⟨h, by rw [fast_mem_rowCF f hb]; exact WideBank8.triple_guardKept⟩
  | fast1 f => exact ⟨h, by rw [fast1_mem_rowCF f hb]; exact WideBank8.site2_guardKept⟩

end
end ShorECDLP.Entrant.WEXFast
end

/-! ### Narrow rows: a pair of adjacent units with one fused clear -/

namespace ShorECDLP.Entrant.WEXFast
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup PathShare
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant
open MeasuredClear (ClearPort)
open WideBank8 (GuardKept)
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

structure UnitPair7 (n : Nat) where
  u₁ : UnitSite n
  u₂ : UnitSite n

namespace UnitPair7
variable {n : Nat} (q : UnitPair7 n)

def gd : List (ClearPort n) := clearData q.u₁.clear.ports

def Geo : Prop :=
  UnitGeoP bank15 q.u₁ ∧ UnitGeoP bank15 q.u₂ ∧ q.u₁.clear.guard = windowRoot ∧ q.u₂.clear.guard = windowRoot

def pairRecords : Nat :=
  codeRecords bank15.bits bank15.paths windowRoot (normalizeW q.u₁.pre) +
    (q.gd.length + Defer.tailRec bank15 (WideBank8.unitTail q.u₂))

def pairProgram (start : Nat) : Straight n start (start + q.pairRecords) :=
  castFinish (by simp only [pairRecords]; omega)
    ((compile bank15.bits bank15.paths windowRoot (normalizeW q.u₁.pre) start).append
      (Defer.deferTail bank15 (WideBank8.unitTail q.u₂) q.gd
        (start + codeRecords bank15.bits bank15.paths windowRoot (normalizeW q.u₁.pre))))

def pairSource (read : ConstantBit n → Bool) : AdaptiveCircuit :=
  (source read bank15.bits bank15.paths windowRoot (normalizeW q.u₁.pre)).seq
    (Defer.deferSource bank15 read (WideBank8.unitTail q.u₂) q.gd)

theorem pairProgram_run (read : ConstantBit n → Bool) (start : Nat) (history : Fin start → Bool) :
    ((q.pairProgram start).instantiate read history).run = (q.pairSource read).run := by
  rw [pairProgram, castFinish_instantiate,
    append_run_fixed _ _ _ _ _ (fun h => Defer.deferTail_run bank15 read (WideBank8.unitTail q.u₂) q.gd _ h),
    AdaptiveCircuit.run_seq, compile_run]
  simp only [pairSource, AdaptiveCircuit.run_seq]

theorem gd_nodup (hg : q.Geo) : (q.gd.map ClearPort.target).Nodup := by
  rw [gd, clearData_targets]
  exact (hg.1.site.placed (.lookup (some q.u₁.clear.guard) q.u₁.clear.ports)
    (by simp [MaskedSite.code])).2.1

theorem pair_sim (read : ConstantBit n → Bool) (hg : q.Geo) :
    ∃ cs : List ℂ, List.Forall₂ (fun (br : InstrumentBranch) (c : ℂ) =>
      ∃ m : List Bool, m.length = literalRecords (erase2 (Block2.unit q.u₁ :: Block2.unit q.u₂ :: [])) ∧
        ∀ address st, AddrValid windowBits windowRoot address st → Clean pathBank st.basis →
          Safe2 read address (Block2.unit q.u₁ :: Block2.unit q.u₂ :: []) st →
          br.kraus (Bridge.signedKet st) =
            c • Bridge.signedKet (ECDSAAdd.run
              (reference2 read address (Block2.unit q.u₁ :: Block2.unit q.u₂ :: [])) m st))
      (q.pairSource read).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
  have hgn := q.gd_nodup hg
  obtain ⟨g1, g2, r1, r2⟩ := hg
  have hp1 : ∀ i ∈ q.u₁.pre, PlacedPair bank15.bits bank15.paths windowRoot i := fun i hi =>
    g1.placed i (List.mem_append_left _ hi)
  obtain ⟨c1, a1, m1⟩ := lnormalized_simulation read bank15.bits bank15.paths bank15_ok.bitsLen q.u₁.pre
    (fun i hi => pair_of_placed_lit _ _ i (hp1 i hi))
  obtain ⟨c2, a2, m2⟩ := Defer.utail_sim read bank15 bank15_ok q.u₂ g2 r2 q.gd hgn
  refine ⟨coherentSeqCoefficients c1 c2, ?_, ?_⟩
  · rw [pairSource, AdaptiveCircuit.run_seq]
    apply simulationAligned_seq a1 a2
    intro b₁ k₁ b₂ k₂ h₁ h₂
    obtain ⟨m₁, hm₁, h₁⟩ := h₁
    obtain ⟨m₂, hm₂, h₂⟩ := h₂
    refine ⟨m₁ ++ m₂, ?_, ?_⟩
    · simp [erase2, Block2.code, UnitSite.code, literalRecords_append, literalRecords, hm₁, hm₂]
    · intro a st hs hcl hsafe
      have hsv : SimulationValid bank15.bits bank15.paths windowRoot a st := ⟨hcl, hs.1, hs.2⟩
      have hm1c : m₁.length = ECDSAAdd.measurementCount (blockReference2 read a (.unit q.u₁)) := by
        rw [hm₁, blockReference2, (specialize_counts read _ a).2]
        simp [Block2.code, UnitSite.code, literalRecords_append, literalRecords]
      have hsafe1 : ∀ m, Clean (portTargets q.u₁.clear.ports)
          (ECDSAAdd.run ((specialize q.u₁.code a).instantiate read) m st).basis := hsafe.1
      have hsafe2 : ∀ m, Clean (portTargets q.u₂.clear.ports)
          (ECDSAAdd.run ((specialize q.u₂.code a).instantiate read) m
            (ECDSAAdd.run ((specialize q.u₁.code a).instantiate read) m₁ st)).basis :=
        (hsafe.2 m₁ hm1c).1
      have hmidv := strict_preserves read bank15.bits bank15.paths q.u₁.code a g1.placed st hsv m₁
      have hn := strict_preserves read bank15.bits bank15.paths q.u₁.pre a hp1 st hsv m₁
      have hrun := unit_runP read bank15 q.u₁ g1 a st m₁ hsv
      have h1 := h₁ a st hs (strict_pathsClean read bank15.bits bank15.paths q.u₁.pre a hp1 st hsv)
      have hred : ECDSAAdd.run (reference2 read a (Block2.unit q.u₁ :: Block2.unit q.u₂ :: [])) (m₁ ++ m₂) st =
          ECDSAAdd.run ((specialize q.u₂.code a).instantiate read) m₂
            (ECDSAAdd.run ((specialize q.u₁.code a).instantiate read) m₁ st) := by
        rw [reference2_cons, reference2_cons, reference2_nil, List.append_nil,
          run_append_records _ _ m₁ m₂ st hm1c]
        rfl
      rw [hred]
      set next := ECDSAAdd.run ((specialize q.u₁.pre a).instantiate read) m₁ st with hnext
      have hclean : Clean (portTargets q.u₁.clear.ports)
          (tableXorState (portMask read q.u₁.clear.ports a) (next.basis q.u₁.clear.guard) next.basis) := by
        have h := hsafe1 m₁
        rw [hrun] at h
        exact h
      have hlast := g1.site.placed (.lookup (some q.u₁.clear.guard) q.u₁.clear.ports) (by simp [MaskedSite.code])
      have hfin : (⟨next.phase, clearRegister (portTargets q.u₁.clear.ports) next.basis⟩ : ECDSAAdd.State) =
          ECDSAAdd.run ((specialize q.u₁.code a).instantiate read) m₁ st := by
        rw [hrun, clear_eq_unload read q.u₁.clear.ports a q.u₁.clear.guard next.basis hclean]
      set mid := ECDSAAdd.run ((specialize q.u₁.code a).instantiate read) m₁ st with hmid
      have hgdv : ∀ p ∈ q.gd, next.basis p.target =
          (mid.basis q.u₂.clear.guard && decide (read (p.ref a) = p.value)) := by
        intro p hp
        simp only [gd, clearData] at hp
        obtain ⟨p0, hp0, rfl⟩ := List.mem_map.mp hp
        have hl := loaded_of_clean_unload read q.u₁.clear.ports a q.u₁.clear.guard next.basis
          hlast.2.1 hclean p0 hp0
        rw [r1, hn.2.2] at hl
        rw [r2, hmidv.2.2]
        exact hl
      have hph : next.phase = mid.phase := by rw [← hfin]
      have hclr : clearRegister (q.gd.map ClearPort.target) next.basis = mid.basis := by
        rw [gd, clearData_targets, ← hfin]
      have h2 := h₂ a mid next hmidv hsafe2 hgdv hph hclr
      change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
      rw [h1, map_smul, h2, smul_smul]
  · rw [simulationCoefficients_mass, m1, m2]
    norm_num

def pairTP : Nat :=
  literalToffolis (normalizeW q.u₁.pre) + traversals q.u₁.pre * (2 ^ bank15.bits.length - 1) +
    blockTP2 bank15 (.unit q.u₂)

def pairSave : Nat := (tableAddressTree bank15.high 0 1).internalNodes + 120

def pairRSave : Nat :=
  MeasuredClear.recordMeasurements
    (MeasuredClear.recordUnaryOps (tableAddressTree bank15.high 0 1) q.u₁.clear.guard bank15.hp) + 127

theorem pair_tCount (read : ConstantBit n → Bool) (hg : q.Geo) (start : Nat) (history : Fin start → Bool) :
    ((q.pairProgram start).instantiate read history).tCount = 7 * q.pairTP := by
  obtain ⟨h1, -⟩ := geo_lay2 bank15 bank15_ok (.unit q.u₁) hg.1
  obtain ⟨h2, h2t⟩ := geo_lay2 bank15 bank15_ok (.unit q.u₂) hg.2.1
  rw [pairProgram, castFinish_instantiate,
    append_tCount_fixed _ _ _ _ _ (fun h => Defer.deferTail_tCount read bank15 (WideBank8.unitTail q.u₂) q.gd
      h2t h2 _ h),
    WEX.compile_tCount read _ _ _ _ h1 start history]
  simp only [pairTP, blockTP2, WideBank8.unitTail, traversals_normalize]
  ring

theorem pair_tp_relation :
    q.pairTP + UnitPair7.pairSave = blockTP2 bank15 (.unit q.u₁) + blockTP2 bank15 (.unit q.u₂) := by
  simp only [pairTP, pairSave, blockTP2]
  omega

theorem pair_records_relation :
    q.pairRecords + q.pairRSave = blockRecP2 bank15 (.unit q.u₁) + blockRecP2 bank15 (.unit q.u₂) := by
  simp only [pairRecords, pairRSave, blockRecP2, Defer.tailRec, Defer.fuseRec, gd, clearData, List.length_map,
    WideBank8.unitTail]
  omega

theorem pair_slots (hg : q.Geo) (start : Nat) :
    (q.pairProgram start).gateSlots ≤ blockSP2 bank15 (.unit q.u₁) + blockSP2 bank15 (.unit q.u₂) + 12 := by
  obtain ⟨h1, -⟩ := geo_lay2 bank15 bank15_ok (.unit q.u₁) hg.1
  obtain ⟨h2, h2t⟩ := geo_lay2 bank15 bank15_ok (.unit q.u₂) hg.2.1
  rw [pairProgram, castFinish_gateSlots, Straight.gateSlots_append, WEX.compile_slots _ _ _ _ h1 start,
    Defer.deferTail_slots bank15 (WideBank8.unitTail q.u₂) q.gd h2t h2]
  simp only [blockSP2, gd, clearData, List.length_map, WideBank8.unitTail, bank_tree_leaves, bank_tree_nodes]
  omega

attribute [local irreducible] WEX.codeRecords lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps WEX.compile Bridge.translate
  MeasuredClear.measuredClear MeasuredClear.measuredClear8 ECDSAAdd.Baselines.normalizeProgram

theorem pair_wellFormed (hg : q.Geo)
    (hp : ∀ p, WInstr.literal p ∈ q.u₁.code ++ q.u₂.code → GatePhysical p) (start : Nat) :
    (q.pairProgram start).WellFormed := by
  have hpref1 : ∀ i ∈ q.u₁.pre, LPlaced bank15.bits bank15.paths windowRoot i := fun i hi =>
    pair_of_placed_lit _ _ i (hg.1.placed i (List.mem_append_left _ hi))
  have hl1 : ∀ p, WInstr.literal p ∈ q.u₁.pre → GatePhysical p := fun p hm =>
    hp p (List.mem_append_left _ (List.mem_append_left _ hm))
  have hl2 : ∀ p, WInstr.literal p ∈ q.u₂.pre → GatePhysical p := fun p hm =>
    hp p (List.mem_append_right _ (List.mem_append_left _ hm))
  rw [pairProgram, castFinish_wellFormed]
  exact straight_append_wellFormed _ _
    (compile_wellFormedL _ _ _ _ bank15_ok.bitsLen (lplaced_normalize _ _ _ _ hpref1)
      (normalized_literals_valid q.u₁.pre hl1) start)
    (Defer.unitTail_wellFormed bank15 bank15_ok q.u₂ hg.2.1 q.gd hl2 _)

theorem pair_residue (start : Nat) : AndGadget.residue (q.pairProgram start) = 0 := by
  simp [pairProgram, AndGadget.residue_cast, AndGadget.residue_append, WEXCredit.compile_residue,
    Defer.deferTail_residue]

theorem pair_support_new (hg : q.Geo)
    (hlit : ∀ p, WInstr.literal p ∈ q.u₁.code ++ q.u₂.code → ECDSAAdd.wires p ⊆ PoolHost.newSourceH7.toFinset)
    (hlook : ∀ c ps, WInstr.lookup c ps ∈ q.u₁.code ++ q.u₂.code →
      (∀ x ∈ c, x ∈ PoolHost.newSourceH7) ∧ portTargets ps ⊆ PoolHost.newSourceH7)
    (start : Nat) : ChallengeMigration.straightWires (q.pairProgram start) ⊆ PoolHost.newSourceH7 := by
  obtain ⟨g1, g2, -, -⟩ := hg
  have hl1 := hlook (some q.u₁.clear.guard) q.u₁.clear.ports
    (List.mem_append_left _ (by simp [UnitSite.code]))
  have hl2 := hlook (some q.u₂.clear.guard) q.u₂.clear.ports
    (List.mem_append_right _ (by simp [UnitSite.code]))
  have hroot7 : windowRoot ∈ PoolHost.newSourceH7 := h7_root
  have hbits7 : windowBits ⊆ PoolHost.newSourceH7 := h7_bits
  have hbank7 : pathBank ⊆ PoolHost.newSourceH7 := h7_bank
  have hhigh7 : bank15.high ⊆ PoolHost.newSourceH7 := h7_high
  have hlow7 : ∀ i : Fin 7, WEXUnlookup.low i ∈ PoolHost.newSourceH7 := by
    intro i; have hi := i.isLt
    rw [PoolHost.newSourceH7_mem]
    simp only [WEXUnlookup.low, fixedPort, oldWork, PoolHost.retiredH7, retiredH, retired]
    omega
  rw [pairProgram, support_cast, straightWires_append]
  refine List.append_subset.mpr ⟨?_, ?_⟩
  · exact compile_support _ _ _ _ PoolHost.newSourceH7 hroot7 hbits7 hbank7
      (normalized_lit_support _ PoolHost.newSourceH7
        (fun p hm => hlit p (List.mem_append_left _ (List.mem_append_left _ hm))))
      (normalized_look_support _ PoolHost.newSourceH7
        (fun c ps hm => hlook c ps (List.mem_append_left _ (List.mem_append_left _ hm)))) start
  · exact Defer.deferTail_support bank15 bank15_ok (WideBank8.unitTail q.u₂) g2.site.kind _ PoolHost.newSourceH7 hl2.2
      (hl2.1 _ (Option.mem_def.mpr rfl)) hlow7 hhigh7 hbank7 hroot7 hbits7
      (by rw [gd, clearData_targets]; exact hl1.2)
      (fun p hm => hlit p (List.mem_append_right _ (List.mem_append_left _ (show _ ∈ q.u₂.pre from hm))))
      (fun c ps hm => hlook c ps (List.mem_append_right _ (List.mem_append_left _ (show _ ∈ q.u₂.pre from hm)))) _

end UnitPair7

/-! #### Narrow codes with fused pairs -/

attribute [local irreducible] WEX.codeRecords lookupMeasurements WEX.portOps tableAddressTree
  MeasuredClear.recordMeasurements MeasuredClear.recordUnaryOps WEX.compile Bridge.translate
  MeasuredClear.measuredClear MeasuredClear.measuredClear8 ECDSAAdd.Baselines.normalizeProgram

inductive HBlock (n : Nat) where
  | blk (b : FBlock2 n)
  | pair (q : UnitPair7 n)
abbrev HCode (n : Nat) := List (HBlock n)

def HBlock.forgetL {n} : HBlock n → Code2 n
  | .blk b => b.forget :: []
  | .pair q => Block2.unit q.u₁ :: Block2.unit q.u₂ :: []

def hforget {n} (code : HCode n) : Code2 n := code.flatMap HBlock.forgetL

@[simp] theorem hforget_cons {n} (b : HBlock n) (code : HCode n) :
    hforget (b :: code) = b.forgetL ++ hforget code := by
  simp [hforget]

@[simp] theorem hforget_append {n} (a b : HCode n) : hforget (a ++ b) = hforget a ++ hforget b := by
  simp [hforget, List.flatMap_append]

theorem hforget_blk {n} (c : FCode2 n) : hforget (c.map HBlock.blk) = fforget c := by
  induction c with
  | nil => rfl
  | cons b c ih => rw [List.map_cons, hforget_cons, ih]; rfl

theorem codeTP2_append7 {n} (B : Bank) (a b : Code2 n) : codeTP2 B (a ++ b) = codeTP2 B a + codeTP2 B b := by
  induction a with
  | nil => simp [codeTP2]
  | cons x a ih => simp [codeTP2, ih, Nat.add_assoc]

theorem recordsP2_append7 {n} (B : Bank) (a b : Code2 n) :
    recordsP2 B (a ++ b) = recordsP2 B a + recordsP2 B b := by
  induction a with
  | nil => simp [recordsP2]
  | cons x a ih => simp [recordsP2, ih, Nat.add_assoc]

theorem codeSP2_append7 {n} (B : Bank) (a b : Code2 n) : codeSP2 B (a ++ b) = codeSP2 B a + codeSP2 B b := by
  induction a with
  | nil => simp [codeSP2]
  | cons x a ih => simp [codeSP2, ih, Nat.add_assoc]

def hblockRec {n} : HBlock n → Nat
  | .blk b => gblockRec b
  | .pair q => q.pairRecords

def hblockProg {n} : (b : HBlock n) → (start : Nat) → Straight n start (start + hblockRec b)
  | .blk b, start => gblockProg b start
  | .pair q, start => q.pairProgram start

def hrecs {n} : HCode n → Nat
  | [] => 0
  | b :: code => hblockRec b + hrecs code

def hprog {n} : (code : HCode n) → (start : Nat) → Straight n start (start + hrecs code)
  | [], _ => .done
  | b :: code, start => castFinish (by simp [hrecs]; omega)
      ((hblockProg b start).append (hprog code (start + hblockRec b)))

def hblockSrc {n} (read : ConstantBit n → Bool) : HBlock n → AdaptiveCircuit
  | .blk b => gblockSrc read b
  | .pair q => q.pairSource read

def hsrc {n} (read : ConstantBit n → Bool) : HCode n → AdaptiveCircuit
  | [] => .done
  | b :: code => (hblockSrc read b).seq (hsrc read code)

theorem hblockProg_run {n} (read : ConstantBit n → Bool) (b : HBlock n) (start : Nat)
    (history : Fin start → Bool) :
    ((hblockProg b start).instantiate read history).run = (hblockSrc read b).run := by
  cases b with
  | blk b => exact gblockProg_run read b start history
  | pair q => exact q.pairProgram_run read start history

theorem hprog_run {n} (read : ConstantBit n → Bool) (code : HCode n) (start : Nat)
    (history : Fin start → Bool) :
    ((hprog code start).instantiate read history).run = (hsrc read code).run := by
  induction code generalizing start with
  | nil => rfl
  | cons b code ih =>
    rw [hprog, castFinish_instantiate, append_run_fixed _ _ _ _ _ (ih _), AdaptiveCircuit.run_seq, hblockProg_run]
    simp only [hsrc, AdaptiveCircuit.run_seq]

def HBlockGeo {n} : HBlock n → Prop
  | .blk b => GBlockGeo b
  | .pair q => q.Geo

def HBlockClean {n} : HBlock n → ECDSAAdd.State → Prop
  | .blk b, st => GBlockClean b st
  | .pair _, st => Clean pathBank st.basis

def HCodeClean {n} (read : ConstantBit n → Bool) (address : Nat) : HCode n → ECDSAAdd.State → Prop
  | [], _ => True
  | b :: code, st => HBlockClean b st ∧
      ∀ m, m.length = ECDSAAdd.measurementCount (reference2 read address b.forgetL) →
        HCodeClean read address code (ECDSAAdd.run (reference2 read address b.forgetL) m st)

def HBlockSim {n} (read : ConstantBit n → Bool) (block : HBlock n)
    (branch : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords (erase2 block.forgetL) ∧
    ∀ address st, AddrValid windowBits windowRoot address st → HBlockClean block st →
      Safe2 read address block.forgetL st →
      branch.kraus (Bridge.signedKet st) =
        c • Bridge.signedKet (ECDSAAdd.run (reference2 read address block.forgetL) m st)

theorem hblock_sim {n} (read : ConstantBit n → Bool) (block : HBlock n) (hg : HBlockGeo block) :
    ∃ cs : List ℂ, List.Forall₂ (HBlockSim read block) (hblockSrc read block).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  cases block with
  | blk b =>
    obtain ⟨cs, al, mass⟩ := gblock_sim read b hg
    refine ⟨cs, al.imp ?_, mass⟩
    intro br c h
    obtain ⟨m, hm, h⟩ := h
    refine ⟨m, by rw [show (HBlock.blk b).forgetL = b.forget :: [] from rfl, WideBank8.Fast16.erase2_single]; exact hm,
      fun a st hs hc hsafe => ?_⟩
    rw [show (HBlock.blk b).forgetL = b.forget :: [] from rfl, WideBank8.Fast16.reference2_single]
    exact h a st hs hc hsafe.1
  | pair q =>
    obtain ⟨cs, al, mass⟩ := q.pair_sim read hg
    exact ⟨cs, al.imp (fun _ _ h => h), mass⟩

theorem hblock_addr {n} (read : ConstantBit n → Bool) (b : HBlock n) (hg : HBlockGeo b)
    (a : Nat) (st : ECDSAAdd.State) (hs : AddrValid windowBits windowRoot a st)
    (hc : HBlockClean b st) (m : List Bool) :
    AddrValid windowBits windowRoot a (ECDSAAdd.run (reference2 read a b.forgetL) m st) := by
  cases b with
  | blk b =>
    rw [show (HBlock.blk b).forgetL = b.forget :: [] from rfl, WideBank8.Fast16.reference2_single]
    exact fblock_addr read b (gblock_geo b hg) a st hs (gblock_clean_to_fclean b st hc) m
  | pair q =>
    have hp : ∀ i ∈ erase2 (Block2.unit q.u₁ :: Block2.unit q.u₂ :: []),
        PlacedPair windowBits pathBank windowRoot i := by
      intro i hi
      rw [erase2_cons, erase2_cons, erase2_nil, List.append_nil, List.mem_append] at hi
      rcases hi with hi | hi
      · exact hg.1.placed i hi
      · exact hg.2.1.placed i hi
    have h := strict_preserves read windowBits pathBank (erase2 (Block2.unit q.u₁ :: Block2.unit q.u₂ :: []))
      a hp st ⟨hc, hs.1, hs.2⟩ m
    exact ⟨h.2.1, h.2.2⟩

def HSim {n} (read : ConstantBit n → Bool) (code : HCode n) (b : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords (erase2 (hforget code)) ∧
    ∀ a st, AddrValid windowBits windowRoot a st → HCodeClean read a code st →
      Safe2 read a (hforget code) st →
      b.kraus (Bridge.signedKet st) = c • Bridge.signedKet (ECDSAAdd.run (reference2 read a (hforget code)) m st)

theorem hsrc_sim {n} (read : ConstantBit n → Bool) (code : HCode n) (hg : ∀ b ∈ code, HBlockGeo b) :
    ∃ cs : List ℂ, List.Forall₂ (HSim read code) (hsrc read code).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  induction code with
  | nil =>
    refine ⟨[1], .cons ?_ .nil, by simp⟩
    exact ⟨[], rfl, fun a st _ _ _ => by
      simp [reference2, erase2, hforget, specialize, ECDSAAdd.ShorPort.Tmpl.instantiate, ECDSAAdd.run]⟩
  | cons b code ih =>
    obtain ⟨cs₁, h₁, mass₁⟩ := hblock_sim read b (hg b (by simp))
    obtain ⟨cs₂, h₂, mass₂⟩ := ih (fun c hc => hg c (by simp [hc]))
    refine ⟨coherentSeqCoefficients cs₁ cs₂, ?_, ?_⟩
    · rw [hsrc, AdaptiveCircuit.run_seq]
      apply simulationAligned_seq h₁ h₂
      intro b₁ c₁ b₂ c₂ hb₁ hb₂
      obtain ⟨m₁, len₁, run₁⟩ := hb₁
      obtain ⟨m₂, len₂, run₂⟩ := hb₂
      refine ⟨m₁ ++ m₂, ?_, ?_⟩
      · simp [hforget_cons, erase2_append, List.length_append, len₁, len₂]
      · intro a st hs hc hsafe
        rw [hforget_cons] at hsafe ⊢
        have hm : m₁.length = ECDSAAdd.measurementCount (reference2 read a b.forgetL) :=
          len₁.trans (specialize_counts read (erase2 b.forgetL) a).2.symm
        have hsp := WideBank8.Fast16.safe2_append_inv read a b.forgetL (hforget code) st hsafe
        have hn := hblock_addr read b (hg b (by simp)) a st hs hc.1 m₁
        change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
        rw [run₁ a st hs hc.1 hsp.1, map_smul,
          run₂ a (ECDSAAdd.run (reference2 read a b.forgetL) m₁ st) hn (hc.2 m₁ hm) (hsp.2 m₁ hm),
          reference2_append, run_append_records _ _ m₁ m₂ st hm]
        simp [smul_smul]
    · rw [simulationCoefficients_mass, mass₁, mass₂]
      norm_num

theorem hprog_coherent {n} (read : ConstantBit n → Bool) (code : HCode n) (hg : ∀ b ∈ code, HBlockGeo b)
    (Valid : BasisState → Prop) (result : BasisState → BasisState)
    (hsafe : ∀ s, Valid s → Safe2 read (tableAddressValue windowBits s) (hforget code) ⟨false,s⟩)
    (hclean : ∀ s, Valid s → HCodeClean read (tableAddressValue windowBits s) code ⟨false,s⟩)
    (hrun : ∀ s, Valid s → ∀ m,
      ECDSAAdd.run (reference2 read (tableAddressValue windowBits s) (hforget code)) m ⟨false,s⟩ = ⟨false,result s⟩)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((hprog code start).instantiate read history)
      (Finsupp.lmapDomain ℂ ℂ result) (fun s => s windowRoot = true ∧ Valid s) := by
  obtain ⟨cs, aligned, mass⟩ := hsrc_sim read code hg
  refine ⟨cs, ?_, mass⟩
  rw [hprog_run]
  apply aligned.imp
  intro b c hb s hs
  obtain ⟨m, _, h⟩ := hb
  have he := h (tableAddressValue windowBits s) ⟨false,s⟩ ⟨rfl, hs.1⟩ (hclean s hs.2) (hsafe s hs.2)
  rw [Bridge.signedKet_false, hrun s hs.2 m, Bridge.signedKet_false] at he
  simpa [ket] using he

def hblockTP {n} : HBlock n → Nat
  | .blk b => gblockTP b
  | .pair q => q.pairTP

def hcodeTP {n} : HCode n → Nat
  | [] => 0
  | b :: code => hblockTP b + hcodeTP code

def hblockSave {n} : HBlock n → Nat
  | .blk b => gblockSave b
  | .pair _ => UnitPair7.pairSave

def hsave {n} : HCode n → Nat
  | [] => 0
  | b :: code => hblockSave b + hsave code

def hblockRSave {n} : HBlock n → Nat
  | .blk b => gblockRSave b
  | .pair q => q.pairRSave

def hrsave {n} : HCode n → Nat
  | [] => 0
  | b :: code => hblockRSave b + hrsave code

def hblockSlack {n} : HBlock n → Nat
  | .blk b => gblockSlack b
  | .pair _ => 52

def hslack {n} : HCode n → Nat
  | [] => 0
  | b :: code => hblockSlack b + hslack code

theorem hblock_tCount {n} (read : ConstantBit n → Bool) (b : HBlock n) (hg : HBlockGeo b)
    (start : Nat) (history : Fin start → Bool) :
    ((hblockProg b start).instantiate read history).tCount = 7 * hblockTP b := by
  cases b with
  | blk b => exact gblock_tCount read b hg start history
  | pair q => exact q.pair_tCount read hg start history

theorem hprog_tCount {n} (read : ConstantBit n → Bool) (code : HCode n) (hg : ∀ b ∈ code, HBlockGeo b)
    (start : Nat) (history : Fin start → Bool) :
    ((hprog code start).instantiate read history).tCount = 7 * hcodeTP code := by
  induction code generalizing start with
  | nil => simp [hprog, hrecs, hcodeTP, Straight.instantiate, AdaptiveCircuit.tCount]
  | cons b code ih =>
    rw [hprog, castFinish_instantiate,
      append_tCount_fixed _ _ _ _ _ (fun h => ih (fun d hd => hg d (by simp [hd])) _ h),
      hblock_tCount read b (hg b (by simp))]
    simp only [hcodeTP]; ring

theorem hcodeTP_relation {n} (code : HCode n) (hg : ∀ b ∈ code, HBlockGeo b) :
    hcodeTP code + hsave code = codeTP2 bank15 (hforget code) + PoolHost.codeExtra (hforget code) := by
  induction code with
  | nil => rfl
  | cons b code ih =>
    have ih' := ih (fun d hd => hg d (by simp [hd]))
    have hb : hblockTP b + hblockSave b = codeTP2 bank15 b.forgetL + PoolHost.codeExtra b.forgetL := by
      have hgb := hg b (by simp)
      cases b with
      | blk b =>
        have h := gcodeTP_relation (b :: []) (fun d hd => by simp at hd; subst hd; exact hgb)
        simp only [gcodeTP, gsave, fforget, List.map_cons, List.map_nil, codeTP2, PoolHost.codeExtra] at h
        simp only [hblockTP, hblockSave, HBlock.forgetL, codeTP2, PoolHost.codeExtra]
        omega
      | pair q =>
        have h := q.pair_tp_relation
        simp only [hblockTP, hblockSave, HBlock.forgetL, codeTP2, PoolHost.codeExtra, PoolHost.blockExtra]
        omega
    simp only [hcodeTP, hsave, hforget_cons, codeTP2_append7, PoolHost.codeExtra_append]
    omega

theorem hrecs_relation {n} (code : HCode n) (hg : ∀ b ∈ code, HBlockGeo b) :
    hrecs code + hrsave code = recordsP2 bank15 (hforget code) := by
  induction code with
  | nil => rfl
  | cons b code ih =>
    have ih' := ih (fun d hd => hg d (by simp [hd]))
    have hb : hblockRec b + hblockRSave b = recordsP2 bank15 b.forgetL := by
      have hgb := hg b (by simp)
      cases b with
      | blk b =>
        have h := grecs_relation (b :: []) (fun d hd => by simp at hd; subst hd; exact hgb)
        simp only [grecs, grsave, fforget, List.map_cons, List.map_nil, recordsP2] at h
        simp only [hblockRec, hblockRSave, HBlock.forgetL, recordsP2]
        omega
      | pair q =>
        have h := q.pair_records_relation
        simp only [hblockRec, hblockRSave, HBlock.forgetL, recordsP2]
        omega
    simp only [hrecs, hrsave, hforget_cons, recordsP2_append7]
    omega

theorem hprog_slots {n} (code : HCode n) (hg : ∀ b ∈ code, HBlockGeo b) (start : Nat) :
    (hprog code start).gateSlots ≤ codeSP2 bank15 (hforget code) + hslack code := by
  induction code generalizing start with
  | nil => simp [hprog, hrecs, hslack, Straight.gateSlots, codeSP2]
  | cons b code ih =>
    have ih' := ih (fun d hd => hg d (by simp [hd])) (start + hblockRec b)
    have hb : (hblockProg b start).gateSlots ≤ codeSP2 bank15 b.forgetL + hblockSlack b := by
      have hgb := hg b (by simp)
      cases b with
      | blk b =>
        have h := gprog_slots (b :: []) (fun d hd => by simp at hd; subst hd; exact hgb) start
        rw [gprog, castFinish_gateSlots, Straight.gateSlots_append] at h
        simp only [gprog, Straight.gateSlots, fforget, List.map_cons, List.map_nil, codeSP2, gslack] at h
        simp only [HBlock.forgetL, codeSP2, hblockSlack]
        change (gblockProg b start).gateSlots ≤ _
        omega
      | pair q =>
        have h := q.pair_slots hgb start
        simp only [HBlock.forgetL, codeSP2, hblockSlack]
        change (q.pairProgram start).gateSlots ≤ _
        omega
    rw [hprog, castFinish_gateSlots, Straight.gateSlots_append]
    simp only [hforget_cons, codeSP2_append7, hslack]
    omega

theorem hprog_wellFormed {n} (code : HCode n) (hg : ∀ b ∈ code, HBlockGeo b)
    (hp : ∀ p, WInstr.literal p ∈ erase2 (hforget code) → GatePhysical p) (start : Nat) :
    (hprog code start).WellFormed := by
  induction code generalizing start with
  | nil => trivial
  | cons b code ih =>
    rw [hprog, castFinish_wellFormed]
    have hpb : ∀ p, WInstr.literal p ∈ erase2 b.forgetL → GatePhysical p := fun p hm =>
      hp p (by rw [hforget_cons, erase2_append]; exact List.mem_append_left _ hm)
    apply straight_append_wellFormed
    · cases b with
      | blk b =>
        exact gblock_wellFormed b (hg (HBlock.blk b) (by simp))
          (fun p hm => hpb p (by simpa [HBlock.forgetL, erase2] using hm)) start
      | pair q =>
        change (q.pairProgram start).WellFormed
        exact q.pair_wellFormed (hg (HBlock.pair q) (by simp))
          (fun p hm => hpb p (by simpa [HBlock.forgetL, erase2, Block2.code] using hm)) start
    · exact ih (fun d hd => hg d (by simp [hd]))
        (fun p hm => hp p (by rw [hforget_cons, erase2_append]; exact List.mem_append_right _ hm)) _

theorem hprog_residue {n} (code : HCode n) (start : Nat) : AndGadget.residue (hprog code start) = 0 := by
  induction code generalizing start with
  | nil => simp [hprog, hrecs]
  | cons b code ih =>
    have hb : AndGadget.residue (hblockProg b start) = 0 := by
      cases b with
      | blk b =>
        have h := gprog_residue (b :: []) start
        simpa [gprog, AndGadget.residue_cast, AndGadget.residue_append] using h
      | pair q => exact q.pair_residue start
    simp [hprog, AndGadget.residue_cast, AndGadget.residue_append, hb, ih]

/-! Moving between a fused pair and its two standard units. -/

theorem hforget_pair {n} (pre post : FCode2 n) (q : UnitPair7 n) :
    hforget (pre.map HBlock.blk ++ HBlock.pair q :: post.map HBlock.blk) =
      fforget (pre ++ FBlock2.std (.unit q.u₁) :: FBlock2.std (.unit q.u₂) :: post) := by
  rw [hforget_append, hforget_cons, hforget_blk, hforget_blk]
  simp [fforget, FBlock2.forget, HBlock.forgetL]

theorem hclean_blk {n} (read : ConstantBit n → Bool) (a : Nat) (c : FCode2 n) (st : ECDSAAdd.State)
    (h : GCodeClean read a c st) : HCodeClean read a (c.map HBlock.blk) st := by
  induction c generalizing st with
  | nil => trivial
  | cons b c ih =>
    refine ⟨h.1, fun m hm => ?_⟩
    rw [show (HBlock.blk b).forgetL = b.forget :: [] from rfl, WideBank8.Fast16.reference2_single] at hm ⊢
    exact ih _ (h.2 m hm)

theorem hclean_pair {n} (read : ConstantBit n → Bool) (a : Nat) (pre post : FCode2 n) (q : UnitPair7 n)
    (st : ECDSAAdd.State)
    (h : GCodeClean read a (pre ++ FBlock2.std (.unit q.u₁) :: FBlock2.std (.unit q.u₂) :: post) st) :
    HCodeClean read a (pre.map HBlock.blk ++ HBlock.pair q :: post.map HBlock.blk) st := by
  induction pre generalizing st with
  | nil =>
    have hfl : (HBlock.pair q).forgetL = Block2.unit q.u₁ :: Block2.unit q.u₂ :: [] := rfl
    refine ⟨h.1.1, fun m hm => ?_⟩
    rw [hfl, reference2_cons, WideBank8.Fast16.reference2_single, ECDSAAdd.measurementCount_append] at hm
    rw [hfl]
    set k := ECDSAAdd.measurementCount (blockReference2 read a (.unit q.u₁)) with hk
    have hlen : (m.take k).length = k := by rw [List.length_take]; omega
    have h1 := h.2 (m.take k) hlen
    have h2 := h1.2 (m.drop k) (by
      rw [List.length_drop]
      show m.length - k = ECDSAAdd.measurementCount (blockReference2 read a (.unit q.u₂))
      omega)
    rw [reference2_cons, WideBank8.Fast16.reference2_single, ← List.take_append_drop k m,
      run_append_records _ _ _ _ st hlen]
    exact hclean_blk read a post _ h2
  | cons x pre ih =>
    refine ⟨h.1, fun m hm => ?_⟩
    rw [show (HBlock.blk x).forgetL = x.forget :: [] from rfl, WideBank8.Fast16.reference2_single] at hm ⊢
    exact ih _ (h.2 m hm)

theorem hsave_pair {n} (pre post : FCode2 n) (q : UnitPair7 n) :
    hsave (pre.map HBlock.blk ++ HBlock.pair q :: post.map HBlock.blk) =
      gsave (pre ++ FBlock2.std (.unit q.u₁) :: FBlock2.std (.unit q.u₂) :: post) + UnitPair7.pairSave := by
  have hp : ∀ c : FCode2 n, hsave (c.map HBlock.blk) = gsave c := by
    intro c; induction c with
    | nil => rfl
    | cons b c ih => simp only [List.map_cons, hsave, gsave, hblockSave, ih]
  induction pre with
  | nil => simp only [List.map_nil, List.nil_append, hsave, gsave, hblockSave, gblockSave, hp]; omega
  | cons x pre ih => simp only [List.map_cons, List.cons_append, hsave, gsave, hblockSave]; omega

theorem hrsave_pair {n} (pre post : FCode2 n) (q : UnitPair7 n) :
    hrsave (pre.map HBlock.blk ++ HBlock.pair q :: post.map HBlock.blk) =
      grsave (pre ++ FBlock2.std (.unit q.u₁) :: FBlock2.std (.unit q.u₂) :: post) + q.pairRSave := by
  have hp : ∀ c : FCode2 n, hrsave (c.map HBlock.blk) = grsave c := by
    intro c; induction c with
    | nil => rfl
    | cons b c ih => simp only [List.map_cons, hrsave, grsave, hblockRSave, ih]
  induction pre with
  | nil => simp only [List.map_nil, List.nil_append, hrsave, grsave, hblockRSave, gblockRSave, hp]; omega
  | cons x pre ih => simp only [List.map_cons, List.cons_append, hrsave, grsave, hblockRSave]; omega

theorem hslack_pair {n} (pre post : FCode2 n) (q : UnitPair7 n) :
    hslack (pre.map HBlock.blk ++ HBlock.pair q :: post.map HBlock.blk) =
      gslack (pre ++ FBlock2.std (.unit q.u₁) :: FBlock2.std (.unit q.u₂) :: post) := by
  have hp : ∀ c : FCode2 n, hslack (c.map HBlock.blk) = gslack c := by
    intro c; induction c with
    | nil => rfl
    | cons b c ih => simp only [List.map_cons, hslack, gslack, hblockSlack, ih]
  induction pre with
  | nil => simp only [List.map_nil, List.nil_append, hslack, gslack, hblockSlack, gblockSlack, hp]; omega
  | cons x pre ih => simp only [List.map_cons, List.cons_append, hslack, gslack, hblockSlack]; omega


def HNoHost7 {n} : HBlock n → Prop
  | .blk b => GNoHost7 b
  | .pair _ => True

theorem hblock_support (b : HBlock 32768) (hg : HBlockGeo b)
    (hlit : ∀ p, WInstr.literal p ∈ erase2 b.forgetL → ∀ w ∈ ECDSAAdd.wires p,
      w = hostWire ∨ w = hostWire2 ∨ w = hostWire3 ∨
      w = PoolHost.hostWire4 ∨ w = PoolHost.hostWire5 ∨ w = PoolHost.hostWire6 ∨ w = PoolHost.hostWire7 ∨
      w ∈ PoolHost.newSourceH7)
    (hstrict : ∀ p, WInstr.literal p ∈ erase2 b.forgetL →
      (hostWire ∈ ECDSAAdd.wires p ∨ hostWire2 ∈ ECDSAAdd.wires p ∨ hostWire3 ∈ ECDSAAdd.wires p ∨
       PoolHost.hostWire4 ∈ ECDSAAdd.wires p ∨ PoolHost.hostWire5 ∈ ECDSAAdd.wires p ∨
       PoolHost.hostWire6 ∈ ECDSAAdd.wires p ∨ PoolHost.hostWire7 ∈ ECDSAAdd.wires p) →
      ∃ c, b = .blk (.std (.plain c)))
    (hctl : ∀ c, b = .blk (.std (.plain c)) →
      hostWire2 ∈ ECDSAAdd.wires (litProg c) → hostCtl ∉ ECDSAAdd.wires (litProg c))
    (hctl3 : ∀ c, b = .blk (.std (.plain c)) →
      hostWire3 ∈ ECDSAAdd.wires (litProg c) → hostCtl3 ∉ ECDSAAdd.wires (litProg c))
    (hctl4 : ∀ c, b = .blk (.std (.plain c)) →
      (14877 ∈ ECDSAAdd.wires (litProg c) ∨ 14876 ∈ ECDSAAdd.wires (litProg c) ∨
        14875 ∈ ECDSAAdd.wires (litProg c) ∨ 14874 ∈ ECDSAAdd.wires (litProg c)) →
      14111 ∉ ECDSAAdd.wires (litProg c) ∧ 19816 ∉ ECDSAAdd.wires (litProg c) ∧
      838 ∉ ECDSAAdd.wires (litProg c) ∧ 14112 ∉ ECDSAAdd.wires (litProg c) ∧
      19815 ∉ ECDSAAdd.wires (litProg c) ∧ 19814 ∉ ECDSAAdd.wires (litProg c))
    (hlook : ∀ c ps, WInstr.lookup c ps ∈ erase2 b.forgetL →
      (∀ q ∈ c, q ∈ PoolHost.newSourceH7) ∧ portTargets ps ⊆ PoolHost.newSourceH7)
    (hgarb : HNoHost7 b) (start : Nat) :
    ChallengeMigration.straightWires (hblockProg b start) ⊆ PoolHost.newSourceH7 := by
  cases b with
  | blk b =>
    have hm : ∀ i, i ∈ b.forget.code → i ∈ erase2 (HBlock.blk b).forgetL := fun i hi => by
      simpa [HBlock.forgetL, erase2] using hi
    exact gblock_support b hg (fun p hp => hlit p (hm _ hp))
      (fun p hp hh => by
        obtain ⟨c, hc⟩ := hstrict p (hm _ hp) hh
        exact ⟨c, HBlock.blk.inj hc⟩)
      (fun c hc => hctl c (congrArg HBlock.blk hc)) (fun c hc => hctl3 c (congrArg HBlock.blk hc))
      (fun c hc => hctl4 c (congrArg HBlock.blk hc))
      (fun c ps hp => hlook c ps (hm _ hp)) hgarb start
  | pair q =>
    have hm : ∀ i, i ∈ q.u₁.code ++ q.u₂.code → i ∈ erase2 (HBlock.pair q).forgetL := fun i hi => by
      simpa [HBlock.forgetL, erase2, Block2.code] using hi
    refine q.pair_support_new hg ?_ (fun c ps hp => hlook c ps (hm _ hp)) start
    intro p hp w hw
    rcases hlit p (hm _ hp) w hw with e | e | e | e | e | e | e | e
    · obtain ⟨c, hc⟩ := hstrict p (hm _ hp) (Or.inl (e ▸ hw)); cases hc
    · obtain ⟨c, hc⟩ := hstrict p (hm _ hp) (Or.inr (Or.inl (e ▸ hw))); cases hc
    · obtain ⟨c, hc⟩ := hstrict p (hm _ hp) (Or.inr (Or.inr (Or.inl (e ▸ hw)))); cases hc
    · obtain ⟨c, hc⟩ := hstrict p (hm _ hp) (Or.inr (Or.inr (Or.inr (Or.inl (e ▸ hw))))); cases hc
    · obtain ⟨c, hc⟩ := hstrict p (hm _ hp) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (e ▸ hw)))))); cases hc
    · obtain ⟨c, hc⟩ := hstrict p (hm _ hp) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (e ▸ hw))))))); cases hc
    · obtain ⟨c, hc⟩ := hstrict p (hm _ hp) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (e ▸ hw))))))); cases hc
    · exact List.mem_toFinset.mpr e

theorem hprog_support (code : HCode 32768) (hg : ∀ b ∈ code, HBlockGeo b)
    (hlit : ∀ p, WInstr.literal p ∈ erase2 (hforget code) → ∀ w ∈ ECDSAAdd.wires p,
      w = hostWire ∨ w = hostWire2 ∨ w = hostWire3 ∨
      w = PoolHost.hostWire4 ∨ w = PoolHost.hostWire5 ∨ w = PoolHost.hostWire6 ∨ w = PoolHost.hostWire7 ∨
      w ∈ PoolHost.newSourceH7)
    (hstrict : ∀ b ∈ code, ∀ p, WInstr.literal p ∈ erase2 b.forgetL →
      (hostWire ∈ ECDSAAdd.wires p ∨ hostWire2 ∈ ECDSAAdd.wires p ∨ hostWire3 ∈ ECDSAAdd.wires p ∨
       PoolHost.hostWire4 ∈ ECDSAAdd.wires p ∨ PoolHost.hostWire5 ∈ ECDSAAdd.wires p ∨
       PoolHost.hostWire6 ∈ ECDSAAdd.wires p ∨ PoolHost.hostWire7 ∈ ECDSAAdd.wires p) →
      ∃ c, b = .blk (.std (.plain c)))
    (hctl : ∀ b ∈ code, ∀ c, b = .blk (.std (.plain c)) →
      hostWire2 ∈ ECDSAAdd.wires (litProg c) → hostCtl ∉ ECDSAAdd.wires (litProg c))
    (hctl3 : ∀ b ∈ code, ∀ c, b = .blk (.std (.plain c)) →
      hostWire3 ∈ ECDSAAdd.wires (litProg c) → hostCtl3 ∉ ECDSAAdd.wires (litProg c))
    (hctl4 : ∀ b ∈ code, ∀ c, b = .blk (.std (.plain c)) →
      (14877 ∈ ECDSAAdd.wires (litProg c) ∨ 14876 ∈ ECDSAAdd.wires (litProg c) ∨
        14875 ∈ ECDSAAdd.wires (litProg c) ∨ 14874 ∈ ECDSAAdd.wires (litProg c)) →
      14111 ∉ ECDSAAdd.wires (litProg c) ∧ 19816 ∉ ECDSAAdd.wires (litProg c) ∧
      838 ∉ ECDSAAdd.wires (litProg c) ∧ 14112 ∉ ECDSAAdd.wires (litProg c) ∧
      19815 ∉ ECDSAAdd.wires (litProg c) ∧ 19814 ∉ ECDSAAdd.wires (litProg c))
    (hlook : ∀ c ps, WInstr.lookup c ps ∈ erase2 (hforget code) →
      (∀ q ∈ c, q ∈ PoolHost.newSourceH7) ∧ portTargets ps ⊆ PoolHost.newSourceH7)
    (hgarb : ∀ b ∈ code, HNoHost7 b)
    (start : Nat) : ChallengeMigration.straightWires (hprog code start) ⊆ PoolHost.newSourceH7 := by
  induction code generalizing start with
  | nil => simp [hprog, hrecs, ChallengeMigration.straightWires]
  | cons b code ih =>
    rw [hprog, support_cast, straightWires_append]
    exact List.append_subset.mpr ⟨hblock_support b (hg b (by simp))
      (fun p hm => hlit p (by rw [hforget_cons, erase2_append]; exact List.mem_append_left _ hm))
      (hstrict b (by simp)) (hctl b (by simp)) (hctl3 b (by simp)) (hctl4 b (by simp))
      (fun c ps hm => hlook c ps (by rw [hforget_cons, erase2_append]; exact List.mem_append_left _ hm))
      (hgarb b (by simp)) start,
      ih (fun d hd => hg d (by simp [hd]))
        (fun p hm => hlit p (by rw [hforget_cons, erase2_append]; exact List.mem_append_right _ hm))
        (fun d hd => hstrict d (by simp [hd])) (fun d hd => hctl d (by simp [hd]))
        (fun d hd => hctl3 d (by simp [hd])) (fun d hd => hctl4 d (by simp [hd]))
        (fun c ps hm => hlook c ps (by rw [hforget_cons, erase2_append]; exact List.mem_append_right _ hm))
        (fun d hd => hgarb d (by simp [hd])) _⟩

end
end ShorECDLP.Entrant.WEXFast

/-! ### The narrow body with fused fast sites -/

namespace ShorECDLP.Entrant.WEXFast.W15G
open Quantum Challenge AndGadget WEXCredit Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup WEXFast
open ShorECDLP.Entrant.Schedule33.Flexible ShorECDLP.Entrant.PathShare
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

theorem gsave_append (x y : FCode2 32768) : gsave (x ++ y) = gsave x + gsave y := by
  induction x with
  | nil => simp [gsave]
  | cons b xs ih => simp [gsave, ih, Nat.add_assoc]
theorem grsave_append (x y : FCode2 32768) : grsave (x ++ y) = grsave x + grsave y := by
  induction x with
  | nil => simp [grsave]
  | cons b xs ih => simp [grsave, ih, Nat.add_assoc]
theorem gsave_std (code : Code2 32768) : gsave (code.map FBlock2.std) = 0 := by
  induction code with
  | nil => rfl
  | cons b code ih => simp [gsave, gblockSave, ih]
theorem grsave_std (code : Code2 32768) : grsave (code.map FBlock2.std) = 0 := by
  induction code with
  | nil => rfl
  | cons b code ih => simp [grsave, gblockRSave, ih]

theorem rowCF_gsave : gsave rowCF = 39680 := by
  have h := tripleF.swapNet_toff tripleF_geometry
  rw [show tripleF.site = tripleSite from rfl, tripleSite_length] at h
  have h1 := site2F.swapNet_toff site2F_geometry
  rw [show site2F.site.ports = site2Ports probeRows from rfl, site2Ports_length] at h1
  rw [rowCF, gsave_append, gsave_append, gsave_std, gsave_std]
  simp only [fgeneric3, gsave, gblockSave, h, h1]

theorem rowCF_grsave : grsave rowCF = 39680 := by
  rw [rowCF, grsave_append, grsave_append, grsave_std, grsave_std]
  simp only [fgeneric3, grsave, gblockRSave, tripleF_garb_length, site2F_garb_length]

/-! The corner fusion on the narrow row. -/

def corner7 : UnitPair7 32768 := ⟨WEXUnlookup.cornerUnit₁, WEXUnlookup.cornerUnit₂⟩

def rowH : HCode 32768 :=
  WideBank8.Row16.headF.map HBlock.blk ++ HBlock.pair corner7 :: WideBank8.Row16.tailF.map HBlock.blk

theorem rowCF_split : rowCF = WideBank8.Row16.headF ++
    FBlock2.std (.unit corner7.u₁) :: FBlock2.std (.unit corner7.u₂) :: WideBank8.Row16.tailF := by
  rw [rowCF]
  simp [WideBank8.Row16.headF, WideBank8.Row16.tailF, corner7, WEXUnlookup.rowPost3]

theorem mem_rowCF_of_head (x : FBlock2 32768) (h : x ∈ WideBank8.Row16.headF) : x ∈ rowCF := by
  rw [rowCF_split]; exact List.mem_append_left _ h

theorem mem_rowCF_of_tail (x : FBlock2 32768) (h : x ∈ WideBank8.Row16.tailF) : x ∈ rowCF := by
  rw [rowCF_split]
  exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))

theorem corner7₁_mem : FBlock2.std (.unit corner7.u₁) ∈ rowCF := by
  rw [rowCF_split]; exact List.mem_append_right _ (List.mem_cons.mpr (Or.inl rfl))

theorem corner7₂_mem : FBlock2.std (.unit corner7.u₂) ∈ rowCF := by
  rw [rowCF_split]
  exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl rfl)))

theorem corner7_geo : corner7.Geo :=
  ⟨rowCF_ggeo _ corner7₁_mem, rowCF_ggeo _ corner7₂_mem, rfl, rfl⟩

theorem rowH_blk_mem (x : FBlock2 32768) (h : HBlock.blk x ∈ rowH) : x ∈ rowCF := by
  rw [rowH, List.mem_append, List.mem_cons] at h
  rcases h with h | h | h
  · obtain ⟨y, hy, he⟩ := List.mem_map.mp h
    cases he
    exact mem_rowCF_of_head _ hy
  · cases h
  · obtain ⟨y, hy, he⟩ := List.mem_map.mp h
    cases he
    exact mem_rowCF_of_tail _ hy

theorem rowH_pair_mem (q : UnitPair7 32768) (h : HBlock.pair q ∈ rowH) : q = corner7 := by
  rw [rowH, List.mem_append, List.mem_cons] at h
  rcases h with h | h | h
  · obtain ⟨y, -, he⟩ := List.mem_map.mp h
    cases he
  · cases h; rfl
  · obtain ⟨y, -, he⟩ := List.mem_map.mp h
    cases he

theorem rowH_hgeo : ∀ b ∈ rowH, HBlockGeo b := by
  intro b hb
  cases b with
  | blk x => exact rowCF_ggeo x (rowH_blk_mem x hb)
  | pair q =>
    rw [rowH_pair_mem q hb]
    exact corner7_geo

theorem hforget_rowH : hforget rowH = WEXUnlookup.rowC := by
  rw [rowH, hforget_pair, ← rowCF_split, fforget_rowCF]

theorem rowH_hsave : hsave rowH = 40055 := by
  rw [rowH, hsave_pair, ← rowCF_split, rowCF_gsave, UnitPair7.pairSave, bank_tree_nodes]

theorem rowH_hrsave : hrsave rowH = 40062 := by
  rw [rowH, hrsave_pair, ← rowCF_split, rowCF_grsave]
  have hcr := (MeasuredClear.recordUnary_counts _ _ _
    (geo_lay2 bank15 bank15_ok (.unit corner7.u₁) corner7_geo.1).2 0).1
  rw [bank_tree_nodes] at hcr
  simp only [UnitPair7.pairRSave]
  omega

theorem gslack_le_fslack (c : FCode2 32768) : gslack c ≤ fslack c + 20 * c.length := by
  induction c with
  | nil => simp [gslack, fslack]
  | cons b c ih =>
    have hb : gblockSlack b ≤ fblockSlack b + 20 := by cases b <;> simp [gblockSlack, fblockSlack]
    simp only [gslack, fslack, List.length_cons]
    omega

theorem rowCF_len : rowCF.length = 19 := by
  simp [rowCF, WEXUnlookup.rowPre3, fgeneric3, WEXUnlookup.rowPost3]

theorem rowH_hslack : hslack rowH ≤ 167784162 := by
  rw [rowH, hslack_pair, ← rowCF_split]
  have h1 := gslack_le_fslack rowCF
  rw [ShorECDLP.Entrant.WEXFast.W15F.rowCF_slack, rowCF_len] at h1
  omega

theorem rowH_htp : hcodeTP rowH + 40055 = ccx2 WEXUnlookup.rowC + PoolHost.codeExtra WEXUnlookup.rowC := by
  have h := hcodeTP_relation rowH rowH_hgeo
  rw [rowH_hsave, hforget_rowH, W15C.codeTP2_15] at h
  exact h

theorem sub_arith (x : Nat) (h : x + 40062 = 1692440) : x = 1652378 := by omega

theorem rowH_hrecords : hrecs rowH = 1652378 := by
  have h := hrecs_relation rowH rowH_hgeo
  rw [rowH_hrsave, hforget_rowH, W15C.rowC_recordsP] at h
  exact sub_arith _ h

theorem rowH_hslots (start : Nat) : (hprog rowH start).gateSlots ≤
    codeSlots windowBits (normalizeW (erase2 WEXUnlookup.rowC)) + 418412326 := by
  have h := hprog_slots rowH rowH_hgeo start
  have hsp := ShorECDLP.Entrant.WEXFast.W15F.rowC_slotsP start
  have hsl := rowH_hslack
  rw [hforget_rowH] at h
  omega

theorem rowH_strict : ∀ b ∈ rowH, ∀ p, WInstr.literal p ∈ erase2 b.forgetL →
    (hostWire ∈ ECDSAAdd.wires p ∨ hostWire2 ∈ ECDSAAdd.wires p ∨ hostWire3 ∈ ECDSAAdd.wires p ∨
     PoolHost.hostWire4 ∈ ECDSAAdd.wires p ∨ PoolHost.hostWire5 ∈ ECDSAAdd.wires p ∨
     PoolHost.hostWire6 ∈ ECDSAAdd.wires p ∨ PoolHost.hostWire7 ∈ ECDSAAdd.wires p) →
    ∃ c, b = .blk (.std (.plain c)) := by
  have hno4 : ∀ u : UnitSite 32768, Block2.unit u ∈ WEXUnlookup.rowC →
      ∀ p, WInstr.literal p ∈ u.code →
      ¬ (PoolHost.hostWire4 ∈ ECDSAAdd.wires p ∨ PoolHost.hostWire5 ∈ ECDSAAdd.wires p ∨
         PoolHost.hostWire6 ∈ ECDSAAdd.wires p ∨ PoolHost.hostWire7 ∈ ECDSAAdd.wires p) := by
    intro u hu p hp h4
    have h := (PoolHost.rowC_unit_no4 u hu).1 p hp
    rcases h4 with h4 | h4 | h4 | h4
    · exact (h _ h4).1 rfl
    · exact (h _ h4).2.1 rfl
    · exact (h _ h4).2.2.1 rfl
    · exact (h _ h4).2.2.2 rfl
  have hmem_rowC : ∀ b ∈ rowH, ∀ d ∈ b.forgetL, d ∈ WEXUnlookup.rowC := by
    intro b hb d hd
    rw [← hforget_rowH]
    exact List.mem_flatMap.mpr ⟨b, hb, hd⟩
  intro b hb p hp hh
  rcases hh with h3 | h3 | h3 | h4
  · cases b with
    | blk x =>
      rw [show (HBlock.blk x).forgetL = x.forget :: [] from rfl, WideBank8.Fast16.erase2_single] at hp
      obtain ⟨c, hc⟩ := ShorECDLP.Entrant.WEXFast.W15F.rowCF_strict x (rowH_blk_mem x hb) p hp (Or.inl h3)
      exact ⟨c, by rw [hc]⟩
    | pair q =>
      have hq := rowH_pair_mem q hb; subst hq; exfalso
      rw [show (HBlock.pair corner7).forgetL = Block2.unit corner7.u₁ :: Block2.unit corner7.u₂ :: [] from rfl,
        erase2_cons, erase2_cons, erase2_nil, List.append_nil, List.mem_append] at hp
      rcases hp with hp | hp
      · obtain ⟨c, hc⟩ := ShorECDLP.Entrant.WEXFast.W15F.rowCF_strict _ corner7₁_mem p hp (Or.inl h3); cases hc
      · obtain ⟨c, hc⟩ := ShorECDLP.Entrant.WEXFast.W15F.rowCF_strict _ corner7₂_mem p hp (Or.inl h3); cases hc
  · cases b with
    | blk x =>
      rw [show (HBlock.blk x).forgetL = x.forget :: [] from rfl, WideBank8.Fast16.erase2_single] at hp
      obtain ⟨c, hc⟩ := ShorECDLP.Entrant.WEXFast.W15F.rowCF_strict x (rowH_blk_mem x hb) p hp (Or.inr (Or.inl h3))
      exact ⟨c, by rw [hc]⟩
    | pair q =>
      have hq := rowH_pair_mem q hb; subst hq; exfalso
      rw [show (HBlock.pair corner7).forgetL = Block2.unit corner7.u₁ :: Block2.unit corner7.u₂ :: [] from rfl,
        erase2_cons, erase2_cons, erase2_nil, List.append_nil, List.mem_append] at hp
      rcases hp with hp | hp
      · obtain ⟨c, hc⟩ := ShorECDLP.Entrant.WEXFast.W15F.rowCF_strict _ corner7₁_mem p hp (Or.inr (Or.inl h3)); cases hc
      · obtain ⟨c, hc⟩ := ShorECDLP.Entrant.WEXFast.W15F.rowCF_strict _ corner7₂_mem p hp (Or.inr (Or.inl h3)); cases hc
  · cases b with
    | blk x =>
      rw [show (HBlock.blk x).forgetL = x.forget :: [] from rfl, WideBank8.Fast16.erase2_single] at hp
      obtain ⟨c, hc⟩ := ShorECDLP.Entrant.WEXFast.W15F.rowCF_strict x (rowH_blk_mem x hb) p hp (Or.inr (Or.inr h3))
      exact ⟨c, by rw [hc]⟩
    | pair q =>
      have hq := rowH_pair_mem q hb; subst hq; exfalso
      rw [show (HBlock.pair corner7).forgetL = Block2.unit corner7.u₁ :: Block2.unit corner7.u₂ :: [] from rfl,
        erase2_cons, erase2_cons, erase2_nil, List.append_nil, List.mem_append] at hp
      rcases hp with hp | hp
      · obtain ⟨c, hc⟩ := ShorECDLP.Entrant.WEXFast.W15F.rowCF_strict _ corner7₁_mem p hp (Or.inr (Or.inr h3)); cases hc
      · obtain ⟨c, hc⟩ := ShorECDLP.Entrant.WEXFast.W15F.rowCF_strict _ corner7₂_mem p hp (Or.inr (Or.inr h3)); cases hc
  · cases b with
    | blk x =>
      cases x with
      | std d =>
        cases d with
        | plain c => exact ⟨c, rfl⟩
        | unit u =>
          exfalso
          have hu : Block2.unit u ∈ WEXUnlookup.rowC := hmem_rowC _ hb _ (by simp [HBlock.forgetL, FBlock2.forget])
          rw [show (HBlock.blk (.std (.unit u))).forgetL = Block2.unit u :: [] from rfl,
            WideBank8.Fast16.erase2_single] at hp
          exact hno4 u hu p hp h4
      | fast f =>
        exfalso
        have hu : Block2.unit (siteUnit f.site) ∈ WEXUnlookup.rowC :=
          hmem_rowC _ hb _ (by simp [HBlock.forgetL, FBlock2.forget])
        rw [show (HBlock.blk (.fast f)).forgetL = Block2.unit (siteUnit f.site) :: [] from rfl,
          WideBank8.Fast16.erase2_single] at hp
        exact hno4 _ hu p hp h4
      | fast1 f =>
        exfalso
        have hu : Block2.unit (siteUnit f.site) ∈ WEXUnlookup.rowC :=
          hmem_rowC _ hb _ (by simp [HBlock.forgetL, FBlock2.forget])
        rw [show (HBlock.blk (.fast1 f)).forgetL = Block2.unit (siteUnit f.site) :: [] from rfl,
          WideBank8.Fast16.erase2_single] at hp
        exact hno4 _ hu p hp h4
    | pair q =>
      exfalso
      have hu1 : Block2.unit q.u₁ ∈ WEXUnlookup.rowC := hmem_rowC _ hb _ (by simp [HBlock.forgetL])
      have hu2 : Block2.unit q.u₂ ∈ WEXUnlookup.rowC := hmem_rowC _ hb _ (by simp [HBlock.forgetL])
      rw [show (HBlock.pair q).forgetL = Block2.unit q.u₁ :: Block2.unit q.u₂ :: [] from rfl,
        erase2_cons, erase2_cons, erase2_nil, List.append_nil, List.mem_append] at hp
      rcases hp with hp | hp
      · exact hno4 q.u₁ hu1 p hp h4
      · exact hno4 q.u₂ hu2 p hp h4

theorem rowH_ctl : ∀ b ∈ rowH, ∀ c, b = .blk (.std (.plain c)) →
    hostWire2 ∈ ECDSAAdd.wires (litProg c) → hostCtl ∉ ECDSAAdd.wires (litProg c) := by
  intro b hb c he
  subst he
  exact ShorECDLP.Entrant.WEXFast.W15F.rowCF_ctl _ (rowH_blk_mem _ hb) c rfl

theorem rowH_ctl3 : ∀ b ∈ rowH, ∀ c, b = .blk (.std (.plain c)) →
    hostWire3 ∈ ECDSAAdd.wires (litProg c) → hostCtl3 ∉ ECDSAAdd.wires (litProg c) := by
  intro b hb c he
  subst he
  exact ShorECDLP.Entrant.WEXFast.W15F.rowCF_ctl3 _ (rowH_blk_mem _ hb) c rfl

theorem rowH_ctl4 : ∀ b ∈ rowH, ∀ c, b = .blk (.std (.plain c)) →
    (14877 ∈ ECDSAAdd.wires (litProg c) ∨ 14876 ∈ ECDSAAdd.wires (litProg c) ∨
      14875 ∈ ECDSAAdd.wires (litProg c) ∨ 14874 ∈ ECDSAAdd.wires (litProg c)) →
    14111 ∉ ECDSAAdd.wires (litProg c) ∧ 19816 ∉ ECDSAAdd.wires (litProg c) ∧
    838 ∉ ECDSAAdd.wires (litProg c) ∧ 14112 ∉ ECDSAAdd.wires (litProg c) ∧
    19815 ∉ ECDSAAdd.wires (litProg c) ∧ 19814 ∉ ECDSAAdd.wires (litProg c) := by
  intro b hb c he
  subst he
  have hc : Block2.plain c ∈ WEXUnlookup.rowC := by
    rw [← hforget_rowH]
    exact List.mem_flatMap.mpr ⟨_, hb, by simp [HBlock.forgetL, FBlock2.forget]⟩
  exact PoolHost.rowC_plain_ctl4 c hc

theorem rowH_nohost : ∀ b ∈ rowH, HNoHost7 b := by
  have ht4 : ∀ w ∈ tripleF.garb, w ≠ 14877 ∧ w ≠ 14876 ∧ w ≠ 14875 ∧ w ≠ 14874 := by decide
  have hs4 : ∀ w ∈ site2F.garb, w ≠ 14877 ∧ w ≠ 14876 ∧ w ≠ 14875 ∧ w ≠ 14874 := by decide
  intro b hb
  cases b with
  | blk x =>
    have hx := rowH_blk_mem x hb
    have h0 := ShorECDLP.Entrant.WEXFast.W15F.rowCF_nohost x hx
    cases x with
    | std _ => trivial
    | fast f =>
      have hf := fast_mem_rowCF f hx
      intro w hw
      have h3 := h0 w hw
      have h4 := ht4 w (hf ▸ hw)
      exact ⟨h3.1, h3.2.1, h3.2.2, h4.1, h4.2.1, h4.2.2.1, h4.2.2.2⟩
    | fast1 f =>
      have hf := fast1_mem_rowCF f hx
      intro w hw
      have h3 := h0 w hw
      have h4 := hs4 w (hf ▸ hw)
      exact ⟨h3.1, h3.2.1, h3.2.2, h4.1, h4.2.1, h4.2.2.1, h4.2.2.2⟩
  | pair q => trivial

attribute [local irreducible] gprog gblockProg hprog hblockProg blockProgP2 clearP WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  WEX.literalToffolis WEX.normalizeW ccx2 gcodeTP hcodeTP Nat.add Nat.mul

def addFixedCG (start : Nat) : Straight 32768 start (start+1652378) :=
  castFinish (congrArg (fun m => start+m) rowH_hrecords) (hprog rowH start)

theorem addFixedCG_run (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((addFixedCG start).instantiate read history).run = (hsrc read rowH).run := by
  rw [addFixedCG, castFinish_instantiate, hprog_run]

theorem addFixedCG_tCount (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((addFixedCG start).instantiate read history).tCount = 7 * hcodeTP rowH := by
  rw [addFixedCG, castFinish_instantiate, hprog_tCount read rowH rowH_hgeo]

theorem addFixedCG_slots (start : Nat) : (addFixedCG start).gateSlots ≤
    codeSlots windowBits (normalizeW (erase2 WEXUnlookup.rowC)) + 418412326 := by
  rw [addFixedCG, castFinish_gateSlots]
  exact rowH_hslots start

theorem addFixedCG_wellFormed (start : Nat) : (addFixedCG start).WellFormed := by
  rw [addFixedCG, castFinish_wellFormed]
  exact hprog_wellFormed rowH rowH_hgeo (by rw [hforget_rowH]; exact WEXUnlookup.rowC_physical) start

theorem addFixedCG_residue (start : Nat) : residue (addFixedCG start) = 0 := by
  rw [addFixedCG, residue_cast]
  exact hprog_residue rowH start

theorem addFixedCG_credit (start : Nat) : ProgramCredit (addFixedCG start) (hcodeTP rowH) := by
  have hz := addFixedCG_residue start
  refine ⟨hz, ?_⟩
  have he := exact_t (addFixedCG start) hz (fun _ => false) (fun _ => false)
  have ht := addFixedCG_tCount (fun _ => false) start (fun _ => false)
  omega

theorem addFixedCG_support (start : Nat) :
    ChallengeMigration.straightWires (addFixedCG start) ⊆ PoolHost.newSourceH7 := by
  rw [addFixedCG, support_cast]
  exact hprog_support rowH rowH_hgeo (by rw [hforget_rowH]; exact PoolHost.rowC_lit_relaxed7)
    rowH_strict rowH_ctl rowH_ctl3 rowH_ctl4 (by rw [hforget_rowH]; exact PoolHost.rowC_look_newH7)
    rowH_nohost start

def rowSourceCG (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  hsrc (readConstant coeffs Q) rowH

theorem gclean_of_fclean {n} (read : ConstantBit n → Bool) (a : Nat) (c : FCode2 n) (st : ECDSAAdd.State)
    (hf : FCodeClean read a c st) (h4 : PoolHost.CodeHost4_2 read a (fforget c) st) :
    GCodeClean read a c st := by
  induction c generalizing st with
  | nil => trivial
  | cons b c ih =>
    refine ⟨?_, fun m hm => ih _ (hf.2 m hm) (h4.2 m hm)⟩
    cases b with
    | std b => exact ⟨hf.1.1, hf.1.2, h4.1⟩
    | fast f => exact hf.1
    | fast1 f => exact hf.1

theorem rowSourceCG_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) :
    CoherentlyImplementsOn (rowSourceCG coeffs Q) (Finsupp.lmapDomain ℂ ℂ (rowPointState coeffs Q)) LiveReady := by
  have h := hprog_coherent (readConstant coeffs Q) rowH rowH_hgeo liveReady (rowPointState coeffs Q)
    (fun s hs => by rw [hforget_rowH]; exact (WEXUnlookup.rowC_safe_run coeffs Q hQ hn _ s hs).1)
    (fun s hs => by
      refine hclean_pair _ _ _ _ corner7 _ ?_
      rw [← rowCF_split]
      exact gclean_of_fclean _ _ rowCF _ (rowCF_clean coeffs Q hQ hn _ s hs)
        (by rw [fforget_rowCF]; exact PoolHost.rowC_host4 coeffs Q hQ hn _ s hs))
    (fun s hs m => by rw [hforget_rowH]; exact WEXUnlookup.rowC_run_any _ coeffs Q hQ hn s hs m) 0 Fin.elim0
  obtain ⟨cs, aligned, mass⟩ := h
  refine ⟨cs, ?_, mass⟩
  rw [hprog_run] at aligned
  exact aligned.imp (fun b c hb s hs => hb s ⟨hs.1.2.2, hs.1⟩)

def fastMiddleSource (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  (fastSignSource.seq (rowSourceCG coeffs Q)).seq fastSignSource

theorem fastMiddle_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) :
    CoherentlyImplementsOn (fastMiddleSource coeffs Q) (Finsupp.lmapDomain ℂ ℂ (middleState coeffs Q)) LiveReady := by
  have first := composeCoherent fastSign_coherent (rowSourceCG_coherent coeffs Q hQ hn)
    (fun s hs => live_write _ s hs)
  exact composeCoherent (f := fun s => rowPointState coeffs Q (signPointState s)) (g := signPointState)
    first fastSign_coherent (fun s hs => live_write _ _ (live_write _ s hs))

def fastBodySource (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  (prefixSource.seq (fastMiddleSource coeffs Q)).seq suffixSource

theorem fastBodySource_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) :
    CoherentlyImplementsOn (fastBodySource coeffs Q) (Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)) Ready := by
  have h := composeCoherent WEXUnlookup.prefix_coherent (fastMiddle_coherent coeffs Q hQ hn)
    (fun s hs => ⟨windowPrepare_live _ (rootFlip_live s hs.1), prefix_hot s hs.2⟩)
  exact composeCoherent (f := fun s => middleState coeffs Q (prefixState s)) (g := suffixState)
    h WEX.suffix_coherent (fun _ _ => True.intro)

def fastBodyProgram (start : Nat) : Straight 32768 start (start+1652890) :=
  castFinish (by omega)
    (((((prefixProgram start).append (nFastProgram start)).append (addFixedCG (start+256))).append
      (nFastProgram (start+256+1652378))).append (suffixProgram (start+256+1652378+256)))

attribute [local irreducible] fastBodyProgram addFixedCG

theorem fastBodyProgram_run (start : Nat) (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (history : Fin start → Bool) :
    ((fastBodyProgram start).instantiate (readConstant coeffs Q) history).run = (fastBodySource coeffs Q).run := by
  have hr : ((fastBodyProgram start).instantiate (readConstant coeffs Q) history).run =
      ((prefixSource.seq ((fastSignSource.seq (hsrc (readConstant coeffs Q) rowH)).seq
        fastSignSource)).seq suffixSource).run := by
    rw [fastBodyProgram, castFinish_instantiate]
    exact five_run (readConstant coeffs Q) _ _ _ _ _ prefixSource fastSignSource
      (hsrc (readConstant coeffs Q) rowH) fastSignSource suffixSource
      (prefixProgram_run _ _) (nFastProgram_run _ _) (addFixedCG_run _ _)
      (nFastProgram_run _ _) (suffixProgram_run _ _) history
  have he : fastBodySource coeffs Q =
      ((prefixSource.seq ((fastSignSource.seq (hsrc (readConstant coeffs Q) rowH)).seq
        fastSignSource)).seq suffixSource) := by
    delta fastBodySource fastMiddleSource rowSourceCG
    rfl
  exact hr.trans (congrArg AdaptiveCircuit.run he.symm)

theorem fastBodyProgram_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((fastBodyProgram start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)) Ready := by
  obtain ⟨cs, aligned, mass⟩ := fastBodySource_coherent coeffs Q hQ hn
  refine ⟨cs, ?_, mass⟩
  rw [fastBodyProgram_run]
  exact aligned

theorem fastBodyProgram_credit (start : Nat) : ProgramCredit (fastBodyProgram start)
    (2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) +
      hcodeTP rowH) := by
  let a := ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)
  have hl : ProgramCredit (nFastProgram start) a := WEX.nFastProgram_credit start
  have hr : ProgramCredit (nFastProgram (start+256+1652378)) a := WEX.nFastProgram_credit _
  rw [fastBodyProgram]
  apply credit_cast
  exact five_credit a (hcodeTP rowH) (prefix_credit start) hl (addFixedCG_credit (start+256)) hr
    (suffix_credit (start+256+1652378+256))

theorem fastBodyProgram_wellFormed (start : Nat) : (fastBodyProgram start).WellFormed := by
  rw [fastBodyProgram, castFinish_wellFormed]
  apply straight_append_wellFormed
  · apply straight_append_wellFormed
    · apply straight_append_wellFormed
      · exact straight_append_wellFormed _ _ (prefixProgram_wellFormed start) (nFastProgram_wellFormed start)
      · exact addFixedCG_wellFormed _
    · exact nFastProgram_wellFormed _
  · exact suffixProgram_wellFormed _

theorem fastBodyProgram_support (start : Nat) :
    ChallengeMigration.straightWires (fastBodyProgram start) ⊆ PoolHost.newSourceH7 := by
  have hsub (l : List Wire) (hl : l ⊆ newSourceH)
      (h4 : ∀ w ∈ l, w ≠ 14877 ∧ w ≠ 14876 ∧ w ≠ 14875 ∧ w ≠ 14874) : l ⊆ PoolHost.newSourceH7 :=
    fun w hw => PoolHost.newSourceH7_of_newH w (hl hw) (h4 w hw).1 (h4 w hw).2.1 (h4 w hw).2.2.1 (h4 w hw).2.2.2
  have hp : ChallengeMigration.straightWires (prefixProgram start) ⊆ PoolHost.newSourceH7 := by
    rw [prefixProgram, straightWires_append, literalProgram_support, literalProgram_support]
    exact hsub _ (newSourceH_of_bounds _ (by decide +kernel)) (by decide +kernel)
  have hs (j : Nat) : ChallengeMigration.straightWires (suffixProgram j) ⊆ PoolHost.newSourceH7 := by
    rw [suffixProgram, straightWires_append, literalProgram_support, literalProgram_support]
    exact hsub _ (newSourceH_of_bounds _ (by decide +kernel)) (by decide +kernel)
  rw [fastBodyProgram, support_cast]
  simp only [straightWires_append, List.append_subset]
  exact ⟨⟨⟨⟨hp, TightSupport.nFast_newH7 _⟩, addFixedCG_support _⟩, TightSupport.nFast_newH7 _⟩, hs _⟩

attribute [local irreducible] WEX.literalSlotSum WEX.portTotal WEX.traversals in
theorem fastBodyProgram_slots_upper (start : Nat) : (fastBodyProgram start).gateSlots ≤ 2000000000 := by
  rw [fastBodyProgram, castFinish_gateSlots]
  simp only [Straight.gateSlots_append, nFastProgram_slots, prefixProgram, suffixProgram, literalProgram_slots]
  have ha := addFixedCG_slots (start+256)
  have len : (signedAddressCircuit 836 870 windowBits).length = 30 := by decide +kernel
  simp only [len, List.length_cons, List.length_nil]
  have hc := WEX.codeSlots_bound windowBits (normalizeW (erase2 WEXUnlookup.rowC))
  rw [literalSlotSum_normalize, portTotal_normalize, traversals_normalize] at hc
  have hl := WEX.clearReferenceRow_literal_slots_bound
  have hp := WEX.clearReferenceRow_portTotal
  have hm := WEXUnlookup.rowC_measures
  have sign := literal_slot_bound (n := 32768) (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)
  rw [ECDSAAdd.Baselines.normalize_slots] at sign
  have bound := fastWindowSign_slots
  have hwlen : windowBits.length = 15 := rfl
  rw [hwlen] at hc
  generalize codeSlots windowBits (normalizeW (erase2 WEXUnlookup.rowC)) = C at hc ha
  generalize (addFixedCG (start + 256)).gateSlots = A at ha ⊢
  generalize ECDSAAdd.Challenge.gateSlots fastWindowSignProgram = G at sign bound
  generalize Bridge.tmplSlots (literalT (n := 32768) (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)) = S
    at sign ⊢
  have h1 := hm.2.1
  have h2 := hm.2.2.1
  have h3 := hm.2.2.2.1
  omega

def compactProgram (start : Nat) : Straight 32768 start (start+1652890) :=
  relabelStraight PoolHost.piH7 (fastBodyProgram start)

theorem count_arith (s x y e : Nat) (h : s + y ≤ 2292120) (hr : x + 40055 = y + e) (he : e ≤ 6) :
    s + x ≤ 2252071 := by omega

theorem fastCount_upper : 2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) +
    hcodeTP rowH ≤ 2252071 := by
  exact count_arith _ _ _ _ Width15Corner.fastCount_upper rowH_htp PoolHost.rowC_codeExtra_le

end
end ShorECDLP.Entrant.WEXFast.W15G
end
