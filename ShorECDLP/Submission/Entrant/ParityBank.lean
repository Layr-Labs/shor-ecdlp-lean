import ShorECDLP.Submission.Entrant.MainA
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
