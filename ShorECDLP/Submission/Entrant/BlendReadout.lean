import ShorECDLP.Submission.Entrant.BlendCoverage
namespace ShorECDLP.Entrant.BlendReadout
open Quantum Challenge RoundedReadout NeighborReadout Readout56
noncomputable section
set_option Elab.async false
set_option exponentiation.threshold 300
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

theorem readWord_concat (history : List Bool) (low high : List Nat) (a b : Nat)
    (hl : readWord history low=some a) (hh : readWord history high=some b) :
    readWord history (low++high)=some (a+2^low.length*b) := by
  induction low generalizing a with
  | nil =>
    have ha : 0=a := by simpa only [readWord,Option.some.injEq] using hl
    subst a
    simpa using hh
  | cons i low ih =>
    cases hi : history[i]? with
    | none => simp [readWord,hi] at hl
    | some bit =>
      cases ht : readWord history low with
      | none => simp [readWord,hi,ht] at hl
      | some v =>
        have he : (if bit then 1 else 0)+2*v=a := by simpa [readWord,hi,ht] using hl
        have hr := ih v ht
        simp [readWord,hi,hr,List.length_cons,pow_succ,←he,Nat.mul_add,
          Nat.add_comm,Nat.add_left_comm,Nat.add_assoc,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc]



def lowerBits {start} (bits : Vector (Fin start) 261) : Vector (Fin start) 5 := bits.take 5

def upperBits {start} (bits : Vector (Fin start) 261) : Vector (Fin start) 256 := bits.drop 5

theorem split_positions {start} (bits : Vector (Fin start) 261) :
    ((lowerBits bits).map Fin.val).toList++((upperBits bits).map Fin.val).toList=
      (bits.map Fin.val).toList := by
  simp only [lowerBits,upperBits,Vector.toList_map,Vector.toList_take,Vector.toList_drop,
    ←List.map_append,List.take_append_drop]

theorem input_split {start} (bits : Vector (Fin start) 261) (history : Fin start→Bool) :
    inputValue bits history=inputValue (lowerBits bits) history+32*inputValue (upperBits bits) history := by
  have h:=readWord_concat (List.ofFn history)
    ((lowerBits bits).map Fin.val).toList ((upperBits bits).map Fin.val).toList _ _
    (input_read (lowerBits bits) history) (input_read (upperBits bits) history)
  rw [split_positions,input_read] at h
  simpa only [Option.some.injEq,Vector.length_toList] using h

theorem plus32 (l u : Nat) (hl : l<32) (hu : u<2^256) :
    l+32*((u+1)%2^256)=(l+32*u+32)%2^261 := by
  have hp : 2^261=32*2^256 := by norm_num
  by_cases h : u+1=2^256
  · rw [h,Nat.mod_self];simp only [Nat.mul_zero,Nat.add_zero]
    have he : l+32*u+32=l+2^261 := by omega
    rw [he,Nat.add_mod_right]
    exact (Nat.mod_eq_of_lt (by omega)).symm
  · have hh : u+1<2^256 := by omega
    rw [Nat.mod_eq_of_lt hh,Nat.mod_eq_of_lt (by omega)]
    omega

theorem minus32 (l u : Nat) (hl : l<32) (hu : u<2^256) :
    l+32*(2^256-1-((1+(2^256-1-u))%2^256))=(l+32*u+2^261-32)%2^261 := by
  have hp : 2^261=32*2^256 := by norm_num
  by_cases h : u=0
  · subst u
    have he : 1+(2^256-1-0)=2^256 := by omega
    rw [he,Nat.mod_self]
    simp only [Nat.sub_zero,Nat.mul_zero,Nat.add_zero]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · have hh : 1+(2^256-1-u)<2^256 := by omega
    rw [Nat.mod_eq_of_lt hh]
    have he : l+32*u+2^261-32=(l+32*(u-1))+2^261 := by omega
    rw [he,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
    omega

end
end ShorECDLP.Entrant.BlendReadout


namespace ShorECDLP.Entrant.BlendReadout
open Quantum Challenge RoundedReadout NeighborReadout Readout56
open Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
attribute [local irreducible] positiveWords negativeWords incrementStep complementStep
theorem suffix56_branch256 (n start : Nat) (bits : Vector (Fin start) 256)
    (read : ConstantBit n→Bool) (history : Fin start→Bool)
    (ψ : State) (hψ : SupportedOn CleanReadout ψ) (b : InstrumentBranch)
    (hb : b∈((suffix56 n start 256 bits).instantiate read history).run)
    (hn : b.kraus ψ≠0) :
    b.kraus ψ=ψ ∧
      (∀i : Fin 27, readWord (List.ofFn history++b.history)
        (sumPositions (start+2+i.val*512) 256).toList=
        some ((i.val+1+inputValue bits history)%2^256)) ∧
      (∀i : Fin 28, readWord (List.ofFn history++b.history)
        (sumPositions (start+2+13824+512+i.val*1024+512) 256).toList=
        some (2^256-1-((i.val+1+(2^256-1-inputValue bits history))%2^256))) := by
  unfold suffix56 at hb
  rw [castFinish_instantiate] at hb
  obtain ⟨h₁,a,u,ha,hu,he₁,rfl⟩:=straight_append_branch _ _ read history b hb
  have han : a.kraus ψ≠0 := by
    intro h;apply hn;simp only [InstrumentBranch.seq,LinearMap.comp_apply,h,map_zero]
  have hc:=constantStep_branch n start read history ψ hψ a ha han
  have hun : u.kraus ψ≠0 := by
    simpa only [InstrumentBranch.seq,LinearMap.comp_apply,hc.1] using hn
  have hcarr:=initial_carry bits history h₁ (he₁.trans (by rw [hc.2]))
  have hval:=initial_value bits history h₁ a.history he₁
  obtain ⟨h₂,p,v,hp,hv,he₂,rfl⟩:=straight_append_branch _ _ read h₁ u hu
  have hpn : p.kraus ψ≠0 := by
    intro h;apply hun;simp only [InstrumentBranch.seq,LinearMap.comp_apply,h,map_zero]
  have hpos:=positiveWords_branch n 27 (start+2) 256 (initialCursor bits)
    read h₁ hcarr ψ hψ p hp hpn
  have hvn : v.kraus ψ≠0 := by
    simpa only [InstrumentBranch.seq,LinearMap.comp_apply,hpos.1] using hun
  let q:=(initialCursor bits).lift (27*(2*256))
  have hqc : h₂ q.carry=true := (lift_carry (initialCursor bits) _ h₁ h₂ p.history he₂).trans hcarr
  have hqv : cursorValue q h₂=inputValue bits history :=
    (lift_value (initialCursor bits) _ h₁ h₂ p.history he₂).trans hval
  obtain ⟨h₃,c,t,hc',ht,he₃,rfl⟩:=straight_append_branch _ _ read h₂ v hv
  have hcn : c.kraus ψ≠0 := by
    intro h;apply hvn;simp only [InstrumentBranch.seq,LinearMap.comp_apply,h,map_zero]
  have hcomp:=complementStep_post n q read h₂ hqc ψ hψ c hc' hcn h₃ he₃
  have htn : t.kraus ψ≠0 := by
    simpa only [InstrumentBranch.seq,LinearMap.comp_apply,hcomp.1] using hvn
  have hneg:=negativeWords_branch n 28 (start+2+27*(2*256)+2*256) 256 q.next
    read h₃ hcomp.2.1 ψ hψ t ht htn
  have hfull₁ : List.ofFn history++(a.seq (p.seq (c.seq t))).history=
      List.ofFn h₁++(p.seq (c.seq t)).history := by
    rw [he₁];simp only [InstrumentBranch.seq,List.append_assoc]
  have hfull₂ : List.ofFn history++(a.seq (p.seq (c.seq t))).history=
      List.ofFn h₂++(c.seq t).history := by
    rw [hfull₁,he₂];simp only [InstrumentBranch.seq,List.append_assoc]
  have hfull₃ : List.ofFn history++(a.seq (p.seq (c.seq t))).history=
      List.ofFn h₃++t.history := by
    rw [hfull₂,he₃];simp only [InstrumentBranch.seq,List.append_assoc]
  refine ⟨by simp only [InstrumentBranch.seq,LinearMap.comp_apply,hc.1,hpos.1,hcomp.1,hneg.1],?_,?_⟩
  · intro i
    rw [hfull₂,readWord_append_left (List.ofFn h₂) (c.seq t).history _ (by
      intro j hj
      have hj':=sumPositions_bound (start+2+i.val*512) 256 j hj
      have hi:=i.isLt
      simp only [List.length_ofFn]
      omega),he₂]
    simpa only [hval] using hpos.2 i
  · intro i
    rw [hfull₃]
    simpa only [hcomp.2.2,hqv] using hneg.2 i



def liftBits {start width extra} (bits : Vector (Fin start) width) :
    Vector (Fin (start+extra)) width := bits.map (fun i=>⟨i.val,by omega⟩)

theorem liftBits_vals {start width extra} (bits : Vector (Fin start) width) :
    ((liftBits (extra:=extra) bits).map Fin.val).toList=(bits.map Fin.val).toList := by
  simp only [liftBits,Vector.map_map]
  rfl

theorem liftBits_value {start width extra} (bits : Vector (Fin start) width)
    (h : Fin start→Bool) (h' : Fin (start+extra)→Bool) (tail : List Bool)
    (he : List.ofFn h'=List.ofFn h++tail) :
    inputValue (liftBits (extra:=extra) bits) h'=inputValue bits h := by
  have hr:=input_read (liftBits (extra:=extra) bits) h'
  rw [liftBits_vals,he,readWord_append_left] at hr
  · rw [input_read] at hr
    exact (Option.some.inj hr).symm
  · intro i hi
    simp only [Vector.toList_map,List.mem_map] at hi
    obtain ⟨j,_,rfl⟩:=hi
    simpa only [List.length_ofFn] using j.isLt

def shiftPositions {start} (bits : Vector (Fin start) 208) (j : ℤ) : Vector Nat 208 :=
  if j=0 then bits.map Fin.val else if 0<j then
    sumPositions (start+2+(j.toNat-1)*416) 208
  else sumPositions (start+2+11232+416+((-j).toNat-1)*832+416) 208

theorem shiftPositions_bound {start} (bits : Vector (Fin start) 208) (j : ℤ)
    (hj : -28≤j ∧ j≤27) (v : Nat) (hv : v∈(shiftPositions bits j).toList) :
    v<start+34946 := by
  unfold shiftPositions at hv
  split_ifs at hv with hz hp
  · simp only [Vector.toList_map,List.mem_map] at hv
    obtain ⟨i,_,rfl⟩:=hv
    have h:=i.isLt
    omega
  · have hb:=sumPositions_bound (start+2+(j.toNat-1)*416) 208 v hv
    omega
  · have hb:=sumPositions_bound (start+2+11232+416+((-j).toNat-1)*832+416) 208 v hv
    omega

theorem shiftPositions_read (n start : Nat) (bits : Vector (Fin start) 208)
    (read : ConstantBit n→Bool) (history : Fin start→Bool)
    (ψ : State) (hψ : SupportedOn CleanReadout ψ) (b : InstrumentBranch)
    (hb : b∈((suffix56 n start 208 bits).instantiate read history).run)
    (hn : b.kraus ψ≠0) (j : ℤ) (hj : -28≤j ∧ j≤27) :
    readWord (List.ofFn history++b.history) (shiftPositions bits j).toList=
      some (neighborWord (inputValue bits history) j) := by
  have hs:=suffix56_branch n start bits read history ψ hψ b hb hn
  unfold shiftPositions
  split_ifs with hz hp
  · subst j
    rw [readWord_append_left]
    · rw [input_read]
      congr 1
      simpa only [Nat.zero_add,Int.natCast_zero,Nat.mod_eq_of_lt (input_lt bits history)] using
        (positive_word_mod (inputValue bits history) 0)
    · intro i hi
      simp only [Vector.toList_map,List.mem_map] at hi
      obtain ⟨k,_,rfl⟩:=hi
      simpa only [List.length_ofFn] using k.isLt
  · let i : Fin 27:=⟨j.toNat-1,by omega⟩
    have hi : (i.val+1 : ℤ)=j := by dsimp [i];omega
    rw [show start+2+(j.toNat-1)*416=start+2+i.val*416 from rfl,hs.2.1 i,positive_word_mod]
    congr 2
    exact congrArg (fun z : ℤ=>(((inputValue bits history : Nat) : ℤ)+z)%(2^208 : Nat)) hi
  · let i : Fin 28:=⟨(-j).toNat-1,by omega⟩
    have hi : -((i.val+1 : Nat) : ℤ)=j := by dsimp [i];omega
    rw [show start+2+11232+416+((-j).toNat-1)*832+416=start+2+11232+416+i.val*832+416 from rfl,
      hs.2.2 i,negative_word_mod _ _ (input_lt bits history)]
    congr 2
    rw [sub_eq_add_neg,hi]

end
end ShorECDLP.Entrant.BlendReadout


namespace ShorECDLP.Entrant.BlendReadout
open Quantum Challenge RoundedReadout NeighborReadout Readout56
open Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 300
set_option linter.unusedSimpArgs false

def plusPositions {start} (bits : Vector (Fin start) 261) : Vector Nat 261 :=
  ((lowerBits bits).map Fin.val)++sumPositions (start+2) 256

def minusPositions {start} (bits : Vector (Fin start) 261) : Vector Nat 261 :=
  ((lowerBits bits).map Fin.val)++sumPositions (start+2+13824+512+512) 256

theorem low_read {start} (bits : Vector (Fin start) 261) (history : Fin start→Bool) (tail : List Bool) :
    readWord (List.ofFn history++tail) ((lowerBits bits).map Fin.val).toList=
      some (inputValue (lowerBits bits) history) := by
  rw [readWord_append_left]
  · exact input_read _ _
  · intro i hi
    simp only [Vector.toList_map,List.mem_map] at hi
    obtain ⟨j,_,rfl⟩:=hi
    simpa only [List.length_ofFn] using j.isLt

theorem left_words_read (n start : Nat) (bits : Vector (Fin start) 261)
    (read : ConstantBit n→Bool) (history : Fin start→Bool)
    (ψ : State) (hψ : SupportedOn CleanReadout ψ) (b : InstrumentBranch)
    (hb : b∈((suffix56 n start 256 (upperBits bits)).instantiate read history).run)
    (hn : b.kraus ψ≠0) :
    b.kraus ψ=ψ ∧
      readWord (List.ofFn history++b.history) (plusPositions bits).toList=
        some ((inputValue bits history+32)%2^261) ∧
      readWord (List.ofFn history++b.history) (minusPositions bits).toList=
        some ((inputValue bits history+2^261-32)%2^261) := by
  have hs:=suffix56_branch256 n start (upperBits bits) read history ψ hψ b hb hn
  have hp:=hs.2.1 ⟨0,by omega⟩
  have hm:=hs.2.2 ⟨0,by omega⟩
  simp only [Nat.zero_add,Nat.zero_mul,Nat.add_zero] at hp hm
  refine ⟨hs.1,?_,?_⟩
  · have h:=readWord_concat (List.ofFn history++b.history)
      ((lowerBits bits).map Fin.val).toList (sumPositions (start+2) 256).toList _ _
      (low_read bits history b.history) hp
    rw [←Vector.toList_append] at h
    change readWord _ (plusPositions bits).toList=_ at h
    rw [Vector.length_toList] at h
    change _=some (inputValue (lowerBits bits) history+32*((1+inputValue (upperBits bits) history)%2^256)) at h
    rw [Nat.add_comm 1,plus32 _ _ (input_lt (lowerBits bits) history) (input_lt (upperBits bits) history),←input_split] at h
    exact h
  · have h:=readWord_concat (List.ofFn history++b.history)
      ((lowerBits bits).map Fin.val).toList (sumPositions (start+2+13824+512+512) 256).toList _ _
      (low_read bits history b.history) hm
    rw [←Vector.toList_append] at h
    change readWord _ (minusPositions bits).toList=_ at h
    rw [Vector.length_toList] at h
    change _=some (inputValue (lowerBits bits) history+32*(2^256-1-((1+(2^256-1-inputValue (upperBits bits) history))%2^256))) at h
    rw [minus32 _ _ (input_lt (lowerBits bits) history) (input_lt (upperBits bits) history),←input_split] at h
    exact h

theorem left_words_bound {start} (bits : Vector (Fin start) 261) (v : Nat) :
    (v∈(plusPositions bits).toList ∨ v∈(minusPositions bits).toList)→v<start+43010 := by
  intro h
  simp only [plusPositions,minusPositions,Vector.toList_append,List.mem_append] at h
  rcases h with (h|h)|(h|h)
  · simp only [Vector.toList_map,List.mem_map] at h
    obtain ⟨i,_,rfl⟩:=h
    have hi:=i.isLt
    omega
  · have hb:=sumPositions_bound (start+2) 256 v h
    omega
  · simp only [Vector.toList_map,List.mem_map] at h
    obtain ⟨i,_,rfl⟩:=h
    have hi:=i.isLt
    omega
  · have hb:=sumPositions_bound (start+2+13824+512+512) 256 v h
    omega

end
end ShorECDLP.Entrant.BlendReadout


namespace ShorECDLP.Entrant.BlendReadout
open Quantum Challenge RoundedReadout NeighborReadout Readout56
open Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 300
set_option linter.unusedSimpArgs false

def leftSuffix (n start : Nat) (bits : Vector (Fin start) 261) : Straight n start (start+43010) :=
  castFinish (by omega) (suffix56 n start 256 (upperBits bits))

def suffix (n start : Nat) (left : Vector (Fin start) 261) (right : Vector (Fin start) 208) :
    Straight n start (start+77956) :=
  castFinish (by omega) ((leftSuffix n start left).append
    (suffix56 n (start+43010) 208 (liftBits (extra:=43010) right)))

def leftPositions {start} (left : Vector (Fin start) 261) (i : Fin 56) : Vector Nat 261 :=
  if i.val<44 then left.map Fin.val else if i.val<50 then plusPositions left else minusPositions left

def rightPositions {start} (right : Vector (Fin start) 208) (i : Fin 56) : Vector Nat 208 :=
  shiftPositions (liftBits (extra:=43010) right) (BlendCoverage.offsetAt i)

theorem offset_bounds (i : Fin 56) : -28≤BlendCoverage.offsetAt i ∧ BlendCoverage.offsetAt i≤27 := by
  simp only [BlendCoverage.offsetAt]
  split_ifs <;> have h:=i.isLt <;> omega

theorem suffix_wellFormed (n start : Nat) (left : Vector (Fin start) 261) (right : Vector (Fin start) 208) :
    (suffix n start left right).WellFormed := by
  unfold suffix
  rw [castFinish_wellFormed]
  apply straight_append_wellFormed
  · unfold leftSuffix
    rw [castFinish_wellFormed]
    exact suffix56_wellFormed _ _ _ _
  · exact suffix56_wellFormed _ _ _ _

theorem suffix_slots (n start : Nat) (left : Vector (Fin start) 261) (right : Vector (Fin start) 208) :
    (suffix n start left right).gateSlots=272846 := by
  simp only [suffix,leftSuffix,castFinish_gateSlots,Straight.gateSlots_append,suffix56_slots]

theorem suffix_t (n start : Nat) (left : Vector (Fin start) 261) (right : Vector (Fin start) 208)
    (read : ConstantBit n→Bool) (history : Fin start→Bool) :
    ((suffix n start left right).instantiate read history).tCount=0 := by
  unfold suffix
  rw [castFinish_instantiate]
  apply append_t_zero _ _ read
  · intro h
    simp only [leftSuffix,castFinish_instantiate]
    exact suffix56_t _ _ _ _ _ _
  · exact suffix56_t _ _ _ _ _

theorem suffix_support (n start : Nat) (left : Vector (Fin start) 261) (right : Vector (Fin start) 208)
    (read : ConstantBit n→Bool) (history : Fin start→Bool) :
    ((suffix n start left right).instantiate read history).wires⊆[0,1] := by
  unfold suffix
  rw [castFinish_instantiate]
  apply outer_append_support _ _ read history ([0,1] : List Wire)
  · simp only [leftSuffix,castFinish_instantiate]
    exact suffix56_support _ _ _ _ _ _
  · exact suffix56_support _ _ _ _ _

theorem suffix_reads (n start : Nat) (left : Vector (Fin start) 261) (right : Vector (Fin start) 208)
    (read : ConstantBit n→Bool) (history : Fin start→Bool)
    (ψ : State) (hψ : SupportedOn CleanReadout ψ) (b : InstrumentBranch)
    (hb : b∈((suffix n start left right).instantiate read history).run)
    (hn : b.kraus ψ≠0) (i : Fin 56) :
    readWord (List.ofFn history++b.history) (leftPositions left i).toList=
      some (BlendCoverage.leftAt (inputValue left history) i) ∧
    readWord (List.ofFn history++b.history) (rightPositions right i).toList=
      some (neighborWord (inputValue right history) (BlendCoverage.offsetAt i)) := by
  unfold suffix at hb
  rw [castFinish_instantiate] at hb
  obtain ⟨h₁,a,u,ha,hu,he₁,rfl⟩:=straight_append_branch _ _ read history b hb
  have han : a.kraus ψ≠0 := by
    intro h
    apply hn
    simp only [InstrumentBranch.seq,LinearMap.comp_apply,h,map_zero]
  have hl:=left_words_read n start left read history ψ hψ a
    (by simpa only [leftSuffix,castFinish_instantiate] using ha) han
  have hun : u.kraus ψ≠0 := by
    simpa only [InstrumentBranch.seq,LinearMap.comp_apply,hl.1] using hn
  have hfull : List.ofFn history++(a.seq u).history=List.ofFn h₁++u.history := by
    rw [he₁]
    simp only [InstrumentBranch.seq,List.append_assoc]
  have hval:=liftBits_value right history h₁ a.history he₁
  refine ⟨?_,?_⟩
  · unfold leftPositions BlendCoverage.leftAt
    split_ifs with hi hi'
    · rw [readWord_append_left]
      · exact input_read left history
      · intro v hv
        simp only [Vector.toList_map,List.mem_map] at hv
        obtain ⟨j,_,rfl⟩:=hv
        simpa only [List.length_ofFn] using j.isLt
    · simp only [InstrumentBranch.seq,←List.append_assoc]
      rw [readWord_append_left]
      · exact hl.2.1
      · intro v hv
        have hv':=left_words_bound left v (Or.inl hv)
        have he:=congrArg List.length he₁
        simp only [List.length_append,List.length_ofFn] at he
        simp only [List.length_append,List.length_ofFn]
        omega
    · simp only [InstrumentBranch.seq,←List.append_assoc]
      rw [readWord_append_left]
      · exact hl.2.2
      · intro v hv
        have hv':=left_words_bound left v (Or.inr hv)
        have he:=congrArg List.length he₁
        simp only [List.length_append,List.length_ofFn] at he
        simp only [List.length_append,List.length_ofFn]
        omega
  · rw [hfull]
    simpa only [rightPositions,hval] using
      shiftPositions_read n (start+43010) (liftBits (extra:=43010) right) read h₁ ψ hψ u hu hun
        (BlendCoverage.offsetAt i) (offset_bounds i)

theorem suffix_weight (n start : Nat) (left : Vector (Fin start) 261) (right : Vector (Fin start) 208) :
    ConditionalCatalyst.weight4 (suffix n start left right)=0 := by
  simp only [suffix,leftSuffix,ConditionalCatalyst.weight4_cast,ConditionalCatalyst.weight4_append,
    ConditionalCatalyst.weight4_suffix56,Nat.zero_add]

theorem suffix_residue (n start : Nat) (left : Vector (Fin start) 261) (right : Vector (Fin start) 208) :
    AndGadget.residue (suffix n start left right)=0 := by
  simp only [suffix,leftSuffix,AndGadget.residue_cast,AndGadget.residue_append,
    ApproximatePhase34.residue_suffix56,Nat.zero_add]

end
end ShorECDLP.Entrant.BlendReadout
