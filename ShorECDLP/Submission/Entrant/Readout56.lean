import ShorECDLP.Submission.Entrant.StackBase

/-! Fifty-six neighbouring right words from one sample: the centre, 27 positive shifts and
28 negative shifts. The construction is `NeighborReadout.neighborSuffix` with one more
negative step; every gate is a permitted record-controlled Clifford on wires 0 and 1. -/

namespace ShorECDLP.Entrant.Readout56
open Quantum ShorECDLP.Challenge ShorECDLP.Entrant.RoundedReadout ShorECDLP.Entrant.NeighborReadout
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def suffix56 (n start width : Nat) (bits : Vector (Fin start) width) :
    Straight n start (start+2+168*width) :=
  let c:=initialCursor bits
  let q:=c.lift (27*(2*width))
  castFinish (by omega)
    ((constantStep n start).append
      ((positiveWords n 27 (start+2) width c).append
        ((complementStep n q).append
          (negativeWords n 28 (start+2+27*(2*width)+2*width) width q.next))))

def rightWords56 {start width : Nat} (bits : Vector (Fin start) width) : List (Vector Nat width) :=
  bits.map Fin.val ::
    List.ofFn (fun i : Fin 27=>sumPositions (start+2+i.val*(2*width)) width) ++
    List.ofFn (fun i : Fin 28=>sumPositions
      (start+2+27*(2*width)+2*width+i.val*(4*width)+2*width) width)

theorem rightWords56_length {start width : Nat} (bits : Vector (Fin start) width) :
    (rightWords56 bits).length=56 := by simp [rightWords56]

attribute [local irreducible] positiveWords negativeWords incrementStep complementStep

theorem suffix56_wellFormed (n start width : Nat) (bits : Vector (Fin start) width) :
    (suffix56 n start width bits).WellFormed := by
  unfold suffix56
  rw [castFinish_wellFormed]
  apply straight_append_wellFormed _ _ (constantStep_wellFormed _ _)
  apply straight_append_wellFormed _ _ (positiveWords_wellFormed _ _ _ _ _)
  exact straight_append_wellFormed _ _ (complementStep_wellFormed _ _)
    (negativeWords_wellFormed _ _ _ _ _)

theorem suffix56_slots (n start width : Nat) (bits : Vector (Fin start) width) :
    (suffix56 n start width bits).gateSlots=7+588*width := by
  simp only [suffix56,castFinish_gateSlots,Straight.gateSlots_append,
    constantStep_slots,positiveWords_slots,complementStep_slots,negativeWords_slots]
  ring

theorem append_t_zero {n a b c : Nat} (p : Straight n a b) (q : Straight n b c)
    (read : ConstantBit n→Bool)
    (hp : ∀h, (p.instantiate read h).tCount=0)
    (hq : ∀h, (q.instantiate read h).tCount=0) (history : Fin a→Bool) :
    ((p.append q).instantiate read history).tCount=0 := by
  apply Nat.eq_zero_of_le_zero
  have h:=outer_append_t_le p q read history 0 (fun h=>le_of_eq (hq h))
  simpa only [hp,Nat.add_zero] using h

theorem suffix56_t (n start width : Nat) (bits : Vector (Fin start) width)
    (read : ConstantBit n→Bool)(history : Fin start→Bool) :
    ((suffix56 n start width bits).instantiate read history).tCount=0 := by
  unfold suffix56
  rw [castFinish_instantiate]
  apply append_t_zero _ _ read (constantStep_t _ _ _)
  intro h
  apply append_t_zero _ _ read (positiveWords_t _ _ _ _ _ _)
  intro h
  exact append_t_zero _ _ read (complementStep_t _ _ _)
    (negativeWords_t _ _ _ _ _ _) h

theorem suffix56_support (n start width : Nat) (bits : Vector (Fin start) width)
    (read : ConstantBit n→Bool)(history : Fin start→Bool) :
    ((suffix56 n start width bits).instantiate read history).wires⊆[0,1] := by
  unfold suffix56
  rw [castFinish_instantiate]
  apply outer_append_support _ _ read history ([0,1] : List Wire) (constantStep_support _ _ _ _)
  intro h
  apply outer_append_support _ _ read h ([0,1] : List Wire) (positiveWords_support _ _ _ _ _ _ _)
  intro h
  exact outer_append_support _ _ read h ([0,1] : List Wire) (complementStep_support _ _ _ _)
    (fun hh=>negativeWords_support _ _ _ _ _ _ hh)

/-- Every nonzero readout branch writes all 56 neighbouring residues explicitly. -/
theorem suffix56_branch (n start : Nat) (bits : Vector (Fin start) 208)
    (read : ConstantBit n→Bool) (history : Fin start→Bool)
    (ψ : State) (hψ : SupportedOn CleanReadout ψ) (b : InstrumentBranch)
    (hb : b∈((suffix56 n start 208 bits).instantiate read history).run)
    (hn : b.kraus ψ≠0) :
    b.kraus ψ=ψ ∧
      (∀i : Fin 27, readWord (List.ofFn history++b.history)
        (sumPositions (start+2+i.val*416) 208).toList=
        some ((i.val+1+inputValue bits history)%2^208)) ∧
      (∀i : Fin 28, readWord (List.ofFn history++b.history)
        (sumPositions (start+2+11232+416+i.val*832+416) 208).toList=
        some (2^208-1-((i.val+1+(2^208-1-inputValue bits history))%2^208))) := by
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
  have hpos:=positiveWords_branch n 27 (start+2) 208 (initialCursor bits)
    read h₁ hcarr ψ hψ p hp hpn
  have hvn : v.kraus ψ≠0 := by
    simpa only [InstrumentBranch.seq,LinearMap.comp_apply,hpos.1] using hun
  let q:=(initialCursor bits).lift (27*(2*208))
  have hqc : h₂ q.carry=true := (lift_carry (initialCursor bits) _ h₁ h₂ p.history he₂).trans hcarr
  have hqv : cursorValue q h₂=inputValue bits history :=
    (lift_value (initialCursor bits) _ h₁ h₂ p.history he₂).trans hval
  obtain ⟨h₃,c,t,hc',ht,he₃,rfl⟩:=straight_append_branch _ _ read h₂ v hv
  have hcn : c.kraus ψ≠0 := by
    intro h;apply hvn;simp only [InstrumentBranch.seq,LinearMap.comp_apply,h,map_zero]
  have hcomp:=complementStep_post n q read h₂ hqc ψ hψ c hc' hcn h₃ he₃
  have htn : t.kraus ψ≠0 := by
    simpa only [InstrumentBranch.seq,LinearMap.comp_apply,hcomp.1] using hvn
  have hneg:=negativeWords_branch n 28 (start+2+27*(2*208)+2*208) 208 q.next
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
      have hj':=sumPositions_bound (start+2+i.val*416) 208 j hj
      have hi:=i.isLt
      simp only [List.length_ofFn]
      omega),he₂]
    simpa only [hval] using hpos.2 i
  · intro i
    rw [hfull₃]
    simpa only [hcomp.2.2,hqv] using hneg.2 i

/-- The physical word list contains a correct explicit record for every offset -28..27. -/
theorem suffix56_reads (n start : Nat) (bits : Vector (Fin start) 208)
    (read : ConstantBit n→Bool) (history : Fin start→Bool)
    (ψ : State) (hψ : SupportedOn CleanReadout ψ) (b : InstrumentBranch)
    (hb : b∈((suffix56 n start 208 bits).instantiate read history).run)
    (hn : b.kraus ψ≠0) (j : ℤ) (hj : -28≤j ∧ j≤27) :
    ∃ps∈rightWords56 bits, readWord (List.ofFn history++b.history) ps.toList=
      some ((((inputValue bits history : Nat) : ℤ)+j)%(2^208 : Nat)).toNat := by
  have hs:=suffix56_branch n start bits read history ψ hψ b hb hn
  by_cases hz : j=0
  · subst j
    refine ⟨bits.map Fin.val,by simp [rightWords56],?_⟩
    rw [readWord_append_left (List.ofFn history) b.history _ (by
      intro i hi
      simp only [Vector.toList_map,List.mem_map] at hi
      obtain ⟨k,_,rfl⟩:=hi
      simpa only [List.length_ofFn] using k.isLt),input_read]
    congr 1
    simpa only [Nat.zero_add,Int.natCast_zero,Nat.mod_eq_of_lt (input_lt bits history)] using
      (positive_word_mod (inputValue bits history) 0)
  · by_cases hp : 0<j
    · let i : Fin 27:=⟨j.toNat-1,by omega⟩
      have hi : (i.val+1 : ℤ)=j := by dsimp [i];omega
      refine ⟨sumPositions (start+2+i.val*416) 208,?_,?_⟩
      · unfold rightWords56
        apply List.mem_cons_of_mem
        apply List.mem_append_left
        exact List.mem_ofFn.mpr ⟨i,rfl⟩
      · rw [hs.2.1 i,positive_word_mod]
        congr 2
        exact congrArg (fun z : ℤ=>(((inputValue bits history : Nat) : ℤ)+z)%(2^208 : Nat)) hi
    · let i : Fin 28:=⟨(-j).toNat-1,by omega⟩
      have hi : -((i.val+1 : Nat) : ℤ)=j := by dsimp [i];omega
      refine ⟨sumPositions (start+2+11232+416+i.val*832+416) 208,?_,?_⟩
      · unfold rightWords56
        apply List.mem_cons_of_mem
        apply List.mem_append_right
        exact List.mem_ofFn.mpr ⟨i,rfl⟩
      · rw [hs.2.2 i,negative_word_mod _ _ (input_lt bits history)]
        congr 2
        rw [sub_eq_add_neg,hi]

end
end ShorECDLP.Entrant.Readout56
