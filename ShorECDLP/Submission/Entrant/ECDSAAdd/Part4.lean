-- Vendored from ECDSAAdd (ecdsa.fail Lean challenge), Apache-2.0, Copyright 2026 Runzhou Tao, Anirudh and ECDSAAdd contributors; 139 source modules at c3f340a (listed in MODULES.txt), concatenated. Changes: module paths, expanded notation, private-name renames.
import ShorECDLP.Submission.Entrant.ECDSAAdd.Part1
import ShorECDLP.Submission.Entrant.ECDSAAdd.Part2
import ShorECDLP.Submission.Entrant.ECDSAAdd.Part3

-- source: ECDSAAdd/Arithmetic/NativeFirstDirectForwardProof.lean
noncomputable section

set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Arithmetic.NativeFirstDirect
attribute [local irreducible] run mappedAdd hAdd kAdd kTail lowCopy rotateRight forward

private theorem block_one (w : Nat → Wire) (a : Nat) :
    wireBlock w a 1=[w a] := by simp [wireBlock,List.range']

private theorem cons_value (h : Wire) (r : List Wire) (s : BasisState) :
    regValue (h::r) s=(s h).toNat+2*regValue r s := by
  cases hb : s h <;> simp [regValue,hb]

private theorem write_value (r : List Wire) (s : BasisState) (q : Wire) (v : Bool)
    (ha : q∉r) : regValue r (writeBit s q v)=regValue r s := by
  apply regValue_congr
  intro j hj
  simp [writeBit,show j≠q from fun e => ha (e ▸ hj)]

private theorem contained (w : Nat → Wire) (a n b m : Nat)
    (lo : b≤a) (hi : a+n≤b+m) : ∀q∈wireBlock w a n,q∈wireBlock w b m := by
  intro q hq
  obtain ⟨i,hi',rfl⟩ := List.mem_map.mp hq
  exact List.mem_map.mpr ⟨i,by
    simp only [List.mem_range'_1] at hi' ⊢
    omega,rfl⟩

/-- A257 and Ext258 are preserved even though the physical A view is wider. -/
def mutable (w : Nat → Wire) : List Wire :=
  wireBlock w 0 257++wireBlock w 770 258++[w 1028]

private def Stable (w : Nat → Wire) (s t : State) : Prop :=
  t.phase=s.phase ∧ ∀q,q∉mutable w → t.basis q=s.basis q

private theorem stable_trans (w : Nat → Wire) (s t u : State)
    (a : Stable w s t) (b : Stable w t u) : Stable w s u :=
  ⟨b.1.trans a.1,fun q hq => (b.2 q hq).trans (a.2 q hq)⟩

private theorem stable_target (w : Nat → Wire) (s t : State) (r : List Wire)
    (hp : t.phase=s.phase) (hf : ∀q,q∉r → t.basis q=s.basis q)
    (hr : ∀q∈r,q∈mutable w) : Stable w s t :=
  ⟨hp,fun q hq => hf q (fun h => hq (hr q h))⟩

private theorem stable_write (w : Nat → Wire) (s : State) (q : Wire) (v : Bool)
    (hq : q∈mutable w) : Stable w s ⟨s.phase,writeBit s.basis q v⟩ := by
  refine ⟨rfl,?_⟩
  intro j hj
  simp [writeBit,show j≠q from fun e => hj (e ▸ hq)]

private theorem outside_index (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (i : Nat) (hi : i < 1798) (ha : 257 ≤ i) (hb : i < 770 ∨ 1028 ≤ i)
    (hs : i ≠ 1028) : w i∉mutable w := by
  simp only [mutable,List.mem_append,List.mem_singleton,not_or]
  exact ⟨⟨block_not_mem w hn i 0 257 hi (by omega) (by omega),
    block_not_mem w hn i 770 258 hi (by omega) hb⟩,
    index_ne w hn i 1028 hi (by omega) hs⟩

private theorem bank_clean (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (s t : State) (a n : Nat) (ha : 1540≤a) (hb : a+n≤1797)
    (hc : regValue (wireBlock w 1540 257) s.basis=0) (fr : Stable w s t) :
    ∀q∈wireBlock w a n,t.basis q=false := by
  intro q hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  rw [fr.2 _ (outside_index w hn i (by omega) (by omega) (by omega) (by omega))]
  exact (regValue_zero _ _).mp hc _ (List.mem_map.mpr
    ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩)

private theorem keep_value (r target : List Wire) (s t : BasisState)
    (hf : ∀q,q∉target → t q=s q) (sep : List.Disjoint r target) :
    regValue r t=regValue r s :=
  regValue_congr r t s (fun q hq => hf q (List.disjoint_left.mp sep hq))

private theorem clear_value (h : Wire) (r : List Wire) (s : BasisState)
    (ha : h∉r) (X : Nat) (hv : regValue (h::r) s=X) :
    regValue (h::r) (writeBit s h false)=2*(X/2) := by
  rw [cons_value,show (writeBit s h false) h=false by simp [writeBit],
    Bool.toNat_false,write_value r s h false ha]
  rw [cons_value] at hv
  cases hb : s h <;> simp only [hb,Bool.toNat_false,Bool.toNat_true] at hv <;> omega

/-- Copy prepares the complete H word from a canonical x, with full frame. -/
theorem lowCopy_prepares (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x : Nat) (hx : x<2^256) (s : State) (m : List Bool)
    (ha : regValue (wireBlock w 1 256) s.basis=0)
    (hb : regValue (wireBlock w 770 258) s.basis=x) :
    (run (lowCopy w) m s).phase=s.phase ∧
    (∀q,q∉wireBlock w 1 255 → (run (lowCopy w) m s).basis q=s.basis q) ∧
    regValue (wireBlock w 1 256) (run (lowCopy w) m s).basis=x/2 := by
  have raw := copyRegister_correct none (wireBlock w 771 255) (wireBlock w 1 255)
    (by simp [wireBlock_length]) (copy_inputs_nd w hn) (by simp) s m
  have c : (run (lowCopy w) m s).phase=s.phase ∧
      (∀q,q∉wireBlock w 1 255 → (run (lowCopy w) m s).basis q=s.basis q) ∧
      regValue (wireBlock w 1 255) (run (lowCopy w) m s).basis=
        regValue (wireBlock w 1 255) s.basis ^^^ regValue (wireBlock w 771 255) s.basis := by
    simpa only [lowCopy,copyValue] using raw
  generalize hz : run (lowCopy w) m s=z at c ⊢
  have clean := (regValue_zero _ _).mp ha
  have dst : regValue (wireBlock w 1 255) s.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    exact clean q (block_subset w 1 255 256 (by omega) q hq)
  have splitB := wireBlock_append w 770 256 2
  have val := hb
  rw [←splitB,regValue_append,wireBlock_length] at val
  have bound := regValue_lt (wireBlock w 770 256) s.basis
  rw [wireBlock_length] at bound
  have low : regValue (wireBlock w 770 256) s.basis=x := by omega
  have splitLow : w 770::wireBlock w 771 255=wireBlock w 770 256 := by
    simpa [block_one] using wireBlock_append w 770 1 255
  have bits : (if s.basis (w 770) then 1 else 0)+
      2*regValue (wireBlock w 771 255) s.basis=x := by
    rw [←splitLow] at low
    exact low
  have src : regValue (wireBlock w 771 255) s.basis=x/2 := by
    cases e : s.basis (w 770) <;> simp [e] at bits <;> omega
  have guard : s.basis (w 256)=false := clean _ (List.mem_map.mpr
    ⟨256,by simp [List.mem_range'_1],rfl⟩)
  have guardOut : z.basis (w 256)=false :=
    (c.2.1 _ (block_not_mem w hn 256 1 255 (by omega) (by omega) (by omega))).trans guard
  refine ⟨c.1,c.2.1,?_⟩
  have splitH := wireBlock_append w 1 255 1
  rw [←splitH,regValue_append]
  have value : regValue (wireBlock w 1 255) z.basis=x/2 := by
    simpa only [dst,src,Nat.zero_xor] using c.2.2
  have high : regValue (wireBlock w 256 1) z.basis=0 := by
    simp only [block_one,regValue,List.foldr_cons,List.foldr_nil,guardOut,
      Bool.false_eq_true,if_false,Nat.mul_zero,Nat.add_zero]
  rw [value,high,Nat.mul_zero,Nat.add_zero]
/-- Complete emitted forward state on the original canonical seed domain.
The Nat expressions are the physical word encodings of the direct first tick. -/
theorem forward_spec (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x : Nat) (hx : x<p) (s : State) (m : List Bool)
    (hin : LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) 0 x s.basis) :
    let e := s.basis (w 770)
    let z := run (forward w) m s
    z.phase=s.phase ∧
    regValue (wireBlock w 0 258) z.basis=
      2*(x/2+(if e then hConstant else 0))+(!e).toNat ∧
    regValue (wireBlock w 770 258) z.basis=
      (x/2+kConstant false e)%2^258 ∧
    z.basis (w 0)=!e ∧ z.basis (w 1028)=e ∧
    (∀q,q∉mutable w → z.basis q=s.basis q) := by
  let e := s.basis (w 770)
  generalize ha : run [.CX (w 770) (w 1028),.CX (w 1028) (w 0),.X (w 0)] m s=a
  generalize hb : run (lowCopy w) m a=b
  generalize hcr : run (hAdd w false) m b=c
  generalize hd : run [.CX (w 1028) (w 770)] (m.drop 252) c=d
  generalize ht : run (rotateRight (wireBlock w 770 258)) (m.drop 252) d=t
  generalize hu : run (kAdd w false) (m.drop 252) t=u
  have full : run (forward w) m s=u := by
    simp only [forward,List.append_assoc]
    rw [run_append,run_take,
      show measurementCount [.CX (w 770) (w 1028),.CX (w 1028) (w 0),.X (w 0)]=0 from rfl,
      List.drop_zero,ha]
    rw [run_append,run_take,(lowCopy_counts w).2,List.drop_zero,hb]
    rw [run_append,run_take,(hAdd_counts w false).2,hcr]
    rw [run_append,run_take,
      show measurementCount [.CX (w 1028) (w 770)]=0 from rfl,List.drop_zero,hd]
    rw [run_append,run_take,(rotate_counts (wireBlock w 770 258)).2.1,List.drop_zero,ht,hu]
  have cleanA := (regValue_zero _ _).mp hin.a
  have mem0 : w 0∈wireBlock w 0 258 := List.mem_map.mpr
    ⟨0,by simp [List.mem_range'_1],rfl⟩
  have fr := front_spec w s m (index_ne w hn 0 1028 (by omega) (by omega) (by omega))
    (cleanA _ mem0) hin.one
  rw [ha] at fr
  have ah : regValue (wireBlock w 1 256) a.basis=0 := by
    rw [fr,write_value _ _ (w 0) _ (block_not_mem w hn 0 1 256 (by omega) (by omega) (by omega)),
      write_value _ _ (w 1028) _ (block_not_mem w hn 1028 1 256 (by omega) (by omega) (by omega))]
    exact (regValue_zero _ _).mpr (fun q hq => cleanA q (contained w 1 256 0 258 (by omega) (by omega) q hq))
  have ab : regValue (wireBlock w 770 258) a.basis=x := by
    rw [fr,write_value _ _ (w 0) _ (block_not_mem w hn 0 770 258 (by omega) (by omega) (by omega)),
      write_value _ _ (w 1028) _ (block_not_mem w hn 1028 770 258 (by omega) (by omega) (by omega))]
    exact hin.b
  have ag : a.basis (w 0)=!e := by rw [fr]; simp [e,writeBit]
  have ase : a.basis (w 1028)=e := by
    rw [fr]; simp [e,writeBit,index_ne w hn 1028 0 (by omega) (by omega) (by omega)]
  have ae : a.basis (w 770)=e := by
    rw [fr]; simp [e,writeBit,index_ne w hn 770 0 (by omega) (by omega) (by omega),
      index_ne w hn 770 1028 (by omega) (by omega) (by omega)]
  have fa : Stable w s a := by
    rw [fr]
    apply stable_trans w s ⟨s.phase,writeBit s.basis (w 1028) e⟩
    · exact stable_write w s _ _ (by simp [mutable])
    · exact stable_write w _ _ _ (by
        simp only [mutable,List.mem_append,List.mem_singleton]
        exact Or.inl (Or.inl (List.mem_map.mpr ⟨0,by simp [List.mem_range'_1],rfl⟩)))
  have xb : x<2^256 := lt_trans hx (by norm_num [p])
  have cp := lowCopy_prepares w hn x xb a m ah ab
  rw [hb] at cp
  have fb : Stable w s b := stable_trans w s a b fa (stable_target w a b _
    cp.1 cp.2.1 (fun q hq => by
      simp only [mutable,List.mem_append,List.mem_singleton]
      exact Or.inl (Or.inl (contained w 1 255 0 257 (by omega) (by omega) q hq))))
  have bs : b.basis (w 1028)=e := (cp.2.1 _ (block_not_mem w hn 1028 1 255 (by omega) (by omega) (by omega))).trans ase
  have bg : b.basis (w 0)=!e := (cp.2.1 _ (block_not_mem w hn 0 1 255 (by omega) (by omega) (by omega))).trans ag
  have be : b.basis (w 770)=e := (cp.2.1 _ (block_not_mem w hn 770 1 255 (by omega) (by omega) (by omega))).trans ae
  have bb : regValue (wireBlock w 770 258) b.basis=x :=
    (keep_value _ _ _ _ cp.2.1 (block_disjoint w hn 770 258 1 255 (by omega) (by omega) (by omega))).trans ab
  have fit : regValue (wireBlock w 1 256) b.basis+(if b.basis (w 1028) then hConstant else 0)<2^256 := by
    rw [cp.2.2,bs]
    have pp : p<2^256 := by norm_num [p]
    have hh : 2*hConstant=p+1 := by norm_num [hConstant,p]
    cases he : e <;> simp [he] <;> omega
  have hc := hAdd_word w b m (h_inputs_nd w hn) (h_sources_fresh w hn false)
    (bank_clean w hn s b 1540 252 (by omega) (by omega) hin.carry fb)
    ((fb.2 _ (outside_index w hn 1797 (by omega) (by omega) (by omega) (by omega))).trans hin.cin)
    (List.disjoint_left.mp (block_disjoint w hn 1 3 4 253 (by omega) (by omega) (by omega))) fit
  rw [hcr] at hc
  have fc : Stable w s c := stable_trans w s b c fb (stable_target w b c _
    hc.1 hc.2.1 (fun q hq => by
      simp only [mutable,List.mem_append,List.mem_singleton]
      exact Or.inl (Or.inl (contained w 4 253 0 257 (by omega) (by omega) q hq))))
  have ch : regValue (wireBlock w 1 256) c.basis=x/2+(if e then hConstant else 0) := by rw [hc.2.2,cp.2.2,bs]
  have cs : c.basis (w 1028)=e := (hc.2.1 _ (block_not_mem w hn 1028 4 253 (by omega) (by omega) (by omega))).trans bs
  have cg : c.basis (w 0)=!e := (hc.2.1 _ (block_not_mem w hn 0 4 253 (by omega) (by omega) (by omega))).trans bg
  have ce : c.basis (w 770)=e := (hc.2.1 _ (block_not_mem w hn 770 4 253 (by omega) (by omega) (by omega))).trans be
  have cb : regValue (wireBlock w 770 258) c.basis=x :=
    (keep_value _ _ _ _ hc.2.1 (block_disjoint w hn 770 258 4 253 (by omega) (by omega) (by omega))).trans bb
  have cl := clear_spec w c (m.drop 252) (ce.trans cs.symm)
  rw [hd] at cl
  have fd : Stable w s d := stable_trans w s c d fc (by
    rw [cl]
    exact stable_write w c _ _ (by
      simp only [mutable,List.mem_append,List.mem_singleton]
      exact Or.inl (Or.inr (List.mem_map.mpr ⟨770,by simp [List.mem_range'_1],rfl⟩))))
  have headB : w 770::wireBlock w 771 257=wireBlock w 770 258 := by
    simpa [block_one] using wireBlock_append w 770 1 257
  have awayB : w 770∉wireBlock w 771 257 := block_not_mem w hn 770 771 257 (by omega) (by omega) (by omega)
  have db : regValue (wireBlock w 770 258) d.basis=2*(x/2) := by
    rw [cl,←headB]
    exact clear_value _ _ _ awayB x (by rw [headB]; exact cb)
  have rr := rotateRight_spec (wireBlock w 770 258) (block_nodup w hn 770 258 (by omega))
    (2*(x/2)) (by omega) d (m.drop 252) db
  have rf := rotate_frame (wireBlock w 770 258) d (m.drop 252)
  rw [ht] at rr rf
  have ft : Stable w s t := stable_trans w s d t fd (stable_target w d t _ rf.1 rf.2.1 (by
    intro q hq; simp [mutable,hq]))
  have tb : regValue (wireBlock w 770 258) t.basis=x/2 := by simpa using rr.2
  have ts : t.basis (w 1028)=e := by
    rw [rf.2.1 _ (block_not_mem w hn 1028 770 258 (by omega) (by omega) (by omega)),cl]
    simpa [writeBit,index_ne w hn 1028 770 (by omega) (by omega) (by omega)] using cs
  have tg : t.basis (w 0)=!e := by
    rw [rf.2.1 _ (block_not_mem w hn 0 770 258 (by omega) (by omega) (by omega)),cl]
    simpa [writeBit,index_ne w hn 0 770 (by omega) (by omega) (by omega)] using cg
  have kh := kAdd_word w t (m.drop 252) (k_inputs_nd w hn) (k_sources_fresh w hn false)
    (bank_clean w hn s t 1540 256 (by omega) (by omega) hin.carry ft)
  rw [hu] at kh
  have fu : Stable w s u := stable_trans w s t u ft (stable_target w t u _ kh.1 kh.2.1 (by
    intro q hq; simp [mutable,hq]))
  have uh : regValue (wireBlock w 1 256) u.basis=x/2+(if e then hConstant else 0) := by
    rw [keep_value _ _ _ _ kh.2.1 (block_disjoint w hn 1 256 770 258 (by omega) (by omega) (by omega)),
      keep_value _ _ _ _ rf.2.1 (block_disjoint w hn 1 256 770 258 (by omega) (by omega) (by omega)),cl,
      write_value _ _ (w 770) _ (block_not_mem w hn 770 1 256 (by omega) (by omega) (by omega))]
    exact ch
  have ug : u.basis (w 0)=!e := (kh.2.1 _ (block_not_mem w hn 0 770 258 (by omega) (by omega) (by omega))).trans tg
  have us : u.basis (w 1028)=e := (kh.2.1 _ (block_not_mem w hn 1028 770 258 (by omega) (by omega) (by omega))).trans ts
  have guard : u.basis (w 257)=false := (fu.2 _ (outside_index w hn 257 (by omega) (by omega) (by omega) (by omega))).trans
    (cleanA _ (List.mem_map.mpr ⟨257,by simp [List.mem_range'_1],rfl⟩))
  have ua : regValue (wireBlock w 0 258) u.basis=2*(x/2+(if e then hConstant else 0))+(!e).toNat := by
    rw [←wireBlock_append w 0 257 1,regValue_append,block_one]
    have headA : w 0::wireBlock w 1 256=wireBlock w 0 257 := by
      simpa [block_one] using wireBlock_append w 0 1 256
    rw [←headA,cons_value,ug,uh]
    simp [regValue,guard,wireBlock_length,Nat.add_comm]
  rw [full]
  exact ⟨fu.1,ua,by simpa [tb,ts] using kh.2.2,ug,us,fu.2⟩

end ECDSAAdd.Arithmetic.NativeFirstDirect
end

-- source: ECDSAAdd/Arithmetic/NativeFirstPrefixMath.lean
noncomputable section

set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.NativeFirstPrefixMath
open SkywalkRails Secp256k1

/-- Mathematical input parity, matching the low bit of the canonical x word. -/
def oddBit (x : Int) : Bool := decide (x%2≠0)
def hValue (prime x : Int) : Int := x/2+(if oddBit x then (prime+1)/2 else 0)
def kValue (prime x : Int) : Int := if oddBit x then (x-prime)/2 else prime+x/2

def directTick (prime x : Int) : SkywalkRails.Tick :=
  ⟨hValue prime x,kValue prime x,!(oddBit x),oddBit x⟩

/-- This is the incumbent seeded state, not the rejected alternative(2x,p). -/
def initp (x : Nat) : SkywalkRails.State :=
  SkywalkRails.encode false false (x : Int) (ECDSAAdd.p : Int)

private theorem split_half (prime x : Int) (hp : prime%2=1) (hx : x%2≠0) :
    (x+prime)/2=x/2+(prime+1)/2 := by omega

/-- Exact original first signed tick: strict x<prime fixes the odd sign record. -/
theorem direct_step (prime x : Int) (hp : 0<prime) (hpo : prime%2=1)
    (hx0 : 0≤x) (hx : x<prime) :
    SkywalkRails.step (SkywalkRails.encode false false x prime)=directTick prime x := by
  by_cases he : x%2=0
  · rw [SkywalkRails.step_encode_even false false x prime hx0 hp hpo he]
    simp [directTick,hValue,kValue,oddBit,he,SkywalkRails.signed,add_comm]
  · rw [SkywalkRails.step_encode_odd false false x prime hx0 hp hpo he]
    have half := split_half prime x hpo he
    simp [directTick,hValue,kValue,oddBit,he,hx,half]

/-- Canonical H and signed K ranges are stated on the whole original domain. -/
theorem direct_bounds (prime x : Int) (hp : 0<prime) (hpo : prime%2=1)
    (hx0 : 0≤x) (hx : x<prime) :
    0≤hValue prime x ∧ hValue prime x<prime ∧
    -prime<kValue prime x ∧ kValue prime x<2*prime := by
  by_cases he : x%2=0
  · simp only [hValue,kValue,oddBit,he,ne_self_iff_false,decide_false,
      Bool.false_eq_true,if_false,add_zero]
    omega
  · have half := split_half prime x hpo he
    simp only [hValue,kValue,oddBit,he,not_false_eq_true,decide_true,if_true]
    omega

/-- No fabricated negative zero: H is nonnegative and K is negative exactly
on the odd input branch. G and S are the original first transcript values. -/
theorem direct_signs (prime x : Int) (hp : 0<prime) (hpo : prime%2=1)
    (hx0 : 0≤x) (hx : x<prime) :
    SkywalkRails.neg (hValue prime x)=false ∧
      SkywalkRails.neg (kValue prime x)=oddBit x := by
  have bounds := direct_bounds prime x hp hpo hx0 hx
  constructor
  · simp only [SkywalkRails.neg,show ¬hValue prime x<0 from by omega,decide_false]
  · by_cases he : x%2=0
    · have positive : 0<kValue prime x := by
        simp only [kValue,oddBit,he,ne_self_iff_false,decide_false,Bool.false_eq_true,if_false]
        omega
      simp [SkywalkRails.neg,oddBit,he,show ¬kValue prime x<0 from by omega]
    · have negative : kValue prime x<0 := by
        have literal : (x-prime)/2<0 := by omega
        simpa [kValue,oddBit,he] using literal
      simp [SkywalkRails.neg,oddBit,he,negative]

/-- The exact first tick's native orientation frame is inherited, not assumed. -/
theorem direct_frame (prime x : Int) (hp : 0<prime) (hpo : prime%2=1)
    (hx0 : 0≤x) (hx : x<prime) : SkywalkRails.Frame (directTick prime x) := by
  rw [←direct_step prime x hp hpo hx0 hx]
  exact SkywalkRails.step_frame false false x prime hx0 hp hpo

/-- Mathematical inverse reconstruction only. This does not erase a register
for free or replace the independently emitted measured inverse circuit. -/
theorem recover_x (prime x : Int) (_hp : 0<prime) (hpo : prime%2=1)
    (_hx0 : 0≤x) (_hx : x<prime) :
    (if oddBit x then 2*kValue prime x+prime else 2*hValue prime x)=x := by
  by_cases he : x%2=0
  · simp only [hValue,kValue,oddBit,he,ne_self_iff_false,decide_false,
      Bool.false_eq_true,if_false,add_zero]
    omega
  · have hxodd : x%2=1 := by omega
    have hd : (x-prime)%2=0 := by
      rw [Int.sub_emod,hxodd,hpo]
      norm_num
    have literal : 2*((x-prime)/2)+prime=x := by omega
    simpa [hValue,kValue,oddBit,he] using literal

private theorem prime_positive : 0<(ECDSAAdd.p : Int) := by norm_num [ECDSAAdd.p]
private theorem prime_odd : (ECDSAAdd.p : Int)%2=1 := by norm_num [ECDSAAdd.p]
private theorem prime_word_bound : (ECDSAAdd.p : Int)<(2^256 : Int) := by norm_num [ECDSAAdd.p]

/-- Closed equality against the actual incumbent secp seed/first tick. -/
theorem secp_first_step (x : Nat) (hx : x<ECDSAAdd.p) :
    SkywalkRails.step (initp x)=directTick (ECDSAAdd.p : Int) (x : Int) := by
  unfold initp
  exact direct_step _ _ prime_positive prime_odd (by omega) (by exact_mod_cast hx)

/-- H fits the n=256 output slice. K fits the native n+2 signed register;
all guard-bit/value claims still require the actual circuit frame theorem. -/
theorem secp_word_bounds (x : Nat) (hx : x<ECDSAAdd.p) :
    0≤hValue (ECDSAAdd.p : Int) (x : Int) ∧
      hValue (ECDSAAdd.p : Int) (x : Int)<(2^256 : Int) ∧
      -(2^257 : Int)<kValue (ECDSAAdd.p : Int) (x : Int) ∧
      kValue (ECDSAAdd.p : Int) (x : Int)<(2^257 : Int) := by
  have b := direct_bounds (ECDSAAdd.p : Int) (x : Int) prime_positive prime_odd
    (by omega) (by exact_mod_cast hx)
  have p := prime_word_bound
  constructor
  · exact b.1
  constructor
  · omega
  constructor <;> omega

/-- The zero input is covered by the prototype contract and preserves the
unique terminal sign, even though the point caller's divisor is nonzero. -/
theorem secp_zero : directTick (ECDSAAdd.p : Int) 0=⟨0,(ECDSAAdd.p : Int),true,false⟩ := by
  simp [directTick,hValue,kValue,oddBit]

end ECDSAAdd.Arithmetic.NativeFirstPrefixMath
end

-- source: ECDSAAdd/Arithmetic/NativeFirstDirectNativeBridge.lean
noncomputable section

set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 1024
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.NativeFirstDirect
open NativeFirstPrefixMath
attribute [local irreducible] run forward

private theorem block_one_NativeFirstDirectNativeBridge (w : Nat → Wire) (a : Nat) :
    wireBlock w a 1=[w a] := by simp [wireBlock,List.range']
private theorem cons_value_NativeFirstDirectNativeBridge (h : Wire) (r : List Wire) (s : BasisState) :
    regValue (h::r) s=(s h).toNat+2*regValue r s := by
  cases hb : s h <;> simp [regValue,hb]

/-- Actual source parity follows from the original word equality. -/
theorem source_parity (w : Nat → Wire) (s : BasisState) (x : Nat)
    (hb : regValue (wireBlock w 770 258) s=x) :
    s (w 770)=oddBit (x : Int) := by
  have split : w 770::wireBlock w 771 257=wireBlock w 770 258 := by
    simpa [block_one_NativeFirstDirectNativeBridge] using wireBlock_append w 770 1 257
  rw [←split,cons_value_NativeFirstDirectNativeBridge] at hb
  cases he : s (w 770)
  · have hi : (x : Int)%2=0 := by simp only [he,Bool.toNat_false] at hb; omega
    simp [he,oddBit,hi]
  · have hi : (x : Int)%2≠0 := by simp only [he,Bool.toNat_true] at hb; omega
    simp [he,oddBit,hi]

/-- The positive magnitude is represented by the actual unsigned H word. -/
theorem h_nat_value (x : Nat) :
    hValue (p : Int) (x : Int)=
      ((x/2+(if oddBit (x : Int) then hConstant else 0) : Nat) : Int) := by
  cases he : oddBit (x : Int) <;>
    simp [hValue,hConstant,he,Int.natCast_ediv]

private theorem decode_positive (n V : Nat) (hv : V<2^(n-1)) (hm : V<2^n) :
    signedDecode n (V%2^n)=(V : Int) := by
  rw [Nat.mod_eq_of_lt hm,signedDecode,if_pos hv]
private theorem decode_negative (n U Q : Nat) (hq : Q≤2^n)
    (hlo : 2^(n-1)≤U+(2^n-Q)) (hhi : U+(2^n-Q)<2^n) :
    signedDecode n ((U+(2^n-Q))%2^n)=(U : Int)-(Q : Int) := by
  rw [Nat.mod_eq_of_lt hhi,signedDecode,if_neg (by omega)]
  have sum : ((2^n-Q : Nat) : Int)+(Q : Int)=((2^n : Nat) : Int) := by
    exact_mod_cast Nat.sub_add_cancel hq
  rw [Nat.cast_add]
  omega
private theorem odd_difference (X P Q : Nat) (hp : 2*Q+1=P)
    (ho : (X : Int)%2≠0) :
    ((X/2 : Nat) : Int)-(Q : Int)=((X : Int)-(P : Int))/2 := by
  have hi : 2*(Q : Int)+1=(P : Int) := by exact_mod_cast hp
  simp only [Int.natCast_ediv,Nat.cast_ofNat]
  omega

/-- Arithmetic is checked on abstract scalars before specializing the modulus. -/
theorem k_decode_value (x : Nat) (hx : x<p) :
    signedDecode 258 ((x/2+kConstant false (oddBit (x : Int)))%2^258)=
      kValue (p : Int) (x : Int) := by
  have pp : p<2^256 := by norm_num [p]
  have qp : 2*((p-1)/2)+1=p := by norm_num [p]
  by_cases he : (x : Int)%2=0
  · have flag : oddBit (x : Int)=false := by simp [oddBit,he]
    have kc : kConstant false false=p := rfl
    have kv : kValue (p : Int) (x : Int)=(p : Int)+(x : Int)/2 := by simp [kValue,flag]
    rw [flag,kc,decode_positive 258 (x/2+p) (by omega) (by omega),kv]
    simp only [Nat.cast_add,Int.natCast_ediv,Nat.cast_ofNat]
    omega
  · have flag : oddBit (x : Int)=true := by simp [oddBit,he]
    have kc : kConstant false true=2^258-(p-1)/2 := rfl
    have kv : kValue (p : Int) (x : Int)=((x : Int)-(p : Int))/2 := by simp [kValue,flag]
    rw [flag,kc,decode_negative 258 (x/2) ((p-1)/2) (by omega) (by omega) (by omega),kv]
    exact odd_difference x p ((p-1)/2) qp he

private theorem first_layout (w : Nat → Wire) :
    compactSkywalkTickLayout w 0=skywalkPoolTick w 0 := by rfl
private theorem first_pre : compactSkywalkTickPreWidth 0=258 := by rfl
private theorem first_post : compactSkywalkTickPostWidth 0=258 := by rfl

private theorem first_a_retained (w : Nat → Wire) :
    (compactSkywalkTickARelease w 0).retained=wireBlock w 1 258 := by
  unfold compactSkywalkTickARelease
  rw [first_post,compactSkywalkTick_half w 0 (by omega),first_pre]
  rw [compactSkywalkSignWord_retained _ 258 (by omega) (by simp [wireBlock_length])]
  simpa only [wireBlock_length] using List.take_length (l := wireBlock w 1 258)
private theorem first_b_retained (w : Nat → Wire) :
    (compactSkywalkTickBRelease w 0).retained=wireBlock w 770 258 := by
  unfold compactSkywalkTickBRelease
  rw [first_post,compactSkywalkTick_b w 0 (by omega),first_pre]
  rw [compactSkywalkSignWord_retained _ 258 (by omega) (by simp [wireBlock_length])]
  simpa only [wireBlock_length] using List.take_length (l := wireBlock w 770 258)
private theorem clean_full (r : List Wire) (s : BasisState) :
    (compactSkywalkSignWord r r.length).Clean s := by
  simp [compactSkywalkSignWord,CompactSkywalkSignReleaseLayout.Clean]
private theorem first_clean (w : Nat → Wire) (s : BasisState) :
    (compactSkywalkTickARelease w 0).Clean s ∧
      (compactSkywalkTickBRelease w 0).Clean s := by
  have a := clean_full (wireBlock w 1 258) s
  have b := clean_full (wireBlock w 770 258) s
  simp only [wireBlock_length] at a b
  unfold compactSkywalkTickARelease compactSkywalkTickBRelease
  rw [compactSkywalkTick_half w 0 (by omega),compactSkywalkTick_b w 0 (by omega),first_pre,first_post]
  exact ⟨a,b⟩

private theorem output_zero (w : Nat → Wire) (u : BasisState) (A B : Int)
    (t : SkywalkRails.Tick) (step : SkywalkRails.step ⟨A,B,false⟩=t)
    (ha : signedRegValue (wireBlock w 1 258) u=t.h)
    (hb : signedRegValue (wireBlock w 770 258) u=t.k)
    (hg : u (w 0)=t.g) (hs : u (w 1028)=t.s)
    (previous : u (w 1797)=false) (carry : regValue (wireBlock w 1540 257) u=0) :
    CompactSkywalkTickOutput w 0 A B false u := by
  simp only [CompactSkywalkTickOutput,first_a_retained,first_b_retained,first_layout,step,
    skywalkPoolTick,skywalkPoolPreviousId,if_pos rfl]
  exact ⟨ha,hb,hg,hs,previous,carry,(first_clean w u).1,(first_clean w u).2⟩

/-- Semantic transport is proved for abstract input/output states. -/
private theorem transport_native (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x : Nat) (hx : x<p) (s z : State)
    (hin : LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) 0 x s.basis)
    (ext : s.basis (w 258)=false)
    (out : z.phase=s.phase ∧
      regValue (wireBlock w 0 258) z.basis=
        2*(x/2+(if s.basis (w 770) then hConstant else 0))+(!(s.basis (w 770))).toNat ∧
      regValue (wireBlock w 770 258) z.basis=(x/2+kConstant false (s.basis (w 770)))%2^258 ∧
      z.basis (w 0)=!(s.basis (w 770)) ∧ z.basis (w 1028)=s.basis (w 770) ∧
      (∀q,q∉mutable w → z.basis q=s.basis q)) :
    z.phase=s.phase ∧ CompactSkywalkTickOutput w 0 ((x : Int)+(p : Int))
      (x : Int) false z.basis := by
  have parity := source_parity w s.basis x hin.b
  rw [parity] at out
  let H := x/2+(if oddBit (x : Int) then hConstant else 0)
  have hp : (H : Int)=hValue (p : Int) (x : Int) := (h_nat_value x).symm
  have bound := secp_word_bounds x hx
  have hbound : H<2^256 := by omega
  have bvalue : signedRegValue (wireBlock w 770 258) z.basis=kValue (p : Int) (x : Int) := by
    rw [signedRegValue,wireBlock_length,out.2.2.1]
    exact k_decode_value x hx
  have split : w 0::wireBlock w 1 257=wireBlock w 0 258 := by
    simpa [block_one_NativeFirstDirectNativeBridge] using wireBlock_append w 0 1 257
  have packed := out.2.1
  rw [←split,cons_value_NativeFirstDirectNativeBridge,out.2.2.2.1] at packed
  have half : regValue (wireBlock w 1 257) z.basis=H := by omega
  have outside (i : Nat) (hi : i<1798) (ha : 257 ≤ i)
      (hb : i < 770 ∨ 1028 ≤ i) (hs : i ≠ 1028) : w i∉mutable w := by
    simp only [mutable,List.mem_append,List.mem_singleton,not_or]
    exact ⟨⟨block_not_mem w hn i 0 257 hi (by omega) (by omega),
      block_not_mem w hn i 770 258 hi (by omega) hb⟩,
      index_ne w hn i 1028 hi (by omega) hs⟩
  have ze : z.basis (w 258)=false :=
    (out.2.2.2.2.2 _ (outside 258 (by omega) (by omega) (by omega) (by omega))).trans ext
  have rawH : regValue (wireBlock w 1 258) z.basis=H := by
    rw [←wireBlock_append w 1 257 1,regValue_append,half,block_one_NativeFirstDirectNativeBridge]
    simp [regValue,ze]
  have avalue : signedRegValue (wireBlock w 1 258) z.basis=hValue (p : Int) (x : Int) := by
    rw [signedRegValue,wireBlock_length,rawH,signedDecode,if_pos (by omega)]
    exact hp
  have previous : z.basis (w 1797)=false :=
    (out.2.2.2.2.2 _ (outside 1797 (by omega) (by omega) (by omega) (by omega))).trans hin.cin
  have carry : regValue (wireBlock w 1540 257) z.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    rw [out.2.2.2.2.2 _ (outside i (by omega) (by omega) (by omega) (by omega))]
    exact (regValue_zero _ _).mp hin.carry _ (List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩)
  have step : SkywalkRails.step ⟨(x : Int)+(p : Int),(x : Int),false⟩=
      directTick (p : Int) (x : Int) := by
    simpa [initp,SkywalkRails.encode,SkywalkRails.signed] using secp_first_step x hx
  exact ⟨out.1,output_zero w z.basis _ _ (directTick (p : Int) (x : Int)) step
    avalue bvalue out.2.2.2.1 out.2.2.2.2.1 previous carry⟩

/-- The existing caller's clean Ext condition is used only at this seam. -/
theorem forward_native_output (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x : Nat) (hx : x<p) (s : State) (m : List Bool)
    (hin : LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) 0 x s.basis)
    (ext : s.basis (w 258)=false) :
    (run (forward w) m s).phase=s.phase ∧
    CompactSkywalkTickOutput w 0 ((x : Int)+(p : Int)) (x : Int) false
      (run (forward w) m s).basis :=
  transport_native w hn x hx s (run (forward w) m s) hin ext (forward_spec w hn x hx s m hin)

end ECDSAAdd.Arithmetic.NativeFirstDirect
end

-- source: ECDSAAdd/Arithmetic/NativeFirstDirectTickUnique.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.NativeFirstDirect

/-- Signed interpretation is injective on physical words of a fixed width. -/
theorem signed_word_unique (r : List Wire) (a b : BasisState)
    (h : signedRegValue r a=signedRegValue r b) :
    ∀q∈r,a q=b q := by
  have ha := regValue_lt r a
  have hb := regValue_lt r b
  have hm := congrArg (fun v : Int => v%((2^r.length : Nat) : Int)) h
  unfold signedRegValue at hm
  dsimp only at hm
  rw [signedDecode_emod,signedDecode_emod,←Int.natCast_emod,←Int.natCast_emod,
    Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] at hm
  have hv : regValue r a=regValue r b := by exact_mod_cast hm
  exact (regValue_eq_iff r a b).mp hv

/-- Complete state uniqueness at an unshrunk integer tick boundary. Every
carry, retained transcript flag, and spectator participates in the frame. -/
theorem native_output_state_unique (L : SkywalkIntegerLayout) (s t : State)
    (phase : s.phase=t.phase)
    (half : signedRegValue L.half s.basis=signedRegValue L.half t.basis)
    (target : signedRegValue L.b s.basis=signedRegValue L.b t.basis)
    (orientation : s.basis L.a0=t.basis L.a0)
    (history : s.basis L.history=t.basis L.history)
    (previous : s.basis L.previous=t.basis L.previous)
    (carry : regValue L.carry s.basis=regValue L.carry t.basis)
    (outside : ∀q,q∉L.wires → s.basis q=t.basis q) : s=t := by
  apply congrArg₂ State.mk phase
  have hh := signed_word_unique L.half s.basis t.basis half
  have hb := signed_word_unique L.b s.basis t.basis target
  have hc := (regValue_eq_iff L.carry s.basis t.basis).mp carry
  funext q
  by_cases hq : q∈L.wires
  · simp only [SkywalkIntegerLayout.wires,List.mem_cons,List.mem_append] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|((hq|hq)|hq)
    · exact previous
    · exact history
    · exact hh L.ext (by simp [SkywalkIntegerLayout.half])
    · exact orientation
    · exact hb L.b0 (by simp [SkywalkIntegerLayout.b])
    · exact hh q (by simp [SkywalkIntegerLayout.half,hq])
    · exact hb q (by simp [SkywalkIntegerLayout.b,hq])
    · exact hc q hq
  · exact outside q hq

end ECDSAAdd.Arithmetic.NativeFirstDirect
end

-- source: ECDSAAdd/Arithmetic/NativeFirstDirectReferenceEq.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 1024
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.NativeFirstDirect
attribute [local irreducible] run forward literalSkywalkSeed compactSkywalkTick wires

/-- The actual incumbent prefix, with its original seed and native tick. -/
def reference (w : Nat → Wire) : Program :=
  literalSkywalkSeed (literalSkywalkPoolSeed w) p++compactSkywalkTick w 0

private theorem a_inside (L : SkywalkIntegerLayout) : ∀q∈L.a,q∈L.wires := by
  intro q hq
  simp only [SkywalkIntegerLayout.a,List.mem_cons] at hq
  simp only [SkywalkIntegerLayout.wires,List.mem_cons,List.mem_append]
  tauto
private theorem b_inside (L : SkywalkIntegerLayout) : ∀q∈L.b,q∈L.wires := by
  intro q hq
  simp only [SkywalkIntegerLayout.b,List.mem_cons] at hq
  simp only [SkywalkIntegerLayout.wires,List.mem_cons,List.mem_append]
  tauto
private theorem carry_inside (L : SkywalkIntegerLayout) : ∀q∈L.carry,q∈L.wires := by
  intro q hq
  simp [SkywalkIntegerLayout.wires,hq]

private theorem first_a (w : Nat → Wire) :
    (compactSkywalkTickLayout w 0).a=wireBlock w 0 258 := by
  simpa only [compactSkywalkTickPreWidth,narrowSkywalkRouteWidth] using compactSkywalkTick_a w 0 (by omega)
private theorem first_b (w : Nat → Wire) :
    (compactSkywalkTickLayout w 0).b=wireBlock w 770 258 := by
  simpa only [compactSkywalkTickPreWidth,narrowSkywalkRouteWidth] using compactSkywalkTick_b w 0 (by omega)
private theorem first_half (w : Nat → Wire) :
    (compactSkywalkTickLayout w 0).half=wireBlock w 1 258 := by
  simpa only [compactSkywalkTickPreWidth,narrowSkywalkRouteWidth] using compactSkywalkTick_half w 0 (by omega)

private theorem retained_full (r : List Wire) (h : r.length=258) :
    (compactSkywalkSignWord r 258).retained=r := by
  rw [compactSkywalkSignWord_retained r 258 (by omega) (by omega)]
  simpa only [h] using List.take_length (l := r)
private theorem a_retained (w : Nat → Wire) :
    (compactSkywalkTickARelease w 0).retained=(compactSkywalkTickLayout w 0).half := by
  unfold compactSkywalkTickARelease
  change (compactSkywalkSignWord _ 258).retained=_
  exact retained_full _ (by rw [first_half,wireBlock_length])
private theorem b_retained (w : Nat → Wire) :
    (compactSkywalkTickBRelease w 0).retained=(compactSkywalkTickLayout w 0).b := by
  unfold compactSkywalkTickBRelease
  change (compactSkywalkSignWord _ 258).retained=_
  exact retained_full _ (by rw [first_b,wireBlock_length])

private theorem sites_inside (w : Nat → Wire) :
    prefixSites w ⊆ (compactSkywalkTickLayout w 0).wires := by
  intro q hq
  simp only [prefixSites,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with ((hq|hq)|hq)|(hq|hq)
  · apply a_inside
    rw [first_a]
    exact block_subset w 0 257 258 (by omega) q hq
  · apply b_inside
    rw [first_b]
    exact hq
  · apply carry_inside
    exact block_subset w 1540 256 257 (by omega) q hq
  · subst q
    simp [SkywalkIntegerLayout.wires,compactSkywalkTickLayout,skywalkPoolPreviousId]
  · subst q
    simp [SkywalkIntegerLayout.wires,compactSkywalkTickLayout,skywalkPoolPreviousId]

private theorem output_unique (w : Nat → Wire) (x : Nat) (s t : State)
    (phase : s.phase=t.phase)
    (a : CompactSkywalkTickOutput w 0 ((x : Int)+(p : Int)) (x : Int) false s.basis)
    (b : CompactSkywalkTickOutput w 0 ((x : Int)+(p : Int)) (x : Int) false t.basis)
    (outside : ∀q,q∉(compactSkywalkTickLayout w 0).wires → s.basis q=t.basis q) : s=t := by
  simp only [CompactSkywalkTickOutput,a_retained,b_retained] at a b
  exact native_output_state_unique _ s t phase (a.1.trans b.1.symm)
    (a.2.1.trans b.2.1.symm) (a.2.2.1.trans b.2.2.1.symm)
    (a.2.2.2.1.trans b.2.2.2.1.symm) (a.2.2.2.2.1.trans b.2.2.2.2.1.symm)
    (a.2.2.2.2.2.1.trans b.2.2.2.2.2.1.symm) outside

/-- Equality of complete states, with independent old and new measurement tapes. -/
theorem forward_reference_eq (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x : Nat) (hx : x<p) (s : State) (mNew mOld : List Bool)
    (hin : LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) 0 x s.basis)
    (ext : s.basis (w 258)=false) :
    run (forward w) mNew s=run (reference w) mOld s := by
  have hp : p<2^256 := by norm_num [p]
  have seed := literalSkywalkSeed_spec (literalSkywalkPoolSeed w) 258 p x
    (literalSkywalkPoolSeed_widths w) (literalSkywalkPoolSeed_valid w hn)
    (by omega) hp (hx.trans hp) s mOld hin
  have input := seed_first_input w hn x hx s mOld hin ext
  generalize he : run (literalSkywalkSeed (literalSkywalkPoolSeed w) p) mOld s=u at seed input
  have oddp : (p : Int)%2=1 := by norm_num [p]
  have fitX : (x : Int)<(2^257 : Int) := by exact_mod_cast (show x<2^257 from by omega)
  have fitSum : (x : Int)+(p : Int)<(2^257 : Int) := by omega
  have range : 0≤(SkywalkRails.route ((x : Int)+(p : Int)) (x : Int)).1 ∧
      (SkywalkRails.route ((x : Int)+(p : Int)) (x : Int)).1<(2^257 : Int) ∧
      0≤(SkywalkRails.route ((x : Int)+(p : Int)) (x : Int)).2 ∧
      (SkywalkRails.route ((x : Int)+(p : Int)) (x : Int)).2<(2^257 : Int) := by
    unfold SkywalkRails.route
    split_ifs <;> omega
  have old := compactSkywalkTickOutput_spec w 0 (by omega) hn
    ((x : Int)+(p : Int)) (x : Int) false (by omega)
    (by change -(2^257 : Int)≤_; omega) (by change _<(2^257 : Int); omega)
    (by change -(2^257 : Int)≤_; omega) (by change _<(2^257 : Int); omega)
    u (mOld.drop 257) input
  generalize ho : run (compactSkywalkTick w 0) (mOld.drop 257) u=v at old
  have new := forward_native_output w hn x hx s mNew hin ext
  generalize hnw : run (forward w) mNew s=z at new ⊢
  have actual : run (reference w) mOld s=v := by
    rw [reference,run_append,run_take,(literalSkywalkPoolSeed_counts w p).2.1,he,ho]
  rw [actual]
  apply output_unique w x z v (new.1.trans (old.1.trans seed.1).symm) new.2 old.2
  intro q hq
  have ns : z.basis q=s.basis q := by
    have frame := run_preserves_outside (forward w) mNew s q (fun h =>
      hq (sites_inside w (List.mem_toFinset.mp ((prefix_support w).1 h))))
    rw [hnw] at frame
    exact frame
  have ts := compactSkywalkTickOutput_frame w 0 (by omega) hn u (mOld.drop 257) q hq
  rw [ho] at ts
  have qa : q∉(literalSkywalkPoolSeed w).a := by
    intro h
    apply hq
    apply a_inside
    rw [first_a]
    exact h
  have ss := literalSkywalkSeed_preserves_outsideA (literalSkywalkPoolSeed w) 258 p x
    (literalSkywalkPoolSeed_widths w) (literalSkywalkPoolSeed_valid w hn)
    (by omega) hp (hx.trans hp) s mOld hin q qa
  rw [he] at ss
  exact ns.trans (ts.trans ss).symm

end ECDSAAdd.Arithmetic.NativeFirstDirect
end

-- source: ECDSAAdd/Arithmetic/NativeFirstDirectCallerFirstStage.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.NativeFirstDirect
open DirectSkywalk
attribute [local irreducible] run forward reference literalSkywalkSeed skywalkSeed compactSkywalkTick

/-- All first-stage history and future-clean assertions follow from the
existing caller, not from an additional promised compressed history. -/
theorem caller_first_stage (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (x y : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (hin : SkywalkArithmeticInput w x y s.basis) :
    CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 1
      (run (forward w) m s).basis := by
  have pool := skywalkShared_integer_nodup w hn
  have ready := caller_ready w hn x y s.basis hin
  have stage0 := arith_seed_stage0 w hn x y hx s [] hin
  have seedEq := directSkywalkLiteralSeed_seed_eq w hn x y hx s [] hin
  rw [←seedEq] at stage0
  have compact0 := (compactSkywalkStage_zero_iff w
    (SkywalkRails.encode false false (x:Int) (p:Int)) _).mpr stage0
  have step := compactSkywalkStageStep w pool x p 0
    (by norm_num [p]) hx0 (by norm_num [p]) (by norm_num [p]) hx
    (arith_coprime x hx0 hx) (by omega)
    (run (literalSkywalkSeed (literalSkywalkPoolSeed w) p) [] s) [] compact0
  have he := forward_reference_eq w pool x hx s m [] ready.1 ready.2
  have ref : run (reference w) [] s=
      run (compactSkywalkTick w 0) [] (run (literalSkywalkSeed (literalSkywalkPoolSeed w) p) [] s) := by
    rw [reference,run_append]
    simp only [List.take_nil,List.drop_nil]
  rw [he,ref]
  exact step.2

end ECDSAAdd.Arithmetic.NativeFirstDirect
end

-- source: ECDSAAdd/Arithmetic/NativeFirstDirectCallerForward.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.NativeFirstDirect
attribute [local irreducible] run forward reference literalSkywalkSeed compactSkywalkTick
  compressedCompactForward compressedPackAfter

private theorem first_tick_count (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) :
    measurementCount (compactSkywalkTick w 0)=257 := by
  have h := (compactSkywalkTick_counts w 0 (by omega) hn).2
  simpa only [compactSkywalkTickPostWidth,narrowSkywalkWidth] using h

private theorem first_forward_join (w : Nat → Wire) :
    compressedCompactForward w 0 512=
      compactSkywalkTick w 0++compressedCompactForward w 1 511 := by
  have zero : compressedPackAfter w 0=[] := by
    rw [compressedPackAfter,show compressedPackDue 0=false from rfl]
    rfl
  rw [compressedCompactForward,zero,List.append_nil]

/-- A first native tick takes only the fixed false prefix; the following
records remain an arbitrary independent stream, including an empty stream. -/
private theorem old_forward_eval (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (s : State) (tail : List Bool) :
    run (compressedCompactForward w 0 512) (List.replicate 257 false++tail) s=
      run (compressedCompactForward w 1 511) tail (run (compactSkywalkTick w 0) [] s) := by
  rw [first_forward_join,run_append,first_tick_count w hn]
  have take : (List.replicate 257 false++tail).take 257=List.replicate 257 false := by
    rw [List.take_append_of_le_length (by simp [List.length_replicate])]
    simpa only [List.length_replicate] using List.take_length (l := List.replicate 257 false)
  have drop : (List.replicate 257 false++tail).drop 257=tail := by
    have nil : (List.replicate 257 false).drop 257=[] := by
      simpa only [List.length_replicate] using List.drop_length (l := List.replicate 257 false)
    rw [List.drop_append,List.length_replicate,nil,Nat.sub_self,List.drop_zero,List.nil_append]
  rw [take,drop,run_replicate_false]

/-- Exact terminal State equality for the entire 512-step compressed forward
schedule. Prefix and tail measurements are independently arbitrary. -/
theorem forward_terminal_eq (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x : Nat) (hx : x<p) (s : State) (first tail : List Bool)
    (hin : LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) 0 x s.basis)
    (ext : s.basis (w 258)=false) :
    run (compressedCompactForward w 1 511) tail (run (forward w) first s)=
      run (compressedCompactForward w 0 512) (List.replicate 257 false++tail)
        (run (literalSkywalkSeed (literalSkywalkPoolSeed w) p) [] s) := by
  have hpfx := forward_reference_eq w hn x hx s first [] hin ext
  have ref : run (reference w) [] s=
      run (compactSkywalkTick w 0) []
        (run (literalSkywalkSeed (literalSkywalkPoolSeed w) p) [] s) := by
    rw [reference,run_append]
    simp only [List.take_nil,List.drop_nil]
  have firstEq := hpfx.trans ref
  exact (congrArg (fun u : State => run (compressedCompactForward w 1 511) tail u) firstEq).trans
    (old_forward_eval w hn _ tail).symm

/-- Concrete old hs1/hs2 witnesses needed by compressedPreparation_facts.
No relationship between first and tail outcome values is required. -/
theorem forward_terminal_states (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x : Nat) (hx : x<p) (s s1 s2 : State) (first tail : List Bool)
    (hin : LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) 0 x s.basis)
    (ext : s.basis (w 258)=false)
    (h1 : run (forward w) first s=s1)
    (h2 : run (compressedCompactForward w 1 511) tail s1=s2) :
    ∃ oldSeed : State,
      run (literalSkywalkSeed (literalSkywalkPoolSeed w) p) [] s=oldSeed ∧
      run (compressedCompactForward w 0 512) (List.replicate 257 false++tail) oldSeed=s2 := by
  refine ⟨run (literalSkywalkSeed (literalSkywalkPoolSeed w) p) [] s,rfl,?_⟩
  have forward := forward_terminal_eq w hn x hx s first tail hin ext
  rw [h1,h2] at forward
  exact forward.symm

end ECDSAAdd.Arithmetic.NativeFirstDirect
end

-- source: ECDSAAdd/Arithmetic/MappedCompressedStageCounts.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1
attribute [local irreducible] logicalCell dblInPlace halfInPlace copyRegister
attribute [local irreducible] compressedHistoryEncode compressedHistoryDecode
attribute [local irreducible] compactSkywalkForward compressedCompactForward compressedCompactReverse
attribute [local irreducible] toffoliCount measurementCount

private theorem renameT (f : Wire → Wire) (P : Program) :
    toffoliCount (renameProgram f P)=toffoliCount P := (renameProgram_counts f P).1
private theorem renameM (f : Wire → Wire) (P : Program) :
    measurementCount (renameProgram f P)=measurementCount P := (renameProgram_counts f P).2

theorem integer512_counts :
    toffoliCount (compressedCompactForward base 0 512)=198142 ∧
    measurementCount (compressedCompactForward base 0 512)=98858 ∧
    toffoliCount (compressedCompactReverse base 0 512)=198312 ∧
    measurementCount (compressedCompactReverse base 0 512)=98688 := by
  have recurrence := compactSkywalkForward_counts base base_pool_nodup 0 512 (by omega)
  have exactCharges := compactSkywalkForward_512_counts base base_pool_nodup
  have ht : compactSkywalkForwardT 0 512=197632 := recurrence.1.symm.trans exactCharges.1
  have hm : compactSkywalkForwardM 0 512=98688 := recurrence.2.symm.trans exactCharges.2
  have packets : compressedPackCount 0 512=170 := by rfl
  have forward := compressedCompactForward_counts base base_pool_nodup 0 512 (by omega)
  have reverse := compressedCompactReverse_counts base base_pool_nodup 0 512 (by omega)
  simpa only [ht,hm,packets,Nat.reduceMul,Nat.reduceAdd] using
    And.intro forward.1 (And.intro forward.2 reverse)

/-- The unchanged delayed codec still emits all 170 packets after tick zero. -/
theorem integer_tail_counts :
    toffoliCount (compressedCompactForward base 1 511)=197628 ∧
    measurementCount (compressedCompactForward base 1 511)=98601 ∧
    toffoliCount (compressedCompactReverse base 1 511)=197798 ∧
    measurementCount (compressedCompactReverse base 1 511)=98431 := by
  have f := compressedCompactForward_counts base base_pool_nodup 1 511 (by omega)
  have r := compressedCompactReverse_counts base base_pool_nodup 1 511 (by omega)
  have t : compactSkywalkForwardT 1 511=197118 := by decide
  have m : compactSkywalkForwardM 1 511=98431 := by decide
  have packs : compressedPackCount 1 511=170 := by decide
  simpa only [t,m,packs,Nat.reduceAdd,Nat.reduceMul] using
    And.intro f.1 (And.intro f.2 r)

theorem kernel_counts (divide : Bool) :
    toffoliCount (kernel divide)=(if divide then 1053240 else 1053750) ∧
    measurementCount (kernel divide)=724028 := by
  have f := NativeFirstDirect.forward_counts base
  have r := NativeFirstKnown.inverse_counts base
  have integer := integer_tail_counts
  have clear := skywalkTerminalClear_counts (base 511) (base 512) (base 770)
  have field := selectedFieldSegment_counts divide
  simp only [kernel,skywalkArithmeticClear,toffoliCount_append,measurementCount_append,
    f.1,f.2,r.1,r.2,integer.1,integer.2.1,integer.2.2.1,integer.2.2.2,
    clear.1,clear.2,field.1,field.2]
  cases divide <;> constructor <;> norm_num

/-- Exact emitted gate and record counts for both candidate stages. The
separate support certificate includes resident ports; caller semantics are
transported separately across the public placement changes. -/
theorem controlled_counts (divide : Bool) :
    toffoliCount (controlled divide)=(if divide then 1053750 else 1054260) ∧
    measurementCount (controlled divide)=724536 := by
  have width : (wireBlock base 0 255).length+1=(wireBlock base 770 256).length := by
    simp [wireBlock]
  have wrapped := directZeroControlled_counts (wireBlock base 770 256) (wireBlock base 0 255)
    (base 2313) (base 2411) (kernel divide) width
  have core := kernel_counts divide
  simp only [controlled] at ⊢
  rw [wrapped.1,wrapped.2,core.1,core.2,wireBlock_length]
  cases divide <;> norm_num

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/NativeFirstDirectCallerProgram.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.NativeFirstDirect
open Secp256k1 MappedCompressed CompressedAllocation
attribute [local irreducible] toffoliCount measurementCount compactSkywalkTick
  compactSkywalkReverseTick compressedCompactForward compressedCompactReverse
  selectedFieldSegment forward inverse NativeFirstKnown.inverse

/-- The new prefix and independent inverse replace seed and tick zero only.
The 511 remaining ticks and the entire codec/field schedule are unchanged. -/
def callerKernel (divide : Bool) : Program :=
  forward base ++ compressedCompactForward base 1 511 ++ skywalkArithmeticClear base ++
    selectedFieldSegment divide ++ skywalkArithmeticClear base ++
    compressedCompactReverse base 1 511 ++ NativeFirstKnown.inverse base

def callerControlled (divide : Bool) : Program :=
  directZeroControlled (wireBlock base 770 256) (wireBlock base 0 255)
    (base 2313) (base 2411) (callerKernel divide)

private theorem zero_codec (w : Nat → Wire) :
    compressedPackAfter w 0=[] ∧ compressedDecodeBefore w 0=[] := by
  constructor <;> rfl

private theorem forward_step_counts (w : Nat → Wire) (i n : Nat) :
    toffoliCount (compressedCompactForward w i (n+1))=
      toffoliCount (compactSkywalkTick w i)+toffoliCount (compressedPackAfter w i)+
        toffoliCount (compressedCompactForward w (i+1) n) ∧
    measurementCount (compressedCompactForward w i (n+1))=
      measurementCount (compactSkywalkTick w i)+measurementCount (compressedPackAfter w i)+
        measurementCount (compressedCompactForward w (i+1) n) := by
  rw [compressedCompactForward,toffoliCount_append,toffoliCount_append,
    measurementCount_append,measurementCount_append]
  exact ⟨rfl,rfl⟩

private theorem reverse_step_counts (w : Nat → Wire) (i n : Nat) :
    toffoliCount (compressedCompactReverse w i (n+1))=
      toffoliCount (compressedCompactReverse w (i+1) n)+toffoliCount (compressedDecodeBefore w i)+
        toffoliCount (compactSkywalkReverseTick w i) ∧
    measurementCount (compressedCompactReverse w i (n+1))=
      measurementCount (compressedCompactReverse w (i+1) n)+measurementCount (compressedDecodeBefore w i)+
        measurementCount (compactSkywalkReverseTick w i) := by
  rw [compressedCompactReverse,toffoliCount_append,toffoliCount_append,
    measurementCount_append,measurementCount_append]
  exact ⟨rfl,rfl⟩

theorem tail_counts :
    toffoliCount (compressedCompactForward base 1 511)=197628 ∧
    measurementCount (compressedCompactForward base 1 511)=98601 ∧
    toffoliCount (compressedCompactReverse base 1 511)=197798 ∧
    measurementCount (compressedCompactReverse base 1 511)=98431 := by
  have f := compressedCompactForward_counts base base_pool_nodup 1 511 (by omega)
  have r := compressedCompactReverse_counts base base_pool_nodup 1 511 (by omega)
  have t : compactSkywalkForwardT 1 511=197118 := by decide
  have m : compactSkywalkForwardM 1 511=98431 := by decide
  have packs : compressedPackCount 1 511=170 := by decide
  simpa only [t,m,packs,Nat.reduceAdd,Nat.reduceMul] using
    And.intro f.1 (And.intro f.2 r)

/-- Counts only. Functional caller acceptance remains a separate obligation. -/
theorem caller_counts (divide : Bool) :
    toffoliCount (callerKernel divide)=(if divide then 1053240 else 1053750) ∧
    measurementCount (callerKernel divide)=724028 ∧
    toffoliCount (callerControlled divide)=(if divide then 1053750 else 1054260) ∧
    measurementCount (callerControlled divide)=724536 := by
  have f := forward_counts base
  have r := NativeFirstKnown.inverse_counts base
  have tails := tail_counts
  have clear := skywalkTerminalClear_counts (base 511) (base 512) (base 770)
  have fields := selectedFieldSegment_counts divide
  have core : toffoliCount (callerKernel divide)=(if divide then 1053240 else 1053750) ∧
      measurementCount (callerKernel divide)=724028 := by
    simp only [callerKernel,skywalkArithmeticClear,toffoliCount_append,measurementCount_append,
      f.1,f.2,r.1,r.2,tails.1,tails.2.1,tails.2.2.1,tails.2.2.2,clear.1,clear.2,
      fields.1,fields.2]
    cases divide <;> constructor <;> norm_num
  have width : (wireBlock base 0 255).length+1=(wireBlock base 770 256).length := by
    simp [wireBlock_length]
  have ctrl := directZeroControlled_counts (wireBlock base 770 256) (wireBlock base 0 255)
    (base 2313) (base 2411) (callerKernel divide) width
  refine ⟨core.1,core.2,?_,?_⟩
  · cases divide <;> simpa only [callerControlled,core.1,wireBlock_length,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub] using ctrl.1
  · simpa only [callerControlled,core.2,wireBlock_length,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub] using ctrl.2

end ECDSAAdd.Arithmetic.NativeFirstDirect
end

-- source: ECDSAAdd/Arithmetic/NativeFirstDirectTailRestore.lean
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.NativeFirstDirect
attribute [local irreducible] run compactSkywalkForward compactSkywalkReverse
  compressedCompactReverse compressedDecodeRange compressedDecodePrefix

/-- The unchanged 511-tick reverse restores the exact first-tick pool.
Field data outside that pool may already have changed. -/
private theorem raw_tail_restore (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x prime : Nat) (hp0 : 0<prime) (hx0 : 0<x) (hpo : prime%2=1)
    (hp : prime<2^256) (hx : x<prime) (hc : x.Coprime prime)
    (initial s : State) (m : List Bool)
    (hinit : CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (prime:Int)) 1 initial.basis)
    (hfinal : CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (prime:Int)) 512 s.basis) :
    (run (compactSkywalkReverse w 1 511) m s).phase=s.phase ∧
    ∀q∈skywalkPoolWires w,(run (compactSkywalkReverse w 1 511) m s).basis q=initial.basis q := by
  let start : State := ⟨s.phase,initial.basis⟩
  have f := compactSkywalkForward_spec w hn x prime 1 511 hp0 hx0 hpo hp hx hc
    (by omega) start [] hinit
  have own := (compactSkywalkStage_terminal w hn x prime hp0 hx0 hpo hp hx hc s.basis hfinal).2
  have reference := (compactSkywalkStage_terminal w hn x prime hp0 hx0 hpo hp hx hc _ f.2).2
  have inverse := compactSkywalkReverse_roundtrip w hn x prime 1 511 hp0 hx0 hpo hp hx hc
    (by omega) start [] m hinit
  have bits : ∀q∈(skywalkPoolWires w).toFinset,
      s.basis q=(run (compactSkywalkForward w 1 511) [] start).basis q := by
    intro q hq
    exact skywalkIntegerStage_agrees w _ 512 (by omega) _ _ own reference q (List.mem_toFinset.mp hq)
  have agrees := pool_run_agrees (compactSkywalkReverse w 1 511) (skywalkPoolWires w).toFinset
    (compactSkywalkReverse_support w hn 1 511 (by omega)) m s
    (run (compactSkywalkForward w 1 511) [] start) f.1.symm bits
  rw [inverse] at agrees
  refine ⟨agrees.1,?_⟩
  intro q hq
  exact agrees.2 q (List.mem_toFinset.mpr hq)

private theorem decode_zero_step (w : Nat → Wire) (n : Nat) :
    compressedDecodeRange w 0 (n+1)=compressedDecodeRange w 1 n ++ compressedDecodeBefore w 0 := by
  rw [compressedDecodeRange]

private theorem tail_decoder (w : Nat → Wire) :
    compressedDecodeRange w 1 511=compressedDecodePrefix w 512 := by
  have h := compressedDecodeRange_zero w 512
  have zero : compressedDecodeBefore w 0=[] := rfl
  rw [decode_zero_step w 511,zero,List.append_nil] at h
  exact h

theorem tail_restore_pool (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (hlo : CompressedHistoryAbove w) (x prime : Nat)
    (hp0 : 0<prime) (hx0 : 0<x) (hpo : prime%2=1)
    (hp : prime<2^256) (hx : x<prime) (hc : x.Coprime prime)
    (initial s : State) (m : List Bool)
    (hinit : CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (prime:Int)) 1 initial.basis)
    (hfinal : CompressedCompactStage w x prime 512 s.basis) :
    (run (compressedCompactReverse w 1 511) m s).phase=s.phase ∧
    (∀q∈skywalkPoolWires w,(run (compressedCompactReverse w 1 511) m s).basis q=initial.basis q) ∧
    (∀q,q∉skywalkPoolWires w → (run (compressedCompactReverse w 1 511) m s).basis q=s.basis q) := by
  have decoded := compressedCompactStage_decoded w hn hlo x prime 512 hp0 hpo (by omega) s hfinal
  have restored := raw_tail_restore w hn x prime hp0 hx0 hpo hp hx hc
    initial (run (compressedDecodePrefix w 512) [] s) m hinit decoded.2
  have actual : run (compressedCompactReverse w 1 511) m s=
      run (compactSkywalkReverse w 1 511) m (run (compressedDecodePrefix w 512) [] s) := by
    rw [compressedCompactReverse_normalize w hn hlo 1 511 (by omega),tail_decoder,
      run_append,compressedDecodePrefix_measurements,List.take_zero,List.drop_zero]
  refine ⟨?_,?_,?_⟩
  · rw [actual]; exact restored.1.trans decoded.1
  · rw [actual]; exact restored.2
  · intro q hq
    exact compressedCompactReverse_frame w hn hlo 1 511 (by omega) s m q hq

end ECDSAAdd.Arithmetic.NativeFirstDirect
end

-- source: ECDSAAdd/Arithmetic/NativeFirstKnownFrame.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Arithmetic.NativeFirstKnown
open NativeFirstDirect
attribute [local irreducible] run hAdd kAdd mappedAdd hReceiver

private theorem contained (w : Nat → Wire) (a n b m : Nat)
    (lo : b≤a) (hi : a+n≤b+m) :
    ∀q∈wireBlock w a n,q∈wireBlock w b m := by
  intro q hq
  obtain ⟨i,hi',rfl⟩ := List.mem_map.mp hq
  exact List.mem_map.mpr ⟨i,by
    simp only [List.mem_range'_1] at hi' ⊢
    omega,rfl⟩

private theorem one_block (w : Nat → Wire) (a : Nat) : wireBlock w a 1=[w a] := by
  simp [wireBlock,List.range']

/-- This physical witness is produced by the existing clean copy. No bound on
the B value or a ghost original-x register is required. -/
theorem front_known_sum (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (s : State) (m : List Bool)
    (ha : regValue (wireBlock w 1 256) s.basis=0) :
    mappedValue (desired w) (run (inverseFront w) m s).basis=
      regValue (wireBlock w 4 253) (run (inverseFront w) m s).basis := by
  let P : Program := [.CX (w 770) (w 1028),.CX (w 1028) (w 0),.X (w 0)]
  let t := run P m s
  let u := run (lowCopy w) m t
  have pm : measurementCount P=0 := rfl
  have front : run (inverseFront w) m s=u := by
    rw [inverseFront,run_append,run_take,pm,List.drop_zero]
  have flags_keep (i : Nat) (hi : i<1798)
      (sep : i≠0 ∧ i≠770 ∧ i≠1028) : t.basis (w i)=s.basis (w i) := by
    apply run_preserves_outside P m s
    have h0 := index_ne w hn i 0 hi (by omega) sep.1
    have hB := index_ne w hn i 770 hi (by omega) sep.2.1
    have hQ := index_ne w hn i 1028 hi (by omega) sep.2.2
    simp [P,wires,Instr.wires,h0,hB,hQ]
  have cleanT : regValue (wireBlock w 1 256) t.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    rw [flags_keep i (by omega) (by omega)]
    exact (regValue_zero _ _).mp ha _ (List.mem_map.mpr ⟨i,by simpa only [List.mem_range'_1] using hi,rfl⟩)
  have copy := copyRegister_correct none (wireBlock w 771 255) (wireBlock w 1 255)
    (by simp [wireBlock_length]) (copy_inputs_nd w hn) (by simp) t m
  have dest0 : regValue (wireBlock w 1 255) t.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    exact (regValue_zero _ _).mp cleanT q (block_subset w 1 255 256 (by omega) q hq)
  have value : regValue (wireBlock w 1 255) u.basis=regValue (wireBlock w 771 255) t.basis := by
    simpa only [lowCopy,copyValue,dest0,Nat.zero_xor] using copy.2.2
  have outside : ∀q,q∉wireBlock w 1 255 → u.basis q=t.basis q := by
    simpa only [lowCopy] using copy.2.1
  have source : regValue (wireBlock w 771 255) u.basis=regValue (wireBlock w 771 255) t.basis := by
    apply regValue_congr
    intro q hq
    exact outside q (List.disjoint_left.mp
      (block_disjoint w hn 771 255 1 255 (by omega) (by omega) (by omega)) hq)
  have equality := value.trans source.symm
  rw [←wireBlock_append w 1 3 252,←wireBlock_append w 771 3 252,
    regValue_append,regValue_append,wireBlock_length,wireBlock_length] at equality
  have lowA := regValue_lt (wireBlock w 1 3) u.basis
  have lowB := regValue_lt (wireBlock w 771 3) u.basis
  rw [wireBlock_length] at lowA lowB
  have upper : regValue (wireBlock w 4 252) u.basis=regValue (wireBlock w 774 252) u.basis := by
    norm_num only [Nat.reducePow] at equality lowA lowB
    omega
  have top : u.basis (w 256)=false := by
    rw [outside _ (block_not_mem w hn 256 1 255 (by omega) (by omega) (by omega))]
    exact (regValue_zero _ _).mp cleanT _ (List.mem_map.mpr ⟨256,by simp [List.mem_range'_1],rfl⟩)
  have topValue : regValue (wireBlock w 256 1) u.basis=0 := by
    simp [one_block,regValue,top]
  rw [front,desired_value,←wireBlock_append w 4 252 1,regValue_append,topValue,
    Nat.mul_zero,Nat.add_zero]
  exact upper.symm

theorem hReceiver_after_forward (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (u : State) (mF mI : List Bool)
    (hc : ∀q∈wireBlock w 1540 252,u.basis q=false)
    (cin : u.basis (w 1797)=false)
    (known : mappedValue (desired w) u.basis=regValue (wireBlock w 4 253) u.basis) :
    run (hReceiver w) mI (run (hAdd w false) mF u)=u := by
  let v := run (hAdd w false) mF u
  have forward := hAdd_spec w false u mF (h_inputs_nd w hn) (h_sources_fresh w hn false) hc
  have carryAway (q : Wire) (hq : q∈wireBlock w 1540 252) : q∉wireBlock w 4 253 :=
    List.disjoint_right.mp (block_disjoint w hn 4 253 1540 252 (by omega) (by omega) (by omega)) hq
  have vc : ∀q∈wireBlock w 1540 252,v.basis q=false := by
    intro q hq
    exact (forward.2.1 q (carryAway q hq)).trans (hc q hq)
  have cancel := hAdd_cancel w u mF mI (h_inputs_nd w hn)
    (fun i => h_sources_fresh w hn i)
    (block_not_mem w hn 1028 4 253 (by omega) (by omega) (by omega)) hc cin
  have inverseSpec := mappedAdd_correct (hBits w true) (wireBlock w 4 253)
    (wireBlock w 1540 252) (w 1797) (h_inputs_nd w hn) (h_sources_fresh w hn true)
    (by simp [hBits_length,wireBlock_length]) (by simp [wireBlock_length]) v mI vc
  have sum : (mappedValue (hBits w true) v.basis+regValue (wireBlock w 4 253) v.basis+
      (v.basis (w 1797)).toNat)%2^253=regValue (wireBlock w 4 253) u.basis := by
    have value := inverseSpec.2.2
    rw [← hAdd] at value
    rw [cancel] at value
    simpa only [wireBlock_length] using value.symm
  have witness : mappedValue (desired w) v.basis=mappedValue (desired w) u.basis := by
    apply mappedValue_congr
    intro q hq
    have fresh := desired_fresh w hn q hq
    exact forward.2.1 q (fun bad => fresh (by simp [bad]))
  have ready : mappedValue (desired w) v.basis=
      (mappedValue (hBits w true) v.basis+regValue (wireBlock w 4 253) v.basis+
        (v.basis (w 1797)).toNat)%2^253 := witness.trans (known.trans sum.symm)
  rw [hReceiver_eq w hn v mI vc ready]
  exact cancel

end ECDSAAdd.Arithmetic.NativeFirstKnown
end

-- source: ECDSAAdd/Arithmetic/NativeFirstKnownInverse.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.NativeFirstKnown
open NativeFirstDirect
attribute [local irreducible] run mappedAdd hAdd kAdd kTail NativeFirstDirect.forward NativeFirstDirect.inverse inverse hReceiver

private theorem copy_away (w : Nat → Wire) (q : Wire)
    (hs : q∉wireBlock w 771 255) (hd : q∉wireBlock w 1 255) :
    q∉wires (lowCopy w) := by
  rw [lowCopy,copyRegister_wires none (wireBlock w 771 255) (wireBlock w 1 255)
    (by simp [wireBlock_length])]
  split_ifs
  · simp
  · simpa only [Option.toList_none,List.nil_append,List.mem_toFinset,
      List.mem_append,not_or] using And.intro hs hd

private theorem front_away (w : Nat → Wire) (q : Wire)
    (h0 : q≠w 0) (hb : q≠w 770) (he : q≠w 1028)
    (hs : q∉wireBlock w 771 255) (hd : q∉wireBlock w 1 255) :
    q∉wires (inverseFront w) := by
  have flags : q∉wires [.CX (w 770) (w 1028),.CX (w 1028) (w 0),.X (w 0)] := by
    simp [wires,Instr.wires,h0,hb,he]
  rw [inverseFront,wires_append,Finset.mem_union,not_or]
  exact ⟨flags,copy_away w q hs hd⟩

private theorem middle_away (w : Nat → Wire) (q : Wire)
    (hb : q≠w 770) (he : q≠w 1028) (hr : q∉wireBlock w 770 258) :
    q∉wires (inverseMiddle w) := by
  have first : q∉wires [.CX (w 1028) (w 770)] := by
    simp [wires,Instr.wires,hb,he]
  have rot : q∉wires (rotateRight (wireBlock w 770 258)) := by
    rw [(rotate_wires (wireBlock w 770 258)).1]
    split_ifs
    · simp
    · simpa only [List.mem_toFinset] using hr
  rw [inverseMiddle,wires_append,Finset.mem_union,not_or]
  exact ⟨first,rot⟩

private theorem state_of_value_frame (r : List Wire) (s t : State)
    (hp : t.phase=s.phase) (hv : regValue r t.basis=regValue r s.basis)
    (he : ∀q,q∉r → t.basis q=s.basis q) : t=s := by
  apply congrArg₂ State.mk hp
  funext q
  by_cases hq : q∈r
  · exact (regValue_eq_iff r _ _).mp hv q hq
  · exact he q hq

private theorem copy_cancel (src dst : List Wire) (hl : src.length=dst.length)
    (hn : (src++dst).Nodup) (s : State) (m n : List Bool) :
    run (copyRegister none src dst) n (run (copyRegister none src dst) m s)=s := by
  have f := copyRegister_correct none src dst hl hn (by simp) s m
  have i := copyRegister_correct none src dst hl hn (by simp)
    (run (copyRegister none src dst) m s) n
  have srcKeep := regValue_congr src (run (copyRegister none src dst) m s).basis s.basis
    (fun q hq => f.2.1 q (List.disjoint_left.mp (List.nodup_append'.mp hn).2.2 hq))
  apply state_of_value_frame dst s _ (i.1.trans f.1)
  · rw [i.2.2,f.2.2]
    simp only [copyValue]
    rw [srcKeep,Nat.xor_assoc,Nat.xor_self,Nat.xor_zero]
  · intro q hq; exact (i.2.1 q hq).trans (f.2.1 q hq)

private theorem rotate_reverse (r : List Wire) :
    (rotateRight r).reverse=rotateLeft r := by
  induction r with
  | nil => rfl
  | cons a r ih =>
    cases r with
    | nil => rfl
    | cons b r =>
      rw [rotateRight,rotateLeft,List.reverse_append,ih]
      rfl
private theorem rotate_proper (r : List Wire) (hn : r.Nodup) :
    ProperProgram (rotateRight r) := by
  induction r with
  | nil => simp [rotateRight,ProperProgram]
  | cons a r ih =>
    cases r with
    | nil => simp [rotateRight,ProperProgram]
    | cons b r =>
      have nd := List.nodup_cons.mp hn
      have ne : a≠b := fun h => nd.1 (by simp [h])
      exact (properProgram_append _ _).mpr
        ⟨by simp [swapBits,ProperProgram,ProperGate,ne,Ne.symm ne],ih nd.2⟩
private theorem rotate_cancel (r : List Wire) (hn : r.Nodup) (s : State) (m n : List Bool) :
    run (rotateLeft r) n (run (rotateRight r) m s)=s := by
  rw [←rotate_reverse]
  exact run_reverse_proper _ (rotate_proper r hn) s m n

private theorem front_cancel (w : Nat → Wire) (s : State) (m n : List Bool)
    (hn : (wireBlock w 771 255++wireBlock w 1 255).Nodup)
    (h0 : w 770≠w 1028) (h1 : w 1028≠w 0) :
    run (inverseBack w) n (run (inverseFront w) m s)=s := by
  let P : Program := [.CX (w 770) (w 1028),.CX (w 1028) (w 0),.X (w 0)]
  have hp : ProperProgram P := by simp [P,ProperProgram,ProperGate,h0,h1]
  have c := copy_cancel (wireBlock w 771 255) (wireBlock w 1 255)
    (by simp [wireBlock_length]) hn (run P m s) m n
  have hm : measurementCount P=0 := properProgram_measurementCount P hp
  have cm := (lowCopy_counts w).2
  change run (lowCopy w++P.reverse) n (run (P++lowCopy w) m s)=s
  rw [run_append,run_take,run_append,run_take,hm,cm,List.drop_zero]
  simp only [List.drop_zero]
  rw [show run (lowCopy w) n (run (lowCopy w) m (run P m s))=run P m s from c]
  exact run_reverse_proper P hp s m n

private theorem middle_cancel (w : Nat → Wire) (s : State) (m n : List Bool)
    (hn : (wireBlock w 770 258).Nodup) (hne : w 1028≠w 770) :
    run (inverseUnmiddle w) n (run (inverseMiddle w) m s)=s := by
  rw [inverseUnmiddle,inverseMiddle,run_append,run_take,run_append,run_take,
    (rotate_counts (wireBlock w 770 258)).2.2.2,
    show measurementCount [.CX (w 1028) (w 770)]=0 from rfl,List.drop_zero]
  rw [rotate_cancel _ hn]
  exact properGate_involution (.CX (w 1028) (w 770)) hne s m n


theorem inverse_roundtrip (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x : Nat) (s : State) (mF mI : List Bool)
    (ready : LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) 0 x s.basis) :
    run (NativeFirstKnown.inverse w) mI (run (NativeFirstDirect.forward w) mF s)=s := by
  let u := run (inverseFront w) mF s
  let v := run (hAdd w false) mF u
  let z := run (inverseMiddle w) (mF.drop 252) v
  have initialCarry : regValue (wireBlock w 1540 257) s.basis=0 := ready.carry
  have clean : ∀q∈wireBlock w 1540 256,s.basis q=false := by
    intro q hq
    exact (regValue_zero _ _).mp initialCarry q
      (block_subset w 1540 256 257 (by omega) q hq)
  have aClean : regValue (wireBlock w 1 256) s.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    have initialA : regValue (wireBlock w 0 258) s.basis=0 := ready.a
    exact (regValue_zero _ _).mp initialA _
      (List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩)
  have frontCarryAway : ∀q∈wireBlock w 1540 256,q∉wires (inverseFront w) := by
    intro q hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hj
    exact front_away w (w j)
      (index_ne w hn j 0 (by omega) (by omega) (by omega))
      (index_ne w hn j 770 (by omega) (by omega) (by omega))
      (index_ne w hn j 1028 (by omega) (by omega) (by omega))
      (block_not_mem w hn j 771 255 (by omega) (by omega) (by omega))
      (block_not_mem w hn j 1 255 (by omega) (by omega) (by omega))
  have uc : ∀q∈wireBlock w 1540 256,u.basis q=false := by
    intro q hq
    exact (run_preserves_outside _ mF s q (frontCarryAway q hq)).trans (clean q hq)
  have ui : u.basis (w 1797)=false := by
    apply Eq.trans (run_preserves_outside _ mF s _ ?_) ready.cin
    exact front_away w (w 1797)
      (index_ne w hn 1797 0 (by omega) (by omega) (by omega))
      (index_ne w hn 1797 770 (by omega) (by omega) (by omega))
      (index_ne w hn 1797 1028 (by omega) (by omega) (by omega))
      (block_not_mem w hn 1797 771 255 (by omega) (by omega) (by omega))
      (block_not_mem w hn 1797 1 255 (by omega) (by omega) (by omega))
  have ha := hAdd_spec w false u mF (h_inputs_nd w hn)
    (h_sources_fresh w hn false)
    (fun q hq => uc q (block_subset w 1540 252 256 (by omega) q hq))
  have vc : ∀q∈wireBlock w 1540 256,v.basis q=false := by
    intro q hq
    have away : q∉wireBlock w 4 253 :=
      List.disjoint_right.mp
        (block_disjoint w hn 4 253 1540 256 (by omega) (by omega) (by omega)) hq
    exact (ha.2.1 q away).trans (uc q hq)
  have zc : ∀q∈wireBlock w 1540 256,z.basis q=false := by
    intro q hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hj
    have away := middle_away w (w j)
      (index_ne w hn j 770 (by omega) (by omega) (by omega))
      (index_ne w hn j 1028 (by omega) (by omega) (by omega))
      (block_not_mem w hn j 770 258 (by omega) (by omega) (by omega))
    exact (run_preserves_outside _ _ v _ away).trans (vc _
      (List.mem_map.mpr ⟨j,by simpa only [List.mem_range'_1] using hj,rfl⟩))
  have kflag : w 1028∉w 770::wireBlock w 771 257 := by
    simp only [List.mem_cons,not_or]
    exact ⟨index_ne w hn 1028 770 (by omega) (by omega) (by omega),
      block_not_mem w hn 1028 771 257 (by omega) (by omega) (by omega)⟩
  have kc := kAdd_cancel w z (mF.drop 252) mI (k_inputs_nd w hn)
    (fun i => k_sources_fresh w hn i) kflag zc
  have mc := middle_cancel w v (mF.drop 252) (mI.drop 256)
    (block_nodup w hn 770 258 (by omega))
    (index_ne w hn 1028 770 (by omega) (by omega) (by omega))
  have hh := hReceiver_after_forward w hn u mF (mI.drop 256)
    (fun q hq => uc q (block_subset w 1540 252 256 (by omega) q hq)) ui
    (front_known_sum w hn s mF aClean)
  have fm : measurementCount (inverseFront w)=0 := by
    simp [inverseFront,measurementCount_append,measurementCount,(lowCopy_counts w).2]
  have mm : measurementCount (inverseMiddle w)=0 := by
    simp [inverseMiddle,measurementCount_append,measurementCount,(rotate_counts _).2.1]
  have um : measurementCount (inverseUnmiddle w)=0 := by
    simp [inverseUnmiddle,measurementCount_append,measurementCount,(rotate_counts _).2.2.2]
  have fr : NativeFirstDirect.forward w=
      inverseFront w++(hAdd w false++(inverseMiddle w++kAdd w false)) := by
    simp only [NativeFirstDirect.forward,inverseFront,inverseMiddle,List.append_assoc]
  have ir : NativeFirstKnown.inverse w=
      kAdd w true++(inverseUnmiddle w++(hReceiver w++inverseBack w)) := by
    simp only [NativeFirstKnown.inverse,List.append_assoc]
  have fRun : run (NativeFirstDirect.forward w) mF s=
      run (kAdd w false) (mF.drop 252) z := by
    rw [fr,run_append,run_take,fm,List.drop_zero]
    rw [run_append,run_take,(hAdd_counts w false).2]
    rw [run_append,run_take,mm,List.drop_zero]
  have iRun (t : State) : run (NativeFirstKnown.inverse w) mI t=
      run (inverseBack w) ((mI.drop 256).drop 252)
        (run (hReceiver w) (mI.drop 256)
          (run (inverseUnmiddle w) (mI.drop 256) (run (kAdd w true) mI t))) := by
    rw [ir,run_append,run_take,(kAdd_counts w true).2]
    rw [run_append,run_take,um,List.drop_zero]
    rw [run_append,run_take,(hReceiver_counts w).2]
  rw [iRun,fRun,kc,mc,hh]
  exact front_cancel w s _ _ (copy_inputs_nd w hn)
    (index_ne w hn 770 1028 (by omega) (by omega) (by omega))
    (index_ne w hn 1028 0 (by omega) (by omega) (by omega))

/-- Convenient replacement equality only on the clean forward image. -/
theorem inverse_eq_old_on_forward (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (x : Nat) (s : State) (mF mI : List Bool)
    (ready : LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) 0 x s.basis) :
    run (NativeFirstKnown.inverse w) mI (run (NativeFirstDirect.forward w) mF s)=
      run (NativeFirstDirect.inverse w) mI (run (NativeFirstDirect.forward w) mF s) := by
  rw [inverse_roundtrip w hn x s mF mI ready,
    NativeFirstDirect.inverse_forward_ready w hn x s mF mI ready]

theorem inverse_restore_after_outside (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (x : Nat)
    (initial field : State) (mF mI : List Bool)
    (hin : LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) 0 x initial.basis)
    (hphase : field.phase=(run (NativeFirstDirect.forward w) mF initial).phase)
    (hpool : ∀q∈skywalkPoolWires w,
      field.basis q=(run (NativeFirstDirect.forward w) mF initial).basis q) :
    (run (NativeFirstKnown.inverse w) mI field).phase=initial.phase ∧
    (∀q∈skywalkPoolWires w,
      (run (NativeFirstKnown.inverse w) mI field).basis q=initial.basis q) ∧
    (∀q,q∉skywalkPoolWires w →
      (run (NativeFirstKnown.inverse w) mI field).basis q=field.basis q) := by
  have support : wires (NativeFirstKnown.inverse w)⊆(skywalkPoolWires w).toFinset := by
    intro q hq
    exact List.mem_toFinset.mpr (prefix_pool_subset w
      (List.mem_toFinset.mp (NativeFirstKnown.inverse_support w hq)))
  have restored := inverse_roundtrip w hn x initial mF mI hin
  have agrees := pool_run_agrees (NativeFirstKnown.inverse w)
    (skywalkPoolWires w).toFinset support mI
    field (run (NativeFirstDirect.forward w) mF initial) hphase
    (fun q hq => hpool q (List.mem_toFinset.mp hq))
  rw [restored] at agrees
  refine ⟨agrees.1,?_,?_⟩
  · intro q hq
    exact agrees.2 q (List.mem_toFinset.mpr hq)
  · intro q hq
    exact run_preserves_outside (NativeFirstKnown.inverse w) mI field q
      (fun h => hq (List.mem_toFinset.mp (support h)))

end ECDSAAdd.Arithmetic.NativeFirstKnown
end

-- source: ECDSAAdd/Arithmetic/NativeFirstDirectCallerStates.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.NativeFirstDirect
open Secp256k1 DirectSkywalk OffsetBorrowedCanonical CompressedFieldSupport MappedCompressed
attribute [local irreducible] run measurementCount forward inverse NativeFirstKnown.inverse reference callerKernel
  literalSkywalkSeed compressedCompactForward compressedCompactReverse selectedFieldSegment
  skywalkArithmeticClear allGroupEncode SkywalkTrace.next Nat.iterate

/-- Pure intermediate helper: the first-stage witness is discharged by the
actual new prefix in the public theorem below. No phase/frame callback occurs. -/
private theorem kernel_states_from_first (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0 < x) (hx : x < p) (s : State)
    (m1 m2 m3 m4 m5 m6 m7 : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409) = false) (hs0 : s.basis (base 2410) = false)
    (s1 s2 s3 s4 s5 s6 s7 : State)
    (hs1 : run (forward base) m1 s = s1)
    (hs2 : run (compressedCompactForward base 1 511) m2 s1 = s2)
    (hs3 : run (skywalkArithmeticClear base) m3 s2 = s3)
    (hs4 : run (selectedFieldSegment divide) m4 s3 = s4)
    (hs5 : run (skywalkArithmeticClear base) m5 s4 = s5)
    (hs6 : run (compressedCompactReverse base 1 511) m6 s5 = s6)
    (hs7 : run (NativeFirstKnown.inverse base) m7 s6 = s7)
    (first : CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s1.basis) :
    DirectSkywalkArithmeticStrong divide base (base 2400) x Y s s7 := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  let L := skywalkSharedSeed base
  let F := skywalkSharedField base
  let Z := (directSkywalkResult divide (s.basis (base 2400)) x Y).val
  have hp0 : 0<p := by norm_num [p]
  have hpo : p%2=1 := by norm_num [p]
  have hp : p<2^256 := by norm_num [p]
  have cop := arith_coprime x hx0 hx
  have pool := skywalkShared_integer_nodup base hn
  have ready := caller_ready base hn x Y.val s.basis hin
  have prefixPhase := forward_native_output base pool x hx s m1 ready.1 ready.2
  rw [hs1] at prefixPhase
  obtain ⟨oldSeed,seedEq,fullEq⟩ := forward_terminal_states base pool x hx s s1 s2
    m1 m2 ready.1 ready.2 hs1 hs2
  have oldhsSeed := (directSkywalkLiteralSeed_seed_eq base hn x Y.val hx s [] hin).symm.trans seedEq
  have seed := skywalkSeed_spec L 258 p x (skywalkShared_seed_widths base)
    (skywalkShared_seed_nodup base hn) (by omega) hp (hx.trans hp)
    s [] (arith_seed_input base hn x Y.val s.basis hin)
  rw [oldhsSeed] at seed
  have stage0 := arith_seed_stage0 base hn x Y.val hx s [] hin
  rw [oldhsSeed] at stage0
  have terminal := compressedCompactForward_512_spec base pool hlo x p hp0 hx0 hpo hp hx cop
    oldSeed (List.replicate 257 false++m2) stage0
  rw [fullEq] at terminal
  obtain ⟨origin,facts,_,encoded,entry⟩ := compressedPreparation_facts hn hlo ho x Y hx0 hx s
    [] (List.replicate 257 false++m2) m3 hin oldSeed s2 s3 seedEq fullEq hs3
  have selectorPool : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base := by
    intro q hq bad
    exact ho q hq (arith_block_subset_shared base 0 1798 (by omega) bad)
  have hg : origin.basis (base 2409)=false := (facts.controls _ (by simp)).trans hg0
  have hs : origin.basis (base 2410)=false := (facts.controls _ (by simp)).trans hs0
  have h4 := selectedFieldSegment_spec divide hn hlo ho selectorPool hf origin.basis hg hs
    facts.env facts.legal facts.workZero facts.unusedZero facts.targetHigh facts.sourceHigh
    x hx0 hx facts.trace Y s3 m4 entry
  rw [hs4] at h4
  have actual4 := encodedCanonical_caller_frame hn hlo origin.basis facts.sourceZero _ s4 h4.2
  have result : fieldResult divide origin.basis x Y = directSkywalkResult divide (s.basis (base 2400)) x Y := by
    simp only [fieldResult,directSkywalkResult,skywalkArithmeticResult,
      facts.controls (base 2400) (by simp)]
  have value4 : regValue F.z s4.basis=Z := by
    rw [result] at actual4
    exact actual4.1
  have keeps := selectedFieldSegment_pool_frame divide hn hlo ho selectorPool hf origin.basis hg hs
    facts.env facts.legal facts.workZero facts.unusedZero facts.targetHigh facts.sourceHigh
    facts.sourceZero x hx0 hx facts.trace Y s3 m4 entry
  rw [hs4] at keeps
  have recovered := clear_after_pool_update hn s2 s4 m3 m5
    (by rw [hs3]; exact keeps.1) (by intro q hq; rw [hs3]; exact keeps.2 q hq)
  rw [hs5] at recovered
  have restored := tail_restore_pool base pool hlo x p hp0 hx0 hpo hp hx cop
    s1 s2 m6 first terminal.2
  have agrees := pool_run_agrees (compressedCompactReverse base 1 511) (skywalkPoolWires base).toFinset
    (compressedCompactReverse_support base pool hlo 1 511 (by omega)) m6 s5 s2 recovered.1
    (fun q hq => recovered.2 q (List.mem_toFinset.mp hq))
  rw [hs6] at agrees
  have phase6 : s6.phase=s1.phase :=
    agrees.1.trans (restored.1.trans ((terminal.1.trans seed.1).trans prefixPhase.1.symm))
  have pool6 : ∀q∈skywalkPoolWires base,s6.basis q=s1.basis q := by
    intro q hq
    exact (agrees.2 q (List.mem_toFinset.mpr hq)).trans (restored.2.1 q hq)
  have h7 := NativeFirstKnown.inverse_restore_after_outside base pool x s s6 m1 m7 ready.1
    (by rw [hs1]; exact phase6)
    (by intro q hq; rw [hs1]; exact pool6 q hq)
  rw [hs7] at h7
  have reverseAway (q : Wire) (hq : q∉skywalkPoolWires base) : s6.basis q=s5.basis q := by
    have a := compressedCompactReverse_frame base pool hlo 1 511 (by omega) s5 m6 q hq
    rw [hs6] at a
    exact a
  have frame7Z (q : Wire) (hz : q∉F.z) : s7.basis q=s.basis q := by
    by_cases hpool : q∈skywalkPoolWires base
    · exact h7.2.1 q hpool
    · have k5 := arith_clear_outside base hn s4 m5 q hpool
      have k3 := arith_clear_outside base hn s2 m3 q hpool
      have k2 := compressedCompactForward_frame base pool hlo 1 511 (by omega) s1 m2 q hpool
      have kEncode : s3.basis q=origin.basis q := by
        rw [encoded]
        exact run_preserves_outside _ [] origin q
          (fun used => hpool (List.mem_toFinset.mp (caller_encoder_pool_support hn hlo used)))
      have k1 : s1.basis q=s.basis q := by
        have a := run_preserves_outside (forward base) m1 s q (fun used => hpool
          (prefix_pool_subset base (List.mem_toFinset.mp ((prefix_support base).1 used))))
        rw [hs1] at a
        exact a
      rw [hs5] at k5
      rw [hs3] at k3
      rw [hs2] at k2
      exact (h7.2.2 q hpool).trans ((reverseAway q hpool).trans (k5.trans
        ((actual4.2 q hz hpool).trans (kEncode.symm.trans (k3.trans (k2.trans k1))))))
  have hz7 : regValue F.z s7.basis=Z := by
    apply Eq.trans (regValue_congr _ _ _ ?_) value4
    intro q hq
    have away : q∉skywalkPoolWires base := fun h => arith_pool_away_z base hn q h hq
    have k5 := arith_clear_outside base hn s4 m5 q away
    rw [hs5] at k5
    exact (h7.2.2 q away).trans ((reverseAway q away).trans k5)
  have hZ : Z<2^256 := (ZMod.val_lt (directSkywalkResult divide (s.basis (base 2400)) x Y)).trans hp
  have high := skywalkShared_numerator_high_zero base s7.basis Z hz7 hZ
  have low7 : regValue (skywalkArithmeticNumerator base) s7.basis=Z := by
    change regValue (wireBlock base 2056 256++[base 2312]) s7.basis=Z at hz7
    rw [regValue_append] at hz7
    simpa [regValue,high,skywalkArithmeticNumerator] using hz7
  refine ⟨h7.1,low7,?_⟩
  intro q hq
  by_cases hz : q∈F.z
  · change q∈wireBlock base 2056 256++[base 2312] at hz
    rcases List.mem_append.mp hz with hlow|hpad
    · exact False.elim (hq hlow)
    · have eq : q=base 2312 := by simpa using hpad
      subst q
      exact high.trans (arith_input_bit base hn x Y.val s.basis hin 2312 (by omega) (by omega) (by omega)).symm
  · exact frame7Z q hz

/-- Public exact seven-stage contract, with no new caller premises. -/
theorem kernel_states (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0 < x) (hx : x < p) (s : State)
    (m1 m2 m3 m4 m5 m6 m7 : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409) = false) (hs0 : s.basis (base 2410) = false)
    (s1 s2 s3 s4 s5 s6 s7 : State)
    (hs1 : run (forward base) m1 s=s1)
    (hs2 : run (compressedCompactForward base 1 511) m2 s1=s2)
    (hs3 : run (skywalkArithmeticClear base) m3 s2=s3)
    (hs4 : run (selectedFieldSegment divide) m4 s3=s4)
    (hs5 : run (skywalkArithmeticClear base) m5 s4=s5)
    (hs6 : run (compressedCompactReverse base 1 511) m6 s5=s6)
    (hs7 : run (NativeFirstKnown.inverse base) m7 s6=s7) :
    DirectSkywalkArithmeticStrong divide base (base 2400) x Y s s7 := by
  have first := caller_first_stage base hn x Y.val hx0 hx s m1 hin
  rw [hs1] at first
  exact kernel_states_from_first divide hn hlo ho hf x Y hx0 hx s m1 m2 m3 m4 m5 m6 m7
    hin hg0 hs0 s1 s2 s3 s4 s5 s6 s7 hs1 hs2 hs3 hs4 hs5 hs6 hs7 first

/-- Interpreter composition keeps every independent record split explicit. -/
theorem kernel_spec (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0 < x) (hx : x < p) (s : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false) :
    DirectSkywalkArithmeticStrong divide base (base 2400) x Y s (run (callerKernel divide) m s) := by
  let P : State → State → Prop := fun initial out =>
    SkywalkArithmeticInput base x Y.val initial.basis →
    initial.basis (base 2409)=false → initial.basis (base 2410)=false →
    DirectSkywalkArithmeticStrong divide base (base 2400) x Y initial out
  have all := skywalkRunSeven (forward base) (compressedCompactForward base 1 511)
    (skywalkArithmeticClear base) (selectedFieldSegment divide) (skywalkArithmeticClear base)
    (compressedCompactReverse base 1 511) (NativeFirstKnown.inverse base) P
    (by
      intro initial s1 s2 s3 s4 s5 s6 s7 m1 m2 m3 m4 m5 m6 m7 h1 h2 h3 h4 h5 h6 h7 input hg hs
      exact kernel_states divide hn hlo ho hf x Y hx0 hx initial m1 m2 m3 m4 m5 m6 m7
        input hg hs s1 s2 s3 s4 s5 s6 s7 h1 h2 h3 h4 h5 h6 h7) s m
  simpa only [callerKernel,List.append_assoc] using all hin hg0 hs0

end ECDSAAdd.Arithmetic.NativeFirstDirect
end

-- source: ECDSAAdd/Arithmetic/MappedCompressedCallerRun.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1
attribute [local irreducible] run measurementCount literalSkywalkSeed literalSkywalkUnseed
  compressedCompactForward compressedCompactReverse selectedFieldSegment skywalkArithmeticClear

/-- Complete actual mapped kernel semantics on the existing strong caller
domain, with arbitrary incoming phase and every full measurement record. -/
theorem kernel_spec (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0 < x) (hx : x < p) (s : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409) = false) (hs0 : s.basis (base 2410) = false) :
    DirectSkywalkArithmeticStrong divide base (base 2400) x Y s (run (kernel divide) m s) := by
  simpa only [MappedCompressed.kernel,NativeFirstDirect.callerKernel] using
    NativeFirstDirect.kernel_spec divide hn hlo ho hf x Y hx0 hx s m hin hg0 hs0

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/MappedCompressedControlledSpec.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 DirectSkywalk
attribute [local irreducible] run measurementCount kernel
  directZeroDivisorEnter directZeroDivisorLeave

private theorem controlled_port_nodup :
    (base 2411::base 2313::(wireBlock base 770 256++wireBlock base 0 255++
      wireBlock base 2056 256)).Nodup := by
  have first : (List.range' 770 256++List.range' 0 255).Nodup := by
    apply List.nodup_append'.mpr
    refine ⟨List.nodup_range',List.nodup_range',List.disjoint_left.mpr ?_⟩
    intro q hx hc
    simp only [List.mem_range'_1] at hx hc
    omega
  have words : (List.range' 770 256++List.range' 0 255++List.range' 2056 256).Nodup := by
    apply List.nodup_append'.mpr
    refine ⟨first,List.nodup_range',List.disjoint_left.mpr ?_⟩
    intro q hxy hz
    simp only [List.mem_append,List.mem_range'_1] at hxy hz
    omega
  have ids : (2411::2313::(List.range' 770 256++List.range' 0 255++List.range' 2056 256)).Nodup := by
    apply List.nodup_cons.mpr
    constructor
    · simp only [List.mem_cons,List.mem_append,List.mem_range'_1]
      omega
    · apply List.nodup_cons.mpr
      constructor
      · simp only [List.mem_append,List.mem_range'_1]
        omega
      · exact words
  change ((2411::2313::(List.range' 770 256++List.range' 0 255++
    List.range' 2056 256)).map base).Nodup
  apply List.Nodup.map_on
  · intro a _ b _ eq; exact base_injective eq
  · exact ids

private theorem zero_flag_outside : base 2411 ∉ skywalkSharedWires base := by
  intro member
  obtain ⟨i,hi,eq⟩ := List.mem_map.mp member
  simp only [List.mem_range'_1] at hi
  have same := base_injective eq
  omega

/-- The actual zero-divisor wrapper satisfies the original strong port
contract. A zero divisor is allowed on the inactive arithmetic branch;
comparison work and repaired kernel cleanliness come from the caller input. -/
theorem controlled_spec (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx : x < p) (s : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (zeroBranch : x = 0 → s.basis (base 2400) = false)
    (hflag : s.basis (base 2411) = false)
    (hg0 : s.basis (base 2409) = false) (hs0 : s.basis (base 2410) = false) :
    DirectSkywalkArithmeticStrong divide base (base 2400) x Y s (run (controlled divide) m s) := by
  let D := directDivisor x
  let R := (directSkywalkResult divide (s.basis (base 2400)) x Y).val
  have positive : 0 < D := Nat.pos_of_ne_zero (directDivisor_ne_zero x)
  have bound : D < p := by
    by_cases zero : x = 0
    · simp only [D,directDivisor,zero,if_true]
      norm_num [p]
    · simpa only [D,directDivisor,zero,if_false] using hx
  have sameResult : directSkywalkResult divide (s.basis (base 2400)) D Y =
      directSkywalkResult divide (s.basis (base 2400)) x Y := by
    by_cases zero : x = 0
    · simp only [directSkywalkResult,zeroBranch zero,Bool.false_eq_true,if_false]
    · simp only [D,directDivisor,zero,if_false]
  have cin : s.basis (base 2313) = false :=
    arith_input_bit base hn x Y.val s.basis hin 2313 (by omega) (by omega) (by omega)
  have carry : ∀ q ∈ wireBlock base 0 255,s.basis q = false := by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    exact arith_input_bit base hn x Y.val s.basis hin i (by omega) (by omega) (by omega)
  have callback : ∀ (t : State) (ms : List Bool),
      regValue (wireBlock base 770 256) t.basis = directDivisor (regValue (wireBlock base 770 256) s.basis) →
      regValue (wireBlock base 2056 256) t.basis = regValue (wireBlock base 2056 256) s.basis →
      t.basis (base 2411) = decide (regValue (wireBlock base 770 256) s.basis = 0) →
      (∀ q,q ≠ base 2411 → q ∉ wireBlock base 770 256 → t.basis q = s.basis q) →
      (run (kernel divide) ms t).phase = t.phase ∧
      regValue (wireBlock base 2056 256) (run (kernel divide) ms t).basis = R ∧
      ∀ q,q ∉ wireBlock base 2056 256 → (run (kernel divide) ms t).basis q = t.basis q := by
    intro t ms divisor numerator _ frame
    have input : SkywalkArithmeticInput base D Y.val t.basis := by
      refine ⟨divisor.trans (congrArg directDivisor hin.1),numerator.trans hin.2.1,?_⟩
      intro q hq hdx hdy
      have ne : q ≠ base 2411 := fun eq => zero_flag_outside (eq ▸ hq)
      exact (frame q ne hdx).trans (hin.2.2 q hq hdx hdy)
    have controls (q : Wire) (hq : q ∈ [base 2400,base 2409,base 2410]) :
        t.basis q = s.basis q := by
      have ne : q ≠ base 2411 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
        rcases hq with rfl|rfl|rfl
        all_goals intro eq; have same := base_injective eq; omega
      have away : q ∉ wireBlock base 770 256 :=
        fun bad => ho q hq (arith_block_subset_shared base 770 256 (by omega) bad)
      exact frame q ne away
    have strong := kernel_spec divide hn hlo ho hf D Y positive bound t ms input
      ((controls _ (by simp)).trans hg0) ((controls _ (by simp)).trans hs0)
    unfold DirectSkywalkArithmeticStrong at strong
    rw [controls (base 2400) (by simp),sameResult] at strong
    exact strong
  have width : (wireBlock base 0 255).length+1 = (wireBlock base 770 256).length := by
    simp only [wireBlock_length]
  have records := directZeroControlled_states (wireBlock base 770 256) (wireBlock base 2056 256)
    (wireBlock base 0 255) (base 2313) (base 2411) controlled_port_nodup width (kernel divide) s
    (m.take (measurementCount (directZeroDivisorEnter (wireBlock base 770 256) (wireBlock base 0 255)
      (base 2313) (base 2411))))
    ((m.drop (measurementCount (directZeroDivisorEnter (wireBlock base 770 256) (wireBlock base 0 255)
      (base 2313) (base 2411)))).take (measurementCount (kernel divide)))
    ((m.drop (measurementCount (directZeroDivisorEnter (wireBlock base 770 256) (wireBlock base 0 255)
      (base 2313) (base 2411)))).drop (measurementCount (kernel divide)))
    R cin hflag carry callback
  simpa only [DirectSkywalkArithmeticStrong,controlled,directZeroControlled,run_append,
    skywalkArithmeticNumerator,R] using records

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Framework/WireRenamePool.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd

private theorem pool_write_rename (f : Wire → Wire) (S : Finset Wire)
    (hf : ∀a∈S,∀b∈S,f a=f b → a=b) (a : Wire) (ha : a∈S)
    (logical physical : BasisState) (v : Bool)
    (hb : ∀q∈S,logical q=physical (f q)) :
    ∀q∈S,writeBit logical a v q=writeBit physical (f a) v (f q) := by
  intro q hq
  by_cases same : q=a
  · subst q
    simp [writeBit]
  · have different : f q≠f a := fun eq => same (hf q hq a ha eq)
    simp [writeBit,Function.update,same,different,hb q hq]

private theorem pool_correct_rename (f : Wire → Wire) (S : Finset Wire)
    (cs : List Correction) (hc : correctionWires cs⊆S) (t s : State)
    (hp : t.phase=s.phase) (hb : ∀q∈S,t.basis q=s.basis (f q)) :
    (correct cs t).phase=(correct (cs.map (renameCorrection f)) s).phase ∧
    ∀q∈S,(correct cs t).basis q=(correct (cs.map (renameCorrection f)) s).basis (f q) := by
  induction cs generalizing t s with
  | nil => exact ⟨hp,hb⟩
  | cons c cs ih =>
    have tail : correctionWires cs⊆S := by
      intro q hq
      apply hc
      cases c <;> exact Finset.mem_union_right _ hq
    cases c with
    | Z a =>
      simp only [List.map_cons,renameCorrection,correct]
      apply ih tail
      · simp only [hp,hb a (hc (by simp [correctionWires]))]
      · exact hb
    | CZ a b =>
      simp only [List.map_cons,renameCorrection,correct]
      apply ih tail
      · simp only [hp,hb a (hc (by simp [correctionWires])),
          hb b (hc (by simp [correctionWires]))]
      · exact hb

private theorem pool_run_rename (f : Wire → Wire) (S : Finset Wire)
    (hf : ∀a∈S,∀b∈S,f a=f b → a=b) (p : Program) (hw : wires p⊆S)
    (m : List Bool) (t s : State) (hp : t.phase=s.phase)
    (hb : ∀q∈S,t.basis q=s.basis (f q)) :
    (run p m t).phase=(run (renameProgram f p) m s).phase ∧
    ∀q∈S,(run p m t).basis q=(run (renameProgram f p) m s).basis (f q) := by
  induction p generalizing m t s with
  | nil => exact ⟨hp,hb⟩
  | cons i p ih =>
    have tail : wires p⊆S := fun q hq => hw (Finset.mem_union_right _ hq)
    have head : i.wires⊆S := fun q hq => hw (Finset.mem_union_left _ hq)
    cases i with
    | X a =>
      have ha : a∈S := head (by simp [Instr.wires])
      simp only [renameProgram,List.map_cons,renameInstr,run]
      apply ih tail
      · exact hp
      · rw [hb a ha]
        exact pool_write_rename f S hf a ha t.basis s.basis _ hb
    | CX a q =>
      have ha : a∈S := head (by simp [Instr.wires])
      have hq : q∈S := head (by simp [Instr.wires])
      simp only [renameProgram,List.map_cons,renameInstr,run]
      apply ih tail
      · exact hp
      · rw [hb q hq,hb a ha]
        exact pool_write_rename f S hf q hq t.basis s.basis _ hb
    | CCX a b q =>
      have ha : a∈S := head (by simp [Instr.wires])
      have hb0 : b∈S := head (by simp [Instr.wires])
      have hq : q∈S := head (by simp [Instr.wires])
      simp only [renameProgram,List.map_cons,renameInstr,run]
      apply ih tail
      · exact hp
      · rw [hb q hq,hb a ha,hb b hb0]
        exact pool_write_rename f S hf q hq t.basis s.basis _ hb
    | measureX q c0 c1 =>
      have hq : q∈S := head (by simp [Instr.wires])
      have corrections : correctionWires (if m.headD false then c1 else c0)⊆S := by
        cases outcome : m.headD false <;> simp only [outcome,Bool.false_eq_true,if_false,if_true]
        · intro a ha
          exact head (Finset.mem_union_left _ (Finset.mem_union_right _ ha))
        · intro a ha
          exact head (Finset.mem_union_right _ ha)
      have selected : (if m.headD false then c1 else c0).map (renameCorrection f)=
          (if m.headD false then c1.map (renameCorrection f) else c0.map (renameCorrection f)) := by
        cases m.headD false <;> rfl
      have updated := pool_correct_rename f S (if m.headD false then c1 else c0) corrections
        ⟨t.phase ^^ (m.headD false && t.basis q),writeBit t.basis q false⟩
        ⟨s.phase ^^ (m.headD false && s.basis (f q)),writeBit s.basis (f q) false⟩
        (by simp only [hp,hb q hq])
        (pool_write_rename f S hf q hq t.basis s.basis false hb)
      have measured :
          (measureAndCorrect q c0 c1 (m.headD false) t).phase=
            (measureAndCorrect (f q) (c0.map (renameCorrection f))
              (c1.map (renameCorrection f)) (m.headD false) s).phase ∧
          ∀a∈S,(measureAndCorrect q c0 c1 (m.headD false) t).basis a=
            (measureAndCorrect (f q) (c0.map (renameCorrection f))
              (c1.map (renameCorrection f)) (m.headD false) s).basis (f a) := by
        simpa only [measureAndCorrect,selected] using updated
      simp only [renameProgram,List.map_cons,renameInstr,run]
      exact ih tail m.tail _ _ measured.1 measured.2

/-- Finite-support semantic relabeling. Only wires inside S must be
injectively placed and related to the logical input. Both correction lists
are covered by actual instruction support; measurement records are arbitrary. -/
theorem run_rename_pool (f : Wire → Wire) (S : Finset Wire)
    (hf : ∀a∈S,∀b∈S,f a=f b → a=b) (p : Program) (hw : wires p⊆S)
    (m : List Bool) (t s : State) (hp : t.phase=s.phase)
    (hb : ∀q∈S,t.basis q=s.basis (f q)) :
    (run (renameProgram f p) m s).phase=(run p m t).phase ∧
    ∀q∈S,(run (renameProgram f p) m s).basis (f q)=(run p m t).basis q := by
  have equality := pool_run_rename f S hf p hw m t s hp hb
  exact ⟨equality.1.symm,fun q hq => (equality.2 q hq).symm⟩

/-- Physical outsiders restore without any relation to logical ghost wires
outside S. This conclusion does not require injectivity. -/
theorem run_rename_pool_outside (f : Wire → Wire) (S : Finset Wire)
    (p : Program) (hw : wires p⊆S) (m : List Bool) (s : State)
    (q : Wire) (hq : q∉S.image f) :
    (run (renameProgram f p) m s).basis q=s.basis q := by
  apply run_preserves_outside
  intro h
  rw [renameProgram_support] at h
  obtain ⟨a,ha,equal⟩ := Finset.mem_image.mp h
  exact hq (Finset.mem_image.mpr ⟨a,hw ha,equal⟩)

end ECDSAAdd
end

-- source: ECDSAAdd/Arithmetic/MappedCompressedPointTransfer.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 ControlledPointLayout DirectSkywalk
attribute [local irreducible] run controlled

/-- Wiring and lease facts only; arithmetic correctness is supplied by
the already proved actual controlled circuit, never as a placement oracle. -/
structure PointArithmeticPlacement (L : ControlledPointLayout) (f : Wire → Wire) : Prop where
  injectiveOnSlots : ∀a∈slots.toFinset,∀b∈slots.toFinset,f a=f b → a=b
  divisorMap : (wireBlock base 770 256).map f=L.point.x
  numeratorMap : (wireBlock base 2056 256).map f=L.point.y
  controlMap : f (base 2400)=L.core.generic
  sharedWork : ∀q∈skywalkSharedWires base,q∈slots.toFinset →
    q∉wireBlock base 770 256 → q∉wireBlock base 2056 256 → f q∈L.dialogPool
  selectorG : f (base 2409)∈L.dialogPool
  selectorS : f (base 2410)∈L.dialogPool
  zeroFlag : f (base 2411)∈L.dialogPool

def logicalInput (domain : Finset Wire) (f : Wire → Wire) (s : State) : State :=
  ⟨s.phase,fun q => if q∈domain then s.basis (f q) else false⟩

private theorem divisor_sites : (wireBlock base 770 256).toFinset⊆slots.toFinset := by
  intro q hq
  apply resident_support
  simp only [resident,List.mem_toFinset,List.mem_append]
  exact Or.inl (Or.inl (List.mem_toFinset.mp hq))
private theorem numerator_sites : (wireBlock base 2056 256).toFinset⊆slots.toFinset := by
  intro q hq
  apply resident_support
  simp only [resident,List.mem_toFinset,List.mem_append]
  exact Or.inl (Or.inr (List.mem_toFinset.mp hq))
private theorem control_site : base 2400∈slots.toFinset := by
  apply slot_mem
  · unfold live; omega
  · unfold CompressedAllocation.omitted; omega

private theorem reg_map_agree (f : Wire → Wire) (r : List Wire)
    (logical physical : BasisState) (h : ∀q∈r,logical q=physical (f q)) :
    regValue r logical=regValue (r.map f) physical := by
  induction r generalizing logical physical with
  | nil => rfl
  | cons a rs ih =>
    change (if logical a then 1 else 0)+2*regValue rs logical=
      (if physical (f a) then 1 else 0)+2*regValue (rs.map f) physical
    rw [h a (by simp),ih logical physical (fun q hq => h q (List.mem_cons_of_mem a hq))]

/-- Transfer the original strong point-arithmetic port contract to physical
wires, using only finite-support injectivity. Logical unused ghost sites are
completed with zero and never impose a condition on physical outsiders. -/
private theorem pointTransfer_core (L : ControlledPointLayout) (f : Wire → Wire)
    (domain : Finset Wire) (divide : Bool)
    (injective : ∀a∈domain,∀b∈domain,f a=f b → a=b)
    (divisorMap : (wireBlock base 770 256).map f=L.point.x)
    (numeratorMap : (wireBlock base 2056 256).map f=L.point.y)
    (controlMap : f (base 2400)=L.core.generic)
    (sharedWork : ∀q∈skywalkSharedWires base,q∈domain → q∉wireBlock base 770 256 → q∉wireBlock base 2056 256 → f q∈L.dialogPool)
    (selectorG : f (base 2409)∈L.dialogPool)
    (selectorS : f (base 2410)∈L.dialogPool)
    (zeroFlag : f (base 2411)∈L.dialogPool)
    (dxSites : (wireBlock base 770 256).toFinset⊆domain)
    (dySites : (wireBlock base 2056 256).toFinset⊆domain)
    (bSite : base 2400∈domain)
    (X : Nat) (Y : Fp) (B : Bool) (hx0 : B=true → X≠0)
    (s : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hX : regValue L.point.x s.basis=X) (hY : regValue L.point.y s.basis=Y.val)
    (clean : regValue L.dialogPool s.basis=0)
    (P : Program) (programSites : wires P⊆domain)
    (P_spec : ∀(t : State)(records : List Bool),
      SkywalkArithmeticInput base X Y.val t.basis →
      (X=0 → t.basis (base 2400)=false) →
      t.basis (base 2411)=false → t.basis (base 2409)=false → t.basis (base 2410)=false →
      DirectSkywalkArithmeticStrong divide base (base 2400) X Y t (run P records t)) :
    let out := run (renameProgram f P) m s
    out.phase=s.phase ∧ regValue L.point.y out.basis=(directSkywalkResult divide B X Y).val ∧
      ∀q,q∉L.point.y → out.basis q=s.basis q := by
  let t := logicalInput domain f s
  have inputBits (q : Wire) (hq : q∈domain) : t.basis q=s.basis (f q) := by
    simp only [t,logicalInput,if_pos hq]
  have zero (q : Wire) (hq : f q∈L.dialogPool) : t.basis q=false := by
    change (if q∈domain then s.basis (f q) else false)=false
    split
    · exact (regValue_zero _ _).mp clean _ hq
    · rfl
  have input : SkywalkArithmeticInput base X Y.val t.basis := by
    refine ⟨?_,?_,?_⟩
    · change regValue (wireBlock base 770 256) t.basis=X
      rw [reg_map_agree f _ t.basis s.basis (fun q hq => inputBits q (dxSites (List.mem_toFinset.mpr hq))),divisorMap]
      exact hX
    · change regValue (wireBlock base 2056 256) t.basis=Y.val
      rw [reg_map_agree f _ t.basis s.basis (fun q hq => inputBits q (dySites (List.mem_toFinset.mpr hq))),numeratorMap]
      exact hY
    · intro q hq hdx hdy
      by_cases used : q∈domain
      · exact zero q (sharedWork q hq used hdx hdy)
      · simp only [t,logicalInput,if_neg used]
  have control : t.basis (base 2400)=B := by
    rw [inputBits _ bSite,controlMap,hb]
  have zeroBranch : X=0 → t.basis (base 2400)=false := by
    intro eq
    rw [control]
    cases B
    · rfl
    · exact False.elim ((hx0 rfl) eq)
  have strong := P_spec t m input zeroBranch
    (zero _ zeroFlag) (zero _ selectorG) (zero _ selectorS)
  have transfer := run_rename_pool f domain injective
    P programSites m t s rfl inputBits
  unfold DirectSkywalkArithmeticStrong at strong
  rw [control] at strong
  refine ⟨transfer.1.trans strong.1,?_,?_⟩
  · rw [←numeratorMap]
    exact (reg_map_agree f _ (run P m t).basis
      (run (renameProgram f P) m s).basis
      (fun q hq => (transfer.2 q (dySites (List.mem_toFinset.mpr hq))).symm)).symm.trans strong.2.1
  · intro q outside
    by_cases image : q∈domain.image f
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp image
      have away : a∉skywalkArithmeticNumerator base := by
        intro mem
        apply outside
        rw [←numeratorMap]
        exact List.mem_map.mpr ⟨a,mem,rfl⟩
      exact (transfer.2 a ha).trans ((strong.2.2 a away).trans (inputBits a ha))
    · exact run_rename_pool_outside f domain P
        programSites m s q image



/-- Transfer the original strong point-arithmetic port contract to physical
wires, using only finite-support injectivity. Logical unused ghost sites are
completed with zero and never impose a condition on physical outsiders. -/
theorem pointTransfer_spec (L : ControlledPointLayout) (f : Wire → Wire)
    (placement : PointArithmeticPlacement L f) (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (X : Nat) (Y : Fp) (B : Bool) (hx : X<p) (hx0 : B=true → X≠0)
    (s : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hX : regValue L.point.x s.basis=X) (hY : regValue L.point.y s.basis=Y.val)
    (clean : regValue L.dialogPool s.basis=0) :
    let out := run (renameProgram f (controlled divide)) m s
    out.phase=s.phase ∧ regValue L.point.y out.basis=(directSkywalkResult divide B X Y).val ∧
      ∀q,q∉L.point.y → out.basis q=s.basis q := by
  rcases placement with ⟨injective,divisorMap,numeratorMap,controlMap,sharedWork,selectorG,selectorS,zeroFlag⟩
  exact pointTransfer_core L f slots.toFinset divide injective divisorMap numeratorMap controlMap
    sharedWork selectorG selectorS zeroFlag divisor_sites numerator_sites control_site
    X Y B hx0 s m hb hX hY clean
    (controlled divide) (controlled_support divide)
    (fun t records input zeroBranch hflag hg hs =>
      controlled_spec divide hn hlo ho hf X Y hx t records input zeroBranch hflag hg hs)

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Arithmetic/MappedCompressedPointArithmetic.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 ControlledPointLayout DirectSkywalk
attribute [local irreducible] run controlled toffoliCount measurementCount
  mixedTranscriptUnitTrace SkywalkTrace.next Nat.iterate

/-- Concrete physical binding of the finite arithmetic support. -/
theorem pointPlacement (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    PointArithmeticPlacement L (pointWireFn L) := by
  have ports := pointWireFn_coordinates L hw
  have scalars := pointWireFn_scalar_dialog L hw
  exact ⟨pointWireFn_injective_slots L hw hn,ports.1,ports.2,pointWireFn_control L,
    pointWireFn_sharedWork L hw,scalars.1,scalars.2.1,scalars.2.2⟩

private theorem logical_shared_nodup : (skywalkSharedWires base).Nodup := by
  apply List.Nodup.map_on
  · intro a _ b _ eq; exact base_injective eq
  · exact List.nodup_range'

private theorem logical_scalar_outside (i : Nat) (hi : 2314 ≤ i) :
    base i ∉ skywalkSharedWires base := by
  intro member
  obtain ⟨j,hj,eq⟩ := List.mem_map.mp member
  simp only [List.mem_range'_1] at hj
  have same := base_injective eq
  omega

private theorem logical_selectors_outside :
    ∀ q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base := by
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl
  all_goals exact logical_scalar_outside _ (by omega)

/-- Fixed logical template layout; only pure labels are checked here.
The actual recorded tape, not its numerical contents, supplies the layout. -/
private theorem logical_mixed_layout :
    MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base) := by
  have scalar : [base 2400,base 2409,base 2410].Nodup := by simp [base]
  have disjoint : [base 2400,base 2409,base 2410].Disjoint (skywalkSharedWires base) :=
    List.disjoint_left.mpr (fun q hq => logical_selectors_outside q hq)
  have hall := List.nodup_append'.mpr ⟨scalar,logical_shared_nodup,disjoint⟩
  have unused : skywalkSharedUnused base⊆skywalkSharedWires base := by
    intro q hq
    simp only [skywalkSharedUnused,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl
    all_goals exact arith_mem base 0 2314 _ (by omega) (by omega)
  apply mixedTranscriptTape_layout
  intro r hr
  have pair := (List.nodup_cons.mp (skywalkShared_tape_layout base logical_shared_nodup
    (base 2400) (logical_selectors_outside _ (by simp)) r hr)).2
  have sub : (r.2::r.1::(skywalkSharedField base).wires)⊆skywalkSharedWires base := by
    intro q hq
    rcases List.mem_cons.mp hq with eq|hq
    · subst q; exact (retained_tape_subset_shared base r hr).2
    rcases List.mem_cons.mp hq with eq|hq
    · subst q; exact (retained_tape_subset_shared base r hr).1
    · exact retained_field_subset_shared base hq
  constructor
  · exact logical_shared_nodup
  · apply List.nodup_iff_count.mpr
    intro q
    have hh := List.nodup_iff_count.mp hall q
    have hp := List.nodup_iff_count.mp pair q
    have hle : (r.2::r.1::(skywalkSharedField base).wires).count q≤
        (skywalkSharedWires base).count q := by
      by_cases hm : q∈r.2::r.1::(skywalkSharedField base).wires
      · have positive := List.count_pos_iff.mpr (sub hm); omega
      · rw [List.count_eq_zero.mpr hm]; omega
    simp only [List.count_append,List.count_cons,List.count_nil] at hh hp hle ⊢
    omega
  · exact fun h => logical_selectors_outside _ (by simp) (fusedSharedSites_subset base h)
  · exact fun h => logical_selectors_outside _ (by simp) (unused h)
  · exact fun h => logical_selectors_outside _ (by simp) (unused h)

/-- Computable concrete point arithmetic: finite placement of the complete
zero-repair and compressed512-round arithmetic caller. -/
def pointCompressedArithmetic (L : ControlledPointLayout) (multiply : Bool) : Program :=
  renameProgram (pointWireFn L) (controlled (!multiply))

/-- Original guarded point-arithmetic contract, unchanged on all canonical
X,Y values, incoming phases, inactive zero divisors and full record streams. -/
theorem pointCompressedArithmetic_correct (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (multiply : Bool) (X Y : Nat) (B : Bool)
    (hX : X<p) (hX0 : B=true → X≠0) (hY : Y<p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=X)
    (hy : regValue L.point.y s.basis=Y) (hc : regValue L.dialogPool s.basis=0) :
    let V := if B then (if multiply then ((Y:Fp)*(X:Fp)).val else ((Y:Fp)/(X:Fp)).val) else Y
    (run (pointCompressedArithmetic L multiply) m s).phase=s.phase ∧
    regValue L.point.y (run (pointCompressedArithmetic L multiply) m s).basis=V ∧
    ∀ q,q∉L.point.y → (run (pointCompressedArithmetic L multiply) m s).basis q=s.basis q := by
  have yValue : (Y:Fp).val=Y := ZMod.val_natCast_of_lt hY
  have result := pointTransfer_spec L (pointWireFn L) (pointPlacement L hw hn) (!multiply)
    logical_shared_nodup base_above logical_selectors_outside logical_mixed_layout
    X (Y:Fp) B hX hX0 s m hb hx (hy.trans yValue.symm) hc
  cases B <;> cases multiply <;>
    simpa only [pointCompressedArithmetic,directSkywalkResult,skywalkArithmeticResult,
      Bool.not_false,Bool.not_true,Bool.false_eq_true,if_false,if_true,yValue] using result

theorem pointCompressedArithmetic_support (L : ControlledPointLayout) (hw : L.Widths)
    (multiply : Bool) : wires (pointCompressedArithmetic L multiply)⊆
      (CompressedPointSquare.residents L++CompressedPointSquare.sharedPool L).toFinset := by
  intro q hq
  rw [pointCompressedArithmetic,renameProgram_support] at hq
  obtain ⟨old,used,rfl⟩ := Finset.mem_image.mp hq
  exact pointWireFn_slots_image L hw (Finset.mem_image.mpr
    ⟨old,controlled_support (!multiply) used,rfl⟩)

/-- Relabeling preserves the exact emitted prices of both arithmetic stages. -/
theorem pointCompressedArithmetic_counts (L : ControlledPointLayout) :
    toffoliCount (pointCompressedArithmetic L false)=1053750 ∧
    measurementCount (pointCompressedArithmetic L false)=724536 ∧
    toffoliCount (pointCompressedArithmetic L true)=1054260 ∧
    measurementCount (pointCompressedArithmetic L true)=724536 := by
  have div := controlled_counts true
  have mul := controlled_counts false
  have rd := renameProgram_counts (pointWireFn L) (controlled true)
  have rm := renameProgram_counts (pointWireFn L) (controlled false)
  simp only [pointCompressedArithmetic,Bool.not_false,Bool.not_true]
  rw [rd.1,rd.2,rm.1,rm.2,div.1,div.2,mul.1,mul.2]
  norm_num

end ECDSAAdd.Arithmetic.MappedCompressed
end

-- source: ECDSAAdd/Math/PointInPlace.lean
noncomputable section

namespace ECDSAAdd.Secp256k1

/-- 有限曲线点同横坐标，当且仅当两点相同或互为相反点。 -/
theorem sameX_iff_eq_or_neg {x y cx cy : Fp}
    (hr : curve.toAffine.Nonsingular x y) (hc : curve.toAffine.Nonsingular cx cy) :
    x=cx ↔ (.some hr : Point)=.some hc ∨ (.some hr : Point)=-(.some hc : Point) := by
  constructor
  · intro hx
    by_cases hy : y = -cy
    · right
      rw [WeierstrassCurve.Affine.Point.neg_some,
        WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨hx, by simpa only [negY_eq_neg] using hy⟩
    · left
      rw [WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨hx, y_eq_of_x_eq_of_not_inverse hr hc hx hy⟩
  · rintro (h | h)
    · exact (WeierstrassCurve.Affine.Point.some.inj h).1
    · rw [WeierstrassCurve.Affine.Point.neg_some,
        WeierstrassCurve.Affine.Point.some.injEq] at h
      exact h.1

/-- 普通分支恰好排除 O、C、−C；不要求 C 与 −C 不同。 -/
theorem ordinary_point_iff (R : Point) {cx cy : Fp}
    (hc : curve.toAffine.Nonsingular cx cy) :
    ((coordinates R).isSome=true ∧ ((coordinates R).getD (0,0)).1≠cx) ↔
      R≠0 ∧ R≠(.some hc : Point) ∧ R≠-(.some hc : Point) := by
  cases R with
  | zero => simp [coordinates, ← WeierstrassCurve.Affine.Point.zero_def]
  | @some x y hr =>
    simp only [coordinates, Option.isSome_some, Option.getD_some, true_and]
    have hh := not_congr (sameX_iff_eq_or_neg hr hc)
    constructor
    · intro hx
      exact ⟨WeierstrassCurve.Affine.Point.some_ne_zero hr, not_or.mp (hh.mp hx)⟩
    · rintro ⟨_, ha, hb⟩
      exact hh.mpr (not_or.mpr ⟨ha,hb⟩)

/-- 构造期纵坐标条件正好识别 C 与 −C 是否不同；退化时禁用倍点标志。 -/
theorem doubling_enabled_iff {cx cy : Fp}
    (hc : curve.toAffine.Nonsingular cx cy) :
    cy≠-cy ↔ (.some hc : Point)≠-(.some hc : Point) := by
  simp only [ne_eq, WeierstrassCurve.Affine.Point.neg_some,
    WeierstrassCurve.Affine.Point.some.injEq, negY_eq_neg, true_and]

/-- 输出侧重算输入的三个角落标志；控制为 false 时每个谓词仍为假。 -/
theorem translated_point_flags (R C : Point) (b : Bool) :
    let R' := if b then R+C else R
    ((b=true ∧ R'=C) ↔ (b=true ∧ R=0)) ∧
    ((b=true ∧ C≠-C ∧ R'=C+C) ↔ (b=true ∧ C≠-C ∧ R=C)) ∧
    ((b=true ∧ R'=0) ↔ (b=true ∧ R=-C)) := by
  cases b <;> simp [add_eq_zero_iff_eq_neg]

/-- 12 步原地流程中的三个域等式：清 y、更新 x、重建 y。 -/
theorem generic_inplace_values (x y cx cy : Fp) (hx : x≠cx) :
    let l := genericSlope x y cx cy
    (y-cy)-l*(x-cx)=0 ∧
    (x-cx)-l*l+3*cx=cx-genericX x y cx cy ∧
    l*(cx-genericX x y cx cy)-cy=genericY x y cx cy := by
  dsimp only
  have he : genericSlope x y cx cy * (x-cx) = y-cy := by
    simp only [genericSlope, genericNumerator, genericDenominator]
    field_simp [sub_ne_zero.mpr hx]
  refine ⟨sub_eq_zero.mpr he.symm, ?_, ?_⟩
  · unfold genericX
    ring
  · unfold genericY
    linear_combination -he

/-- 第二个除数为零只会发生在输入 −2C；该结论以普通分支为前提。 -/
theorem second_denominator_zero_iff {x y cx cy : Fp}
    (hr : curve.toAffine.Nonsingular x y) (hc : curve.toAffine.Nonsingular cx cy)
    (hx : x≠cx) :
    cx-genericX x y cx cy=0 ↔ (.some hr : Point)=-((.some hc : Point)+.some hc) := by
  let R : Point := .some hr
  let C : Point := .some hc
  constructor
  · intro hz
    have hs : R+C=C ∨ R+C=-C := by
      rw [← genericAdd_correct hr hc hx]
      exact (sameX_iff_eq_or_neg (generic_nonsingular hr hc hx) hc).mp
        (sub_eq_zero.mp hz).symm
    rcases hs with hs | hs
    · have hR : R=0 := add_right_cancel (hs.trans (zero_add C).symm)
      exact False.elim (WeierstrassCurve.Affine.Point.some_ne_zero hr hR)
    · change R=-(C+C)
      calc
        R = (R+C)-C := by abel
        _ = -C-C := by rw [hs]
        _ = -(C+C) := by abel
  · intro hR
    have hs : R+C=-C := by
      change (.some hr : Point)+(.some hc : Point)=-(.some hc : Point)
      rw [hR]
      abel
    have he := congrArg coordinates ((genericAdd_correct hr hc hx).trans hs)
    simp only [C, genericAdd, WeierstrassCurve.Affine.Point.neg_some, coordinates,
      Option.some.injEq, Prod.mk.injEq] at he
    exact sub_eq_zero.mpr he.1.symm

/-- 例外斜率是编译期常量；O 的坐标按现有编码取零，使定义全域成立。 -/
def exceptionalSlope (C : Point) : Fp :=
  let r := (coordinates (-(C+C))).getD (0,0)
  let c := (coordinates C).getD (0,0)
  genericSlope r.1 r.2 c.1 c.2

/-- 例外分支下该常量就是当前斜率，可由受控常量 XOR 清零。 -/
theorem exceptional_slope_eq {x y cx cy : Fp}
    (hr : curve.toAffine.Nonsingular x y) (hc : curve.toAffine.Nonsingular cx cy)
    (hx : x≠cx) (hz : cx-genericX x y cx cy=0) :
    genericSlope x y cx cy = exceptionalSlope (.some hc) := by
  have he := (second_denominator_zero_iff hr hc hx).mp hz
  unfold exceptionalSlope
  rw [← he]
  rfl

/-- 第二除数非零时，从当前 y 与 x 重算斜率；供减法清理 λ。 -/
theorem slope_from_output (x y cx cy : Fp) (hx : x≠cx)
    (hd : cx-genericX x y cx cy≠0) :
    (genericY x y cx cy+cy) / (cx-genericX x y cx cy) = genericSlope x y cx cy := by
  have he := (generic_inplace_values x y cx cy hx).2.2
  rw [← he]
  field_simp
  ring

end ECDSAAdd.Secp256k1
end

-- source: ECDSAAdd/Arithmetic/PointInPlaceProgram.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Secp256k1

/-- 受控常数模加：掩码源、无控制模加、清源。 -/
def pointInPlaceConstantAdd (L : ControlledPointLayout) (r : List Wire) (k : Fp) : Program :=
  let M := L.inPlaceConstant r
  maskedConstant L.core.generic M.a k.val ++ modAddInPlace M p ++ maskedConstant L.core.generic M.a k.val

/-- 规范取负，两个高位在调用边界均零。 -/
def pointInPlaceNegate (L : ControlledPointLayout) : Program :=
  controlledModSub L.core.generic L.inPlaceNegate p ++
  swapRegisters L.core.generic L.point.x L.inPlaceNegate.low ++
  controlledModAdd L.core.generic L.inPlaceNegate p

/-- 从当前x/y重算斜率；零除数例外用编译期常量清除。 -/
def pointInPlaceClearSlope (L : ControlledPointLayout) (lambdaStar : Fp) : Program :=
  equalConstant L.core.generic L.core.equalX L.inPlaceXZero 0 ++
  [.CX L.core.generic L.core.equalNegY,.CX L.core.equalX L.core.equalNegY] ++
  divideSub (L.inPlaceDivide L.core.equalNegY L.point.x L.point.y) ++
  maskedConstant L.core.equalX L.inPlaceSlope lambdaStar.val ++
  [.CX L.core.generic L.core.equalNegY,.CX L.core.equalX L.core.equalNegY] ++
  equalConstant L.core.generic L.core.equalX L.inPlaceXZero 0

/-- §16.3十二步普通分支；λ在未启用分支始终为零，外部乘积无需外部控制。 -/
def pointInPlaceGeneric (L : ControlledPointLayout) (cx cy lambdaStar : Fp) : Program :=
  pointInPlaceConstantAdd L L.point.x (-cx) ++
  pointInPlaceConstantAdd L L.point.y (-cy) ++
  divideAdd (L.inPlaceDivide L.core.generic L.point.x L.point.y) ++
  montMulSub L.inPlaceMultiply p ++
  squareSub L.inPlaceKaratsuba ++
  pointInPlaceConstantAdd L L.point.x (3*cx) ++
  montMulAdd L.inPlaceMultiply p ++
  pointInPlaceClearSlope L lambdaStar ++
  pointInPlaceNegate L ++
  pointInPlaceConstantAdd L L.point.x cx ++
  pointInPlaceConstantAdd L L.point.y (-cy)

/-- g=b XOR o XOR d XOR i；同一CX序列装载与清理。 -/
def pointInPlaceGenericFlag (L : ControlledPointLayout) : Program :=
  [.CX L.control L.core.generic,.CX L.infinitySelect L.core.generic,
    .CX L.doubleSelect L.core.generic,.CX L.genericSelect L.core.generic]

/-- h=b∧[cy≠−cy]，条件是编译期常量，不添加几何前提。 -/
def pointInPlaceDoubleEnable (L : ControlledPointLayout) (cy : Fp) : Program :=
  if cy≠-cy then [.CX L.control L.core.double] else []

/-- 互斥角落的四次XOR：O→C、C→2C、−C→O。 -/
def pointInPlaceCorners (L : ControlledPointLayout) (C : Point) : Program :=
  maskedPointConstant L.infinitySelect L.point C ++
  maskedPointConstant L.doubleSelect L.point C ++
  maskedPointConstant L.doubleSelect L.point (C+C) ++
  maskedPointConstant L.genericSelect L.point (-C)

/-- 输入分类、普通分支、三个互斥角落写回，再从输出清除分类位。 -/
def pointInPlaceFinite (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  pointInPlaceDoubleEnable L cy ++
  equalConstant L.control L.infinitySelect L.inPlacePointZero (pointCode 0) ++
  equalConstant L.core.double L.doubleSelect L.inPlacePointZero (pointCode C) ++
  equalConstant L.control L.genericSelect L.inPlacePointZero (pointCode (-C)) ++
  pointInPlaceGenericFlag L ++
  pointInPlaceGeneric L cx cy (exceptionalSlope C) ++
  pointInPlaceCorners L C ++
  pointInPlaceGenericFlag L ++
  equalConstant L.control L.infinitySelect L.inPlacePointZero (pointCode C) ++
  equalConstant L.core.double L.doubleSelect L.inPlacePointZero (pointCode (C+C)) ++
  equalConstant L.control L.genericSelect L.inPlacePointZero (pointCode 0) ++
  pointInPlaceDoubleEnable L cy

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointRecoveryLayout.lean
noncomputable section

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.ControlledPointLayout

def recoveryConstant (L : ControlledPointLayout) (r : List Wire) : MeasuredCanonicalModLayout :=
  {src:=L.dialogPool.take 256,out:=r,carry:=(L.dialogPool.drop 256).take 256,
    high:=L.core.poolWire 512,cin:=L.core.poolWire 513,flag:=L.core.poolWire 514}

def recoveryNegate (L : ControlledPointLayout) : CompactRecoveryNegateLayout :=
  {word:=L.point.x,work:=L.dialogPool.take 256,cin:=L.core.poolWire 256,zero:=L.core.poolWire 257}

def recoveryStageSites (L : ControlledPointLayout) : List Wire :=
  PointAddLayout.pointWires L.point++[L.control]++L.inPlaceFlags++L.dialogPool.take 515

theorem recoveryConstant_widths (L : ControlledPointLayout) (hw : L.Widths) (r : List Wire)
    (hr : r.length=256) : (L.recoveryConstant r).Widths 256 := by
  constructor <;> simp [recoveryConstant,L.dialogPool_length hw,hr]

theorem recoveryConstant_pool (L : ControlledPointLayout) (hw : L.Widths) (r : List Wire) :
    (L.recoveryConstant r).src++(L.recoveryConstant r).carry++
      [(L.recoveryConstant r).high,(L.recoveryConstant r).cin,(L.recoveryConstant r).flag]=L.dialogPool.take 515 := by
  simp only [recoveryConstant]
  rw [←List.take_add]
  norm_num
  calc
    L.dialogPool.take 512++[L.core.poolWire 512,L.core.poolWire 513,L.core.poolWire 514]=
      (L.dialogPool.take 512++[L.core.poolWire 512])++[L.core.poolWire 513,L.core.poolWire 514] := by simp
    _=(L.dialogPool.take 513++[L.core.poolWire 513])++[L.core.poolWire 514] := by
      rw [L.dialogBit_prefix hw 512 (by omega)]
      simp [List.append_assoc]
    _=L.dialogPool.take 514++[L.core.poolWire 514] := by rw [L.dialogBit_prefix hw 513 (by omega)]
    _=L.dialogPool.take 515 := L.dialogBit_prefix hw 514 (by omega)

theorem recoveryConstant_nodup (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y) :
    (L.core.generic::(L.recoveryConstant r).wires).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
  have pool := (List.take_sublist 515 L.dialogPool).count_le q
  rw [←L.recoveryConstant_pool hw r] at pool
  rcases hr with rfl|rfl
  all_goals
    simp only [recoveryConstant,MeasuredCanonicalModLayout.wires,dialogUsedWires,inPlaceFlags,
      PointAddLayout.pointWires,List.count_cons,List.count_append,List.count_nil] at h pool ⊢
    omega

theorem recoveryNegate_pool (L : ControlledPointLayout) (hw : L.Widths) :
    L.recoveryNegate.work++[L.recoveryNegate.cin,L.recoveryNegate.zero]=L.dialogPool.take 258 := by
  simp only [recoveryNegate]
  calc
    L.dialogPool.take 256++[L.core.poolWire 256,L.core.poolWire 257]=
      (L.dialogPool.take 256++[L.core.poolWire 256])++[L.core.poolWire 257] := by simp
    _=L.dialogPool.take 257++[L.core.poolWire 257] := by rw [L.dialogBit_prefix hw 256 (by omega)]
    _=L.dialogPool.take 258 := L.dialogBit_prefix hw 257 (by omega)

theorem recoveryNegate_nodup (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    (L.recoveryNegate.wires L.core.generic).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
  have pool := (List.take_sublist 258 L.dialogPool).count_le q
  rw [←L.recoveryNegate_pool hw] at pool
  simp only [recoveryNegate,CompactRecoveryNegateLayout.wires,dialogUsedWires,inPlaceFlags,
    PointAddLayout.pointWires,List.count_cons,List.count_append,List.count_nil] at h pool ⊢
  omega

theorem recoveryStageSites_certified (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.recoveryStageSites.Nodup ∧ L.recoveryStageSites.length=1036 := by
  constructor
  · apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
    have ht := (List.take_sublist 515 L.dialogPool).count_le q
    simp only [recoveryStageSites,dialogUsedWires,List.count_append] at h ⊢
    omega
  · simp [recoveryStageSites,PointAddLayout.pointWires,inPlaceFlags,point,hw.inputX,hw.inputY,L.dialogPool_length hw]

end ECDSAAdd.Arithmetic.ControlledPointLayout
end

-- source: ECDSAAdd/Arithmetic/PointRecoveryOperations.lean
noncomputable section

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

def pointRecoveryConstantAdd (L : ControlledPointLayout) (r : List Wire) (k : Fp) : Program :=
  compactRecoveryConstant (L.recoveryConstant r) L.core.generic SquareReduction.c p k.val
def pointRecoveryReflection (L : ControlledPointLayout) : Program :=
  L.recoveryNegate.reflection L.core.generic p

def pointRecoveryNegate (L : ControlledPointLayout) : Program :=
  L.recoveryNegate.program L.core.generic p SquareReduction.c

theorem pointRecoveryConstantAdd_correct (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y)
    (k : Fp) (X : Nat) (B : Bool) (hX : X<p) (s : State) (records : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue r s.basis=X) (hc : regValue L.dialogPool s.basis=0) :
    (run (pointRecoveryConstantAdd L r k) records s).phase=s.phase ∧
    regValue r (run (pointRecoveryConstantAdd L r k) records s).basis=(X+(if B then k.val else 0))%p ∧
    ∀q,q∉r → (run (pointRecoveryConstantAdd L r k) records s).basis q=s.basis q := by
  let K := L.recoveryConstant r
  have len : r.length=256 := by rcases hr with rfl|rfl;exact hw.inputX;exact hw.inputY
  have widths := L.recoveryConstant_widths hw r len
  have nd := L.recoveryConstant_nodup hw hn r hr
  have aux (q : Wire) (hq : q∈K.src++K.carry++[K.high,K.cin,K.flag]) : s.basis q=false := by
    change q∈(L.recoveryConstant r).src++(L.recoveryConstant r).carry++
      [(L.recoveryConstant r).high,(L.recoveryConstant r).cin,(L.recoveryConstant r).flag] at hq
    rw [L.recoveryConstant_pool hw r] at hq
    exact (regValue_zero _ _).mp hc q (List.mem_of_mem_take hq)
  have source : regValue K.src s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => aux q (by simp [hq]))
  have carries : ∀q∈K.carry,s.basis q=false := fun q hq => aux q (by simp [hq])
  have result := compactRecoveryConstant_correct K L.core.generic 256 SquareReduction.c p k.val widths nd
    (by decide) (by norm_num [p,SquareReduction.c]) (by norm_num [SquareReduction.c]) k.isLt X hX s records
    source hx (aux _ (by simp)) (aux _ (by simp)) carries (aux _ (by simp))
  simpa only [pointRecoveryConstantAdd,K,hb] using result

theorem pointRecoveryNegate_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X : Nat) (B : Bool) (hX : X<p) (s : State) (records : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=X) (hc : regValue L.dialogPool s.basis=0) :
    (run (pointRecoveryNegate L) records s).phase=s.phase ∧
    regValue L.point.x (run (pointRecoveryNegate L) records s).basis=(if B then (p-X)%p else X) ∧
    ∀q,q∉L.point.x → (run (pointRecoveryNegate L) records s).basis q=s.basis q := by
  let K := L.recoveryNegate
  have aux (q : Wire) (hq : q∈K.work++[K.cin,K.zero]) : s.basis q=false := by
    change q∈L.recoveryNegate.work++[L.recoveryNegate.cin,L.recoveryNegate.zero] at hq
    rw [L.recoveryNegate_pool hw] at hq
    exact (regValue_zero _ _).mp hc q (List.mem_of_mem_take hq)
  have work : regValue K.work s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => aux q (by simp [hq]))
  have sizes : K.work.length=K.word.length := by simp [K,recoveryNegate,point,hw.inputX,L.dialogPool_length hw]
  have npos : 0<K.word.length := by simp [K,recoveryNegate,point,hw.inputX]
  have pc : p+SquareReduction.c=2^K.word.length := by simp [K,recoveryNegate,point,hw.inputX];norm_num [p,SquareReduction.c]
  have result := K.program_correct L.core.generic (L.recoveryNegate_nodup hw hn) sizes npos p SquareReduction.c X
    pc (by norm_num [SquareReduction.c]) hX s records hx work (aux _ (by simp)) (aux _ (by simp))
  simpa only [pointRecoveryNegate,K,recoveryNegate,hb] using result

theorem pointRecoveryReflection_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X : Nat) (B : Bool) (hX : X<p) (s : State) (records : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=X) (hc : regValue L.dialogPool s.basis=0) :
    (run (pointRecoveryReflection L) records s).phase=s.phase ∧
    regValue L.point.x (run (pointRecoveryReflection L) records s).basis=(if B then p-1-X else X) ∧
    ∀q,q∉L.point.x → (run (pointRecoveryReflection L) records s).basis q=s.basis q := by
  let K := L.recoveryNegate
  have aux (q : Wire) (hq : q∈K.work++[K.cin,K.zero]) : s.basis q=false := by
    change q∈L.recoveryNegate.work++[L.recoveryNegate.cin,L.recoveryNegate.zero] at hq
    rw [L.recoveryNegate_pool hw] at hq
    exact (regValue_zero _ _).mp hc q (List.mem_of_mem_take hq)
  have work : regValue K.work s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => aux q (by simp [hq]))
  have sizes : K.work.length=K.word.length := by simp [K,recoveryNegate,point,hw.inputX,L.dialogPool_length hw]
  have npos : 0<K.word.length := by simp [K,recoveryNegate,point,hw.inputX]
  have result := K.reflection_correct L.core.generic (L.recoveryNegate_nodup hw hn) sizes npos p X
    (by simp [K,recoveryNegate,point,hw.inputX];norm_num [p]) hX s records hx work
    (aux _ (by simp)) (aux _ (by simp))
  simpa only [pointRecoveryNegate,K,recoveryNegate,hb] using result

theorem pointRecoveryConstantAdd_counts (L : ControlledPointLayout) (hw : L.Widths)
    (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y) (k : Fp) :
    toffoliCount (pointRecoveryConstantAdd L r k)=1023 ∧ measurementCount (pointRecoveryConstantAdd L r k)=1023 := by
  have len : r.length=256 := by rcases hr with rfl|rfl;exact hw.inputX;exact hw.inputY
  exact compactRecoveryConstant_counts _ _ 256 _ _ _ (L.recoveryConstant_widths hw r len) (by decide)

theorem pointRecoveryNegate_counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (pointRecoveryNegate L)=1022 ∧ measurementCount (pointRecoveryNegate L)=1022 := by
  have sizes : L.recoveryNegate.work.length=L.recoveryNegate.word.length := by
    simp [recoveryNegate,point,hw.inputX,L.dialogPool_length hw]
  have h := L.recoveryNegate.program_counts L.core.generic p SquareReduction.c sizes (by simp [recoveryNegate,point,hw.inputX])
  simpa [pointRecoveryNegate,recoveryNegate,point,hw.inputX] using h

theorem pointRecoveryConstantAdd_support (L : ControlledPointLayout) (hw : L.Widths) (r : List Wire) (k : Fp) :
    wires (pointRecoveryConstantAdd L r k)⊆(L.core.generic::r++L.dialogPool.take 515).toFinset := by
  have support := compactRecoveryConstant_support (L.recoveryConstant r) L.core.generic SquareReduction.c p k.val
  intro q hq
  have h := support hq
  rw [←L.recoveryConstant_pool hw r]
  simp only [recoveryConstant,MeasuredCanonicalModLayout.wires,List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
  tauto

theorem pointRecoveryNegate_support (L : ControlledPointLayout) (hw : L.Widths) :
    wires (pointRecoveryNegate L)⊆(L.core.generic::L.point.x++L.dialogPool.take 258).toFinset := by
  have sizes : L.recoveryNegate.work.length=L.recoveryNegate.word.length := by simp [recoveryNegate,point,hw.inputX,L.dialogPool_length hw]
  have support := L.recoveryNegate.program_support L.core.generic p SquareReduction.c sizes
  intro q hq
  have h := support hq
  rw [←L.recoveryNegate_pool hw]
  simp only [recoveryNegate,CompactRecoveryNegateLayout.wires,List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
  tauto

theorem pointRecoveryReflection_counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (pointRecoveryReflection L)=255 ∧ measurementCount (pointRecoveryReflection L)=255 := by
  have sizes : L.recoveryNegate.work.length=L.recoveryNegate.word.length := by
    simp [recoveryNegate,point,hw.inputX,L.dialogPool_length hw]
  have h := L.recoveryNegate.reflection_counts L.core.generic p sizes (by simp [recoveryNegate,point,hw.inputX])
  simpa [pointRecoveryReflection,recoveryNegate,point,hw.inputX] using h

theorem pointRecoveryReflection_support (L : ControlledPointLayout) (hw : L.Widths) :
    wires (pointRecoveryReflection L)⊆(L.core.generic::L.point.x++L.dialogPool.take 258).toFinset := by
  have support := L.recoveryNegate.reflection_support L.core.generic p
  intro q hq
  have h := support hq
  rw [←L.recoveryNegate_pool hw]
  simp only [recoveryNegate,CompactRecoveryNegateLayout.wires,List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
  tauto

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointDialogConstant.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

def pointDialogConstantAdd (L : ControlledPointLayout) (r : List Wire) (k : Fp) : Program :=
  pointRecoveryConstantAdd L r k

/-- Narrow exact canonical constant addition; phase and every non-target
site, including source/control/shared scratch, return for all records. -/
theorem pointDialogConstantAdd_correct (L : ControlledPointLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y)
    (k : Fp) (Z : Nat) (B : Bool) (hZ : Z<p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hz : regValue r s.basis=Z)
    (hc : regValue L.dialogPool s.basis=0) :
    (run (pointDialogConstantAdd L r k) m s).phase=s.phase ∧
      regValue r (run (pointDialogConstantAdd L r k) m s).basis=(Z+(if B then k.val else 0))%p ∧
      ∀ q∉r,(run (pointDialogConstantAdd L r k) m s).basis q=s.basis q :=
  pointRecoveryConstantAdd_correct L hw hnd r hr k Z B hZ s m hb hz hc

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointDialogDivide.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

/-- Exact Skywalk replacement with the original guarded divisor contract. -/
theorem pointDialog_arithmetic_correct (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (multiply : Bool) (X Y : Nat) (B : Bool)
    (hX : X<p) (hX0 : B=true → X≠0) (hY : Y<p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=X)
    (hy : regValue L.point.y s.basis=Y) (hc : regValue L.dialogPool s.basis=0) :
    let V := if B then (if multiply then ((Y:Fp)*(X:Fp)).val else ((Y:Fp)/(X:Fp)).val) else Y
    (run (pointOffsetBorrowedArithmetic L multiply) m s).phase=s.phase ∧
      regValue L.point.y (run (pointOffsetBorrowedArithmetic L multiply) m s).basis=V ∧
      ∀ q∉L.point.y,(run (pointOffsetBorrowedArithmetic L multiply) m s).basis q=s.basis q :=
  pointOffsetBorrowedArithmetic_correct L hw hn multiply X Y B hX hX0 hY s m hb hx hy hc

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointDialogNegate.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

def pointDialogNegate (L : ControlledPointLayout) : Program := pointRecoveryNegate L

/-- Compatibility with the existing public zero-work negation interface. -/
theorem pointDialogNegate_spec (L : ControlledPointLayout) (hw : L.Widths) (hnd : L.wires.Nodup)
    (A : Nat) (B : Bool) (hA : A<p) :
    (Triple (fun st => ((Holds.holds st L.core.generic B ∧ Holds.holds st L.dialogNegate.a A) ∧ Holds.holds st L.dialogNegate.z 0) ∧ Holds.holds st L.dialogNegate.work 0) (pointDialogNegate L)
      (fun st => ((Holds.holds st L.core.generic B ∧ Holds.holds st L.dialogNegate.a (if B then (p-A)%p else A)) ∧ Holds.holds st L.dialogNegate.z 0) ∧ Holds.holds st L.dialogNegate.work 0)) := by
  intro s m h
  simp only [Holds.holds] at h ⊢
  have he : L.dialogNegate.a=L.point.x++[L.core.poolWire 0] := by simp only [dialogNegate]
  have hpn : p<2^256 := by norm_num [p]
  have low := (regValue_low_iff L.point.x [L.core.poolWire 0] s.basis A
    (by rw [show L.point.x.length=256 from hw.inputX];exact hA.trans hpn)).mp (he ▸ h.1.1.2)
  let K := L.recoveryNegate
  have pool : [L.core.poolWire 0]++L.dialogNegate.z++L.dialogNegate.work=L.dialogPool.take 1030 :=
    L.dialogNegate_borrow hw
  have allZero : ∀q∈L.dialogPool.take 1030,s.basis q=false := by
    rw [←pool]
    intro q hq
    simp only [List.mem_append] at hq
    rcases hq with (hq|hq)|hq
    · exact (regValue_zero _ _).mp low.2 q hq
    · exact (regValue_zero _ _).mp h.1.2 q hq
    · exact (regValue_zero _ _).mp h.2 q hq
  have poolSubset : L.dialogPool.take 258⊆L.dialogPool.take 1030 := by
    intro q hq
    have eq : (L.dialogPool.take 1030).take 258=L.dialogPool.take 258 := by
      rw [List.take_take,Nat.min_eq_left (by omega)]
    rw [←eq] at hq
    exact List.mem_of_mem_take hq
  have aux (q : Wire) (hq : q∈K.work++[K.cin,K.zero]) : s.basis q=false := by
    change q∈L.recoveryNegate.work++[L.recoveryNegate.cin,L.recoveryNegate.zero] at hq
    rw [L.recoveryNegate_pool hw] at hq
    exact allZero q (poolSubset hq)
  have work : regValue K.work s.basis=0 := (regValue_zero _ _).mpr (fun q hq => aux q (by simp [hq]))
  have sizes : K.work.length=K.word.length := by simp [K,recoveryNegate,point,hw.inputX,L.dialogPool_length hw]
  have result := K.program_correct L.core.generic (L.recoveryNegate_nodup hw hnd) sizes
    (by simp [K,recoveryNegate,point,hw.inputX]) p SquareReduction.c A
    (by simp [K,recoveryNegate,point,hw.inputX];norm_num [p,SquareReduction.c])
    (by norm_num [SquareReduction.c]) hA s m low.1 work (aux _ (by simp)) (aux _ (by simp))
  rw [h.1.1.1] at result
  change (run (pointDialogNegate L) m s).phase=s.phase ∧
    regValue L.point.x (run (pointDialogNegate L) m s).basis=(if B then (p-A)%p else A) ∧
    (∀q,q∉L.point.x → (run (pointDialogNegate L) m s).basis q=s.basis q) at result
  have same (q : Wire) (hq : q∈L.core.generic::L.core.poolWire 0::L.dialogNegate.z++L.dialogNegate.work) :
      (run (pointDialogNegate L) m s).basis q=s.basis q := by
    apply result.2.2 q
    intro bad
    have nd := List.nodup_iff_count.mp (L.dialogNegate_nodup hw hnd) q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    simp only [ModInPlaceLayout.wires,he,List.count_cons,List.count_append,List.count_nil] at nd a
    omega
  refine ⟨result.1,⟨⟨?_,?_⟩,?_⟩,?_⟩
  · exact (same _ (by simp)).trans h.1.1.1
  · rw [he,regValue_append,result.2.1]
    have z : (run (pointDialogNegate L) m s).basis (L.core.poolWire 0)=false :=
      (same _ (by simp)).trans ((regValue_zero _ _).mp low.2 _ (by simp))
    simp [regValue,z]
  · exact (regValue_congr _ _ _ (fun q hq => same q (by simp [hq]))).trans h.1.2
  · exact (regValue_congr _ _ _ (fun q hq => same q (by simp [hq]))).trans h.2

theorem pointDialogNegate_correct (L : ControlledPointLayout) (hw : L.Widths) (hnd : L.wires.Nodup)
    (A : Nat) (B : Bool) (hA : A<p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=A)
    (hc : regValue L.dialogPool s.basis=0) :
    (run (pointDialogNegate L) m s).phase=s.phase ∧
      regValue L.point.x (run (pointDialogNegate L) m s).basis=(if B then (p-A)%p else A) ∧
      ∀ q∉L.point.x,(run (pointDialogNegate L) m s).basis q=s.basis q :=
  pointRecoveryNegate_correct L hw hnd A B hA s m hb hx hc

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointDialogSquare.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

/-- Exact controlled streamed square subtraction with clean branch boundaries. -/
def pointDialogSquare (L : ControlledPointLayout) : Program := pointMeasuredSquareCandidate L

theorem pointDialogSquare_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Nat) (B : Bool) (hX : X<p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=X)
    (hy : regValue L.point.y s.basis=Y) (hc : regValue L.dialogPool s.basis=0) :
    (run (pointDialogSquare L) m s).phase=s.phase ∧
    regValue L.point.x (run (pointDialogSquare L) m s).basis=
      (X+p-(if B then Y*Y else 0)%p)%p ∧
    ∀q,q∉L.point.x → (run (pointDialogSquare L) m s).basis q=s.basis q :=
  pointMeasuredSquareCandidate_correct L hw hn X Y B hX s m hb hx hy hc

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointDialogState.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

/-- 六阶段边界只有点坐标存活，池归零，其余线路逐线保持输入快照。 -/
structure PointDialogValues (L : ControlledPointLayout) (X Y : Fp) (G : Bool)
    (base s : BasisState) : Prop where
  x : regValue L.point.x s=X.val
  y : regValue L.point.y s=Y.val
  generic : s L.core.generic=G
  clean : regValue L.dialogPool s=0
  rest : ∀q,q∉L.point.x++L.point.y → s q=base q

namespace PointDialogValues
variable {L : ControlledPointLayout} {X X' Y Y' : Fp} {G : Bool} {base s t : BasisState}

theorem withX (hn : L.wires.Nodup) (v : PointDialogValues L X Y G base s)
    (hx : regValue L.point.x t=X'.val) (hf : ∀q,q∉L.point.x → t q=s q) :
    PointDialogValues L X' Y G base t := by
  have away (q : Wire) (hq : q∈L.point.y++[L.core.generic]++L.dialogPool) : q∉L.point.x := by
    intro hh
    have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hh
    simp only [dialogUsedWires,inPlaceFlags,PointAddLayout.pointWires,
      List.count_append,List.count_cons,List.count_nil] at h h1
    omega
  refine ⟨hx,?_,?_,?_,?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => hf q (away q (by simp [hq])))).trans v.y
  · exact (hf _ (away _ (by simp))).trans v.generic
  · exact (regValue_congr _ _ _ (fun q hq => hf q (away q (by simp [hq])))).trans v.clean
  · intro q hq; exact (hf q (fun h=>hq (List.mem_append_left _ h))).trans (v.rest q hq)

theorem withY (hn : L.wires.Nodup) (v : PointDialogValues L X Y G base s)
    (hy : regValue L.point.y t=Y'.val) (hf : ∀q,q∉L.point.y → t q=s q) :
    PointDialogValues L X Y' G base t := by
  have away (q : Wire) (hq : q∈L.point.x++[L.core.generic]++L.dialogPool) : q∉L.point.y := by
    intro hh
    have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hh
    simp only [dialogUsedWires,inPlaceFlags,PointAddLayout.pointWires,
      List.count_append,List.count_cons,List.count_nil] at h h1
    omega
  refine ⟨?_,hy,?_,?_,?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => hf q (away q (by simp [hq])))).trans v.x
  · exact (hf _ (away _ (by simp))).trans v.generic
  · exact (regValue_congr _ _ _ (fun q hq => hf q (away q (by simp [hq])))).trans v.clean
  · intro q hq; exact (hf q (fun h=>hq (List.mem_append_right _ h))).trans (v.rest q hq)
end PointDialogValues
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointDialogSteps.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1
private instance : NeZero p := ⟨by norm_num [p]⟩
private instance : Fact (1<p) := ⟨by norm_num [p]⟩

private theorem sub_val (x y : Fp) : (x-y).val=(x.val+p-y.val)%p := by
  rw [sub_eq_add_neg,ZMod.val_add,ZMod.neg_val',Nat.add_mod_mod]
  rw [←Nat.add_sub_assoc (le_of_lt (ZMod.val_lt y))]

variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (base : BasisState)
include hw hn

theorem dialogStep_addX (k : Fp) :
    Triple (PointDialogValues L X Y G base) (pointDialogConstantAdd L L.point.x k)
      (PointDialogValues L (X+(if G then k else 0)) Y G base) := by
  intro s m v
  obtain ⟨hp,hx,hf⟩ := pointDialogConstantAdd_correct L hw hn L.point.x (Or.inl rfl)
    k X.val G X.isLt s m v.generic v.x v.clean
  refine ⟨hp,v.withX hn ?_ hf⟩
  cases G <;> simpa [ZMod.val_add,Nat.mod_eq_of_lt (ZMod.val_lt X)] using hx

theorem dialogStep_addY (k : Fp) :
    Triple (PointDialogValues L X Y G base) (pointDialogConstantAdd L L.point.y k)
      (PointDialogValues L X (Y+(if G then k else 0)) G base) := by
  intro s m v
  obtain ⟨hp,hy,hf⟩ := pointDialogConstantAdd_correct L hw hn L.point.y (Or.inr rfl)
    k Y.val G Y.isLt s m v.generic v.y v.clean
  refine ⟨hp,v.withY hn ?_ hf⟩
  cases G <;> simpa [ZMod.val_add,Nat.mod_eq_of_lt (ZMod.val_lt Y)] using hy

theorem dialogStep_negate :
    Triple (PointDialogValues L X Y G base) (pointDialogNegate L)
      (PointDialogValues L (if G then -X else X) Y G base) := by
  intro s m v
  obtain ⟨hp,hx,hf⟩ := pointDialogNegate_correct L hw hn X.val G X.isLt s m v.generic v.x v.clean
  refine ⟨hp,v.withX hn ?_ hf⟩
  cases G <;> simpa only [Bool.false_eq_true,if_false,if_true,ZMod.neg_val'] using hx

theorem dialogStep_square :
    Triple (PointDialogValues L X Y G base) (pointDialogSquare L)
      (PointDialogValues L (X-(if G then Y*Y else 0)) Y G base) := by
  intro s m v
  obtain ⟨hp,hx,hf⟩ := pointDialogSquare_correct L hw hn X.val Y.val G X.isLt s m
    v.generic v.x v.y v.clean
  refine ⟨hp,v.withX hn ?_ hf⟩
  cases G <;> simpa [sub_val,ZMod.val_mul,Nat.mod_eq_of_lt (ZMod.val_lt X)] using hx

theorem dialogStep_arithmetic (multiply : Bool) (hX : G=true → X≠0) :
    Triple (PointDialogValues L X Y G base)
      (pointOffsetBorrowedArithmetic L multiply)
      (PointDialogValues L X (if G then (if multiply then Y*X else Y/X) else Y) G base) := by
  intro s m v
  have hX0 : G=true → X.val≠0 := by
    intro hg hx; apply hX hg; apply ZMod.val_injective p; simpa using hx
  obtain ⟨hp,hy,hf⟩ := pointDialog_arithmetic_correct L hw hn multiply X.val Y.val G
    X.isLt hX0 Y.isLt s m v.generic v.x v.y v.clean
  refine ⟨hp,v.withY hn ?_ hf⟩
  cases G <;> cases multiply <;> simpa only [Bool.false_eq_true,if_false,if_true,ZMod.natCast_zmod_val] using hy

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointRecoveryStage.lean
noncomputable section

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

/-- Stage 6: conditional canonical x reflection followed by the two classical
coordinate corrections. Every scratch bank is cleaned before reuse. -/
def pointRecoveryStage (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  pointRecoveryReflection L++pointDialogConstantAdd L L.point.x (cx+1)++pointDialogConstantAdd L L.point.y (-cy)

theorem pointRecoveryReflection_step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (base : BasisState) :
    Triple (PointDialogValues L X Y G base) (pointRecoveryReflection L)
      (PointDialogValues L (if G then -1-X else X) Y G base) := by
  intro s m v
  obtain ⟨phase,value,same⟩ := pointRecoveryReflection_correct L hw hn X.val G X.isLt s m v.generic v.x v.clean
  refine ⟨phase,v.withX hn ?_ same⟩
  cases G
  · simpa only [Bool.false_eq_true,if_false] using value
  · have xb : X.val<p := X.isLt
    have hp : 1≤p := by norm_num [p]
    have cast : ((p-1-X.val : Nat) : Fp)=-1-X := by
      rw [Nat.cast_sub (by omega : X.val≤p-1),Nat.cast_sub hp]
      simp only [ZMod.natCast_self,Nat.cast_one,zero_sub,ZMod.natCast_zmod_val]
    have val := congrArg ZMod.val cast
    rw [ZMod.val_natCast_of_lt (by omega : p-1-X.val<p)] at val
    exact (show regValue L.point.x (run (pointRecoveryReflection L) m s).basis=p-1-X.val from value).trans val

theorem pointRecoveryStage_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y cx cy : Fp) (G : Bool) (base : BasisState) :
    Triple (PointDialogValues L X Y G base) (pointRecoveryStage L cx cy)
      (PointDialogValues L (if G then cx-X else X) (if G then Y-cy else Y) G base) := by
  have a := pointRecoveryReflection_step L hw hn X Y G base
  have b := dialogStep_addX L hw hn (if G then -1-X else X) Y G base (cx+1)
  have c := dialogStep_addY L hw hn ((if G then -1-X else X)+(if G then cx+1 else 0)) Y G base (-cy)
  have all := (a.seq b).seq c
  have x : (if G then -1-X else X)+(if G then cx+1 else 0)=(if G then cx-X else X) := by
    cases G <;> simp; ring
  have y : Y+(if G then -cy else 0)=(if G then Y-cy else Y) := by cases G <;> simp [sub_eq_add_neg]
  rw [x,y] at all
  exact all

theorem pointRecoveryStage_counts (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    toffoliCount (pointRecoveryStage L cx cy)=2301 ∧ measurementCount (pointRecoveryStage L cx cy)=2301 := by
  have neg := pointRecoveryReflection_counts L hw
  have x := pointRecoveryConstantAdd_counts L hw L.point.x (Or.inl rfl) (cx+1)
  have y := pointRecoveryConstantAdd_counts L hw L.point.y (Or.inr rfl) (-cy)
  simp only [pointRecoveryStage,pointDialogConstantAdd,toffoliCount_append,
    measurementCount_append,neg.1,neg.2,x.1,x.2,y.1,y.2]
  decide

theorem pointRecoveryStage_support (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    wires (pointRecoveryStage L cx cy)⊆L.recoveryStageSites.toFinset := by
  have neg := pointRecoveryReflection_support L hw
  have x := pointRecoveryConstantAdd_support L hw L.point.x (cx+1)
  have y := pointRecoveryConstantAdd_support L hw L.point.y (-cy)
  have small : L.dialogPool.take 258⊆L.dialogPool.take 515 := by
    intro q hq
    have eq : (L.dialogPool.take 515).take 258=L.dialogPool.take 258 := by
      rw [List.take_take,Nat.min_eq_left (by omega)]
    rw [←eq] at hq
    exact List.mem_of_mem_take hq
  have en : (L.core.generic::L.point.x++L.dialogPool.take 258).toFinset⊆L.recoveryStageSites.toFinset := by
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq
    simp only [recoveryStageSites,PointAddLayout.pointWires,inPlaceFlags,List.mem_toFinset,
      List.mem_cons,List.mem_append,List.not_mem_nil,or_false]
    have ht : q∈L.dialogPool.take 258 → q∈L.dialogPool.take 515 := fun h => small h
    tauto
  have ex : (L.core.generic::L.point.x++L.dialogPool.take 515).toFinset⊆L.recoveryStageSites.toFinset := by
    intro q hq
    simp [recoveryStageSites,PointAddLayout.pointWires,inPlaceFlags] at hq ⊢
    tauto
  have ey : (L.core.generic::L.point.y++L.dialogPool.take 515).toFinset⊆L.recoveryStageSites.toFinset := by
    intro q hq
    simp [recoveryStageSites,PointAddLayout.pointWires,inPlaceFlags] at hq ⊢
    tauto
  simpa only [pointRecoveryStage,pointDialogConstantAdd,wires_append,Finset.union_subset_iff] using
    And.intro (And.intro (neg.trans en) (x.trans ex)) (y.trans ey)

/-- A certified allocation including residents bounds peak-live qubits;
this is not a measurement of the exact or minimum live peak. -/
theorem pointRecoveryStage_resource_targets (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (cx cy : Fp) :
    toffoliCount (pointRecoveryStage L cx cy)=2301 ∧
    measurementCount (pointRecoveryStage L cx cy)=2301 ∧
    qubitCount (pointRecoveryStage L cx cy)≤1036 ∧ L.recoveryStageSites.length=1036 ∧ 1036<1297 ∧ 2301<8000 := by
  have sites := L.recoveryStageSites_certified hw hn
  have counts := pointRecoveryStage_counts L hw cx cy
  refine ⟨counts.1,counts.2,?_,sites.2,by decide,by decide⟩
  rw [qubitCount]
  calc
    _ ≤ L.recoveryStageSites.toFinset.card := Finset.card_le_card (pointRecoveryStage_support L hw cx cy)
    _ = 1036 := by rw [List.toFinset_card_of_nodup sites.1,sites.2]

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Math/DialogPoint.lean
noncomputable section

namespace ECDSAAdd.Secp256k1

/-- 六阶段流程第二分母为零的唯一额外输入。 -/
def dialogExceptionPoint (C : Point) : Point := -(C+C)

/-- 只启用未被 O、倍点、相反点分支覆盖的新例外。 -/
def dialogExceptionEnabled (C : Point) : Prop :=
  dialogExceptionPoint C≠0 ∧ dialogExceptionPoint C≠C ∧ dialogExceptionPoint C≠-C

/-- 禁用重合的经典例外不会遗漏输入；尤其不假定不存在二阶点。 -/
theorem dialog_generic_iff (R C : Point) :
    (R≠0 ∧ (C≠-C → R≠C) ∧ R≠-C ∧ (dialogExceptionEnabled C → R≠dialogExceptionPoint C)) ↔
    (R≠0 ∧ R≠C ∧ R≠-C ∧ R≠dialogExceptionPoint C) := by
  constructor
  · rintro ⟨ho,hd,hi,hh⟩
    have hrc : R≠C := by
      by_cases hc : C=-C
      · exact fun he => hi (he.trans hc)
      · exact hd hc
    refine ⟨ho,hrc,hi,?_⟩
    intro he
    have hen : dialogExceptionEnabled C := by
      unfold dialogExceptionEnabled
      rw [← he]
      exact ⟨ho,hrc,hi⟩
    exact hh hen he
  · rintro ⟨ho,hd,hi,hh⟩
    exact ⟨ho,fun _ => hd,hi,fun _ => hh⟩

/-- 普通路径同时具有两个非零分母，不给点加规格添加新前提。 -/
theorem dialog_denominators_ne_zero {x y cx cy : Fp}
    (hr : curve.toAffine.Nonsingular x y) (hc : curve.toAffine.Nonsingular cx cy)
    (hR : (.some hr : Point)≠(.some hc : Point)) (hI : (.some hr : Point)≠-(.some hc : Point))
    (hH : (.some hr : Point)≠dialogExceptionPoint (.some hc)) :
    x≠cx ∧ cx-genericX x y cx cy≠0 := by
  have hx : x≠cx := by
    intro he
    rcases (sameX_iff_eq_or_neg hr hc).mp he with he|he
    · exact hR he
    · exact hI he
  exact ⟨hx,fun hz => hH ((second_denominator_zero_iff hr hc hx).mp hz)⟩

/-- 新例外的输出恒为 −C。 -/
theorem dialog_exception_add (C : Point) : dialogExceptionPoint C+C=-C := by
  unfold dialogExceptionPoint
  abel

/-- 从输出 −C 重算第四标志，控制为假时也成立。 -/
theorem dialog_translated_exception (R C : Point) (b : Bool) :
    let R' := if b then R+C else R
    (b=true ∧ dialogExceptionEnabled C ∧ R'=-C) ↔
      (b=true ∧ dialogExceptionEnabled C ∧ R=dialogExceptionPoint C) := by
  have he : R+C=-C ↔ R=dialogExceptionPoint C := by
    constructor
    · intro hh
      apply add_right_cancel (b:=C)
      rw [hh,dialog_exception_add]
    · intro hh; rw [hh,dialog_exception_add]
  cases b <;> simp [he]

/-- 四类输入标志两两互斥；倍点类与 H 类均有经典使能条件。 -/
theorem dialog_input_disjoint (R C : Point) (b : Bool) (hC : C≠0) :
    let o := b=true ∧ R=0
    let d := b=true ∧ C≠-C ∧ R=C
    let i := b=true ∧ R=-C
    let h := b=true ∧ dialogExceptionEnabled C ∧ R=dialogExceptionPoint C
    ¬(o∧d) ∧ ¬(o∧i) ∧ ¬(o∧h) ∧ ¬(d∧i) ∧ ¬(d∧h) ∧ ¬(i∧h) := by
  dsimp only
  have hn : -C≠0 := neg_ne_zero.mpr hC
  simp only [dialogExceptionEnabled]
  constructor
  · rintro ⟨⟨_,ho⟩,_,_,hd⟩; exact hC (hd.symm.trans ho)
  constructor
  · rintro ⟨⟨_,ho⟩,_,hi⟩; exact hn (hi.symm.trans ho)
  constructor
  · rintro ⟨⟨_,ho⟩,_,hh,he⟩; exact hh.1 (he.symm.trans ho)
  constructor
  · rintro ⟨⟨_,hd,he⟩,_,hi⟩; exact hd (he.symm.trans hi)
  constructor
  · rintro ⟨⟨_,_,hd⟩,_,hh,he⟩; exact hh.2.1 (he.symm.trans hd)
  · rintro ⟨⟨_,hi⟩,_,hh,he⟩; exact hh.2.2 (he.symm.trans hi)

/-- 输入分支平移到输出分支，四个谓词逐项一致。 -/
theorem dialog_translated_flags (R C : Point) (b : Bool) :
    let R' := if b then R+C else R
    ((b=true ∧ R'=C) ↔ (b=true ∧ R=0)) ∧
    ((b=true ∧ C≠-C ∧ R'=C+C) ↔ (b=true ∧ C≠-C ∧ R=C)) ∧
    ((b=true ∧ R'=0) ↔ (b=true ∧ R=-C)) ∧
    ((b=true ∧ dialogExceptionEnabled C ∧ R'=-C) ↔
      (b=true ∧ dialogExceptionEnabled C ∧ R=dialogExceptionPoint C)) := by
  have ht := translated_point_flags R C b
  exact ⟨ht.1,ht.2.1,ht.2.2,dialog_translated_exception R C b⟩

/-- 输出检测的四类也互斥，无需假设 C≠−C。 -/
theorem dialog_output_disjoint (R C : Point) (b : Bool) (hC : C≠0) :
    let R' := if b then R+C else R
    let o := b=true ∧ R'=C
    let d := b=true ∧ C≠-C ∧ R'=C+C
    let i := b=true ∧ R'=0
    let h := b=true ∧ dialogExceptionEnabled C ∧ R'=-C
    ¬(o∧d) ∧ ¬(o∧i) ∧ ¬(o∧h) ∧ ¬(d∧i) ∧ ¬(d∧h) ∧ ¬(i∧h) := by
  dsimp only
  have ht := dialog_translated_flags R C b
  rw [ht.1,ht.2.1,ht.2.2.1,ht.2.2.2]
  exact dialog_input_disjoint R C b hC

end ECDSAAdd.Secp256k1
end

-- source: ECDSAAdd/Math/DialogPointFlags.lean
noncomputable section

namespace ECDSAAdd.Secp256k1
variable [DecidableEq Point]

def dialogInfinity (b : Bool) (R : Point) : Bool := b && decide (R=0)
def dialogDouble (b : Bool) (R C : Point) : Bool := b && decide (C≠-C) && decide (R=C)
def dialogInversePoint (b : Bool) (R C : Point) : Bool := b && decide (R=-C)
def dialogException (b : Bool) (R C : Point) : Bool :=
  b && decide (dialogExceptionPoint C≠0 ∧ dialogExceptionPoint C≠C ∧ dialogExceptionPoint C≠-C) &&
    decide (R=dialogExceptionPoint C)
def dialogOrdinary (b : Bool) (R C : Point) : Bool :=
  b ^^ dialogInfinity b R ^^ dialogDouble b R C ^^ dialogInversePoint b R C ^^ dialogException b R C

@[simp] theorem dialogException_zero (b : Bool) (C : Point) : dialogException b 0 C=false := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.false_eq_true, iff_false, dialogException,Bool.and_eq_true,decide_eq_true_eq]
  rintro ⟨⟨_,he⟩,hr⟩
  exact he.1 hr.symm

@[simp] theorem dialogException_self (b : Bool) (C : Point) : dialogException b C C=false := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.false_eq_true, iff_false, dialogException,Bool.and_eq_true,decide_eq_true_eq]
  rintro ⟨⟨_,he⟩,hr⟩
  exact he.2.1 hr.symm

@[simp] theorem dialogException_neg (b : Bool) (C : Point) : dialogException b (-C) C=false := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.false_eq_true, iff_false, dialogException,Bool.and_eq_true,decide_eq_true_eq]
  rintro ⟨⟨_,he⟩,hr⟩
  exact he.2.2 hr.symm

/-- 四个互斥角落的XOR余位正好选择普通分支。 -/
theorem dialogOrdinary_true (b : Bool) (R C : Point) (hc : C≠0) :
    dialogOrdinary b R C=true ↔
      b=true ∧ R≠0 ∧ R≠C ∧ R≠-C ∧ R≠dialogExceptionPoint C := by
  have hnc : -C≠0 := neg_ne_zero.mpr hc
  cases b with
  | false => simp [dialogOrdinary,dialogInfinity,dialogDouble,dialogInversePoint,dialogException]
  | true =>
    by_cases h0 : R=0
    · subst R
      simp [dialogOrdinary,dialogInfinity,dialogDouble,dialogInversePoint,
        Ne.symm hc,Ne.symm hnc]
    by_cases h1 : R=C
    · subst R
      by_cases h2 : C=-C
      · have he : (C=-C) ↔ True := iff_true_intro h2
        simp [dialogOrdinary,dialogInfinity,dialogDouble,dialogInversePoint,hc,he]
      · simp [dialogOrdinary,dialogInfinity,dialogDouble,dialogInversePoint,hc,h2]
    by_cases h2 : R=-C
    · subst R
      simp [dialogOrdinary,dialogInfinity,dialogDouble,dialogInversePoint,hnc,h1]
    by_cases hh : R=dialogExceptionPoint C
    · have hen : dialogExceptionPoint C≠0 ∧ dialogExceptionPoint C≠C ∧ dialogExceptionPoint C≠-C := by
        rw [← hh]; exact ⟨h0,h1,h2⟩
      simp [dialogOrdinary,dialogInfinity,dialogDouble,dialogInversePoint,dialogException,hh,hen]
    · simp [dialogOrdinary,dialogInfinity,dialogDouble,dialogInversePoint,dialogException,h0,h1,h2,hh]

/-- 输出检测重算四个布尔标志，可对接pointEqual的decide桥。 -/
theorem dialogFlags_output (b : Bool) (R C : Point) :
    let S := if b then R+C else R
    (b && decide (S=C))=dialogInfinity b R ∧
    (b && decide (C≠-C) && decide (S=C+C))=dialogDouble b R C ∧
    (b && decide (S=0))=dialogInversePoint b R C ∧
    (b && decide (dialogExceptionPoint C≠0 ∧ dialogExceptionPoint C≠C ∧ dialogExceptionPoint C≠-C) &&
      decide (S=-C))=dialogException b R C := by
  have ht := dialog_translated_flags R C b
  dsimp only
  simp only [dialogInfinity,dialogDouble,dialogInversePoint,dialogException]
  refine ⟨?_,?_,?_,?_⟩ <;> apply Bool.eq_iff_iff.mpr
  · simpa only [Bool.and_eq_true,decide_eq_true_eq] using ht.1
  · simpa only [Bool.and_eq_true,decide_eq_true_eq,← and_assoc] using ht.2.1
  · simpa only [Bool.and_eq_true,decide_eq_true_eq] using ht.2.2.1
  · simpa only [Bool.and_eq_true,decide_eq_true_eq,dialogExceptionEnabled,← and_assoc] using ht.2.2.2


/-- 四类角落的XOR写回，包含H与−C两次常量更新。 -/
theorem dialogCorners_nat (b : Bool) (R C : Point) (hc : C≠0) (f : Point → Nat) (hf : f 0=0) :
    ((((((f (if dialogOrdinary b R C then R+C else R) ^^^
      (if dialogInfinity b R then f C else 0)) ^^^
      (if dialogDouble b R C then f C else 0)) ^^^
      (if dialogDouble b R C then f (C+C) else 0)) ^^^
      (if dialogInversePoint b R C then f (-C) else 0)) ^^^
      (if dialogException b R C then f (dialogExceptionPoint C) else 0)) ^^^
      (if dialogException b R C then f (-C) else 0) ) = f (if b then R+C else R) := by
  have hnc : -C≠0 := neg_ne_zero.mpr hc
  cases b with
  | false => simp [dialogOrdinary,dialogInfinity,dialogDouble,dialogInversePoint,dialogException]
  | true =>
    by_cases h0 : R=0
    · subst R
      simp [dialogOrdinary,dialogInfinity,dialogDouble,dialogInversePoint,
        Ne.symm hc,Ne.symm hnc,hf]
    by_cases h1 : R=C
    · subst R
      by_cases h2 : C=-C
      · have hz : C+C=0 := add_eq_zero_iff_eq_neg.mpr h2
        simp [dialogOrdinary,dialogInfinity,dialogDouble,dialogInversePoint,hc,hz,hf,← h2]
      · simp [dialogOrdinary,dialogInfinity,dialogDouble,dialogInversePoint,hc,h2]
    by_cases h2 : R=-C
    · subst R
      simp [dialogOrdinary,dialogInfinity,dialogDouble,dialogInversePoint,hnc,h1,hf]
    by_cases hh : R=dialogExceptionPoint C
    · have hen : dialogExceptionPoint C≠0 ∧ dialogExceptionPoint C≠C ∧ dialogExceptionPoint C≠-C := by
        rw [← hh]; exact ⟨h0,h1,h2⟩
      simp [dialogOrdinary,dialogInfinity,dialogDouble,dialogInversePoint,dialogException,hh,hen,dialog_exception_add]
    · simp [dialogOrdinary,dialogInfinity,dialogDouble,dialogInversePoint,dialogException,h0,h1,h2,hh]


/-- 四类角落的XOR写回，包含H与−C两次常量更新。 -/
theorem dialogCorners_bool (b : Bool) (R C : Point) (hc : C≠0) (f : Point → Bool) (hf : f 0=false) :
    ((((((f (if dialogOrdinary b R C then R+C else R) ^^
      (if dialogInfinity b R then f C else false)) ^^
      (if dialogDouble b R C then f C else false)) ^^
      (if dialogDouble b R C then f (C+C) else false)) ^^
      (if dialogInversePoint b R C then f (-C) else false)) ^^
      (if dialogException b R C then f (dialogExceptionPoint C) else false)) ^^
      (if dialogException b R C then f (-C) else false) ) = f (if b then R+C else R) := by
  have hnc : -C≠0 := neg_ne_zero.mpr hc
  cases b with
  | false => simp [dialogOrdinary,dialogInfinity,dialogDouble,dialogInversePoint,dialogException]
  | true =>
    by_cases h0 : R=0
    · subst R
      simp [dialogOrdinary,dialogInfinity,dialogDouble,dialogInversePoint,
        Ne.symm hc,Ne.symm hnc,hf]
    by_cases h1 : R=C
    · subst R
      by_cases h2 : C=-C
      · have hz : C+C=0 := add_eq_zero_iff_eq_neg.mpr h2
        simp [dialogOrdinary,dialogInfinity,dialogDouble,dialogInversePoint,hc,hz,hf,← h2]
      · simp [dialogOrdinary,dialogInfinity,dialogDouble,dialogInversePoint,hc,h2]
    by_cases h2 : R=-C
    · subst R
      simp [dialogOrdinary,dialogInfinity,dialogDouble,dialogInversePoint,hnc,h1,hf]
    by_cases hh : R=dialogExceptionPoint C
    · have hen : dialogExceptionPoint C≠0 ∧ dialogExceptionPoint C≠C ∧ dialogExceptionPoint C≠-C := by
        rw [← hh]; exact ⟨h0,h1,h2⟩
      simp [dialogOrdinary,dialogInfinity,dialogDouble,dialogInversePoint,dialogException,hh,hen,dialog_exception_add]
    · simp [dialogOrdinary,dialogInfinity,dialogDouble,dialogInversePoint,dialogException,h0,h1,h2,hh]

end ECDSAAdd.Secp256k1
end

-- source: ECDSAAdd/Arithmetic/PointDialogProgram.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

/-- 一次除法、专用平方、一次乘法；斜率直接存于当前y。 -/
def pointDialogGeneric (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  pointDialogConstantAdd L L.point.x (-cx) ++
  pointDialogConstantAdd L L.point.y (-cy) ++
  pointOffsetBorrowedArithmetic L false ++
  pointDialogSquare L ++
  pointDialogConstantAdd L L.point.x (3*cx) ++
  pointOffsetBorrowedArithmetic L true ++
  pointRecoveryStage L cx cy

/-- 标志别名：equalX=hEnable，equalNegY=h；其余三个输入分类仍为o/d/i。 -/
def pointDialogGenericFlag (L : ControlledPointLayout) : Program :=
  pointInPlaceGenericFlag L ++ [.CX L.core.equalNegY L.core.generic]

def pointDialogExceptionEnable (L : ControlledPointLayout) (C : Point) : Program :=
  if !pointEqual (dialogExceptionPoint C) 0 && !pointEqual (dialogExceptionPoint C) C &&
      !pointEqual (dialogExceptionPoint C) (-C) then [.CX L.control L.core.equalX] else []

def pointDialogCorners (L : ControlledPointLayout) (C : Point) : Program :=
  pointInPlaceCorners L C ++
  maskedPointConstant L.core.equalNegY L.point (dialogExceptionPoint C) ++
  maskedPointConstant L.core.equalNegY L.point (-C)

def pointDialogFinite (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  pointInPlaceDoubleEnable L cy ++ pointDialogExceptionEnable L C ++
  equalConstant L.control L.infinitySelect L.dialogPointZero (pointCode 0) ++
  equalConstant L.core.double L.doubleSelect L.dialogPointZero (pointCode C) ++
  equalConstant L.control L.genericSelect L.dialogPointZero (pointCode (-C)) ++
  equalConstant L.core.equalX L.core.equalNegY L.dialogPointZero (pointCode (dialogExceptionPoint C)) ++
  pointDialogGenericFlag L ++ pointDialogGeneric L cx cy ++ pointDialogCorners L C ++
  pointDialogGenericFlag L ++
  equalConstant L.control L.infinitySelect L.dialogPointZero (pointCode C) ++
  equalConstant L.core.double L.doubleSelect L.dialogPointZero (pointCode (C+C)) ++
  equalConstant L.control L.genericSelect L.dialogPointZero (pointCode 0) ++
  equalConstant L.core.equalX L.core.equalNegY L.dialogPointZero (pointCode (-C)) ++
  pointDialogExceptionEnable L C ++ pointInPlaceDoubleEnable L cy

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompressedPointDialogProgram.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1 MappedCompressed

/-- 一次除法、专用平方、一次乘法；斜率直接存于当前y。 -/
def pointCompressedDialogGeneric (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  pointDialogConstantAdd L L.point.x (-cx) ++
  pointDialogConstantAdd L L.point.y (-cy) ++
  pointCompressedArithmetic L false ++
  CompressedPointSquare.computableProgram L ++
  pointDialogConstantAdd L L.point.x (3*cx) ++
  pointCompressedArithmetic L true ++
  pointRecoveryStage L cx cy

def pointCompressedDialogFinite (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  pointInPlaceDoubleEnable L cy ++ pointDialogExceptionEnable L C ++
  equalConstant L.control L.infinitySelect L.dialogPointZero (pointCode 0) ++
  equalConstant L.core.double L.doubleSelect L.dialogPointZero (pointCode C) ++
  equalConstant L.control L.genericSelect L.dialogPointZero (pointCode (-C)) ++
  equalConstant L.core.equalX L.core.equalNegY L.dialogPointZero (pointCode (dialogExceptionPoint C)) ++
  pointDialogGenericFlag L ++ pointCompressedDialogGeneric L cx cy ++ pointDialogCorners L C ++
  pointDialogGenericFlag L ++
  equalConstant L.control L.infinitySelect L.dialogPointZero (pointCode C) ++
  equalConstant L.core.double L.doubleSelect L.dialogPointZero (pointCode (C+C)) ++
  equalConstant L.control L.genericSelect L.dialogPointZero (pointCode 0) ++
  equalConstant L.core.equalX L.core.equalNegY L.dialogPointZero (pointCode (-C)) ++
  pointDialogExceptionEnable L C ++ pointInPlaceDoubleEnable L cy

/-- Candidate full in-place point addition; infinity constant emits no gates. -/
def pointCompressedAdd (L : ControlledPointLayout) (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _hc =>
      pointCompressedDialogFinite L C cx cy

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/SquareSubResources.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

theorem squareSub_counts (L : SquareSubLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    toffoliCount (squareSub L)=275129 ∧ measurementCount (squareSub L)=275129 := by
  have hk := karatsubaSquare_counts L.integer (L.integer_valid hw hn)
  have hr := squareReduce_counts L.reduction (L.reduction_widths hw)
  have ho := modSubInPlace_resources L.output 256 SquareReduction.p (L.output_widths hw)
    (L.output_nodup hn) (by omega)
  simp only [squareSub,toffoliCount_append,measurementCount_append,hk.1.1,hk.1.2,hk.2.1,hk.2.2,
    hr.1.1,hr.1.2,hr.2.1,hr.2.2,ho.1,ho.2.1]
  norm_num

/-- 全部门列均位于输入、目标及2217位工作区内。 -/
theorem squareSub_wires_subset (L : SquareSubLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    wires (squareSub L)⊆L.wires.toFinset := by
  have ik : L.integer.wires.toFinset⊆L.wires.toFinset := by
    intro w hm
    have h := List.count_pos_iff.mpr (List.mem_toFinset.mp hm)
    have hx := congrArg (List.count w) (List.take_append_drop 128 L.x)
    have hp := congrArg (List.count w) (List.take_append_drop 128 L.pad)
    have hr := (List.take_sublist 258 L.r).count_le w
    apply List.mem_toFinset.mpr
    apply List.count_pos_iff.mp
    simp only [SquareSubLayout.wires,SquareSubLayout.work,SquareSubLayout.integer,
      KaratsubaSquareLayout.wires,List.count_append,List.count_cons,List.count_nil] at h hx hp ⊢
    omega
  have ir : L.reduction.wires.toFinset⊆L.wires.toFinset := by
    intro w hm
    have h := List.count_pos_iff.mpr (List.mem_toFinset.mp hm)
    have hz := congrArg (List.count w) (List.take_append_drop 256 L.z)
    apply List.mem_toFinset.mpr
    apply List.count_pos_iff.mp
    simp only [SquareSubLayout.wires,SquareSubLayout.work,SquareSubLayout.reduction,
      SquareReduceLayout.wires,List.count_append,List.count_cons,List.count_nil] at h hz ⊢
    omega
  have io : L.output.toModAddCoreLayout.wires.toFinset⊆L.wires.toFinset := by
    intro w hm
    have h := List.count_pos_iff.mpr (List.mem_toFinset.mp hm)
    have hr := (List.take_sublist 256 L.r).count_le w
    have hc := (List.take_sublist 256 L.carry).count_le w
    apply List.mem_toFinset.mpr
    apply List.count_pos_iff.mp
    simp only [SquareSubLayout.wires,SquareSubLayout.work,SquareSubLayout.output,
      ModAddCoreLayout.wires,ModAddCoreLayout.z,ModAddCoreLayout.work,
      List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have hk := karatsubaSquare_wires_subset L.integer (L.integer_valid hw hn)
  have hr := squareReduce_wires_subset L.reduction (L.reduction_widths hw)
  have ho : wires (modSubInPlace L.output SquareReduction.p)⊆L.wires.toFinset := by
    rw [modSubInPlace_wires L.output 256 SquareReduction.p (L.output_widths hw) (by omega)]
    exact io
  simp only [squareSub,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨hk.1.trans ik,hr.1.trans ir⟩,ho⟩,hr.2.trans ir⟩,hk.2.trans ik⟩

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointDialogCounts.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Secp256k1 ControlledPointLayout

/-- 常数掩码只含CX；每段成本完全来自同一模加核。 -/
theorem pointDialogConstantAdd_counts (L : ControlledPointLayout) (hw : L.Widths)
    (_hnd : L.wires.Nodup) (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y) (k : Fp) :
    toffoliCount (pointDialogConstantAdd L r k)=1023 ∧
    measurementCount (pointDialogConstantAdd L r k)=1023 := by
  exact pointRecoveryConstantAdd_counts L hw r hr k

/-- Direct exact negation with shared zero/carry workspace; retained as a public utility. -/
theorem pointDialogNegate_counts (L : ControlledPointLayout) (hw : L.Widths) (_hnd : L.wires.Nodup) :
    toffoliCount (pointDialogNegate L)=1022 ∧ measurementCount (pointDialogNegate L)=1022 :=
  pointRecoveryNegate_counts L hw


theorem pointDialogSquare_counts (L : ControlledPointLayout) (hw : L.Widths) (_hn : L.wires.Nodup) :
    toffoliCount (pointDialogSquare L)=99902 ∧
      measurementCount (pointDialogSquare L)=99382 :=
  pointMeasuredSquareCandidate_counts L hw

theorem pointDialogGeneric_counts (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (cx cy : Fp) :
    toffoliCount (pointDialogGeneric L cx cy)=2216223 ∧
    measurementCount (pointDialogGeneric L cx cy)=1558291 := by
  have ha k := pointDialogConstantAdd_counts L hw hn L.point.x (Or.inl rfl) k
  have hb k := pointDialogConstantAdd_counts L hw hn L.point.y (Or.inr rfl) k
  have hd := pointOffsetBorrowedArithmetic_counts L hw hn
  have hs := pointDialogSquare_counts L hw hn
  have recovery := pointRecoveryStage_counts L hw cx cy
  simp only [pointDialogGeneric,toffoliCount_append,measurementCount_append,
    (ha _).1,(ha _).2,(hb _).1,(hb _).2,hd.1,hd.2.1,hd.2.2.1,hd.2.2.2,
    hs.1,hs.2,recovery.1,recovery.2]
  norm_num

theorem pointDialogFinite_counts (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (C : Point) (cx cy : Fp) :
    toffoliCount (pointDialogFinite L C cx cy)=2220327 ∧
    measurementCount (pointDialogFinite L C cx cy)=1562395 := by
  have hg := pointDialogGeneric_counts L hw hn cx cy
  have hz c t k := equalConstant_counts c t L.dialogPointZero k
  have hpl : (PointAddLayout.pointWires L.point).length=513 := by
    simp only [PointAddLayout.pointWires,List.length_cons,List.length_append,
      show L.point.x.length=256 from hw.inputX,show L.point.y.length=256 from hw.inputY]
  have hzl : L.dialogPointZero.length=513 := by
    have he := (zeroPorts_maps (PointAddLayout.pointWires L.point) (L.dialogPool.take 513)
      (by simp only [List.length_take,L.dialogPool_length hw]; exact hpl)).1
    simpa only [List.length_map,hpl] using congrArg List.length he
  have he : toffoliCount (pointInPlaceDoubleEnable L cy)=0 ∧
      measurementCount (pointInPlaceDoubleEnable L cy)=0 := by
    unfold pointInPlaceDoubleEnable
    split <;> simp [toffoliCount,measurementCount]
  have hh : toffoliCount (pointDialogExceptionEnable L C)=0 ∧
      measurementCount (pointDialogExceptionEnable L C)=0 := by
    unfold pointDialogExceptionEnable
    split <;> simp [toffoliCount,measurementCount]
  simp only [pointDialogFinite,pointDialogCorners,pointInPlaceCorners,toffoliCount_append,
    measurementCount_append,hg.1,hg.2,(hz _ _ _).1,(hz _ _ _).2,hzl,
    (maskedPointConstant_counts _ _ _).1,(maskedPointConstant_counts _ _ _).2,he.1,he.2,hh.1,hh.2]
  norm_num [pointDialogGenericFlag,pointInPlaceGenericFlag,toffoliCount,measurementCount]

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointDialogGeneric.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

theorem pointDialogGeneric_true (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y cx cy : Fp) (base : BasisState) (hX : X≠cx) (hd : cx-genericX X Y cx cy≠0) :
    Triple (PointDialogValues L X Y true base) (pointDialogGeneric L cx cy)
      (PointDialogValues L (genericX X Y cx cy) (genericY X Y cx cy) true base) := by
  let a := genericSlope X Y cx cy
  let d := cx-genericX X Y cx cy
  have hv := generic_inplace_values X Y cx cy hX
  have h1 := dialogStep_addX L hw hn X Y true base (-cx)
  have h2 := dialogStep_addY L hw hn (X-cx) Y true base (-cy)
  simp only [if_true,←sub_eq_add_neg] at h1 h2
  have h3 := dialogStep_arithmetic L hw hn (X-cx) (Y-cy) true base false (fun _=>sub_ne_zero.mpr hX)
  have ha : (Y-cy)/(X-cx)=a := rfl
  simp only [if_true,Bool.false_eq_true,if_false,ha] at h3
  have h4 := dialogStep_square L hw hn (X-cx) a true base
  simp only [if_true] at h4
  have h5 := dialogStep_addX L hw hn ((X-cx)-a*a) a true base (3*cx)
  simp only [if_true] at h5
  rw [show (X-cx)-a*a+3*cx=d from hv.2.1] at h5
  have h6 := dialogStep_arithmetic L hw hn d a true base true (fun _=>hd)
  simp only [if_true] at h6
  have recovery := pointRecoveryStage_correct L hw hn d (a*d) cx cy true base
  simp only [if_true] at recovery
  rw [show cx-d=genericX X Y cx cy by dsimp [d];ring] at recovery
  rw [show a*d-cy=genericY X Y cx cy from hv.2.2] at recovery
  have h := (((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq recovery
  simpa only [pointDialogGeneric,List.append_assoc] using h

theorem pointDialogGeneric_false (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y cx cy : Fp) (base : BasisState) :
    Triple (PointDialogValues L X Y false base) (pointDialogGeneric L cx cy)
      (PointDialogValues L X Y false base) := by
  have h1 := dialogStep_addX L hw hn X Y false base (-cx)
  have h2 := dialogStep_addY L hw hn X Y false base (-cy)
  have h3 := dialogStep_arithmetic L hw hn X Y false base false (by simp)
  have h4 := dialogStep_square L hw hn X Y false base
  have h5 := dialogStep_addX L hw hn X Y false base (3*cx)
  have h6 := dialogStep_arithmetic L hw hn X Y false base true (by simp)
  have recovery := pointRecoveryStage_correct L hw hn X Y cx cy false base
  simp only [Bool.false_eq_true,if_false,if_true,add_zero,sub_zero] at h1 h2 h3 h4 h5 h6 recovery
  have h := (((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq recovery
  simpa only [pointDialogGeneric,List.append_assoc] using h

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointInPlaceConstant.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

private theorem constant_mask (M : ModInPlaceLayout) (c : Wire) (k A Z : Nat) (B : Bool)
    (hn : (c::M.wires).Nodup) (hk : k<2^M.a.length) :
    (Triple (fun st => ((Holds.holds st c B ∧ Holds.holds st M.a A) ∧ Holds.holds st M.z Z) ∧ Holds.holds st M.work 0) (maskedConstant c M.a k)
      (fun st => ((Holds.holds st c B ∧ Holds.holds st M.a (A ^^^ (if B then k else 0))) ∧ Holds.holds st M.z Z) ∧ Holds.holds st M.work 0)) := by
  have hc : c∉M.a := by
    intro h
    exact (List.nodup_cons.mp hn).1 (by simp [ModInPlaceLayout.wires,h])
  have hna : M.a.Nodup := by
    have h := (List.nodup_cons.mp hn).2
    exact (List.nodup_append.mp (List.nodup_append.mp h).1).1
  intro s m h
  simp only [Holds.holds] at h ⊢
  obtain ⟨hp,hframe,hvalue⟩ := maskedConstant_correct c M.a k hna hc hk s m
  have away (q : Wire) (hq : q∈M.z++M.work) : q∉M.a := by
    intro ha
    have h := List.nodup_iff_count.mp hn q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr ha
    simp only [ModInPlaceLayout.wires,List.count_append,List.count_cons] at h h1
    omega
  refine ⟨hp,⟨⟨(hframe c hc).trans h.1.1.1,?_⟩,?_⟩,?_⟩
  · simpa only [h.1.1.1,h.1.1.2] using hvalue
  · exact (regValue_congr _ _ _ (fun q hq => hframe q (away q (List.mem_append_left _ hq)))).trans h.1.2
  · exact (regValue_congr _ _ _ (fun q hq => hframe q (away q (List.mem_append_right _ hq)))).trans h.2

private theorem constant_add (M : ModInPlaceLayout) (c : Wire) (A Z : Nat) (B : Bool)
    (hw : M.Widths 256) (hn : (c::M.wires).Nodup) (hA : A≤p) (hZ : Z<p) :
    (Triple (fun st => ((Holds.holds st c B ∧ Holds.holds st M.a A) ∧ Holds.holds st M.z Z) ∧ Holds.holds st M.work 0) (modAddInPlace M p)
      (fun st => ((Holds.holds st c B ∧ Holds.holds st M.a A) ∧ Holds.holds st M.z ((Z+A)%p)) ∧ Holds.holds st M.work 0)) := by
  intro s m h
  have hp : 0<p := by norm_num [p]
  have hpn : p<2^256 := by norm_num [p]
  have hnd := (List.nodup_cons.mp hn).2
  obtain ⟨hf,hv⟩ := modAddInPlace_spec M 256 p A Z hw hnd hp hpn hA hZ
    s m ⟨⟨h.1.1.2,h.1.2⟩,h.2⟩
  have hc : c∉M.z := by
    intro hh
    exact (List.nodup_cons.mp hn).1 (by simp [ModInPlaceLayout.wires,hh])
  have keep := modAddInPlace_frame M 256 p A Z hw hnd hp hpn hA hZ s m h.1.1.2 h.1.2 h.2 c hc
  exact ⟨hf,⟨⟨keep.trans h.1.1.1,hv.1.1⟩,hv.1.2⟩,hv.2⟩

/-- 掩码源在模加后仍保留，第二次CX序列将其清零。 -/
theorem constant_program_spec (M : ModInPlaceLayout) (c : Wire) (k Z : Nat) (B : Bool)
    (hw : M.Widths 256) (hn : (c::M.wires).Nodup) (hk : k<p) (hZ : Z<p) :
    (Triple (fun st => ((Holds.holds st c B ∧ Holds.holds st M.a 0) ∧ Holds.holds st M.z Z) ∧ Holds.holds st M.work 0) (maskedConstant c M.a k ++ modAddInPlace M p ++ maskedConstant c M.a k)
      (fun st => ((Holds.holds st c B ∧ Holds.holds st M.a 0) ∧ Holds.holds st M.z ((Z+(if B then k else 0))%p)) ∧ Holds.holds st M.work 0)) := by
  have hkp : k<2^M.a.length := by
    simp only [hw.core.a,Nat.reduceAdd]
    have hp : p<2^256 := by norm_num [p]
    have hmono (n : Nat) : 2^n≤2^(n+1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hm := hmono 256
    simp only [Nat.reduceAdd] at hm
    exact hk.trans (hp.trans_le hm)
  have ha := constant_mask M c k 0 Z B hn hkp
  simp only [Nat.zero_xor] at ha
  have hb := constant_add M c (if B then k else 0) Z B hw hn (by split <;> omega) hZ
  have hc := constant_mask M c k (if B then k else 0) ((Z+(if B then k else 0))%p) B hn hkp
  simpa only [Nat.xor_self] using (ha.seq hb).seq hc

theorem constant_program_frame (M : ModInPlaceLayout) (c : Wire) (k Z : Nat) (B : Bool)
    (hw : M.Widths 256) (hn : (c::M.wires).Nodup) (hk : k<p) (hZ : Z<p)
    (s : State) (m : List Bool) (hb : s.basis c=B) (ha : regValue M.a s.basis=0)
    (hz : regValue M.z s.basis=Z) (hc : regValue M.work s.basis=0)
    (q : Wire) (hq : q∉M.z) :
    (run (maskedConstant c M.a k ++ modAddInPlace M p ++ maskedConstant c M.a k) m s).basis q=s.basis q := by
  obtain ⟨_,hv⟩ := constant_program_spec M c k Z B hw hn hk hZ s m ⟨⟨⟨hb,ha⟩,hz⟩,hc⟩
  by_cases hqc : q=c
  · subst q; exact hv.1.1.1.trans hb.symm
  by_cases hqa : q∈M.a
  · exact (regValue_eq_iff _ _ _).mp (hv.1.1.2.trans ha.symm) q hqa
  by_cases hqw : q∈M.work
  · exact (regValue_eq_iff _ _ _).mp (hv.2.trans hc.symm) q hqw
  apply run_preserves_outside
  intro hh
  have hm := maskedConstant_wires_subset c M.a k
  rw [wires_append,wires_append] at hh
  have hcore : q∉M.toModAddCoreLayout.wires := by
    intro hh'
    have hw' : q∉M.toModAddCoreLayout.work := by
      intro h; exact hqw (by simp [ModInPlaceLayout.work,h])
    simp only [ModAddCoreLayout.wires,List.mem_append,ModInPlaceLayout.z] at hh' hq
    tauto
  have hmask : q∉wires (maskedConstant c M.a k) := by
    intro h; have h' := hm h
    simp [hqc,hqa] at h'
  have hmid : q∉wires (modAddInPlace M p) := by
    rw [modAddInPlace,modAddCore_wires M.toModAddCoreLayout 256 p hw.core (by omega)]
    simpa using hcore
  simp [hmask,hmid] at hh

/-- 常数加法在低256位上给出规范结果，源、目标高位及其余线路逐线恢复。 -/
theorem pointInPlaceConstantAdd_correct (L : ControlledPointLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y)
    (k : Fp) (Z : Nat) (B : Bool) (hZ : Z<p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hz : regValue r s.basis=Z)
    (hc : regValue L.inPlaceBorrow s.basis=0) :
    (run (pointInPlaceConstantAdd L r k) m s).phase=s.phase ∧
      regValue r (run (pointInPlaceConstantAdd L r k) m s).basis=(Z+(if B then k.val else 0))%p ∧
      ∀ q∉r,(run (pointInPlaceConstantAdd L r k) m s).basis q=s.basis q := by
  let M := L.inPlaceConstant r
  have hl : r.length=256 := by rcases hr with rfl | rfl; exact hw.inputX; exact hw.inputY
  have hM := L.inPlaceConstant_widths hw r hl
  have hnm : (L.core.generic::M.wires).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp (L.inPlace_interfaces_nodup hw hnd) q
    have ht := (List.take_sublist 1030 L.inPlaceBorrow).count_le q
    rw [← L.inPlaceConstant_borrow hw r] at ht
    have hbc := L.inPlaceBorrow_count q
    rcases hr with rfl | rfl
    all_goals
      simp only [M,inPlaceConstant,inPlaceUnary,ModInPlaceLayout.wires,ModInPlaceLayout.z,ModInPlaceLayout.work,
        ModUnaryLayout.core,ModAddCoreLayout.z,ModAddCoreLayout.work,PointAddLayout.pointWires,inPlaceFlags,
        List.count_append,List.count_cons,List.count_nil] at h ht ⊢
      omega
  have hs : L.inPlaceBorrow.take 257++[L.inPlaceBit 257]++M.work ⊆ L.inPlaceBorrow := by
    rw [L.inPlaceConstant_borrow hw r]
    exact (List.take_sublist _ _).subset
  have clean := (regValue_zero _ _).mp hc
  have hhigh : s.basis (L.inPlaceBit 257)=false := clean _ (hs (by simp))
  have ha : M.a=L.inPlaceBorrow.take 257 := by simp only [M,inPlaceConstant]
  have hsource : regValue M.a s.basis=0 := by
    rw [ha]
    exact (regValue_zero _ _).mpr
      (fun q hq => clean q (hs (List.mem_append_left _ (List.mem_append_left _ hq))))
  have hwork : regValue M.work s.basis=0 := (regValue_zero _ _).mpr
    (fun q hq => clean q (hs (List.mem_append_right _ hq)))
  have hout : regValue M.z s.basis=Z := by
    simp only [M,inPlaceConstant,ModInPlaceLayout.z,ModUnaryLayout.core,inPlaceUnary,ModAddCoreLayout.z]
    rw [regValue_append,hz]
    simp [regValue,hhigh]
  obtain ⟨hp,hv⟩ := constant_program_spec M L.core.generic k.val Z B hM hnm k.isLt hZ
    s m ⟨⟨⟨hb,hsource⟩,hout⟩,hwork⟩
  have keep := constant_program_frame M L.core.generic k.val Z B hM hnm k.isLt hZ s m hb hsource hout hwork
  have hzView : M.z=r++[L.inPlaceBit 257] := by
    simp only [M,inPlaceConstant,ModInPlaceLayout.z,ModUnaryLayout.core,inPlaceUnary,ModAddCoreLayout.z]
  rw [hzView] at hv
  have hlow := (regValue_low_iff r [L.inPlaceBit 257]
    (run (pointInPlaceConstantAdd L r k) m s).basis ((Z+(if B then k.val else 0))%p)
    (by rw [hl]; exact (Nat.mod_lt _ (by norm_num [p])).trans (by norm_num [p]))).mp hv.1.2
  refine ⟨hp,hlow.1,?_⟩
  intro q hq
  by_cases he : q=L.inPlaceBit 257
  · subst q
    exact ((regValue_zero _ _).mp hlow.2 _ (by simp)).trans hhigh.symm
  · apply keep q
    simp only [M,inPlaceConstant,ModInPlaceLayout.z,ModUnaryLayout.core,inPlaceUnary,ModAddCoreLayout.z]
    simp [hq,he]

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointInPlaceNegate.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout

private theorem negate_swap (L : ControlledPointLayout) (hw : L.Widths) (hnd : L.wires.Nodup)
    (A T : Nat) (B : Bool) (hA : A<p) (hT : T<p) :
    (Triple (fun st => ((Holds.holds st L.core.generic B ∧ Holds.holds st L.inPlaceNegate.a A) ∧ Holds.holds st L.inPlaceNegate.z T) ∧ Holds.holds st L.inPlaceNegate.work 0) (swapRegisters L.core.generic L.point.x L.inPlaceNegate.low)
      (fun st => ((Holds.holds st L.core.generic B ∧ Holds.holds st L.inPlaceNegate.a (if B then T else A)) ∧ Holds.holds st L.inPlaceNegate.z (if B then A else T)) ∧ Holds.holds st L.inPlaceNegate.work 0)) := by
  have hn := L.inPlaceNegate_nodup hw hnd
  have hm := L.inPlaceNegate_widths hw
  have he : L.inPlaceNegate.a=L.point.x++[L.inPlaceBit 0] := by
    simp only [inPlaceNegate]
  have hswap : (L.core.generic::L.point.x++L.inPlaceNegate.low).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [ModInPlaceLayout.wires,he,ModInPlaceLayout.z,ModAddCoreLayout.z,
      List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have away (q : Wire) (hq : q∈L.core.generic::L.inPlaceBit 0::L.inPlaceNegate.high::L.inPlaceNegate.work) :
      q∉L.point.x ∧ q∉L.inPlaceNegate.low := by
    have h := List.nodup_iff_count.mp hn q
    have hpos := List.count_pos_iff.mpr hq
    simp only [ModInPlaceLayout.wires,he,ModInPlaceLayout.z,ModAddCoreLayout.z,
      List.count_append,List.count_cons,List.count_nil] at h hpos
    constructor
    all_goals intro hq'; have hp := List.count_pos_iff.mpr hq'; omega
  intro s m h
  simp only [Holds.holds] at h ⊢
  have hp : p<2^256 := by norm_num [p]
  have hx := (regValue_low_iff L.point.x [L.inPlaceBit 0] s.basis A
    (by rw [show L.point.x.length=256 from hw.inputX]; exact hA.trans hp)).mp (he ▸ h.1.1.2)
  have ht := (regValue_low_iff L.inPlaceNegate.low [L.inPlaceNegate.high] s.basis T
    (by rw [hm.core.low]; exact hT.trans hp)).mp h.1.2
  obtain ⟨hphase,hframe,hx',ht'⟩ := swapRegisters_correct L.core.generic L.point.x L.inPlaceNegate.low
    (hw.inputX.trans hm.core.low.symm) hswap s m
  have keep (q : Wire) (hq : q∈L.core.generic::L.inPlaceBit 0::L.inPlaceNegate.high::L.inPlaceNegate.work) :=
    hframe q (away q hq).1 (away q hq).2
  have h0 := keep (L.inPlaceBit 0) (by simp)
  have h1 := keep L.inPlaceNegate.high (by simp)
  have high0 := (regValue_zero _ _).mp hx.2 (L.inPlaceBit 0) (by simp)
  have high1 := (regValue_zero _ _).mp ht.2 L.inPlaceNegate.high (by simp)
  refine ⟨hphase,⟨⟨(keep _ (by simp)).trans h.1.1.1,?_⟩,?_⟩,?_⟩
  · rw [he,regValue_append,hx',h.1.1.1,ht.1,hx.1]
    simp [regValue,h0,high0]
  · change regValue (L.inPlaceNegate.low++[L.inPlaceNegate.high]) _=_
    rw [regValue_append,ht',h.1.1.1,hx.1,ht.1]
    simp [regValue,h1,high1]
  · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans h.2

/-- 规范取负的三阶段规格；关闭控制时仍执行固定门列并清理临时寄存器。 -/
theorem pointInPlaceNegate_spec (L : ControlledPointLayout) (hw : L.Widths) (hnd : L.wires.Nodup)
    (A : Nat) (B : Bool) (hA : A<p) :
    (Triple (fun st => ((Holds.holds st L.core.generic B ∧ Holds.holds st L.inPlaceNegate.a A) ∧ Holds.holds st L.inPlaceNegate.z 0) ∧ Holds.holds st L.inPlaceNegate.work 0) (pointInPlaceNegate L)
      (fun st => ((Holds.holds st L.core.generic B ∧ Holds.holds st L.inPlaceNegate.a (if B then (p-A)%p else A)) ∧ Holds.holds st L.inPlaceNegate.z 0) ∧ Holds.holds st L.inPlaceNegate.work 0)) := by
  have hp : 0<p := by norm_num [p]
  have hpn : p<2^256 := by norm_num [p]
  have hm := L.inPlaceNegate_widths hw
  have hn := L.inPlaceNegate_nodup hw hnd
  have hs := controlledModSub_spec L.core.generic L.inPlaceNegate 256 p A 0 B hm hn hp hpn
    (Nat.le_of_lt hA) hp
  simp only [Nat.zero_add] at hs
  have ht := negate_swap L hw hnd A (if B then (p-A)%p else 0) B hA
    (by split; exact Nat.mod_lt _ hp; exact hp)
  have ha := controlledModAdd_spec L.core.generic L.inPlaceNegate 256 p
    (if B then (if B then (p-A)%p else 0) else A) (if B then A else (if B then (p-A)%p else 0)) B
    hm hn hp hpn (by cases B <;> simp; omega; exact Nat.le_of_lt (Nat.mod_lt _ hp))
    (by cases B <;> simp; exact hp; exact hA)
  have hresult : (if B then ((if B then A else (if B then (p-A)%p else 0))+
      (if B then (if B then (p-A)%p else 0) else A))%p else (if B then A else (if B then (p-A)%p else 0)))=0 := by
    cases B
    · rfl
    · simp only [if_true]
      rw [Nat.add_mod_mod,Nat.add_sub_of_le (Nat.le_of_lt hA),Nat.mod_self]
  have h := (hs.seq ht).seq ha
  have he : (if B then (if B then (p-A)%p else 0) else A)=(if B then (p-A)%p else A) := by cases B <;> rfl
  rw [hresult] at h
  simpa only [pointInPlaceNegate,he] using h

/-- 取负后仅输入x的低位改变，临时差、高位与所有其它线路恢复。 -/
theorem pointInPlaceNegate_correct (L : ControlledPointLayout) (hw : L.Widths) (hnd : L.wires.Nodup)
    (A : Nat) (B : Bool) (hA : A<p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=A)
    (hc : regValue L.inPlaceBorrow s.basis=0) :
    (run (pointInPlaceNegate L) m s).phase=s.phase ∧
      regValue L.point.x (run (pointInPlaceNegate L) m s).basis=(if B then (p-A)%p else A) ∧
      ∀ q∉L.point.x,(run (pointInPlaceNegate L) m s).basis q=s.basis q := by
  have hm := L.inPlaceNegate_widths hw
  have hp : 0<p := by norm_num [p]
  have hp2 : p<2^256 := by norm_num [p]
  have he : L.inPlaceNegate.a=L.point.x++[L.inPlaceBit 0] := by simp only [inPlaceNegate]
  have hs : [L.inPlaceBit 0]++L.inPlaceNegate.z++L.inPlaceNegate.work ⊆ L.inPlaceBorrow := by
    rw [L.inPlaceNegate_borrow hw]
    exact (List.take_sublist _ _).subset
  have clean := (regValue_zero _ _).mp hc
  have hhigh : s.basis (L.inPlaceBit 0)=false := clean _ (hs (by simp))
  have ha : regValue L.inPlaceNegate.a s.basis=A := by
    rw [he,regValue_append,hx]
    simp [regValue,hhigh]
  have hz : regValue L.inPlaceNegate.z s.basis=0 := (regValue_zero _ _).mpr
    (fun q hq => clean q (hs (List.mem_append_left _ (List.mem_append_right _ hq))))
  have hwork : regValue L.inPlaceNegate.work s.basis=0 := (regValue_zero _ _).mpr
    (fun q hq => clean q (hs (List.mem_append_right _ hq)))
  obtain ⟨hphase,hv⟩ := pointInPlaceNegate_spec L hw hnd A B hA s m ⟨⟨⟨hb,ha⟩,hz⟩,hwork⟩
  have hvbound : (if B then (p-A)%p else A)<p := by split; exact Nat.mod_lt _ hp; exact hA
  have hlow := (regValue_low_iff L.point.x [L.inPlaceBit 0] (run (pointInPlaceNegate L) m s).basis
    (if B then (p-A)%p else A) (by rw [show L.point.x.length=256 from hw.inputX]; exact hvbound.trans hp2)).mp
    (he ▸ hv.1.1.2)
  refine ⟨hphase,hlow.1,?_⟩
  intro q hq
  by_cases hqb : q=L.core.generic
  · subst q; exact hv.1.1.1.trans hb.symm
  by_cases hq0 : q=L.inPlaceBit 0
  · subst q; exact ((regValue_zero _ _).mp hlow.2 _ (by simp)).trans hhigh.symm
  by_cases hqz : q∈L.inPlaceNegate.z
  · exact (regValue_eq_iff _ _ _).mp (hv.1.2.trans hz.symm) q hqz
  by_cases hqw : q∈L.inPlaceNegate.work
  · exact (regValue_eq_iff _ _ _).mp (hv.2.trans hwork.symm) q hqw
  have hqa : q∉L.inPlaceNegate.a := by rw [he]; simp [hq,hq0]
  have subset (M : ModInPlaceLayout) : M.maskedCore.wires ⊆ M.z++M.work := by
    intro w hh
    simp only [ModInPlaceLayout.maskedCore,ModAddCoreLayout.wires,ModAddCoreLayout.z,
      ModAddCoreLayout.work,ModInPlaceLayout.z,ModInPlaceLayout.work,List.mem_append,List.mem_cons] at hh ⊢
    grind only
  have hmask : q∉L.inPlaceNegate.maskedCore.wires := by
    intro hh
    have hh' := subset L.inPlaceNegate hh
    simp only [List.mem_append] at hh'
    exact hh'.elim hqz hqw
  have hqlow : q∉L.inPlaceNegate.low := by
    intro h; exact hqz (by simp [ModInPlaceLayout.z,ModAddCoreLayout.z,h])
  have hswap : q∉wires (swapRegisters L.core.generic L.point.x L.inPlaceNegate.low) := by
    intro h
    have hh := swapRegisters_wires L.core.generic L.point.x L.inPlaceNegate.low (hw.inputX.trans hm.core.low.symm) h
    simp [hqb,hq,hqlow] at hh
  apply run_preserves_outside
  simp only [pointInPlaceNegate,wires_append,controlledModSub_wires _ _ 256 p hm (by omega),
    controlledModAdd_wires _ _ 256 p hm (by omega),Finset.mem_union,List.mem_toFinset,List.mem_cons,
    List.mem_append,not_or]
  have htake : q∉L.inPlaceNegate.a.take 256 := fun h => hqa ((List.take_sublist _ _).subset h)
  simp only [hqb,hqa,hmask,hswap,htake,not_false_eq_true,and_self]

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointInPlaceProduct.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout

/-- 外部乘加/乘减只改当前y；两个扩展高位和全部借用位在边界归零。 -/
theorem pointInPlaceProduct_correct (L : ControlledPointLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (A X Y : Nat) (hA : A<p) (hX : X<p) (hY : Y<p)
    (s : State) (m : List Bool) (ha : regValue L.inPlaceSlope s.basis=A)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y)
    (hz : regValue L.inPlaceBorrow s.basis=0) :
    ((run (montMulAdd L.inPlaceMultiply p) m s).phase=s.phase ∧
      regValue L.point.y (run (montMulAdd L.inPlaceMultiply p) m s).basis=(Y+(A*X)%p)%p ∧
      ∀ q∉L.point.y,(run (montMulAdd L.inPlaceMultiply p) m s).basis q=s.basis q) ∧
    ((run (montMulSub L.inPlaceMultiply p) m s).phase=s.phase ∧
      regValue L.point.y (run (montMulSub L.inPlaceMultiply p) m s).basis=(Y+p-(A*X)%p)%p ∧
      ∀ q∉L.point.y,(run (montMulSub L.inPlaceMultiply p) m s).basis q=s.basis q) := by
  letI : Fact p.Prime := ⟨Secp256k1.p_prime⟩
  have hp : p<2^256 := by norm_num [p]
  have hp0 : 0<p := by norm_num [p]
  have hs : [L.inPlaceBit 0,L.inPlaceBit 1]++L.inPlaceMultiply.work ⊆ L.inPlaceBorrow := by
    rw [L.inPlaceMultiply_borrow hw]
    exact (List.take_sublist _ _).subset
  have clean := (regValue_zero _ _).mp hz
  have h0 : s.basis (L.inPlaceBit 0)=false := clean _ (hs (by simp))
  have h1 : s.basis (L.inPlaceBit 1)=false := clean _ (hs (by simp))
  have hwork : regValue L.inPlaceMultiply.work s.basis=0 := (regValue_zero _ _).mpr
    (fun q hq => clean q (hs (List.mem_append_right _ hq)))
  have hin : regValue L.inPlaceMultiply.x s.basis=A := by
    change regValue (L.inPlaceSlope++[L.inPlaceBit 0]) s.basis=A
    rw [regValue_append,ha]
    simp [regValue,h0]
  have hout : regValue L.inPlaceMultiply.out s.basis=Y := by
    change regValue (L.point.y++[L.inPlaceBit 1]) s.basis=Y
    rw [regValue_append,hy]
    simp [regValue,h1]
  have hwf := L.inPlaceMultiply_widths hw
  have hnf := L.inPlaceMultiply_nodup hw hnd
  have keep (q : Wire) (hq : q∉L.inPlaceMultiply.out) := And.intro
    (montMulAdd_frame L.inPlaceMultiply p A X Y hwf hnf hp secp256k1_mod_sixteen hA (hX.trans hp) hY
      s m hin hx hout hwork q hq)
    (montMulSub_frame L.inPlaceMultiply p A X Y hwf hnf hp secp256k1_mod_sixteen hA (hX.trans hp) hY
      s m hin hx hout hwork q hq)
  have finish (P : Program) (V : Nat) (hV : V<p)
      (hphase : (run P m s).phase=s.phase)
      (hval : regValue L.inPlaceMultiply.out (run P m s).basis=V)
      (hframe : ∀ q∉L.inPlaceMultiply.out,(run P m s).basis q=s.basis q) :
      (run P m s).phase=s.phase ∧ regValue L.point.y (run P m s).basis=V ∧
        ∀ q∉L.point.y,(run P m s).basis q=s.basis q := by
    have hlow := (regValue_low_iff L.point.y [L.inPlaceBit 1] (run P m s).basis V
      (by rw [show L.point.y.length=256 from hw.inputY]; exact hV.trans hp)).mp hval
    refine ⟨hphase,hlow.1,?_⟩
    intro q hq
    by_cases he : q=L.inPlaceBit 1
    · subst q
      exact ((regValue_zero _ _).mp hlow.2 _ (by simp)).trans h1.symm
    · apply hframe q
      change q∉L.point.y++[L.inPlaceBit 1]
      simp [hq,he]
  obtain ⟨hpa,hva⟩ := montMulAdd_spec L.inPlaceMultiply p A X Y hwf hnf hp secp256k1_mod_sixteen hA (hX.trans hp) hY
    s m ⟨⟨⟨hin,hx⟩,hout⟩,hwork⟩
  obtain ⟨hps,hvs⟩ := montMulSub_spec L.inPlaceMultiply p A X Y hwf hnf hp secp256k1_mod_sixteen hA (hX.trans hp) hY
    s m ⟨⟨⟨hin,hx⟩,hout⟩,hwork⟩
  exact ⟨finish _ _ (Nat.mod_lt _ hp0) hpa hva.1.2 (fun q hq => (keep q hq).1),
    finish _ _ (Nat.mod_lt _ hp0) hps hvs.1.2 (fun q hq => (keep q hq).2)⟩

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/KaratsubaSquareState.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- The retained half-squares and temporary registers at composition boundaries. -/
structure KaratsubaValues (L : KaratsubaSquareLayout) (lo hi av dv cv zv sv : Nat)
    (s : BasisState) : Prop where
  low : regValue L.low s=lo
  high : regValue L.high s=hi
  a : regValue L.a s=av
  d : regValue L.d s=dv
  c : regValue L.c s=cv
  z : regValue L.z s=zv
  sum : regValue L.sum s=sv
  pad : regValue L.pad s=0
  mask : regValue L.mask s=0
  carry : regValue L.carry s=0
  cin : s L.cin=false

namespace KaratsubaValues

private theorem keep (L : KaratsubaSquareLayout) (h : L.Valid) (r dst : List Wire)
    (hc : ∀ w,r.count w+dst.count w≤L.wires.count w) (s u : BasisState)
    (hf : ∀ w,w∉dst→u w=s w) : regValue r u=regValue r s := by
  apply regValue_congr
  intro w hw
  apply hf
  intro hd
  have hn := List.nodup_iff_count.mp h.nodup w
  have hr := List.count_pos_iff.mpr hw
  have ht := List.count_pos_iff.mpr hd
  have hh := hc w
  omega

theorem update_a (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi av dv cv zv sv V : Nat) (s u : BasisState)
    (hs : KaratsubaValues L lo hi av dv cv zv sv s)
    (hv : regValue L.a u=V) (hf : ∀ w,w∉L.a→u w=s w) :
    KaratsubaValues L lo hi V dv cv zv sv u := by
  have same (r : List Wire) (hc : ∀ w,r.count w+L.a.count w≤L.wires.count w) :
      regValue r u=regValue r s := keep L h r L.a hc s u hf
  refine ⟨?_,?_,hv,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · apply Eq.trans (same L.low (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.low
  · apply Eq.trans (same L.high (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.high
  · apply Eq.trans (same L.d (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.d
  · apply Eq.trans (same L.c (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.c
  · apply Eq.trans (same L.z (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.z
  · apply Eq.trans (same L.sum (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.sum
  · apply Eq.trans (same L.pad (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.pad
  · apply Eq.trans (same L.mask (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.mask
  · apply Eq.trans (same L.carry (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.carry
  · apply Eq.trans (hf L.cin (by
      intro hw
      have hh := List.nodup_iff_count.mp h.nodup L.cin
      have ht := List.count_pos_iff.mpr hw
      simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at hh
      simp only [beq_self_eq_true,ite_true] at hh
      omega)) hs.cin

theorem update_d (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi av dv cv zv sv V : Nat) (s u : BasisState)
    (hs : KaratsubaValues L lo hi av dv cv zv sv s)
    (hv : regValue L.d u=V) (hf : ∀ w,w∉L.d→u w=s w) :
    KaratsubaValues L lo hi av V cv zv sv u := by
  have same (r : List Wire) (hc : ∀ w,r.count w+L.d.count w≤L.wires.count w) :
      regValue r u=regValue r s := keep L h r L.d hc s u hf
  refine ⟨?_,?_,?_,hv,?_,?_,?_,?_,?_,?_,?_⟩
  · apply Eq.trans (same L.low (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.low
  · apply Eq.trans (same L.high (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.high
  · apply Eq.trans (same L.a (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.a
  · apply Eq.trans (same L.c (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.c
  · apply Eq.trans (same L.z (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.z
  · apply Eq.trans (same L.sum (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.sum
  · apply Eq.trans (same L.pad (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.pad
  · apply Eq.trans (same L.mask (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.mask
  · apply Eq.trans (same L.carry (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.carry
  · apply Eq.trans (hf L.cin (by
      intro hw
      have hh := List.nodup_iff_count.mp h.nodup L.cin
      have ht := List.count_pos_iff.mpr hw
      simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at hh
      simp only [beq_self_eq_true,ite_true] at hh
      omega)) hs.cin

theorem update_c (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi av dv cv zv sv V : Nat) (s u : BasisState)
    (hs : KaratsubaValues L lo hi av dv cv zv sv s)
    (hv : regValue L.c u=V) (hf : ∀ w,w∉L.c→u w=s w) :
    KaratsubaValues L lo hi av dv V zv sv u := by
  have same (r : List Wire) (hc : ∀ w,r.count w+L.c.count w≤L.wires.count w) :
      regValue r u=regValue r s := keep L h r L.c hc s u hf
  refine ⟨?_,?_,?_,?_,hv,?_,?_,?_,?_,?_,?_⟩
  · apply Eq.trans (same L.low (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.low
  · apply Eq.trans (same L.high (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.high
  · apply Eq.trans (same L.a (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.a
  · apply Eq.trans (same L.d (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.d
  · apply Eq.trans (same L.z (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.z
  · apply Eq.trans (same L.sum (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.sum
  · apply Eq.trans (same L.pad (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.pad
  · apply Eq.trans (same L.mask (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.mask
  · apply Eq.trans (same L.carry (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.carry
  · apply Eq.trans (hf L.cin (by
      intro hw
      have hh := List.nodup_iff_count.mp h.nodup L.cin
      have ht := List.count_pos_iff.mpr hw
      simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at hh
      simp only [beq_self_eq_true,ite_true] at hh
      omega)) hs.cin

theorem update_z (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi av dv cv zv sv V : Nat) (s u : BasisState)
    (hs : KaratsubaValues L lo hi av dv cv zv sv s)
    (hv : regValue L.z u=V) (hf : ∀ w,w∉L.z→u w=s w) :
    KaratsubaValues L lo hi av dv cv V sv u := by
  have same (r : List Wire) (hc : ∀ w,r.count w+L.z.count w≤L.wires.count w) :
      regValue r u=regValue r s := keep L h r L.z hc s u hf
  refine ⟨?_,?_,?_,?_,?_,hv,?_,?_,?_,?_,?_⟩
  · apply Eq.trans (same L.low (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.low
  · apply Eq.trans (same L.high (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.high
  · apply Eq.trans (same L.a (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.a
  · apply Eq.trans (same L.d (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.d
  · apply Eq.trans (same L.c (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.c
  · apply Eq.trans (same L.sum (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.sum
  · apply Eq.trans (same L.pad (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.pad
  · apply Eq.trans (same L.mask (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.mask
  · apply Eq.trans (same L.carry (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.carry
  · apply Eq.trans (hf L.cin (by
      intro hw
      have hh := List.nodup_iff_count.mp h.nodup L.cin
      have ht := List.count_pos_iff.mpr hw
      simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at hh
      simp only [beq_self_eq_true,ite_true] at hh
      omega)) hs.cin

theorem update_sum (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi av dv cv zv sv V : Nat) (s u : BasisState)
    (hs : KaratsubaValues L lo hi av dv cv zv sv s)
    (hv : regValue L.sum u=V) (hf : ∀ w,w∉L.sum→u w=s w) :
    KaratsubaValues L lo hi av dv cv zv V u := by
  have same (r : List Wire) (hc : ∀ w,r.count w+L.sum.count w≤L.wires.count w) :
      regValue r u=regValue r s := keep L h r L.sum hc s u hf
  refine ⟨?_,?_,?_,?_,?_,?_,hv,?_,?_,?_,?_⟩
  · apply Eq.trans (same L.low (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.low
  · apply Eq.trans (same L.high (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.high
  · apply Eq.trans (same L.a (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.a
  · apply Eq.trans (same L.d (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.d
  · apply Eq.trans (same L.c (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.c
  · apply Eq.trans (same L.z (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.z
  · apply Eq.trans (same L.pad (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.pad
  · apply Eq.trans (same L.mask (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.mask
  · apply Eq.trans (same L.carry (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.carry
  · apply Eq.trans (hf L.cin (by
      intro hw
      have hh := List.nodup_iff_count.mp h.nodup L.cin
      have ht := List.count_pos_iff.mpr hw
      simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at hh
      simp only [beq_self_eq_true,ite_true] at hh
      omega)) hs.cin

end KaratsubaValues

theorem karatsuba_squareLow_spec (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi _av dv cv zv sv : Nat) :
    Triple (KaratsubaValues L lo hi 0 dv cv zv sv) L.squareLow
      (KaratsubaValues L lo hi (lo^2) dv cv zv sv) := by
  have hn : (L.cin::L.low++L.a++L.pad++L.mask++L.carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have hh := List.nodup_iff_count.mp h.nodup w
    simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at hh ⊢; omega
  have hd : L.a.length=2*L.low.length := by simp [h.a_length,h.low_length]
  have hp : L.low.length-1≤L.pad.length := by simp [h.low_length,h.pad_length]
  have hm : 2*(L.low.length-1)≤L.mask.length := by simp [h.low_length,h.mask_length]
  have hk : 2*(L.low.length-1)-1≤L.carry.length := by simp [h.low_length,h.carry_length]
  intro s m hs
  have hr := triangularSquare_spec L.low L.a L.pad L.mask L.carry L.cin
    hn hd hp hm hk lo s m ⟨⟨⟨⟨⟨hs.low,hs.a⟩,hs.pad⟩,hs.mask⟩,hs.carry⟩,hs.cin⟩
  have hf := triangularSquare_frame L.low L.a L.pad L.mask L.carry L.cin
    hn hd hp hm hk s m hs.a hs.pad hs.mask hs.carry hs.cin
  exact ⟨hr.1,KaratsubaValues.update_a L h _ _ _ _ _ _ _ _ _ _ hs hr.2.1.1.1.1.2 hf⟩

theorem karatsuba_clearLow_spec (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi _av dv cv zv sv : Nat) :
    Triple (KaratsubaValues L lo hi (lo^2) dv cv zv sv) L.clearLow
      (KaratsubaValues L lo hi 0 dv cv zv sv) := by
  have hn : (L.cin::L.low++L.a++L.pad++L.mask++L.carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have hh := List.nodup_iff_count.mp h.nodup w
    simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at hh ⊢; omega
  have hd : L.a.length=2*L.low.length := by simp [h.a_length,h.low_length]
  have hp : L.low.length-1≤L.pad.length := by simp [h.low_length,h.pad_length]
  have hm : 2*(L.low.length-1)≤L.mask.length := by simp [h.low_length,h.mask_length]
  have hk : 2*(L.low.length-1)-1≤L.carry.length := by simp [h.low_length,h.carry_length]
  intro s m hs
  have hr := triangularSquareClear_spec L.low L.a L.pad L.mask L.carry L.cin
    hn hd hp hm hk lo s m ⟨⟨⟨⟨⟨hs.low,hs.a⟩,hs.pad⟩,hs.mask⟩,hs.carry⟩,hs.cin⟩
  have hf := triangularSquareClear_frame L.low L.a L.pad L.mask L.carry L.cin
    hn hd hp hm hk s m (by simpa [hs.low] using hs.a) hs.pad hs.mask hs.carry hs.cin
  exact ⟨hr.1,KaratsubaValues.update_a L h _ _ _ _ _ _ _ _ _ _ hs hr.2.1.1.1.1.2 hf⟩

theorem karatsuba_squareHigh_spec (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi av _dv cv zv sv : Nat) :
    Triple (KaratsubaValues L lo hi av 0 cv zv sv) L.squareHigh
      (KaratsubaValues L lo hi av (hi^2) cv zv sv) := by
  have hn : (L.cin::L.high++L.d++L.pad++L.mask++L.carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have hh := List.nodup_iff_count.mp h.nodup w
    simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at hh ⊢; omega
  have hd : L.d.length=2*L.high.length := by simp [h.d_length,h.high_length]
  have hp : L.high.length-1≤L.pad.length := by simp [h.high_length,h.pad_length]
  have hm : 2*(L.high.length-1)≤L.mask.length := by simp [h.high_length,h.mask_length]
  have hk : 2*(L.high.length-1)-1≤L.carry.length := by simp [h.high_length,h.carry_length]
  intro s m hs
  have hr := triangularSquare_spec L.high L.d L.pad L.mask L.carry L.cin
    hn hd hp hm hk hi s m ⟨⟨⟨⟨⟨hs.high,hs.d⟩,hs.pad⟩,hs.mask⟩,hs.carry⟩,hs.cin⟩
  have hf := triangularSquare_frame L.high L.d L.pad L.mask L.carry L.cin
    hn hd hp hm hk s m hs.d hs.pad hs.mask hs.carry hs.cin
  exact ⟨hr.1,KaratsubaValues.update_d L h _ _ _ _ _ _ _ _ _ _ hs hr.2.1.1.1.1.2 hf⟩

theorem karatsuba_clearHigh_spec (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi av _dv cv zv sv : Nat) :
    Triple (KaratsubaValues L lo hi av (hi^2) cv zv sv) L.clearHigh
      (KaratsubaValues L lo hi av 0 cv zv sv) := by
  have hn : (L.cin::L.high++L.d++L.pad++L.mask++L.carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have hh := List.nodup_iff_count.mp h.nodup w
    simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at hh ⊢; omega
  have hd : L.d.length=2*L.high.length := by simp [h.d_length,h.high_length]
  have hp : L.high.length-1≤L.pad.length := by simp [h.high_length,h.pad_length]
  have hm : 2*(L.high.length-1)≤L.mask.length := by simp [h.high_length,h.mask_length]
  have hk : 2*(L.high.length-1)-1≤L.carry.length := by simp [h.high_length,h.carry_length]
  intro s m hs
  have hr := triangularSquareClear_spec L.high L.d L.pad L.mask L.carry L.cin
    hn hd hp hm hk hi s m ⟨⟨⟨⟨⟨hs.high,hs.d⟩,hs.pad⟩,hs.mask⟩,hs.carry⟩,hs.cin⟩
  have hf := triangularSquareClear_frame L.high L.d L.pad L.mask L.carry L.cin
    hn hd hp hm hk s m (by simpa [hs.high] using hs.d) hs.pad hs.mask hs.carry hs.cin
  exact ⟨hr.1,KaratsubaValues.update_d L h _ _ _ _ _ _ _ _ _ _ hs hr.2.1.1.1.1.2 hf⟩

theorem karatsuba_squareSum_spec (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi av dv _cv zv sv : Nat) :
    Triple (KaratsubaValues L lo hi av dv 0 zv sv) L.squareSum
      (KaratsubaValues L lo hi av dv (sv^2) zv sv) := by
  have hn : (L.cin::L.sum++L.c++L.pad++L.mask++L.carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have hh := List.nodup_iff_count.mp h.nodup w
    simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at hh ⊢; omega
  have hd : L.c.length=2*L.sum.length := by simp [h.c_length,h.sum_length]
  have hp : L.sum.length-1≤L.pad.length := by simp [h.sum_length,h.pad_length]
  have hm : 2*(L.sum.length-1)≤L.mask.length := by simp [h.sum_length,h.mask_length]
  have hk : 2*(L.sum.length-1)-1≤L.carry.length := by simp [h.sum_length,h.carry_length]
  intro s m hs
  have hr := triangularSquare_spec L.sum L.c L.pad L.mask L.carry L.cin
    hn hd hp hm hk sv s m ⟨⟨⟨⟨⟨hs.sum,hs.c⟩,hs.pad⟩,hs.mask⟩,hs.carry⟩,hs.cin⟩
  have hf := triangularSquare_frame L.sum L.c L.pad L.mask L.carry L.cin
    hn hd hp hm hk s m hs.c hs.pad hs.mask hs.carry hs.cin
  exact ⟨hr.1,KaratsubaValues.update_c L h _ _ _ _ _ _ _ _ _ _ hs hr.2.1.1.1.1.2 hf⟩

theorem karatsuba_clearSquareSum_spec (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi av dv _cv zv sv : Nat) :
    Triple (KaratsubaValues L lo hi av dv (sv^2) zv sv) L.clearSquareSum
      (KaratsubaValues L lo hi av dv 0 zv sv) := by
  have hn : (L.cin::L.sum++L.c++L.pad++L.mask++L.carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have hh := List.nodup_iff_count.mp h.nodup w
    simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at hh ⊢; omega
  have hd : L.c.length=2*L.sum.length := by simp [h.c_length,h.sum_length]
  have hp : L.sum.length-1≤L.pad.length := by simp [h.sum_length,h.pad_length]
  have hm : 2*(L.sum.length-1)≤L.mask.length := by simp [h.sum_length,h.mask_length]
  have hk : 2*(L.sum.length-1)-1≤L.carry.length := by simp [h.sum_length,h.carry_length]
  intro s m hs
  have hr := triangularSquareClear_spec L.sum L.c L.pad L.mask L.carry L.cin
    hn hd hp hm hk sv s m ⟨⟨⟨⟨⟨hs.sum,hs.c⟩,hs.pad⟩,hs.mask⟩,hs.carry⟩,hs.cin⟩
  have hf := triangularSquareClear_frame L.sum L.c L.pad L.mask L.carry L.cin
    hn hd hp hm hk s m (by simpa [hs.sum] using hs.c) hs.pad hs.mask hs.carry hs.cin
  exact ⟨hr.1,KaratsubaValues.update_c L h _ _ _ _ _ _ _ _ _ _ hs hr.2.1.1.1.1.2 hf⟩

theorem karatsuba_prepareSum_spec (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi av dv cv zv : Nat) :
    Triple (KaratsubaValues L lo hi av dv cv zv 0) L.prepareSum
      (KaratsubaValues L lo hi av dv cv zv (lo+hi)) := by
  intro s m hs
  have hr := (karatsuba_sum_correct L h s.basis hs.pad hs.carry hs.cin).1 s m
    ⟨by simpa [hs.low,hs.high] using hs.sum,fun _ _ => rfl⟩
  have hv : regValue L.sum (run L.prepareSum m s).basis=(lo+hi) := by
    simpa [hs.low,hs.high] using hr.2.1
  exact ⟨hr.1,KaratsubaValues.update_sum L h _ _ _ _ _ _ _ _ _ _ hs hv hr.2.2⟩

theorem karatsuba_clearSum_spec (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi av dv cv zv : Nat) :
    Triple (KaratsubaValues L lo hi av dv cv zv (lo+hi)) L.clearSum
      (KaratsubaValues L lo hi av dv cv zv 0) := by
  intro s m hs
  have hr := (karatsuba_sum_correct L h s.basis hs.pad hs.carry hs.cin).2 s m
    ⟨by simpa [hs.low,hs.high] using hs.sum,fun _ _ => rfl⟩
  have hv : regValue L.sum (run L.clearSum m s).basis=0 := by
    simpa [hs.low,hs.high] using hr.2.1
  exact ⟨hr.1,KaratsubaValues.update_sum L h _ _ _ _ _ _ _ _ _ _ hs hv hr.2.2⟩


theorem karatsuba_copySquares_spec (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi av dv cv sv : Nat) :
    Triple (KaratsubaValues L lo hi av dv cv 0 sv) L.copySquares
      (KaratsubaValues L lo hi av dv cv (av+2^256*dv) sv) ∧
    Triple (KaratsubaValues L lo hi av dv cv (av+2^256*dv) sv) L.copySquares
      (KaratsubaValues L lo hi av dv cv 0 sv) := by
  constructor
  · intro s m hs
    have hr := (karatsuba_copySquares_frame L h s.basis).1 s m ⟨hs.z,fun _ _=>rfl⟩
    exact ⟨hr.1,KaratsubaValues.update_z L h _ _ _ _ _ _ _ _ _ _ hs
      (by simpa [hs.a,hs.d] using hr.2.1) hr.2.2⟩
  · intro s m hs
    have hr := (karatsuba_copySquares_frame L h s.basis).2 s m
      ⟨by simpa [hs.a,hs.d] using hs.z,fun _ _=>rfl⟩
    exact ⟨hr.1,KaratsubaValues.update_z L h _ _ _ _ _ _ _ _ _ _ hs hr.2.1 hr.2.2⟩

/-- Full-word value after a modular operation in its high 384-bit slice. -/
def karatsubaHighValue (sub : Bool) (v a : Nat) : Nat :=
  v%2^128+2^128*(if sub then (v/2^128+2^384-a)%2^384 else (v/2^128+a)%2^384)

theorem karatsuba_high_a_spec (sub : Bool) (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi av dv cv zv sv : Nat) :
    Triple (KaratsubaValues L lo hi av dv cv zv sv)
      (if sub then subInPlace (L.a++L.pad) (L.z.drop 128) L.carry L.cin
       else addInPlace (L.a++L.pad) (L.z.drop 128) L.carry L.cin)
      (KaratsubaValues L lo hi av dv cv (karatsubaHighValue sub zv av) sv) := by
  have hn : (L.cin::(L.a++L.pad)++L.z++L.carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have hh := List.nodup_iff_count.mp h.nodup w
    simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at hh ⊢; omega
  intro s m hs
  have pv : regValue (L.pad) s.basis=0 := by
    exact hs.pad
  have hr := karatsuba_high_correct sub (L.a++L.pad) L.z L.carry L.cin hn h.z_length
    (by simp [h.a_length,h.pad_length]) h.carry_length s m hs.carry hs.cin
  refine ⟨hr.1,KaratsubaValues.update_z L h _ _ _ _ _ _ _ _ _ _ hs ?_ hr.2.2⟩
  simpa only [karatsubaHighValue,regValue_append,pv,Nat.mul_zero,Nat.add_zero,hs.z,hs.a] using hr.2.1

theorem karatsuba_high_d_spec (sub : Bool) (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi av dv cv zv sv : Nat) :
    Triple (KaratsubaValues L lo hi av dv cv zv sv)
      (if sub then subInPlace (L.d++L.pad) (L.z.drop 128) L.carry L.cin
       else addInPlace (L.d++L.pad) (L.z.drop 128) L.carry L.cin)
      (KaratsubaValues L lo hi av dv cv (karatsubaHighValue sub zv dv) sv) := by
  have hn : (L.cin::(L.d++L.pad)++L.z++L.carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have hh := List.nodup_iff_count.mp h.nodup w
    simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at hh ⊢; omega
  intro s m hs
  have pv : regValue (L.pad) s.basis=0 := by
    exact hs.pad
  have hr := karatsuba_high_correct sub (L.d++L.pad) L.z L.carry L.cin hn h.z_length
    (by simp [h.d_length,h.pad_length]) h.carry_length s m hs.carry hs.cin
  refine ⟨hr.1,KaratsubaValues.update_z L h _ _ _ _ _ _ _ _ _ _ hs ?_ hr.2.2⟩
  simpa only [karatsubaHighValue,regValue_append,pv,Nat.mul_zero,Nat.add_zero,hs.z,hs.d] using hr.2.1

theorem karatsuba_high_c_spec (sub : Bool) (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi av dv cv zv sv : Nat) :
    Triple (KaratsubaValues L lo hi av dv cv zv sv)
      (if sub then subInPlace (L.c++L.pad.take 126) (L.z.drop 128) L.carry L.cin
       else addInPlace (L.c++L.pad.take 126) (L.z.drop 128) L.carry L.cin)
      (KaratsubaValues L lo hi av dv cv (karatsubaHighValue sub zv cv) sv) := by
  have hn : (L.cin::(L.c++L.pad.take 126)++L.z++L.carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have hh := List.nodup_iff_count.mp h.nodup w
    have hp := (List.take_sublist 126 L.pad).count_le w
    simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at hh ⊢; omega
  intro s m hs
  have pv : regValue (L.pad.take 126) s.basis=0 := by
    exact (regValue_zero _ _).mpr (fun w hw=>(regValue_zero _ _).mp hs.pad w (List.mem_of_mem_take hw))
  have hr := karatsuba_high_correct sub (L.c++L.pad.take 126) L.z L.carry L.cin hn h.z_length
    (by simp [h.c_length,h.pad_length]) h.carry_length s m hs.carry hs.cin
  refine ⟨hr.1,KaratsubaValues.update_z L h _ _ _ _ _ _ _ _ _ _ hs ?_ hr.2.2⟩
  simpa only [karatsubaHighValue,regValue_append,pv,Nat.mul_zero,Nat.add_zero,hs.z,hs.c] using hr.2.1


private theorem high_add (v a : Nat) :
    karatsubaHighValue false v a=(v+2^128*a)%2^512 := by
  unfold karatsubaHighValue
  norm_num only [Bool.false_eq_true,if_false]
  omega

private theorem high_sub (v a : Nat) (hv : v<2^512) (ha : a<2^384) :
    karatsubaHighValue true v a=(v+2^512-2^128*a)%2^512 := by
  unfold karatsubaHighValue
  norm_num only [if_true]
  omega

private theorem high_bound (sub : Bool) (v a : Nat) :
    karatsubaHighValue sub v a<2^512 := by
  unfold karatsubaHighValue
  split <;> omega

private theorem combine_value (av dv cv initial result : Nat)
    (ha : av<2^384) (hd : dv<2^384)
    (_hi : initial<2^512) (hr : result<2^512)
    (he : initial+2^128*cv=result+2^128*av+2^128*dv) :
    karatsubaHighValue true (karatsubaHighValue true
      (karatsubaHighValue false initial cv) av) dv=result := by
  rw [high_sub _ _ (high_bound _ _ _) hd,high_sub _ _ (high_bound _ _ _) ha,high_add]
  omega

private theorem uncombine_value (av dv cv initial result : Nat)
    (hc : cv<2^384) (hi : initial<2^512) (_hr : result<2^512)
    (he : initial+2^128*cv=result+2^128*av+2^128*dv) :
    karatsubaHighValue true (karatsubaHighValue false
      (karatsubaHighValue false result dv) av) cv=initial := by
  rw [high_sub _ _ (high_bound _ _ _) hc,high_add,high_add]
  omega


/-- Recombination is modulo the full result width, including intermediate wraps. -/
theorem karatsuba_combine_spec (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi av dv cv sv initial result : Nat)
    (ha : av<2^384) (hd : dv<2^384) (hi' : initial<2^512) (hr : result<2^512)
    (he : initial+2^128*cv=result+2^128*av+2^128*dv) :
    Triple (KaratsubaValues L lo hi av dv cv initial sv) L.combine
      (KaratsubaValues L lo hi av dv cv result sv) := by
  have c := karatsuba_high_c_spec false L h lo hi av dv cv initial sv
  have a := karatsuba_high_a_spec true L h lo hi av dv cv
    (karatsubaHighValue false initial cv) sv
  have d := karatsuba_high_d_spec true L h lo hi av dv cv
    (karatsubaHighValue true (karatsubaHighValue false initial cv) av) sv
  have hh := (c.seq a).seq d
  rw [combine_value av dv cv initial result ha hd hi' hr he] at hh
  exact hh

theorem karatsuba_uncombine_spec (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi av dv cv sv initial result : Nat)
    (hc : cv<2^384) (hi' : initial<2^512) (hr : result<2^512)
    (he : initial+2^128*cv=result+2^128*av+2^128*dv) :
    Triple (KaratsubaValues L lo hi av dv cv result sv) L.uncombine
      (KaratsubaValues L lo hi av dv cv initial sv) := by
  have d := karatsuba_high_d_spec false L h lo hi av dv cv result sv
  have a := karatsuba_high_a_spec false L h lo hi av dv cv
    (karatsubaHighValue false result dv) sv
  have c := karatsuba_high_c_spec true L h lo hi av dv cv
    (karatsubaHighValue false (karatsubaHighValue false result dv) av) sv
  have hh := (d.seq a).seq c
  rw [uncombine_value av dv cv initial result hc hi' hr he] at hh
  exact hh

private theorem recombination_bounds (lo hi : Nat) (hl : lo<2^128) (hh : hi<2^128) :
    lo^2<2^384 ∧ hi^2<2^384 ∧ (lo+hi)^2<2^384 ∧
    lo^2+2^256*hi^2<2^512 ∧ (lo+2^128*hi)^2<2^512 ∧
    lo^2+2^256*hi^2+2^128*(lo+hi)^2=
      (lo+2^128*hi)^2+2^128*lo^2+2^128*hi^2 := by
  have al := square_bound lo 128 hl
  have ah := square_bound hi 128 hh
  have ac := square_sum128_square_bound lo hi hl hh
  have xb : lo+2^128*hi<2^256 := by omega
  have ax := square_bound _ 256 xb
  refine ⟨by omega,by omega,by omega,by omega,by simpa only [Nat.reduceMul] using ax,?_⟩
  ring

/-- The full compute preserves its input, retains A and D, and clears every temporary. -/
theorem karatsubaSquare_spec (L : KaratsubaSquareLayout) (h : L.Valid) (lo hi : Nat) :
    Triple (KaratsubaValues L lo hi 0 0 0 0 0) (karatsubaSquare L)
      (KaratsubaValues L lo hi (lo^2) (hi^2) 0 ((lo+2^128*hi)^2) 0) := by
  intro s m hs
  have hl : lo<2^128 := by simpa [h.low_length,hs.low] using regValue_lt L.low s.basis
  have hh : hi<2^128 := by simpa [h.high_length,hs.high] using regValue_lt L.high s.basis
  obtain ⟨ba,bd,bc,bi,br,be⟩ := recombination_bounds lo hi hl hh
  have a := karatsuba_squareLow_spec L h lo hi 0 0 0 0 0
  have d := karatsuba_squareHigh_spec L h lo hi (lo^2) 0 0 0 0
  have s1 := karatsuba_prepareSum_spec L h lo hi (lo^2) (hi^2) 0 0
  have c1 := karatsuba_squareSum_spec L h lo hi (lo^2) (hi^2) 0 0 (lo+hi)
  have s2 := karatsuba_clearSum_spec L h lo hi (lo^2) (hi^2) ((lo+hi)^2) 0
  have cp := (karatsuba_copySquares_spec L h lo hi (lo^2) (hi^2) ((lo+hi)^2) 0).1
  have comb := karatsuba_combine_spec L h lo hi (lo^2) (hi^2) ((lo+hi)^2) 0
    (lo^2+2^256*hi^2) ((lo+2^128*hi)^2) ba bd bi br be
  have s3 := karatsuba_prepareSum_spec L h lo hi (lo^2) (hi^2) ((lo+hi)^2) ((lo+2^128*hi)^2)
  have c2 := karatsuba_clearSquareSum_spec L h lo hi (lo^2) (hi^2) 0 ((lo+2^128*hi)^2) (lo+hi)
  have s4 := karatsuba_clearSum_spec L h lo hi (lo^2) (hi^2) 0 ((lo+2^128*hi)^2)
  exact ((((((((a.seq d).seq s1).seq c1).seq s2).seq cp).seq comb).seq s3).seq c2).seq s4 s m hs

/-- Cleanup uses forward programs and restores all retained square words. -/
theorem karatsubaSquareClear_spec (L : KaratsubaSquareLayout) (h : L.Valid) (lo hi : Nat) :
    Triple (KaratsubaValues L lo hi (lo^2) (hi^2) 0 ((lo+2^128*hi)^2) 0)
      (karatsubaSquareClear L) (KaratsubaValues L lo hi 0 0 0 0 0) := by
  intro s m hs
  have hl : lo<2^128 := by simpa [h.low_length,hs.low] using regValue_lt L.low s.basis
  have hh : hi<2^128 := by simpa [h.high_length,hs.high] using regValue_lt L.high s.basis
  obtain ⟨ba,bd,bc,bi,br,be⟩ := recombination_bounds lo hi hl hh
  have s1 := karatsuba_prepareSum_spec L h lo hi (lo^2) (hi^2) 0 ((lo+2^128*hi)^2)
  have c1 := karatsuba_squareSum_spec L h lo hi (lo^2) (hi^2) 0 ((lo+2^128*hi)^2) (lo+hi)
  have s2 := karatsuba_clearSum_spec L h lo hi (lo^2) (hi^2) ((lo+hi)^2) ((lo+2^128*hi)^2)
  have comb := karatsuba_uncombine_spec L h lo hi (lo^2) (hi^2) ((lo+hi)^2) 0
    (lo^2+2^256*hi^2) ((lo+2^128*hi)^2) bc bi br be
  have cp := (karatsuba_copySquares_spec L h lo hi (lo^2) (hi^2) ((lo+hi)^2) 0).2
  have s3 := karatsuba_prepareSum_spec L h lo hi (lo^2) (hi^2) ((lo+hi)^2) 0
  have c2 := karatsuba_clearSquareSum_spec L h lo hi (lo^2) (hi^2) 0 0 (lo+hi)
  have s4 := karatsuba_clearSum_spec L h lo hi (lo^2) (hi^2) 0 0
  have d := karatsuba_clearHigh_spec L h lo hi (lo^2) 0 0 0 0
  have a := karatsuba_clearLow_spec L h lo hi 0 0 0 0 0
  exact ((((((((s1.seq c1).seq s2).seq comb).seq cp).seq s3).seq c2).seq s4).seq d).seq a s m hs


private theorem values_frame (L : KaratsubaSquareLayout)
    (lo hi av dv zv av' dv' zv' : Nat) (s u : BasisState)
    (hs : KaratsubaValues L lo hi av dv 0 zv 0 s)
    (hu : KaratsubaValues L lo hi av' dv' 0 zv' 0 u)
    (ho : ∀ w,w∉L.wires→u w=s w) :
    ∀ w,w∉L.a++L.d++L.z→u w=s w := by
  intro w hw
  have eqv (r : List Wire) (he : regValue r u=regValue r s) (hm : w∈r) : u w=s w :=
    (regValue_eq_iff r u s).mp he w hm
  by_cases hl : w∈L.low
  · exact eqv L.low (hu.low.trans hs.low.symm) hl
  by_cases hh : w∈L.high
  · exact eqv L.high (hu.high.trans hs.high.symm) hh
  by_cases hc : w∈L.c
  · exact eqv L.c (hu.c.trans hs.c.symm) hc
  by_cases hz : w∈L.sum
  · exact eqv L.sum (hu.sum.trans hs.sum.symm) hz
  by_cases hp : w∈L.pad
  · exact eqv L.pad (hu.pad.trans hs.pad.symm) hp
  by_cases hm : w∈L.mask
  · exact eqv L.mask (hu.mask.trans hs.mask.symm) hm
  by_cases hk : w∈L.carry
  · exact eqv L.carry (hu.carry.trans hs.carry.symm) hk
  by_cases hi : w=L.cin
  · subst w; exact hu.cin.trans hs.cin.symm
  apply ho
  simpa only [KaratsubaSquareLayout.wires,List.mem_cons,List.mem_append,hl,hh,hc,hz,hp,hm,hk,hi,
    false_or,or_false] using hw

/-- Every wire outside the three retained output words is exactly preserved. -/
theorem karatsubaSquare_frame (L : KaratsubaSquareLayout) (h : L.Valid) (lo hi : Nat)
    (s : State) (m : List Bool) (hs : KaratsubaValues L lo hi 0 0 0 0 0 s.basis) :
    ∀ w,w∉L.a++L.d++L.z→(run (karatsubaSquare L) m s).basis w=s.basis w := by
  have hr := karatsubaSquare_spec L h lo hi s m hs
  apply values_frame L lo hi 0 0 0 (lo^2) (hi^2) ((lo+2^128*hi)^2) _ _ hs hr.2
  intro w hw
  apply run_preserves_outside
  intro hm
  exact hw (List.mem_toFinset.mp ((karatsubaSquare_wires_subset L h).1 hm))

theorem karatsubaSquareClear_frame (L : KaratsubaSquareLayout) (h : L.Valid) (lo hi : Nat)
    (s : State) (m : List Bool)
    (hs : KaratsubaValues L lo hi (lo^2) (hi^2) 0 ((lo+2^128*hi)^2) 0 s.basis) :
    ∀ w,w∉L.a++L.d++L.z→(run (karatsubaSquareClear L) m s).basis w=s.basis w := by
  have hr := karatsubaSquareClear_spec L h lo hi s m hs
  apply values_frame L lo hi (lo^2) (hi^2) ((lo+2^128*hi)^2) 0 0 0 _ _ hs hr.2
  intro w hw
  apply run_preserves_outside
  intro hm
  exact hw (List.mem_toFinset.mp ((karatsubaSquare_wires_subset L h).2 hm))

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/SignedSquareCandidate.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

namespace KaratsubaSquareLayout

def signedSquareLow (L : KaratsubaSquareLayout) : Program :=
  signedTriangularSquare L.low L.a L.pad L.mask L.carry L.cin
def signedClearLow (L : KaratsubaSquareLayout) : Program :=
  signedTriangularSquareClear L.low L.a L.pad L.mask L.carry L.cin
def signedSquareHigh (L : KaratsubaSquareLayout) : Program :=
  signedTriangularSquare L.high L.d L.pad L.mask L.carry L.cin
def signedClearHigh (L : KaratsubaSquareLayout) : Program :=
  signedTriangularSquareClear L.high L.d L.pad L.mask L.carry L.cin
def signedSquareSum (L : KaratsubaSquareLayout) : Program :=
  signedTriangularSquare L.sum L.c L.pad L.mask L.carry L.cin
def signedClearSquareSum (L : KaratsubaSquareLayout) : Program :=
  signedTriangularSquareClear L.sum L.c L.pad L.mask L.carry L.cin

end KaratsubaSquareLayout

/-- Drop-in gate-stream candidate: same Karatsuba schedule and exact reduction,
with every triangular leaf replaced by the exact signed-row producer. -/
def signedKaratsubaSquare (L : KaratsubaSquareLayout) : Program :=
  L.signedSquareLow ++ L.signedSquareHigh ++ L.prepareSum ++ L.signedSquareSum ++ L.clearSum ++
  L.copySquares ++ L.combine ++ L.prepareSum ++ L.signedClearSquareSum ++ L.clearSum

def signedKaratsubaSquareClear (L : KaratsubaSquareLayout) : Program :=
  L.prepareSum ++ L.signedSquareSum ++ L.clearSum ++ L.uncombine ++ L.copySquares ++
  L.prepareSum ++ L.signedClearSquareSum ++ L.clearSum ++ L.signedClearHigh ++ L.signedClearLow

theorem signedKaratsubaSquare_counts (L : KaratsubaSquareLayout) (h : L.Valid) :
    (toffoliCount (signedKaratsubaSquare L)=35453 ∧
      measurementCount (signedKaratsubaSquare L)=35453) ∧
    (toffoliCount (signedKaratsubaSquareClear L)=35453 ∧
      measurementCount (signedKaratsubaSquareClear L)=35453) := by
  have lo := signedTriangularSquare_counts_128 L.low L.a L.pad L.mask L.carry L.cin
    h.low_length h.a_length (by simp [h.pad_length]) (by simp [h.mask_length])
    (by simp [h.carry_length])
  have hi := signedTriangularSquare_counts_128 L.high L.d L.pad L.mask L.carry L.cin
    h.high_length h.d_length (by simp [h.pad_length]) (by simp [h.mask_length])
    (by simp [h.carry_length])
  have su := signedTriangularSquare_counts_129 L.sum L.c L.pad L.mask L.carry L.cin
    h.sum_length h.c_length (by simp [h.pad_length]) (by simp [h.mask_length])
    (by simp [h.carry_length])
  obtain ⟨sp,sc⟩ := L.sum_counts h
  obtain ⟨comb,uncomb⟩ := L.combine_counts h
  have cp := L.copySquares_counts h
  simp [signedKaratsubaSquare,signedKaratsubaSquareClear,
    KaratsubaSquareLayout.signedSquareLow,KaratsubaSquareLayout.signedClearLow,
    KaratsubaSquareLayout.signedSquareHigh,KaratsubaSquareLayout.signedClearHigh,
    KaratsubaSquareLayout.signedSquareSum,KaratsubaSquareLayout.signedClearSquareSum,
    toffoliCount_append,measurementCount_append,lo.1.1,lo.1.2,lo.2.1,lo.2.2,
    hi.1.1,hi.1.2,hi.2.1,hi.2.2,su.1.1,su.1.2,su.2.1,su.2.2,
    sp.1,sp.2,sc.1,sc.2,comb.1,comb.2,uncomb.1,uncomb.2,cp.1,cp.2]

/-- Complete exact-arithmetic square-subtract candidate.  Functional promotion
waits for the signed-leaf correctness theorem and the full point proof. -/
def signedSquareSub (L : SquareSubLayout) : Program :=
  signedKaratsubaSquare L.integer ++ squareReduce L.reduction ++
  modSubInPlace L.output SquareReduction.p ++ squareReduceClear L.reduction ++
  signedKaratsubaSquareClear L.integer

theorem signedSquareSub_counts (L : SquareSubLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    toffoliCount (signedSquareSub L)=81589 ∧
      measurementCount (signedSquareSub L)=81589 := by
  have hk := signedKaratsubaSquare_counts L.integer (L.integer_valid hw hn)
  have hr := squareReduce_counts L.reduction (L.reduction_widths hw)
  have ho := modSubInPlace_resources L.output 256 SquareReduction.p (L.output_widths hw)
    (L.output_nodup hn) (by omega)
  simp [signedSquareSub,toffoliCount_append,measurementCount_append,
    hk.1.1,hk.1.2,hk.2.1,hk.2.2,hr.1.1,hr.1.2,hr.2.1,hr.2.2,ho.1,ho.2.1]

/-- With the existing 256-bit controlled source load/unload around the square,
the complete stage prices at 82,101 Toffolis. -/
theorem signedPointSquare_projected_count : 512+81589=82101 := by norm_num

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/SignedKaratsubaSquareState.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

theorem signedKaratsuba_squareLow_spec (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi _av dv cv zv sv : Nat) :
    Triple (KaratsubaValues L lo hi 0 dv cv zv sv) L.signedSquareLow
      (KaratsubaValues L lo hi (lo^2) dv cv zv sv) := by
  have hn : (L.cin::L.low++L.a++L.pad++L.mask++L.carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have hh := List.nodup_iff_count.mp h.nodup w
    simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at hh ⊢
    omega
  have hd : L.a.length=2*L.low.length := by simp [h.a_length,h.low_length]
  intro s m hs
  have hr := signedTriangularSquare_spec L.cin L.low L.a L.pad L.mask L.carry
    hn (by simp [h.low_length]) hd (by simp [h.pad_length])
    (by simp [h.low_length,h.mask_length]) (by simp [h.a_length,h.carry_length]) lo
    s m ⟨⟨⟨⟨⟨hs.low,hs.a⟩,hs.pad⟩,hs.mask⟩,hs.carry⟩,hs.cin⟩
  have hf := signedTriangularSquare_frame L.cin L.low L.a L.pad L.mask L.carry
    hn (by simp [h.low_length]) hd (by simp [h.pad_length])
    (by simp [h.low_length,h.mask_length]) (by simp [h.a_length,h.carry_length])
    s m hs.a hs.pad hs.mask hs.carry hs.cin
  exact ⟨hr.1,KaratsubaValues.update_a L h _ _ _ _ _ _ _ _ _ _ hs
    hr.2.1.1.1.1.2 hf⟩

theorem signedKaratsuba_clearLow_spec (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi _av dv cv zv sv : Nat) :
    Triple (KaratsubaValues L lo hi (lo^2) dv cv zv sv) L.signedClearLow
      (KaratsubaValues L lo hi 0 dv cv zv sv) := by
  have hn : (L.cin::L.low++L.a++L.pad++L.mask++L.carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have hh := List.nodup_iff_count.mp h.nodup w
    simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at hh ⊢
    omega
  have hd : L.a.length=2*L.low.length := by simp [h.a_length,h.low_length]
  intro s m hs
  have hr := signedTriangularSquareClear_spec L.cin L.low L.a L.pad L.mask L.carry
    hn (by simp [h.low_length]) hd (by simp [h.pad_length])
    (by simp [h.low_length,h.mask_length]) (by simp [h.a_length,h.carry_length]) lo
    s m ⟨⟨⟨⟨⟨hs.low,hs.a⟩,hs.pad⟩,hs.mask⟩,hs.carry⟩,hs.cin⟩
  have hf := signedTriangularSquareClear_frame L.cin L.low L.a L.pad L.mask L.carry
    hn (by simp [h.low_length]) hd (by simp [h.pad_length])
    (by simp [h.low_length,h.mask_length]) (by simp [h.a_length,h.carry_length])
    s m (by simpa [hs.low] using hs.a) hs.pad hs.mask hs.carry hs.cin
  exact ⟨hr.1,KaratsubaValues.update_a L h _ _ _ _ _ _ _ _ _ _ hs
    hr.2.1.1.1.1.2 hf⟩

theorem signedKaratsuba_squareHigh_spec (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi av _dv cv zv sv : Nat) :
    Triple (KaratsubaValues L lo hi av 0 cv zv sv) L.signedSquareHigh
      (KaratsubaValues L lo hi av (hi^2) cv zv sv) := by
  have hn : (L.cin::L.high++L.d++L.pad++L.mask++L.carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have hh := List.nodup_iff_count.mp h.nodup w
    simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at hh ⊢
    omega
  have hd : L.d.length=2*L.high.length := by simp [h.d_length,h.high_length]
  intro s m hs
  have hr := signedTriangularSquare_spec L.cin L.high L.d L.pad L.mask L.carry
    hn (by simp [h.high_length]) hd (by simp [h.pad_length])
    (by simp [h.high_length,h.mask_length]) (by simp [h.d_length,h.carry_length]) hi
    s m ⟨⟨⟨⟨⟨hs.high,hs.d⟩,hs.pad⟩,hs.mask⟩,hs.carry⟩,hs.cin⟩
  have hf := signedTriangularSquare_frame L.cin L.high L.d L.pad L.mask L.carry
    hn (by simp [h.high_length]) hd (by simp [h.pad_length])
    (by simp [h.high_length,h.mask_length]) (by simp [h.d_length,h.carry_length])
    s m hs.d hs.pad hs.mask hs.carry hs.cin
  exact ⟨hr.1,KaratsubaValues.update_d L h _ _ _ _ _ _ _ _ _ _ hs
    hr.2.1.1.1.1.2 hf⟩

theorem signedKaratsuba_clearHigh_spec (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi av _dv cv zv sv : Nat) :
    Triple (KaratsubaValues L lo hi av (hi^2) cv zv sv) L.signedClearHigh
      (KaratsubaValues L lo hi av 0 cv zv sv) := by
  have hn : (L.cin::L.high++L.d++L.pad++L.mask++L.carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have hh := List.nodup_iff_count.mp h.nodup w
    simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at hh ⊢
    omega
  have hd : L.d.length=2*L.high.length := by simp [h.d_length,h.high_length]
  intro s m hs
  have hr := signedTriangularSquareClear_spec L.cin L.high L.d L.pad L.mask L.carry
    hn (by simp [h.high_length]) hd (by simp [h.pad_length])
    (by simp [h.high_length,h.mask_length]) (by simp [h.d_length,h.carry_length]) hi
    s m ⟨⟨⟨⟨⟨hs.high,hs.d⟩,hs.pad⟩,hs.mask⟩,hs.carry⟩,hs.cin⟩
  have hf := signedTriangularSquareClear_frame L.cin L.high L.d L.pad L.mask L.carry
    hn (by simp [h.high_length]) hd (by simp [h.pad_length])
    (by simp [h.high_length,h.mask_length]) (by simp [h.d_length,h.carry_length])
    s m (by simpa [hs.high] using hs.d) hs.pad hs.mask hs.carry hs.cin
  exact ⟨hr.1,KaratsubaValues.update_d L h _ _ _ _ _ _ _ _ _ _ hs
    hr.2.1.1.1.1.2 hf⟩

theorem signedKaratsuba_squareSum_spec (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi av dv _cv zv sv : Nat) :
    Triple (KaratsubaValues L lo hi av dv 0 zv sv) L.signedSquareSum
      (KaratsubaValues L lo hi av dv (sv^2) zv sv) := by
  have hn : (L.cin::L.sum++L.c++L.pad++L.mask++L.carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have hh := List.nodup_iff_count.mp h.nodup w
    simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at hh ⊢
    omega
  have hd : L.c.length=2*L.sum.length := by simp [h.c_length,h.sum_length]
  intro s m hs
  have hr := signedTriangularSquare_spec L.cin L.sum L.c L.pad L.mask L.carry
    hn (by simp [h.sum_length]) hd (by simp [h.pad_length])
    (by simp [h.sum_length,h.mask_length]) (by simp [h.c_length,h.carry_length]) sv
    s m ⟨⟨⟨⟨⟨hs.sum,hs.c⟩,hs.pad⟩,hs.mask⟩,hs.carry⟩,hs.cin⟩
  have hf := signedTriangularSquare_frame L.cin L.sum L.c L.pad L.mask L.carry
    hn (by simp [h.sum_length]) hd (by simp [h.pad_length])
    (by simp [h.sum_length,h.mask_length]) (by simp [h.c_length,h.carry_length])
    s m hs.c hs.pad hs.mask hs.carry hs.cin
  exact ⟨hr.1,KaratsubaValues.update_c L h _ _ _ _ _ _ _ _ _ _ hs
    hr.2.1.1.1.1.2 hf⟩

theorem signedKaratsuba_clearSquareSum_spec (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi av dv _cv zv sv : Nat) :
    Triple (KaratsubaValues L lo hi av dv (sv^2) zv sv) L.signedClearSquareSum
      (KaratsubaValues L lo hi av dv 0 zv sv) := by
  have hn : (L.cin::L.sum++L.c++L.pad++L.mask++L.carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have hh := List.nodup_iff_count.mp h.nodup w
    simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at hh ⊢
    omega
  have hd : L.c.length=2*L.sum.length := by simp [h.c_length,h.sum_length]
  intro s m hs
  have hr := signedTriangularSquareClear_spec L.cin L.sum L.c L.pad L.mask L.carry
    hn (by simp [h.sum_length]) hd (by simp [h.pad_length])
    (by simp [h.sum_length,h.mask_length]) (by simp [h.c_length,h.carry_length]) sv
    s m ⟨⟨⟨⟨⟨hs.sum,hs.c⟩,hs.pad⟩,hs.mask⟩,hs.carry⟩,hs.cin⟩
  have hf := signedTriangularSquareClear_frame L.cin L.sum L.c L.pad L.mask L.carry
    hn (by simp [h.sum_length]) hd (by simp [h.pad_length])
    (by simp [h.sum_length,h.mask_length]) (by simp [h.c_length,h.carry_length])
    s m (by simpa [hs.sum] using hs.c) hs.pad hs.mask hs.carry hs.cin
  exact ⟨hr.1,KaratsubaValues.update_c L h _ _ _ _ _ _ _ _ _ _ hs
    hr.2.1.1.1.1.2 hf⟩

private theorem signed_recombination_bounds (lo hi : Nat)
    (hl : lo<2^128) (hh : hi<2^128) :
    lo^2<2^384 ∧ hi^2<2^384 ∧ (lo+hi)^2<2^384 ∧
    lo^2+2^256*hi^2<2^512 ∧ (lo+2^128*hi)^2<2^512 ∧
    lo^2+2^256*hi^2+2^128*(lo+hi)^2=
      (lo+2^128*hi)^2+2^128*lo^2+2^128*hi^2 := by
  have al := square_bound lo 128 hl
  have ah := square_bound hi 128 hh
  have ac := square_sum128_square_bound lo hi hl hh
  have xb : lo+2^128*hi<2^256 := by omega
  have ax := square_bound _ 256 xb
  refine ⟨by omega,by omega,by omega,by omega,by simpa only [Nat.reduceMul] using ax,?_⟩
  ring

theorem signedKaratsubaSquare_spec (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi : Nat) :
    Triple (KaratsubaValues L lo hi 0 0 0 0 0) (signedKaratsubaSquare L)
      (KaratsubaValues L lo hi (lo^2) (hi^2) 0 ((lo+2^128*hi)^2) 0) := by
  intro s m hs
  have hl : lo<2^128 := by simpa [h.low_length,hs.low] using regValue_lt L.low s.basis
  have hh : hi<2^128 := by simpa [h.high_length,hs.high] using regValue_lt L.high s.basis
  obtain ⟨ba,bd,bc,bi,br,be⟩ := signed_recombination_bounds lo hi hl hh
  have a := signedKaratsuba_squareLow_spec L h lo hi 0 0 0 0 0
  have d := signedKaratsuba_squareHigh_spec L h lo hi (lo^2) 0 0 0 0
  have s1 := karatsuba_prepareSum_spec L h lo hi (lo^2) (hi^2) 0 0
  have c1 := signedKaratsuba_squareSum_spec L h lo hi (lo^2) (hi^2) 0 0 (lo+hi)
  have s2 := karatsuba_clearSum_spec L h lo hi (lo^2) (hi^2) ((lo+hi)^2) 0
  have cp := (karatsuba_copySquares_spec L h lo hi (lo^2) (hi^2) ((lo+hi)^2) 0).1
  have comb := karatsuba_combine_spec L h lo hi (lo^2) (hi^2) ((lo+hi)^2) 0
    (lo^2+2^256*hi^2) ((lo+2^128*hi)^2) ba bd bi br be
  have s3 := karatsuba_prepareSum_spec L h lo hi (lo^2) (hi^2) ((lo+hi)^2)
    ((lo+2^128*hi)^2)
  have c2 := signedKaratsuba_clearSquareSum_spec L h lo hi (lo^2) (hi^2) 0
    ((lo+2^128*hi)^2) (lo+hi)
  have s4 := karatsuba_clearSum_spec L h lo hi (lo^2) (hi^2) 0 ((lo+2^128*hi)^2)
  have chain := ((((((((a.seq d).seq s1).seq c1).seq s2).seq cp).seq comb).seq s3).seq c2).seq s4
  simpa [signedKaratsubaSquare,KaratsubaSquareLayout.signedSquareLow,
    KaratsubaSquareLayout.signedSquareHigh,KaratsubaSquareLayout.signedSquareSum,
    KaratsubaSquareLayout.signedClearSquareSum] using chain s m hs

theorem signedKaratsubaSquareClear_spec (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi : Nat) :
    Triple (KaratsubaValues L lo hi (lo^2) (hi^2) 0 ((lo+2^128*hi)^2) 0)
      (signedKaratsubaSquareClear L) (KaratsubaValues L lo hi 0 0 0 0 0) := by
  intro s m hs
  have hl : lo<2^128 := by simpa [h.low_length,hs.low] using regValue_lt L.low s.basis
  have hh : hi<2^128 := by simpa [h.high_length,hs.high] using regValue_lt L.high s.basis
  obtain ⟨ba,bd,bc,bi,br,be⟩ := signed_recombination_bounds lo hi hl hh
  have s1 := karatsuba_prepareSum_spec L h lo hi (lo^2) (hi^2) 0 ((lo+2^128*hi)^2)
  have c1 := signedKaratsuba_squareSum_spec L h lo hi (lo^2) (hi^2) 0
    ((lo+2^128*hi)^2) (lo+hi)
  have s2 := karatsuba_clearSum_spec L h lo hi (lo^2) (hi^2) ((lo+hi)^2)
    ((lo+2^128*hi)^2)
  have comb := karatsuba_uncombine_spec L h lo hi (lo^2) (hi^2) ((lo+hi)^2) 0
    (lo^2+2^256*hi^2) ((lo+2^128*hi)^2) bc bi br be
  have cp := (karatsuba_copySquares_spec L h lo hi (lo^2) (hi^2) ((lo+hi)^2) 0).2
  have s3 := karatsuba_prepareSum_spec L h lo hi (lo^2) (hi^2) ((lo+hi)^2) 0
  have c2 := signedKaratsuba_clearSquareSum_spec L h lo hi (lo^2) (hi^2) 0 0 (lo+hi)
  have s4 := karatsuba_clearSum_spec L h lo hi (lo^2) (hi^2) 0 0
  have d := signedKaratsuba_clearHigh_spec L h lo hi (lo^2) 0 0 0 0
  have a := signedKaratsuba_clearLow_spec L h lo hi 0 0 0 0 0
  have chain := ((((((((s1.seq c1).seq s2).seq comb).seq cp).seq s3).seq c2).seq s4).seq d).seq a
  simpa [signedKaratsubaSquareClear,KaratsubaSquareLayout.signedSquareSum,
    KaratsubaSquareLayout.signedClearSquareSum,KaratsubaSquareLayout.signedClearHigh,
    KaratsubaSquareLayout.signedClearLow] using chain s m hs

theorem signedKaratsubaSquare_wires_subset (L : KaratsubaSquareLayout) (h : L.Valid) :
    wires (signedKaratsubaSquare L)⊆L.wires.toFinset ∧
      wires (signedKaratsubaSquareClear L)⊆L.wires.toFinset := by
  have own (r : List Wire) (hc : ∀w,r.count w≤L.wires.count w) :
      r.toFinset⊆L.wires.toFinset := by
    intro w hw
    apply List.mem_toFinset.mpr
    apply List.count_pos_iff.mp
    exact lt_of_lt_of_le (List.count_pos_iff.mpr (List.mem_toFinset.mp hw)) (hc w)
  have leaf (src dst : List Wire)
      (hsrc : src=L.low ∨ src=L.high ∨ src=L.sum)
      (hdst : dst=L.a ∨ dst=L.d ∨ dst=L.c)
      (hs : 2≤src.length) (hd : dst.length=2*src.length) :
      wires (signedTriangularSquare src dst L.pad L.mask L.carry L.cin)⊆L.wires.toFinset ∧
        wires (signedTriangularSquareClear src dst L.pad L.mask L.carry L.cin)⊆
          L.wires.toFinset := by
    have hw := signedTriangularSquare_wires_subset L.cin src dst L.pad L.mask L.carry
      hs hd (by simp [h.pad_length]) (by rcases hsrc with rfl|rfl|rfl <;>
        simp [h.low_length,h.high_length,h.sum_length,h.mask_length])
      (by rcases hdst with rfl|rfl|rfl <;>
        simp [h.a_length,h.d_length,h.c_length,h.carry_length])
    have ho : (L.cin::src++dst++L.pad++L.mask++L.carry).toFinset⊆L.wires.toFinset := by
      apply own
      intro w
      rcases hsrc with rfl|rfl|rfl <;> rcases hdst with rfl|rfl|rfl <;>
        simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] <;> omega
    exact ⟨hw.1.trans ho,hw.2.trans ho⟩
  have low := leaf L.low L.a (Or.inl rfl) (Or.inl rfl)
    (by simp [h.low_length]) (by simp [h.low_length,h.a_length])
  have high := leaf L.high L.d (Or.inr (Or.inl rfl)) (Or.inr (Or.inl rfl))
    (by simp [h.high_length]) (by simp [h.high_length,h.d_length])
  have sum := leaf L.sum L.c (Or.inr (Or.inr rfl)) (Or.inr (Or.inr rfl))
    (by simp [h.sum_length]) (by simp [h.sum_length,h.c_length])
  obtain ⟨sp,sc⟩ := L.sum_wires_subset h
  obtain ⟨comb,uncomb⟩ := L.combine_wires_subset h
  have cp := L.copySquares_wires_subset h
  simp only [signedKaratsubaSquare,signedKaratsubaSquareClear,
    KaratsubaSquareLayout.signedSquareLow,KaratsubaSquareLayout.signedClearLow,
    KaratsubaSquareLayout.signedSquareHigh,KaratsubaSquareLayout.signedClearHigh,
    KaratsubaSquareLayout.signedSquareSum,KaratsubaSquareLayout.signedClearSquareSum,
    wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨low.1,high.1⟩,sp⟩,sum.1⟩,sc⟩,cp⟩,comb⟩,sp⟩,sum.2⟩,sc⟩,
    ⟨⟨⟨⟨⟨⟨⟨⟨sp,sum.1⟩,sc⟩,uncomb⟩,cp⟩,sp⟩,sum.2⟩,sc⟩,high.2⟩,low.2⟩

private theorem signed_values_frame (L : KaratsubaSquareLayout)
    (lo hi av dv zv av' dv' zv' : Nat) (s u : BasisState)
    (hs : KaratsubaValues L lo hi av dv 0 zv 0 s)
    (hu : KaratsubaValues L lo hi av' dv' 0 zv' 0 u)
    (ho : ∀w,w∉L.wires→u w=s w) :
    ∀w,w∉L.a++L.d++L.z→u w=s w := by
  intro w hw
  have eqv (r : List Wire) (he : regValue r u=regValue r s) (hm : w∈r) : u w=s w :=
    (regValue_eq_iff r u s).mp he w hm
  by_cases hl : w∈L.low
  · exact eqv L.low (hu.low.trans hs.low.symm) hl
  by_cases hh : w∈L.high
  · exact eqv L.high (hu.high.trans hs.high.symm) hh
  by_cases hc : w∈L.c
  · exact eqv L.c (hu.c.trans hs.c.symm) hc
  by_cases hsum : w∈L.sum
  · exact eqv L.sum (hu.sum.trans hs.sum.symm) hsum
  by_cases hp : w∈L.pad
  · exact eqv L.pad (hu.pad.trans hs.pad.symm) hp
  by_cases hm : w∈L.mask
  · exact eqv L.mask (hu.mask.trans hs.mask.symm) hm
  by_cases hk : w∈L.carry
  · exact eqv L.carry (hu.carry.trans hs.carry.symm) hk
  by_cases hc' : w=L.cin
  · subst w; exact hu.cin.trans hs.cin.symm
  apply ho
  simpa only [KaratsubaSquareLayout.wires,List.mem_cons,List.mem_append,hl,hh,hc,hsum,
    hp,hm,hk,hc',false_or,or_false] using hw

theorem signedKaratsubaSquare_frame (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi : Nat) (s : State) (m : List Bool)
    (hs : KaratsubaValues L lo hi 0 0 0 0 0 s.basis) :
    ∀w,w∉L.a++L.d++L.z→(run (signedKaratsubaSquare L) m s).basis w=s.basis w := by
  have hr := signedKaratsubaSquare_spec L h lo hi s m hs
  apply signed_values_frame L lo hi 0 0 0 (lo^2) (hi^2) ((lo+2^128*hi)^2)
    _ _ hs hr.2
  intro w hw
  apply run_preserves_outside
  intro hm
  exact hw (List.mem_toFinset.mp ((signedKaratsubaSquare_wires_subset L h).1 hm))

theorem signedKaratsubaSquareClear_frame (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi : Nat) (s : State) (m : List Bool)
    (hs : KaratsubaValues L lo hi (lo^2) (hi^2) 0 ((lo+2^128*hi)^2) 0 s.basis) :
    ∀w,w∉L.a++L.d++L.z→(run (signedKaratsubaSquareClear L) m s).basis w=s.basis w := by
  have hr := signedKaratsubaSquareClear_spec L h lo hi s m hs
  apply signed_values_frame L lo hi (lo^2) (hi^2) ((lo+2^128*hi)^2) 0 0 0
    _ _ hs hr.2
  intro w hw
  apply run_preserves_outside
  intro hm
  exact hw (List.mem_toFinset.mp ((signedKaratsubaSquare_wires_subset L h).2 hm))

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/SquareNormalizeProof.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 常数受控加减的完整逐线规格；临时常数及进位均归零。 -/
theorem maskedConst_frame (sub : Bool) (c cin : Wire) (T y carry : List Wire)
    (hn : (c::cin::(T++y++carry)).Nodup) (hT : T.length=y.length)
    (hc : carry.length+1=y.length) (K : Nat) (hK : K<2^T.length)
    (base : BasisState) (hz : regValue (T++carry) base=0) (hi : base cin=false) (A : Nat) :
    Triple (SquareFrame y base A)
      (if sub then maskedSubConst c T y carry cin K else maskedAddConst c T y carry cin K)
      (SquareFrame y base (if sub then (A+2^y.length-(if base c then K else 0))%2^y.length
        else (A+(if base c then K else 0))%2^y.length)) := by
  have outside (w : Wire) (hw : w∈c::cin::(T++carry)) : w∉y := by
    intro hy
    have h := List.nodup_iff_count.mp hn w
    have h1 := List.count_pos_iff.mpr hw
    have h2 := List.count_pos_iff.mpr hy
    simp only [List.count_cons,List.count_append] at h h1
    omega
  intro s m h
  have keep (w : Wire) (hw : w∈c::cin::(T++carry)) := h.2 w (outside w hw)
  have ct : s.basis c=base c := keep c (by simp)
  have ci : s.basis cin=false := (keep cin (by simp)).trans hi
  have clean (r : List Wire) (hr : r⊆T++carry) : regValue r s.basis=0 := by
    apply (regValue_zero _ _).mpr; intro w hw
    have hh := hr hw
    rw [keep w (by simp only [List.mem_cons,List.mem_append] at hh ⊢; tauto)]
    exact (regValue_zero _ _).mp hz w hh
  have tz := clean T (by simp)
  have cz := clean carry (by simp)
  have frame (prg : Program)
      (ws : wires prg⊆(c::cin::(T++y++carry)).toFinset)
      (pc : (run prg m s).basis c=base c) (pi : (run prg m s).basis cin=false)
      (pt : regValue T (run prg m s).basis=0) (pk : regValue carry (run prg m s).basis=0) :
      ∀w,w∉y → (run prg m s).basis w=base w := by
    intro w hw
    by_cases ht : w∈T
    · exact ((regValue_zero _ _).mp pt w ht).trans ((regValue_zero _ _).mp hz w (by simp [ht])).symm
    by_cases hk : w∈carry
    · exact ((regValue_zero _ _).mp pk w hk).trans ((regValue_zero _ _).mp hz w (by simp [hk])).symm
    by_cases hcw : w=c
    · subst w; exact pc
    by_cases hiw : w=cin
    · subst w; exact pi.trans hi.symm
    have ho : w∉wires prg := fun hh => by
      have hm := ws hh
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hm
      tauto
    exact (run_preserves_outside prg m s w ho).trans (h.2 w hw)
  cases sub
  · have specs := maskedAddConst_spec c cin T y carry hn hT hc K hK (base c) A s m ⟨⟨⟨⟨ct,tz⟩,h.1⟩,ci⟩,cz⟩
    simp only [Bool.false_eq_true,↓reduceIte]
    exact ⟨specs.1,specs.2.1.1.2,frame _ (maskedConst_wires_subset c T y carry cin K hT hc).1
      specs.2.1.1.1.1 specs.2.1.2 specs.2.1.1.1.2 specs.2.2⟩
  · have specs := maskedSubConst_spec c cin T y carry hn hT hc K hK (base c) A s m ⟨⟨⟨⟨ct,tz⟩,h.1⟩,ci⟩,cz⟩
    simp only [↓reduceIte]
    exact ⟨specs.1,specs.2.1.1.2,frame _ (maskedConst_wires_subset c T y carry cin K hT hc).2
      specs.2.1.1.1.1 specs.2.1.2 specs.2.1.1.1.2 specs.2.2⟩

/-- 规范化只改变低256位及其保留标志。 -/
def SquareNormFrame (L : SquareReduceLayout) (base : BasisState) (V : Nat) (F : Bool)
    (s : BasisState) : Prop :=
  regValue L.value s=V ∧ s L.flag=F ∧ ∀w,w∉L.value++[L.flag] → s w=base w

private theorem norm_nd (L : SquareReduceLayout) (hn : L.wires.Nodup) :
    (L.flag::L.cin::(L.value++L.mask++L.carry)).Nodup := by
  apply List.nodup_iff_count.mpr; intro w
  have h := List.nodup_iff_count.mp hn w
  have hv := (List.take_sublist 256 L.r).count_le w
  simp only [SquareReduceLayout.wires,List.count_append,List.count_cons,List.count_nil] at h
  simp only [List.count_cons,List.count_append,SquareReduceLayout.value]
  omega

private theorem norm_outside (L : SquareReduceLayout) (hn : L.wires.Nodup) (w : Wire)
    (hw : w∈L.cin::(L.mask++L.carry)) : w∉L.value++[L.flag] := by
  intro hh
  have h := List.nodup_iff_count.mp (norm_nd L hn) w
  have h1 := List.count_pos_iff.mpr hw
  have h2 := List.count_pos_iff.mpr hh
  simp only [List.count_cons,List.count_append,List.count_nil] at h h1 h2
  omega

private theorem norm_compare (L : SquareReduceLayout) (hn : L.wires.Nodup) (hw : L.Widths)
    (base : BasisState) (hz : regValue (L.mask++L.carry) base=0) (hi : base L.cin=false)
    (W : Nat) (F : Bool) :
    Triple (SquareNormFrame L base W F)
      (compareLtConst none L.value L.mask (L.carry.take 256) L.cin L.flag SquareReduction.p)
      (SquareNormFrame L base W (F ^^ decide (W<SquareReduction.p))) := by
  have hv : L.value.length=256 := by simp [SquareReduceLayout.value,hw.r]
  have nd : (L.flag::L.cin::(L.value++L.mask++L.carry.take 256)).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have h := List.nodup_iff_count.mp (norm_nd L hn) w
    have hc := (List.take_sublist 256 L.carry).count_le w
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  have ht : L.value.length=L.mask.length := hv.trans hw.mask.symm
  have hc : (L.carry.take 256).length=L.mask.length := by simp [hw.carry,hw.mask]
  have hp : SquareReduction.p<2^L.mask.length := by norm_num [hw.mask,SquareReduction.p,SquareReduction.B,SquareReduction.c]
  intro s m h
  have keep (w : Wire) (hh : w∈L.cin::(L.mask++L.carry)) := h.2.2 w (norm_outside L hn w hh)
  have ci : s.basis L.cin=false := (keep _ (by simp)).trans hi
  have clean (r : List Wire) (hr : r⊆L.mask++L.carry) : regValue r s.basis=0 := by
    apply (regValue_zero _ _).mpr; intro w hh
    have hmem := hr hh
    rw [keep w (by simp only [List.mem_cons] ; exact Or.inr hmem)]
    exact (regValue_zero _ _).mp hz w hmem
  have tz := clean L.mask (by simp)
  have cz := clean (L.carry.take 256) (by intro w hh; simp [List.mem_of_mem_take hh])
  have sp := compareLtConst_spec L.value L.mask (L.carry.take 256) L.cin L.flag
    nd ht hc SquareReduction.p hp W F s m ⟨⟨⟨⟨h.1,tz⟩,cz⟩,ci⟩,h.2.1⟩
  refine ⟨sp.1,sp.2.1.1.1.1,sp.2.2,?_⟩
  intro w hh
  have hval : w∉L.value := fun hm => hh (by simp [hm])
  have hflag : w≠L.flag := fun he => hh (by simp [he])
  by_cases hm : w∈L.mask
  · exact ((regValue_zero _ _).mp sp.2.1.1.1.2 w hm).trans ((regValue_zero _ _).mp hz w (by simp [hm])).symm
  by_cases hcy : w∈L.carry.take 256
  · exact ((regValue_zero _ _).mp sp.2.1.1.2 w hcy).trans
      ((regValue_zero _ _).mp hz w (by simp [List.mem_of_mem_take hcy])).symm
  by_cases hci : w=L.cin
  · subst w; exact sp.2.1.2.trans hi.symm
  have ho : w∉wires (compareLtConst none L.value L.mask (L.carry.take 256) L.cin L.flag SquareReduction.p) := by
    rw [(compareLt_wires none L.value L.mask (L.carry.take 256) L.cin L.flag ht hc).2]
    simpa using (show w∉L.flag::L.cin::(L.value++L.mask++L.carry.take 256) by simp [hflag,hci,hval,hm,hcy])
  exact (run_preserves_outside _ m s w ho).trans (h.2.2 w hh)

private theorem norm_flip (L : SquareReduceLayout) (hn : L.wires.Nodup)
    (base : BasisState) (W : Nat) (F : Bool) :
    Triple (SquareNormFrame L base W F) [.X L.flag] (SquareNormFrame L base W (!F)) := by
  have hf : L.flag∉L.value := by
    have hh := (List.nodup_cons.mp (norm_nd L hn)).1
    intro hm; exact hh (by simp [hm])
  intro s m h
  refine ⟨rfl,?_,?_,?_⟩
  · change regValue L.value (writeBit s.basis L.flag (!(s.basis L.flag)))=W
    rw [regValue_congr L.value _ s.basis (fun w hw => by simp [writeBit,Function.update,show w≠L.flag from fun he => hf (he ▸ hw)])]
    exact h.1
  · simpa [run,writeBit] using congrArg Bool.not h.2.1
  · intro w hw
    have hf : w≠L.flag := fun he => hw (by simp [he])
    simpa [run,writeBit,hf] using h.2.2 w hw

private theorem norm_arith (sub : Bool) (L : SquareReduceLayout) (hn : L.wires.Nodup) (hw : L.Widths)
    (base : BasisState) (hz : regValue (L.mask++L.carry) base=0) (hi : base L.cin=false)
    (W : Nat) (F : Bool) :
    Triple (SquareNormFrame L base W F)
      (if sub then maskedSubConst L.flag L.mask L.value (L.carry.take 255) L.cin SquareReduction.p
       else maskedAddConst L.flag L.mask L.value (L.carry.take 255) L.cin SquareReduction.p)
      (SquareNormFrame L base
        (if sub then (W+2^256-(if F then SquareReduction.p else 0))%2^256
         else (W+(if F then SquareReduction.p else 0))%2^256) F) := by
  have hv : L.value.length=256 := by simp [SquareReduceLayout.value,hw.r]
  have nd : (L.flag::L.cin::(L.mask++L.value++L.carry.take 255)).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have h := List.nodup_iff_count.mp (norm_nd L hn) w
    have hc := (List.take_sublist 255 L.carry).count_le w
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  have ht : L.mask.length=L.value.length := hw.mask.trans hv.symm
  have hc : (L.carry.take 255).length+1=L.value.length := by simp [hw.carry,hv]
  have hp : SquareReduction.p<2^L.mask.length := by norm_num [hw.mask,SquareReduction.p,SquareReduction.B,SquareReduction.c]
  intro s m h
  have keep (w : Wire) (hh : w∈L.cin::(L.mask++L.carry)) := h.2.2 w (norm_outside L hn w hh)
  have ci : s.basis L.cin=false := (keep _ (by simp)).trans hi
  have clean : regValue (L.mask++L.carry.take 255) s.basis=0 := by
    apply (regValue_zero _ _).mpr; intro w hh
    have hmem : w∈L.mask++L.carry := by
      simp only [List.mem_append] at hh ⊢
      exact hh.elim Or.inl (fun h => Or.inr (List.mem_of_mem_take h))
    rw [keep w (by simp only [List.mem_cons]; exact Or.inr hmem)]
    exact (regValue_zero _ _).mp hz w hmem
  have sp := maskedConst_frame sub L.flag L.cin L.mask L.value (L.carry.take 255)
    nd ht hc SquareReduction.p hp s.basis clean ci W s m ⟨h.1,fun _ _ => rfl⟩
  have hf : L.flag∉L.value := by
    have hh := (List.nodup_cons.mp (norm_nd L hn)).1
    intro hm; exact hh (by simp [hm])
  refine ⟨sp.1,?_,(sp.2.2 L.flag hf).trans h.2.1,?_⟩
  · simpa only [hv,h.2.1] using sp.2.1
  · intro w hh
    exact (sp.2.2 w (fun hm => hh (by simp [hm]))).trans (h.2.2 w hh)

/-- 规范化及独立前向恢复；保留标志精确记录是否试减 p。 -/
theorem squareNormalize_correct (L : SquareReduceLayout) (hn : L.wires.Nodup) (hw : L.Widths)
    (base : BasisState) (hz : regValue (L.mask++L.carry) base=0) (hi : base L.cin=false)
    (W : Nat) (hW : W<SquareReduction.B) :
    Triple (SquareNormFrame L base W false) (squareNormalize L)
      (SquareNormFrame L base (W%SquareReduction.p) (decide (SquareReduction.p≤W))) ∧
    Triple (SquareNormFrame L base (W%SquareReduction.p) (decide (SquareReduction.p≤W)))
      (squareDenormalize L) (SquareNormFrame L base W false) := by
  have hW' : W<2^256 := hW
  have hc : (!(decide (W<SquareReduction.p)))=decide (SquareReduction.p≤W) := by
    by_cases h : W<SquareReduction.p <;> simp [h, show (SquareReduction.p≤W)↔¬W<SquareReduction.p by omega]
  have hc' : (!(decide (SquareReduction.p≤W)))=decide (W<SquareReduction.p) := by
    rw [←hc,Bool.not_not]
  have hnumb : (W+2^256-(if decide (SquareReduction.p≤W) then SquareReduction.p else 0))%2^256=
      W%SquareReduction.p := by
    have hh := SquareReduction.normalize W hW
    by_cases h : SquareReduction.p≤W
    · simp only [h,decide_true,↓reduceIte] at hh ⊢
      have he : W+2^256-SquareReduction.p=(W-SquareReduction.p)+2^256 := by omega
      rw [he,Nat.add_mod_right,Nat.mod_eq_of_lt (by change W-SquareReduction.p<SquareReduction.B; omega)]
      exact hh
    · simp only [h,decide_false,Bool.false_eq_true,↓reduceIte,Nat.sub_zero,Nat.add_mod_right] at hh ⊢
      rw [Nat.mod_eq_of_lt hW']
      exact hh
  have hnuma : (W%SquareReduction.p+(if decide (SquareReduction.p≤W) then SquareReduction.p else 0))%2^256=W := by
    have hh := SquareReduction.normalize W hW
    by_cases h : SquareReduction.p≤W
    · simp only [h,decide_true,↓reduceIte] at hh ⊢
      rw [←hh,Nat.sub_add_cancel h,Nat.mod_eq_of_lt hW']
    · simp only [h,decide_false,Bool.false_eq_true,↓reduceIte,Nat.sub_zero] at hh ⊢
      rw [←hh,Nat.add_zero,Nat.mod_eq_of_lt hW']
  have cmp := norm_compare L hn hw base hz hi W false
  simp only [Bool.false_xor] at cmp
  have flip := norm_flip L hn base W (decide (W<SquareReduction.p))
  rw [hc] at flip
  have sb := norm_arith true L hn hw base hz hi W (decide (SquareReduction.p≤W))
  simp only [↓reduceIte,hnumb] at sb
  have ad := norm_arith false L hn hw base hz hi (W%SquareReduction.p) (decide (SquareReduction.p≤W))
  simp only [Bool.false_eq_true,↓reduceIte,hnuma] at ad
  have fl := norm_flip L hn base W (decide (SquareReduction.p≤W))
  rw [hc'] at fl
  have cm := norm_compare L hn hw base hz hi W (decide (W<SquareReduction.p))
  simp only [Bool.xor_self] at cm
  constructor
  · simpa only [squareNormalize,List.append_assoc] using cmp.seq (flip.seq sb)
  · simpa only [squareDenormalize,List.append_assoc] using ad.seq (fl.seq cm)

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/SquareReduceLayout.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
namespace SquareReduceLayout

theorem value_length (L : SquareReduceLayout) (hw : L.Widths) : L.value.length=256 := by
  simp [value,hw.r]
theorem quotient_length (L : SquareReduceLayout) (hw : L.Widths) : L.quotient.length=33 := by
  simp [quotient,hw.r]
theorem extended_length (L : SquareReduceLayout) (hw : L.Widths) : L.extended.length=257 := by
  simp [extended,L.value_length hw]
theorem value_quotient (L : SquareReduceLayout) : L.value++L.quotient=L.r :=
  List.take_append_drop _ _

theorem first_nodup (L : SquareReduceLayout) (hn : L.wires.Nodup) :
    (L.cin::(L.high++L.r++L.pad++L.carry)).Nodup := by
  apply List.nodup_iff_count.mpr; intro w
  have h := List.nodup_iff_count.mp hn w
  simp only [wires,List.count_append,List.count_cons,List.count_nil] at h ⊢
  omega

theorem second_nodup (L : SquareReduceLayout) (hn : L.wires.Nodup) :
    (L.cin::(L.quotient++L.extended++L.pad++L.carry)).Nodup := by
  apply List.nodup_iff_count.mpr; intro w
  have h := List.nodup_iff_count.mp hn w
  have he := congrArg (List.count w) L.value_quotient
  simp only [List.count_append] at he
  simp only [wires,extended,List.count_append,List.count_cons,List.count_nil] at h ⊢
  omega

theorem value_read (L : SquareReduceLayout) (hw : L.Widths) (s : BasisState) :
    regValue L.value s=regValue L.r s%SquareReduction.B := by
  rw [←L.value_quotient,regValue_append,L.value_length hw]
  simp only [SquareReduction.B,Nat.add_mul_mod_self_left]
  exact (Nat.mod_eq_of_lt (by simpa [L.value_length hw] using regValue_lt L.value s)).symm

theorem quotient_read (L : SquareReduceLayout) (hw : L.Widths) (s : BasisState) :
    regValue L.quotient s=regValue L.r s/SquareReduction.B := by
  have he := regValue_append L.value L.quotient s
  rw [L.value_quotient,L.value_length hw] at he
  have hb := regValue_lt L.value s
  rw [L.value_length hw] at hb
  simp only [SquareReduction.B]
  omega

theorem extended_low (L : SquareReduceLayout) (hw : L.Widths) (s : BasisState) :
    regValue L.value s=regValue L.extended s%SquareReduction.B := by
  simpa [extended,L.value_length hw,SquareReduction.B] using regValue_low L.value L.b s

theorem extended_high (L : SquareReduceLayout) (hw : L.Widths) (s : BasisState) :
    (s L.b).toNat=regValue L.extended s/SquareReduction.B := by
  simp only [extended,regValue_append,L.value_length hw,SquareReduction.B]
  rw [Nat.add_mul_div_left _ _ (by positivity),
    Nat.div_eq_of_lt (by simpa [L.value_length hw] using regValue_lt L.value s)]
  cases hb : s L.b <;> simp [regValue,hb]

end SquareReduceLayout
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/SquareReduceProof.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 第一折叠及其清理。高33位保留为后续折叠的商记录。 -/
theorem squareFirstFold_correct (L : SquareReduceLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (base : BasisState)
    (hz : regValue (L.pad++L.carry) base=0) (hi : base L.cin=false) :
    let U := regValue L.low base+SquareReduction.c*regValue L.high base
    Triple (SquareFrame L.r base 0)
      (copyRegister none L.low L.value ++
        squareFoldAdd L.high L.r L.pad L.carry L.cin squareFoldShifts)
      (SquareFrame L.r base U) ∧
    Triple (SquareFrame L.r base U)
      (squareFoldClear L.high L.r L.pad L.carry L.cin squareFoldShifts ++
        copyRegister none L.low L.value)
      (SquareFrame L.r base 0) := by
  have hr := hw.r
  have hh := hw.high
  have hpad := hw.pad
  have hcarry := hw.carry
  have hlr : (L.low++L.r).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have h := List.nodup_iff_count.mp hn w
    simp only [SquareReduceLayout.wires,List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have hcopy := karatsuba_copy_low L.low L.r 256 hw.low (by omega) hlr base
  have hlow : regValue L.low base<SquareReduction.B := by
    simpa [hw.low,SquareReduction.B] using regValue_lt L.low base
  have hhigh : regValue L.high base<SquareReduction.B := by
    simpa [hw.high,SquareReduction.B] using regValue_lt L.high base
  have hweight : squareFoldWeight squareFoldShifts=SquareReduction.c := by
    norm_num [squareFoldWeight,squareFoldShifts,SquareReduction.c]
  have hfold := squareFold_correct L.high L.r L.pad L.carry L.cin squareFoldShifts
    (L.first_nodup hn) (by omega)
    (by intro j hj; simp [squareFoldShifts] at hj; omega) (by omega) (by omega)
    base hz hi (regValue L.low base) (by
      rw [hweight,hw.r,Nat.mul_comm (regValue L.high base)]
      exact SquareReduction.first_bound _ _ hlow hhigh)
  simpa only [hweight,Nat.mul_comm (regValue L.high base),SquareReduceLayout.value] using
    And.intro (hcopy.1.seq hfold.1) (hfold.2.seq hcopy.2)

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/SquareReduceState.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

/-- 各折叠阶段的显式值：q、b、f 是必须保留的记录，借用区始终为零。 -/
structure SquareReduceValues (L : SquareReduceLayout) (lo hi v q : Nat) (b f : Bool)
    (s : BasisState) : Prop where
  low : regValue L.low s=lo
  high : regValue L.high s=hi
  value : regValue L.value s=v
  quotient : regValue L.quotient s=q
  pad : regValue L.pad s=0
  mask : regValue L.mask s=0
  carry : regValue L.carry s=0
  cin : s L.cin=false
  bit : s L.b=b
  flag : s L.flag=f

namespace SquareReduceValues

variable {L : SquareReduceLayout} {lo hi v q : Nat} {b f : Bool} {s t : BasisState}

theorem work_zero (h : SquareReduceValues L lo hi v q b f s) :
    regValue (L.pad++L.carry) s=0 := by simp [regValue_append,h.pad,h.carry]

theorem r_read (h : SquareReduceValues L lo hi v q b f s) (hw : L.Widths) :
    regValue L.r s=v+SquareReduction.B*q := by
  rw [←L.value_quotient,regValue_append,L.value_length hw,h.value,h.quotient]
  rfl

theorem extended_read (h : SquareReduceValues L lo hi v q b f s) (hw : L.Widths) :
    regValue L.extended s=v+SquareReduction.B*b.toNat := by
  simp only [SquareReduceLayout.extended,regValue_append,L.value_length hw,h.value]
  cases b <;> simp [regValue,h.bit,SquareReduction.B]

/-- 整个289位目标改变时，所有其它寄存器由目标外保持推出。 -/
theorem of_r_frame (h : SquareReduceValues L lo hi v q b f s) (hw : L.Widths)
    (hn : L.wires.Nodup) (U : Nat) (ht : SquareFrame L.r s U t) :
    SquareReduceValues L lo hi (U%SquareReduction.B) (U/SquareReduction.B) b f t := by
  have outside (w : Wire) (hm : w∈L.low++L.high++L.pad++L.mask++L.carry++[L.cin,L.b,L.flag]) :
      w∉L.r := by
    intro hr
    have h1 := List.nodup_iff_count.mp hn w
    have h2 := List.count_pos_iff.mpr hm
    have h3 := List.count_pos_iff.mpr hr
    simp only [SquareReduceLayout.wires,List.count_append,List.count_cons,List.count_nil] at h1 h2
    omega
  have keep (r : List Wire) (hr : r⊆L.low++L.high++L.pad++L.mask++L.carry++[L.cin,L.b,L.flag]) :
      regValue r t=regValue r s := regValue_congr _ _ _ (fun w hm => ht.2 w (outside w (hr hm)))
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (keep _ (by intro w hm; simp [hm])).trans h.low
  · exact (keep _ (by intro w hm; simp [hm])).trans h.high
  · rw [L.value_read hw,ht.1]
  · rw [L.quotient_read hw,ht.1]
  · exact (keep _ (by intro w hm; simp [hm])).trans h.pad
  · exact (keep _ (by intro w hm; simp [hm])).trans h.mask
  · exact (keep _ (by intro w hm; simp [hm])).trans h.carry
  · exact (ht.2 _ (outside _ (by simp))).trans h.cin
  · exact (ht.2 _ (outside _ (by simp))).trans h.bit
  · exact (ht.2 _ (outside _ (by simp))).trans h.flag

/-- 第二折叠改变低256位和独立 b，商 q 逐位保持。 -/
theorem of_extended_frame (h : SquareReduceValues L lo hi v q b f s) (hw : L.Widths)
    (hn : L.wires.Nodup) (V : Nat) (ht : SquareFrame L.extended s V t) :
    SquareReduceValues L lo hi (V%SquareReduction.B) q (decide (SquareReduction.B≤V)) f t := by
  have hc (w : Wire) := congrArg (List.count w) L.value_quotient
  simp only [List.count_append] at hc
  have outside (w : Wire) (hm : w∈L.low++L.high++L.quotient++L.pad++L.mask++L.carry++[L.cin,L.flag]) :
      w∉L.extended := by
    intro hr
    have h1 := List.nodup_iff_count.mp hn w
    have h2 := List.count_pos_iff.mpr hm
    have h3 := List.count_pos_iff.mpr hr
    have he := hc w
    simp only [SquareReduceLayout.wires,SquareReduceLayout.extended,List.count_append,
      List.count_cons,List.count_nil] at h1 h2 h3
    omega
  have keep (r : List Wire) (hr : r⊆L.low++L.high++L.quotient++L.pad++L.mask++L.carry++[L.cin,L.flag]) :
      regValue r t=regValue r s := regValue_congr _ _ _ (fun w hm => ht.2 w (outside w (hr hm)))
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (keep _ (by intro w hm; simp [hm])).trans h.low
  · exact (keep _ (by intro w hm; simp [hm])).trans h.high
  · rw [L.extended_low hw,ht.1]
  · exact (keep _ (by intro w hm; simp [hm])).trans h.quotient
  · exact (keep _ (by intro w hm; simp [hm])).trans h.pad
  · exact (keep _ (by intro w hm; simp [hm])).trans h.mask
  · exact (keep _ (by intro w hm; simp [hm])).trans h.carry
  · exact (ht.2 _ (outside _ (by simp))).trans h.cin
  · apply Bool.eq_iff_iff.mpr
    have he : regValue (L.value++[L.b]) t=V := ht.1
    simpa [L.value_length hw,SquareReduction.B,he] using
      regValue_highBit L.value L.b t
  · exact (ht.2 _ (outside _ (by simp))).trans h.flag

/-- 第三折叠仅更新低256位，保留 q、b、f。 -/
theorem of_value_frame (h : SquareReduceValues L lo hi v q b f s)
    (hn : L.wires.Nodup) (V : Nat) (ht : SquareFrame L.value s V t) :
    SquareReduceValues L lo hi V q b f t := by
  have hc (w : Wire) := congrArg (List.count w) L.value_quotient
  simp only [List.count_append] at hc
  have outside (w : Wire) (hm : w∈L.low++L.high++L.quotient++L.pad++L.mask++L.carry++[L.cin,L.b,L.flag]) :
      w∉L.value := by
    intro hr
    have h1 := List.nodup_iff_count.mp hn w
    have h2 := List.count_pos_iff.mpr hm
    have h3 := List.count_pos_iff.mpr hr
    have he := hc w
    simp only [SquareReduceLayout.wires,List.count_append,List.count_cons,List.count_nil] at h1 h2
    omega
  have keep (r : List Wire) (hr : r⊆L.low++L.high++L.quotient++L.pad++L.mask++L.carry++[L.cin,L.b,L.flag]) :
      regValue r t=regValue r s := regValue_congr _ _ _ (fun w hm => ht.2 w (outside w (hr hm)))
  refine ⟨?_,?_,ht.1,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (keep _ (by intro w hm; simp [hm])).trans h.low
  · exact (keep _ (by intro w hm; simp [hm])).trans h.high
  · exact (keep _ (by intro w hm; simp [hm])).trans h.quotient
  · exact (keep _ (by intro w hm; simp [hm])).trans h.pad
  · exact (keep _ (by intro w hm; simp [hm])).trans h.mask
  · exact (keep _ (by intro w hm; simp [hm])).trans h.carry
  · exact (ht.2 _ (outside _ (by simp))).trans h.cin
  · exact (ht.2 _ (outside _ (by simp))).trans h.bit
  · exact (ht.2 _ (outside _ (by simp))).trans h.flag

theorem of_norm_frame (h : SquareReduceValues L lo hi v q b f s)
    (hn : L.wires.Nodup) (V : Nat) (F : Bool) (ht : SquareNormFrame L s V F t) :
    SquareReduceValues L lo hi V q b F t := by
  have hc (w : Wire) := congrArg (List.count w) L.value_quotient
  simp only [List.count_append] at hc
  have outside (w : Wire) (hm : w∈L.low++L.high++L.quotient++L.pad++L.mask++L.carry++[L.cin,L.b]) :
      w∉L.value++[L.flag] := by
    intro hr
    have h1 := List.nodup_iff_count.mp hn w
    have h2 := List.count_pos_iff.mpr hm
    have h3 := List.count_pos_iff.mpr hr
    simp only [List.count_append,List.count_cons,List.count_nil] at h3
    have he := hc w
    simp only [SquareReduceLayout.wires,List.count_append,List.count_cons,List.count_nil] at h1 h2
    omega
  have keep (r : List Wire) (hr : r⊆L.low++L.high++L.quotient++L.pad++L.mask++L.carry++[L.cin,L.b]) :
      regValue r t=regValue r s := regValue_congr _ _ _ (fun w hm => ht.2.2 w (outside w (hr hm)))
  refine ⟨?_,?_,ht.1,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (keep _ (by intro w hm; simp [hm])).trans h.low
  · exact (keep _ (by intro w hm; simp [hm])).trans h.high
  · exact (keep _ (by intro w hm; simp [hm])).trans h.quotient
  · exact (keep _ (by intro w hm; simp [hm])).trans h.pad
  · exact (keep _ (by intro w hm; simp [hm])).trans h.mask
  · exact (keep _ (by intro w hm; simp [hm])).trans h.carry
  · exact (ht.2.2 _ (outside _ (by simp))).trans h.cin
  · exact (ht.2.2 _ (outside _ (by simp))).trans h.bit
  · exact ht.2.1

end SquareReduceValues
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/SquareReduceSpec.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

private theorem first_values (L : SquareReduceLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (lo hi : Nat) :
    let U := lo+SquareReduction.c*hi
    Triple (SquareReduceValues L lo hi 0 0 false false)
      (copyRegister none L.low L.value ++ squareFoldAdd L.high L.r L.pad L.carry L.cin squareFoldShifts)
      (SquareReduceValues L lo hi (U%SquareReduction.B) (U/SquareReduction.B) false false) ∧
    Triple (SquareReduceValues L lo hi (U%SquareReduction.B) (U/SquareReduction.B) false false)
      (squareFoldClear L.high L.r L.pad L.carry L.cin squareFoldShifts ++ copyRegister none L.low L.value)
      (SquareReduceValues L lo hi 0 0 false false) := by
  dsimp
  constructor
  · intro s m h
    have sp := (squareFirstFold_correct L hw hn s.basis h.work_zero h.cin).1 s m
      ⟨by simpa using h.r_read hw, fun _ _ => rfl⟩
    simp only [h.low,h.high] at sp
    exact ⟨sp.1,h.of_r_frame hw hn _ sp.2⟩
  · intro s m h
    have sp := (squareFirstFold_correct L hw hn s.basis h.work_zero h.cin).2 s m
      ⟨by rw [h.r_read hw,h.low,h.high]; exact Nat.mod_add_div _ _, fun _ _ => rfl⟩
    simpa using And.intro sp.1 (h.of_r_frame hw hn _ sp.2)

private theorem second_values (L : SquareReduceLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (A Q : Nat) (hA : A<SquareReduction.B) (hV : A+SquareReduction.c*Q<2^257)
    (lo hi : Nat) :
    let V := A+SquareReduction.c*Q
    Triple (SquareReduceValues L lo hi A Q false false)
      (squareFoldAdd L.quotient L.extended L.pad L.carry L.cin squareFoldShifts)
      (SquareReduceValues L lo hi (V%SquareReduction.B) Q (decide (SquareReduction.B≤V)) false) ∧
    Triple (SquareReduceValues L lo hi (V%SquareReduction.B) Q (decide (SquareReduction.B≤V)) false)
      (squareFoldClear L.quotient L.extended L.pad L.carry L.cin squareFoldShifts)
      (SquareReduceValues L lo hi A Q false false) := by
  have hweight : squareFoldWeight squareFoldShifts=SquareReduction.c := by
    norm_num [squareFoldWeight,squareFoldShifts,SquareReduction.c]
  have primitive (base : BasisState) (hz : regValue (L.pad++L.carry) base=0)
      (hc : base L.cin=false) (hq : regValue L.quotient base=Q) :=
    squareFold_correct L.quotient L.extended L.pad L.carry L.cin squareFoldShifts
      (L.second_nodup hn) (by rw [L.extended_length hw]; omega)
      (by intro j hj; rw [L.quotient_length hw,L.extended_length hw]; simp [squareFoldShifts] at hj; omega)
      (by rw [hw.pad,L.extended_length hw,L.quotient_length hw]; omega)
      (by rw [hw.carry,L.extended_length hw]; omega)
      base hz hc A (by simpa only [L.extended_length hw,hweight,hq,Nat.mul_comm Q] using hV)
  dsimp
  constructor
  · intro s m h
    have sp := (primitive s.basis h.work_zero h.cin h.quotient).1 s m
      ⟨by simpa using h.extended_read hw,fun _ _ => rfl⟩
    simp only [hweight,h.quotient,Nat.mul_comm Q] at sp
    exact ⟨sp.1,h.of_extended_frame hw hn _ sp.2⟩
  · intro s m h
    have he : (decide (SquareReduction.B≤A+SquareReduction.c*Q)).toNat =
        (A+SquareReduction.c*Q)/SquareReduction.B := by
      have hv : A+SquareReduction.c*Q<2*SquareReduction.B := by simpa only [SquareReduction.B,show 2^257=2*2^256 by omega] using hV
      have hb := SquareReduction.carry_bound _ hv
      by_cases hc : SquareReduction.B≤A+SquareReduction.c*Q
      · simp only [hc,decide_true,Bool.toNat_true]
        have hp : 0<SquareReduction.B := by norm_num [SquareReduction.B]
        have hh : 1≤(A+SquareReduction.c*Q)/SquareReduction.B := (Nat.le_div_iff_mul_le hp).mpr (by simpa using hc)
        omega
      · simp only [hc,decide_false,Bool.toNat_false]
        exact (Nat.div_eq_of_lt (by omega)).symm
    have sp := (primitive s.basis h.work_zero h.cin h.quotient).2 s m
      ⟨by rw [h.extended_read hw,he,hweight,h.quotient,Nat.mul_comm Q]; exact Nat.mod_add_div _ _,fun _ _ => rfl⟩
    have hv := h.of_extended_frame hw hn _ sp.2
    simpa [Nat.mod_eq_of_lt hA,show ¬SquareReduction.B≤A by omega] using And.intro sp.1 hv

private theorem third_values (L : SquareReduceLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (A Q : Nat) (b : Bool) (hW : A+SquareReduction.c*b.toNat<SquareReduction.B)
    (lo hi : Nat) :
    let W := A+SquareReduction.c*b.toNat
    Triple (SquareReduceValues L lo hi A Q b false)
      (maskedAddConst L.b L.mask L.value (L.carry.take 255) L.cin SquareReduction.c)
      (SquareReduceValues L lo hi W Q b false) ∧
    Triple (SquareReduceValues L lo hi W Q b false)
      (maskedSubConst L.b L.mask L.value (L.carry.take 255) L.cin SquareReduction.c)
      (SquareReduceValues L lo hi A Q b false) := by
  have nd : (L.b::L.cin::(L.mask++L.value++L.carry.take 255)).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have h := List.nodup_iff_count.mp hn w
    have hv := (List.take_sublist 256 L.r).count_le w
    have hc := (List.take_sublist 255 L.carry).count_le w
    simp only [SquareReduceLayout.wires,List.count_append,List.count_cons,List.count_nil] at h
    simp only [SquareReduceLayout.value,List.count_append,List.count_cons]
    omega
  have prim (sub : Bool) (base : BasisState) (hz : regValue (L.mask++L.carry.take 255) base=0)
      (hc : base L.cin=false) (X : Nat) :=
    maskedConst_frame sub L.b L.cin L.mask L.value (L.carry.take 255) nd
      (by rw [hw.mask,L.value_length hw]) (by simp [hw.carry,L.value_length hw])
      SquareReduction.c (by norm_num [hw.mask,SquareReduction.c]) base hz hc X
  have clean {X : Nat} {s : BasisState} (h : SquareReduceValues L lo hi X Q b false s) :
      regValue (L.mask++L.carry.take 255) s=0 := by
    apply (regValue_zero _ _).mpr; intro w hh
    simp only [List.mem_append] at hh
    exact hh.elim ((regValue_zero _ _).mp h.mask w)
      (fun hh => (regValue_zero _ _).mp h.carry w (List.mem_of_mem_take hh))
  have hb : (if b then SquareReduction.c else 0)=SquareReduction.c*b.toNat := by cases b <;> simp
  have hA : A<SquareReduction.B := by omega
  dsimp
  constructor
  · intro s m h
    have sp := prim false s.basis (clean h) h.cin A s m ⟨h.value,fun _ _ => rfl⟩
    simp only [Bool.false_eq_true,↓reduceIte,h.bit,hb,L.value_length hw,
      Nat.mod_eq_of_lt (show A+SquareReduction.c*b.toNat<2^256 from hW)] at sp
    exact ⟨sp.1,h.of_value_frame hn _ sp.2⟩
  · intro s m h
    have sp := prim true s.basis (clean h) h.cin (A+SquareReduction.c*b.toNat) s m
      ⟨h.value,fun _ _ => rfl⟩
    have he : A+SquareReduction.c*b.toNat+2^256-SquareReduction.c*b.toNat=A+2^256 := by omega
    simp only [↓reduceIte,h.bit,hb,L.value_length hw,he,Nat.add_mod_right,
      Nat.mod_eq_of_lt (show A<2^256 from hA)] at sp
    exact ⟨sp.1,h.of_value_frame hn _ sp.2⟩

private theorem norm_values (L : SquareReduceLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (W Q : Nat) (b : Bool) (hW : W<SquareReduction.B) (lo hi : Nat) :
    Triple (SquareReduceValues L lo hi W Q b false) (squareNormalize L)
      (SquareReduceValues L lo hi (W%SquareReduction.p) Q b (decide (SquareReduction.p≤W))) ∧
    Triple (SquareReduceValues L lo hi (W%SquareReduction.p) Q b (decide (SquareReduction.p≤W)))
      (squareDenormalize L) (SquareReduceValues L lo hi W Q b false) := by
  constructor
  · intro s m h
    have hz : regValue (L.mask++L.carry) s.basis=0 := by simp [regValue_append,h.mask,h.carry]
    have sp := (squareNormalize_correct L hn hw s.basis hz h.cin W hW).1 s m
      ⟨h.value,h.flag,fun _ _ => rfl⟩
    exact ⟨sp.1,h.of_norm_frame hn _ _ sp.2⟩
  · intro s m h
    have hz : regValue (L.mask++L.carry) s.basis=0 := by simp [regValue_append,h.mask,h.carry]
    have sp := (squareNormalize_correct L hn hw s.basis hz h.cin W hW).2 s m
      ⟨h.value,h.flag,fun _ _ => rfl⟩
    exact ⟨sp.1,h.of_norm_frame hn _ _ sp.2⟩

/-- 约减历史：商 q、第二折叠进位 b、规范化标志 f 保留到外部输出更新以后。 -/
def SquareReduced (L : SquareReduceLayout) (lo hi : Nat) : BasisState → Prop :=
  let U := lo+SquareReduction.c*hi
  let V := U%SquareReduction.B+SquareReduction.c*(U/SquareReduction.B)
  let W := V%SquareReduction.B+SquareReduction.c*(V/SquareReduction.B)
  SquareReduceValues L lo hi ((lo+SquareReduction.B*hi)%SquareReduction.p)
    (U/SquareReduction.B) (decide (SquareReduction.B≤V)) (decide (SquareReduction.p≤W))

/-- 同一合法门列的完整准备与独立前向清理；相位对全部测量记录精确保持。 -/
theorem squareReduce_correct (L : SquareReduceLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (lo hi : Nat) (hlo : lo<SquareReduction.B) (hhi : hi<SquareReduction.B) :
    Triple (SquareReduceValues L lo hi 0 0 false false) (squareReduce L) (SquareReduced L lo hi) ∧
    Triple (SquareReduced L lo hi) (squareReduceClear L) (SquareReduceValues L lo hi 0 0 false false) := by
  let U := lo+SquareReduction.c*hi
  let V := U%SquareReduction.B+SquareReduction.c*(U/SquareReduction.B)
  let b := decide (SquareReduction.B≤V)
  let W := V%SquareReduction.B+SquareReduction.c*(V/SquareReduction.B)
  have hV : V<2*SquareReduction.B := SquareReduction.second_bound lo hi hlo hhi
  have hb : b.toNat=V/SquareReduction.B := by
    have hq := SquareReduction.carry_bound V hV
    by_cases h : SquareReduction.B≤V
    · simp only [b,h,decide_true,Bool.toNat_true]
      have hp : 0<SquareReduction.B := by norm_num [SquareReduction.B]
      have hh : 1≤V/SquareReduction.B := (Nat.le_div_iff_mul_le hp).mpr (by simpa using h)
      omega
    · simp only [b,h,decide_false,Bool.toNat_false]
      exact (Nat.div_eq_of_lt (by omega)).symm
  have hW : W<SquareReduction.B := SquareReduction.third_bound V (SquareReduction.second_fine_bound lo hi hlo hhi)
  have hmod : W%SquareReduction.p=(lo+SquareReduction.B*hi)%SquareReduction.p := by
    dsimp [W,V,U]
    rw [SquareReduction.fold_mod,SquareReduction.fold_mod,SquareReduction.first_mod]
  have f1 := first_values L hw hn lo hi
  have f2 := second_values L hw hn (U%SquareReduction.B) (U/SquareReduction.B)
    (Nat.mod_lt _ (by norm_num [SquareReduction.B]))
    (by simpa only [SquareReduction.B,show 2^257=2*2^256 by omega] using hV) lo hi
  have f3 := third_values L hw hn (V%SquareReduction.B) (U/SquareReduction.B) b
    (by simpa only [hb] using hW) lo hi
  have f4 := norm_values L hw hn W (U/SquareReduction.B) b hW lo hi
  simp only [hb] at f3
  constructor
  · simpa only [squareReduce,SquareReduced,U,V,W,b,hmod,List.append_assoc] using
      f1.1.seq (f2.1.seq (f3.1.seq f4.1))
  · simpa only [squareReduceClear,SquareReduced,U,V,W,b,hmod,List.append_assoc] using
      f4.2.seq (f3.2.seq (f2.2.seq f1.2))

/-- 所有视图外线路逐位保持，准备和恢复使用各自实际支持集。 -/
theorem squareReduce_frame (L : SquareReduceLayout) (hw : L.Widths)
    (m : List Bool) (s : State) (w : Wire) (ho : w∉L.wires) :
    (run (squareReduce L) m s).basis w=s.basis w ∧
    (run (squareReduceClear L) m s).basis w=s.basis w := by
  have hs := squareReduce_wires_subset L hw
  constructor
  · exact run_preserves_outside _ m s w (fun hm => ho (List.mem_toFinset.mp (hs.1 hm)))
  · exact run_preserves_outside _ m s w (fun hm => ho (List.mem_toFinset.mp (hs.2 hm)))

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/SquareSubSpec.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

private theorem reduce_values_congr (R : SquareReduceLayout) (lo hi v q : Nat) (b f : Bool)
    (s t : BasisState) (h : SquareReduceValues R lo hi v q b f s)
    (he : ∀ w,w∈R.wires→t w=s w) : SquareReduceValues R lo hi v q b f t := by
  have re (r : List Wire) (hr : r⊆R.wires) : regValue r t=regValue r s :=
    regValue_congr _ _ _ (fun w hw=>he w (hr hw))
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (re _ (by intro w hw; simp [SquareReduceLayout.wires,hw])).trans h.low
  · exact (re _ (by intro w hw; simp [SquareReduceLayout.wires,hw])).trans h.high
  · exact (re _ (by intro w hw; have hm:=List.mem_of_mem_take hw; simp [SquareReduceLayout.wires,hm])).trans h.value
  · exact (re _ (by intro w hw; have hm:=List.mem_of_mem_drop hw; simp [SquareReduceLayout.wires,hm])).trans h.quotient
  · exact (re _ (by intro w hw; simp [SquareReduceLayout.wires,hw])).trans h.pad
  · exact (re _ (by intro w hw; simp [SquareReduceLayout.wires,hw])).trans h.mask
  · exact (re _ (by intro w hw; simp [SquareReduceLayout.wires,hw])).trans h.carry
  · exact (he _ (by simp [SquareReduceLayout.wires])).trans h.cin
  · exact (he _ (by simp [SquareReduceLayout.wires])).trans h.bit
  · exact (he _ (by simp [SquareReduceLayout.wires])).trans h.flag

private theorem reduce_strong_frame (R : SquareReduceLayout) (_hw : R.Widths)
    (lo hi v q v' q' : Nat) (b f b' f' : Bool) (s t : BasisState)
    (hs : SquareReduceValues R lo hi v q b f s)
    (ht : SquareReduceValues R lo hi v' q' b' f' t)
    (ho : ∀ w,w∉R.wires→t w=s w) :
    ∀ w,w∉R.r++[R.b,R.flag]→t w=s w := by
  intro w hw'
  have eqv (r : List Wire) (he : regValue r t=regValue r s) (hm : w∈r) : t w=s w :=
    (regValue_eq_iff r t s).mp he w hm
  by_cases hl : w∈R.low
  · exact eqv _ (ht.low.trans hs.low.symm) hl
  by_cases hh : w∈R.high
  · exact eqv _ (ht.high.trans hs.high.symm) hh
  by_cases hp : w∈R.pad
  · exact eqv _ (ht.pad.trans hs.pad.symm) hp
  by_cases hm : w∈R.mask
  · exact eqv _ (ht.mask.trans hs.mask.symm) hm
  by_cases hk : w∈R.carry
  · exact eqv _ (ht.carry.trans hs.carry.symm) hk
  by_cases hc : w=R.cin
  · subst w; exact ht.cin.trans hs.cin.symm
  apply ho
  simpa only [SquareReduceLayout.wires,List.mem_append,List.mem_cons,List.not_mem_nil,
    hl,hh,hp,hm,hk,hc,false_or,or_false] using hw'

private theorem count_disjoint (L : SquareSubLayout) (hn : L.wires.Nodup)
    (a b : List Wire) (hc : ∀w,a.count w+b.count w≤L.wires.count w) : List.Disjoint a b := by
  apply List.disjoint_left.mpr
  intro w ha hb
  have hh:=List.nodup_iff_count.mp hn w
  have h1:=List.count_pos_iff.mpr ha
  have h2:=List.count_pos_iff.mpr hb
  have h3:=hc w
  omega

private theorem out_reduction_disjoint (L : SquareSubLayout) (hn : L.wires.Nodup) :
    List.Disjoint L.out L.reduction.wires := by
  apply count_disjoint L hn
  intro w
  have hz:=congrArg (List.count w) (List.take_append_drop 256 L.z)
  simp only [SquareSubLayout.reduction,SquareReduceLayout.wires,SquareSubLayout.wires,
    SquareSubLayout.work,List.count_append,List.count_cons,List.count_nil] at hz ⊢
  omega

/-- The output update restores its extended high bit as well as all arithmetic work. -/
theorem squareSub_output_frame (L : SquareSubLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (A O : Nat)
    (ha : regValue (L.r.take 256) base=A) (hs : base L.sourceHigh=false)
    (hh : base L.outputHigh=false) (hz : regValue L.output.work base=0)
    (hA : A≤SquareReduction.p) (hO : O<SquareReduction.p) :
    Triple (SquareFrame L.out base O) (modSubInPlace L.output SquareReduction.p)
      (SquareFrame L.out base ((O+SquareReduction.p-A)%SquareReduction.p)) := by
  have hp : 0<SquareReduction.p := by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hpn : SquareReduction.p<2^256 := by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have ds : List.Disjoint L.output.a L.out := by
    apply count_disjoint L hn; intro w
    have hc:=(List.take_sublist 256 L.r).count_le w
    simp only [SquareSubLayout.output,SquareSubLayout.wires,SquareSubLayout.work,
      List.count_append,List.count_cons,List.count_nil]; omega
  have dw : List.Disjoint L.output.work L.out := by
    apply count_disjoint L hn; intro w
    have hc:=(List.take_sublist 256 L.carry).count_le w
    simp only [SquareSubLayout.output,ModInPlaceLayout.work,ModAddCoreLayout.work,
      SquareSubLayout.wires,SquareSubLayout.work,List.count_append,List.count_cons,List.count_nil]; omega
  have dh : L.outputHigh∉L.out := by
    intro ho
    have hh:=List.nodup_iff_count.mp hn L.outputHigh
    have hc:=List.count_pos_iff.mpr ho
    simp only [SquareSubLayout.wires,SquareSubLayout.work,List.count_append,List.count_cons,List.count_nil] at hh
    simp only [beq_self_eq_true,ite_true] at hh
    omega
  intro s m h
  have sa : regValue L.output.a s.basis=A := by
    rw [regValue_congr _ _ _ (fun w hw=>h.2 w (fun ho=>List.disjoint_left.mp ds hw ho))]
    change regValue (L.r.take 256++[L.sourceHigh]) base=A
    rw [regValue_append,ha]
    have hb : regValue [L.sourceHigh] base=0 := by simp [regValue,hs]
    simp only [hb,Nat.mul_zero,Nat.add_zero]
  have sh : s.basis L.outputHigh=false := (h.2 _ dh).trans hh
  have sz : regValue L.output.z s.basis=O := by
    change regValue (L.out++[L.outputHigh]) s.basis=O
    rw [regValue_append,h.1]
    have hb : regValue [L.outputHigh] s.basis=0 := by simp [regValue,sh]
    simp only [hb,Nat.mul_zero,Nat.add_zero]
  have sw : regValue L.output.work s.basis=0 :=
    (regValue_congr _ _ _ (fun w hw=>h.2 w (fun ho=>List.disjoint_left.mp dw hw ho))).trans hz
  have hr:=modSubInPlace_spec L.output 256 SquareReduction.p A O
    (L.output_widths hw) (L.output_nodup hn) hp hpn hA hO s m ⟨⟨sa,sz⟩,sw⟩
  have hv:=hr.2.1.2
  change regValue L.output.z (run (modSubInPlace L.output SquareReduction.p) m s).basis=
    (O+SquareReduction.p-A)%SquareReduction.p at hv
  have hb : (O+SquareReduction.p-A)%SquareReduction.p<2^256 :=
    (Nat.mod_lt _ hp).trans hpn
  change regValue (L.out++[L.outputHigh]) _=_ at hv
  rw [regValue_append,hw.out] at hv
  have one : regValue [L.outputHigh] (run (modSubInPlace L.output SquareReduction.p) m s).basis=
      if (run (modSubInPlace L.output SquareReduction.p) m s).basis L.outputHigh then 1 else 0 := by
    simp [regValue]
  rw [one] at hv
  have hf : (run (modSubInPlace L.output SquareReduction.p) m s).basis L.outputHigh=false := by
    cases he : (run (modSubInPlace L.output SquareReduction.p) m s).basis L.outputHigh <;> (simp [he] at hv ⊢; try omega)
  refine ⟨hr.1,?_,?_⟩
  · simpa [hf] using hv
  · intro w ho
    by_cases he : w=L.outputHigh
    · subst w; exact hf.trans hh.symm
    apply Eq.trans _ (h.2 w ho)
    apply modSubInPlace_frame L.output 256 SquareReduction.p A O
      (L.output_widths hw) (L.output_nodup hn) hp hpn hA hO s m sa sz sw
    simpa [ModInPlaceLayout.z,ModAddCoreLayout.z,SquareSubLayout.output] using And.intro ho he


private def reduceDirty (L : SquareSubLayout) := L.r++[L.b,L.flag]
private def outputClean (L : SquareSubLayout) := L.output.work++[L.sourceHigh,L.outputHigh]
private def ReduceStage (L : SquareSubLayout) (P : BasisState→Prop) (base : BasisState)
    (O : Nat) (s : BasisState) :=
  P s ∧ regValue L.out s=O ∧ ∀ w,w∉L.out++reduceDirty L→s w=base w

private theorem outputClean_disjoint (L : SquareSubLayout) (hn : L.wires.Nodup) :
    List.Disjoint (outputClean L) (L.out++reduceDirty L) := by
  apply count_disjoint L hn; intro w
  have hc:=(List.take_sublist 256 L.carry).count_le w
  simp only [outputClean,reduceDirty,SquareSubLayout.output,ModInPlaceLayout.work,ModAddCoreLayout.work,
    SquareSubLayout.wires,SquareSubLayout.work,List.count_append,List.count_cons,List.count_nil]
  omega

private theorem reduceDirty_zero (L : SquareSubLayout) (hw : L.Widths) (lo hi : Nat)
    (s : BasisState) (h : SquareReduceValues L.reduction lo hi 0 0 false false s) :
    regValue (reduceDirty L) s=0 := by
  have hr := h.r_read (L.reduction_widths hw)
  have rb : regValue L.r s=0 := by simpa [SquareSubLayout.reduction] using hr
  change regValue (L.r++[L.b,L.flag]) s=0
  rw [regValue_append,rb]
  have hb : s L.b=false := h.bit
  have hf : s L.flag=false := h.flag
  simp [regValue,hb,hf]

/-- Reduction history survives the output update and is then completely restored. -/
theorem squareSub_middle (L : SquareSubLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (lo hi O : Nat)
    (hc : SquareReduceValues L.reduction lo hi 0 0 false false base)
    (hz : regValue (outputClean L) base=0) (hO : O<SquareReduction.p) :
    Triple (SquareFrame L.out base O)
      (squareReduce L.reduction ++ modSubInPlace L.output SquareReduction.p ++ squareReduceClear L.reduction)
      (SquareFrame L.out base ((O+SquareReduction.p-(lo+SquareReduction.B*hi)%SquareReduction.p)%SquareReduction.p)) := by
  let R := L.reduction
  let A := (lo+SquareReduction.B*hi)%SquareReduction.p
  let O' := (O+SquareReduction.p-A)%SquareReduction.p
  have wr := L.reduction_widths hw
  have nr := L.reduction_nodup hn
  have dis := out_reduction_disjoint L hn
  have hlo : lo<SquareReduction.B := by
    have hh:=regValue_lt R.low base
    rw [hc.low,wr.low] at hh; exact hh
  have hhi : hi<SquareReduction.B := by
    have hh:=regValue_lt R.high base
    rw [hc.high,wr.high] at hh; exact hh
  have sp:=squareReduce_correct R wr nr lo hi hlo hhi
  have hp : 0<SquareReduction.p := by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have dn : ∀w,w∈L.out→w∉R.r++[R.b,R.flag] := by
    intro w ho hd
    apply List.disjoint_left.mp dis ho
    simpa only [R,SquareSubLayout.reduction] using
      (show w∈L.reduction.wires from by
        simp only [SquareReduceLayout.wires,List.mem_append,List.mem_cons,List.not_mem_nil] at hd ⊢
        tauto)
  have first : Triple (SquareFrame L.out base O) (squareReduce R)
      (ReduceStage L (SquareReduced R lo hi) base O) := by
    intro s m hs
    have pre:=reduce_values_congr R lo hi 0 0 false false base s.basis hc
      (fun w hw=>hs.2 w (fun ho=>List.disjoint_left.mp dis ho hw))
    have sr:=sp.1 s m pre
    have fr:=reduce_strong_frame R wr _ _ _ _ _ _ _ _ _ _ s.basis _ pre sr.2
      (fun w hw=>(squareReduce_frame R wr m s w hw).1)
    refine ⟨sr.1,sr.2,?_,?_⟩
    · exact (regValue_congr _ _ _ (fun w hw=>fr w (dn w hw))).trans hs.1
    · intro w hw'
      simp only [List.mem_append,not_or] at hw'
      exact (fr w hw'.2).trans (hs.2 w hw'.1)
  have second : Triple (ReduceStage L (SquareReduced R lo hi) base O)
      (modSubInPlace L.output SquareReduction.p)
      (ReduceStage L (SquareReduced R lo hi) base O') := by
    intro s m hs
    have clean : regValue (outputClean L) s.basis=0 :=
      (regValue_congr _ _ _ (fun w hw=>hs.2.2 w
        (fun hd=>List.disjoint_left.mp (outputClean_disjoint L hn) hw hd))).trans hz
    have cw := (regValue_zero _ _).mp clean
    have hwork : regValue L.output.work s.basis=0 :=
      (regValue_zero _ _).mpr (fun w hw=>cw w (by simp [outputClean,hw]))
    have sbit : s.basis L.sourceHigh=false := cw _ (by simp [outputClean])
    have obit : s.basis L.outputHigh=false := cw _ (by simp [outputClean])
    have ha : regValue (L.r.take 256) s.basis=A := hs.1.value
    have op:=squareSub_output_frame L hw hn s.basis A O ha sbit obit hwork
      (Nat.le_of_lt (Nat.mod_lt _ hp)) hO s m ⟨hs.2.1,fun _ _=>rfl⟩
    refine ⟨op.1,?_,op.2.1,?_⟩
    · exact reduce_values_congr R _ _ _ _ _ _ s.basis _ hs.1
        (fun w hw=>op.2.2 w (fun ho=>List.disjoint_left.mp dis ho hw))
    · intro w hw'
      have ho : w∉L.out := fun ho=>hw' (by simp [ho])
      exact (op.2.2 w ho).trans (hs.2.2 w hw')
  have third : Triple (ReduceStage L (SquareReduced R lo hi) base O')
      (squareReduceClear R) (SquareFrame L.out base O') := by
    intro s m hs
    have sr:=sp.2 s m hs.1
    have fr:=reduce_strong_frame R wr _ _ _ _ _ _ _ _ _ _ s.basis _ hs.1 sr.2
      (fun w hw=>(squareReduce_frame R wr m s w hw).2)
    refine ⟨sr.1,?_,?_⟩
    · exact (regValue_congr _ _ _ (fun w hw=>fr w (dn w hw))).trans hs.2.1
    · intro w ho
      by_cases hd : w∈reduceDirty L
      · have hf:=reduceDirty_zero L hw lo hi _ sr.2
        have hb:=reduceDirty_zero L hw lo hi _ hc
        exact ((regValue_eq_iff _ _ _).mp (hf.trans hb.symm)) w hd
      · exact (fr w hd).trans (hs.2.2 w (by simp [ho,hd]))
  exact (first.seq second).seq third


private def integerDirty (L : SquareSubLayout) := L.a++L.d++L.z
private def integerClean (L : SquareSubLayout) := L.r++L.mask++L.carry++[L.cin]++L.pad++
  [L.b,L.flag,L.sourceHigh,L.outputHigh,L.constantHigh,L.maskHigh,L.layoutFlag,L.sumHigh]

private theorem integerClean_sub (L : SquareSubLayout) : integerClean L⊆L.work := by
  intro w hw
  simp only [integerClean,SquareSubLayout.work,List.mem_append,List.mem_cons,List.not_mem_nil] at hw ⊢
  tauto

private theorem outputClean_sub (L : SquareSubLayout) : outputClean L⊆integerClean L := by
  intro w hw
  have hc : w∈L.carry.take 256→w∈L.carry := fun hh=>List.mem_of_mem_take hh
  simp only [outputClean,SquareSubLayout.output,ModInPlaceLayout.work,ModAddCoreLayout.work,
    integerClean,List.mem_append,List.mem_cons,List.not_mem_nil] at hw ⊢
  tauto

private theorem integerClean_disjoint (L : SquareSubLayout) (hn : L.wires.Nodup) :
    List.Disjoint (integerClean L) (L.out++integerDirty L) := by
  apply count_disjoint L hn; intro w
  simp only [integerClean,integerDirty,SquareSubLayout.work,SquareSubLayout.wires,
    List.count_append,List.count_cons,List.count_nil]
  omega

private theorem out_integer_disjoint (L : SquareSubLayout) (hn : L.wires.Nodup) :
    List.Disjoint L.out L.integer.wires := by
  apply count_disjoint L hn; intro w
  have hx:=congrArg (List.count w) (List.take_append_drop 128 L.x)
  have hp:=congrArg (List.count w) (List.take_append_drop 128 L.pad)
  have hr:=(List.take_sublist 258 L.r).count_le w
  simp only [SquareSubLayout.integer,KaratsubaSquareLayout.wires,SquareSubLayout.work,
    SquareSubLayout.wires,List.count_append,List.count_cons,List.count_nil] at hx hp ⊢
  omega

private theorem integer_values_congr (K : KaratsubaSquareLayout) (lo hi av dv cv zv sv : Nat)
    (s t : BasisState) (hs : KaratsubaValues K lo hi av dv cv zv sv s)
    (he : ∀ w,w∈K.wires→t w=s w) : KaratsubaValues K lo hi av dv cv zv sv t := by
  have re (r : List Wire) (hr : r⊆K.wires) : regValue r t=regValue r s :=
    regValue_congr _ _ _ (fun w hw=>he w (hr hw))
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (re _ (by intro w hw; simp [KaratsubaSquareLayout.wires,hw])).trans hs.low
  · exact (re _ (by intro w hw; simp [KaratsubaSquareLayout.wires,hw])).trans hs.high
  · exact (re _ (by intro w hw; simp [KaratsubaSquareLayout.wires,hw])).trans hs.a
  · exact (re _ (by intro w hw; simp [KaratsubaSquareLayout.wires,hw])).trans hs.d
  · exact (re _ (by intro w hw; simp [KaratsubaSquareLayout.wires,hw])).trans hs.c
  · exact (re _ (by intro w hw; simp [KaratsubaSquareLayout.wires,hw])).trans hs.z
  · exact (re _ (by intro w hw; simp [KaratsubaSquareLayout.wires,hw])).trans hs.sum
  · exact (re _ (by intro w hw; simp [KaratsubaSquareLayout.wires,hw])).trans hs.pad
  · exact (re _ (by intro w hw; simp [KaratsubaSquareLayout.wires,hw])).trans hs.mask
  · exact (re _ (by intro w hw; simp [KaratsubaSquareLayout.wires,hw])).trans hs.carry
  · exact (he _ (by simp [KaratsubaSquareLayout.wires])).trans hs.cin

private theorem integer_initial (L : SquareSubLayout) (base : BasisState)
    (hz : regValue L.work base=0) :
    KaratsubaValues L.integer (regValue (L.x.take 128) base) (regValue (L.x.drop 128) base)
      0 0 0 0 0 base := by
  have zero (r : List Wire) (hr : r⊆L.work) : regValue r base=0 :=
    (regValue_zero _ _).mpr (fun w hw=>(regValue_zero _ _).mp hz w (hr hw))
  refine ⟨rfl,rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact zero _ (by intro w hw; simp [SquareSubLayout.integer,SquareSubLayout.work] at hw ⊢; tauto)
  · exact zero _ (by intro w hw; simp [SquareSubLayout.integer,SquareSubLayout.work] at hw ⊢; tauto)
  · apply zero; intro w hw
    have hr : w∈L.r := List.mem_of_mem_take hw
    simp [SquareSubLayout.work,hr]
  · exact zero _ (by intro w hw; simp [SquareSubLayout.integer,SquareSubLayout.work] at hw ⊢; tauto)
  · apply zero; intro w hw
    change w∈L.pad.drop 128++[L.sumHigh] at hw
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with hw | hw
    · have hp:=List.mem_of_mem_drop hw; simp [SquareSubLayout.work,hp]
    · simp [SquareSubLayout.work,hw]
  · apply zero; intro w hw
    have hp : w∈L.pad := List.mem_of_mem_take hw
    simp [SquareSubLayout.work,hp]
  · exact zero _ (by intro w hw; simp [SquareSubLayout.integer,SquareSubLayout.work] at hw ⊢; tauto)
  · exact zero _ (by intro w hw; simp [SquareSubLayout.integer,SquareSubLayout.work] at hw ⊢; tauto)
  · exact (regValue_zero _ _).mp hz _ (by simp [SquareSubLayout.work,SquareSubLayout.integer])

private theorem reduction_initial (L : SquareSubLayout) (s : BasisState)
    (hz : regValue (integerClean L) s=0) :
    SquareReduceValues L.reduction (regValue (L.z.take 256) s) (regValue (L.z.drop 256) s)
      0 0 false false s := by
  have zero (r : List Wire) (hr : r⊆integerClean L) : regValue r s=0 :=
    (regValue_zero _ _).mpr (fun w hw=>(regValue_zero _ _).mp hz w (hr hw))
  refine ⟨rfl,rfl,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · apply zero; intro w hw
    have hr : w∈L.r := List.mem_of_mem_take hw
    simp [integerClean,hr]
  · apply zero; intro w hw
    have hr : w∈L.r := List.mem_of_mem_drop hw
    simp [integerClean,hr]
  · exact zero _ (by intro w hw; simp [SquareSubLayout.reduction,integerClean] at hw ⊢; tauto)
  · exact zero _ (by intro w hw; simp [SquareSubLayout.reduction,integerClean] at hw ⊢; tauto)
  · exact zero _ (by intro w hw; simp [SquareSubLayout.reduction,integerClean] at hw ⊢; tauto)
  · exact (regValue_zero _ _).mp hz _ (by simp [SquareSubLayout.reduction,integerClean])
  · exact (regValue_zero _ _).mp hz _ (by simp [SquareSubLayout.reduction,integerClean])
  · exact (regValue_zero _ _).mp hz _ (by simp [SquareSubLayout.reduction,integerClean])

private def IntegerStage (L : SquareSubLayout) (P : BasisState→Prop) (base : BasisState)
    (O : Nat) (s : BasisState) :=
  P s ∧ regValue L.out s=O ∧ ∀ w,w∉L.out++integerDirty L→s w=base w

/-- Full square-subtract correctness with an explicit target-only frame. -/
theorem squareSub_correct (L : SquareSubLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (X O : Nat) (hx : regValue L.x base=X)
    (hz : regValue L.work base=0) (hO : O<SquareReduction.p) :
    Triple (SquareFrame L.out base O) (squareSub L)
      (SquareFrame L.out base ((O+SquareReduction.p-X^2%SquareReduction.p)%SquareReduction.p)) := by
  let lo:=regValue (L.x.take 128) base
  let hi:=regValue (L.x.drop 128) base
  let K:=L.integer
  let O':=(O+SquareReduction.p-X^2%SquareReduction.p)%SquareReduction.p
  have wk:=L.integer_valid hw hn
  have dis:=out_integer_disjoint L hn
  have pre:=integer_initial L base hz
  have xsum : lo+2^128*hi=X := by
    have he:=regValue_append (L.x.take 128) (L.x.drop 128) base
    rw [List.take_append_drop,hx,List.length_take,hw.x] at he
    simpa only [Nat.min_eq_left (by decide : 128≤256)] using he.symm
  have dn : ∀w,w∈L.out→w∉integerDirty L := by
    intro w ho hd
    apply List.disjoint_left.mp dis ho
    simp only [integerDirty,List.mem_append] at hd
    simp only [SquareSubLayout.integer,KaratsubaSquareLayout.wires,List.mem_cons,List.mem_append]
    tauto
  have first : Triple (SquareFrame L.out base O) (karatsubaSquare K)
      (IntegerStage L (KaratsubaValues K lo hi (lo^2) (hi^2) 0 (X^2) 0) base O) := by
    intro s m hs
    have ps:=integer_values_congr K lo hi 0 0 0 0 0 base s.basis pre
      (fun w hw=>hs.2 w (fun ho=>List.disjoint_left.mp dis ho hw))
    have sp:=karatsubaSquare_spec K wk lo hi s m ps
    rw [xsum] at sp
    have fr:=karatsubaSquare_frame K wk lo hi s m ps
    refine ⟨sp.1,sp.2,?_,?_⟩
    · exact (regValue_congr _ _ _ (fun w hw=>fr w (dn w hw))).trans hs.1
    · intro w hw'
      simp only [List.mem_append,not_or] at hw'
      exact (fr w hw'.2).trans (hs.2 w hw'.1)
  have middle : Triple
      (IntegerStage L (KaratsubaValues K lo hi (lo^2) (hi^2) 0 (X^2) 0) base O)
      (squareReduce L.reduction ++ modSubInPlace L.output SquareReduction.p ++ squareReduceClear L.reduction)
      (IntegerStage L (KaratsubaValues K lo hi (lo^2) (hi^2) 0 (X^2) 0) base O') := by
    intro s m hs
    have cz : regValue (integerClean L) s.basis=0 := by
      apply (regValue_zero _ _).mpr; intro w hw'
      rw [hs.2.2 w (fun hm=>List.disjoint_left.mp (integerClean_disjoint L hn) hw' hm)]
      exact (regValue_zero _ _).mp hz w (integerClean_sub L hw')
    have oz : regValue (outputClean L) s.basis=0 :=
      (regValue_zero _ _).mpr (fun w hw'=>(regValue_zero _ _).mp cz w (outputClean_sub L hw'))
    have rp:=reduction_initial L s.basis cz
    have sp:=squareSub_middle L hw hn s.basis _ _ O rp oz hO s m ⟨hs.2.1,fun _ _=>rfl⟩
    have zsum : regValue (L.z.take 256) s.basis+SquareReduction.B*regValue (L.z.drop 256) s.basis=X^2 := by
      have he:=regValue_append (L.z.take 256) (L.z.drop 256) s.basis
      rw [List.take_append_drop,List.length_take,hw.z] at he
      have hv : regValue L.z s.basis=X^2 := hs.1.z
      rw [hv] at he
      simpa only [Nat.min_eq_left (by decide : 256≤512),SquareReduction.B] using he.symm
    rw [zsum] at sp
    refine ⟨sp.1,?_,sp.2.1,?_⟩
    · exact integer_values_congr K _ _ _ _ _ _ _ s.basis _ hs.1
        (fun w hw=>sp.2.2 w (fun ho=>List.disjoint_left.mp dis ho hw))
    · intro w hw'
      exact (sp.2.2 w (fun ho=>hw' (by simp [ho]))).trans (hs.2.2 w hw')
  have last : Triple
      (IntegerStage L (KaratsubaValues K lo hi (lo^2) (hi^2) 0 (X^2) 0) base O')
      (karatsubaSquareClear K) (SquareFrame L.out base O') := by
    intro s m hs
    have ps : KaratsubaValues K lo hi (lo^2) (hi^2) 0 ((lo+2^128*hi)^2) 0 s.basis := by
      simpa only [xsum] using hs.1
    have sp:=karatsubaSquareClear_spec K wk lo hi s m ps
    have fr:=karatsubaSquareClear_frame K wk lo hi s m ps
    refine ⟨sp.1,?_,?_⟩
    · exact (regValue_congr _ _ _ (fun w hw=>fr w (dn w hw))).trans hs.2.1
    · intro w ho
      by_cases hd : w∈integerDirty L
      · have dz : regValue (integerDirty L) (run (karatsubaSquareClear K) m s).basis=0 := by
          simp only [integerDirty,regValue_append]
          have ha : regValue L.a (run (karatsubaSquareClear K) m s).basis=0 := sp.2.a
          have hd : regValue L.d (run (karatsubaSquareClear K) m s).basis=0 := sp.2.d
          have hz : regValue L.z (run (karatsubaSquareClear K) m s).basis=0 := sp.2.z
          simp only [ha,hd,hz,Nat.mul_zero,Nat.add_zero]
        have hb : base w=false := (regValue_zero _ _).mp hz w (by
          simp only [integerDirty,List.mem_append] at hd
          simp only [SquareSubLayout.work,List.mem_append]; tauto)
        exact ((regValue_zero _ _).mp dz w hd).trans hb.symm
      · exact (fr w hd).trans (hs.2.2 w (by simp [ho,hd]))
  simpa only [squareSub,List.append_assoc] using (first.seq middle).seq last


/-- Any 256-bit input may be squared; only the subtracted-from output must be canonical. -/
theorem squareSub_spec (L : SquareSubLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X O : Nat) (hO : O<SquareReduction.p) :
    (Triple (fun st => (Holds.holds st L.x X ∧ Holds.holds st L.out O) ∧ Holds.holds st L.work 0) (squareSub L)
      (fun st => (Holds.holds st L.x X ∧ Holds.holds st L.out ((O+SquareReduction.p-X^2%SquareReduction.p)%SquareReduction.p)) ∧ Holds.holds st L.work 0)) := by
  intro s m hs
  have sp:=squareSub_correct L hw hn s.basis X O hs.1.1 hs.2 hO s m
    ⟨hs.1.2,fun _ _=>rfl⟩
  have dx : List.Disjoint L.x L.out := by
    apply count_disjoint L hn; intro w
    simp only [SquareSubLayout.wires,List.count_append]; omega
  have dw : List.Disjoint L.work L.out := by
    apply count_disjoint L hn; intro w
    simp only [SquareSubLayout.wires,List.count_append]; omega
  refine ⟨sp.1,⟨?_,sp.2.1⟩,?_⟩
  · exact (regValue_congr _ _ _ (fun w hw=>sp.2.2 w
      (fun ho=>List.disjoint_left.mp dx hw ho))).trans hs.1.1
  · exact (regValue_congr _ _ _ (fun w hw=>sp.2.2 w
      (fun ho=>List.disjoint_left.mp dw hw ho))).trans hs.2

/-- Target-only frame, including the aliased padding, retained reduction history and all extra bits. -/
theorem squareSub_frame (L : SquareSubLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X O : Nat) (hO : O<SquareReduction.p) (s : State) (m : List Bool)
    (hx : regValue L.x s.basis=X) (ho : regValue L.out s.basis=O)
    (hz : regValue L.work s.basis=0) (w : Wire) (hwout : w∉L.out) :
    (run (squareSub L) m s).basis w=s.basis w :=
  (squareSub_correct L hw hn s.basis X O hx hz hO s m ⟨ho,fun _ _=>rfl⟩).2.2 w hwout

/-- Full exact signed-row square-subtract correctness with an explicit target-only frame. -/
theorem signedSquareSub_correct (L : SquareSubLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (X O : Nat) (hx : regValue L.x base=X)
    (hz : regValue L.work base=0) (hO : O<SquareReduction.p) :
    Triple (SquareFrame L.out base O) (signedSquareSub L)
      (SquareFrame L.out base ((O+SquareReduction.p-X^2%SquareReduction.p)%SquareReduction.p)) := by
  let lo:=regValue (L.x.take 128) base
  let hi:=regValue (L.x.drop 128) base
  let K:=L.integer
  let O':=(O+SquareReduction.p-X^2%SquareReduction.p)%SquareReduction.p
  have wk:=L.integer_valid hw hn
  have dis:=out_integer_disjoint L hn
  have pre:=integer_initial L base hz
  have xsum : lo+2^128*hi=X := by
    have he:=regValue_append (L.x.take 128) (L.x.drop 128) base
    rw [List.take_append_drop,hx,List.length_take,hw.x] at he
    simpa only [Nat.min_eq_left (by decide : 128≤256)] using he.symm
  have dn : ∀w,w∈L.out→w∉integerDirty L := by
    intro w ho hd
    apply List.disjoint_left.mp dis ho
    simp only [integerDirty,List.mem_append] at hd
    simp only [SquareSubLayout.integer,KaratsubaSquareLayout.wires,List.mem_cons,List.mem_append]
    tauto
  have first : Triple (SquareFrame L.out base O) (signedKaratsubaSquare K)
      (IntegerStage L (KaratsubaValues K lo hi (lo^2) (hi^2) 0 (X^2) 0) base O) := by
    intro s m hs
    have ps:=integer_values_congr K lo hi 0 0 0 0 0 base s.basis pre
      (fun w hw=>hs.2 w (fun ho=>List.disjoint_left.mp dis ho hw))
    have sp:=signedKaratsubaSquare_spec K wk lo hi s m ps
    rw [xsum] at sp
    have fr:=signedKaratsubaSquare_frame K wk lo hi s m ps
    refine ⟨sp.1,sp.2,?_,?_⟩
    · exact (regValue_congr _ _ _ (fun w hw=>fr w (dn w hw))).trans hs.1
    · intro w hw'
      simp only [List.mem_append,not_or] at hw'
      exact (fr w hw'.2).trans (hs.2 w hw'.1)
  have middle : Triple
      (IntegerStage L (KaratsubaValues K lo hi (lo^2) (hi^2) 0 (X^2) 0) base O)
      (squareReduce L.reduction ++ modSubInPlace L.output SquareReduction.p ++ squareReduceClear L.reduction)
      (IntegerStage L (KaratsubaValues K lo hi (lo^2) (hi^2) 0 (X^2) 0) base O') := by
    intro s m hs
    have cz : regValue (integerClean L) s.basis=0 := by
      apply (regValue_zero _ _).mpr; intro w hw'
      rw [hs.2.2 w (fun hm=>List.disjoint_left.mp (integerClean_disjoint L hn) hw' hm)]
      exact (regValue_zero _ _).mp hz w (integerClean_sub L hw')
    have oz : regValue (outputClean L) s.basis=0 :=
      (regValue_zero _ _).mpr (fun w hw'=>(regValue_zero _ _).mp cz w (outputClean_sub L hw'))
    have rp:=reduction_initial L s.basis cz
    have sp:=squareSub_middle L hw hn s.basis _ _ O rp oz hO s m ⟨hs.2.1,fun _ _=>rfl⟩
    have zsum : regValue (L.z.take 256) s.basis+SquareReduction.B*regValue (L.z.drop 256) s.basis=X^2 := by
      have he:=regValue_append (L.z.take 256) (L.z.drop 256) s.basis
      rw [List.take_append_drop,List.length_take,hw.z] at he
      have hv : regValue L.z s.basis=X^2 := hs.1.z
      rw [hv] at he
      simpa only [Nat.min_eq_left (by decide : 256≤512),SquareReduction.B] using he.symm
    rw [zsum] at sp
    refine ⟨sp.1,?_,sp.2.1,?_⟩
    · exact integer_values_congr K _ _ _ _ _ _ _ s.basis _ hs.1
        (fun w hw=>sp.2.2 w (fun ho=>List.disjoint_left.mp dis ho hw))
    · intro w hw'
      exact (sp.2.2 w (fun ho=>hw' (by simp [ho]))).trans (hs.2.2 w hw')
  have last : Triple
      (IntegerStage L (KaratsubaValues K lo hi (lo^2) (hi^2) 0 (X^2) 0) base O')
      (signedKaratsubaSquareClear K) (SquareFrame L.out base O') := by
    intro s m hs
    have ps : KaratsubaValues K lo hi (lo^2) (hi^2) 0 ((lo+2^128*hi)^2) 0 s.basis := by
      simpa only [xsum] using hs.1
    have sp:=signedKaratsubaSquareClear_spec K wk lo hi s m ps
    have fr:=signedKaratsubaSquareClear_frame K wk lo hi s m ps
    refine ⟨sp.1,?_,?_⟩
    · exact (regValue_congr _ _ _ (fun w hw=>fr w (dn w hw))).trans hs.2.1
    · intro w ho
      by_cases hd : w∈integerDirty L
      · have dz : regValue (integerDirty L) (run (signedKaratsubaSquareClear K) m s).basis=0 := by
          simp only [integerDirty,regValue_append]
          have ha : regValue L.a (run (signedKaratsubaSquareClear K) m s).basis=0 := sp.2.a
          have hd : regValue L.d (run (signedKaratsubaSquareClear K) m s).basis=0 := sp.2.d
          have hz : regValue L.z (run (signedKaratsubaSquareClear K) m s).basis=0 := sp.2.z
          simp only [ha,hd,hz,Nat.mul_zero,Nat.add_zero]
        have hb : base w=false := (regValue_zero _ _).mp hz w (by
          simp only [integerDirty,List.mem_append] at hd
          simp only [SquareSubLayout.work,List.mem_append]; tauto)
        exact ((regValue_zero _ _).mp dz w hd).trans hb.symm
      · exact (fr w hd).trans (hs.2.2 w (by simp [ho,hd]))
  simpa only [signedSquareSub,List.append_assoc] using (first.seq middle).seq last


/-- Signed-row Step 4 is exact for every 256-bit input; only the output must be canonical. -/
theorem signedSquareSub_spec (L : SquareSubLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X O : Nat) (hO : O<SquareReduction.p) :
    (Triple (fun st => (Holds.holds st L.x X ∧ Holds.holds st L.out O) ∧ Holds.holds st L.work 0) (signedSquareSub L)
      (fun st => (Holds.holds st L.x X ∧ Holds.holds st L.out ((O+SquareReduction.p-X^2%SquareReduction.p)%SquareReduction.p)) ∧ Holds.holds st L.work 0)) := by
  intro s m hs
  have sp:=signedSquareSub_correct L hw hn s.basis X O hs.1.1 hs.2 hO s m
    ⟨hs.1.2,fun _ _=>rfl⟩
  have dx : List.Disjoint L.x L.out := by
    apply count_disjoint L hn; intro w
    simp only [SquareSubLayout.wires,List.count_append]; omega
  have dw : List.Disjoint L.work L.out := by
    apply count_disjoint L hn; intro w
    simp only [SquareSubLayout.wires,List.count_append]; omega
  refine ⟨sp.1,⟨?_,sp.2.1⟩,?_⟩
  · exact (regValue_congr _ _ _ (fun w hw=>sp.2.2 w
      (fun ho=>List.disjoint_left.mp dx hw ho))).trans hs.1.1
  · exact (regValue_congr _ _ _ (fun w hw=>sp.2.2 w
      (fun ho=>List.disjoint_left.mp dw hw ho))).trans hs.2

/-- Target-only frame for the signed-row Step 4 implementation. -/
theorem signedSquareSub_frame (L : SquareSubLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X O : Nat) (hO : O<SquareReduction.p) (s : State) (m : List Bool)
    (hx : regValue L.x s.basis=X) (ho : regValue L.out s.basis=O)
    (hz : regValue L.work s.basis=0) (w : Wire) (hwout : w∉L.out) :
    (run (signedSquareSub L) m s).basis w=s.basis w :=
  (signedSquareSub_correct L hw hn s.basis X O hx hz hO s m ⟨ho,fun _ _=>rfl⟩).2.2 w hwout

theorem signedSquareSub_wires_subset (L : SquareSubLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) : wires (signedSquareSub L)⊆L.wires.toFinset := by
  have ik : L.integer.wires.toFinset⊆L.wires.toFinset := by
    intro w hm
    have h := List.count_pos_iff.mpr (List.mem_toFinset.mp hm)
    have hx := congrArg (List.count w) (List.take_append_drop 128 L.x)
    have hp := congrArg (List.count w) (List.take_append_drop 128 L.pad)
    have hr := (List.take_sublist 258 L.r).count_le w
    apply List.mem_toFinset.mpr
    apply List.count_pos_iff.mp
    simp only [SquareSubLayout.wires,SquareSubLayout.work,SquareSubLayout.integer,
      KaratsubaSquareLayout.wires,List.count_append,List.count_cons,List.count_nil] at h hx hp ⊢
    omega
  have ir : L.reduction.wires.toFinset⊆L.wires.toFinset := by
    intro w hm
    have h := List.count_pos_iff.mpr (List.mem_toFinset.mp hm)
    have hz := congrArg (List.count w) (List.take_append_drop 256 L.z)
    apply List.mem_toFinset.mpr
    apply List.count_pos_iff.mp
    simp only [SquareSubLayout.wires,SquareSubLayout.work,SquareSubLayout.reduction,
      SquareReduceLayout.wires,List.count_append,List.count_cons,List.count_nil] at h hz ⊢
    omega
  have io : L.output.toModAddCoreLayout.wires.toFinset⊆L.wires.toFinset := by
    intro w hm
    have h := List.count_pos_iff.mpr (List.mem_toFinset.mp hm)
    have hr := (List.take_sublist 256 L.r).count_le w
    have hc := (List.take_sublist 256 L.carry).count_le w
    apply List.mem_toFinset.mpr
    apply List.count_pos_iff.mp
    simp only [SquareSubLayout.wires,SquareSubLayout.work,SquareSubLayout.output,
      ModAddCoreLayout.wires,ModAddCoreLayout.z,ModAddCoreLayout.work,
      List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have hk := signedKaratsubaSquare_wires_subset L.integer (L.integer_valid hw hn)
  have hr := squareReduce_wires_subset L.reduction (L.reduction_widths hw)
  have ho : wires (modSubInPlace L.output SquareReduction.p)⊆L.wires.toFinset := by
    rw [modSubInPlace_wires L.output 256 SquareReduction.p (L.output_widths hw) (by omega)]
    exact io
  simp only [signedSquareSub,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨hk.1.trans ik,hr.1.trans ir⟩,ho⟩,hr.2.trans ir⟩,hk.2.trans ik⟩

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointInPlaceSquare.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

/-- 专用平方只改变当前 x；整个 P 与斜率输入均恢复。 -/
theorem pointInPlaceSquare_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (A X : Nat) (hX : X<p) (s : State) (m : List Bool)
    (ha : regValue L.inPlaceSlope s.basis=A) (hx : regValue L.point.x s.basis=X)
    (hc : regValue L.inPlaceBorrow s.basis=0) :
    (run (squareSub L.inPlaceKaratsuba) m s).phase=s.phase ∧
      regValue L.point.x (run (squareSub L.inPlaceKaratsuba) m s).basis=(X+p-(A*A)%p)%p ∧
      ∀q,q∉L.point.x → (run (squareSub L.inPlaceKaratsuba) m s).basis q=s.basis q := by
  have hp : SquareReduction.p=p := by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c,p]
  have ha' : regValue L.inPlaceKaratsuba.x s.basis=A := by rw [L.inPlaceKaratsuba_x hw]; exact ha
  have hx' : regValue L.inPlaceKaratsuba.out s.basis=X := hx
  have hz : regValue L.inPlaceKaratsuba.work s.basis=0 := by
    apply (regValue_zero _ _).mpr; intro q hq
    exact (regValue_zero _ _).mp hc q (L.inPlaceKaratsuba_work_subset hw hq)
  have spec := squareSub_spec L.inPlaceKaratsuba (L.inPlaceKaratsuba_widths hw)
    (L.inPlaceKaratsuba_nodup hw hn) A X (by simpa only [hp] using hX)
    s m ⟨⟨ha',hx'⟩,hz⟩
  refine ⟨spec.1,?_,?_⟩
  · simpa only [hp,pow_two] using spec.2.1.2
  · intro q hq
    exact squareSub_frame L.inPlaceKaratsuba (L.inPlaceKaratsuba_widths hw)
      (L.inPlaceKaratsuba_nodup hw hn) A X (by simpa only [hp] using hX)
      s m ha' hx' hz q hq

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointInPlaceState.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

/-- 普通分支边界的直接寄存器断言；求逆布局在这些边界完整清零。 -/
structure PointInPlaceValues (L : ControlledPointLayout) (X Y A : Fp) (G E Q : Bool)
    (s : BasisState) : Prop where
  x : regValue L.point.x s=X.val
  y : regValue L.point.y s=Y.val
  slope : regValue L.inPlaceSlope s=A.val
  generic : s L.core.generic=G
  equal : s L.core.equalX=E
  quotient : s L.core.equalNegY=Q
  clean : regValue L.inPlaceInverse.wires s=0

private theorem state_nodup (L : ControlledPointLayout) (hw : L.Widths) (hnd : L.wires.Nodup) :
    (L.point.x++L.point.y++L.inPlaceSlope++[L.core.generic,L.core.equalX,L.core.equalNegY]++L.inPlaceInverse.wires).Nodup := by
  apply List.nodup_iff_count.mpr; intro q
  have h := List.nodup_iff_count.mp (L.inPlace_interfaces_nodup hw hnd) q
  simp only [PointAddLayout.pointWires,inPlaceFlags,List.count_append,List.count_cons,List.count_nil] at h ⊢
  omega

namespace PointInPlaceValues

variable {L : ControlledPointLayout} {X X' Y Y' A A' : Fp} {G E Q : Bool} {s t : BasisState}

theorem borrow (v : PointInPlaceValues L X Y A G E Q s) : regValue L.inPlaceBorrow s=0 := by
  apply (regValue_zero _ _).mpr; intro q hq
  apply (regValue_zero _ _).mp v.clean
  have hb := L.inPlaceBorrow_count q
  have hp := List.count_pos_iff.mpr hq
  exact List.count_pos_iff.mp (by omega)

theorem withX (hw : L.Widths) (hnd : L.wires.Nodup) (v : PointInPlaceValues L X Y A G E Q s)
    (hx : regValue L.point.x t=X'.val) (hf : ∀ q∉L.point.x,t q=s q) :
    PointInPlaceValues L X' Y A G E Q t := by
  have away (q : Wire) (hq : q∈L.point.y++L.inPlaceSlope++[L.core.generic,L.core.equalX,L.core.equalNegY]++L.inPlaceInverse.wires) :
      q∉L.point.x := by
    have hn := state_nodup L hw hnd
    rw [List.append_assoc,List.append_assoc,List.append_assoc] at hn
    simp only [List.append_assoc] at hq
    exact List.disjoint_right.mp (List.nodup_append'.mp hn).2.2 hq
  refine ⟨hx,?_,?_,?_,?_,?_,?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => hf q (away q (by simp [hq])))).trans v.y
  · exact (regValue_congr _ _ _ (fun q hq => hf q (away q (by simp [hq])))).trans v.slope
  · exact (hf _ (away _ (by simp))).trans v.generic
  · exact (hf _ (away _ (by simp))).trans v.equal
  · exact (hf _ (away _ (by simp))).trans v.quotient
  · exact (regValue_congr _ _ _ (fun q hq => hf q (away q (by simp [hq])))).trans v.clean

theorem withY (hw : L.Widths) (hnd : L.wires.Nodup) (v : PointInPlaceValues L X Y A G E Q s)
    (hy : regValue L.point.y t=Y'.val) (hf : ∀ q∉L.point.y,t q=s q) :
    PointInPlaceValues L X Y' A G E Q t := by
  have away (q : Wire) (hq : q∈L.point.x++L.inPlaceSlope++[L.core.generic,L.core.equalX,L.core.equalNegY]++L.inPlaceInverse.wires) :
      q∉L.point.y := by
    intro hh
    have h := List.nodup_iff_count.mp (state_nodup L hw hnd) q
    have ha := List.count_pos_iff.mpr hq
    have hb := List.count_pos_iff.mpr hh
    simp only [List.count_append] at h ha
    omega
  refine ⟨?_,hy,?_,?_,?_,?_,?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => hf q (away q (by simp [hq])))).trans v.x
  · exact (regValue_congr _ _ _ (fun q hq => hf q (away q (by simp [hq])))).trans v.slope
  · exact (hf _ (away _ (by simp))).trans v.generic
  · exact (hf _ (away _ (by simp))).trans v.equal
  · exact (hf _ (away _ (by simp))).trans v.quotient
  · exact (regValue_congr _ _ _ (fun q hq => hf q (away q (by simp [hq])))).trans v.clean

theorem withSlope (hw : L.Widths) (hnd : L.wires.Nodup) (v : PointInPlaceValues L X Y A G E Q s)
    (ha : regValue L.inPlaceSlope t=A'.val) (hf : ∀ q∉L.inPlaceSlope,t q=s q) :
    PointInPlaceValues L X Y A' G E Q t := by
  have away (q : Wire) (hq : q∈L.point.x++L.point.y++[L.core.generic,L.core.equalX,L.core.equalNegY]++L.inPlaceInverse.wires) :
      q∉L.inPlaceSlope := by
    intro hh
    have h := List.nodup_iff_count.mp (state_nodup L hw hnd) q
    have ha := List.count_pos_iff.mpr hq
    have hb := List.count_pos_iff.mpr hh
    simp only [List.count_append] at h ha
    omega
  refine ⟨?_,?_,ha,?_,?_,?_,?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => hf q (away q (by simp [hq])))).trans v.x
  · exact (regValue_congr _ _ _ (fun q hq => hf q (away q (by simp [hq])))).trans v.y
  · exact (hf _ (away _ (by simp))).trans v.generic
  · exact (hf _ (away _ (by simp))).trans v.equal
  · exact (hf _ (away _ (by simp))).trans v.quotient
  · exact (regValue_congr _ _ _ (fun q hq => hf q (away q (by simp [hq])))).trans v.clean

theorem withEqual {E' : Bool} (hw : L.Widths) (hnd : L.wires.Nodup) (v : PointInPlaceValues L X Y A G E Q s)
    (he : t L.core.equalX=E') (hf : ∀ q,q≠L.core.equalX → t q=s q) :
    PointInPlaceValues L X Y A G E' Q t := by
  have away (q : Wire) (hq : q∈L.point.x++L.point.y++L.inPlaceSlope++[L.core.generic,L.core.equalNegY]++L.inPlaceInverse.wires) :
      q≠L.core.equalX := by
    intro heq; subst q
    have h := List.nodup_iff_count.mp (state_nodup L hw hnd) L.core.equalX
    have ha := List.count_pos_iff.mpr hq
    simp only [List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at h ha
    omega
  refine ⟨?_,?_,?_,?_,he,?_,?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => hf q (away q (by simp [hq])))).trans v.x
  · exact (regValue_congr _ _ _ (fun q hq => hf q (away q (by simp [hq])))).trans v.y
  · exact (regValue_congr _ _ _ (fun q hq => hf q (away q (by simp [hq])))).trans v.slope
  · exact (hf _ (away _ (by simp))).trans v.generic
  · exact (hf _ (away _ (by simp))).trans v.quotient
  · exact (regValue_congr _ _ _ (fun q hq => hf q (away q (by simp [hq])))).trans v.clean

theorem withQuotient {Q' : Bool} (hw : L.Widths) (hnd : L.wires.Nodup) (v : PointInPlaceValues L X Y A G E Q s)
    (he : t L.core.equalNegY=Q') (hf : ∀ q,q≠L.core.equalNegY → t q=s q) :
    PointInPlaceValues L X Y A G E Q' t := by
  have away (q : Wire) (hq : q∈L.point.x++L.point.y++L.inPlaceSlope++[L.core.generic,L.core.equalX]++L.inPlaceInverse.wires) :
      q≠L.core.equalNegY := by
    intro heq; subst q
    have h := List.nodup_iff_count.mp (state_nodup L hw hnd) L.core.equalNegY
    have ha := List.count_pos_iff.mpr hq
    simp only [List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at h ha
    omega
  refine ⟨?_,?_,?_,?_,?_,he,?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => hf q (away q (by simp [hq])))).trans v.x
  · exact (regValue_congr _ _ _ (fun q hq => hf q (away q (by simp [hq])))).trans v.y
  · exact (regValue_congr _ _ _ (fun q hq => hf q (away q (by simp [hq])))).trans v.slope
  · exact (hf _ (away _ (by simp))).trans v.generic
  · exact (hf _ (away _ (by simp))).trans v.equal
  · exact (regValue_congr _ _ _ (fun q hq => hf q (away q (by simp [hq])))).trans v.clean

end PointInPlaceValues
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointInPlaceSteps.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

private instance : NeZero p := ⟨by norm_num [p]⟩
private instance : Fact (1<p) := ⟨by norm_num [p]⟩

private theorem sub_val_PointInPlaceSteps (x y : Fp) : (x-y).val=(x.val+p-y.val)%p := by
  rw [sub_eq_add_neg,ZMod.val_add,ZMod.neg_val',Nat.add_mod_mod]
  rw [← Nat.add_sub_assoc (le_of_lt (ZMod.val_lt y))]

variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y A : Fp) (G E Q : Bool)
include hw hn

theorem pointStep_addX (k : Fp) :
    Triple (PointInPlaceValues L X Y A G E Q) (pointInPlaceConstantAdd L L.point.x k)
      (PointInPlaceValues L (X+(if G then k else 0)) Y A G E Q) := by
  intro s m v
  obtain ⟨hp,hx,hf⟩ := pointInPlaceConstantAdd_correct L hw hn L.point.x (Or.inl rfl) k X.val G X.isLt
    s m v.generic v.x v.borrow
  refine ⟨hp,v.withX hw hn ?_ hf⟩
  cases G <;> simpa [ZMod.val_add,Nat.mod_eq_of_lt (ZMod.val_lt X)] using hx

theorem pointStep_addY (k : Fp) :
    Triple (PointInPlaceValues L X Y A G E Q) (pointInPlaceConstantAdd L L.point.y k)
      (PointInPlaceValues L X (Y+(if G then k else 0)) A G E Q) := by
  intro s m v
  obtain ⟨hp,hy,hf⟩ := pointInPlaceConstantAdd_correct L hw hn L.point.y (Or.inr rfl) k Y.val G Y.isLt
    s m v.generic v.y v.borrow
  refine ⟨hp,v.withY hw hn ?_ hf⟩
  cases G <;> simpa [ZMod.val_add,Nat.mod_eq_of_lt (ZMod.val_lt Y)] using hy

theorem pointStep_product :
    Triple (PointInPlaceValues L X Y A G E Q) (montMulAdd L.inPlaceMultiply p)
      (PointInPlaceValues L X (Y+A*X) A G E Q) ∧
    Triple (PointInPlaceValues L X Y A G E Q) (montMulSub L.inPlaceMultiply p)
      (PointInPlaceValues L X (Y-A*X) A G E Q) := by
  constructor
  · intro s m v
    obtain ⟨hp,hy,hf⟩ := (pointInPlaceProduct_correct L hw hn A.val X.val Y.val A.isLt X.isLt Y.isLt
      s m v.slope v.x v.y v.borrow).1
    exact ⟨hp,v.withY hw hn (by simpa only [ZMod.val_add,ZMod.val_mul] using hy) hf⟩
  · intro s m v
    obtain ⟨hp,hy,hf⟩ := (pointInPlaceProduct_correct L hw hn A.val X.val Y.val A.isLt X.isLt Y.isLt
      s m v.slope v.x v.y v.borrow).2
    exact ⟨hp,v.withY hw hn (by simpa only [sub_val_PointInPlaceSteps,ZMod.val_mul] using hy) hf⟩

theorem pointStep_negate :
    Triple (PointInPlaceValues L X Y A G E Q) (pointInPlaceNegate L)
      (PointInPlaceValues L (if G then -X else X) Y A G E Q) := by
  intro s m v
  obtain ⟨hp,hx,hf⟩ := pointInPlaceNegate_correct L hw hn X.val G X.isLt s m v.generic v.x v.borrow
  refine ⟨hp,v.withX hw hn ?_ hf⟩
  cases G <;> simpa only [Bool.false_eq_true,if_false,if_true,ZMod.neg_val'] using hx

theorem pointStep_square :
    Triple (PointInPlaceValues L X Y A G E Q)
      (squareSub L.inPlaceKaratsuba)
      (PointInPlaceValues L (X-A*A) Y A G E Q) := by
  intro s m v
  obtain ⟨hp,hx,hf⟩ := pointInPlaceSquare_correct L hw hn A.val X.val X.isLt s m v.slope v.x v.borrow
  exact ⟨hp,v.withX hw hn (by simpa only [sub_val_PointInPlaceSteps,ZMod.val_mul] using hx) hf⟩

theorem pointStep_divideAdd (hX : G=true → X≠0) :
    Triple (PointInPlaceValues L X Y A G E Q) (divideAdd (L.inPlaceDivide L.core.generic L.point.x L.point.y))
      (PointInPlaceValues L X Y (if G then A+Y/X else A) G E Q) := by
  have hd : G=true → X.val≠0 := by
    intro hg hx
    apply hX hg
    apply ZMod.val_injective p
    simpa only [ZMod.val_zero] using hx
  intro s m v
  have hwd := L.inPlaceDivide_widths hw L.core.generic _ _ hw.inputX hw.inputY
  have hnd := L.inPlaceDivide_nodup hw hn L.core.generic (by simp [inPlaceFlags])
  obtain ⟨hp,hv⟩ := divideAdd_spec _ hwd hnd X.val Y.val A.val G X.isLt Y.isLt A.isLt hd
    s m ⟨⟨⟨⟨v.generic,v.x⟩,v.y⟩,v.slope⟩,v.clean⟩
  have hf := divide_frame _ hwd hnd X.val Y.val A.val G X.isLt Y.isLt A.isLt hd
    s m v.generic v.x v.y v.slope v.clean
  refine ⟨hp,v.withSlope hw hn ?_ (fun q hq => (hf q hq).1)⟩
  have hval := hv.1.2
  change regValue L.inPlaceSlope _ = _ at hval
  cases G <;> simpa only [Bool.false_eq_true,if_false,if_true,ZMod.val_add,div_eq_mul_inv,
    ZMod.val_mul,ZMod.natCast_zmod_val,mul_comm] using hval

theorem pointStep_divideSub (hX : Q=true → X≠0) :
    Triple (PointInPlaceValues L X Y A G E Q) (divideSub (L.inPlaceDivide L.core.equalNegY L.point.x L.point.y))
      (PointInPlaceValues L X Y (if Q then A-Y/X else A) G E Q) := by
  have hd : Q=true → X.val≠0 := by
    intro hq hx
    apply hX hq
    apply ZMod.val_injective p
    simpa only [ZMod.val_zero] using hx
  intro s m v
  have hwd := L.inPlaceDivide_widths hw L.core.equalNegY _ _ hw.inputX hw.inputY
  have hnd := L.inPlaceDivide_nodup hw hn L.core.equalNegY (by simp [inPlaceFlags])
  obtain ⟨hp,hv⟩ := divideSub_spec _ hwd hnd X.val Y.val A.val Q X.isLt Y.isLt A.isLt hd
    s m ⟨⟨⟨⟨v.quotient,v.x⟩,v.y⟩,v.slope⟩,v.clean⟩
  have hf := divide_frame _ hwd hnd X.val Y.val A.val Q X.isLt Y.isLt A.isLt hd
    s m v.quotient v.x v.y v.slope v.clean
  refine ⟨hp,v.withSlope hw hn ?_ (fun q hq => (hf q hq).2)⟩
  have hval := hv.1.2
  change regValue L.inPlaceSlope _ = _ at hval
  cases Q <;> simpa only [Bool.false_eq_true,if_false,if_true,sub_val_PointInPlaceSteps,div_eq_mul_inv,
    ZMod.val_mul,ZMod.natCast_zmod_val,mul_comm] using hval

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointInPlaceSupport.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout

/-- 普通分支的语法支持上界，仅计入实际使用的求逆核心。 -/
def pointInPlaceCoreWires (L : ControlledPointLayout) : List Wire :=
  L.point.x++L.point.y++L.inPlaceSlope++[L.core.generic,L.core.equalX,L.core.equalNegY]++L.inPlaceOuterCoreWires


theorem ControlledPointLayout.inPlaceBorrow_used_subset (L : ControlledPointLayout) :
    L.inPlaceBorrow ⊆ L.inPlaceOuterCoreWires := by
  rw [L.inPlaceBorrow_eq]
  exact L.inPlaceInverse.idleBorrow_subset


theorem modPrograms_not_mem (q c : Wire) (ng : q≠c) (M : ModInPlaceLayout) (hM : M.Widths 256) (hnM : q∉M.wires) :
      q∉wires (modAddInPlace M p) ∧ q∉wires (modSubInPlace M p) ∧
      q∉wires (controlledModAdd c M p) ∧ q∉wires (controlledModSub c M p) := by
    have hm : q∉M.maskedCore.wires := by
      simp only [ModInPlaceLayout.wires,ModInPlaceLayout.work,ModInPlaceLayout.z,
        ModAddCoreLayout.z,ModAddCoreLayout.work,List.mem_append,List.mem_cons,not_or] at hnM
      simp only [ModInPlaceLayout.maskedCore,ModAddCoreLayout.wires,ModAddCoreLayout.z,ModAddCoreLayout.work,
        List.mem_append,List.mem_cons]
      grind only
    have hc : q∉M.toModAddCoreLayout.wires := by
      simp only [ModInPlaceLayout.wires,ModInPlaceLayout.work,ModInPlaceLayout.z,
        ModAddCoreLayout.wires,List.mem_append,not_or] at hnM ⊢
      grind only
    have ha : q∉M.a := fun h => hnM (by simp [ModInPlaceLayout.wires,h])
    have hat : q∉M.a.take 256 := fun h => ha ((List.take_sublist _ _).subset h)
    rw [modAddInPlace,modAddCore_wires M.toModAddCoreLayout 256 p hM.core (by omega),
      modSubInPlace_wires M 256 p hM (by omega),controlledModAdd_wires _ M 256 p hM (by omega),
      controlledModSub_wires _ M 256 p hM (by omega)]
    simp [ng,hc,hm,ha,hat]

private theorem mont_not_mem (q : Wire) (M : MontLayout) (hw : M.Widths) (hn : q∉M.wires) :
    q∉wires (montMulAdd M p) ∧ q∉wires (montMulSub M p) := by
  have h := montAdapter_wires M p hw
  have ht : q∈M.x.take 256 → q∈M.x := fun h => List.mem_of_mem_take h
  simp only [h.2.1,h.2.2,List.mem_toFinset,List.mem_append]
  simp only [MontLayout.wires,List.mem_append] at hn
  clear h hw
  tauto

private theorem zero_not_mem (L : ControlledPointLayout) (hw : L.Widths) (q : Wire)
    (ng : q≠L.core.generic) (ne : q≠L.core.equalX) (nx : q∉L.point.x)
    (ntake : ∀ n,q∉L.inPlaceBorrow.take n) : q∉wires (equalConstant L.core.generic L.core.equalX L.inPlaceXZero 0) := by
    rw [equalConstant_wires]
    have hp := zeroPorts_perm L.point.x (L.inPlaceBorrow.take 256)
      (by rw [show L.point.x.length=256 from hw.inputX]; simp [L.inPlaceBorrow_length hw])
    have he := List.toFinset_eq_of_perm _ _ hp
    simp only [inPlaceXZero]
    rw [List.toFinset_cons,List.toFinset_cons,he]
    simp [ng,ne,nx,ntake]

private theorem divide_not_mem (L : ControlledPointLayout) (hw : L.Widths) (q : Wire)
    (nx : q∉L.point.x) (ny : q∉L.point.y) (na : q∉L.inPlaceSlope) (ni : q∉L.inPlaceOuterCoreWires)
    (c : Wire) (nc : q≠c) :
    q∉wires (divideAdd (L.inPlaceDivide c L.point.x L.point.y)) ∧
    q∉wires (divideSub (L.inPlaceDivide c L.point.x L.point.y)) := by
  have hd := divide_wires (L.inPlaceDivide c L.point.x L.point.y)
    (L.inPlaceDivide_widths hw c _ _ hw.inputX hw.inputY)
  simp only [hd.1,hd.2]
  have nn : q∉L.inPlaceInverse.compactCoreWires := fun hh => ni (L.compactCore_outer hh)
  simp [DivideLayout.usedWires,inPlaceDivide,nc,nx,ny,na,nn]

private theorem views_not_mem (L : ControlledPointLayout) (hw : L.Widths) (q : Wire)
    (hnot : q∉(pointInPlaceCoreWires L).toFinset) :
    q∉L.inPlaceBorrow ∧ q∉L.inPlaceMultiply.wires ∧
    q∉L.inPlaceNegate.wires ∧
    (∀ r : List Wire,q∉r → q∉(L.inPlaceConstant r).wires) := by
  have hn := hnot
  simp only [pointInPlaceCoreWires,List.mem_toFinset,List.mem_append,List.mem_cons,not_or] at hn
  rcases hn with ⟨⟨⟨⟨nx,ny⟩,na⟩,ng,ne,nq,_⟩,ni⟩
  have nb : q∉L.inPlaceBorrow := fun h => ni (L.inPlaceBorrow_used_subset h)
  have nslice (j n : Nat) : q∉(L.inPlaceBorrow.drop j).take n := by
    intro h; exact nb ((List.drop_sublist _ _).subset ((List.take_sublist _ _).subset h))
  have ntake (n : Nat) : q∉L.inPlaceBorrow.take n := fun h => nb ((List.take_sublist _ _).subset h)
  have nbit (j : Nat) (hj : j<2603) : q≠L.inPlaceBit j := by
    intro he
    apply nb
    rw [he,inPlaceBit,List.getD_eq_getElem _ _ (by rw [L.inPlaceBorrow_length hw]; exact hj)]
    exact List.getElem_mem _
  have nwM : q∉L.inPlaceMultiply.work := by
    intro h
    apply nb
    have hh := L.inPlaceMultiply_borrow hw
    have hp : q∈L.inPlaceBorrow.take 1829 := hh ▸ List.mem_append_right _ h
    exact List.mem_of_mem_take hp
  have nM : q∉L.inPlaceMultiply.wires := by
    change q∉(L.inPlaceSlope++[L.inPlaceBit 0])++L.point.x++(L.point.y++[L.inPlaceBit 1])++L.inPlaceMultiply.work
    simp [na,nx,ny,nwM,nbit]
  have ntail : q∉L.inPlaceBorrow.tail.take 256 := by simpa only [List.drop_one] using nslice 1 256
  have nN : q∉L.inPlaceNegate.wires := by
    simp [inPlaceNegate,ModInPlaceLayout.wires,ModInPlaceLayout.z,ModInPlaceLayout.work,
      inPlaceUnary,ModUnaryLayout.core,ModAddCoreLayout.z,ModAddCoreLayout.work,nx,nslice,ntail,nbit]
  have nConst (r : List Wire) (nr : q∉r) : q∉(L.inPlaceConstant r).wires := by
    simp [inPlaceConstant,ModInPlaceLayout.wires,ModInPlaceLayout.z,ModInPlaceLayout.work,
      inPlaceUnary,ModUnaryLayout.core,ModAddCoreLayout.z,ModAddCoreLayout.work,nr,nslice,ntake,nbit]
  exact ⟨nb,nM,nN,nConst⟩

theorem square_layout_not_mem (K : SquareSubLayout) (hw : K.Widths) (hn : K.wires.Nodup)
    (q : Wire) (nx : q∉K.x) (no : q∉K.out) (nw : q∉K.work) : q∉wires (squareSub K) := by
  intro hm
  have hs:=List.mem_toFinset.mp (squareSub_wires_subset K hw hn hm)
  simp only [SquareSubLayout.wires,List.mem_append,nx,no,nw,false_or] at hs

private theorem karatsuba_out (L : ControlledPointLayout) : L.inPlaceKaratsuba.out=L.point.x := rfl

private theorem square_not_mem (L : ControlledPointLayout) (hw : L.Widths) (hnd : L.wires.Nodup)
    (q : Wire) (na : q∉L.inPlaceSlope) (nx : q∉L.point.x) (nb : q∉L.inPlaceBorrow) :
    q∉wires (squareSub L.inPlaceKaratsuba) := by
  apply square_layout_not_mem L.inPlaceKaratsuba (L.inPlaceKaratsuba_widths hw)
    (L.inPlaceKaratsuba_nodup hw hnd) q
  · rw [L.inPlaceKaratsuba_x hw]; exact na
  · rw [karatsuba_out]; exact nx
  · exact fun hm=>nb (L.inPlaceKaratsuba_work_subset hw hm)


theorem pointInPlaceGeneric_wires_subset (L : ControlledPointLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup)
    (cx cy k : Fp) : wires (pointInPlaceGeneric L cx cy k) ⊆ (pointInPlaceCoreWires L).toFinset := by
  intro q
  contrapose!
  intro hnot
  have hn := hnot
  simp only [pointInPlaceCoreWires,List.mem_toFinset,List.mem_append,List.mem_cons,not_or] at hn
  rcases hn with ⟨⟨⟨⟨nx,ny⟩,na⟩,ng,ne,nq,_⟩,ni⟩
  obtain ⟨nb,nM,nN,nConst⟩ := views_not_mem L hw q hnot
  have ntake (n : Nat) : q∉L.inPlaceBorrow.take n := fun h => nb ((List.take_sublist _ _).subset h)
  have nDivide := divide_not_mem L hw q nx ny na ni
  have nEq := zero_not_mem L hw q ng ne nx ntake
  have nMasked (c : Wire) (r : List Wire) (v : Nat) (nc : q≠c) (nr : q∉r) : q∉wires (maskedConstant c r v) := by
    intro h
    have hh := maskedConstant_wires_subset c r v h
    simp [nc,nr] at hh
  have nCA (r : List Wire) (nr : q∉r) (hr : r.length=256) (v : Fp) : q∉wires (pointInPlaceConstantAdd L r v) := by
    have nm := nConst r nr
    have ha : q∉(L.inPlaceConstant r).a := fun h => nm (by simp [ModInPlaceLayout.wires,h])
    simp only [pointInPlaceConstantAdd,wires_append,Finset.mem_union,not_or]
    exact ⟨⟨nMasked _ _ _ ng ha,(modPrograms_not_mem q L.core.generic ng _ (L.inPlaceConstant_widths hw r hr) nm).1⟩,nMasked _ _ _ ng ha⟩
  have nswap : q∉wires (swapRegisters L.core.generic L.point.x L.inPlaceNegate.low) := by
    intro h
    have h' := swapRegisters_wires _ _ _ (hw.inputX.trans (L.inPlaceNegate_widths hw).core.low.symm) h
    have nlow : q∉L.inPlaceNegate.low := fun hh => nN (by simp [ModInPlaceLayout.wires,ModInPlaceLayout.z,ModAddCoreLayout.z,hh])
    change q∈(L.core.generic::L.point.x++L.inPlaceNegate.low).toFinset at h'
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,ng,nx,nlow,or_false] at h'
  have hm := mont_not_mem q L.inPlaceMultiply (L.inPlaceMultiply_widths hw) nM
  have nsquare := square_not_mem L hw hnd q na nx nb
  have hneg := modPrograms_not_mem q L.core.generic ng L.inPlaceNegate (L.inPlaceNegate_widths hw) nN
  simp only [pointInPlaceGeneric,pointInPlaceClearSlope,pointInPlaceNegate,wires_append,Finset.mem_union]
  have nmg := (nDivide L.core.generic ng).1
  have nmq := (nDivide L.core.equalNegY nq).2
  have nmask := nMasked L.core.equalX L.inPlaceSlope k.val ne na
  have ncx v := nCA L.point.x nx hw.inputX v
  have ncy v := nCA L.point.y ny hw.inputY v
  have nCX : q∉wires [.CX L.core.generic L.core.equalNegY,.CX L.core.equalX L.core.equalNegY] := by
    simp [wires,Instr.wires,ng,ne,nq]
  simp only [ncx _,ncy _,nmg,nmq,hm.1,hm.2,nsquare,nEq,nmask,nCX,hneg.2.2.1,hneg.2.2.2,
    nswap,false_or,not_false_eq_true]

/-- 已恢复的λ/e/q及求逆工作位与语法支持上界共同给出完整逐线保持。 -/
private theorem generic_frame_values (L : ControlledPointLayout) (P : Program)
    (hP : wires P ⊆ (pointInPlaceCoreWires L).toFinset)
    (X Y X' Y' : Fp) (G : Bool) (s : State) (m : List Bool)
    (hi : PointInPlaceValues L X Y 0 G false false s.basis)
    (ho : PointInPlaceValues L X' Y' 0 G false false (run P m s).basis)
    (q : Wire) (hx : q∉L.point.x) (hy : q∉L.point.y) :
    (run P m s).basis q=s.basis q := by
  by_cases ha : q∈L.inPlaceSlope
  · exact (regValue_eq_iff _ _ _).mp (ho.slope.trans hi.slope.symm) q ha
  by_cases hg : q=L.core.generic
  · subst q; exact ho.generic.trans hi.generic.symm
  by_cases he : q=L.core.equalX
  · subst q; exact ho.equal.trans hi.equal.symm
  by_cases hq : q=L.core.equalNegY
  · subst q; exact ho.quotient.trans hi.quotient.symm
  by_cases hc : q∈L.inPlaceInverse.wires
  · exact (regValue_eq_iff _ _ _).mp (ho.clean.trans hi.clean.symm) q hc
  apply run_preserves_outside
  apply mt (@hP q)
  have hu : q∉L.inPlaceOuterCoreWires := fun h => hc
    (L.inPlaceOuterCore_sublist.subset h)
  simp [pointInPlaceCoreWires,hx,hy,ha,hg,he,hq,hu]

theorem pointInPlaceGeneric_frame (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (cx cy k : Fp)
    (X Y X' Y' : Fp) (G : Bool) (s : State) (m : List Bool)
    (hi : PointInPlaceValues L X Y 0 G false false s.basis)
    (ho : PointInPlaceValues L X' Y' 0 G false false (run (pointInPlaceGeneric L cx cy k) m s).basis)
    (q : Wire) (hx : q∉L.point.x) (hy : q∉L.point.y) :
    (run (pointInPlaceGeneric L cx cy k) m s).basis q=s.basis q :=
  generic_frame_values L _ (pointInPlaceGeneric_wires_subset L hw hn cx cy k) X Y X' Y' G s m hi ho q hx hy

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointInPlaceClassification.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Secp256k1

/-- 三个角落位依次为O、启用的倍点和相反点；完整点编码用于检测。 -/
def inPlaceInfinity (b : Bool) (R : Point) : Bool := b && pointEqual R 0
def inPlaceDouble (b : Bool) (R C : Point) : Bool := b && !pointEqual C (-C) && pointEqual R C
def inPlaceInversePoint (b : Bool) (R C : Point) : Bool := b && pointEqual R (-C)
def inPlaceOrdinary (b : Bool) (R C : Point) : Bool :=
  ((b ^^ inPlaceInfinity b R) ^^ inPlaceDouble b R C) ^^ inPlaceInversePoint b R C

private theorem equal_simp [DecidableEq Point] (R C : Point) : pointEqual R C = decide (R=C) := by
  simp only [pointEqual,pointCode_injective.eq_iff]

/-- XOR分类不重叠；C=-C时禁用倍点，所以也覆盖二阶点。 -/
theorem inPlaceOrdinary_true (b : Bool) (R C : Point) (hc : C≠0) :
    inPlaceOrdinary b R C=true ↔ b=true ∧ R≠0 ∧ R≠C ∧ R≠-C := by
  classical
  have hnc : -C≠0 := neg_ne_zero.mpr hc
  by_cases h0 : R=0
  · subst R
    simp [inPlaceOrdinary,inPlaceInfinity,inPlaceDouble,inPlaceInversePoint,equal_simp,
      Ne.symm hc,Ne.symm hnc]
  by_cases h1 : R=C
  · subst R
    by_cases h2 : C=-C
    · have he : (C=-C) ↔ True := iff_true_intro h2
      cases b <;> simp [inPlaceOrdinary,inPlaceInfinity,inPlaceDouble,inPlaceInversePoint,equal_simp,hc,he]
    · cases b <;> simp [inPlaceOrdinary,inPlaceInfinity,inPlaceDouble,inPlaceInversePoint,equal_simp,hc,h2]
  by_cases h2 : R=-C
  · subst R
    cases b <;> simp [inPlaceOrdinary,inPlaceInfinity,inPlaceDouble,inPlaceInversePoint,equal_simp,hnc,h1]
  cases b <;> simp [inPlaceOrdinary,inPlaceInfinity,inPlaceDouble,inPlaceInversePoint,equal_simp,h0,h1,h2]

/-- 输出侧检测重建原输入的三个角落位。 -/
theorem inPlaceFlags_output (b : Bool) (R C : Point) :
    let S := if b then R+C else R
    (b && pointEqual S C)=inPlaceInfinity b R ∧
    (b && !pointEqual C (-C) && pointEqual S (C+C))=inPlaceDouble b R C ∧
    (b && pointEqual S 0)=inPlaceInversePoint b R C := by
  classical
  have hh := translated_point_flags R C b
  simp only [inPlaceInfinity,inPlaceDouble,inPlaceInversePoint,equal_simp]
  apply And.intro
  · apply Bool.eq_iff_iff.mpr
    simpa only [Bool.and_eq_true,decide_eq_true_eq] using hh.1
  constructor
  · apply Bool.eq_iff_iff.mpr
    simpa only [Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq,decide_eq_false_iff_not,← and_assoc] using hh.2.1
  · apply Bool.eq_iff_iff.mpr
    simpa only [Bool.and_eq_true,decide_eq_true_eq] using hh.2.2

/-- 三个角落的XOR写回，对任意零点编码为0的自然数字段成立。 -/
theorem inPlaceCorners_nat (b : Bool) (R C : Point) (hc : C≠0) (f : Point → Nat) (hf : f 0=0) :
    (((f (if inPlaceOrdinary b R C then R+C else R) ^^^
      (if inPlaceInfinity b R then f C else 0)) ^^^
      (if inPlaceDouble b R C then f C else 0)) ^^^
      (if inPlaceDouble b R C then f (C+C) else 0)) ^^^
      (if inPlaceInversePoint b R C then f (-C) else 0) = f (if b then R+C else R) := by
  classical
  have hnc : -C≠0 := neg_ne_zero.mpr hc
  cases b with
  | false => simp [inPlaceOrdinary,inPlaceInfinity,inPlaceDouble,inPlaceInversePoint]
  | true =>
    by_cases h0 : R=0
    · subst R
      simp [inPlaceOrdinary,inPlaceInfinity,inPlaceDouble,inPlaceInversePoint,equal_simp,
        Ne.symm hc,Ne.symm hnc,hf]
    by_cases h1 : R=C
    · subst R
      by_cases h2 : C=-C
      · have hz : C+C=0 := add_eq_zero_iff_eq_neg.mpr h2
        simp [inPlaceOrdinary,inPlaceInfinity,inPlaceDouble,inPlaceInversePoint,equal_simp,hc,hz,hf,← h2]
      · simp [inPlaceOrdinary,inPlaceInfinity,inPlaceDouble,inPlaceInversePoint,equal_simp,hc,h2]
    by_cases h2 : R=-C
    · subst R
      simp [inPlaceOrdinary,inPlaceInfinity,inPlaceDouble,inPlaceInversePoint,equal_simp,hnc,h1,hf]
    simp [inPlaceOrdinary,inPlaceInfinity,inPlaceDouble,inPlaceInversePoint,equal_simp,h0,h1,h2]
/-- 三个角落的XOR写回，对任意零点编码为0的布尔字段成立。 -/
theorem inPlaceCorners_bool (b : Bool) (R C : Point) (hc : C≠0) (f : Point → Bool) (hf : f 0=false) :
    ((((f (if inPlaceOrdinary b R C then R+C else R) ^^
      (if inPlaceInfinity b R then f C else false)) ^^
      (if inPlaceDouble b R C then f C else false)) ^^
      (if inPlaceDouble b R C then f (C+C) else false)) ^^
      (if inPlaceInversePoint b R C then f (-C) else false)) = f (if b then R+C else R) := by
  classical
  have hnc : -C≠0 := neg_ne_zero.mpr hc
  cases b with
  | false => simp [inPlaceOrdinary,inPlaceInfinity,inPlaceDouble,inPlaceInversePoint]
  | true =>
    by_cases h0 : R=0
    · subst R
      simp [inPlaceOrdinary,inPlaceInfinity,inPlaceDouble,inPlaceInversePoint,equal_simp,
        Ne.symm hc,Ne.symm hnc,hf]
    by_cases h1 : R=C
    · subst R
      by_cases h2 : C=-C
      · have hz : C+C=0 := add_eq_zero_iff_eq_neg.mpr h2
        simp [inPlaceOrdinary,inPlaceInfinity,inPlaceDouble,inPlaceInversePoint,equal_simp,hc,hz,hf,← h2]
      · simp [inPlaceOrdinary,inPlaceInfinity,inPlaceDouble,inPlaceInversePoint,equal_simp,hc,h2]
    by_cases h2 : R=-C
    · subst R
      simp [inPlaceOrdinary,inPlaceInfinity,inPlaceDouble,inPlaceInversePoint,equal_simp,hnc,h1,hf]
    simp [inPlaceOrdinary,inPlaceInfinity,inPlaceDouble,inPlaceInversePoint,equal_simp,h0,h1,h2]

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointInPlaceFlagGates.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

private theorem xorFour (b o d i g : Wire) (ho : o≠g) (hd : d≠g) (hi : i≠g)
    (s : State) (m : List Bool) :
    run [.CX b g,.CX o g,.CX d g,.CX i g] m s=
      ⟨s.phase,writeBit s.basis g ((((s.basis g ^^ s.basis b) ^^ s.basis o) ^^ s.basis d) ^^ s.basis i)⟩ := by
  simp [run,writeBit,ho,hd,hi]

theorem pointInPlaceGenericFlag_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (s : State) (m : List Bool) :
    run (pointInPlaceGenericFlag L) m s=
      ⟨s.phase,writeBit s.basis L.core.generic
        ((((s.basis L.core.generic ^^ s.basis L.control) ^^ s.basis L.infinitySelect) ^^
          s.basis L.doubleSelect) ^^ s.basis L.genericSelect)⟩ := by
  have hc := List.nodup_iff_count.mp (L.inPlace_interfaces_nodup hw hn) L.core.generic
  simp only [inPlaceFlags,List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at hc
  have ho : L.infinitySelect≠L.core.generic := by intro he; simp only [he,beq_self_eq_true,if_true] at hc; omega
  have hd : L.doubleSelect≠L.core.generic := by intro he; simp only [he,beq_self_eq_true,if_true] at hc; omega
  have hi : L.genericSelect≠L.core.generic := by intro he; simp only [he,beq_self_eq_true,if_true] at hc; omega
  exact xorFour _ _ _ _ _ ho hd hi s m

theorem pointInPlaceDoubleEnable_correct (L : ControlledPointLayout) (cy : Fp) (s : State) (m : List Bool) :
    run (pointInPlaceDoubleEnable L cy) m s=
      ⟨s.phase,writeBit s.basis L.core.double
        (s.basis L.core.double ^^ (s.basis L.control && decide (cy≠-cy)))⟩ := by
  by_cases hc : cy≠-cy
  · simp [pointInPlaceDoubleEnable,hc,run]
  · simp [pointInPlaceDoubleEnable,hc,run,writeBit]

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointDialogBoundary.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

/-- 点加阶段边界：合法点、控制、七个标志以及归零的斜率/求逆区。 -/
structure PointDialogBoundary (L : ControlledPointLayout) (R : Point) (b : Bool)
    (f : BasisState) (s : BasisState) : Prop where
  point : Holds.holds s L.point R
  control : s L.control=b
  flags : ∀ q∈L.inPlaceFlags,s q=f q
  clean : regValue L.dialogPool s=0

namespace PointDialogBoundary

variable {L : ControlledPointLayout} {R R' : Point} {b : Bool} {f f' s t : BasisState}

private theorem flag_away (hn : L.wires.Nodup) (q : Wire)
    (hq : q∈PointAddLayout.pointWires L.point++[L.control]++L.dialogPool) :
    q∉L.inPlaceFlags := by
  intro hf
  have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
  have h1 := List.count_pos_iff.mpr hq
  have h2 := List.count_pos_iff.mpr hf
  simp only [dialogUsedWires,List.count_append,List.count_cons,List.count_nil] at h h1
  omega

/-- 仅更新七个标志时，点、控制和干净工作区保持。 -/
theorem withFlags (hn : L.wires.Nodup) (v : PointDialogBoundary L R b f s)
    (hh : ∀ q∈L.inPlaceFlags,t q=f' q) (he : ∀ q∉L.inPlaceFlags,t q=s q) :
    PointDialogBoundary L R b f' t := by
  have hp := (point_holds _ _ _).mp v.point
  have away := flag_away hn
  refine ⟨(point_holds _ _ _).mpr ⟨?_,?_,?_⟩,?_,hh,?_⟩
  · exact (he _ (away _ (by simp [PointAddLayout.pointWires]))).trans hp.1
  · exact (regValue_congr _ _ _ (fun q hq => he q (away q (by simp [PointAddLayout.pointWires,hq])))).trans hp.2.1
  · exact (regValue_congr _ _ _ (fun q hq => he q (away q (by simp [PointAddLayout.pointWires,hq])))).trans hp.2.2
  · exact (he _ (away _ (by simp))).trans v.control
  · exact (regValue_congr _ _ _ (fun q hq => he q (away q (by simp [hq])))).trans v.clean

/-- 任意点坐标写回的外部保持会保留控制、标志和干净工作区。 -/
theorem withPoint (hn : L.wires.Nodup) (v : PointDialogBoundary L R b f s)
    (hp : Holds.holds t L.point R') (he : ∀ q∉PointAddLayout.pointWires L.point,t q=s q) :
    PointDialogBoundary L R' b f t := by
  have away (q : Wire) (hq : q∈[L.control]++L.inPlaceFlags++L.dialogPool) :
      q∉PointAddLayout.pointWires L.point := by
    intro hh
    have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hh
    simp only [dialogUsedWires,List.count_append,List.count_cons,List.count_nil] at h h1
    omega
  refine ⟨hp,(he _ (away _ (by simp))).trans v.control,?_,?_⟩
  · intro q hq; exact (he q (away q (by simp [hq]))).trans (v.flags q hq)
  · exact (regValue_congr _ _ _ (fun q hq => he q (away q (by simp [hq])))).trans v.clean

end PointDialogBoundary
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointInPlaceBoundary.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

/-- 点加阶段边界：合法点、控制、七个标志以及归零的斜率/求逆区。 -/
structure PointInPlaceBoundary (L : ControlledPointLayout) (R : Point) (b : Bool)
    (f : BasisState) (s : BasisState) : Prop where
  point : Holds.holds s L.point R
  control : s L.control=b
  flags : ∀ q∈L.inPlaceFlags,s q=f q
  slope : regValue L.inPlaceSlope s=0
  clean : regValue L.inPlaceInverse.wires s=0

namespace PointInPlaceBoundary

variable {L : ControlledPointLayout} {R R' : Point} {b : Bool} {f f' s t : BasisState}

private theorem flag_away (hw : L.Widths) (hn : L.wires.Nodup) (q : Wire)
    (hq : q∈PointAddLayout.pointWires L.point++[L.control]++L.inPlaceSlope++L.inPlaceInverse.wires) :
    q∉L.inPlaceFlags := by
  intro hf
  have h := List.nodup_iff_count.mp (L.inPlace_interfaces_nodup hw hn) q
  have h1 := List.count_pos_iff.mpr hq
  have h2 := List.count_pos_iff.mpr hf
  simp only [List.count_append,List.count_cons,List.count_nil] at h h1
  omega

/-- 仅更新七个标志时，点、控制和干净工作区保持。 -/
theorem withFlags (hw : L.Widths) (hn : L.wires.Nodup) (v : PointInPlaceBoundary L R b f s)
    (hh : ∀ q∈L.inPlaceFlags,t q=f' q) (he : ∀ q∉L.inPlaceFlags,t q=s q) :
    PointInPlaceBoundary L R b f' t := by
  have hp := (point_holds _ _ _).mp v.point
  have away := flag_away hw hn
  refine ⟨(point_holds _ _ _).mpr ⟨?_,?_,?_⟩,?_,hh,?_,?_⟩
  · exact (he _ (away _ (by simp [PointAddLayout.pointWires]))).trans hp.1
  · exact (regValue_congr _ _ _ (fun q hq => he q (away q (by simp [PointAddLayout.pointWires,hq])))).trans hp.2.1
  · exact (regValue_congr _ _ _ (fun q hq => he q (away q (by simp [PointAddLayout.pointWires,hq])))).trans hp.2.2
  · exact (he _ (away _ (by simp))).trans v.control
  · exact (regValue_congr _ _ _ (fun q hq => he q (away q (by simp [hq])))).trans v.slope
  · exact (regValue_congr _ _ _ (fun q hq => he q (away q (by simp [hq])))).trans v.clean

/-- 任意点坐标写回的外部保持会保留控制、标志和干净工作区。 -/
theorem withPoint (hw : L.Widths) (hn : L.wires.Nodup) (v : PointInPlaceBoundary L R b f s)
    (hp : Holds.holds t L.point R') (he : ∀ q∉PointAddLayout.pointWires L.point,t q=s q) :
    PointInPlaceBoundary L R' b f t := by
  have away (q : Wire) (hq : q∈[L.control]++L.inPlaceSlope++L.inPlaceFlags++L.inPlaceInverse.wires) :
      q∉PointAddLayout.pointWires L.point := by
    intro hh
    have h := List.nodup_iff_count.mp (L.inPlace_interfaces_nodup hw hn) q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hh
    simp only [List.count_append,List.count_cons,List.count_nil] at h h1
    omega
  refine ⟨hp,(he _ (away _ (by simp))).trans v.control,?_,?_,?_⟩
  · intro q hq; exact (he q (away q (by simp [hq]))).trans (v.flags q hq)
  · exact (regValue_congr _ _ _ (fun q hq => he q (away q (by simp [hq])))).trans v.slope
  · exact (regValue_congr _ _ _ (fun q hq => he q (away q (by simp [hq])))).trans v.clean

theorem values (v : PointInPlaceBoundary L R b f s)
    (he : f L.core.equalX=false) (hq : f L.core.equalNegY=false) :
    PointInPlaceValues L ((coordinates R).getD (0,0)).1 ((coordinates R).getD (0,0)).2
      0 (f L.core.generic) false false s := by
  have hp := (point_holds _ _ _).mp v.point
  exact ⟨hp.2.1,hp.2.2,v.slope,v.flags _ (by simp [inPlaceFlags]),
    (v.flags _ (by simp [inPlaceFlags])).trans he,(v.flags _ (by simp [inPlaceFlags])).trans hq,v.clean⟩

end PointInPlaceBoundary
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointInPlaceCorners.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

/-- 四次常量XOR的逐字段作用，对任意输入位串成立。 -/
theorem pointInPlaceCorners_effect (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (s : State) (m : List Bool) :
    PointEffect L.point
      ((((s.basis L.infinitySelect && pointFinite C) ^^ (s.basis L.doubleSelect && pointFinite C)) ^^
        (s.basis L.doubleSelect && pointFinite (C+C))) ^^ (s.basis L.genericSelect && pointFinite (-C)))
      ((((if s.basis L.infinitySelect then pointX C else 0) ^^^ (if s.basis L.doubleSelect then pointX C else 0)) ^^^
        (if s.basis L.doubleSelect then pointX (C+C) else 0)) ^^^ (if s.basis L.genericSelect then pointX (-C) else 0))
      ((((if s.basis L.infinitySelect then pointY C else 0) ^^^ (if s.basis L.doubleSelect then pointY C else 0)) ^^^
        (if s.basis L.doubleSelect then pointY (C+C) else 0)) ^^^ (if s.basis L.genericSelect then pointY (-C) else 0))
      s (run (pointInPlaceCorners L C) m s) := by
  have hr : (PointAddLayout.pointWires L.point).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have hh := List.nodup_iff_count.mp (L.inPlace_interfaces_nodup hw hn) q
    simp only [List.count_append] at hh
    omega
  have away (q : Wire) (hq : q∈L.inPlaceFlags) : q∉PointAddLayout.pointWires L.point := by
    intro hp
    have hh := List.nodup_iff_count.mp (L.inPlace_interfaces_nodup hw hn) q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hp
    simp only [List.count_append] at hh
    omega
  have ho := away L.infinitySelect (by simp [inPlaceFlags])
  have hd := away L.doubleSelect (by simp [inPlaceFlags])
  have hi := away L.genericSelect (by simp [inPlaceFlags])
  let u := run (maskedPointConstant L.infinitySelect L.point C) m s
  have e0 := maskedPointConstant_correct _ _ C hr ho hw.inputX hw.inputY s m
  have ud : u.basis L.doubleSelect=s.basis L.doubleSelect := e0.outside _ hd
  let v := run (maskedPointConstant L.doubleSelect L.point C) m u
  have e1 := maskedPointConstant_correct _ _ C hr hd hw.inputX hw.inputY u m
  have vd : v.basis L.doubleSelect=s.basis L.doubleSelect := (e0.trans e1).outside _ hd
  let w := run (maskedPointConstant L.doubleSelect L.point (C+C)) m v
  have e2 := maskedPointConstant_correct _ _ (C+C) hr hd hw.inputX hw.inputY v m
  have wi : w.basis L.genericSelect=s.basis L.genericSelect := ((e0.trans e1).trans e2).outside _ hi
  have e3 := maskedPointConstant_correct _ _ (-C) hr hi hw.inputX hw.inputY w m
  have hh := ((e0.trans e1).trans e2).trans e3
  rw [pointInPlaceCorners,run_append,run_take,run_append,run_take,run_append,run_take]
  simp only [measurementCount_append,(maskedPointConstant_counts _ _ _).2,Nat.zero_add,List.drop_zero]
  simpa only [ud,vd,wi] using hh

/-- 输入分类确定的四次XOR将普通分支输出或角落输入统一写为受控平移结果。 -/
theorem pointBoundary_corners (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R C : Point) (hc : C≠0) (b : Bool) (f : BasisState)
    (ho : f L.infinitySelect=inPlaceInfinity b R)
    (hd : f L.doubleSelect=inPlaceDouble b R C)
    (hi : f L.genericSelect=inPlaceInversePoint b R C) :
    Triple (PointInPlaceBoundary L (if inPlaceOrdinary b R C then R+C else R) b f)
      (pointInPlaceCorners L C) (PointInPlaceBoundary L (if b then R+C else R) b f) := by
  intro s m v
  have he := pointInPlaceCorners_effect L hw hn C s m
  have vo := (v.flags _ (by simp [inPlaceFlags])).trans ho
  have vd := (v.flags _ (by simp [inPlaceFlags])).trans hd
  have vi := (v.flags _ (by simp [inPlaceFlags])).trans hi
  have hp := (point_holds _ _ _).mp v.point
  refine ⟨he.phase,v.withPoint hw hn ((point_holds _ _ _).mpr ⟨?_,?_,?_⟩) he.outside⟩
  · rw [he.finite,hp.1,vo,vd,vi]
    have h := inPlaceCorners_bool b R C hc pointFinite (by rfl)
    have bool_if (a b : Bool) : (if a then b else false)=(a && b) := by cases a <;> rfl
    simpa only [bool_if,Bool.xor_assoc] using h
  · rw [he.x,hp.2.1,vo,vd,vi]
    simpa only [Nat.xor_assoc] using inPlaceCorners_nat b R C hc pointX (by rfl)
  · rw [he.y,hp.2.2,vo,vd,vi]
    simpa only [Nat.xor_assoc] using inPlaceCorners_nat b R C hc pointY (by rfl)

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointDialogCorners.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

/-- 四次常量XOR的逐字段作用，对任意输入位串成立。 -/
theorem pointDialogCorners_effect (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (s : State) (m : List Bool) :
    PointEffect L.point
      ((((((s.basis L.infinitySelect && pointFinite C) ^^ (s.basis L.doubleSelect && pointFinite C)) ^^
        (s.basis L.doubleSelect && pointFinite (C+C))) ^^ (s.basis L.genericSelect && pointFinite (-C))) ^^
        (s.basis L.core.equalNegY && pointFinite (dialogExceptionPoint C))) ^^
        (s.basis L.core.equalNegY && pointFinite (-C)))
      ((((((if s.basis L.infinitySelect then pointX C else 0) ^^^ (if s.basis L.doubleSelect then pointX C else 0)) ^^^
        (if s.basis L.doubleSelect then pointX (C+C) else 0)) ^^^ (if s.basis L.genericSelect then pointX (-C) else 0)) ^^^
        (if s.basis L.core.equalNegY then pointX (dialogExceptionPoint C) else 0)) ^^^
        (if s.basis L.core.equalNegY then pointX (-C) else 0))
      ((((((if s.basis L.infinitySelect then pointY C else 0) ^^^ (if s.basis L.doubleSelect then pointY C else 0)) ^^^
        (if s.basis L.doubleSelect then pointY (C+C) else 0)) ^^^ (if s.basis L.genericSelect then pointY (-C) else 0)) ^^^
        (if s.basis L.core.equalNegY then pointY (dialogExceptionPoint C) else 0)) ^^^
        (if s.basis L.core.equalNegY then pointY (-C) else 0))
      s (run (pointDialogCorners L C) m s) := by
  have hr : (PointAddLayout.pointWires L.point).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
    simp only [dialogUsedWires,List.count_append] at h
    omega
  have away : L.core.equalNegY∉PointAddLayout.pointWires L.point := by
    intro hh
    have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) L.core.equalNegY
    have hp := List.count_pos_iff.mpr hh
    simp only [dialogUsedWires,inPlaceFlags,List.count_append,List.count_cons,List.count_nil,
      beq_self_eq_true,if_true] at h
    omega
  let u := run (pointInPlaceCorners L C) m s
  have e0 := pointInPlaceCorners_effect L hw hn C s m
  have uh : u.basis L.core.equalNegY=s.basis L.core.equalNegY := e0.outside _ away
  let v := run (maskedPointConstant L.core.equalNegY L.point (dialogExceptionPoint C)) m u
  have e1 := maskedPointConstant_correct _ _ (dialogExceptionPoint C) hr away hw.inputX hw.inputY u m
  have vh : v.basis L.core.equalNegY=s.basis L.core.equalNegY := (e0.trans e1).outside _ away
  have e2 := maskedPointConstant_correct _ _ (-C) hr away hw.inputX hw.inputY v m
  have he := (e0.trans e1).trans e2
  rw [pointDialogCorners,run_append,run_take,run_append,run_take]
  simp only [pointInPlaceCorners,measurementCount_append,(maskedPointConstant_counts _ _ _).2,
    Nat.add_zero,List.drop_zero]
  simpa only [uh,vh] using he

/-- 输入分类确定的四次XOR将普通分支输出或角落输入统一写为受控平移结果。 -/
theorem dialogBoundary_corners [DecidableEq Point] (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R C : Point) (hc : C≠0) (b : Bool) (f : BasisState)
    (ho : f L.infinitySelect=dialogInfinity b R)
    (hd : f L.doubleSelect=dialogDouble b R C)
    (hi : f L.genericSelect=dialogInversePoint b R C)
    (hh : f L.core.equalNegY=dialogException b R C) :
    Triple (PointDialogBoundary L (if dialogOrdinary b R C then R+C else R) b f)
      (pointDialogCorners L C) (PointDialogBoundary L (if b then R+C else R) b f) := by
  intro s m v
  have he := pointDialogCorners_effect L hw hn C s m
  have vo := (v.flags _ (by simp [inPlaceFlags])).trans ho
  have vd := (v.flags _ (by simp [inPlaceFlags])).trans hd
  have vi := (v.flags _ (by simp [inPlaceFlags])).trans hi
  have vh := (v.flags _ (by simp [inPlaceFlags])).trans hh
  have hp := (point_holds _ _ _).mp v.point
  refine ⟨he.phase,v.withPoint hn ((point_holds _ _ _).mpr ⟨?_,?_,?_⟩) he.outside⟩
  · rw [he.finite,hp.1,vo,vd,vi,vh]
    have h := dialogCorners_bool b R C hc pointFinite (by rfl)
    have bool_if (a b : Bool) : (if a then b else false)=(a && b) := by cases a <;> rfl
    simpa only [bool_if,Bool.xor_assoc] using h
  · rw [he.x,hp.2.1,vo,vd,vi,vh]
    simpa only [Nat.xor_assoc] using dialogCorners_nat b R C hc pointX (by rfl)
  · rw [he.y,hp.2.2,vo,vd,vi,vh]
    simpa only [Nat.xor_assoc] using dialogCorners_nat b R C hc pointY (by rfl)

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointDialogGenericPoint.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

theorem dialogBoundary_generic (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) (b : Bool) (f : BasisState) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (hg : f L.core.generic=true → R≠0 ∧ R≠(.some hc : Point) ∧ R≠-(.some hc : Point) ∧
      R≠dialogExceptionPoint (.some hc)) :
    Triple (PointDialogBoundary L R b f) (pointDialogGeneric L cx cy)
      (PointDialogBoundary L (if f L.core.generic then R+.some hc else R) b f) := by
  intro s m v
  have hp := (point_holds _ _ _).mp v.point
  have values : PointDialogValues L ((coordinates R).getD (0,0)).1
      ((coordinates R).getD (0,0)).2 (f L.core.generic) s.basis s.basis :=
    ⟨hp.2.1,hp.2.2,v.flags _ (by simp [inPlaceFlags]),v.clean,fun _ _=>rfl⟩
  have hfinite : L.point.finite∉L.point.x++L.point.y := by
    intro hh
    have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) L.point.finite
    have ht := List.count_pos_iff.mpr hh
    simp only [dialogUsedWires,PointAddLayout.pointWires,List.count_append,List.count_cons,
      beq_self_eq_true,if_true] at h ht
    omega
  have outside (q : Wire) (hq : q∉PointAddLayout.pointWires L.point) : q∉L.point.x++L.point.y := by
    simp only [PointAddLayout.pointWires,List.mem_append,List.mem_cons,not_or] at hq ⊢
    exact ⟨hq.1.2,hq.2⟩
  cases hG : f L.core.generic with
  | false =>
    rw [hG] at values
    obtain ⟨phase,hv⟩ := pointDialogGeneric_false L hw hn _ _ cx cy s.basis s m values
    refine ⟨phase,v.withPoint hn ?_ (fun q hq=>hv.rest q (outside q hq))⟩
    simp only [Bool.false_eq_true,if_false]
    exact (point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1,hv.x,hv.y⟩
  | true =>
    have he := hg hG
    cases R with
    | zero => exact False.elim (he.1 rfl)
    | @some x y hr =>
      have den := dialog_denominators_ne_zero hr hc he.2.1 he.2.2.1 he.2.2.2
      rw [hG] at values
      obtain ⟨phase,hv⟩ := pointDialogGeneric_true L hw hn x y cx cy s.basis den.1 den.2 s m values
      refine ⟨phase,v.withPoint hn ?_ (fun q hq=>hv.rest q (outside q hq))⟩
      simp only [if_true,←genericAdd_correct hr hc den.1,genericAdd]
      exact (point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1,hv.x,hv.y⟩

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointDialogBoundarySteps.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem dialogBoundary_equal (R C : Point) (b : Bool) (f : BasisState) (c t : Wire)
    (hc : c=L.control ∨ c∈L.inPlaceFlags) (ht : t∈L.inPlaceFlags) (hct : c≠t) (B : Bool)
    (hb : (if c=L.control then b else f c)=B) :
    Triple (PointDialogBoundary L R b f)
      (equalConstant c t L.dialogPointZero (pointCode C))
      (PointDialogBoundary L R b (writeBit f t (f t ^^ (B && pointEqual R C)))) := by
  have hnd := L.dialogPointZero_nodup hn c t hct hc ht
  intro s m v
  have hclean : regValue (L.dialogPool.take 513) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq=>(regValue_zero _ _).mp v.clean q (List.take_subset _ _ hq))
  have hh := equalPoint_correct c t L.point (L.dialogPool.take 513) R C hw.inputX hw.inputY
    (by simp [L.dialogPool_length hw]) hnd s m v.point hclean
  have hcval : s.basis c=B := by
    rw [← hb]
    split_ifs with h
    · subst c; exact v.control
    · exact v.flags c (hc.resolve_left h)
  change run (equalConstant c t L.dialogPointZero (pointCode C)) m s=_ at hh
  refine ⟨by rw [hh],v.withFlags hn ?_ ?_⟩
  · intro q hq
    rw [hh]
    by_cases he : q=t
    · subst q; simp [writeBit,hcval,v.flags t ht]
    · simp [writeBit,he,v.flags q hq]
  · intro q hq
    rw [hh]
    have hqt : q≠t := fun he => hq (he ▸ ht)
    simp [writeBit,hqt]

theorem dialogBoundary_genericFlag (R : Point) (b : Bool) (f : BasisState) :
    Triple (PointDialogBoundary L R b f) (pointInPlaceGenericFlag L)
      (PointDialogBoundary L R b (writeBit f L.core.generic
        ((((f L.core.generic ^^ b) ^^ f L.infinitySelect) ^^ f L.doubleSelect) ^^ f L.genericSelect))) := by
  intro s m v
  have hh := pointInPlaceGenericFlag_correct L hw hn s m
  refine ⟨by rw [hh],v.withFlags hn ?_ ?_⟩
  · intro q hq
    rw [hh]
    by_cases he : q=L.core.generic
    · subst q
      simp [writeBit,v.control,v.flags L.core.generic (by simp [inPlaceFlags]),
        v.flags L.infinitySelect (by simp [inPlaceFlags]),v.flags L.doubleSelect (by simp [inPlaceFlags]),
        v.flags L.genericSelect (by simp [inPlaceFlags])]
    · simp [writeBit,he,v.flags q hq]
  · intro q hq
    rw [hh]
    have hqt : q≠L.core.generic := fun he => hq (by simp [he,inPlaceFlags])
    simp [writeBit,hqt]

omit hw in
theorem dialogBoundary_doubleEnable (R : Point) (b : Bool) (f : BasisState) (cy : Fp) :
    Triple (PointDialogBoundary L R b f) (pointInPlaceDoubleEnable L cy)
      (PointDialogBoundary L R b (writeBit f L.core.double
        (f L.core.double ^^ (b && decide (cy≠-cy))))) := by
  intro s m v
  have hh := pointInPlaceDoubleEnable_correct L cy s m
  refine ⟨by rw [hh],v.withFlags hn ?_ ?_⟩
  · intro q hq
    rw [hh]
    by_cases he : q=L.core.double
    · subst q; simp [writeBit,v.control,v.flags L.core.double (by simp [inPlaceFlags])]
    · simp [writeBit,he,v.flags q hq]
  · intro q hq
    rw [hh]
    have hqt : q≠L.core.double := fun he => hq (by simp [he,inPlaceFlags])
    simp [writeBit,hqt]

omit hw in
theorem dialogBoundary_cx (R : Point) (b : Bool) (f : BasisState) (c t : Wire)
    (hc : c=L.control ∨ c∈L.inPlaceFlags) (ht : t∈L.inPlaceFlags) (B : Bool)
    (hb : (if c=L.control then b else f c)=B) :
    Triple (PointDialogBoundary L R b f) [.CX c t]
      (PointDialogBoundary L R b (writeBit f t (f t ^^ B))) := by
  intro s m v
  have hcval : s.basis c=B := by
    rw [←hb]; split_ifs with h
    · subst c; exact v.control
    · exact v.flags c (hc.resolve_left h)
  refine ⟨rfl,v.withFlags hn ?_ ?_⟩
  · intro q hq
    by_cases he : q=t
    · subst q; simp [run,writeBit,hcval,v.flags t ht]
    · simp [run,writeBit,he,v.flags q hq]
  · intro q hq
    have hqt : q≠t := fun he=>hq (he ▸ ht)
    simp [run,writeBit,hqt]

omit hw in
theorem dialogBoundary_exceptionEnable (R C : Point) (b : Bool) (f : BasisState) :
    Triple (PointDialogBoundary L R b f) (pointDialogExceptionEnable L C)
      (PointDialogBoundary L R b (writeBit f L.core.equalX
        (f L.core.equalX ^^ (b && (!pointEqual (dialogExceptionPoint C) 0 &&
          !pointEqual (dialogExceptionPoint C) C && !pointEqual (dialogExceptionPoint C) (-C)))))) := by
  unfold pointDialogExceptionEnable
  split_ifs with h
  · simpa only [h,Bool.and_true] using dialogBoundary_cx L hn R b f L.control L.core.equalX
      (Or.inl rfl) (by simp [inPlaceFlags]) b (by simp)
  · intro s m v
    refine ⟨rfl,⟨v.point,v.control,?_,v.clean⟩⟩
    intro q hq
    have hf : (!pointEqual (dialogExceptionPoint C) 0 &&
      !pointEqual (dialogExceptionPoint C) C && !pointEqual (dialogExceptionPoint C) (-C))=false :=
      Bool.eq_false_iff.mpr h
    simpa [hf,writeBit] using v.flags q hq

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointDialogFlagState.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

def dialogFlagState (L : ControlledPointLayout) (O D I G E H K : Bool) : BasisState :=
  writeBit (writeBit (writeBit (writeBit (writeBit (writeBit (writeBit (fun _=>false)
    L.infinitySelect O) L.doubleSelect D) L.genericSelect I) L.core.generic G)
      L.core.equalX E) L.core.equalNegY H) L.core.double K

private theorem flag_reads (o d i g e h k : Wire) (hn : [o,d,i,g,e,h,k].Nodup)
    (O D I G E H K : Bool) :
    let f := writeBit (writeBit (writeBit (writeBit (writeBit (writeBit (writeBit (fun _=>false)
      o O) d D) i I) g G) e E) h H) k K
    f o=O ∧ f d=D ∧ f i=I ∧ f g=G ∧ f e=E ∧ f h=H ∧ f k=K := by
  simp only [List.nodup_cons,List.mem_cons,not_or] at hn
  simp_all [writeBit]

theorem dialogFlagState_read (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (O D I G E H K : Bool) :
    let f := dialogFlagState L O D I G E H K
    f L.infinitySelect=O ∧ f L.doubleSelect=D ∧ f L.genericSelect=I ∧
      f L.core.generic=G ∧ f L.core.equalX=E ∧ f L.core.equalNegY=H ∧ f L.core.double=K := by
  have hh : L.inPlaceFlags.Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
    simp only [dialogUsedWires,List.count_append] at h
    omega
  exact flag_reads _ _ _ _ _ _ _ hh O D I G E H K

theorem dialogFlagState_zero (L : ControlledPointLayout) :
    dialogFlagState L false false false false false false false=(fun _=>false) := by
  funext q
  simp [dialogFlagState,writeBit]

theorem PointDialogBoundary.congrFlags {L : ControlledPointLayout} {R : Point} {b : Bool}
    {f f' s : BasisState} (v : PointDialogBoundary L R b f s)
    (he : ∀q,q∈L.inPlaceFlags → f q=f' q) : PointDialogBoundary L R b f' s :=
  ⟨v.point,v.control,fun q hq=>(v.flags q hq).trans (he q hq),v.clean⟩

/-- 只比较七个真实标志位，不对函数在池外的取值施加要求。 -/
theorem dialogFlagState_update (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (O D I G E H K T : Bool) :
    (∀q,q∈L.inPlaceFlags →
      writeBit (dialogFlagState L O D I G E H K) L.infinitySelect T q=dialogFlagState L T D I G E H K q) ∧
    (∀q,q∈L.inPlaceFlags →
      writeBit (dialogFlagState L O D I G E H K) L.doubleSelect T q=dialogFlagState L O T I G E H K q) ∧
    (∀q,q∈L.inPlaceFlags →
      writeBit (dialogFlagState L O D I G E H K) L.genericSelect T q=dialogFlagState L O D T G E H K q) ∧
    (∀q,q∈L.inPlaceFlags →
      writeBit (dialogFlagState L O D I G E H K) L.core.generic T q=dialogFlagState L O D I T E H K q) ∧
    (∀q,q∈L.inPlaceFlags →
      writeBit (dialogFlagState L O D I G E H K) L.core.equalX T q=dialogFlagState L O D I G T H K q) ∧
    (∀q,q∈L.inPlaceFlags →
      writeBit (dialogFlagState L O D I G E H K) L.core.equalNegY T q=dialogFlagState L O D I G E T K q) ∧
    (∀q,q∈L.inPlaceFlags →
      writeBit (dialogFlagState L O D I G E H K) L.core.double T q=dialogFlagState L O D I G E H T q) := by
  have hnd : L.inPlaceFlags.Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
    simp only [dialogUsedWires,List.count_append] at h
    omega
  simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,not_or] at hnd
  repeat' constructor
  all_goals
    intro q hq
    simp only [inPlaceFlags,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [dialogFlagState,writeBit,eq_comm]

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointDialogFlagSteps.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

omit hw in
theorem dialogFlag_separation : (L.control::L.inPlaceFlags).Nodup := by
  apply List.nodup_iff_count.mpr; intro q
  have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
  simp only [dialogUsedWires,List.count_append,List.count_cons] at h ⊢
  omega

theorem dialogFlag_equalO (R C : Point) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (equalConstant L.control L.infinitySelect L.dialogPointZero (pointCode C))
      (PointDialogBoundary L R b (dialogFlagState L (O ^^ (b && pointEqual R C)) D I G E H K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := dialogBoundary_equal L hw hn R C b (dialogFlagState L O D I G E H K) L.control L.infinitySelect
    (Or.inl rfl)
    (by simp [inPlaceFlags]) (by tauto) b
    (by simp)
  simp only [hr.1] at hh
  exact hh.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).1)

theorem dialogFlag_equalD (R C : Point) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (equalConstant L.core.double L.doubleSelect L.dialogPointZero (pointCode C))
      (PointDialogBoundary L R b (dialogFlagState L O (D ^^ (K && pointEqual R C)) I G E H K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := dialogBoundary_equal L hw hn R C b (dialogFlagState L O D I G E H K) L.core.double L.doubleSelect
    (Or.inr (by simp [inPlaceFlags]))
    (by simp [inPlaceFlags]) (by tauto) K
    (by rw [if_neg (by tauto)]; exact hr.2.2.2.2.2.2)
  simp only [hr.2.1] at hh
  exact hh.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).2.1)

theorem dialogFlag_equalI (R C : Point) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (equalConstant L.control L.genericSelect L.dialogPointZero (pointCode C))
      (PointDialogBoundary L R b (dialogFlagState L O D (I ^^ (b && pointEqual R C)) G E H K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := dialogBoundary_equal L hw hn R C b (dialogFlagState L O D I G E H K) L.control L.genericSelect
    (Or.inl rfl)
    (by simp [inPlaceFlags]) (by tauto) b
    (by simp)
  simp only [hr.2.2.1] at hh
  exact hh.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).2.2.1)

theorem dialogFlag_equalH (R C : Point) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (equalConstant L.core.equalX L.core.equalNegY L.dialogPointZero (pointCode C))
      (PointDialogBoundary L R b (dialogFlagState L O D I G E (H ^^ (E && pointEqual R C)) K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := dialogBoundary_equal L hw hn R C b (dialogFlagState L O D I G E H K) L.core.equalX L.core.equalNegY
    (Or.inr (by simp [inPlaceFlags]))
    (by simp [inPlaceFlags]) (by tauto) E
    (by rw [if_neg (by tauto)]; exact hr.2.2.2.2.1)
  simp only [hr.2.2.2.2.2.1] at hh
  exact hh.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).2.2.2.2.2.1)

omit hw in
theorem dialogFlag_doubleEnable (R : Point) (b O D I G E H K : Bool) (cy : Fp) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (pointInPlaceDoubleEnable L cy)
      (PointDialogBoundary L R b (dialogFlagState L O D I G E H (K ^^ (b && decide (cy≠-cy))))) := by
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := dialogBoundary_doubleEnable L hn R b (dialogFlagState L O D I G E H K) cy
  simp only [hr.2.2.2.2.2.2] at hh
  exact hh.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).2.2.2.2.2.2)

omit hw in
theorem dialogFlag_exceptionEnable (R : Point) (b O D I G E H K : Bool) (C : Point) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (pointDialogExceptionEnable L C)
      (PointDialogBoundary L R b (dialogFlagState L O D I G (E ^^ (b && (!pointEqual (dialogExceptionPoint C) 0 && !pointEqual (dialogExceptionPoint C) C && !pointEqual (dialogExceptionPoint C) (-C)))) H K)) := by
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := dialogBoundary_exceptionEnable L hn R C b (dialogFlagState L O D I G E H K)
  simp only [hr.2.2.2.2.1] at hh
  exact hh.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).2.2.2.2.1)

theorem dialogFlag_generic (R : Point) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (pointDialogGenericFlag L)
      (PointDialogBoundary L R b (dialogFlagState L O D I (((((G ^^ b) ^^ O) ^^ D) ^^ I) ^^ H) E H K)) := by
  have hr := dialogFlagState_read L hn O D I G E H K
  have h1 := dialogBoundary_genericFlag L hw hn R b (dialogFlagState L O D I G E H K)
  simp only [hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1] at h1
  have h1' := h1.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).2.2.2.1)
  let A := ((((G ^^ b) ^^ O) ^^ D) ^^ I)
  have readA := dialogFlagState_read L hn O D I A E H K
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,not_or] at sep
  have h2 := dialogBoundary_cx L hn R b (dialogFlagState L O D I A E H K)
    L.core.equalNegY L.core.generic (Or.inr (by simp [inPlaceFlags])) (by simp [inPlaceFlags]) H
    (by rw [if_neg (by tauto)]; exact readA.2.2.2.2.2.1)
  simp only [readA.2.2.2.1] at h2
  have h2' := h2.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I A E H K _).2.2.2.1)
  exact h1'.seq h2'

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointDialogFiniteSpec.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

private theorem equal_simp_PointDialogFiniteSpec [DecidableEq Point] (R C : Point) : pointEqual R C=decide (R=C) := by
  simp only [pointEqual,pointCode_injective.eq_iff]

theorem pointDialogFinite_spec (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) :
    Triple (PointDialogBoundary L R b (fun _=>false)) (pointDialogFinite L (.some hc) cx cy)
      (PointDialogBoundary L (if b then R+.some hc else R) b (fun _=>false)) := by
  classical
  let C : Point := .some hc
  let O := dialogInfinity b R
  let D := dialogDouble b R C
  let I := dialogInversePoint b R C
  let H := dialogException b R C
  let G := dialogOrdinary b R C
  let E := b && decide (dialogExceptionEnabled C)
  let K := b && decide (cy≠-cy)
  let S := if b then R+C else R
  have hC : C≠0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  have hK : K=(b && decide (C≠-C)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [K,Bool.and_eq_true,decide_eq_true_eq]
    exact and_congr_right (fun _=>doubling_enabled_iff hc)
  have hE : (!pointEqual (dialogExceptionPoint C) 0 && !pointEqual (dialogExceptionPoint C) C &&
      !pointEqual (dialogExceptionPoint C) (-C))=decide (dialogExceptionEnabled C) := by
    simp [equal_simp_PointDialogFiniteSpec,dialogExceptionEnabled,Bool.and_assoc]
  have hO : (b && pointEqual R 0)=O := by simp only [O,dialogInfinity,equal_simp_PointDialogFiniteSpec]
  have hD : (K && pointEqual R C)=D := by rw [hK]; simp only [D,dialogDouble,equal_simp_PointDialogFiniteSpec]
  have hI : (b && pointEqual R (-C))=I := by simp only [I,dialogInversePoint,equal_simp_PointDialogFiniteSpec]
  have hH : (E && pointEqual R (dialogExceptionPoint C))=H := by
    simp [E,H,dialogException,dialogExceptionEnabled,equal_simp_PointDialogFiniteSpec]
  have h0 := dialogFlag_doubleEnable L hn R b false false false false false false false cy
  simp only [Bool.false_xor] at h0
  have h1 := dialogFlag_exceptionEnable L hn R b false false false false false false K C
  rw [hE,Bool.false_xor] at h1
  have h2 := dialogFlag_equalO L hw hn R 0 b false false false false E false K
  rw [hO,Bool.false_xor] at h2
  have h3 := dialogFlag_equalD L hw hn R C b O false false false E false K
  rw [hD,Bool.false_xor] at h3
  have h4 := dialogFlag_equalI L hw hn R (-C) b O D false false E false K
  rw [hI,Bool.false_xor] at h4
  have h5 := dialogFlag_equalH L hw hn R (dialogExceptionPoint C) b O D I false E false K
  rw [hH,Bool.false_xor] at h5
  have h6 := dialogFlag_generic L hw hn R b O D I false E H K
  simp only [Bool.false_xor] at h6
  have read := dialogFlagState_read L hn O D I G E H K
  have h7 := dialogBoundary_generic L hw hn R b (dialogFlagState L O D I G E H K) hc
    (fun hg => ((dialogOrdinary_true b R C hC).mp (read.2.2.2.1.symm.trans hg)).2)
  rw [read.2.2.2.1] at h7
  have h8 := dialogBoundary_corners L hw hn R C hC b (dialogFlagState L O D I G E H K)
    read.1 read.2.1 read.2.2.1 read.2.2.2.2.2.1
  have h9 := dialogFlag_generic L hw hn S b O D I G E H K
  have hgclear : (((((G ^^ b) ^^ O) ^^ D) ^^ I) ^^ H)=false := by
    dsimp only [G,dialogOrdinary,O,D,I,H]
    generalize dialogInfinity b R=o,dialogDouble b R C=d,dialogInversePoint b R C=i,
      dialogException b R C=h
    cases b <;> cases o <;> cases d <;> cases i <;> cases h <;> rfl
  rw [hgclear] at h9
  have hf := dialogFlags_output b R C
  have h10 := dialogFlag_equalO L hw hn S C b O D I false E H K
  simp only [equal_simp_PointDialogFiniteSpec] at h10
  rw [hf.1,Bool.xor_self] at h10
  have h11 := dialogFlag_equalD L hw hn S (C+C) b false D I false E H K
  have hdo : (K && pointEqual S (C+C))=D := by
    rw [hK]; simpa only [equal_simp_PointDialogFiniteSpec] using hf.2.1
  rw [hdo,Bool.xor_self] at h11
  have h12 := dialogFlag_equalI L hw hn S 0 b false false I false E H K
  simp only [equal_simp_PointDialogFiniteSpec] at h12
  rw [hf.2.2.1,Bool.xor_self] at h12
  have h13 := dialogFlag_equalH L hw hn S (-C) b false false false false E H K
  have heout : (E && pointEqual S (-C))=H := by
    simpa [E,H,S,dialogExceptionEnabled,equal_simp_PointDialogFiniteSpec] using hf.2.2.2
  rw [heout,Bool.xor_self] at h13
  have h14 := dialogFlag_exceptionEnable L hn S b false false false false E false K C
  rw [hE,show (E ^^ (b && decide (dialogExceptionEnabled C)))=false from Bool.xor_self E] at h14
  have h15 := dialogFlag_doubleEnable L hn S b false false false false false false K cy
  rw [show (K ^^ (b && decide (cy≠-cy)))=false from Bool.xor_self K] at h15
  have h := ((((((((((((((h0.seq h1).seq h2).seq h3).seq h4).seq h5).seq h6).seq h7).seq h8).seq h9).seq h10).seq h11).seq h12).seq h13).seq h14).seq h15
  simpa only [pointDialogFinite,List.append_assoc,dialogFlagState_zero] using h

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/OffsetBorrowedSupportPoint.lean
noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic
open ControlledPointLayout DirectSkywalk
attribute [local irreducible] pointOffsetBorrowedArithmetic compactOffsetCallerArithmetic

/-- Instruction-derived compact support includes both exact zero-repair branches. -/
theorem pointOffsetBorrowedArithmetic_compact_support (L : ControlledPointLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) (multiply : Bool) :
    wires (pointOffsetBorrowedArithmetic L multiply) ⊆
      (L.core.generic::L.point.x++L.point.y++L.compactPointPool).toFinset := by
  let W := (L.core.generic::L.point.x++L.point.y++L.compactPointPool).toFinset
  have pool (i : Nat) (hi : i < 1542 ∨ 1800 ≤ i ∧ i < 1805) : L.core.poolWire i∈W := by
    have hm : L.core.poolWire i∈L.compactPointPool := by
      rcases hi with hi|hi
      · apply List.mem_append_left
        exact arith_mem L.core.poolWire 0 1542 i (by omega) hi
      · apply List.mem_append_right
        exact arith_mem L.core.poolWire 1800 5 i hi.1 hi.2
    simp [W,hm]
  have hb : L.core.generic∈W := by simp [W]
  have hg : L.skywalkDirectSelectorG∈W := pool 1802 (Or.inr ⟨by omega,by omega⟩)
  have hs : L.skywalkDirectSelectorS∈W := pool 1803 (Or.inr ⟨by omega,by omega⟩)
  have hz : L.skywalkDirectZero∈W := pool 1804 (Or.inr ⟨by omega,by omega⟩)
  have hi : directSkywalkCin L∈W := pool 1801 (Or.inr ⟨by omega,by omega⟩)
  have kernel := compactOffsetCallerArithmetic_support (!multiply) L.skywalkDirectMap
    (L.skywalkDirectMap_nodup hw hn) L.core.generic L.skywalkDirectSelectorG L.skywalkDirectSelectorS
    W (L.compactSharedMap_support hw) hb hg hs
  have own : (L.skywalkDirectZero::directSkywalkCin L::(L.point.x++directSkywalkCarry L)).toFinset⊆W := by
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq
    rcases hq with rfl|rfl|hx|hc
    · exact hz
    · exact hi
    · simp [W,hx]
    · rw [directSkywalkCarry,wireBlock] at hc
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hc
      simp only [List.mem_range'_1] at hj
      exact pool j (Or.inl (by omega))
  have repair := (directZeroDivisor_wires L.point.x (directSkywalkCarry L)
    (directSkywalkCin L) L.skywalkDirectZero).trans own
  rw [wires_append] at repair
  have enter : wires (directZeroDivisorEnter L.point.x (directSkywalkCarry L)
      (directSkywalkCin L) L.skywalkDirectZero)⊆W := fun _ h => repair (Finset.mem_union_left _ h)
  have leave : wires (directZeroDivisorLeave L.point.x (directSkywalkCarry L)
      (directSkywalkCin L) L.skywalkDirectZero)⊆W := fun _ h => repair (Finset.mem_union_right _ h)
  simp only [pointOffsetBorrowedArithmetic,directZeroControlled,wires_append,Finset.union_subset_iff]
  exact ⟨enter,kernel,leave⟩

theorem pointOffsetBorrowedArithmetic_compact_declared (L : ControlledPointLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) (multiply : Bool) :
    wires (pointOffsetBorrowedArithmetic L multiply)⊆L.compactPointSites.toFinset := by
  apply (pointOffsetBorrowedArithmetic_compact_support L hw hn multiply).trans
  intro q hq
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc] at hq
  simp only [compactPointSites,PointAddLayout.pointWires,inPlaceFlags,List.mem_toFinset,
    List.mem_cons,List.mem_append,List.not_mem_nil,or_false,or_assoc]
  tauto

theorem pointOffsetBorrowedArithmetic_compact_resources (L : ControlledPointLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) (multiply : Bool) :
    wires (pointOffsetBorrowedArithmetic L multiply)⊆L.compactPointSites.toFinset ∧
    L.compactPointSites.Nodup ∧ L.compactPointSites.length=2068 ∧
    qubitCount (pointOffsetBorrowedArithmetic L multiply)≤2068 := by
  have sup := pointOffsetBorrowedArithmetic_compact_declared L hw hn multiply
  have nd := L.compactPointSites_nodup hw hn
  have len := L.compactPointSites_length hw
  refine ⟨sup,nd,len,?_⟩
  unfold qubitCount
  calc
    _ ≤ L.compactPointSites.toFinset.card := Finset.card_le_card sup
    _ = 2068 := by rw [List.toFinset_card_of_nodup nd,len]
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointDialogSupport.lean
noncomputable section

set_option maxHeartbeats 3000000

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

attribute [local irreducible] pointOffsetBorrowedArithmetic directSkywalkArithmetic directZeroControlled
  pointRecoveryConstantAdd compactRecoveryConstant pointRecoveryReflection CompactRecoveryNegateLayout.reflection

theorem dialogPort_wires (L : ControlledPointLayout) (hw : L.Widths) :
    L.dialogPort.wires.toFinset=(L.core.generic::L.point.x++L.point.y++L.dialogPool).toFinset := by
  have hp := DialogLayout.fromPool_wires_perm L.core.poolWire L.core.generic L.point.x L.point.y
    hw.inputX hw.inputY
  rw [L.core.pool_prefix hw 2613 (by omega)] at hp
  exact List.toFinset_eq_of_perm _ _ hp

theorem pointDialogGeneric_small_wires (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) :
    wires (pointDialogGeneric L cx cy)⊆(L.core.generic::L.point.x++L.point.y++L.dialogPool.take 1805).toFinset := by
  let S := (L.core.generic::L.point.x++L.point.y++L.dialogPool.take 1805).toFinset
  have prefixSmall (n : Nat) (hn : n≤1805) : L.dialogPool.take n⊆L.dialogPool.take 1805 := by
    intro q hq
    have e : (L.dialogPool.take 1805).take n=L.dialogPool.take n := by
      rw [List.take_take,Nat.min_eq_left hn]
    rw [←e] at hq
    exact List.mem_of_mem_take hq
  have ca (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y) (k : Fp) :
      wires (pointDialogConstantAdd L r k)⊆S := by
    have sup := pointRecoveryConstantAdd_support L hw r k
    intro q hq
    have h := sup hq
    have p : q∈L.dialogPool.take 515 → q∈L.dialogPool.take 1805 := fun h => prefixSmall 515 (by omega) h
    rcases hr with rfl|rfl
    all_goals simp only [S,List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢;tauto
  have arith (multiply : Bool) : wires (pointOffsetBorrowedArithmetic L multiply)⊆S := by
    have sup := pointOffsetBorrowedArithmetic_compact_support L hw hn multiply
    have pool : L.compactPointPool⊆L.dialogPool.take 1805 := by
      intro q hq
      have whole : L.dialogPool.take 1805=wireBlock L.core.poolWire 0 1805 := by
        rw [L.core.pool_prefix hw 1805 (by omega)]
        simp [dialogPool,List.take_take]
      rw [whole]
      simp only [compactPointPool,List.mem_append] at hq
      rcases hq with hq|hq
      all_goals
        obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
        simp only [List.mem_range'_1] at hi
        exact DirectSkywalk.arith_mem L.core.poolWire 0 1805 i (by omega) (by omega)
    intro q hq
    have h := sup hq
    simp only [S,List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
    have subset : q∈L.compactPointPool → q∈L.dialogPool.take 1805 := fun hq => pool hq
    tauto
  have square : wires (pointDialogSquare L)⊆S := by
    have sup := pointMeasuredSquareCandidate_support L hw hn
    intro q hq
    have h := sup hq
    have p : q∈L.dialogPool.take 776 → q∈L.dialogPool.take 1805 := fun h => prefixSmall 776 (by omega) h
    simp only [S,List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
    tauto
  have recover : wires (pointRecoveryStage L cx cy)⊆S := by
    have reflect := pointRecoveryReflection_support L hw
    have reflS : wires (pointRecoveryReflection L)⊆S := by
      intro q hq
      have h := reflect hq
      have p : q∈L.dialogPool.take 258 → q∈L.dialogPool.take 1805 := fun h => prefixSmall 258 (by omega) h
      simp only [S,List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
      tauto
    simpa only [pointRecoveryStage,wires_append,Finset.union_subset_iff] using
      And.intro (And.intro reflS (ca L.point.x (Or.inl rfl) (cx+1))) (ca L.point.y (Or.inr rfl) (-cy))
  simpa only [pointDialogGeneric,wires_append,Finset.union_subset_iff] using
    And.intro (And.intro (And.intro (And.intro (And.intro (And.intro
      (ca L.point.x (Or.inl rfl) (-cx)) (ca L.point.y (Or.inr rfl) (-cy)))
      (arith false)) square) (ca L.point.x (Or.inl rfl) (3*cx))) (arith true)) recover

theorem pointDialogGeneric_wires (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) :
    wires (pointDialogGeneric L cx cy)⊆(L.core.generic::L.point.x++L.point.y++L.dialogPool).toFinset := by
  apply (pointDialogGeneric_small_wires L hw hn cx cy).trans
  intro q hq
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq ⊢
  have subset : q∈L.dialogPool.take 1805 → q∈L.dialogPool := List.mem_of_mem_take
  tauto

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointDialogWires.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

attribute [local irreducible] pointDialogGeneric

private theorem equalPoint_wires (L : ControlledPointLayout) (hw : L.Widths) (c t : Wire) (C : Point) :
    wires (equalConstant c t L.dialogPointZero (pointCode C))=
      (c::t::PointAddLayout.pointWires L.point++L.dialogPool.take 513).toFinset := by
  rw [equalConstant_wires]
  have hp := zeroPorts_perm (PointAddLayout.pointWires L.point) (L.dialogPool.take 513)
    (by simp [PointAddLayout.pointWires,show L.point.x.length=256 from hw.inputX,
      show L.point.y.length=256 from hw.inputY,L.dialogPool_length hw])
  simp only [dialogPointZero,List.toFinset_cons]
  rw [List.toFinset_eq_of_perm _ _ hp]
  simp only [List.cons_append,List.toFinset_cons]

private theorem genericFlag_wires (L : ControlledPointLayout) : wires (pointInPlaceGenericFlag L)=
    [L.control,L.infinitySelect,L.doubleSelect,L.genericSelect,L.core.generic].toFinset := by
  ext q
  simp only [pointInPlaceGenericFlag,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,
    Finset.mem_singleton,Finset.notMem_empty,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
  tauto

/-- Complete gate support is contained in the original caller footprint. -/
theorem pointDialogFinite_wires (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (C : Point) (cx cy : Fp) :
    wires (pointDialogFinite L C cx cy)⊆L.dialogUsedWires.toFinset := by
  have hG := pointDialogGeneric_wires L hw hn cx cy
  have hGU : wires (pointDialogGeneric L cx cy)⊆L.dialogUsedWires.toFinset := by
    apply hG.trans
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq
    simp only [List.mem_toFinset,dialogUsedWires,inPlaceFlags,PointAddLayout.pointWires,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    rcases hq with ((hg|hx)|hy)|hp
    · subst q; simp
    · simp [hx]
    · simp [hy]
    · simp [hp]
  have hE := equalPoint_wires L hw
  have hB : (L.dialogPool.take 513).toFinset⊆L.dialogUsedWires.toFinset := by
    intro q hq
    have hh := List.take_subset 513 L.dialogPool (List.mem_toFinset.mp hq)
    simp [dialogUsedWires,hh]
  have hM (c : Wire) (hc : c∈L.inPlaceFlags) (P : Point) :
      wires (maskedPointConstant c L.point P)⊆L.dialogUsedWires.toFinset := by
    apply (maskedPointConstant_support _ _ _).trans
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons] at hq
    rcases hq with rfl|hq
    · simp [dialogUsedWires,hc]
    · simp [dialogUsedWires,hq]
  have hO := hM L.infinitySelect (by simp [inPlaceFlags]) C
  have hD := hM L.doubleSelect (by simp [inPlaceFlags]) C
  have hDD := hM L.doubleSelect (by simp [inPlaceFlags]) (C+C)
  have hI := hM L.genericSelect (by simp [inPlaceFlags]) (-C)
  have hHE := hM L.core.equalNegY (by simp [inPlaceFlags]) (dialogExceptionPoint C)
  have hHI := hM L.core.equalNegY (by simp [inPlaceFlags]) (-C)
  have hH : wires (pointInPlaceDoubleEnable L cy)⊆[L.control,L.core.double].toFinset := by
    by_cases hh : cy≠-cy <;> simp [pointInPlaceDoubleEnable,hh,wires,Instr.wires]
  have hEX : wires (pointDialogExceptionEnable L C)⊆[L.control,L.core.equalX].toFinset := by
    unfold pointDialogExceptionEnable
    split <;> simp [wires,Instr.wires]
  have hF := genericFlag_wires L
  rw [pointDialogFinite]
  simp only [wires_append,hE,pointDialogGenericFlag,wires_append,hF,pointDialogCorners,pointInPlaceCorners,wires_append]
  intro q
  have hgu := @hGU q
  have ho := @hO q
  have hd := @hD q
  have hdd := @hDD q
  have hi := @hI q
  have hb := @hB q
  have hh := @hH q
  have hhe := @hHE q
  have hhi := @hHI q
  have hex := @hEX q
  simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,List.mem_toFinset,dialogUsedWires,
    inPlaceFlags,PointAddLayout.pointWires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hgu ho hd hdd hi hb hh hhe hhi hex ⊢
  clear hG hGU hE hB hM hO hD hDD hI hH hHE hHI hEX hF hw
  grind only
/-- Complete gate support is contained in the original caller footprint. -/
theorem pointDialogFinite_small_wires (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (C : Point) (cx cy : Fp) :
    wires (pointDialogFinite L C cx cy)⊆L.skywalkPointUsedWires.toFinset := by
  have hG := pointDialogGeneric_small_wires L hw hn cx cy
  have hGU : wires (pointDialogGeneric L cx cy)⊆L.skywalkPointUsedWires.toFinset := by
    apply hG.trans
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq
    simp only [List.mem_toFinset,skywalkPointUsedWires,inPlaceFlags,PointAddLayout.pointWires,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    rcases hq with ((hg|hx)|hy)|hp
    · subst q; simp
    · simp [hx]
    · simp [hy]
    · simp [hp]
  have hE := equalPoint_wires L hw
  have hB : (L.dialogPool.take 513).toFinset⊆L.skywalkPointUsedWires.toFinset := by
    intro q hq
    have he : (L.dialogPool.take 1805).take 513=L.dialogPool.take 513 := by
      simp only [List.take_take,Nat.min_eq_left (show 513≤1805 by omega)]
    have hm := List.mem_toFinset.mp hq
    rw [←he] at hm
    have hh := List.take_subset 513 (L.dialogPool.take 1805) hm
    simp [skywalkPointUsedWires,hh]
  have hM (c : Wire) (hc : c∈L.inPlaceFlags) (P : Point) :
      wires (maskedPointConstant c L.point P)⊆L.skywalkPointUsedWires.toFinset := by
    apply (maskedPointConstant_support _ _ _).trans
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons] at hq
    rcases hq with rfl|hq
    · simp [skywalkPointUsedWires,hc]
    · simp [skywalkPointUsedWires,hq]
  have hO := hM L.infinitySelect (by simp [inPlaceFlags]) C
  have hD := hM L.doubleSelect (by simp [inPlaceFlags]) C
  have hDD := hM L.doubleSelect (by simp [inPlaceFlags]) (C+C)
  have hI := hM L.genericSelect (by simp [inPlaceFlags]) (-C)
  have hHE := hM L.core.equalNegY (by simp [inPlaceFlags]) (dialogExceptionPoint C)
  have hHI := hM L.core.equalNegY (by simp [inPlaceFlags]) (-C)
  have hH : wires (pointInPlaceDoubleEnable L cy)⊆[L.control,L.core.double].toFinset := by
    by_cases hh : cy≠-cy <;> simp [pointInPlaceDoubleEnable,hh,wires,Instr.wires]
  have hEX : wires (pointDialogExceptionEnable L C)⊆[L.control,L.core.equalX].toFinset := by
    unfold pointDialogExceptionEnable
    split <;> simp [wires,Instr.wires]
  have hF := genericFlag_wires L
  rw [pointDialogFinite]
  simp only [wires_append,hE,pointDialogGenericFlag,wires_append,hF,pointDialogCorners,pointInPlaceCorners,wires_append]
  intro q
  have hgu := @hGU q
  have ho := @hO q
  have hd := @hD q
  have hdd := @hDD q
  have hi := @hI q
  have hb := @hB q
  have hh := @hH q
  have hhe := @hHE q
  have hhi := @hHI q
  have hex := @hEX q
  simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,List.mem_toFinset,skywalkPointUsedWires,
    inPlaceFlags,PointAddLayout.pointWires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hgu ho hd hdd hi hb hh hhe hhi hex ⊢
  clear hG hGU hE hB hM hO hD hDD hI hH hHE hHI hEX hF hw
  grind only

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/CompressedPointDialogResources.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.CompressedPointDialog
open ControlledPointLayout Secp256k1 MappedCompressed
attribute [local irreducible] wires pointCompressedArithmetic CompressedPointSquare.computableProgram
  pointRecoveryConstantAdd pointRecoveryReflection compactRecoveryConstant
  CompactRecoveryNegateLayout.reflection

def sites (L : ControlledPointLayout) : List Wire :=
  CompressedPointSquare.residents L++CompressedPointSquare.sharedPool L

theorem prefix_small (L : ControlledPointLayout) (hw : L.Widths) (n : Nat) (hn : n ≤ 515) :
    L.dialogPool.take n ⊆ CompressedPointSquare.sharedPool L := by
  have pref : (L.dialogPool.take 515).take n=L.dialogPool.take n := by
    rw [List.take_take,Nat.min_eq_left hn]
  have whole : L.dialogPool.take 515=wireBlock L.core.poolWire 0 515 := by
    simp only [dialogPool,List.take_take,Nat.min_eq_left (show 515 ≤ 2613 by omega)]
    exact (L.core.pool_prefix hw 515 (by omega)).symm
  intro q hq
  rw [←pref] at hq
  have mem := List.mem_of_mem_take hq
  rw [whole] at mem
  exact List.mem_append_left _ (List.mem_append_left _ mem)

theorem generic_support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (cx cy : Fp) :
    wires (pointCompressedDialogGeneric L cx cy)⊆(sites L).toFinset := by
  have ca (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y) (k : Fp) :
      wires (pointDialogConstantAdd L r k)⊆(sites L).toFinset := by
    have sup := pointRecoveryConstantAdd_support L hw r k
    intro q hq
    have h := sup hq
    have small := prefix_small L hw 515 (Nat.le_refl 515)
    rcases hr with rfl|rfl
    all_goals
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h
      simp only [sites,CompressedPointSquare.residents,PointAddLayout.pointWires,inPlaceFlags,
        List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false]
      have p : q∈L.dialogPool.take 515 → q∈CompressedPointSquare.sharedPool L := fun h => small h
      tauto
  have arith (b : Bool) := pointCompressedArithmetic_support L hw b
  have square := CompressedPointSquare.computable_support L hw hn
  have recover := pointRecoveryStage_support L hw cx cy
  have recovery : wires (pointRecoveryStage L cx cy)⊆(sites L).toFinset := by
    intro q hq
    have h := List.mem_toFinset.mp (recover hq)
    have p := prefix_small L hw 515 (Nat.le_refl 515)
    simp only [recoveryStageSites,List.mem_append] at h
    simp only [sites,CompressedPointSquare.residents,List.mem_toFinset,List.mem_append]
    tauto
  simpa only [pointCompressedDialogGeneric,wires_append,Finset.union_subset_iff,sites] using
    And.intro (And.intro (And.intro (And.intro (And.intro (And.intro
      (ca L.point.x (Or.inl rfl) (-cx)) (ca L.point.y (Or.inr rfl) (-cy)))
      (arith false)) square) (ca L.point.x (Or.inl rfl) (3*cx))) (arith true)) recovery

theorem generic_counts (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (cx cy : Fp) :
    toffoliCount (pointCompressedDialogGeneric L cx cy)=2213282 ∧
    measurementCount (pointCompressedDialogGeneric L cx cy)=1553824 := by
  have a k := pointDialogConstantAdd_counts L hw hn L.point.x (Or.inl rfl) k
  have b k := pointDialogConstantAdd_counts L hw hn L.point.y (Or.inr rfl) k
  have arith := pointCompressedArithmetic_counts L
  have square := CompressedPointSquare.counts L hw
  have recovery := pointRecoveryStage_counts L hw cx cy
  simp only [pointCompressedDialogGeneric,toffoliCount_append,measurementCount_append,
    (a _).1,(a _).2,(b _).1,(b _).2,arith.1,arith.2.1,arith.2.2.1,arith.2.2.2,
    square.1,square.2,recovery.1,recovery.2]
  norm_num

theorem finite_counts (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (C : Point) (cx cy : Fp) :
    toffoliCount (pointCompressedDialogFinite L C cx cy)=2217386 ∧
    measurementCount (pointCompressedDialogFinite L C cx cy)=1557928 := by
  have hg := generic_counts L hw hn cx cy
  have hz c t k := equalConstant_counts c t L.dialogPointZero k
  have hpl : (PointAddLayout.pointWires L.point).length=513 := by
    simp only [PointAddLayout.pointWires,List.length_cons,List.length_append,
      show L.point.x.length=256 from hw.inputX,show L.point.y.length=256 from hw.inputY]
  have hzl : L.dialogPointZero.length=513 := by
    have he := (zeroPorts_maps (PointAddLayout.pointWires L.point) (L.dialogPool.take 513)
      (by simp only [List.length_take,L.dialogPool_length hw]; exact hpl)).1
    simpa only [List.length_map,hpl] using congrArg List.length he
  have he : toffoliCount (pointInPlaceDoubleEnable L cy)=0 ∧
      measurementCount (pointInPlaceDoubleEnable L cy)=0 := by
    unfold pointInPlaceDoubleEnable
    split <;> simp [toffoliCount,measurementCount]
  have hh : toffoliCount (pointDialogExceptionEnable L C)=0 ∧
      measurementCount (pointDialogExceptionEnable L C)=0 := by
    unfold pointDialogExceptionEnable
    split <;> simp [toffoliCount,measurementCount]
  simp only [pointCompressedDialogFinite,pointDialogCorners,pointInPlaceCorners,toffoliCount_append,
    measurementCount_append,hg.1,hg.2,(hz _ _ _).1,(hz _ _ _).2,hzl,
    (maskedPointConstant_counts _ _ _).1,(maskedPointConstant_counts _ _ _).2,he.1,he.2,hh.1,hh.2]
  norm_num [pointDialogGenericFlag,pointInPlaceGenericFlag,toffoliCount,measurementCount]

private theorem equalPoint_wires (L : ControlledPointLayout) (hw : L.Widths) (c t : Wire) (C : Point) :
    wires (equalConstant c t L.dialogPointZero (pointCode C))=
      (c::t::PointAddLayout.pointWires L.point++L.dialogPool.take 513).toFinset := by
  rw [equalConstant_wires]
  have hp := zeroPorts_perm (PointAddLayout.pointWires L.point) (L.dialogPool.take 513)
    (by simp [PointAddLayout.pointWires,show L.point.x.length=256 from hw.inputX,
      show L.point.y.length=256 from hw.inputY,L.dialogPool_length hw])
  simp only [dialogPointZero,List.toFinset_cons]
  rw [List.toFinset_eq_of_perm _ _ hp]
  simp only [List.cons_append,List.toFinset_cons]

private theorem genericFlag_wires (L : ControlledPointLayout) : wires (pointInPlaceGenericFlag L)=
    [L.control,L.infinitySelect,L.doubleSelect,L.genericSelect,L.core.generic].toFinset := by
  ext q
  simp only [pointInPlaceGenericFlag,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,
    Finset.mem_singleton,Finset.notMem_empty,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
  tauto

theorem finite_support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (C : Point) (cx cy : Fp) :
    wires (pointCompressedDialogFinite L C cx cy)⊆(sites L).toFinset := by
  have hGU := generic_support L hw hn cx cy
  have hE := equalPoint_wires L hw
  have hB : (L.dialogPool.take 513).toFinset⊆(sites L).toFinset := by
    intro q hq
    have hm := prefix_small L hw 513 (by omega) (List.mem_toFinset.mp hq)
    simp [sites,CompressedPointSquare.residents,hm]
  have hM (c : Wire) (hc : c∈L.inPlaceFlags) (P : Point) :
      wires (maskedPointConstant c L.point P)⊆(sites L).toFinset := by
    apply (maskedPointConstant_support _ _ _).trans
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons] at hq
    rcases hq with rfl|hq
    · simp [sites,CompressedPointSquare.residents,hc]
    · simp [sites,CompressedPointSquare.residents,hq]
  have hO := hM L.infinitySelect (by simp [inPlaceFlags]) C
  have hD := hM L.doubleSelect (by simp [inPlaceFlags]) C
  have hDD := hM L.doubleSelect (by simp [inPlaceFlags]) (C+C)
  have hI := hM L.genericSelect (by simp [inPlaceFlags]) (-C)
  have hHE := hM L.core.equalNegY (by simp [inPlaceFlags]) (dialogExceptionPoint C)
  have hHI := hM L.core.equalNegY (by simp [inPlaceFlags]) (-C)
  have hH : wires (pointInPlaceDoubleEnable L cy)⊆[L.control,L.core.double].toFinset := by
    by_cases hh : cy≠-cy <;> simp [pointInPlaceDoubleEnable,hh,wires,Instr.wires]
  have hEX : wires (pointDialogExceptionEnable L C)⊆[L.control,L.core.equalX].toFinset := by
    unfold pointDialogExceptionEnable
    split <;> simp [wires,Instr.wires]
  have hF := genericFlag_wires L
  rw [pointCompressedDialogFinite]
  simp only [wires_append,hE,pointDialogGenericFlag,wires_append,hF,pointDialogCorners,pointInPlaceCorners,wires_append]
  intro q
  have hgu := @hGU q
  have ho := @hO q
  have hd := @hD q
  have hdd := @hDD q
  have hi := @hI q
  have hb := @hB q
  have hh := @hH q
  have hhe := @hHE q
  have hhi := @hHI q
  have hex := @hEX q
  simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,List.mem_toFinset,sites,CompressedPointSquare.residents,
    inPlaceFlags,PointAddLayout.pointWires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hgu ho hd hdd hi hb hh hhe hhi hex ⊢
  clear hGU hE hB hM hO hD hDD hI hH hHE hHI hEX hF hw
  grind only

theorem sites_subset (L : ControlledPointLayout) (hw : L.Widths) : sites L⊆L.dialogUsedWires := by
  intro q hq
  simp only [sites,List.mem_append] at hq
  rcases hq with res|pool
  · exact List.mem_append_left _ res
  · have mem : q∈L.dialogPool := by
      simp only [CompressedPointSquare.sharedPool,List.mem_append] at pool
      rcases pool with (pool|pool)|pool
      all_goals
        obtain ⟨i,hi,rfl⟩ := List.mem_map.mp pool
        simp only [List.mem_range'_1] at hi
        change L.core.poolWire i∈L.core.pool.take 2613
        rw [←L.core.pool_prefix hw 2613 (by omega)]
        exact List.mem_map.mpr ⟨i,by simp [List.mem_range'_1];omega,rfl⟩
    exact List.mem_append_right _ mem

theorem finite_wires (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (C : Point) (cx cy : Fp) :
    wires (pointCompressedDialogFinite L C cx cy)⊆L.dialogUsedWires.toFinset := by
  apply (finite_support L hw hn C cx cy).trans
  intro q hq
  exact List.mem_toFinset.mpr (sites_subset L hw (List.mem_toFinset.mp hq))

theorem finite_qubits (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (C : Point) (cx cy : Fp) :
    qubitCount (pointCompressedDialogFinite L C cx cy) ≤ 1899 := by
  have length : (sites L).length=1899 := by
    rw [sites,List.length_append,CompressedPointSquare.residents_length L hw,CompressedPointSquare.sharedPool_length]
  change (wires (pointCompressedDialogFinite L C cx cy)).card ≤ 1899
  exact (Finset.card_le_card (finite_support L hw hn C cx cy)).trans ((List.toFinset_card_le _).trans_eq length)

end ECDSAAdd.Arithmetic.CompressedPointDialog
end

-- source: ECDSAAdd/Arithmetic/CompressedPointDialogSteps.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Arithmetic.CompressedPointDialog
open ControlledPointLayout Secp256k1 MappedCompressed
attribute [local irreducible] run pointCompressedArithmetic CompressedPointSquare.computableProgram
  pointMeasuredSquareCandidate

theorem step_square (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (base : BasisState) :
    Triple (PointDialogValues L X Y G base) (CompressedPointSquare.computableProgram L)
      (PointDialogValues L (X-(if G then Y*Y else 0)) Y G base) := by
  intro s m v
  rw [CompressedPointSquare.state_eq L hw hn X.val Y.val G X.isLt s m
    v.generic v.x v.y v.clean]
  simpa only [pointDialogSquare] using dialogStep_square L hw hn X Y G base s m v

theorem step_arithmetic (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (base : BasisState) (multiply : Bool) (hX : G=true → X≠0) :
    Triple (PointDialogValues L X Y G base) (pointCompressedArithmetic L multiply)
      (PointDialogValues L X (if G then (if multiply then Y*X else Y/X) else Y) G base) := by
  intro s m v
  have hX0 : G=true → X.val≠0 := by
    intro hg hx
    apply hX hg
    apply ZMod.val_injective p
    simpa using hx
  obtain ⟨phase,value,rest⟩ := pointCompressedArithmetic_correct L hw hn multiply
    X.val Y.val G X.isLt hX0 Y.isLt s m v.generic v.x v.y v.clean
  refine ⟨phase,v.withY hn ?_ rest⟩
  cases G <;> cases multiply <;>
    simpa only [Bool.false_eq_true,if_false,if_true,ZMod.natCast_zmod_val] using value

theorem generic_true (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y cx cy : Fp) (base : BasisState) (hX : X≠cx) (hd : cx-genericX X Y cx cy≠0) :
    Triple (PointDialogValues L X Y true base) (pointCompressedDialogGeneric L cx cy)
      (PointDialogValues L (genericX X Y cx cy) (genericY X Y cx cy) true base) := by
  let a := genericSlope X Y cx cy
  let d := cx-genericX X Y cx cy
  have hv := generic_inplace_values X Y cx cy hX
  have h1 := dialogStep_addX L hw hn X Y true base (-cx)
  have h2 := dialogStep_addY L hw hn (X-cx) Y true base (-cy)
  simp only [if_true,←sub_eq_add_neg] at h1 h2
  have h3 := step_arithmetic L hw hn (X-cx) (Y-cy) true base false (fun _=>sub_ne_zero.mpr hX)
  have ha : (Y-cy)/(X-cx)=a := rfl
  simp only [if_true,Bool.false_eq_true,if_false,ha] at h3
  have h4 := step_square L hw hn (X-cx) a true base
  simp only [if_true] at h4
  have h5 := dialogStep_addX L hw hn ((X-cx)-a*a) a true base (3*cx)
  simp only [if_true] at h5
  rw [show (X-cx)-a*a+3*cx=d from hv.2.1] at h5
  have h6 := step_arithmetic L hw hn d a true base true (fun _=>hd)
  simp only [if_true] at h6
  have recovery := pointRecoveryStage_correct L hw hn d (a*d) cx cy true base
  simp only [if_true] at recovery
  rw [show cx-d=genericX X Y cx cy by dsimp [d];ring] at recovery
  rw [show a*d-cy=genericY X Y cx cy from hv.2.2] at recovery
  have h := (((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq recovery
  simpa only [pointCompressedDialogGeneric,List.append_assoc] using h

theorem generic_false (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y cx cy : Fp) (base : BasisState) :
    Triple (PointDialogValues L X Y false base) (pointCompressedDialogGeneric L cx cy)
      (PointDialogValues L X Y false base) := by
  have h1 := dialogStep_addX L hw hn X Y false base (-cx)
  have h2 := dialogStep_addY L hw hn X Y false base (-cy)
  have h3 := step_arithmetic L hw hn X Y false base false (by simp)
  have h4 := step_square L hw hn X Y false base
  have h5 := dialogStep_addX L hw hn X Y false base (3*cx)
  have h6 := step_arithmetic L hw hn X Y false base true (by simp)
  have recovery := pointRecoveryStage_correct L hw hn X Y cx cy false base
  simp only [Bool.false_eq_true,if_false,if_true,add_zero,sub_zero] at h1 h2 h3 h4 h5 h6 recovery
  have h := (((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq recovery
  simpa only [pointCompressedDialogGeneric,List.append_assoc] using h


theorem boundary_generic (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) (b : Bool) (f : BasisState) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (hg : f L.core.generic=true → R≠0 ∧ R≠(.some hc : Point) ∧ R≠-(.some hc : Point) ∧
      R≠dialogExceptionPoint (.some hc)) :
    Triple (PointDialogBoundary L R b f) (pointCompressedDialogGeneric L cx cy)
      (PointDialogBoundary L (if f L.core.generic then R+.some hc else R) b f) := by
  intro s m v
  have hp := (point_holds _ _ _).mp v.point
  have values : PointDialogValues L ((coordinates R).getD (0,0)).1
      ((coordinates R).getD (0,0)).2 (f L.core.generic) s.basis s.basis :=
    ⟨hp.2.1,hp.2.2,v.flags _ (by simp [inPlaceFlags]),v.clean,fun _ _=>rfl⟩
  have hfinite : L.point.finite∉L.point.x++L.point.y := by
    intro hh
    have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) L.point.finite
    have ht := List.count_pos_iff.mpr hh
    simp only [dialogUsedWires,PointAddLayout.pointWires,List.count_append,List.count_cons,
      beq_self_eq_true,if_true] at h ht
    omega
  have outside (q : Wire) (hq : q∉PointAddLayout.pointWires L.point) : q∉L.point.x++L.point.y := by
    simp only [PointAddLayout.pointWires,List.mem_append,List.mem_cons,not_or] at hq ⊢
    exact ⟨hq.1.2,hq.2⟩
  cases hG : f L.core.generic with
  | false =>
    rw [hG] at values
    obtain ⟨phase,hv⟩ := generic_false L hw hn _ _ cx cy s.basis s m values
    refine ⟨phase,v.withPoint hn ?_ (fun q hq=>hv.rest q (outside q hq))⟩
    simp only [Bool.false_eq_true,if_false]
    exact (point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1,hv.x,hv.y⟩
  | true =>
    have he := hg hG
    cases R with
    | zero => exact False.elim (he.1 rfl)
    | @some x y hr =>
      have den := dialog_denominators_ne_zero hr hc he.2.1 he.2.2.1 he.2.2.2
      rw [hG] at values
      obtain ⟨phase,hv⟩ := generic_true L hw hn x y cx cy s.basis den.1 den.2 s m values
      refine ⟨phase,v.withPoint hn ?_ (fun q hq=>hv.rest q (outside q hq))⟩
      simp only [if_true,←genericAdd_correct hr hc den.1,genericAdd]
      exact (point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1,hv.x,hv.y⟩

end ECDSAAdd.Arithmetic.CompressedPointDialog
end

-- source: ECDSAAdd/Arithmetic/CompressedPointDialogSpec.lean
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.CompressedPointDialog
open ControlledPointLayout Secp256k1
attribute [local irreducible] run wires pointCompressedDialogGeneric pointDialogGeneric
  MappedCompressed.pointCompressedArithmetic CompressedPointSquare.computableProgram

private theorem equal_simp [DecidableEq Point] (R C : Point) : pointEqual R C=decide (R=C) := by
  simp only [pointEqual,pointCode_injective.eq_iff]

theorem finite_spec (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) :
    Triple (PointDialogBoundary L R b (fun _=>false)) (pointCompressedDialogFinite L (.some hc) cx cy)
      (PointDialogBoundary L (if b then R+.some hc else R) b (fun _=>false)) := by
  classical
  let C : Point := .some hc
  let O := dialogInfinity b R
  let D := dialogDouble b R C
  let I := dialogInversePoint b R C
  let H := dialogException b R C
  let G := dialogOrdinary b R C
  let E := b && decide (dialogExceptionEnabled C)
  let K := b && decide (cy≠-cy)
  let S := if b then R+C else R
  have hC : C≠0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  have hK : K=(b && decide (C≠-C)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [K,Bool.and_eq_true,decide_eq_true_eq]
    exact and_congr_right (fun _=>doubling_enabled_iff hc)
  have hE : (!pointEqual (dialogExceptionPoint C) 0 && !pointEqual (dialogExceptionPoint C) C &&
      !pointEqual (dialogExceptionPoint C) (-C))=decide (dialogExceptionEnabled C) := by
    simp [equal_simp,dialogExceptionEnabled,Bool.and_assoc]
  have hO : (b && pointEqual R 0)=O := by simp only [O,dialogInfinity,equal_simp]
  have hD : (K && pointEqual R C)=D := by rw [hK]; simp only [D,dialogDouble,equal_simp]
  have hI : (b && pointEqual R (-C))=I := by simp only [I,dialogInversePoint,equal_simp]
  have hH : (E && pointEqual R (dialogExceptionPoint C))=H := by
    simp [E,H,dialogException,dialogExceptionEnabled,equal_simp]
  have h0 := dialogFlag_doubleEnable L hn R b false false false false false false false cy
  simp only [Bool.false_xor] at h0
  have h1 := dialogFlag_exceptionEnable L hn R b false false false false false false K C
  rw [hE,Bool.false_xor] at h1
  have h2 := dialogFlag_equalO L hw hn R 0 b false false false false E false K
  rw [hO,Bool.false_xor] at h2
  have h3 := dialogFlag_equalD L hw hn R C b O false false false E false K
  rw [hD,Bool.false_xor] at h3
  have h4 := dialogFlag_equalI L hw hn R (-C) b O D false false E false K
  rw [hI,Bool.false_xor] at h4
  have h5 := dialogFlag_equalH L hw hn R (dialogExceptionPoint C) b O D I false E false K
  rw [hH,Bool.false_xor] at h5
  have h6 := dialogFlag_generic L hw hn R b O D I false E H K
  simp only [Bool.false_xor] at h6
  have read := dialogFlagState_read L hn O D I G E H K
  have h7 := boundary_generic L hw hn R b (dialogFlagState L O D I G E H K) hc
    (fun hg => ((dialogOrdinary_true b R C hC).mp (read.2.2.2.1.symm.trans hg)).2)
  rw [read.2.2.2.1] at h7
  have h8 := dialogBoundary_corners L hw hn R C hC b (dialogFlagState L O D I G E H K)
    read.1 read.2.1 read.2.2.1 read.2.2.2.2.2.1
  have h9 := dialogFlag_generic L hw hn S b O D I G E H K
  have hgclear : (((((G ^^ b) ^^ O) ^^ D) ^^ I) ^^ H)=false := by
    dsimp only [G,dialogOrdinary,O,D,I,H]
    generalize dialogInfinity b R=o,dialogDouble b R C=d,dialogInversePoint b R C=i,
      dialogException b R C=h
    cases b <;> cases o <;> cases d <;> cases i <;> cases h <;> rfl
  rw [hgclear] at h9
  have hf := dialogFlags_output b R C
  have h10 := dialogFlag_equalO L hw hn S C b O D I false E H K
  simp only [equal_simp] at h10
  rw [hf.1,Bool.xor_self] at h10
  have h11 := dialogFlag_equalD L hw hn S (C+C) b false D I false E H K
  have hdo : (K && pointEqual S (C+C))=D := by
    rw [hK]; simpa only [equal_simp] using hf.2.1
  rw [hdo,Bool.xor_self] at h11
  have h12 := dialogFlag_equalI L hw hn S 0 b false false I false E H K
  simp only [equal_simp] at h12
  rw [hf.2.2.1,Bool.xor_self] at h12
  have h13 := dialogFlag_equalH L hw hn S (-C) b false false false false E H K
  have heout : (E && pointEqual S (-C))=H := by
    simpa [E,H,S,dialogExceptionEnabled,equal_simp] using hf.2.2.2
  rw [heout,Bool.xor_self] at h13
  have h14 := dialogFlag_exceptionEnable L hn S b false false false false E false K C
  rw [hE,show (E ^^ (b && decide (dialogExceptionEnabled C)))=false from Bool.xor_self E] at h14
  have h15 := dialogFlag_doubleEnable L hn S b false false false false false false K cy
  rw [show (K ^^ (b && decide (cy≠-cy)))=false from Bool.xor_self K] at h15
  have h := ((((((((((((((h0.seq h1).seq h2).seq h3).seq h4).seq h5).seq h6).seq h7).seq h8).seq h9).seq h10).seq h11).seq h12).seq h13).seq h14).seq h15
  simpa only [pointCompressedDialogFinite,List.append_assoc,dialogFlagState_zero] using h


private theorem shared_subset (L : ControlledPointLayout) (hw : L.Widths) :
    CompressedPointSquare.residents L++CompressedPointSquare.sharedPool L ⊆ L.dialogUsedWires := by
  intro q hq
  rcases List.mem_append.mp hq with res|pool
  · exact List.mem_append_left _ res
  · have mem : q∈L.dialogPool := by
      simp only [CompressedPointSquare.sharedPool,List.mem_append] at pool
      rcases pool with (pool|pool)|pool
      all_goals
        obtain ⟨i,hi,rfl⟩ := List.mem_map.mp pool
        simp only [List.mem_range'_1] at hi
        change L.core.poolWire i∈L.core.pool.take 2613
        rw [←L.core.pool_prefix hw 2613 (by omega)]
        exact List.mem_map.mpr ⟨i,by simp [List.mem_range'_1];omega,rfl⟩
    exact List.mem_append_right _ mem

private theorem generic_used (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (cx cy : Fp) :
    wires (pointCompressedDialogGeneric L cx cy)⊆L.dialogUsedWires.toFinset := by
  have old := pointDialogGeneric_wires L hw hn cx cy
  have embed : (L.core.generic::L.point.x++L.point.y++L.dialogPool).toFinset⊆L.dialogUsedWires.toFinset := by
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq
    simp only [dialogUsedWires,PointAddLayout.pointWires,inPlaceFlags,List.mem_toFinset,
      List.mem_cons,List.mem_append,List.not_mem_nil,or_false]
    tauto
  have original := old.trans embed
  have common : (CompressedPointSquare.residents L++CompressedPointSquare.sharedPool L).toFinset⊆
      L.dialogUsedWires.toFinset := by
    intro q hq
    exact List.mem_toFinset.mpr (shared_subset L hw (List.mem_toFinset.mp hq))
  have div := (MappedCompressed.pointCompressedArithmetic_support L hw false).trans common
  have mul := (MappedCompressed.pointCompressedArithmetic_support L hw true).trans common
  have square := (CompressedPointSquare.computable_support L hw hn).trans common
  intro q hq
  have ho := @original q
  have hd := @div q
  have hm := @mul q
  have hs := @square q
  simp only [pointCompressedDialogGeneric,pointDialogGeneric,wires_append,Finset.mem_union] at hq ho
  tauto

private theorem finite_wires_CompressedPointDialogSpec (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (cx cy : Fp) : wires (pointCompressedDialogFinite L C cx cy)⊆L.dialogUsedWires.toFinset := by
  have old := pointDialogFinite_wires L hw hn C cx cy
  have generic := generic_used L hw hn cx cy
  intro q hq
  have ho := @old q
  have hg := @generic q
  simp only [pointCompressedDialogFinite,pointDialogFinite,wires_append,Finset.mem_union] at hq ho
  tauto

private theorem boundary_frame_values (L : ControlledPointLayout) (P : Program)
    (hP : wires P⊆L.dialogUsedWires.toFinset) (R R' : Point) (b : Bool) (s : State) (m : List Bool)
    (hi : PointDialogBoundary L R b (fun _ => false) s.basis)
    (ho : PointDialogBoundary L R' b (fun _ => false) (run P m s).basis)
    (q : Wire) (hp : q∉PointAddLayout.pointWires L.point) : (run P m s).basis q=s.basis q := by
  by_cases hc : q=L.control
  · subst q; exact ho.control.trans hi.control.symm
  by_cases hf : q∈L.inPlaceFlags
  · exact (ho.flags q hf).trans (hi.flags q hf).symm
  by_cases hw : q∈L.dialogPool
  · exact (regValue_eq_iff _ _ _).mp (ho.clean.trans hi.clean.symm) q hw
  apply run_preserves_outside
  apply mt (@hP q)
  simp [dialogUsedWires,hp,hc,hf,hw]

theorem finite_frame (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (s : State) (m : List Bool)
    (hi : PointDialogBoundary L R b (fun _ => false) s.basis)
    (q : Wire) (hq : q∉PointAddLayout.pointWires L.point) :
    (run (pointCompressedDialogFinite L (.some hc) cx cy) m s).basis q=s.basis q := by
  have ho := (finite_spec L hw hn R hc b s m hi).2
  exact boundary_frame_values L _ (finite_wires_CompressedPointDialogSpec L hw hn (.some hc) cx cy) R _ b s m hi ho q hq

private theorem boundary_work_subset (L : ControlledPointLayout) :
    L.inPlaceFlags++L.dialogPool ⊆ L.work := by
  intro q hq
  have h1 := List.count_pos_iff.mpr hq
  have ht := (List.take_sublist 2613 L.core.pool).count_le q
  apply List.count_pos_iff.mp
  simp only [dialogPool,List.count_append] at h1
  simp only [work,outWork,temporary,inPlaceFlags,selectors,PointAddLayout.work,PointAddLayout.words,
    PointAddLayout.flags,List.flatten_cons,List.flatten_nil,List.append_nil,List.count_append,List.count_cons,List.count_nil] at h1 ht ⊢
  omega

private theorem work_not_point (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.work) : q∉PointAddLayout.pointWires L.point := by
  intro hp
  have hh := List.nodup_iff_count.mp hn q
  have h1 := List.count_pos_iff.mpr hq
  have h2 := List.count_pos_iff.mpr hp
  simp only [ControlledPointLayout.wires,work,outWork,temporary,point,extras,selectors,PointAddLayout.wires,
    List.count_append,List.count_cons,List.count_nil] at hh h1 h2
  omega

/-- 公共布局的全部分配工作位恢复为零，包括本实现未使用的旧银行。 -/
theorem full_spec (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) :
    (Triple (fun st => (Holds.holds st L.control b ∧ Holds.holds st L.point R) ∧ Holds.holds st L.work 0) (pointCompressedDialogFinite L (.some hc) cx cy)
      (fun st => (Holds.holds st L.control b ∧ Holds.holds st L.point (if b then R+.some hc else R)) ∧ Holds.holds st L.work 0)) := by
  intro s m hs
  have hz : regValue L.work s.basis=0 := hs.2
  have clean (q : Wire) (hq : q∈L.inPlaceFlags++L.dialogPool) : s.basis q=false :=
    (regValue_zero _ _).mp hz q (boundary_work_subset L hq)
  have hi : PointDialogBoundary L R b (fun _ => false) s.basis := by
    refine ⟨hs.1.2,hs.1.1,fun q hq => clean q (by simp [hq]),?_⟩
    · exact (regValue_zero _ _).mpr (fun q hq => clean q (by simp [hq]))
  obtain ⟨hp,ho⟩ := finite_spec L hw hn R hc b s m hi
  refine ⟨hp,⟨ho.control,ho.point⟩,?_⟩
  apply (regValue_zero _ _).mpr
  intro q hq
  rw [finite_frame L hw hn R hc b s m hi q (work_not_point L hn q hq)]
  exact (regValue_zero _ _).mp hz q hq

/-- All valid points and all constants, including infinity and exceptional
branches; original work and control contracts and arbitrary phase retained. -/
theorem add_spec (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (b : Bool) (R C : Point) :
    (Triple (fun st => (Holds.holds st L.control b ∧ Holds.holds st L.point R) ∧ Holds.holds st L.work 0) (pointCompressedAdd L C)
      (fun st => (Holds.holds st L.control b ∧ Holds.holds st L.point (if b then R+C else R)) ∧ Holds.holds st L.work 0)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [pointCompressedAdd,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self] using And.intro (Eq.refl s.phase) hs
  | some hc => exact full_spec L hw hn R hc b

end ECDSAAdd.Arithmetic.CompressedPointDialog
end

-- source: ECDSAAdd/Arithmetic/ControlledPointLayout.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Secp256k1


/-- 控制只进入三个最终输出标志，候选算术及测量序列不依赖控制值。 -/
def pointSelectors (L : ControlledPointLayout) : Program :=
  [.CCX L.control L.core.generic L.genericSelect,
   .CCX L.control L.core.double L.doubleSelect,
   .X L.core.input.finite,.CCX L.control L.core.input.finite L.infinitySelect,.X L.core.input.finite]

def selectedPointOutput (L : ControlledPointLayout) (C : Point) : Program :=
  pointGenericOutput L.selected++maskedPointConstant L.doubleSelect L.core.output (C+C)++
    maskedPointConstant L.infinitySelect L.core.output C

def controlledPointOutput (L : ControlledPointLayout) (C : Point) : Program :=
  pointSelectors L++selectedPointOutput L C++pointSelectors L

/-- 控制为假的分支也计算并清理候选，只抑制最终输出。 -/
def controlledPointAddOut (L : ControlledPointLayout) (C : Point) : Program :=
  match C with
  | .zero => copyRegister (some L.control) (PointAddLayout.pointWires L.core.input)
      (PointAddLayout.pointWires L.core.output)
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
    pointFlagsCompute L.core cx cy++pointCandidateCompute L.core cx cy++controlledPointOutput L C++
      pointCandidateClear L.core cx cy++pointFlagsClear L.core cx cy

/-- 除法中心原地点加；有限常量执行固定门列，C=O时构造为空。 -/
def controlledPointAdd (L : ControlledPointLayout) (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ => pointCompressedDialogFinite L C cx cy

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointSelectors.lean
noncomputable section

namespace ECDSAAdd.Arithmetic

def selectorState (L : ControlledPointLayout) (s : BasisState) (G D O : Bool) : BasisState :=
  writeBit (writeBit (writeBit s L.genericSelect G) L.doubleSelect D) L.infinitySelect O

theorem ControlledPointLayout.selector_nodup (L : ControlledPointLayout) (hn : L.wires.Nodup) :
    [L.control,L.core.generic,L.core.double,L.core.input.finite,
      L.genericSelect,L.doubleSelect,L.infinitySelect].Nodup := by
  apply List.nodup_iff_count.mpr; intro w
  have hh := List.nodup_iff_count.mp hn w
  simp only [ControlledPointLayout.wires,ControlledPointLayout.extras,ControlledPointLayout.selectors,
    PointAddLayout.wires,PointAddLayout.pointWires,PointAddLayout.work,PointAddLayout.flags,
    List.count_append,List.count_cons,List.count_nil] at hh ⊢
  omega

theorem pointSelectors_correct (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (s : State) (m : List Bool) :
    run (pointSelectors L) m s=⟨s.phase,selectorState L s.basis
      (s.basis L.genericSelect ^^ (s.basis L.control && s.basis L.core.generic))
      (s.basis L.doubleSelect ^^ (s.basis L.control && s.basis L.core.double))
      (s.basis L.infinitySelect ^^ (s.basis L.control && !s.basis L.core.input.finite))⟩ := by
  have hh := L.selector_nodup hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,
    List.nodup_nil,not_false_eq_true,and_true] at hh
  rcases hh with ⟨⟨hbg,hbd,hbf,hbG,hbD,hbO⟩,⟨hgd,hgf,hgG,hgD,hgO⟩,
    ⟨hdf,hdG,hdD,hdO⟩,⟨hfG,hfD,hfO⟩,⟨hGD,hGO⟩,hDO⟩
  simp only [pointSelectors,run]
  apply congrArg (State.mk s.phase)
  funext w
  by_cases hG : w=L.genericSelect
  · subst w; simp [selectorState,writeBit, *, Ne.symm]
  · by_cases hD : w=L.doubleSelect
    · subst w; simp [selectorState,writeBit, *, Ne.symm]
    · by_cases hO : w=L.infinitySelect
      · subst w; simp [selectorState,writeBit, *, Ne.symm]
      · by_cases hf : w=L.core.input.finite
        · subst w; simp [selectorState,writeBit, *, Ne.symm]
        · simp [selectorState,writeBit, *, Ne.symm]

theorem selectorState_outside (L : ControlledPointLayout) (s : BasisState) (G D O : Bool)
    (w : Wire) (hw : w∉L.selectors) : selectorState L s G D O w=s w := by
  simp only [ControlledPointLayout.selectors,List.mem_cons,List.not_mem_nil,or_false,not_or] at hw
  simp [selectorState,writeBit,hw.1,hw.2.1,hw.2.2]

theorem selectorState_values (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (s : BasisState) (G D O : Bool) :
    selectorState L s G D O L.genericSelect=G ∧ selectorState L s G D O L.doubleSelect=D ∧
      selectorState L s G D O L.infinitySelect=O := by
  have hh := (List.nodup_cons.mp (List.nodup_append'.mp hn).2.1).2
  change [L.genericSelect,L.doubleSelect,L.infinitySelect].Nodup at hh
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,
    List.nodup_nil,not_false_eq_true,and_true] at hh
  rcases hh with ⟨⟨hGD,hGO⟩,hDO⟩
  simp [selectorState,writeBit, *]

theorem pointSelectors_counts (L : ControlledPointLayout) :
    toffoliCount (pointSelectors L)=3 ∧ measurementCount (pointSelectors L)=0 := by
  simp [pointSelectors,toffoliCount,measurementCount]

theorem pointSelectors_wires (L : ControlledPointLayout) :
    wires (pointSelectors L)=[L.control,L.core.generic,L.core.double,L.core.input.finite,
      L.genericSelect,L.doubleSelect,L.infinitySelect].toFinset := by
  ext w; simp [pointSelectors,wires,Instr.wires]; tauto

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/SelectedPointOutput.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Secp256k1

theorem ControlledPointLayout.output_nodup (L : ControlledPointLayout) (hn : L.wires.Nodup) :
    (PointAddLayout.pointWires L.core.output).Nodup :=
  (List.nodup_append'.mp (List.nodup_append'.mp (L.core_nodup hn)).1).2.1

theorem ControlledPointLayout.extra_not_output (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (w : Wire) (hw : w∈L.extras) : w∉PointAddLayout.pointWires L.core.output := by
  intro ho
  exact L.extra_not_core hn w hw (by simp [PointAddLayout.wires,ho])

theorem selectedPointOutput_counts (L : ControlledPointLayout) (h : L.Widths) (C : Point) :
    toffoliCount (selectedPointOutput L C)=512 ∧ measurementCount (selectedPointOutput L C)=0 := by
  simp [selectedPointOutput,toffoliCount_append,measurementCount_append,
    (pointGenericOutput_counts L.selected (L.selected_widths h)).1,
    (pointGenericOutput_counts L.selected (L.selected_widths h)).2,maskedPointConstant_counts]

theorem selectedPointOutput_correct (L : ControlledPointLayout) (h : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (s : State) (m : List Bool) :
    PointEffect L.core.output
      (s.basis L.genericSelect ^^ (s.basis L.doubleSelect && pointFinite (C+C)) ^^ (s.basis L.infinitySelect && pointFinite C))
      ((if s.basis L.genericSelect then regValue (L.core.candidateX.take 256) s.basis else 0) ^^^
        (if s.basis L.doubleSelect then pointX (C+C) else 0) ^^^ (if s.basis L.infinitySelect then pointX C else 0))
      ((if s.basis L.genericSelect then regValue (L.core.candidateY.take 256) s.basis else 0) ^^^
        (if s.basis L.doubleSelect then pointY (C+C) else 0) ^^^ (if s.basis L.infinitySelect then pointY C else 0)) s
      (run (selectedPointOutput L C) m s) := by
  have hd := L.extra_not_output hn L.doubleSelect (by simp [ControlledPointLayout.extras,ControlledPointLayout.selectors])
  have ho := L.extra_not_output hn L.infinitySelect (by simp [ControlledPointLayout.extras,ControlledPointLayout.selectors])
  let u := run (pointGenericOutput L.selected) m s
  have e0 := pointGenericOutput_correct L.selected (L.selected_widths h) (L.selected_nodup hn) s m
  have ud : u.basis L.doubleSelect=s.basis L.doubleSelect := e0.outside _ hd
  let v := run (maskedPointConstant L.doubleSelect L.core.output (C+C)) m u
  have e1 := maskedPointConstant_correct L.doubleSelect L.core.output (C+C) (L.output_nodup hn) hd h.outputX h.outputY u m
  have vo : v.basis L.infinitySelect=s.basis L.infinitySelect := (e0.trans e1).outside _ ho
  have e2 := maskedPointConstant_correct L.infinitySelect L.core.output C (L.output_nodup hn) ho h.outputX h.outputY v m
  have hh := (e0.trans e1).trans e2
  rw [selectedPointOutput,run_append,run_take,run_append,run_take]
  simp only [measurementCount_append,(pointGenericOutput_counts L.selected (L.selected_widths h)).2,
    (maskedPointConstant_counts L.doubleSelect L.core.output (C+C)).2,Nat.zero_add,List.drop_zero]
  simpa only [ControlledPointLayout.selected,ud,vo] using hh

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ControlledPointOutput.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Secp256k1

theorem ControlledPointLayout.core_not_selectors (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (w : Wire) (hw : w∈L.core.wires) : w∉L.selectors := by
  intro hs
  exact L.extra_not_core hn w (List.mem_cons_of_mem _ hs) hw

theorem controlledPointOutput_correct (L : ControlledPointLayout) (h : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (s : State) (m : List Bool)
    (hz : s.basis L.genericSelect=false ∧ s.basis L.doubleSelect=false ∧ s.basis L.infinitySelect=false) :
    PointEffect L.core.output
      (s.basis L.control && (s.basis L.core.generic ^^ (s.basis L.core.double && pointFinite (C+C)) ^^ (!s.basis L.core.input.finite && pointFinite C)))
      (if s.basis L.control then
        (if s.basis L.core.generic then regValue (L.core.candidateX.take 256) s.basis else 0) ^^^
        (if s.basis L.core.double then pointX (C+C) else 0) ^^^ (if !s.basis L.core.input.finite then pointX C else 0) else 0)
      (if s.basis L.control then
        (if s.basis L.core.generic then regValue (L.core.candidateY.take 256) s.basis else 0) ^^^
        (if s.basis L.core.double then pointY (C+C) else 0) ^^^ (if !s.basis L.core.input.finite then pointY C else 0) else 0) s
      (run (controlledPointOutput L C) m s) := by
  let G := s.basis L.control && s.basis L.core.generic
  let D := s.basis L.control && s.basis L.core.double
  let O := s.basis L.control && !s.basis L.core.input.finite
  let u : State := ⟨s.phase,selectorState L s.basis G D O⟩
  have hu : run (pointSelectors L) m s=u := by
    rw [pointSelectors_correct L hn]; simp only [hz.1,hz.2.1,hz.2.2,Bool.false_xor]; rfl
  have uc (w : Wire) (hw : w∈L.core.wires) : u.basis w=s.basis w :=
    selectorState_outside L _ _ _ _ w (L.core_not_selectors hn w hw)
  have us := selectorState_values L hn s.basis G D O
  have ub : u.basis L.control=s.basis L.control := by
    apply selectorState_outside
    exact (List.nodup_cons.mp (List.nodup_append'.mp hn).2.1).1
  let v := run (selectedPointOutput L C) m u
  have he := selectedPointOutput_correct L h hn C u m
  have vs (w : Wire) (hw : w∈L.extras) : v.basis w=u.basis w :=
    he.outside w (L.extra_not_output hn w hw)
  have vd := vs L.doubleSelect (by simp [ControlledPointLayout.extras,ControlledPointLayout.selectors])
  have vg := vs L.genericSelect (by simp [ControlledPointLayout.extras,ControlledPointLayout.selectors])
  have vo := vs L.infinitySelect (by simp [ControlledPointLayout.extras,ControlledPointLayout.selectors])
  have vb := vs L.control (by simp [ControlledPointLayout.extras])
  have hd := (L.core.output_interfaces (L.core_nodup hn)).2.2
  have vf : v.basis L.core.input.finite=s.basis L.core.input.finite := by
    rw [he.outside _ (fun hw => (List.nodup_cons.mp hd).1 (List.mem_cons_of_mem _ hw))]
    exact uc _ (by simp [PointAddLayout.wires,PointAddLayout.pointWires])
  have vD : v.basis L.core.double=s.basis L.core.double := by
    rw [he.outside _ (List.nodup_cons.mp (List.nodup_cons.mp hd).2).1]
    exact uc _ (by simp [PointAddLayout.wires,PointAddLayout.work,PointAddLayout.flags])
  have vG : v.basis L.core.generic=s.basis L.core.generic := by
    have hh := (List.nodup_append'.mp (L.core.pool_external_nodup (L.core_nodup hn))).2.2
    rw [he.outside _ (List.disjoint_left.mp hh (List.mem_append_right _ (by simp [PointAddLayout.flags])))]
    exact uc _ (by simp [PointAddLayout.wires,PointAddLayout.work,PointAddLayout.flags])
  have ht : run (pointSelectors L) m v=⟨s.phase,selectorState L v.basis false false false⟩ := by
    rw [pointSelectors_correct L hn]
    have hp : v.phase=s.phase := he.phase
    simp only [hp,vg,vd,vo,vb,vG,vD,vf,ub,show u.basis L.genericSelect=G from us.1,
      show u.basis L.doubleSelect=D from us.2.1,show u.basis L.infinitySelect=O from us.2.2,G,D,O,Bool.xor_self]
  have eo (w : Wire) (hw : w∈PointAddLayout.pointWires L.core.output) : w∉L.selectors :=
    L.core_not_selectors hn w (by simp [PointAddLayout.wires,hw])
  have ux : regValue (L.core.candidateX.take 256) u.basis=regValue (L.core.candidateX.take 256) s.basis := by
    apply regValue_congr; intro w hw
    exact uc w (by have hm := List.mem_of_mem_take hw; simp [PointAddLayout.wires,PointAddLayout.work,PointAddLayout.words,hm])
  have uy : regValue (L.core.candidateY.take 256) u.basis=regValue (L.core.candidateY.take 256) s.basis := by
    apply regValue_congr; intro w hw
    exact uc w (by have hm := List.mem_of_mem_take hw; simp [PointAddLayout.wires,PointAddLayout.work,PointAddLayout.words,hm])
  have huf : u.basis L.core.output.finite=s.basis L.core.output.finite := uc _ (by simp [PointAddLayout.wires,PointAddLayout.pointWires])
  have hur (r : List Wire) (hr : ∀ w∈r,w∈PointAddLayout.pointWires L.core.output) :
      regValue r u.basis=regValue r s.basis := regValue_congr _ _ _ (fun w hw => uc w (by simp [PointAddLayout.wires,hr w hw]))
  have htr (r : List Wire) (hr : ∀ w∈r,w∈PointAddLayout.pointWires L.core.output) :
      regValue r (selectorState L v.basis false false false)=regValue r v.basis :=
    regValue_congr _ _ _ (fun w hw => selectorState_outside L _ _ _ _ w (eo w (hr w hw)))
  rw [controlledPointOutput,run_append,run_take,run_append,run_take]
  simp only [measurementCount_append,(pointSelectors_counts L).2,(selectedPointOutput_counts L h C).2,
    Nat.zero_add,List.drop_zero,hu]
  change PointEffect _ _ _ _ s (run (pointSelectors L) m v)
  rw [ht]
  refine ⟨rfl,?_,?_,?_,?_⟩
  · intro w hw
    by_cases hs : w∈L.selectors
    · simp only [ControlledPointLayout.selectors,List.mem_cons,List.not_mem_nil,or_false] at hs
      rcases hs with rfl|rfl|rfl
      · exact (selectorState_values L hn v.basis false false false).1.trans hz.1.symm
      · exact (selectorState_values L hn v.basis false false false).2.1.trans hz.2.1.symm
      · exact (selectorState_values L hn v.basis false false false).2.2.trans hz.2.2.symm
    · dsimp only
      rw [selectorState_outside L _ _ _ _ w hs,he.outside w hw]
      exact selectorState_outside L _ _ _ _ w hs
  · dsimp only
    rw [selectorState_outside L v.basis false false false L.core.output.finite (eo L.core.output.finite (by simp [PointAddLayout.pointWires])),he.finite,
      huf,show u.basis L.genericSelect=G from us.1,show u.basis L.doubleSelect=D from us.2.1,
      show u.basis L.infinitySelect=O from us.2.2]
    cases hb : s.basis L.control <;> simp [G,D,O,hb]
  · rw [htr _ (by intro w hw; simp [PointAddLayout.pointWires,hw]),he.x,
      hur _ (by intro w hw; simp [PointAddLayout.pointWires,hw]),ux,
      show u.basis L.genericSelect=G from us.1,show u.basis L.doubleSelect=D from us.2.1,
      show u.basis L.infinitySelect=O from us.2.2]
    cases hb : s.basis L.control <;> simp [G,D,O,hb]
  · rw [htr _ (by intro w hw; simp [PointAddLayout.pointWires,hw]),he.y,
      hur _ (by intro w hw; simp [PointAddLayout.pointWires,hw]),uy,
      show u.basis L.genericSelect=G from us.1,show u.basis L.doubleSelect=D from us.2.1,
      show u.basis L.infinitySelect=O from us.2.2]
    cases hb : s.basis L.control <;> simp [G,D,O,hb]

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ControlledPointStages.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Secp256k1

def PointControl (L : ControlledPointLayout) (b : Bool) (s : BasisState) : Prop :=
  s L.control=b ∧ s L.genericSelect=false ∧ s L.doubleSelect=false ∧ s L.infinitySelect=false

theorem pointControl_frame (L : ControlledPointLayout) (hn : L.wires.Nodup) (b : Bool)
    {P Q : BasisState → Prop} {c : Program} (hc : Triple P c Q)
    (hw : wires c⊆L.core.wires.toFinset) :
    Triple (fun s => P s ∧ PointControl L b s) c (fun s => Q s ∧ PointControl L b s) := by
  apply hc.frame
  intro s t he hb
  have hh (w : Wire) (hm : w∈L.extras) : t w=s w :=
    (he w (fun hm' => L.extra_not_core hn w hm (List.mem_toFinset.mp (hw hm')))).symm
  simpa only [PointControl,hh L.control (by simp [ControlledPointLayout.extras]),
    hh L.genericSelect (by simp [ControlledPointLayout.extras,ControlledPointLayout.selectors]),
    hh L.doubleSelect (by simp [ControlledPointLayout.extras,ControlledPointLayout.selectors]),
    hh L.infinitySelect (by simp [ControlledPointLayout.extras,ControlledPointLayout.selectors])] using hb

theorem ControlledPointLayout.candidate_subset (L : ControlledPointLayout) (h : L.Widths) :
    L.core.candidateUsed.toFinset⊆L.core.wires.toFinset := by
  intro w hw
  have hp : w∈candidatePool L.core.poolWire → w∈L.core.pool := fun hh => (L.core.candidatePool_sublist h).subset hh
  simp only [List.mem_toFinset,PointAddLayout.candidateUsed,PointAddLayout.extendedX,
    PointAddLayout.extendedY,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
  simp only [List.mem_toFinset,PointAddLayout.wires,PointAddLayout.pointWires,
    PointAddLayout.work,PointAddLayout.words,PointAddLayout.flags,List.flatten_cons,List.flatten_nil,
    List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  rcases hw with (((((((((((((((hx|hxh)|(hy|hyh))|hdx)|hdy)|hs)|hsq)|ho)|hcx)|hd)|hp)|hcy)|hk)|hdv)|hi)|hg)|hw
  all_goals try { subst w; simp }
  all_goals try { have hh := List.mem_of_mem_take hdx; simp_all only [true_or,or_true] }
  all_goals try { have hh := List.mem_of_mem_take hcy; simp_all only [true_or,or_true] }
  all_goals try { have hh := List.mem_of_mem_take hdy; simp_all only [true_or,or_true] }
  all_goals try { have hh := List.mem_of_mem_take hd; simp_all only [true_or,or_true] }
  all_goals simp_all only [true_or,or_true]

theorem ControlledPointLayout.flags_subset (L : ControlledPointLayout) :
    (L.core.input.finite::L.core.input.x++L.core.input.y++L.core.flags++L.core.pool.take 256).toFinset⊆L.core.wires.toFinset := by
  intro w hw
  simp only [List.mem_toFinset,List.mem_append,List.mem_cons] at hw
  have hp : w∈L.core.pool.take 256 → w∈L.core.pool := List.mem_of_mem_take
  rcases hw with (((hf|hx)|hy)|hflags)|hpool
  all_goals simp_all [PointAddLayout.wires,PointAddLayout.pointWires,PointAddLayout.work]

theorem controlledPointStage_output (L : ControlledPointLayout) (h : L.Widths) (hn : L.wires.Nodup)
    (b : Bool) (R : Point) (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy)
    (OF : Bool) (OX OY : Nat) :
    let C : Point := .some hc
    let V := candidateResult (pointGeneric R cx) (pointX R) (pointY R) cx.val cy.val
    Triple (fun s => PointStage L.core R cx cy OF OX OY V s ∧ PointControl L b s)
      (controlledPointOutput L C)
      (fun s => PointStage L.core R cx cy (OF^^(b&&pointFinite (R+C)))
        (OX^^^(if b then pointX (R+C) else 0)) (OY^^^(if b then pointY (R+C) else 0)) V s ∧ PointControl L b s) := by
  dsimp only
  intro s m hs
  obtain ⟨⟨hv,hb⟩,hctrl⟩ := hs
  have hh := controlledPointOutput_correct L h hn (.some hc) s m hctrl.2
  have hx := h.words L.core.candidateX (by simp [PointAddLayout.words])
  have hy := h.words L.core.candidateY (by simp [PointAddLayout.words])
  have hbnd := candidateResult_xy_lt (pointGeneric R cx) (pointX R) (pointY R) cx cy
    (point_coordinates_lt R).1 (point_coordinates_lt R).2
  have hlow (r : List Wire) (hr : r.length=257) (V : Nat) (hV : V<p)
      (hv : regValue r s.basis=V) : regValue (r.take 256) s.basis=V := by
    have ht := regValue_low_iff (r.take 256) (r.drop 256) s.basis V
      (by simp only [List.length_take,hr]; exact lt_trans hV (by norm_num [p]))
    rw [List.take_append_drop] at ht
    exact (ht.mp hv).1
  have hX := hlow L.core.candidateX hx _ hbnd.1 (hv.1 .x)
  have hY := hlow L.core.candidateY hy _ hbnd.2 (hv.1 .y)
  rw [hX,hY,hv.2.2,hb.finite,hb.double,hctrl.1] at hh
  have he := point_classification_xor R cx cy hc
  dsimp only at he
  have heF := congrArg Prod.fst he
  have heX := congrArg (fun t => t.2.1) he
  have heY := congrArg (fun t => t.2.2) he
  dsimp only at heF heX heY
  rw [heF,heX,heY] at hh
  have ep (w : Wire) (hw : w∈L.extras) := hh.outside w (L.extra_not_output hn w hw)
  refine ⟨hh.phase,⟨hv.pointOutput (L.core_nodup hn) hh,hb.pointOutput (L.core_nodup hn) hh⟩,?_⟩
  simpa only [PointControl,ep L.control (by simp [ControlledPointLayout.extras]),
    ep L.genericSelect (by simp [ControlledPointLayout.extras,ControlledPointLayout.selectors]),
    ep L.doubleSelect (by simp [ControlledPointLayout.extras,ControlledPointLayout.selectors]),
    ep L.infinitySelect (by simp [ControlledPointLayout.extras,ControlledPointLayout.selectors])] using hctrl

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ControlledPointOutSpec.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Secp256k1

def ControlledPointReady (L : ControlledPointLayout) (b : Bool) (R : Point)
    (OF : Bool) (OX OY : Nat) (s : BasisState) : Prop :=
  PointReady L.core R OF OX OY s ∧ PointControl L b s

/-- 任意目标位串的受控 XOR 引理；原地程序只对有限常量调用此辅助程序。 -/
theorem controlledPointAddOut_finite_ready (L : ControlledPointLayout) (h : L.Widths)
    (hn : L.wires.Nodup) (b : Bool) (R : Point) (cx cy : Fp)
    (hc : curve.toAffine.Nonsingular cx cy) (OF : Bool) (OX OY : Nat) :
    let C : Point := .some hc
    Triple (ControlledPointReady L b R OF OX OY) (controlledPointAddOut L C)
      (ControlledPointReady L b R (OF^^(b&&pointFinite (R+C)))
        (OX^^^(if b then pointX (R+C) else 0)) (OY^^^(if b then pointY (R+C) else 0))) := by
  dsimp only
  have hnc := L.core_nodup hn
  have hb := point_coordinates_lt R
  have hg : pointGeneric R cx=true → pointX R≠cx.val := fun hh => (pointGeneric_domain R cx hh).2
  have hs := pointCandidate_support L.core h cx cy
  have hf := pointFlags_support L.core h cx cy
  have hcompute := pointCandidate_compute_spec L.core h hnc (pointGeneric R cx) (pointX R) (pointY R) cx cy hb.1 hb.2 hg
  have hclear := pointCandidate_clear_spec L.core h hnc (pointGeneric R cx) (pointX R) (pointY R) cx cy hb.1 hb.2 hg
  have h1 := pointControl_frame L hn b (pointStage_flags L.core h hnc R cx cy OF OX OY)
    (by rw [hf.1]; exact L.flags_subset)
  have h2 := pointControl_frame L hn b (pointStage_candidate L.core h hnc R cx cy OF OX OY _ _ _ hs.1 hcompute)
    (by rw [hs.1]; exact L.candidate_subset h)
  have h3 := controlledPointStage_output L h hn b R cx cy hc OF OX OY
  have h4 := pointControl_frame L hn b (pointStage_candidate L.core h hnc R cx cy
    (OF^^(b&&pointFinite (R+.some hc))) (OX^^^(if b then pointX (R+.some hc) else 0))
    (OY^^^(if b then pointY (R+.some hc) else 0)) _ _ _ hs.2 hclear)
    (by rw [hs.2]; exact L.candidate_subset h)
  have h5 := pointControl_frame L hn b (pointStage_clearFlags L.core h hnc R cx cy
    (OF^^(b&&pointFinite (R+.some hc))) (OX^^^(if b then pointX (R+.some hc) else 0))
    (OY^^^(if b then pointY (R+.some hc) else 0)))
    (by rw [hf.2]; exact L.flags_subset)
  exact (((h1.seq h2).seq h3).seq h4).seq h5

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointDialogIntegration.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

private theorem boundary_frame_values (L : ControlledPointLayout) (P : Program)
    (hP : wires P⊆L.dialogUsedWires.toFinset) (R R' : Point) (b : Bool) (s : State) (m : List Bool)
    (hi : PointDialogBoundary L R b (fun _ => false) s.basis)
    (ho : PointDialogBoundary L R' b (fun _ => false) (run P m s).basis)
    (q : Wire) (hp : q∉PointAddLayout.pointWires L.point) : (run P m s).basis q=s.basis q := by
  by_cases hc : q=L.control
  · subst q; exact ho.control.trans hi.control.symm
  by_cases hf : q∈L.inPlaceFlags
  · exact (ho.flags q hf).trans (hi.flags q hf).symm
  by_cases hw : q∈L.dialogPool
  · exact (regValue_eq_iff _ _ _).mp (ho.clean.trans hi.clean.symm) q hw
  apply run_preserves_outside
  apply mt (@hP q)
  simp [dialogUsedWires,hp,hc,hf,hw]

theorem pointDialogFinite_frame (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (s : State) (m : List Bool)
    (hi : PointDialogBoundary L R b (fun _ => false) s.basis)
    (q : Wire) (hq : q∉PointAddLayout.pointWires L.point) :
    (run (pointDialogFinite L (.some hc) cx cy) m s).basis q=s.basis q := by
  have ho := (pointDialogFinite_spec L hw hn R hc b s m hi).2
  exact boundary_frame_values L _ (pointDialogFinite_wires L hw hn (.some hc) cx cy) R _ b s m hi ho q hq

private theorem boundary_work_subset (L : ControlledPointLayout) :
    L.inPlaceFlags++L.dialogPool ⊆ L.work := by
  intro q hq
  have h1 := List.count_pos_iff.mpr hq
  have ht := (List.take_sublist 2613 L.core.pool).count_le q
  apply List.count_pos_iff.mp
  simp only [dialogPool,List.count_append] at h1
  simp only [work,outWork,temporary,inPlaceFlags,selectors,PointAddLayout.work,PointAddLayout.words,
    PointAddLayout.flags,List.flatten_cons,List.flatten_nil,List.append_nil,List.count_append,List.count_cons,List.count_nil] at h1 ht ⊢
  omega

private theorem work_not_point (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.work) : q∉PointAddLayout.pointWires L.point := by
  intro hp
  have hh := List.nodup_iff_count.mp hn q
  have h1 := List.count_pos_iff.mpr hq
  have h2 := List.count_pos_iff.mpr hp
  simp only [ControlledPointLayout.wires,work,outWork,temporary,point,extras,selectors,PointAddLayout.wires,
    List.count_append,List.count_cons,List.count_nil] at hh h1 h2
  omega

/-- 公共布局的全部分配工作位恢复为零，包括本实现未使用的旧银行。 -/
theorem pointDialogFinite_full_spec (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) :
    (Triple (fun st => (Holds.holds st L.control b ∧ Holds.holds st L.point R) ∧ Holds.holds st L.work 0) (pointCompressedDialogFinite L (.some hc) cx cy)
      (fun st => (Holds.holds st L.control b ∧ Holds.holds st L.point (if b then R+.some hc else R)) ∧ Holds.holds st L.work 0)) := by
  exact CompressedPointDialog.full_spec L hw hn R hc b

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ControlledPointAddSpec.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Secp256k1

theorem controlledPointAddOut_ready (L : ControlledPointLayout) (h : L.Widths)
    (hn : L.wires.Nodup) (b : Bool) (R C : Point) (hc : C≠0) (OF : Bool) (OX OY : Nat) :
    Triple (ControlledPointReady L b R OF OX OY) (controlledPointAddOut L C)
      (ControlledPointReady L b R (OF^^(b&&pointFinite (R+C)))
        (OX^^^(if b then pointX (R+C) else 0)) (OY^^^(if b then pointY (R+C) else 0))) := by
  cases C with
  | zero => exact (hc rfl).elim
  | some hp => exact controlledPointAddOut_finite_ready L h hn b R _ _ hp OF OX OY

/-- 完整受控原地点加：任意合法点与经典常量，包括 O、互逆点和倍点。
控制位保持；临时点、算术工作区及三个选择位全部归零；所有测量记录下相位恢复。 -/
theorem controlledPointAdd_spec (L : ControlledPointLayout) (h : L.Widths) (hn : L.wires.Nodup)
    (b : Bool) (R C : Point) :
    (Triple (fun st => (Holds.holds st L.control b ∧ Holds.holds st L.point R) ∧ Holds.holds st L.work 0) (controlledPointAdd L C)
      (fun st => (Holds.holds st L.control b ∧ Holds.holds st L.point (if b then R+C else R)) ∧ Holds.holds st L.work 0)) := by
  cases C with
  | zero =>
    intro s m hs
    change s.phase=s.phase ∧ _
    refine ⟨rfl,?_⟩
    change ((Holds.holds s.basis L.control b ∧ Holds.holds s.basis L.point (if b then R+0 else R)) ∧ _)
    simpa only [add_zero,ite_self] using hs
  | some hp => exact pointDialogFinite_full_spec L h hn R hp b

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ControlledPointSupport.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Secp256k1

def ControlledPointLayout.usedWires (L : ControlledPointLayout) := L.core.usedWires++L.extras

theorem ControlledPointLayout.used_subset (L : ControlledPointLayout) (h : L.Widths) :
    L.core.usedWires.toFinset⊆L.core.wires.toFinset := by
  intro w hw
  simp only [PointAddLayout.usedWires,List.toFinset_append,Finset.mem_union] at hw
  rcases hw with hw|hw
  · exact L.candidate_subset h hw
  · simpa only [List.mem_toFinset] using (show w∈L.core.wires from by
      simp only [PointAddLayout.boundaryWires,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with (rfl|rfl|rfl|rfl)|hw
      all_goals simp_all [PointAddLayout.wires,PointAddLayout.pointWires,PointAddLayout.work,PointAddLayout.flags] <;> tauto)

theorem ControlledPointLayout.used_nodup (L : ControlledPointLayout) (h : L.Widths) (hn : L.wires.Nodup) :
    L.usedWires.Nodup := by
  apply List.nodup_append'.mpr
  refine ⟨L.core.usedWires_nodup h (L.core_nodup hn),(List.nodup_append'.mp hn).2.1,?_⟩
  exact List.disjoint_left.mpr (fun w hw he => L.extra_not_core hn w he
    (List.mem_toFinset.mp (L.used_subset h (List.mem_toFinset.mpr hw))))

theorem controlledPointAddOut_support (L : ControlledPointLayout) (h : L.Widths) (cx cy : Fp)
    (hc : curve.toAffine.Nonsingular cx cy) :
    wires (controlledPointAddOut L (.some hc))=L.usedWires.toFinset := by
  have hflags : (L.core.input.finite::L.core.input.x++L.core.input.y++L.core.flags++L.core.pool.take 256).toFinset ⊆
      L.usedWires.toFinset := by
    intro w hw
    have hp : w∈L.core.pool.take 256 → w∈candidatePool L.core.poolWire := L.core.pool_prefix_used h 256 (by omega) w
    simp only [ControlledPointLayout.usedWires,PointAddLayout.usedWires,PointAddLayout.candidateUsed,PointAddLayout.boundaryWires,
      PointAddLayout.extendedX,PointAddLayout.extendedY,PointAddLayout.flags,
      List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hw ⊢
    rcases hw with (((hw|hw)|hw)|(hw|hw|hw|hw))|hw
    all_goals simp_all only [true_or,or_true]
  have hgeneric : (L.genericSelect::L.core.candidateX.take 256++L.core.candidateY.take 256++PointAddLayout.pointWires L.core.output).toFinset ⊆
      L.usedWires.toFinset := by
    intro w hw
    have hx : w∈L.core.candidateX.take 256 → w∈L.core.candidateX := List.mem_of_mem_take
    simp only [ControlledPointLayout.usedWires,ControlledPointLayout.extras,ControlledPointLayout.selectors,
      PointAddLayout.usedWires,PointAddLayout.candidateUsed,PointAddLayout.boundaryWires,
      List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hw ⊢
    rcases hw with ((hw|hw)|hw)|hw
    all_goals simp_all only [true_or,or_true]
  have hconstant (q : Wire) (hq : q∈L.extras) :
      (q::PointAddLayout.pointWires L.core.output).toFinset ⊆ L.usedWires.toFinset := by
    intro w hw
    simp only [ControlledPointLayout.usedWires,PointAddLayout.usedWires,PointAddLayout.boundaryWires,List.mem_toFinset,
      List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hw ⊢
    rcases hw with rfl|hw
    · exact Or.inr hq
    · tauto
  have hsel : [L.control,L.core.generic,L.core.double,L.core.input.finite,L.genericSelect,L.doubleSelect,L.infinitySelect].toFinset⊆L.usedWires.toFinset := by
    intro w hw
    simp only [ControlledPointLayout.usedWires,ControlledPointLayout.extras,ControlledPointLayout.selectors,
      PointAddLayout.usedWires,PointAddLayout.candidateUsed,PointAddLayout.boundaryWires,
      List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hw ⊢
    rcases hw with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp only [true_or,or_true]
  have hcandidate : L.core.candidateUsed.toFinset⊆L.usedWires.toFinset := by
    simp [ControlledPointLayout.usedWires,PointAddLayout.usedWires]
  have cC := (pointCandidate_support L.core h cx cy).1
  have cU := (pointCandidate_support L.core h cx cy).2
  have fC := (pointFlags_support L.core h cx cy).1
  have fU := (pointFlags_support L.core h cx cy).2
  have oG := pointGenericOutput_support L.selected (L.selected_widths h)
  have oD := (maskedPointConstant_support L.doubleSelect L.core.output ((.some hc : Point)+.some hc)).trans
    (hconstant L.doubleSelect (by simp [ControlledPointLayout.extras,ControlledPointLayout.selectors]))
  have oO := (maskedPointConstant_support L.infinitySelect L.core.output (.some hc)).trans
    (hconstant L.infinitySelect (by simp [ControlledPointLayout.extras,ControlledPointLayout.selectors]))
  rw [controlledPointAddOut,wires_append,wires_append,wires_append,wires_append,cC,cU,fC,fU,
    controlledPointOutput,wires_append,wires_append,selectedPointOutput,wires_append,wires_append,oG,pointSelectors_wires]
  change _ = L.usedWires.toFinset
  apply Finset.Subset.antisymm
  · simp only [Finset.union_subset_iff]
    exact ⟨⟨⟨⟨hflags,hcandidate⟩,⟨⟨hsel,⟨⟨hgeneric,oD⟩,oO⟩⟩,hsel⟩⟩,hcandidate⟩,hflags⟩
  · intro w hw
    simp only [ControlledPointLayout.usedWires,PointAddLayout.usedWires,List.mem_toFinset,List.mem_append] at hw
    simp only [ControlledPointLayout.selected,Finset.mem_union,List.mem_toFinset,List.mem_cons,List.mem_append,
      PointAddLayout.flags,List.not_mem_nil,or_false]
    clear cC cU fC fU oG oD oO
    rcases hw with (hw|hw)|hw
    · simp only [hw,true_or,or_true]
    · simp only [PointAddLayout.boundaryWires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with (hw|hw|hw|hw)|hw
      all_goals simp_all only [true_or,or_true]
    · simp only [ControlledPointLayout.extras,ControlledPointLayout.selectors,List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with hw|hw|hw|hw
      all_goals simp_all only [true_or,or_true]

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ControlledPointResources.lean
noncomputable section

namespace ECDSAAdd.Arithmetic
open Secp256k1

theorem controlledPointOutput_counts (L : ControlledPointLayout) (h : L.Widths) (C : Point) :
    toffoliCount (controlledPointOutput L C)=518 ∧ measurementCount (controlledPointOutput L C)=0 := by
  simp only [controlledPointOutput,toffoliCount_append,measurementCount_append,
    (pointSelectors_counts L).1,(pointSelectors_counts L).2,
    (selectedPointOutput_counts L h C).1,(selectedPointOutput_counts L h C).2]
  exact ⟨trivial,trivial⟩

theorem controlledPointAddOut_finite_resources (L : ControlledPointLayout) (h : L.Widths)
    (hn : L.wires.Nodup) (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (controlledPointAddOut L (.some hc))=9295112 ∧
    measurementCount (controlledPointAddOut L (.some hc))=6126846 ∧
    qubitCount (controlledPointAddOut L (.some hc))=6731 := by
  have cc := pointCandidate_counts L.core h (L.core_nodup hn) cx cy
  have cf := pointFlags_counts L.core h cx cy
  have co := controlledPointOutput_counts L h (.some hc)
  refine ⟨?_,?_,?_⟩
  · simp only [controlledPointAddOut,toffoliCount_append,cc.1.1,cc.2.1,cf.1.1,cf.2.1,co.1]
  · simp only [controlledPointAddOut,measurementCount_append,cc.1.2,cc.2.2,cf.1.2,cf.2.2,co.2]
  · rw [qubitCount,controlledPointAddOut_support L h cx cy hc,List.toFinset_card_of_nodup (L.used_nodup h hn)]
    simp [ControlledPointLayout.usedWires,ControlledPointLayout.extras,ControlledPointLayout.selectors,L.core.usedWires_length h]

/-- Exact costs of the same complete Skywalk point program, with a physical support bound. -/
theorem controlledPointAdd_finite_resources (L : ControlledPointLayout) (h : L.Widths)
    (hn : L.wires.Nodup) (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (controlledPointAdd L (.some hc))=2217386 ∧
    measurementCount (controlledPointAdd L (.some hc))=1557928 ∧
    qubitCount (controlledPointAdd L (.some hc))≤1899 := by
  have hh := CompressedPointDialog.finite_counts L h hn (.some hc) cx cy
  exact ⟨hh.1,hh.2,CompressedPointDialog.finite_qubits L h hn (.some hc) cx cy⟩

/-- C=O 在构造期为空程序，故实际门数、测量和线路集合均为空。 -/
theorem controlledPointAdd_zero_resources (L : ControlledPointLayout) :
    toffoliCount (controlledPointAdd L 0)=0 ∧ measurementCount (controlledPointAdd L 0)=0 ∧
    qubitCount (controlledPointAdd L 0)=0 := by
  simp [controlledPointAdd,toffoliCount,measurementCount,qubitCount,wires]

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/DirectZeroPhysical.lean
noncomputable section
namespace ECDSAAdd.Arithmetic
open RecordedQuantum

theorem zeroSeeded_physical (xs carry : List Wire) (cin target : Wire)
    (hn : (target::cin::(xs++carry)).Nodup) :
    GatePhysical (ZeroSeededConstantCompare.program xs carry cin target) := by
  cases xs with
  | nil => simp [ZeroSeededConstantCompare.program,GatePhysical]
  | cons x xs =>
    cases xs with
    | nil =>
      have ht : x ≠ target := by
        intro eq; subst target
        have h := List.nodup_iff_count.mp hn x
        simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
        omega
      simp [ZeroSeededConstantCompare.program,ZeroSeededConstantCompare.prepare,GatePhysical,PhysicalInstr,ProperGate,ht]
    | cons y xs =>
      cases carry with
      | nil => simp [ZeroSeededConstantCompare.program,GatePhysical]
      | cons c cs =>
        have xc : x ≠ c := by
          intro eq; subst c
          have h := List.nodup_iff_count.mp hn x
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
          omega
        have nd : ([c,target]++(y::xs)++cs).Nodup := by
          apply List.nodup_iff_count.mpr
          intro w
          have h := List.nodup_iff_count.mp hn w
          simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
          omega
        have pre : GatePhysical (ZeroSeededConstantCompare.prepare x c) := by
          simp [ZeroSeededConstantCompare.prepare,GatePhysical,PhysicalInstr,ProperGate,xc]
        have post : GatePhysical (ZeroSeededConstantCompare.release x c) := by
          simp [ZeroSeededConstantCompare.release,GatePhysical,PhysicalInstr,ProperGate,xc]
        simp only [ZeroSeededConstantCompare.program,gatePhysical_append]
        exact ⟨⟨pre,compareConstantLt_physical _ _ _ _ _ nd⟩,post⟩

theorem directZero_physical (xs carry : List Wire) (cin flag : Wire) (kernel : Program)
    (hn : (flag::cin::(xs++carry)).Nodup) (hk : GatePhysical kernel) :
    GatePhysical (directZeroControlled xs carry cin flag kernel) := by
  have hz := zeroSeeded_physical xs carry cin flag hn
  have away : flag ∉ xs := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
  have hm := maskedConstant_physical flag xs 1 away
  simp only [directZeroControlled,directZeroDivisorEnter,directZeroDivisorLeave,gatePhysical_append]
  exact ⟨⟨hz,hm⟩,hk,hm,hz⟩
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/FixedFieldPhysical.lean
noncomputable section
namespace ECDSAAdd.Arithmetic
open RecordedQuantum
theorem fixedForwardField_physical : GatePhysical (OffsetBorrowedField.program id 2409) := by
  apply physicalGateCheck_correct
  decide +kernel

theorem fixedInverseField_physical : GatePhysical (OffsetBorrowedInverse.program id 2409) := by
  apply physicalGateCheck_correct
  decide +kernel
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/KnownOutputAdderPhysical.lean
noncomputable section
namespace ECDSAAdd.Arithmetic.KnownOutputAdder
open RecordedQuantum

theorem xorBit_physical (b : MappedBit) (t : Wire) (ha : ∀q∈b.wire,q≠t) :
    GatePhysical (xorBit b t) := by
  cases h : b.wire <;> cases f : b.flip <;>
    simp_all [xorBit,GatePhysical,PhysicalInstr,ProperGate]

theorem prepare_physical (b d : MappedBit) (y c : Wire) (hy : y≠c)
    (hb : ∀q∈b.wire,q≠c) (hd : ∀q∈d.wire,q≠c) : GatePhysical (prepare b d y c) := by
  simp only [prepare,gatePhysical_append]
  exact ⟨⟨by simp [GatePhysical,PhysicalInstr,ProperGate,hy],xorBit_physical b c hb⟩,xorBit_physical d c hd⟩

theorem program_physical (bits sums : List MappedBit) (ys carry : List Wire) (cin : Wire)
    (hl : bits.length=ys.length) (hs : sums.length=ys.length)
    (hc : carry.length+1=ys.length) (hn : (cin::ys++carry).Nodup)
    (hb : ∀b∈bits,∀q∈b.wire,q∉cin::ys++carry)
    (hd : ∀b∈sums,∀q∈b.wire,q∉cin::ys++carry) :
    GatePhysical (program bits ys sums carry cin) := by
  induction ys generalizing bits sums carry cin with
  | nil => simp at hc
  | cons y ys ih =>
    cases bits with
    | nil => simp at hl
    | cons b bs =>
      cases sums with
      | nil => simp at hs
      | cons d ds =>
        have sm : GatePhysical (mappedSum b y cin) := by
          apply mappedSum_physical
          · intro eq; subst cin
            exact (List.nodup_cons.mp hn).1 (by simp)
          · intro q hq eq; subst q
            exact hb b (by simp) y hq (by simp)
        cases ys with
        | nil =>
          have be : bs=[] := List.eq_nil_of_length_eq_zero (by simpa using hl)
          have de : ds=[] := List.eq_nil_of_length_eq_zero (by simpa using hs)
          subst bs; subst ds
          exact sm
        | cons y' ys =>
          cases bs with
          | nil => simp at hl
          | cons b' bs =>
            cases ds with
            | nil => simp at hs
            | cons d' ds =>
              cases carry with
              | nil => simp at hc
              | cons c cs =>
                have tailnd : (c::(y'::ys)++cs).Nodup := by
                  apply List.nodup_iff_count.mpr
                  intro w
                  have h := List.nodup_iff_count.mp hn w
                  simp only [List.count_cons,List.count_append] at h ⊢
                  omega
                have tailbits : ∀z∈b'::bs,∀q∈z.wire,q∉c::(y'::ys)++cs := by
                  intro z hz q hq hm
                  apply hb z (List.mem_cons_of_mem _ hz) q hq
                  simp only [List.mem_cons,List.mem_append] at hm ⊢
                  tauto
                have tailsums : ∀z∈d'::ds,∀q∈z.wire,q∉c::(y'::ys)++cs := by
                  intro z hz q hq hm
                  apply hd z (List.mem_cons_of_mem _ hz) q hq
                  simp only [List.mem_cons,List.mem_append] at hm ⊢
                  tauto
                have py : y'≠c := by
                  intro eq; subst c
                  exact (List.nodup_cons.mp tailnd).1 (by simp)
                have pb : ∀q∈b'.wire,q≠c := by
                  intro q hq eq; subst q
                  exact hb b' (by simp) c hq (by simp)
                have pd : ∀q∈d'.wire,q≠c := by
                  intro q hq eq; subst q
                  exact hd d' (by simp) c hq (by simp)
                have pr := prepare_physical b' d' y' c py pb pd
                have tl := ih (b'::bs) (d'::ds) cs c
                  (by simpa using hl) (by simpa using hs) (by simpa using hc)
                  tailnd tailbits tailsums
                simp only [program,gatePhysical_append]
                exact ⟨⟨⟨pr,tl⟩,mappedEraseCarry_physical _ _ _ _⟩,sm⟩
end ECDSAAdd.Arithmetic.KnownOutputAdder
end

-- source: ECDSAAdd/Arithmetic/SelectedCellPhysical.lean
noncomputable section
namespace ECDSAAdd.Arithmetic
open RecordedQuantum

theorem transcriptWindow_physical (b source flag : Wire) (constant : Bool) (body : Program)
    (hb : b≠flag) (hs : source≠flag) (hp : GatePhysical body) :
    GatePhysical (transcriptSelectWindow b source flag constant body) := by
  have comp : GatePhysical (transcriptSelectCompute b source flag constant) := by
    cases constant <;> simp [transcriptSelectCompute,GatePhysical,PhysicalInstr,ProperGate,hb,hs]
  have expose : GatePhysical (transcriptSelectExpose flag constant) := by
    cases constant <;> simp [transcriptSelectExpose,GatePhysical,PhysicalInstr,ProperGate]
  have erase : GatePhysical (transcriptSelectErase b source flag constant) := by
    cases constant <;> simp [transcriptSelectErase,GatePhysical,PhysicalInstr]
  simp only [transcriptSelectWindow,gatePhysical_append]
  exact ⟨⟨⟨⟨comp,expose⟩,hp⟩,expose⟩,erase⟩

theorem fixedFieldSwap_physical : GatePhysical
    (swapRegisters 2410 (balancedSharedPorts id 2409).r (balancedSharedPorts id 2409).y) := by
  apply physicalGateCheck_correct
  decide +kernel

theorem fixedFieldBodies_physical :
    GatePhysical (OffsetBorrowedCanonical.body id 2409 2410) ∧
    GatePhysical (OffsetBorrowedInverseCanonical.body id 2409 2410) := by
  have x : GatePhysical [.X 2409] := by simp [GatePhysical,PhysicalInstr,ProperGate]
  simp only [OffsetBorrowedCanonical.body,OffsetBorrowedInverseCanonical.body,
    OffsetBorrowedInverseCanonical.double,gatePhysical_append]
  exact ⟨⟨⟨⟨x,fixedForwardField_physical⟩,x⟩,fixedFieldSwap_physical⟩,
    ⟨fixedFieldSwap_physical,⟨⟨x,fixedInverseField_physical⟩,x⟩⟩⟩

theorem fixedSelectedCells_physical (i : Nat) (hi : i<512) (ig is : Bool) :
    GatePhysical (OffsetBorrowedCanonical.cell id 2400 i (1028+i) 2409 2410 ig is) ∧
    GatePhysical (OffsetBorrowedInverseCanonical.cell id 2400 i (1028+i) 2409 2410 ig is) := by
  have outerB : (2400 : Wire) ≠ 2409 := by decide
  have outerS : (i : Wire) ≠ 2409 := by omega
  have innerB : (2400 : Wire) ≠ 2410 := by decide
  have innerS : (1028+i : Wire) ≠ 2410 := by
    exact Nat.ne_of_lt ((Nat.add_lt_add_left hi 1028).trans (by decide))
  exact ⟨transcriptWindow_physical _ _ _ _ _ outerB outerS
    (transcriptWindow_physical _ _ _ _ _ innerB innerS fixedFieldBodies_physical.1),
    transcriptWindow_physical _ _ _ _ _ outerB outerS
    (transcriptWindow_physical _ _ _ _ _ innerB innerS fixedFieldBodies_physical.2)⟩
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/MappedFieldPhysical.lean
noncomputable section
namespace ECDSAAdd.Arithmetic
open RecordedQuantum MappedCompressed

theorem logicalCell_physical (divide : Bool) (i : Nat) (hi : i<512) :
    GatePhysical (logicalCell divide i) := by
  have h := fixedSelectedCells_physical i hi
    (mixedTranscriptUnitTrace.getD i (false,false)).1
    (mixedTranscriptUnitTrace.getD i (false,false)).2
  cases divide <;> simp only [logicalCell,Bool.false_eq_true,if_false,if_true]
  · exact h.2
  · exact h.1

theorem mappedGroup_physical (divide : Bool) (j : Nat) (hj : j<170) :
    GatePhysical (mappedGroup divide j) := by
  have codec := transcriptCodec_physical (compressedHistoryMap (placed j) (3*j))
  have a := gatePhysical_rename _ (placed_injective j) _ (logicalCell_physical divide (3*j) (by omega))
  have b := gatePhysical_rename _ (placed_injective j) _ (logicalCell_physical divide (3*j+1) (by omega))
  have c := gatePhysical_rename _ (placed_injective j) _ (logicalCell_physical divide (3*j+2) (by omega))
  cases divide <;> simp only [mappedGroup,Bool.false_eq_true,if_false,if_true,gatePhysical_append]
  · exact ⟨⟨codec.2,⟨⟨c,b⟩,a⟩⟩,codec.1⟩
  · exact ⟨⟨codec.2,⟨⟨a,b⟩,c⟩⟩,codec.1⟩

theorem mappedGroups_physical (divide : Bool) (j n : Nat) (hj : j+n≤170) :
    GatePhysical (mappedGroups divide j n) := by
  induction n generalizing j with
  | zero => simp [mappedGroups,GatePhysical]
  | succ n ih =>
    have head := mappedGroup_physical divide j (by omega)
    have tail := ih (j+1) (by omega)
    cases divide <;> simp only [mappedGroups,Bool.false_eq_true,if_false,if_true,gatePhysical_append]
    · exact ⟨tail,head⟩
    · exact ⟨head,tail⟩

theorem fixedConverters_physical (canonical : Bool) : GatePhysical (converterPair canonical) := by
  have hn : (skywalkSharedWires id).Nodup := by
    simpa only [skywalkSharedWires,wireBlock,List.map_id] using (List.nodup_range' (s:=0) (n:=2314))
  have ht := balancedSharedTargetConvert_nodup id hn
  have hs := balancedSharedSourceConvert_nodup id hn
  have t := balancedConverters_physical _ ht
  have s := balancedConverters_physical _ hs
  cases canonical <;> simp only [converterPair,Bool.false_eq_true,if_false,if_true,gatePhysical_append]
  · exact ⟨t.1,s.1⟩
  · exact ⟨t.2,s.2⟩

theorem firstMappedGroup_physical (divide : Bool) : GatePhysical (EntryMappedFieldSegmentTrim.firstGroup divide) := by
  have zero : GatePhysical EntryMappedFieldSegmentTrim.logicalZero :=
    transcriptWindow_physical _ _ _ _ _ (by decide) (by decide) fixedFieldSwap_physical
  have z := gatePhysical_rename _ (placed_injective 0) _ zero
  have a := gatePhysical_rename _ (placed_injective 0) _ (logicalCell_physical divide 1 (by decide))
  have b := gatePhysical_rename _ (placed_injective 0) _ (logicalCell_physical divide 2 (by decide))
  have codec := transcriptCodec_physical (compressedHistoryMap (placed 0) 0)
  cases divide <;> simp only [EntryMappedFieldSegmentTrim.firstGroup,Bool.false_eq_true,if_false,if_true,gatePhysical_append]
  · exact ⟨⟨codec.2,⟨⟨b,a⟩,z⟩⟩,codec.1⟩
  · exact ⟨⟨codec.2,⟨⟨z,a⟩,b⟩⟩,codec.1⟩

theorem penultimateCell_physical (divide : Bool) : GatePhysical (PenultimateSwapIdentity.cell divide) := by
  have x : GatePhysical [.X 2409] := by simp [GatePhysical,PhysicalInstr,ProperGate]
  cases divide <;> simp only [PenultimateSwapIdentity.cell,Bool.false_eq_true,if_false,if_true]
  · apply transcriptWindow_physical _ _ _ _ _ (by decide) (by decide)
    simpa only [gatePhysical_append] using And.intro (And.intro x fixedInverseField_physical) x
  · apply transcriptWindow_physical _ _ _ _ _ (by decide) (by decide)
    simpa only [gatePhysical_append] using And.intro (And.intro x fixedForwardField_physical) x

theorem penultimateReplay_physical (divide : Bool) : GatePhysical (PenultimateMapped.replay divide) := by
  have first := firstMappedGroup_physical divide
  have groups := mappedGroups_physical divide 1 169 (by decide)
  have last := gatePhysical_rename _ allPlaced_injective _ (penultimateCell_physical divide)
  cases divide <;> simp only [PenultimateMapped.replay,Bool.false_eq_true,if_false,if_true,gatePhysical_append]
  · exact ⟨⟨last,groups⟩,first⟩
  · exact ⟨⟨first,groups⟩,last⟩

theorem fixedCopy_physical : GatePhysical
    (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a) := by
  apply physicalGateCheck_correct
  decide +kernel

theorem selectedFieldSegment_physical (divide : Bool) : GatePhysical (PenultimateMapped.fieldSegment divide) := by
  have cp := gatePhysical_rename _ allPlaced_injective _ fixedCopy_physical
  have cent := gatePhysical_rename _ allPlaced_injective _ (fixedConverters_physical false)
  have canon := gatePhysical_rename _ allPlaced_injective _ (fixedConverters_physical true)
  have replay := penultimateReplay_physical divide
  have empty : GatePhysical [] := by simp [GatePhysical]
  cases divide <;> simp only [PenultimateMapped.fieldSegment,Bool.false_eq_true,if_false,if_true,gatePhysical_append]
  · exact ⟨⟨⟨⟨cp,cent⟩,replay⟩,canon⟩,empty⟩
  · exact ⟨⟨⟨⟨empty,cent⟩,replay⟩,canon⟩,cp⟩
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/NativeFirstPhysical.lean
noncomputable section
namespace ECDSAAdd.Arithmetic.NativeFirstDirect
open RecordedQuantum

theorem adds_physical (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) (inv : Bool) :
    GatePhysical (hAdd w inv) ∧ GatePhysical (kAdd w inv) := by
  have h : GatePhysical (hAdd w inv) := by
    apply mappedAdd_physical _ _ _ _ (h_inputs_nd w hn)
    intro b hb q hq
    apply h_sources_fresh w hn inv q
    exact List.mem_flatMap.mpr ⟨b,hb,by simpa using hq⟩
  have k : GatePhysical (mappedAdd (kBits w inv) (wireBlock w 771 257) (wireBlock w 1540 256) (w 770)) := by
    apply mappedAdd_physical _ _ _ _ (k_inputs_nd w hn)
    intro b hb q hq
    apply k_sources_fresh w hn inv q
    exact List.mem_flatMap.mpr ⟨b,hb,by simpa using hq⟩
  refine ⟨h,?_⟩
  rw [kAdd,gatePhysical_append]
  exact ⟨k,by simp [GatePhysical,PhysicalInstr,ProperGate]⟩

theorem programs_physical (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) :
    GatePhysical (forward w) ∧ GatePhysical (inverse w) := by
  have cp : GatePhysical (lowCopy w) := copyRegister_physical none _ _ (copy_inputs_nd w hn) (by simp)
  have ro := rotate_physical (wireBlock w 770 258) (block_nodup w hn _ _ (by omega))
  have a := adds_physical w hn false
  have b := adds_physical w hn true
  have n1 := index_ne w hn 770 1028 (by omega) (by omega) (by omega)
  have n2 := index_ne w hn 1028 0 (by omega) (by omega) (by omega)
  have n3 := index_ne w hn 1028 770 (by omega) (by omega) (by omega)
  have pre : GatePhysical [.CX (w 770) (w 1028),.CX (w 1028) (w 0),.X (w 0)] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,n1,n2]
  have post : GatePhysical [.X (w 0),.CX (w 1028) (w 0),.CX (w 770) (w 1028)] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,n1,n2]
  have mid : GatePhysical [.CX (w 1028) (w 770)] := by simp [GatePhysical,PhysicalInstr,ProperGate,n3]
  simp only [forward,inverse,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨⟨pre,cp⟩,a.1⟩,mid⟩,ro.1⟩,a.2⟩,⟨⟨⟨⟨⟨b.2,ro.2⟩,mid⟩,b.1⟩,cp⟩,post⟩⟩
end ECDSAAdd.Arithmetic.NativeFirstDirect
end

-- source: ECDSAAdd/Arithmetic/NativeKnownPhysical.lean
noncomputable section

namespace ECDSAAdd.Arithmetic.NativeFirstKnown
open NativeFirstDirect RecordedQuantum

 theorem hReceiver_physical (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) :
    GatePhysical (hReceiver w) := by
  rw [hReceiver,sealedProgram_eq]
  apply KnownOutputAdder.program_physical
  · simp [hBits_length,wireBlock_length]
  · simp [desired_length,wireBlock_length]
  · simp [wireBlock_length]
  · exact h_inputs_nd w hn
  · intro b hb q hq
    apply h_sources_fresh w hn true q
    exact List.mem_flatMap.mpr ⟨b,hb,by simpa using hq⟩
  · intro b hb q hq
    apply desired_fresh w hn q
    exact List.mem_flatMap.mpr ⟨b,hb,by simpa using hq⟩

theorem inverse_physical (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) :
    GatePhysical (inverse w) := by
  have ka := (adds_physical w hn true).2
  have hr := hReceiver_physical w hn
  have cp : GatePhysical (lowCopy w) := copyRegister_physical none _ _ (copy_inputs_nd w hn) (by simp)
  have ro := (rotate_physical (wireBlock w 770 258) (block_nodup w hn _ _ (by omega))).2
  have n1 := index_ne w hn 770 1028 (by omega) (by omega) (by omega)
  have n2 := index_ne w hn 1028 0 (by omega) (by omega) (by omega)
  have n3 := index_ne w hn 1028 770 (by omega) (by omega) (by omega)
  have post : GatePhysical [.X (w 0),.CX (w 1028) (w 0),.CX (w 770) (w 1028)] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,n1,n2]
  have mid : GatePhysical [.CX (w 1028) (w 770)] := by simp [GatePhysical,PhysicalInstr,ProperGate,n3]
  simp only [inverse,inverseUnmiddle,inverseBack,gatePhysical_append]
  exact ⟨⟨⟨ka,ro,mid⟩,hr⟩,cp,post⟩

end ECDSAAdd.Arithmetic.NativeFirstKnown
end

-- source: ECDSAAdd/Arithmetic/MappedKernelPhysical.lean
noncomputable section
namespace ECDSAAdd.Arithmetic
open RecordedQuantum MappedCompressed

theorem mappedClear_physical : GatePhysical (skywalkArithmeticClear base) := by
  simp [skywalkArithmeticClear,skywalkTerminalClear,base,GatePhysical,PhysicalInstr,ProperGate]

theorem mappedKernel_physical (divide : Bool) : GatePhysical (kernel divide) := by
  have first := (NativeFirstDirect.programs_physical base base_pool_nodup).1
  have loops := compressedLoops_physical base 1 511 (by decide) base_pool_nodup
  have last := NativeFirstKnown.inverse_physical base base_pool_nodup
  have field : GatePhysical (MappedCompressed.selectedFieldSegment divide) := selectedFieldSegment_physical divide
  simp only [kernel,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨⟨first,loops.1⟩,mappedClear_physical⟩,field⟩,mappedClear_physical⟩,loops.2⟩,last⟩

theorem mappedControlled_physical (divide : Bool) : GatePhysical (controlled divide) := by
  apply directZero_physical _ _ _ _ _ _ (mappedKernel_physical divide)
  decide +kernel
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PhysicalSupportRename.lean
noncomputable section
namespace ECDSAAdd.Arithmetic
open RecordedQuantum

theorem gatePhysical_rename_support (f : Wire → Wire) (p : Program)
    (hf : ∀ a∈wires p,∀ b∈wires p,f a=f b → a=b) (hp : GatePhysical p) :
    GatePhysical (renameProgram f p) := by
  induction p with
  | nil => simp [renameProgram,GatePhysical]
  | cons i p ih =>
    have first : PhysicalInstr (.gate i) := hp i (by simp)
    have sub : ∀ a∈i.wires,∀ b∈i.wires,f a=f b → a=b := by
      intro a ha b hb eq
      exact hf a (Finset.mem_union_left _ ha) b (Finset.mem_union_left _ hb) eq
    have head : GatePhysical (renameProgram f [i]) := by
      cases i with
      | X t => simp [renameProgram,renameInstr,GatePhysical,PhysicalInstr,ProperGate]
      | measureX t a b => simp [renameProgram,renameInstr,GatePhysical,PhysicalInstr]
      | CX c t =>
        have ne : f c≠f t := fun eq => first (sub c (by simp [Instr.wires]) t (by simp [Instr.wires]) eq)
        simpa [renameProgram,renameInstr,GatePhysical,PhysicalInstr,ProperGate] using ne
      | CCX a b t =>
        have na : f a≠f t := fun eq => first.1 (sub a (by simp [Instr.wires]) t (by simp [Instr.wires]) eq)
        have nb : f b≠f t := fun eq => first.2 (sub b (by simp [Instr.wires]) t (by simp [Instr.wires]) eq)
        simpa [renameProgram,renameInstr,GatePhysical,PhysicalInstr,ProperGate] using And.intro na nb
    have tail := ih (fun a ha b hb eq => hf a (Finset.mem_union_right _ ha) b (Finset.mem_union_right _ hb) eq)
      (fun j hj => hp j (by simp [hj]))
    change GatePhysical (renameProgram f [i] ++ renameProgram f p)
    exact (gatePhysical_append _ _).mpr ⟨head,tail⟩
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointFixedPrimitivesPhysical.lean
noncomputable section
namespace ECDSAAdd.Arithmetic
open RecordedQuantum Secp256k1

theorem zeroControlled_physical (c target : Wire) (bs : List ZeroBit)
    (hn : (c :: target :: bs.flatMap ZeroBit.wires).Nodup) :
    GatePhysical (zeroControlled c target bs) := by
  induction bs generalizing c with
  | nil =>
    have h : c ≠ target := by simpa using (List.nodup_cons.mp hn).1
    simpa [zeroControlled,GatePhysical,PhysicalInstr,ProperGate] using h
  | cons b bs ih =>
    have ht : (b.work :: target :: bs.flatMap ZeroBit.wires).Nodup := by
      apply List.nodup_iff_count.mpr; intro q
      have h := List.nodup_iff_count.mp hn q
      simp only [List.flatMap_cons,ZeroBit.wires,List.count_cons,List.count_append,List.count_nil] at h ⊢
      omega
    have hcw : c ≠ b.work := by
      intro he; subst c
      have h := List.nodup_iff_count.mp hn b.work
      simp only [List.flatMap_cons,ZeroBit.wires,List.count_cons,List.count_append,List.count_nil,
        beq_self_eq_true,ite_true] at h; omega
    have hiw : b.input ≠ b.work := by
      intro he
      have h := List.nodup_iff_count.mp hn b.work
      simp only [List.flatMap_cons,ZeroBit.wires,List.count_cons,List.count_append,List.count_nil,
        he,beq_self_eq_true,ite_true] at h; omega
    change GatePhysical ([.X b.input,.CCX c b.input b.work,.X b.input] ++
      zeroControlled b.work target bs ++ [.X b.input,.measureX b.work [] [.CZ c b.input],.X b.input])
    simp only [gatePhysical_append]
    exact ⟨⟨by simp [GatePhysical,PhysicalInstr,ProperGate,hcw,hiw],ih _ ht⟩,
      by simp [GatePhysical,PhysicalInstr,ProperGate]⟩

theorem equalConstant_physical (c target : Wire) (bs : List ZeroBit) (k : Nat)
    (hn : (c :: target :: bs.flatMap ZeroBit.wires).Nodup) :
    GatePhysical (equalConstant c target bs k) := by
  simp only [equalConstant,gatePhysical_append]
  exact ⟨⟨xorConstant_physical _ _,zeroControlled_physical _ _ _ hn⟩,xorConstant_physical _ _⟩

theorem compactRecoveryConstant_physical (K : MeasuredCanonicalModLayout) (control : Wire)
    (c p k : Nat) (hn : (control :: K.wires).Nodup) :
    GatePhysical (compactRecoveryConstant K control c p k) := by
  have hc : control ∉ K.src := by
    intro h; exact (List.nodup_cons.mp hn).1 (by simp [MeasuredCanonicalModLayout.wires,h])
  simp only [compactRecoveryConstant,gatePhysical_append]
  exact ⟨⟨maskedConstant_physical _ _ _ hc,K.physical c p (List.nodup_cons.mp hn).2⟩,
    maskedConstant_physical _ _ _ hc⟩

theorem CompactRecoveryNegateLayout.reflection_physical (L : CompactRecoveryNegateLayout)
    (control : Wire) (p : Nat) (hn : (L.wires control).Nodup) :
    GatePhysical (L.reflection control p) := by
  have count := List.nodup_iff_count.mp hn
  have hc : control ∉ L.word := by
    intro hm; have h := count control; have hh := List.count_pos_iff.mpr hm
    simp only [wires,List.count_cons,List.count_append,beq_self_eq_true,ite_true] at h; omega
  have nd : (L.cin :: L.word ++ L.carries).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := count q
    have ht := (List.take_sublist (L.word.length-1) L.work).count_le q
    simp only [wires,carries,List.count_cons,List.count_append] at h ⊢; omega
  have hs : ∀ q ∈ some control, q ∉ L.cin :: L.word ++ L.carries := by
    intro q hq hm
    have he : control = q := by simpa using hq
    subst q
    have h := count control; have hh := List.count_pos_iff.mpr hm
    have ht := (List.take_sublist (L.word.length-1) L.work).count_le control
    simp only [wires,carries,List.count_cons,List.count_append,beq_self_eq_true,ite_true] at h hh
    omega
  simp only [reflection,complement,add,gatePhysical_append]
  exact ⟨maskedConstant_physical _ _ _ hc,mappedConstAdd_physical _ _ _ _ _ nd hs⟩

theorem maskedPointConstant_physical (c : Wire) (r : PointReg) (C : Point)
    (hc : c ∉ PointAddLayout.pointWires r) : GatePhysical (maskedPointConstant c r C) := by
  have hf : c ∉ [r.finite] := fun h => hc (by simpa [PointAddLayout.pointWires] using Or.inl h)
  have hx : c ∉ r.x := fun h => hc (by simp [PointAddLayout.pointWires,h])
  have hy : c ∉ r.y := fun h => hc (by simp [PointAddLayout.pointWires,h])
  simp only [maskedPointConstant,gatePhysical_append]
  exact ⟨⟨maskedConstant_physical _ _ _ hf,maskedConstant_physical _ _ _ hx⟩,
    maskedConstant_physical _ _ _ hy⟩

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/PointFixedPhysical.lean
noncomputable section
namespace ECDSAAdd.Arithmetic
open RecordedQuantum Secp256k1 ControlledPointLayout

theorem pointDialogConstantAdd_physical (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y) (k : Fp) :
    GatePhysical (pointDialogConstantAdd L r k) :=
  compactRecoveryConstant_physical _ _ _ _ _ (L.recoveryConstant_nodup hw hn r hr)

theorem pointRecoveryStage_physical (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (cx cy : Fp) : GatePhysical (pointRecoveryStage L cx cy) := by
  simp only [pointRecoveryStage,gatePhysical_append]
  exact ⟨⟨CompactRecoveryNegateLayout.reflection_physical _ _ _ (L.recoveryNegate_nodup hw hn),
    pointDialogConstantAdd_physical L hw hn _ (Or.inl rfl) _⟩,
    pointDialogConstantAdd_physical L hw hn _ (Or.inr rfl) _⟩

theorem dialogEqual_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (c t : Wire) (hc : c=L.control ∨ c∈L.inPlaceFlags) (ht : t∈L.inPlaceFlags)
    (hct : c≠t) (k : Nat) : GatePhysical (equalConstant c t L.dialogPointZero k) := by
  apply equalConstant_physical
  have h := L.dialogPointZero_nodup hn c t hct hc ht
  have len : (PointAddLayout.pointWires L.point).length = (L.dialogPool.take 513).length := by
    have hx : L.point.x.length = 256 := hw.inputX
    have hy : L.point.y.length = 256 := hw.inputY
    simp [PointAddLayout.pointWires,hx,hy,L.dialogPool_length hw]
  exact ((zeroPorts_perm _ _ len).cons t |>.cons c).nodup_iff.mpr h

theorem pointDialogFlags_physical (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (cy : Fp) (C : Point) :
    GatePhysical (pointInPlaceDoubleEnable L cy) ∧
    GatePhysical (pointDialogExceptionEnable L C) ∧
    GatePhysical (pointDialogGenericFlag L) := by
  have h := dialogFlag_separation (L:=L) hn
  simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at h
  constructor
  · unfold pointInPlaceDoubleEnable
    split <;> simp_all [GatePhysical,PhysicalInstr,ProperGate]
  constructor
  · unfold pointDialogExceptionEnable
    split <;> simp_all [GatePhysical,PhysicalInstr,ProperGate]
  · simp_all [pointDialogGenericFlag,pointInPlaceGenericFlag,GatePhysical,PhysicalInstr,ProperGate,ne_comm]

theorem pointDialogCorners_physical (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (C : Point) : GatePhysical (pointDialogCorners L C) := by
  have away (c : Wire) (hc : c ∈ L.inPlaceFlags) : c ∉ PointAddLayout.pointWires L.point := by
    intro hm
    have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) c
    have hf := List.count_pos_iff.mpr hc
    have hp := List.count_pos_iff.mpr hm
    simp only [dialogUsedWires,List.count_append,List.count_cons] at h
    omega
  have all (c : Wire) (hc : c ∈ L.inPlaceFlags) (D : Point) : GatePhysical (maskedPointConstant c L.point D) :=
    maskedPointConstant_physical c L.point D (away c hc)
  simp only [pointDialogCorners,pointInPlaceCorners,gatePhysical_append]
  repeat constructor
  all_goals apply all _ (by simp [inPlaceFlags])

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/SkywalkPointPhysical.lean
noncomputable section
namespace ECDSAAdd.Arithmetic
open RecordedQuantum Secp256k1 ControlledPointLayout MappedCompressed
attribute [local irreducible] controlled wires

theorem pointCompressedArithmetic_physical (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (multiply : Bool) : GatePhysical (pointCompressedArithmetic L multiply) := by
  apply gatePhysical_rename_support (pointWireFn L) (controlled (!multiply))
  · intro a ha b hb eq
    exact pointWireFn_injective_slots L hw hn a (controlled_support (!multiply) ha) b (controlled_support (!multiply) hb) eq
  · exact mappedControlled_physical _

theorem skywalkGeneric_physical (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (cx cy : Fp) : GatePhysical (pointCompressedDialogGeneric L cx cy) := by
  have ax (k : Fp) := pointDialogConstantAdd_physical L hw hn L.point.x (Or.inl rfl) k
  have ay (k : Fp) := pointDialogConstantAdd_physical L hw hn L.point.y (Or.inr rfl) k
  have di := pointCompressedArithmetic_physical L hw hn false
  have mu := pointCompressedArithmetic_physical L hw hn true
  have sq := CompressedPointSquare.computableProgram_physical L hw hn
  have recovery := pointRecoveryStage_physical L hw hn cx cy
  simp only [pointCompressedDialogGeneric,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨⟨ax _,ay _⟩,di⟩,sq⟩,ax _⟩,mu⟩,recovery⟩
theorem skywalkFinite_physical (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (C : Point) (cx cy : Fp) :
    GatePhysical (pointCompressedDialogFinite L C cx cy) := by
  have sep := dialogFlag_separation (L:=L) hn
  have eq1 (k : Nat) := dialogEqual_physical L hw hn L.control L.infinitySelect
    (Or.inl rfl) (by simp [inPlaceFlags])
    (by simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true] at sep; tauto) k
  have eq2 (k : Nat) := dialogEqual_physical L hw hn L.core.double L.doubleSelect
    (Or.inr (by simp [inPlaceFlags])) (by simp [inPlaceFlags])
    (by simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true] at sep; tauto) k
  have eq3 (k : Nat) := dialogEqual_physical L hw hn L.control L.genericSelect
    (Or.inl rfl) (by simp [inPlaceFlags])
    (by simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true] at sep; tauto) k
  have eq4 (k : Nat) := dialogEqual_physical L hw hn L.core.equalX L.core.equalNegY
    (Or.inr (by simp [inPlaceFlags])) (by simp [inPlaceFlags])
    (by simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true] at sep; tauto) k
  have fl := pointDialogFlags_physical L hn cy C
  have ge := skywalkGeneric_physical L hw hn cx cy
  have co := pointDialogCorners_physical L hn C
  simp only [pointCompressedDialogFinite,gatePhysical_append]
  simp only [eq1,eq2,eq3,eq4,fl.1,fl.2.1,fl.2.2,ge,co,and_self]

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ValueWalkPointConstant.lean
/- PR #80 的值走点加路径；与 Skywalk 共享布局、语义及基础算术。 -/
noncomputable section

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

def valueWalkPointDialogConstantAdd (L : ControlledPointLayout) (r : List Wire) (k : Fp) : Program :=
  maskedConstant L.core.generic (L.dialogUnary r).a k.val ++
    modAddInPlace (L.dialogUnary r) p ++ maskedConstant L.core.generic (L.dialogUnary r).a k.val

/-- 常数加法在低256位上给出规范结果，源、目标高位及其余线路逐线恢复。 -/
theorem valueWalkPointDialogConstantAdd_correct (L : ControlledPointLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y)
    (k : Fp) (Z : Nat) (B : Bool) (hZ : Z<p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hz : regValue r s.basis=Z)
    (hc : regValue L.dialogPool s.basis=0) :
    (run (valueWalkPointDialogConstantAdd L r k) m s).phase=s.phase ∧
      regValue r (run (valueWalkPointDialogConstantAdd L r k) m s).basis=(Z+(if B then k.val else 0))%p ∧
      ∀ q∉r,(run (valueWalkPointDialogConstantAdd L r k) m s).basis q=s.basis q := by
  let M := L.dialogUnary r
  have hl : r.length=256 := by rcases hr with rfl | rfl; exact hw.inputX; exact hw.inputY
  have hM := L.dialogUnary_widths hw r hl
  have hnm : (L.core.generic::M.wires).Nodup := L.dialogUnary_nodup hw hnd r hr
  have hs : L.dialogPool.take 257++[L.core.poolWire 257]++M.work ⊆ L.dialogPool := by
    change (L.dialogUnary r).a++[(L.dialogUnary r).high]++(L.dialogUnary r).work ⊆ _
    rw [L.dialogUnary_borrow hw r]
    exact (List.take_sublist _ _).subset
  have clean := (regValue_zero _ _).mp hc
  have hhigh : s.basis (L.core.poolWire 257)=false := clean _ (hs (by simp))
  have ha : M.a=L.dialogPool.take 257 := by simp only [M,dialogUnary]
  have hsource : regValue M.a s.basis=0 := by
    rw [ha]
    exact (regValue_zero _ _).mpr
      (fun q hq => clean q (hs (List.mem_append_left _ (List.mem_append_left _ hq))))
  have hwork : regValue M.work s.basis=0 := (regValue_zero _ _).mpr
    (fun q hq => clean q (hs (List.mem_append_right _ hq)))
  have hout : regValue M.z s.basis=Z := by
    simp only [M,dialogUnary,ModInPlaceLayout.z,ModAddCoreLayout.z]
    rw [regValue_append,hz]
    simp [regValue,hhigh]
  obtain ⟨hp,hv⟩ := constant_program_spec M L.core.generic k.val Z B hM hnm k.isLt hZ
    s m ⟨⟨⟨hb,hsource⟩,hout⟩,hwork⟩
  have keep := constant_program_frame M L.core.generic k.val Z B hM hnm k.isLt hZ s m hb hsource hout hwork
  have hzView : M.z=r++[L.core.poolWire 257] := by
    simp only [M,dialogUnary,ModInPlaceLayout.z,ModAddCoreLayout.z]
  rw [hzView] at hv
  have hlow := (regValue_low_iff r [L.core.poolWire 257]
    (run (valueWalkPointDialogConstantAdd L r k) m s).basis ((Z+(if B then k.val else 0))%p)
    (by rw [hl]; exact (Nat.mod_lt _ (by norm_num [p])).trans (by norm_num [p]))).mp hv.1.2
  refine ⟨hp,hlow.1,?_⟩
  intro q hq
  by_cases he : q=L.core.poolWire 257
  · subst q
    exact ((regValue_zero _ _).mp hlow.2 _ (by simp)).trans hhigh.symm
  · apply keep q
    simp only [M,dialogUnary,ModInPlaceLayout.z,ModAddCoreLayout.z]
    simp [hq,he]

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ValueWalkPointDivide.lean
/- PR #80 的值走点加路径；与 Skywalk 共享布局、语义及基础算术。 -/
noncomputable section

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

/-- 同一原地乘除视图；目标高位归零后，只有低256位载荷改变。 -/
theorem valueWalkPointDialog_arithmetic_correct (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (multiply : Bool) (X Y : Nat) (B : Bool)
    (hX : X<p) (hX0 : B=true → X≠0) (hY : Y<p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=X)
    (hy : regValue L.point.y s.basis=Y) (hc : regValue L.dialogPool s.basis=0) :
    let circuit := if multiply then dialogMultiply L.dialogPort p else dialogDivide L.dialogPort p
    let V := if B then (if multiply then ((Y:Fp)*(X:Fp)).val else ((Y:Fp)/(X:Fp)).val) else Y
    (run circuit m s).phase=s.phase ∧ regValue L.point.y (run circuit m s).basis=V ∧
      ∀ q∉L.point.y,(run circuit m s).basis q=s.basis q := by
  dsimp only
  let D := L.dialogPort
  have hd : D.Widths := DialogLayout.fromPool_widths _ _ _ _
  have nd := L.dialogPort_nodup hw hn
  have fields := L.dialogPort_fields hw
  have hwork : D.work ⊆ L.dialogPool := fun {_} h =>
    (List.take_subset 2612 L.dialogPool) ((L.dialogPort_work hw).subset h)
  have highMem : L.core.poolWire 2612∈L.dialogPool := by
    have h := L.dialogBit_prefix hw 2612 (by omega)
    have hh : L.core.poolWire 2612∈L.dialogPool.take 2612++[L.core.poolWire 2612] := by simp
    rw [h] at hh
    exact List.take_subset _ _ hh
  have hhigh := (regValue_zero _ _).mp hc _ highMem
  have hyD : regValue D.y s.basis=Y := by
    rw [fields.2.2,regValue_append,hy]; simp [regValue,hhigh]
  have hcD : regValue D.work s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hc q (hwork hq))
  have hbD : s.basis D.control=B := fields.1 ▸ hb
  have hxD : regValue D.x s.basis=X := fields.2.1 ▸ hx
  have hv :
      (run (if multiply then dialogMultiply D p else dialogDivide D p) m s).phase=s.phase ∧
      Holds.holds (run (if multiply then dialogMultiply D p else dialogDivide D p) m s).basis
        D.control B ∧
      regValue D.x (run (if multiply then dialogMultiply D p else dialogDivide D p) m s).basis=X ∧
      regValue D.y (run (if multiply then dialogMultiply D p else dialogDivide D p) m s).basis=
        (if B then (if multiply then ((Y:Fp)*(X:Fp)).val else ((Y:Fp)/(X:Fp)).val) else Y) ∧
      regValue D.work (run (if multiply then dialogMultiply D p else dialogDivide D p) m s).basis=0 := by
    cases multiply
    · simpa only [Bool.false_eq_true,if_false,Holds.holds,and_assoc] using
        dialogDivide_spec D hd nd B X Y hX hX0 hY s m ⟨⟨⟨hbD,hxD⟩,hyD⟩,hcD⟩
    · simpa only [if_true,Holds.holds,and_assoc] using
        dialogMultiply_spec D hd nd B X Y hX hX0 hY s m ⟨⟨⟨hbD,hxD⟩,hyD⟩,hcD⟩
  have bound : (if B then (if multiply then ((Y:Fp)*(X:Fp)).val else ((Y:Fp)/(X:Fp)).val) else Y)<p := by
    split
    · split <;> exact ZMod.val_lt _
    · exact hY
  have low := (regValue_low_iff L.point.y [L.core.poolWire 2612] _
    _ (by rw [show L.point.y.length=256 from hw.inputY]; exact bound.trans (by norm_num [p]))).mp
    (fields.2.2 ▸ hv.2.2.2.1)
  refine ⟨hv.1,low.1,?_⟩
  intro q hq
  by_cases hg : q=D.control
  · subst q; exact hv.2.1.trans hbD.symm
  by_cases hxx : q∈D.x
  · exact (regValue_eq_iff _ _ _).mp (hv.2.2.1.trans hxD.symm) q hxx
  by_cases hh : q=L.core.poolWire 2612
  · subst q; exact ((regValue_zero _ _).mp low.2 _ (by simp)).trans hhigh.symm
  by_cases hwq : q∈D.work
  · exact (regValue_eq_iff _ _ _).mp (hv.2.2.2.2.trans hcD.symm) q hwq
  have outside : q∉D.wires := by
    intro mem
    have h := D.external_value_perm.mem_iff.mpr mem
    have hrest : q∉D.first.valueTapeWires D.records := fun hh =>
      hwq (List.mem_append_left _ hh)
    have hz : q∉D.z := fun hh => hwq (List.mem_append_right _ hh)
    change q∈(D.control::D.x++D.y++D.z)++D.first.valueTapeWires D.records at h
    simp only [List.mem_append,List.mem_cons] at h
    have hyq : q∉D.y := by rw [fields.2.2]; simp [hq,hh]
    rcases h with (((hg' | hx') | hy') | hz') | hr
    · exact hg hg'
    · exact hxx hx'
    · exact hyq hy'
    · exact hz hz'
    · exact hrest hr
  have frame := dialog_frame D p hd nd s m q outside
  dsimp only [D] at frame
  by_cases hm : multiply=true
  · rw [if_pos hm]; exact frame.2
  · rw [if_neg hm]; exact frame.1
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ValueWalkPointNegate.lean
/- PR #80 的值走点加路径；与 Skywalk 共享布局、语义及基础算术。 -/
noncomputable section

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout

def valueWalkPointDialogNegate (L : ControlledPointLayout) : Program :=
  controlledModSub L.core.generic L.dialogNegate p ++
    swapRegisters L.core.generic L.point.x L.dialogNegate.low ++
    controlledModAdd L.core.generic L.dialogNegate p

private theorem negate_swap_ValueWalkPointNegate (L : ControlledPointLayout) (hw : L.Widths) (hnd : L.wires.Nodup)
    (A T : Nat) (B : Bool) (hA : A<p) (hT : T<p) :
    (Triple (fun st => ((Holds.holds st L.core.generic B ∧ Holds.holds st L.dialogNegate.a A) ∧ Holds.holds st L.dialogNegate.z T) ∧ Holds.holds st L.dialogNegate.work 0) (swapRegisters L.core.generic L.point.x L.dialogNegate.low)
      (fun st => ((Holds.holds st L.core.generic B ∧ Holds.holds st L.dialogNegate.a (if B then T else A)) ∧ Holds.holds st L.dialogNegate.z (if B then A else T)) ∧ Holds.holds st L.dialogNegate.work 0)) := by
  have hn := L.dialogNegate_nodup hw hnd
  have hm := L.dialogNegate_widths hw
  have he : L.dialogNegate.a=L.point.x++[L.core.poolWire 0] := by
    simp only [dialogNegate]
  have hswap : (L.core.generic::L.point.x++L.dialogNegate.low).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [ModInPlaceLayout.wires,he,ModInPlaceLayout.z,ModAddCoreLayout.z,
      List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have away (q : Wire) (hq : q∈L.core.generic::L.core.poolWire 0::L.dialogNegate.high::L.dialogNegate.work) :
      q∉L.point.x ∧ q∉L.dialogNegate.low := by
    have h := List.nodup_iff_count.mp hn q
    have hpos := List.count_pos_iff.mpr hq
    simp only [ModInPlaceLayout.wires,he,ModInPlaceLayout.z,ModAddCoreLayout.z,
      List.count_append,List.count_cons,List.count_nil] at h hpos
    constructor
    all_goals intro hq'; have hp := List.count_pos_iff.mpr hq'; omega
  intro s m h
  simp only [Holds.holds] at h ⊢
  have hp : p<2^256 := by norm_num [p]
  have hx := (regValue_low_iff L.point.x [L.core.poolWire 0] s.basis A
    (by rw [show L.point.x.length=256 from hw.inputX]; exact hA.trans hp)).mp (he ▸ h.1.1.2)
  have ht := (regValue_low_iff L.dialogNegate.low [L.dialogNegate.high] s.basis T
    (by rw [hm.core.low]; exact hT.trans hp)).mp h.1.2
  obtain ⟨hphase,hframe,hx',ht'⟩ := swapRegisters_correct L.core.generic L.point.x L.dialogNegate.low
    (hw.inputX.trans hm.core.low.symm) hswap s m
  have keep (q : Wire) (hq : q∈L.core.generic::L.core.poolWire 0::L.dialogNegate.high::L.dialogNegate.work) :=
    hframe q (away q hq).1 (away q hq).2
  have h0 := keep (L.core.poolWire 0) (by simp)
  have h1 := keep L.dialogNegate.high (by simp)
  have high0 := (regValue_zero _ _).mp hx.2 (L.core.poolWire 0) (by simp)
  have high1 := (regValue_zero _ _).mp ht.2 L.dialogNegate.high (by simp)
  refine ⟨hphase,⟨⟨(keep _ (by simp)).trans h.1.1.1,?_⟩,?_⟩,?_⟩
  · rw [he,regValue_append,hx',h.1.1.1,ht.1,hx.1]
    simp [regValue,h0,high0]
  · change regValue (L.dialogNegate.low++[L.dialogNegate.high]) _=_
    rw [regValue_append,ht',h.1.1.1,hx.1,ht.1]
    simp [regValue,h1,high1]
  · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans h.2

/-- 规范取负的三阶段规格；关闭控制时仍执行固定门列并清理临时寄存器。 -/
theorem valueWalkPointDialogNegate_spec (L : ControlledPointLayout) (hw : L.Widths) (hnd : L.wires.Nodup)
    (A : Nat) (B : Bool) (hA : A<p) :
    (Triple (fun st => ((Holds.holds st L.core.generic B ∧ Holds.holds st L.dialogNegate.a A) ∧ Holds.holds st L.dialogNegate.z 0) ∧ Holds.holds st L.dialogNegate.work 0) (valueWalkPointDialogNegate L)
      (fun st => ((Holds.holds st L.core.generic B ∧ Holds.holds st L.dialogNegate.a (if B then (p-A)%p else A)) ∧ Holds.holds st L.dialogNegate.z 0) ∧ Holds.holds st L.dialogNegate.work 0)) := by
  have hp : 0<p := by norm_num [p]
  have hpn : p<2^256 := by norm_num [p]
  have hm := L.dialogNegate_widths hw
  have hn := L.dialogNegate_nodup hw hnd
  have hs := controlledModSub_spec L.core.generic L.dialogNegate 256 p A 0 B hm hn hp hpn
    (Nat.le_of_lt hA) hp
  simp only [Nat.zero_add] at hs
  have ht := negate_swap_ValueWalkPointNegate L hw hnd A (if B then (p-A)%p else 0) B hA
    (by split; exact Nat.mod_lt _ hp; exact hp)
  have ha := controlledModAdd_spec L.core.generic L.dialogNegate 256 p
    (if B then (if B then (p-A)%p else 0) else A) (if B then A else (if B then (p-A)%p else 0)) B
    hm hn hp hpn (by cases B <;> simp; omega; exact Nat.le_of_lt (Nat.mod_lt _ hp))
    (by cases B <;> simp; exact hp; exact hA)
  have hresult : (if B then ((if B then A else (if B then (p-A)%p else 0))+
      (if B then (if B then (p-A)%p else 0) else A))%p else (if B then A else (if B then (p-A)%p else 0)))=0 := by
    cases B
    · rfl
    · simp only [if_true]
      rw [Nat.add_mod_mod,Nat.add_sub_of_le (Nat.le_of_lt hA),Nat.mod_self]
  have h := (hs.seq ht).seq ha
  have he : (if B then (if B then (p-A)%p else 0) else A)=(if B then (p-A)%p else A) := by cases B <;> rfl
  rw [hresult] at h
  simpa only [valueWalkPointDialogNegate,he] using h

/-- 取负后仅输入x的低位改变，临时差、高位与所有其它线路恢复。 -/
theorem valueWalkPointDialogNegate_correct (L : ControlledPointLayout) (hw : L.Widths) (hnd : L.wires.Nodup)
    (A : Nat) (B : Bool) (hA : A<p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=A)
    (hc : regValue L.dialogPool s.basis=0) :
    (run (valueWalkPointDialogNegate L) m s).phase=s.phase ∧
      regValue L.point.x (run (valueWalkPointDialogNegate L) m s).basis=(if B then (p-A)%p else A) ∧
      ∀ q∉L.point.x,(run (valueWalkPointDialogNegate L) m s).basis q=s.basis q := by
  have hm := L.dialogNegate_widths hw
  have hp : 0<p := by norm_num [p]
  have hp2 : p<2^256 := by norm_num [p]
  have he : L.dialogNegate.a=L.point.x++[L.core.poolWire 0] := by simp only [dialogNegate]
  have hs : [L.core.poolWire 0]++L.dialogNegate.z++L.dialogNegate.work ⊆ L.dialogPool := by
    rw [L.dialogNegate_borrow hw]
    exact (List.take_sublist _ _).subset
  have clean := (regValue_zero _ _).mp hc
  have hhigh : s.basis (L.core.poolWire 0)=false := clean _ (hs (by simp))
  have ha : regValue L.dialogNegate.a s.basis=A := by
    rw [he,regValue_append,hx]
    simp [regValue,hhigh]
  have hz : regValue L.dialogNegate.z s.basis=0 := (regValue_zero _ _).mpr
    (fun q hq => clean q (hs (List.mem_append_left _ (List.mem_append_right _ hq))))
  have hwork : regValue L.dialogNegate.work s.basis=0 := (regValue_zero _ _).mpr
    (fun q hq => clean q (hs (List.mem_append_right _ hq)))
  obtain ⟨hphase,hv⟩ := valueWalkPointDialogNegate_spec L hw hnd A B hA s m ⟨⟨⟨hb,ha⟩,hz⟩,hwork⟩
  have hvbound : (if B then (p-A)%p else A)<p := by split; exact Nat.mod_lt _ hp; exact hA
  have hlow := (regValue_low_iff L.point.x [L.core.poolWire 0] (run (valueWalkPointDialogNegate L) m s).basis
    (if B then (p-A)%p else A) (by rw [show L.point.x.length=256 from hw.inputX]; exact hvbound.trans hp2)).mp
    (he ▸ hv.1.1.2)
  refine ⟨hphase,hlow.1,?_⟩
  intro q hq
  by_cases hqb : q=L.core.generic
  · subst q; exact hv.1.1.1.trans hb.symm
  by_cases hq0 : q=L.core.poolWire 0
  · subst q; exact ((regValue_zero _ _).mp hlow.2 _ (by simp)).trans hhigh.symm
  by_cases hqz : q∈L.dialogNegate.z
  · exact (regValue_eq_iff _ _ _).mp (hv.1.2.trans hz.symm) q hqz
  by_cases hqw : q∈L.dialogNegate.work
  · exact (regValue_eq_iff _ _ _).mp (hv.2.trans hwork.symm) q hqw
  have hqa : q∉L.dialogNegate.a := by rw [he]; simp [hq,hq0]
  have subset (M : ModInPlaceLayout) : M.maskedCore.wires ⊆ M.z++M.work := by
    intro w hh
    simp only [ModInPlaceLayout.maskedCore,ModAddCoreLayout.wires,ModAddCoreLayout.z,
      ModAddCoreLayout.work,ModInPlaceLayout.z,ModInPlaceLayout.work,List.mem_append,List.mem_cons] at hh ⊢
    grind only
  have hmask : q∉L.dialogNegate.maskedCore.wires := by
    intro hh
    have hh' := subset L.dialogNegate hh
    simp only [List.mem_append] at hh'
    exact hh'.elim hqz hqw
  have hqlow : q∉L.dialogNegate.low := by
    intro h; exact hqz (by simp [ModInPlaceLayout.z,ModAddCoreLayout.z,h])
  have hswap : q∉wires (swapRegisters L.core.generic L.point.x L.dialogNegate.low) := by
    intro h
    have hh := swapRegisters_wires L.core.generic L.point.x L.dialogNegate.low (hw.inputX.trans hm.core.low.symm) h
    simp [hqb,hq,hqlow] at hh
  apply run_preserves_outside
  simp only [valueWalkPointDialogNegate,wires_append,controlledModSub_wires _ _ 256 p hm (by omega),
    controlledModAdd_wires _ _ 256 p hm (by omega),Finset.mem_union,List.mem_toFinset,List.mem_cons,
    List.mem_append,not_or]
  have htake : q∉L.dialogNegate.a.take 256 := fun h => hqa ((List.take_sublist _ _).subset h)
  simp only [hqb,hqa,hmask,hswap,htake,not_false_eq_true,and_self]

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ValueWalkPointSquare.lean
/- PR #80 的值走点加路径；与 Skywalk 共享布局、语义及基础算术。 -/
noncomputable section

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

def valueWalkPointDialogSquare (L : ControlledPointLayout) : Program :=
  copyRegister (some L.core.generic) L.point.y (L.dialogPool.take 256) ++
  squareSub L.dialogSquare ++
  copyRegister (some L.core.generic) L.point.y (L.dialogPool.take 256)

private theorem masked_square (K : SquareSubLayout) (c : Wire) (src : List Wire)
    (hw : K.Widths) (hn : (c::src++K.wires).Nodup) (hl : src.length=K.x.length)
    (X Y : Nat) (B : Bool) (hX : X<SquareReduction.p) (s : State) (m : List Bool)
    (hb : s.basis c=B) (hy : regValue src s.basis=Y) (hx : regValue K.out s.basis=X)
    (ha : regValue K.x s.basis=0) (hc : regValue K.work s.basis=0) :
    let C := copyRegister (some c) src K.x
    (run (C++squareSub K++C) m s).phase=s.phase ∧
    regValue K.out (run (C++squareSub K++C) m s).basis=
      (X+SquareReduction.p-(if B then Y*Y else 0)%SquareReduction.p)%SquareReduction.p ∧
    ∀q,q∉K.out → (run (C++squareSub K++C) m s).basis q=s.basis q := by
  dsimp only
  let C := copyRegister (some c) src K.x
  have nd : K.wires.Nodup := (List.nodup_append.mp (List.nodup_cons.mp hn).2).2.1
  have cpnd : (src++K.x).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [SquareSubLayout.wires,List.count_append,List.count_cons] at h ⊢
    omega
  have away (q : Wire) (hq : q∈c::src++K.out++K.work) : q∉K.x := by
    intro hh
    have h := List.nodup_iff_count.mp hn q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hh
    simp only [SquareSubLayout.wires,List.count_append,List.count_cons] at h h1
    omega
  have cno := away c (by simp)
  generalize hs1 : run C (m.take (measurementCount C)) s = s1
  let rest := m.drop (measurementCount C)

  obtain ⟨p1,f1,v1⟩ := copyRegister_correct (some c) src K.x hl cpnd (by simpa using cno)
    s (m.take (measurementCount C))
  change run (copyRegister (some c) src K.x) (m.take (measurementCount C)) s=s1 at hs1
  rw [hs1] at p1 f1 v1
  have a1 : regValue K.x s1.basis=(if B then Y else 0) := by
    simpa only [copyValue,hb,hy,ha,Nat.zero_xor] using v1
  have x1 : regValue K.out s1.basis=X :=
    (regValue_congr _ _ _ (fun q hq => f1 q (away q (by simp [hq])))).trans hx
  have w1 : regValue K.work s1.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => f1 q (away q (by simp [hq])))).trans hc
  obtain ⟨p2,v2⟩ := squareSub_spec K hw nd (if B then Y else 0) X hX s1
    (rest.take (measurementCount (squareSub K))) ⟨⟨a1,x1⟩,w1⟩
  have f2 := squareSub_frame K hw nd (if B then Y else 0) X hX s1
    (rest.take (measurementCount (squareSub K))) a1 x1 w1
  generalize hs2 : run (squareSub K) (rest.take (measurementCount (squareSub K))) s1=s2
  rw [hs2] at p2 v2 f2
  have outAway (q : Wire) (hq : q∈c::src) : q∉K.out := by
    intro hh
    have h := List.nodup_iff_count.mp hn q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hh
    simp only [SquareSubLayout.wires,List.count_append,List.count_cons] at h h1
    omega
  have b2 : s2.basis c=B := (f2 c (outAway c (by simp))).trans ((f1 c cno).trans hb)
  have y2 : regValue src s2.basis=Y :=
    (regValue_congr _ _ _ (fun q hq =>
      (f2 q (outAway q (by simp [hq]))).trans (f1 q (away q (by simp [hq]))))).trans hy
  obtain ⟨p3,f3,v3⟩ := copyRegister_correct (some c) src K.x hl cpnd (by simpa using cno)
    s2 (rest.drop (measurementCount (squareSub K)))
  have av2 : regValue K.x s2.basis=(if B then Y else 0) := v2.1.1
  have a3 : regValue K.x (run C (rest.drop (measurementCount (squareSub K))) s2).basis=0 := by
    simpa only [C,copyValue,b2,y2,av2,Nat.xor_self] using v3
  have result : run (C++squareSub K++C) m s=run C (rest.drop (measurementCount (squareSub K))) s2 := by
    rw [List.append_assoc,run_append]
    change run (squareSub K++C) rest (run C (m.take (measurementCount C)) s)=_
    rw [hs1,run_append,hs2]
  rw [result]
  refine ⟨p3.trans (p2.trans p1),?_,?_⟩
  · have eqv := regValue_congr K.out _ _ (fun q hq => f3 q (away q (by simp [hq])))
    rw [eqv,v2.1.2]
    cases B <;> simp [pow_two]
  · intro q hq
    by_cases hqa : q∈K.x
    · exact (regValue_eq_iff _ _ _).mp (a3.trans ha.symm) q hqa
    · exact (f3 q hqa).trans ((f2 q hq).trans (f1 q hqa))

theorem valueWalkPointDialogSquare_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Nat) (B : Bool) (hX : X<p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=X)
    (hy : regValue L.point.y s.basis=Y) (hc : regValue L.dialogPool s.basis=0) :
    (run (valueWalkPointDialogSquare L) m s).phase=s.phase ∧
    regValue L.point.x (run (valueWalkPointDialogSquare L) m s).basis=
      (X+p-(if B then Y*Y else 0)%p)%p ∧
    ∀q,q∉L.point.x → (run (valueWalkPointDialogSquare L) m s).basis q=s.basis q := by
  have nd : (L.core.generic::L.point.y++L.dialogSquare.wires).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
    have ht := (List.take_sublist 2217 (L.dialogPool.drop 256)).count_le q
    have he := congrArg (List.count q) (List.take_append_drop 256 L.dialogPool)
    rw [SquareSubLayout.wires,L.dialogSquare_work hw]
    change (L.core.generic::L.point.y++((L.dialogPool.take 256)++L.point.x++
      (L.dialogPool.drop 256).take 2217)).count q≤1
    simp only [dialogUsedWires,inPlaceFlags,PointAddLayout.pointWires,
      List.count_append,List.count_cons,List.count_nil] at h ht he ⊢
    omega
  have ha : regValue L.dialogSquare.x s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hc q (List.take_subset 256 _ hq))
  have hz : regValue L.dialogSquare.work s.basis=0 := by
    rw [L.dialogSquare_work hw]
    exact (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hc q
      (List.drop_subset 256 _ (List.take_subset 2217 _ hq)))
  have hp : SquareReduction.p=p := by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c,p]
  have h := masked_square L.dialogSquare L.core.generic L.point.y
    (L.dialogSquare_widths hw) nd (by simp [dialogSquare,SquareSubLayout.fromPool,point,hw.inputY,L.dialogPool_length hw])
    X Y B (by simpa only [hp] using hX) s m hb hy hx ha hz
  simpa only [valueWalkPointDialogSquare,hp] using h

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ValueWalkPointSteps.lean
/- PR #80 的值走点加路径；与 Skywalk 共享布局、语义及基础算术。 -/
noncomputable section

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1
private instance : NeZero p := ⟨by norm_num [p]⟩
private instance : Fact (1<p) := ⟨by norm_num [p]⟩

private theorem sub_val_ValueWalkPointSteps (x y : Fp) : (x-y).val=(x.val+p-y.val)%p := by
  rw [sub_eq_add_neg,ZMod.val_add,ZMod.neg_val',Nat.add_mod_mod]
  rw [←Nat.add_sub_assoc (le_of_lt (ZMod.val_lt y))]

variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (base : BasisState)
include hw hn

theorem valueWalkDialogStep_addX (k : Fp) :
    Triple (PointDialogValues L X Y G base) (valueWalkPointDialogConstantAdd L L.point.x k)
      (PointDialogValues L (X+(if G then k else 0)) Y G base) := by
  intro s m v
  obtain ⟨hp,hx,hf⟩ := valueWalkPointDialogConstantAdd_correct L hw hn L.point.x (Or.inl rfl)
    k X.val G X.isLt s m v.generic v.x v.clean
  refine ⟨hp,v.withX hn ?_ hf⟩
  cases G <;> simpa [ZMod.val_add,Nat.mod_eq_of_lt (ZMod.val_lt X)] using hx

theorem valueWalkDialogStep_addY (k : Fp) :
    Triple (PointDialogValues L X Y G base) (valueWalkPointDialogConstantAdd L L.point.y k)
      (PointDialogValues L X (Y+(if G then k else 0)) G base) := by
  intro s m v
  obtain ⟨hp,hy,hf⟩ := valueWalkPointDialogConstantAdd_correct L hw hn L.point.y (Or.inr rfl)
    k Y.val G Y.isLt s m v.generic v.y v.clean
  refine ⟨hp,v.withY hn ?_ hf⟩
  cases G <;> simpa [ZMod.val_add,Nat.mod_eq_of_lt (ZMod.val_lt Y)] using hy

theorem valueWalkDialogStep_negate :
    Triple (PointDialogValues L X Y G base) (valueWalkPointDialogNegate L)
      (PointDialogValues L (if G then -X else X) Y G base) := by
  intro s m v
  obtain ⟨hp,hx,hf⟩ := valueWalkPointDialogNegate_correct L hw hn X.val G X.isLt s m v.generic v.x v.clean
  refine ⟨hp,v.withX hn ?_ hf⟩
  cases G <;> simpa only [Bool.false_eq_true,if_false,if_true,ZMod.neg_val'] using hx

theorem valueWalkDialogStep_square :
    Triple (PointDialogValues L X Y G base) (valueWalkPointDialogSquare L)
      (PointDialogValues L (X-(if G then Y*Y else 0)) Y G base) := by
  intro s m v
  obtain ⟨hp,hx,hf⟩ := valueWalkPointDialogSquare_correct L hw hn X.val Y.val G X.isLt s m
    v.generic v.x v.y v.clean
  refine ⟨hp,v.withX hn ?_ hf⟩
  cases G <;> simpa [sub_val_ValueWalkPointSteps,ZMod.val_mul,Nat.mod_eq_of_lt (ZMod.val_lt X)] using hx

theorem valueWalkDialogStep_arithmetic (multiply : Bool) (hX : G=true → X≠0) :
    Triple (PointDialogValues L X Y G base)
      (if multiply then dialogMultiply L.dialogPort p else dialogDivide L.dialogPort p)
      (PointDialogValues L X (if G then (if multiply then Y*X else Y/X) else Y) G base) := by
  intro s m v
  have hX0 : G=true → X.val≠0 := by
    intro hg hx; apply hX hg; apply ZMod.val_injective p; simpa using hx
  obtain ⟨hp,hy,hf⟩ := valueWalkPointDialog_arithmetic_correct L hw hn multiply X.val Y.val G
    X.isLt hX0 Y.isLt s m v.generic v.x v.y v.clean
  refine ⟨hp,v.withY hn ?_ hf⟩
  cases G <;> cases multiply <;> simpa only [Bool.false_eq_true,if_false,if_true,ZMod.natCast_zmod_val] using hy

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ValueWalkPointProgram.lean
/- PR #80 的值走点加路径；与 Skywalk 共享布局、语义及基础算术。 -/
noncomputable section

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

/-- 一次除法、专用平方、一次乘法；斜率直接存于当前y。 -/
def valueWalkPointDialogGeneric (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  valueWalkPointDialogConstantAdd L L.point.x (-cx) ++
  valueWalkPointDialogConstantAdd L L.point.y (-cy) ++
  dialogDivide L.dialogPort p ++
  valueWalkPointDialogSquare L ++
  valueWalkPointDialogConstantAdd L L.point.x (3*cx) ++
  dialogMultiply L.dialogPort p ++
  valueWalkPointDialogNegate L ++
  valueWalkPointDialogConstantAdd L L.point.x cx ++
  valueWalkPointDialogConstantAdd L L.point.y (-cy)

/-- 完整有限加数程序，复用共同的输入分类和角落处理。 -/
def valueWalkPointDialogFinite (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  pointInPlaceDoubleEnable L cy ++ pointDialogExceptionEnable L C ++
  equalConstant L.control L.infinitySelect L.dialogPointZero (pointCode 0) ++
  equalConstant L.core.double L.doubleSelect L.dialogPointZero (pointCode C) ++
  equalConstant L.control L.genericSelect L.dialogPointZero (pointCode (-C)) ++
  equalConstant L.core.equalX L.core.equalNegY L.dialogPointZero (pointCode (dialogExceptionPoint C)) ++
  pointDialogGenericFlag L ++ valueWalkPointDialogGeneric L cx cy ++ pointDialogCorners L C ++
  pointDialogGenericFlag L ++
  equalConstant L.control L.infinitySelect L.dialogPointZero (pointCode C) ++
  equalConstant L.core.double L.doubleSelect L.dialogPointZero (pointCode (C+C)) ++
  equalConstant L.control L.genericSelect L.dialogPointZero (pointCode 0) ++
  equalConstant L.core.equalX L.core.equalNegY L.dialogPointZero (pointCode (-C)) ++
  pointDialogExceptionEnable L C ++ pointInPlaceDoubleEnable L cy

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ValueWalkPointCounts.lean
/- PR #80 的值走点加路径；与 Skywalk 共享布局、语义及基础算术。 -/
noncomputable section

namespace ECDSAAdd.Arithmetic
open Secp256k1 ControlledPointLayout

/-- 常数掩码只含CX；每段成本完全来自同一模加核。 -/
theorem valueWalkPointDialogConstantAdd_counts (L : ControlledPointLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y) (k : Fp) :
    toffoliCount (valueWalkPointDialogConstantAdd L r k)=1023 ∧
    measurementCount (valueWalkPointDialogConstantAdd L r k)=1023 := by
  have hn := (List.nodup_cons.mp (L.dialogUnary_nodup hw hnd r hr)).2
  have hl : r.length=256 := by
    rcases hr with rfl | rfl
    · exact hw.inputX
    · exact hw.inputY
  have ha := modAddInPlace_resources (L.dialogUnary r) 256 p (L.dialogUnary_widths hw r hl) hn (by omega)
  simp only [valueWalkPointDialogConstantAdd,toffoliCount_append,measurementCount_append,
    (maskedConstant_counts _ _ _).1,(maskedConstant_counts _ _ _).2,ha.1,ha.2.1]
  norm_num

/-- T←−x、受控交换、T+=x的同门列计数。 -/
theorem valueWalkPointDialogNegate_counts (L : ControlledPointLayout) (hw : L.Widths) (hnd : L.wires.Nodup) :
    toffoliCount (valueWalkPointDialogNegate L)=3838 ∧ measurementCount (valueWalkPointDialogNegate L)=2558 := by
  have hn := L.dialogNegate_nodup hw hnd
  have hl := L.dialogNegate_widths hw
  have ha := controlledModAdd_resources L.core.generic L.dialogNegate 256 p hl hn (by omega)
  have hs := controlledModSub_resources L.core.generic L.dialogNegate 256 p hl hn (by omega)
  have hswap : (L.core.generic::L.point.x++L.dialogNegate.low).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [dialogNegate, ModInPlaceLayout.wires,ModInPlaceLayout.z,
      ModAddCoreLayout.z,List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have he := swapRegisters_resources L.core.generic L.point.x L.dialogNegate.low
    (hw.inputX.trans hl.core.low.symm) hswap
  simp only [valueWalkPointDialogNegate,toffoliCount_append,measurementCount_append,ha.1,ha.2.1,hs.1,hs.2.1,he.1,he.2]
  rw [show L.point.x.length=256 from hw.inputX]
  norm_num


theorem valueWalkPointDialogSquare_counts (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    toffoliCount (valueWalkPointDialogSquare L)=275641 ∧ measurementCount (valueWalkPointDialogSquare L)=275129 := by
  have hc := copyRegister_counts (some L.core.generic) L.point.y (L.dialogPool.take 256)
    (by simp [show L.point.y.length=256 from hw.inputY,L.dialogPool_length hw])
  have hs := squareSub_counts L.dialogSquare (L.dialogSquare_widths hw) (L.dialogSquare_nodup hw hn)
  simp only [valueWalkPointDialogSquare,toffoliCount_append,measurementCount_append,hc.1,hc.2,hs.1,hs.2]
  rw [show L.point.y.length=256 from hw.inputY]
  norm_num

theorem valueWalkPointDialogGeneric_counts (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (cx cy : Fp) :
    toffoliCount (valueWalkPointDialogGeneric L cx cy)=6282702 ∧
    measurementCount (valueWalkPointDialogGeneric L cx cy)=3775170 := by
  have ha k := valueWalkPointDialogConstantAdd_counts L hw hn L.point.x (Or.inl rfl) k
  have hb k := valueWalkPointDialogConstantAdd_counts L hw hn L.point.y (Or.inr rfl) k
  have hd := dialog_counts L.dialogPort p (DialogLayout.fromPool_widths _ _ _ _) (L.dialogPort_nodup hw hn)
  have hs := valueWalkPointDialogSquare_counts L hw hn
  have hn' := valueWalkPointDialogNegate_counts L hw hn
  simp only [valueWalkPointDialogGeneric,toffoliCount_append,measurementCount_append,
    (ha _).1,(ha _).2,(hb _).1,(hb _).2,hd.1,hd.2.1,hd.2.2.1,hd.2.2.2,
    hs.1,hs.2,hn'.1,hn'.2]
  norm_num

theorem valueWalkPointDialogFinite_counts (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (C : Point) (cx cy : Fp) :
    toffoliCount (valueWalkPointDialogFinite L C cx cy)=6286806 ∧
    measurementCount (valueWalkPointDialogFinite L C cx cy)=3779274 := by
  have hg := valueWalkPointDialogGeneric_counts L hw hn cx cy
  have hz c t k := equalConstant_counts c t L.dialogPointZero k
  have hpl : (PointAddLayout.pointWires L.point).length=513 := by
    simp only [PointAddLayout.pointWires,List.length_cons,List.length_append,
      show L.point.x.length=256 from hw.inputX,show L.point.y.length=256 from hw.inputY]
  have hzl : L.dialogPointZero.length=513 := by
    have he := (zeroPorts_maps (PointAddLayout.pointWires L.point) (L.dialogPool.take 513)
      (by simp only [List.length_take,L.dialogPool_length hw]; exact hpl)).1
    simpa only [List.length_map,hpl] using congrArg List.length he
  have he : toffoliCount (pointInPlaceDoubleEnable L cy)=0 ∧
      measurementCount (pointInPlaceDoubleEnable L cy)=0 := by
    unfold pointInPlaceDoubleEnable
    split <;> simp [toffoliCount,measurementCount]
  have hh : toffoliCount (pointDialogExceptionEnable L C)=0 ∧
      measurementCount (pointDialogExceptionEnable L C)=0 := by
    unfold pointDialogExceptionEnable
    split <;> simp [toffoliCount,measurementCount]
  simp only [valueWalkPointDialogFinite,pointDialogCorners,pointInPlaceCorners,toffoliCount_append,
    measurementCount_append,hg.1,hg.2,(hz _ _ _).1,(hz _ _ _).2,hzl,
    (maskedPointConstant_counts _ _ _).1,(maskedPointConstant_counts _ _ _).2,he.1,he.2,hh.1,hh.2]
  norm_num [pointDialogGenericFlag,pointInPlaceGenericFlag,toffoliCount,measurementCount]

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ValueWalkPointGeneric.lean
/- PR #80 的值走点加路径；与 Skywalk 共享布局、语义及基础算术。 -/
noncomputable section

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

theorem valueWalkPointDialogGeneric_true (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y cx cy : Fp) (base : BasisState) (hX : X≠cx) (hd : cx-genericX X Y cx cy≠0) :
    Triple (PointDialogValues L X Y true base) (valueWalkPointDialogGeneric L cx cy)
      (PointDialogValues L (genericX X Y cx cy) (genericY X Y cx cy) true base) := by
  let a := genericSlope X Y cx cy
  let d := cx-genericX X Y cx cy
  have hv := generic_inplace_values X Y cx cy hX
  have h1 := valueWalkDialogStep_addX L hw hn X Y true base (-cx)
  have h2 := valueWalkDialogStep_addY L hw hn (X-cx) Y true base (-cy)
  simp only [if_true,←sub_eq_add_neg] at h1 h2
  have h3 := valueWalkDialogStep_arithmetic L hw hn (X-cx) (Y-cy) true base false (fun _=>sub_ne_zero.mpr hX)
  have ha : (Y-cy)/(X-cx)=a := rfl
  simp only [if_true,Bool.false_eq_true,if_false,ha] at h3
  have h4 := valueWalkDialogStep_square L hw hn (X-cx) a true base
  simp only [if_true] at h4
  have h5 := valueWalkDialogStep_addX L hw hn ((X-cx)-a*a) a true base (3*cx)
  simp only [if_true] at h5
  rw [show (X-cx)-a*a+3*cx=d from hv.2.1] at h5
  have h6 := valueWalkDialogStep_arithmetic L hw hn d a true base true (fun _=>hd)
  simp only [if_true] at h6
  have h7 := valueWalkDialogStep_negate L hw hn d (a*d) true base
  simp only [if_true] at h7
  have h8 := valueWalkDialogStep_addX L hw hn (-d) (a*d) true base cx
  simp only [if_true] at h8
  rw [show -d+cx=genericX X Y cx cy by dsimp [d]; ring] at h8
  have h9 := valueWalkDialogStep_addY L hw hn (genericX X Y cx cy) (a*d) true base (-cy)
  simp only [if_true,←sub_eq_add_neg] at h9
  rw [show a*d-cy=genericY X Y cx cy from hv.2.2] at h9
  have h := (((((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq h7).seq h8).seq h9
  simpa only [valueWalkPointDialogGeneric,List.append_assoc] using h

theorem valueWalkPointDialogGeneric_false (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y cx cy : Fp) (base : BasisState) :
    Triple (PointDialogValues L X Y false base) (valueWalkPointDialogGeneric L cx cy)
      (PointDialogValues L X Y false base) := by
  have h1 := valueWalkDialogStep_addX L hw hn X Y false base (-cx)
  have h2 := valueWalkDialogStep_addY L hw hn X Y false base (-cy)
  have h3 := valueWalkDialogStep_arithmetic L hw hn X Y false base false (by simp)
  have h4 := valueWalkDialogStep_square L hw hn X Y false base
  have h5 := valueWalkDialogStep_addX L hw hn X Y false base (3*cx)
  have h6 := valueWalkDialogStep_arithmetic L hw hn X Y false base true (by simp)
  have h7 := valueWalkDialogStep_negate L hw hn X Y false base
  have h8 := valueWalkDialogStep_addX L hw hn X Y false base cx
  have h9 := valueWalkDialogStep_addY L hw hn X Y false base (-cy)
  simp only [Bool.false_eq_true,if_false,if_true,add_zero,sub_zero] at h1 h2 h3 h4 h5 h6 h7 h8 h9
  have h := (((((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq h7).seq h8).seq h9
  simpa only [valueWalkPointDialogGeneric,List.append_assoc] using h

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ValueWalkPointGenericPoint.lean
/- PR #80 的值走点加路径；与 Skywalk 共享布局、语义及基础算术。 -/
noncomputable section

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

theorem valueWalkDialogBoundary_generic (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) (b : Bool) (f : BasisState) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (hg : f L.core.generic=true → R≠0 ∧ R≠(.some hc : Point) ∧ R≠-(.some hc : Point) ∧
      R≠dialogExceptionPoint (.some hc)) :
    Triple (PointDialogBoundary L R b f) (valueWalkPointDialogGeneric L cx cy)
      (PointDialogBoundary L (if f L.core.generic then R+.some hc else R) b f) := by
  intro s m v
  have hp := (point_holds _ _ _).mp v.point
  have values : PointDialogValues L ((coordinates R).getD (0,0)).1
      ((coordinates R).getD (0,0)).2 (f L.core.generic) s.basis s.basis :=
    ⟨hp.2.1,hp.2.2,v.flags _ (by simp [inPlaceFlags]),v.clean,fun _ _=>rfl⟩
  have hfinite : L.point.finite∉L.point.x++L.point.y := by
    intro hh
    have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) L.point.finite
    have ht := List.count_pos_iff.mpr hh
    simp only [dialogUsedWires,PointAddLayout.pointWires,List.count_append,List.count_cons,
      beq_self_eq_true,if_true] at h ht
    omega
  have outside (q : Wire) (hq : q∉PointAddLayout.pointWires L.point) : q∉L.point.x++L.point.y := by
    simp only [PointAddLayout.pointWires,List.mem_append,List.mem_cons,not_or] at hq ⊢
    exact ⟨hq.1.2,hq.2⟩
  cases hG : f L.core.generic with
  | false =>
    rw [hG] at values
    obtain ⟨phase,hv⟩ := valueWalkPointDialogGeneric_false L hw hn _ _ cx cy s.basis s m values
    refine ⟨phase,v.withPoint hn ?_ (fun q hq=>hv.rest q (outside q hq))⟩
    simp only [Bool.false_eq_true,if_false]
    exact (point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1,hv.x,hv.y⟩
  | true =>
    have he := hg hG
    cases R with
    | zero => exact False.elim (he.1 rfl)
    | @some x y hr =>
      have den := dialog_denominators_ne_zero hr hc he.2.1 he.2.2.1 he.2.2.2
      rw [hG] at values
      obtain ⟨phase,hv⟩ := valueWalkPointDialogGeneric_true L hw hn x y cx cy s.basis den.1 den.2 s m values
      refine ⟨phase,v.withPoint hn ?_ (fun q hq=>hv.rest q (outside q hq))⟩
      simp only [if_true,←genericAdd_correct hr hc den.1,genericAdd]
      exact (point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1,hv.x,hv.y⟩

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ValueWalkPointFiniteSpec.lean
/- PR #80 的值走点加路径；与 Skywalk 共享布局、语义及基础算术。 -/
noncomputable section

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

private theorem equal_simp_ValueWalkPointFiniteSpec [DecidableEq Point] (R C : Point) : pointEqual R C=decide (R=C) := by
  simp only [pointEqual,pointCode_injective.eq_iff]

theorem valueWalkPointDialogFinite_spec (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) :
    Triple (PointDialogBoundary L R b (fun _=>false)) (valueWalkPointDialogFinite L (.some hc) cx cy)
      (PointDialogBoundary L (if b then R+.some hc else R) b (fun _=>false)) := by
  classical
  let C : Point := .some hc
  let O := dialogInfinity b R
  let D := dialogDouble b R C
  let I := dialogInversePoint b R C
  let H := dialogException b R C
  let G := dialogOrdinary b R C
  let E := b && decide (dialogExceptionEnabled C)
  let K := b && decide (cy≠-cy)
  let S := if b then R+C else R
  have hC : C≠0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  have hK : K=(b && decide (C≠-C)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [K,Bool.and_eq_true,decide_eq_true_eq]
    exact and_congr_right (fun _=>doubling_enabled_iff hc)
  have hE : (!pointEqual (dialogExceptionPoint C) 0 && !pointEqual (dialogExceptionPoint C) C &&
      !pointEqual (dialogExceptionPoint C) (-C))=decide (dialogExceptionEnabled C) := by
    simp [equal_simp_ValueWalkPointFiniteSpec,dialogExceptionEnabled,Bool.and_assoc]
  have hO : (b && pointEqual R 0)=O := by simp only [O,dialogInfinity,equal_simp_ValueWalkPointFiniteSpec]
  have hD : (K && pointEqual R C)=D := by rw [hK]; simp only [D,dialogDouble,equal_simp_ValueWalkPointFiniteSpec]
  have hI : (b && pointEqual R (-C))=I := by simp only [I,dialogInversePoint,equal_simp_ValueWalkPointFiniteSpec]
  have hH : (E && pointEqual R (dialogExceptionPoint C))=H := by
    simp [E,H,dialogException,dialogExceptionEnabled,equal_simp_ValueWalkPointFiniteSpec]
  have h0 := dialogFlag_doubleEnable L hn R b false false false false false false false cy
  simp only [Bool.false_xor] at h0
  have h1 := dialogFlag_exceptionEnable L hn R b false false false false false false K C
  rw [hE,Bool.false_xor] at h1
  have h2 := dialogFlag_equalO L hw hn R 0 b false false false false E false K
  rw [hO,Bool.false_xor] at h2
  have h3 := dialogFlag_equalD L hw hn R C b O false false false E false K
  rw [hD,Bool.false_xor] at h3
  have h4 := dialogFlag_equalI L hw hn R (-C) b O D false false E false K
  rw [hI,Bool.false_xor] at h4
  have h5 := dialogFlag_equalH L hw hn R (dialogExceptionPoint C) b O D I false E false K
  rw [hH,Bool.false_xor] at h5
  have h6 := dialogFlag_generic L hw hn R b O D I false E H K
  simp only [Bool.false_xor] at h6
  have read := dialogFlagState_read L hn O D I G E H K
  have h7 := valueWalkDialogBoundary_generic L hw hn R b (dialogFlagState L O D I G E H K) hc
    (fun hg => ((dialogOrdinary_true b R C hC).mp (read.2.2.2.1.symm.trans hg)).2)
  rw [read.2.2.2.1] at h7
  have h8 := dialogBoundary_corners L hw hn R C hC b (dialogFlagState L O D I G E H K)
    read.1 read.2.1 read.2.2.1 read.2.2.2.2.2.1
  have h9 := dialogFlag_generic L hw hn S b O D I G E H K
  have hgclear : (((((G ^^ b) ^^ O) ^^ D) ^^ I) ^^ H)=false := by
    dsimp only [G,dialogOrdinary,O,D,I,H]
    generalize dialogInfinity b R=o,dialogDouble b R C=d,dialogInversePoint b R C=i,
      dialogException b R C=h
    cases b <;> cases o <;> cases d <;> cases i <;> cases h <;> rfl
  rw [hgclear] at h9
  have hf := dialogFlags_output b R C
  have h10 := dialogFlag_equalO L hw hn S C b O D I false E H K
  simp only [equal_simp_ValueWalkPointFiniteSpec] at h10
  rw [hf.1,Bool.xor_self] at h10
  have h11 := dialogFlag_equalD L hw hn S (C+C) b false D I false E H K
  have hdo : (K && pointEqual S (C+C))=D := by
    rw [hK]; simpa only [equal_simp_ValueWalkPointFiniteSpec] using hf.2.1
  rw [hdo,Bool.xor_self] at h11
  have h12 := dialogFlag_equalI L hw hn S 0 b false false I false E H K
  simp only [equal_simp_ValueWalkPointFiniteSpec] at h12
  rw [hf.2.2.1,Bool.xor_self] at h12
  have h13 := dialogFlag_equalH L hw hn S (-C) b false false false false E H K
  have heout : (E && pointEqual S (-C))=H := by
    simpa [E,H,S,dialogExceptionEnabled,equal_simp_ValueWalkPointFiniteSpec] using hf.2.2.2
  rw [heout,Bool.xor_self] at h13
  have h14 := dialogFlag_exceptionEnable L hn S b false false false false E false K C
  rw [hE,show (E ^^ (b && decide (dialogExceptionEnabled C)))=false from Bool.xor_self E] at h14
  have h15 := dialogFlag_doubleEnable L hn S b false false false false false false K cy
  rw [show (K ^^ (b && decide (cy≠-cy)))=false from Bool.xor_self K] at h15
  have h := ((((((((((((((h0.seq h1).seq h2).seq h3).seq h4).seq h5).seq h6).seq h7).seq h8).seq h9).seq h10).seq h11).seq h12).seq h13).seq h14).seq h15
  simpa only [valueWalkPointDialogFinite,List.append_assoc,dialogFlagState_zero] using h

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ValueWalkPointSupport.lean
/- PR #80 的值走点加路径；与 Skywalk 共享布局、语义及基础算术。 -/
noncomputable section

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

theorem valueWalkDialogPort_wires (L : ControlledPointLayout) (hw : L.Widths) :
    L.dialogPort.wires.toFinset=(L.core.generic::L.point.x++L.point.y++L.dialogPool).toFinset := by
  have hp := DialogLayout.fromPool_wires_perm L.core.poolWire L.core.generic L.point.x L.point.y
    hw.inputX hw.inputY
  rw [L.core.pool_prefix hw 2613 (by omega)] at hp
  exact List.toFinset_eq_of_perm _ _ hp

theorem valueWalkPointDialogGeneric_wires (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) :
    wires (valueWalkPointDialogGeneric L cx cy)=(L.core.generic::L.point.x++L.point.y++L.dialogPool).toFinset := by
  have hd := dialog_wires L.dialogPort p (DialogLayout.fromPool_widths _ _ _ _) (L.dialogPort_nodup hw hn)
  rw [valueWalkDialogPort_wires L hw] at hd
  apply Finset.Subset.antisymm
  · intro q
    contrapose!
    intro hnot
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,not_or] at hnot
    rcases hnot with ⟨⟨⟨ng,nx⟩,ny⟩,nb⟩
    have ntake (n : Nat) : q∉L.dialogPool.take n := fun h=>nb (List.take_subset _ _ h)
    have nslice (j n : Nat) : q∉(L.dialogPool.drop j).take n :=
      fun h=>nb (List.drop_subset _ _ (List.take_subset _ _ h))
    have nbit (i : Nat) (hi : i<2613) : q≠L.core.poolWire i := by
      intro he
      have hh : L.core.poolWire i∈L.dialogPool.take i++[L.core.poolWire i] := by simp
      rw [L.dialogBit_prefix hw i hi] at hh
      exact nb (he ▸ List.take_subset _ _ hh)
    have nConst (r : List Wire) (nr : q∉r) : q∉(L.dialogUnary r).wires := by
      simp [dialogUnary,ModInPlaceLayout.wires,ModInPlaceLayout.z,ModInPlaceLayout.work,
        ModAddCoreLayout.z,ModAddCoreLayout.work,nr,ntake,nslice,nbit]
    have nNeg : q∉L.dialogNegate.wires := by
      have ntail : q∉L.dialogPool.tail.take 256 := by simpa only [List.drop_one] using nslice 1 256
      simp [dialogNegate,dialogUnary,ModInPlaceLayout.wires,ModInPlaceLayout.z,ModInPlaceLayout.work,
        ModAddCoreLayout.z,ModAddCoreLayout.work,nx,ntail,nslice,nbit]
    have nMasked (r : List Wire) (v : Nat) (nr : q∉r) : q∉wires (maskedConstant L.core.generic r v) := by
      intro h; have hh := maskedConstant_wires_subset L.core.generic r v h
      simp [ng,nr] at hh
    have nCA (r : List Wire) (nr : q∉r) (hr : r.length=256) (v : Fp) :
        q∉wires (valueWalkPointDialogConstantAdd L r v) := by
      have nm := nConst r nr
      have na : q∉(L.dialogUnary r).a := fun h=>nm (by simp [ModInPlaceLayout.wires,h])
      simp only [valueWalkPointDialogConstantAdd,wires_append,Finset.mem_union,not_or]
      exact ⟨⟨nMasked _ _ na,(modPrograms_not_mem q L.core.generic ng _ (L.dialogUnary_widths hw r hr) nm).1⟩,
        nMasked _ _ na⟩
    have nswap : q∉wires (swapRegisters L.core.generic L.point.x L.dialogNegate.low) := by
      intro h
      have hh := swapRegisters_wires _ _ _ (hw.inputX.trans (L.dialogNegate_widths hw).core.low.symm) h
      have nl : q∉L.dialogNegate.low := fun h=>nNeg
        (by simp [ModInPlaceLayout.wires,ModInPlaceLayout.z,ModAddCoreLayout.z,h])
      change q∈(L.core.generic::L.point.x++L.dialogNegate.low).toFinset at hh
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append,ng,nx,nl,or_false] at hh
    have ncopy : q∉wires (copyRegister (some L.core.generic) L.point.y (L.dialogPool.take 256)) := by
      rw [copyRegister_wires _ _ _ (by simp [show L.point.y.length=256 from hw.inputY,L.dialogPool_length hw])]
      split <;> simp [ng,ny,ntake]
    have nsquare : q∉wires (squareSub L.dialogSquare) := by
      apply square_layout_not_mem L.dialogSquare (L.dialogSquare_widths hw) (L.dialogSquare_nodup hw hn) q
      · exact ntake 256
      · exact nx
      · rw [L.dialogSquare_work hw]; exact nslice 256 2217
    have nneg := modPrograms_not_mem q L.core.generic ng L.dialogNegate (L.dialogNegate_widths hw) nNeg
    have nD : q∉wires (dialogDivide L.dialogPort p) := by rw [hd.1]; simp [ng,nx,ny,nb]
    have nU : q∉wires (dialogMultiply L.dialogPort p) := by rw [hd.2]; simp [ng,nx,ny,nb]
    simp only [valueWalkPointDialogGeneric,valueWalkPointDialogSquare,valueWalkPointDialogNegate,wires_append,Finset.mem_union,
      nCA L.point.x nx hw.inputX _,nCA L.point.y ny hw.inputY _,nD,nU,ncopy,nsquare,
      nneg.2.2.1,nneg.2.2.2,nswap,false_or,not_false_eq_true]
  · intro q hq
    simp only [valueWalkPointDialogGeneric,wires_append,Finset.mem_union,hd.1]
    simp only [hq,true_or,or_true]
end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ValueWalkPointWires.lean
/- PR #80 的值走点加路径；与 Skywalk 共享布局、语义及基础算术。 -/
noncomputable section

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

private theorem equalPoint_wires_ValueWalkPointWires (L : ControlledPointLayout) (hw : L.Widths) (c t : Wire) (C : Point) :
    wires (equalConstant c t L.dialogPointZero (pointCode C))=
      (c::t::PointAddLayout.pointWires L.point++L.dialogPool.take 513).toFinset := by
  rw [equalConstant_wires]
  have hp := zeroPorts_perm (PointAddLayout.pointWires L.point) (L.dialogPool.take 513)
    (by simp [PointAddLayout.pointWires,show L.point.x.length=256 from hw.inputX,
      show L.point.y.length=256 from hw.inputY,L.dialogPool_length hw])
  simp only [dialogPointZero,List.toFinset_cons]
  rw [List.toFinset_eq_of_perm _ _ hp]
  simp only [List.cons_append,List.toFinset_cons]

private theorem genericFlag_wires_ValueWalkPointWires (L : ControlledPointLayout) : wires (pointInPlaceGenericFlag L)=
    [L.control,L.infinitySelect,L.doubleSelect,L.genericSelect,L.core.generic].toFinset := by
  ext q
  simp only [pointInPlaceGenericFlag,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,
    Finset.mem_singleton,Finset.notMem_empty,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
  tauto

/-- 有限常量点加的完整实际支持等式，包括条件false时仍执行的门列。 -/
theorem valueWalkPointDialogFinite_wires (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (C : Point) (cx cy : Fp) :
    wires (valueWalkPointDialogFinite L C cx cy)=L.dialogUsedWires.toFinset := by
  have hG := valueWalkPointDialogGeneric_wires L hw hn cx cy
  have hE := equalPoint_wires_ValueWalkPointWires L hw
  have hB : (L.dialogPool.take 513).toFinset⊆L.dialogUsedWires.toFinset := by
    intro q hq
    have hh := List.take_subset 513 L.dialogPool (List.mem_toFinset.mp hq)
    simp [dialogUsedWires,hh]
  have hM (c : Wire) (hc : c∈L.inPlaceFlags) (P : Point) :
      wires (maskedPointConstant c L.point P)⊆L.dialogUsedWires.toFinset := by
    apply (maskedPointConstant_support _ _ _).trans
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons] at hq
    rcases hq with rfl|hq
    · simp [dialogUsedWires,hc]
    · simp [dialogUsedWires,hq]
  have hO := hM L.infinitySelect (by simp [inPlaceFlags]) C
  have hD := hM L.doubleSelect (by simp [inPlaceFlags]) C
  have hDD := hM L.doubleSelect (by simp [inPlaceFlags]) (C+C)
  have hI := hM L.genericSelect (by simp [inPlaceFlags]) (-C)
  have hHE := hM L.core.equalNegY (by simp [inPlaceFlags]) (dialogExceptionPoint C)
  have hHI := hM L.core.equalNegY (by simp [inPlaceFlags]) (-C)
  have hH : wires (pointInPlaceDoubleEnable L cy)⊆[L.control,L.core.double].toFinset := by
    by_cases hh : cy≠-cy <;> simp [pointInPlaceDoubleEnable,hh,wires,Instr.wires]
  have hEX : wires (pointDialogExceptionEnable L C)⊆[L.control,L.core.equalX].toFinset := by
    unfold pointDialogExceptionEnable
    split <;> simp [wires,Instr.wires]
  have hF := genericFlag_wires_ValueWalkPointWires L
  rw [valueWalkPointDialogFinite]
  simp only [wires_append,hG,hE,pointDialogGenericFlag,wires_append,hF,pointDialogCorners,pointInPlaceCorners,wires_append]
  apply Finset.Subset.antisymm
  · intro q
    have ho := @hO q
    have hd := @hD q
    have hdd := @hDD q
    have hi := @hI q
    have hb := @hB q
    have hh := @hH q
    have hhe := @hHE q
    have hhi := @hHI q
    have hex := @hEX q
    simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,List.mem_toFinset,dialogUsedWires,
      inPlaceFlags,PointAddLayout.pointWires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ho hd hdd hi hb hh hhe hhi hex ⊢
    clear hG hE hB hM hO hD hDD hI hH hHE hHI hEX hF hw
    grind only
  · intro q
    simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,List.mem_toFinset,dialogUsedWires,
      inPlaceFlags,PointAddLayout.pointWires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    clear hG hE hB hM hO hD hDD hI hH hHE hHI hEX hF hw
    grind only

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ValueWalkPointIntegration.lean
/- PR #80 的值走点加路径；与 Skywalk 共享布局、语义及基础算术。 -/
noncomputable section

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

private theorem boundary_frame_values_ValueWalkPointIntegration (L : ControlledPointLayout) (P : Program)
    (hP : wires P⊆L.dialogUsedWires.toFinset) (R R' : Point) (b : Bool) (s : State) (m : List Bool)
    (hi : PointDialogBoundary L R b (fun _ => false) s.basis)
    (ho : PointDialogBoundary L R' b (fun _ => false) (run P m s).basis)
    (q : Wire) (hp : q∉PointAddLayout.pointWires L.point) : (run P m s).basis q=s.basis q := by
  by_cases hc : q=L.control
  · subst q; exact ho.control.trans hi.control.symm
  by_cases hf : q∈L.inPlaceFlags
  · exact (ho.flags q hf).trans (hi.flags q hf).symm
  by_cases hw : q∈L.dialogPool
  · exact (regValue_eq_iff _ _ _).mp (ho.clean.trans hi.clean.symm) q hw
  apply run_preserves_outside
  apply mt (@hP q)
  simp [dialogUsedWires,hp,hc,hf,hw]

theorem valueWalkPointDialogFinite_frame (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (s : State) (m : List Bool)
    (hi : PointDialogBoundary L R b (fun _ => false) s.basis)
    (q : Wire) (hq : q∉PointAddLayout.pointWires L.point) :
    (run (valueWalkPointDialogFinite L (.some hc) cx cy) m s).basis q=s.basis q := by
  have ho := (valueWalkPointDialogFinite_spec L hw hn R hc b s m hi).2
  exact boundary_frame_values_ValueWalkPointIntegration L _ (by rw [valueWalkPointDialogFinite_wires L hw hn]) R _ b s m hi ho q hq

private theorem boundary_work_subset_ValueWalkPointIntegration (L : ControlledPointLayout) :
    L.inPlaceFlags++L.dialogPool ⊆ L.work := by
  intro q hq
  have h1 := List.count_pos_iff.mpr hq
  have ht := (List.take_sublist 2613 L.core.pool).count_le q
  apply List.count_pos_iff.mp
  simp only [dialogPool,List.count_append] at h1
  simp only [work,outWork,temporary,inPlaceFlags,selectors,PointAddLayout.work,PointAddLayout.words,
    PointAddLayout.flags,List.flatten_cons,List.flatten_nil,List.append_nil,List.count_append,List.count_cons,List.count_nil] at h1 ht ⊢
  omega

private theorem work_not_point_ValueWalkPointIntegration (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.work) : q∉PointAddLayout.pointWires L.point := by
  intro hp
  have hh := List.nodup_iff_count.mp hn q
  have h1 := List.count_pos_iff.mpr hq
  have h2 := List.count_pos_iff.mpr hp
  simp only [ControlledPointLayout.wires,work,outWork,temporary,point,extras,selectors,PointAddLayout.wires,
    List.count_append,List.count_cons,List.count_nil] at hh h1 h2
  omega

/-- 公共布局的全部分配工作位恢复为零，包括本实现未使用的旧银行。 -/
theorem valueWalkPointDialogFinite_full_spec (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) :
    (Triple (fun st => (Holds.holds st L.control b ∧ Holds.holds st L.point R) ∧ Holds.holds st L.work 0) (valueWalkPointDialogFinite L (.some hc) cx cy)
      (fun st => (Holds.holds st L.control b ∧ Holds.holds st L.point (if b then R+.some hc else R)) ∧ Holds.holds st L.work 0)) := by
  intro s m hs
  have hz : regValue L.work s.basis=0 := hs.2
  have clean (q : Wire) (hq : q∈L.inPlaceFlags++L.dialogPool) : s.basis q=false :=
    (regValue_zero _ _).mp hz q (boundary_work_subset_ValueWalkPointIntegration L hq)
  have hi : PointDialogBoundary L R b (fun _ => false) s.basis := by
    refine ⟨hs.1.2,hs.1.1,fun q hq => clean q (by simp [hq]),?_⟩
    · exact (regValue_zero _ _).mpr (fun q hq => clean q (by simp [hq]))
  obtain ⟨hp,ho⟩ := valueWalkPointDialogFinite_spec L hw hn R hc b s m hi
  refine ⟨hp,⟨ho.control,ho.point⟩,?_⟩
  apply (regValue_zero _ _).mpr
  intro q hq
  rw [valueWalkPointDialogFinite_frame L hw hn R hc b s m hi q (work_not_point_ValueWalkPointIntegration L hn q hq)]
  exact (regValue_zero _ _).mp hz q hq

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Arithmetic/ValueWalkPointResources.lean
/- PR #80 的值走点加路径；与 Skywalk 共享布局、语义及基础算术。 -/
noncomputable section

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

/-- 实际支持由点513位、外部控制、七标志与共享池2613位组成。 -/
theorem valueWalkPointDialogFinite_qubits (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (cx cy : Fp) : qubitCount (valueWalkPointDialogFinite L C cx cy)=3134 := by
  rw [qubitCount,valueWalkPointDialogFinite_wires L hw hn,List.toFinset_card_of_nodup (L.dialogUsed_nodup hn)]
  simp [dialogUsedWires,PointAddLayout.pointWires,inPlaceFlags,
    show L.point.x.length=256 from hw.inputX,show L.point.y.length=256 from hw.inputY,L.dialogPool_length hw]

end ECDSAAdd.Arithmetic
end

-- source: ECDSAAdd/Challenge/Contract.lean
noncomputable section

/-! Protected challenge contract. Signed basis states and fixed measurement
records only; this is not a quantum-channel or hardware claim. -/
namespace ECDSAAdd.Challenge
open Secp256k1

/-- Public classical construction parameter; no secret-input restriction on C. -/
abbrev Entry := Point → Program

def control : Wire := 0

def point : PointReg :=
  ⟨1, (List.range 256).map (· + 2), (List.range 256).map (· + 258)⟩

/-- Control plus the canonical 513-bit point representation. -/
def ioWires : Finset Wire := Finset.range 514

def clean (st : BasisState) : Prop := ∀ w, 514 ≤ w → st w = false

def encodes (b : Bool) (R : Point) (st : BasisState) : Prop :=
  st control = b ∧ Holds.holds st point R ∧ clean st

/-- Includes idle I/O wires. This is static distinct wires, not peak-live. -/
def qubits (p : Program) : Nat := (ioWires ∪ wires p).card

def correctionValid : Correction → Prop
  | .Z _ => True
  | .CZ a b => a ≠ b

def instructionValid : Instr → Prop
  | .X _ => True
  | .CX c t => c ≠ t
  | .CCX a b t => a ≠ b ∧ a ≠ t ∧ b ≠ t
  | .measureX _ c₀ c₁ =>
      (∀ c ∈ c₀, correctionValid c) ∧ (∀ c ∈ c₁, correctionValid c)

/-- Static structural slots count the measurement itself and BOTH correction lists,
including the branch not taken on a particular record. -/
def instructionSlots : Instr → Nat
  | .measureX _ c₀ c₁ => 1 + c₀.length + c₁.length
  | _ => 1

def gateSlots (p : Program) : Nat := (p.map instructionSlots).sum

/-- Uniform upper bounds over all classical addends, including infinity. -/
structure Bounds where
  toffoli : Nat
  measurements : Nat
  qubits : Nat
  gateSlots : Nat

/-- Every non-I/O bit is zero before and after, and Triple restores phase.
The entrant cannot replace the encoding, layout, semantic model or counters. -/
structure Certificate (entry : Entry) (bounds : Bounds) : Prop where
  correct : ∀ C b R, Triple (encodes b R) (entry C)
    (encodes b (if b then R + C else R))
  physical : ∀ C i, i ∈ entry C → instructionValid i
  toffoli_le : ∀ C, toffoliCount (entry C) ≤ bounds.toffoli
  measurements_le : ∀ C, measurementCount (entry C) ≤ bounds.measurements
  qubits_le : ∀ C, qubits (entry C) ≤ bounds.qubits
  gateSlots_le : ∀ C, gateSlots (entry C) ≤ bounds.gateSlots

/-- Organizer thresholds remain explicit; choosing numeric values is policy. -/
def Within (bounds limits : Bounds) : Prop :=
  bounds.toffoli ≤ limits.toffoli ∧ bounds.measurements ≤ limits.measurements ∧
  bounds.qubits ≤ limits.qubits ∧ bounds.gateSlots ≤ limits.gateSlots

theorem qubits_ge_io (p : Program) : 514 ≤ qubits p := by
  have h := Finset.card_le_card (Finset.subset_union_left : ioWires ⊆ ioWires ∪ wires p)
  simpa [ioWires, qubits] using h

@[simp] theorem qubits_empty : qubits [] = 514 := by
  simp [qubits, ioWires, wires]

@[simp] theorem gateSlots_append (p q : Program) :
    gateSlots (p ++ q) = gateSlots p + gateSlots q := by
  simp [gateSlots]

theorem Certificate.phase_restored {entry bounds} (h : Certificate entry bounds)
    (C : Point) (b : Bool) (R : Point) (s : State) (m : List Bool)
    (hs : encodes b R s.basis) : (run (entry C) m s).phase = s.phase :=
  (h.correct C b R s m hs).1

theorem Certificate.all_work_clean {entry bounds} (h : Certificate entry bounds)
    (C : Point) (b : Bool) (R : Point) (s : State) (m : List Bool)
    (hs : encodes b R s.basis) : clean (run (entry C) m s).basis :=
  (h.correct C b R s m hs).2.2.2

end ECDSAAdd.Challenge
end

-- source: ECDSAAdd/Baselines/Layout.lean
noncomputable section

namespace ECDSAAdd.Baselines
open Arithmetic

/-- A fixed instance of the legacy allocation. Only actual program support is
charged by the challenge; unused legacy fields remain zero by framing. -/
def layout : ControlledPointLayout where
  control := Challenge.control
  genericSelect := 9814
  doubleSelect := 9815
  infinitySelect := 9816
  core := {
    input := Challenge.point
    output := ⟨514, List.range' 515 256, List.range' 771 256⟩
    dx := List.range' 1027 257
    dy := List.range' 1284 257
    slope := List.range' 1541 257
    square := List.range' 1798 257
    offset := List.range' 2055 257
    candidateX := List.range' 2312 257
    delta := List.range' 2569 257
    product := List.range' 2826 257
    candidateY := List.range' 3083 257
    constant := List.range' 3340 257
    divisor := List.range' 3597 256
    inverse := List.range' 3853 256
    inputXHigh := 4109
    inputYHigh := 4110
    equalX := 4111
    equalNegY := 4112
    generic := 4113
    double := 4114
    pool := List.range' 4115 5699
  }

theorem layout_control : layout.control = Challenge.control := rfl
theorem layout_point : layout.point = Challenge.point := rfl

theorem layout_widths : layout.Widths := by
  constructor <;>
    simp [layout, Challenge.point, PointAddLayout.words]

theorem core_wires : layout.core.wires = List.range' 1 9813 := by
  have mr (a n : Nat) : (List.range n).map (· + a) = List.range' a n := by
    simpa only [Nat.add_comm] using (List.range'_eq_map_range (s := a) (n := n)).symm
  have consr (s n : Nat) : s :: List.range' (s+1) n = List.range' s (n+1) := rfl
  simp only [PointAddLayout.wires, PointAddLayout.work,
    PointAddLayout.words, PointAddLayout.flags, PointAddLayout.pointWires, layout,
    Challenge.point, List.flatten_cons, List.flatten_nil, List.append_nil, mr]
  rw [show [4109,4110] = List.range' 4109 2 from rfl,
    show [4111,4112,4113,4114] = List.range' 4111 4 from rfl]
  simp only [consr, ← List.append_assoc]
  rw [show List.range' 1 257 ++ List.range' 258 256 = List.range' 1 513
    from List.range'_append_1]
  rw [show List.range' 1 513 ++ List.range' 514 257 = List.range' 1 770
    from List.range'_append_1]
  rw [show List.range' 1 770 ++ List.range' 771 256 = List.range' 1 1026
    from List.range'_append_1]
  rw [show List.range' 1 1026 ++ List.range' 1027 257 = List.range' 1 1283
    from List.range'_append_1]
  rw [show List.range' 1 1283 ++ List.range' 1284 257 = List.range' 1 1540
    from List.range'_append_1]
  rw [show List.range' 1 1540 ++ List.range' 1541 257 = List.range' 1 1797
    from List.range'_append_1]
  rw [show List.range' 1 1797 ++ List.range' 1798 257 = List.range' 1 2054
    from List.range'_append_1]
  rw [show List.range' 1 2054 ++ List.range' 2055 257 = List.range' 1 2311
    from List.range'_append_1]
  rw [show List.range' 1 2311 ++ List.range' 2312 257 = List.range' 1 2568
    from List.range'_append_1]
  rw [show List.range' 1 2568 ++ List.range' 2569 257 = List.range' 1 2825
    from List.range'_append_1]
  rw [show List.range' 1 2825 ++ List.range' 2826 257 = List.range' 1 3082
    from List.range'_append_1]
  rw [show List.range' 1 3082 ++ List.range' 3083 257 = List.range' 1 3339
    from List.range'_append_1]
  rw [show List.range' 1 3339 ++ List.range' 3340 257 = List.range' 1 3596
    from List.range'_append_1]
  rw [show List.range' 1 3596 ++ List.range' 3597 256 = List.range' 1 3852
    from List.range'_append_1]
  rw [show List.range' 1 3852 ++ List.range' 3853 256 = List.range' 1 4108
    from List.range'_append_1]
  rw [show List.range' 1 4108 ++ List.range' 4109 2 = List.range' 1 4110
    from List.range'_append_1]
  rw [show List.range' 1 4110 ++ List.range' 4111 4 = List.range' 1 4114
    from List.range'_append_1]
  rw [show List.range' 1 4114 ++ List.range' 4115 5699 = List.range' 1 9813
    from List.range'_append_1]

theorem layout_nodup : layout.wires.Nodup := by
  change (layout.core.wires ++ [0,9814,9815,9816]).Nodup
  rw [core_wires, List.nodup_append']
  refine ⟨List.nodup_range', by decide, ?_⟩
  intro a ha hb
  simp only [List.mem_range'_1] at ha
  simp only [List.mem_cons, List.not_mem_nil] at hb
  rcases hb with rfl | rfl | rfl | rfl | h
  all_goals omega

theorem work_lower (w : Wire) (hw : w ∈ layout.work) : 514 ≤ w := by
  simp only [ControlledPointLayout.work, ControlledPointLayout.temporary,
    ControlledPointLayout.outWork, ControlledPointLayout.selectors,
    PointAddLayout.work, PointAddLayout.words, PointAddLayout.flags,
    PointAddLayout.pointWires, layout, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.mem_append, List.mem_cons, List.mem_range'_1,
    List.not_mem_nil, or_false, or_assoc] at hw
  rcases hw with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals first | (subst w; decide) | exact Nat.le_trans (by decide) h.1

end ECDSAAdd.Baselines
end

-- source: ECDSAAdd/Submissions/Skywalk.lean
noncomputable section

namespace ECDSAAdd.Submissions.Skywalk
open Arithmetic Secp256k1

/-- PR #81：压缩 Skywalk 完整受控原地点加，与现有公开入口相同。 -/
def program (L : ControlledPointLayout) (C : Point) : Program := controlledPointAdd L C

/-- 有限经典加数的静态 Toffoli 与测量指令计数。 -/
def gateCount : Nat := 2217386
def measurementCount : Nat := 1557928
/-- 真实支持集基数的已证上界；不声称等于该值或为峰值存活线路数。 -/
def qubitBound : Nat := 1899

/-- 所有合法输入点、控制位和测量记录；相位恢复，全部工作位清零。 -/
theorem correctness (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (b : Bool) (R C : Point) :
    (Triple (fun st => (Holds.holds st L.control b ∧ Holds.holds st L.point R) ∧ Holds.holds st L.work 0) (program L C)
      (fun st => (Holds.holds st L.control b ∧ Holds.holds st L.point (if b then R+C else R)) ∧ Holds.holds st L.work 0)) :=
  controlledPointAdd_spec L hw hn b R C

theorem gate_count (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    ECDSAAdd.toffoliCount (program L (.some hc))=gateCount :=
  (controlledPointAdd_finite_resources L hw hn cx cy hc).1

theorem measurement_count (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    ECDSAAdd.measurementCount (program L (.some hc))=measurementCount :=
  (controlledPointAdd_finite_resources L hw hn cx cy hc).2.1

theorem qubit_count (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    ECDSAAdd.qubitCount (program L (.some hc))≤qubitBound :=
  (controlledPointAdd_finite_resources L hw hn cx cy hc).2.2

/-- 无穷远常量在构造期发出空程序。 -/
theorem zero_resources (L : ControlledPointLayout) :
    ECDSAAdd.toffoliCount (program L 0)=0 ∧
    ECDSAAdd.measurementCount (program L 0)=0 ∧
    ECDSAAdd.qubitCount (program L 0)=0 :=
  controlledPointAdd_zero_resources L

end ECDSAAdd.Submissions.Skywalk
end

-- source: ECDSAAdd/Submissions/ValueWalk.lean
noncomputable section

namespace ECDSAAdd.Submissions.ValueWalk
open Arithmetic Secp256k1

/-- PR #80：固定512轮、已证位宽收窄的完整受控原地点加。 -/
def program (L : ControlledPointLayout) (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      valueWalkPointDialogFinite L C cx cy

/-- 有限经典加数的静态成本；gate 指 Toffoli，线路数为精确支持基数。 -/
def gateCount : Nat := 6286806
def measurementCount : Nat := 3779274
def qubitCount : Nat := 3134

/-- 所有合法输入点、控制位和测量记录；相位恢复，全部工作位清零。 -/
theorem correctness (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (b : Bool) (R C : Point) :
    (Triple (fun st => (Holds.holds st L.control b ∧ Holds.holds st L.point R) ∧ Holds.holds st L.work 0) (program L C)
      (fun st => (Holds.holds st L.control b ∧ Holds.holds st L.point (if b then R+C else R)) ∧ Holds.holds st L.work 0)) := by
  cases C with
  | zero =>
    intro s m hs
    change s.phase=s.phase ∧ _
    refine ⟨rfl,?_⟩
    change ((Holds.holds s.basis L.control b ∧ Holds.holds s.basis L.point (if b then R+0 else R)) ∧ _)
    simpa only [add_zero,ite_self] using hs
  | some hp => exact valueWalkPointDialogFinite_full_spec L hw hn R hp b

theorem gate_count (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    ECDSAAdd.toffoliCount (program L (.some hc))=gateCount :=
  (valueWalkPointDialogFinite_counts L hw hn (.some hc) cx cy).1

theorem measurement_count (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    ECDSAAdd.measurementCount (program L (.some hc))=measurementCount :=
  (valueWalkPointDialogFinite_counts L hw hn (.some hc) cx cy).2

theorem qubit_count (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    ECDSAAdd.qubitCount (program L (.some hc))=qubitCount :=
  valueWalkPointDialogFinite_qubits L hw hn (.some hc) cx cy

/-- 无穷远常量在构造期发出空程序。 -/
theorem zero_resources (L : ControlledPointLayout) :
    ECDSAAdd.toffoliCount (program L 0)=0 ∧
    ECDSAAdd.measurementCount (program L 0)=0 ∧
    ECDSAAdd.qubitCount (program L 0)=0 := by
  simp [program,ECDSAAdd.toffoliCount,ECDSAAdd.measurementCount,ECDSAAdd.qubitCount,wires]

end ECDSAAdd.Submissions.ValueWalk
end

-- source: ECDSAAdd/Baselines/Frame.lean
noncomputable section

namespace ECDSAAdd.Baselines
open Arithmetic Secp256k1

theorem point_wire_lt (w : Wire) (h : w ∈ PointAddLayout.pointWires Challenge.point) :
    w < 514 := by
  simp only [PointAddLayout.pointWires, Challenge.point, List.mem_append,
    List.mem_cons, List.mem_map, List.mem_range] at h
  rcases h with (rfl | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩
  · decide
  · exact Nat.lt_of_lt_of_le (Nat.add_lt_add_right hi 2) (by decide)
  · exact Nat.add_lt_add_right hi 258

theorem dialog_support_partition (L : ControlledPointLayout) (w : Wire)
    (hw : w ∈ L.dialogUsedWires) :
    w = L.control ∨ w ∈ PointAddLayout.pointWires L.point ∨ w ∈ L.work := by
  simp only [ControlledPointLayout.dialogUsedWires, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with ((hp | hc) | hf) | hb
  · exact Or.inr (Or.inl hp)
  · exact Or.inl hc
  · right; right
    simp only [ControlledPointLayout.inPlaceFlags, List.mem_cons, List.not_mem_nil] at hf
    simp only [ControlledPointLayout.work, ControlledPointLayout.outWork,
      ControlledPointLayout.selectors, PointAddLayout.work, PointAddLayout.flags,
      List.mem_append, List.mem_cons, List.not_mem_nil]
    tauto
  · right; right
    have hb' : w ∈ L.core.pool := List.mem_of_mem_take hb
    simp only [ControlledPointLayout.work, ControlledPointLayout.outWork,
      PointAddLayout.work, List.mem_append]
    tauto

/-- Upgrade the old named-work Triple using actual support, never an entrant
claim that unlisted wires are irrelevant. -/
theorem fixed_correct (p : Program) (b : Bool) (R S : Point)
    (spec : (Triple (fun st => (Holds.holds st layout.control b ∧ Holds.holds st layout.point R) ∧ Holds.holds st layout.work 0) p
      (fun st => (Holds.holds st layout.control b ∧ Holds.holds st layout.point S) ∧ Holds.holds st layout.work 0)))
    (support : wires p ⊆ layout.dialogUsedWires.toFinset) :
    Triple (Challenge.encodes b R) p (Challenge.encodes b S) := by
  intro st tape hs
  have hz : regValue layout.work st.basis = 0 :=
    (regValue_zero _ _).mpr (fun w hw => hs.2.2 w (work_lower w hw))
  obtain ⟨phase, ⟨hctrl, hpoint⟩, hwork⟩ := spec st tape ⟨⟨hs.1,hs.2.1⟩,hz⟩
  refine ⟨phase, hctrl, hpoint, ?_⟩
  intro w hw
  by_cases hm : w ∈ layout.work
  · exact (regValue_zero _ _).mp hwork w hm
  · have outside : w ∉ wires p := by
      intro h
      have hparts := dialog_support_partition layout w (List.mem_toFinset.mp (support h))
      rcases hparts with hc | hp | hwork
      · have hc' : w = 0 := hc
        subst w
        exact (by decide : ¬ (514 ≤ (0:Nat))) hw
      · exact (Nat.not_lt_of_ge hw) (point_wire_lt w hp)
      · exact hm hwork
    exact (run_preserves_outside p tape st w outside).trans (hs.2.2 w hw)

end ECDSAAdd.Baselines
end

-- source: ECDSAAdd/Baselines/Correctness.lean
noncomputable section

namespace ECDSAAdd.Baselines
open Arithmetic Secp256k1
attribute [local irreducible] valueWalkPointDialogFinite wires

def skywalk : Challenge.Entry := Submissions.Skywalk.program layout
def valueWalk : Challenge.Entry := Submissions.ValueWalk.program layout

theorem skywalk_correct (C : Point) (b : Bool) (R : Point) :
    Triple (Challenge.encodes b R) (skywalk C)
      (Challenge.encodes b (if b then R+C else R)) := by
  apply fixed_correct _ b R _ (Submissions.Skywalk.correctness layout layout_widths layout_nodup b R C)
  cases C with
  | zero => simp [Submissions.Skywalk.program, controlledPointAdd, wires]
  | some hc => exact CompressedPointDialog.finite_wires layout layout_widths layout_nodup _ _ _

theorem valueWalk_correct (C : Point) (b : Bool) (R : Point) :
    Triple (Challenge.encodes b R) (valueWalk C)
      (Challenge.encodes b (if b then R+C else R)) := by
  apply fixed_correct _ b R _ (Submissions.ValueWalk.correctness layout layout_widths layout_nodup b R C)
  cases C with
  | zero => simp [Submissions.ValueWalk.program, wires]
  | some hc =>
    exact (valueWalkPointDialogFinite_wires layout layout_widths layout_nodup _ _ _).le

theorem skywalk_toffoli (C : Point) : toffoliCount (skywalk C) ≤ 2217386 := by
  cases C with
  | zero => simp [skywalk, Submissions.Skywalk.program, controlledPointAdd, toffoliCount]
  | some hc => exact (Submissions.Skywalk.gate_count layout layout_widths layout_nodup _ _ hc).le

theorem skywalk_measurements (C : Point) : measurementCount (skywalk C) ≤ 1557928 := by
  cases C with
  | zero => simp [skywalk, Submissions.Skywalk.program, controlledPointAdd, measurementCount]
  | some hc => exact (Submissions.Skywalk.measurement_count layout layout_widths layout_nodup _ _ hc).le

theorem valueWalk_toffoli (C : Point) : toffoliCount (valueWalk C) ≤ 6286806 := by
  cases C with
  | zero => simp [valueWalk, Submissions.ValueWalk.program, toffoliCount]
  | some hc => exact (Submissions.ValueWalk.gate_count layout layout_widths layout_nodup _ _ hc).le

theorem valueWalk_measurements (C : Point) : measurementCount (valueWalk C) ≤ 3779274 := by
  cases C with
  | zero => simp [valueWalk, Submissions.ValueWalk.program, measurementCount]
  | some hc => exact (Submissions.ValueWalk.measurement_count layout layout_widths layout_nodup _ _ hc).le

end ECDSAAdd.Baselines
end

-- source: ECDSAAdd/Baselines/Normalize.lean
noncomputable section

namespace ECDSAAdd.Baselines
open Challenge

/-- Remove repeated controls without changing signed-basis execution. -/
def normalizeCorrection : Correction → Correction
  | .Z t => .Z t
  | .CZ a b => if a = b then .Z a else .CZ a b

def normalizeInstr : Instr → Instr
  | .CCX a b t => if a = b then .CX a t else .CCX a b t
  | .measureX t c₀ c₁ => .measureX t (c₀.map normalizeCorrection) (c₁.map normalizeCorrection)
  | i => i

def normalizeProgram (p : Program) : Program := p.map normalizeInstr

theorem normalizeCorrection_valid (c : Correction) :
    correctionValid (normalizeCorrection c) := by
  cases c with
  | Z t => trivial
  | CZ a b => by_cases h : a = b <;> simp [normalizeCorrection, h, correctionValid]

theorem normalizeInstr_valid (i : Instr)
    (h : RecordedQuantum.PhysicalInstr (.gate i)) :
    instructionValid (normalizeInstr i) := by
  cases i with
  | X t => trivial
  | CX c t => exact h
  | CCX a b t =>
    change a ≠ t ∧ b ≠ t at h
    by_cases hab : a = b
    · simpa [normalizeInstr, hab, instructionValid] using h.1
    · simpa [normalizeInstr, hab, instructionValid] using And.intro hab h
  | measureX t c₀ c₁ =>
    simp only [normalizeInstr, instructionValid, List.mem_map]
    constructor <;> intro c hc <;> obtain ⟨d, hd, rfl⟩ := hc
    all_goals exact normalizeCorrection_valid d

theorem normalize_correct (cs : List Correction) (s : State) :
    correct (cs.map normalizeCorrection) s = correct cs s := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih =>
    cases c with
    | Z t => simpa only [List.map_cons, normalizeCorrection, correct] using ih _
    | CZ a b =>
      by_cases hab : a = b
      · subst b
        simpa [normalizeCorrection, correct] using ih ⟨s.phase ^^ s.basis a, s.basis⟩
      · simpa [normalizeCorrection, hab, correct] using ih ⟨s.phase ^^ (s.basis a && s.basis b), s.basis⟩

theorem normalize_run (p : Program) (m : List Bool) (s : State) :
    run (normalizeProgram p) m s = run p m s := by
  induction p generalizing m s with
  | nil => rfl
  | cons i p ih =>
    cases i with
    | X t => simpa only [normalizeProgram, List.map_cons, normalizeInstr, run] using ih m _
    | CX c t => simpa only [normalizeProgram, List.map_cons, normalizeInstr, run] using ih m _
    | CCX a b t =>
      by_cases hab : a = b
      · subst b
        simpa [normalizeProgram, normalizeInstr, run] using
          ih m ⟨s.phase, writeBit s.basis t (s.basis t ^^ s.basis a)⟩
      · simpa [normalizeProgram, normalizeInstr, hab, run] using
          ih m ⟨s.phase, writeBit s.basis t (s.basis t ^^ (s.basis a && s.basis b))⟩
    | measureX t c₀ c₁ =>
      simp only [normalizeProgram, List.map_cons, normalizeInstr, run]
      change run (normalizeProgram p) m.tail _ = _
      rw [ih]
      congr 1
      simp only [measureAndCorrect]
      split <;> exact normalize_correct _ _

theorem normalize_slots (p : Program) : gateSlots (normalizeProgram p) = gateSlots p := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    cases i with
    | CCX a b t =>
      by_cases hab : a = b <;>
        simp_all [normalizeProgram, normalizeInstr, gateSlots, instructionSlots]
    | X t => simpa [normalizeProgram, normalizeInstr, gateSlots, instructionSlots] using ih
    | CX c t => simpa [normalizeProgram, normalizeInstr, gateSlots, instructionSlots] using ih
    | measureX t c₀ c₁ => simpa [normalizeProgram, normalizeInstr, gateSlots, instructionSlots] using ih

theorem normalize_measurements (p : Program) :
    measurementCount (normalizeProgram p) = measurementCount p := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    cases i <;> simp_all [normalizeProgram, normalizeInstr, measurementCount]
    split <;> simp_all [measurementCount]

/-- Number of Toffoli slots removed by normalization. -/
def repeatedControls : Program → Nat
  | [] => 0
  | .CCX a b _ :: p => (if a = b then 1 else 0) + repeatedControls p
  | _ :: p => repeatedControls p

theorem normalize_toffoli_exact (p : Program) :
    toffoliCount (normalizeProgram p) + repeatedControls p = toffoliCount p := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    cases i with
    | CCX a b t =>
      by_cases h : a = b <;>
        simp only [normalizeProgram, List.map_cons, normalizeInstr, h, ↓reduceIte,
          toffoliCount, repeatedControls] at ih ⊢ <;> omega
    | X t => simpa [normalizeProgram, normalizeInstr, toffoliCount, repeatedControls] using ih
    | CX a t => simpa [normalizeProgram, normalizeInstr, toffoliCount, repeatedControls] using ih
    | measureX t cs ds => simpa [normalizeProgram, normalizeInstr, toffoliCount, repeatedControls] using ih

theorem normalize_toffoli (p : Program) :
    toffoliCount (normalizeProgram p) ≤ toffoliCount p := by
  induction p with
  | nil => exact Nat.le_refl _
  | cons i p ih =>
    cases i <;> simp_all [normalizeProgram, normalizeInstr, toffoliCount]
    split <;> simp_all [toffoliCount]
    exact Nat.le_trans ih (Nat.le_add_left _ _)

theorem normalize_correctionWires (cs : List Correction) :
    correctionWires (cs.map normalizeCorrection) = correctionWires cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases c with
    | Z t => simp [normalizeCorrection, correctionWires, ih]
    | CZ a b => by_cases hab : a = b <;> simp [normalizeCorrection, hab, correctionWires, ih]

theorem normalize_wires (p : Program) : wires (normalizeProgram p) = wires p := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    cases i with
    | CCX a b t => by_cases hab : a = b <;> simp_all [normalizeProgram, normalizeInstr, wires, Instr.wires]
    | measureX t c₀ c₁ =>
      simp only [normalizeProgram, List.map_cons, normalizeInstr, wires, Instr.wires,
        normalize_correctionWires]
      exact congrArg (_ ∪ ·) ih
    | X t => simpa only [normalizeProgram, List.map_cons, normalizeInstr, wires] using congrArg (_ ∪ ·) ih
    | CX c t => simpa only [normalizeProgram, List.map_cons, normalizeInstr, wires] using congrArg (_ ∪ ·) ih

theorem normalize_physical (p : Program)
    (h : ∀ i ∈ p, RecordedQuantum.PhysicalInstr (.gate i)) :
    ∀ i ∈ normalizeProgram p, instructionValid i := by
  intro i hi
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
  exact normalizeInstr_valid j (h j hj)

theorem normalize_qubits (p : Program) : qubits (normalizeProgram p) = qubits p := by
  simp only [qubits, normalize_wires]

theorem normalize_triple (p : Program) (P Q : BasisState → Prop) :
    Triple P (normalizeProgram p) Q ↔ Triple P p Q := by
  simp only [Triple, normalize_run]

end ECDSAAdd.Baselines
end

-- source: ECDSAAdd/Baselines/Qubits.lean
noncomputable section

namespace ECDSAAdd.Baselines
open Arithmetic Secp256k1
attribute [local irreducible] valueWalkPointDialogFinite pointCompressedDialogFinite wires

theorem point_wires : PointAddLayout.pointWires layout.point = List.range' 1 513 := by
  have mr (a n : Nat) : (List.range n).map (· + a) = List.range' a n := by
    simpa only [Nat.add_comm] using (List.range'_eq_map_range (s := a) (n := n)).symm
  simp only [layout_point, PointAddLayout.pointWires, Challenge.point, mr]
  change List.range' 1 257 ++ List.range' 258 256 = List.range' 1 513
  exact List.range'_append_1

theorem io_partition (w : Wire) (h : w ∈ Challenge.ioWires) :
    w ∈ PointAddLayout.pointWires layout.point ∨ w = layout.control := by
  rw [point_wires]
  have hw : w < 514 := Finset.mem_range.mp h
  by_cases hz : w = 0
  · exact Or.inr hz
  · left
    apply List.mem_range'_1.mpr
    exact ⟨Nat.pos_of_ne_zero hz, hw⟩

theorem io_subset_sites :
    Challenge.ioWires ⊆ (CompressedPointDialog.sites layout).toFinset := by
  intro w hw
  have h := io_partition w hw
  simp only [CompressedPointDialog.sites, CompressedPointSquare.residents,
    List.mem_toFinset, List.mem_append, List.mem_cons, List.not_mem_nil]
  rcases h with hp | hc
  · exact Or.inl (Or.inl (Or.inl hp))
  · exact Or.inl (Or.inl (Or.inr (Or.inl hc)))

theorem io_subset_dialog :
    Challenge.ioWires ⊆ layout.dialogUsedWires.toFinset := by
  intro w hw
  have h := io_partition w hw
  simp only [ControlledPointLayout.dialogUsedWires,
    List.mem_toFinset, List.mem_append, List.mem_cons, List.not_mem_nil]
  rcases h with hp | hc
  · exact Or.inl (Or.inl (Or.inl hp))
  · exact Or.inl (Or.inl (Or.inr (Or.inl hc)))

theorem skywalk_qubits (C : Point) : Challenge.qubits (skywalk C) ≤ 1899 := by
  cases C with
  | zero =>
    change Challenge.qubits [] ≤ 1899
    rw [Challenge.qubits_empty]
    decide
  | @some cx cy hc =>
    have support := CompressedPointDialog.finite_support layout layout_widths layout_nodup (.some hc) cx cy
    have card := Finset.card_le_card (Finset.union_subset io_subset_sites support)
    have length : (CompressedPointDialog.sites layout).length = 1899 := by
      rw [CompressedPointDialog.sites, List.length_append,
        CompressedPointSquare.residents_length layout layout_widths,
        CompressedPointSquare.sharedPool_length]
    exact card.trans ((List.toFinset_card_le _).trans_eq length)

theorem valueWalk_qubits (C : Point) : Challenge.qubits (valueWalk C) ≤ 3134 := by
  cases C with
  | zero =>
    change Challenge.qubits [] ≤ 3134
    rw [Challenge.qubits_empty]
    decide
  | @some cx cy hc =>
    change (Challenge.ioWires ∪ wires (valueWalkPointDialogFinite layout (.some hc) _ _)).card ≤ 3134
    rw [valueWalkPointDialogFinite_wires layout layout_widths layout_nodup,
      Finset.union_eq_right.mpr io_subset_dialog,
      List.toFinset_card_of_nodup (layout.dialogUsed_nodup layout_nodup)]
    simp only [ControlledPointLayout.dialogUsedWires, List.length_append,
      PointAddLayout.pointWires, ControlledPointLayout.inPlaceFlags, List.length_cons,
      List.length_nil, show layout.point.x.length = 256 from layout_widths.inputX,
      show layout.point.y.length = 256 from layout_widths.inputY,
      ControlledPointLayout.dialogPool_length layout layout_widths]
    decide

end ECDSAAdd.Baselines
end

-- source: ECDSAAdd/Baselines/NormalizedEntries.lean
noncomputable section

namespace ECDSAAdd.Baselines
open Challenge Secp256k1

/-- Skywalk with same-wire CZ and repeated-control CCX normalized. -/
def normalizedSkywalk : Entry := fun C => normalizeProgram (skywalk C)
/-- ValueWalk with same-wire CZ and repeated-control CCX normalized. -/
def normalizedValueWalk : Entry := fun C => normalizeProgram (valueWalk C)

theorem normalizedSkywalk_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (normalizedSkywalk C) (encodes b (if b then R+C else R)) :=
  (normalize_triple _ _ _).mpr (skywalk_correct C b R)

theorem normalizedValueWalk_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (normalizedValueWalk C) (encodes b (if b then R+C else R)) :=
  (normalize_triple _ _ _).mpr (valueWalk_correct C b R)

theorem normalizedSkywalk_toffoli_exact (C : Point) :
    toffoliCount (normalizedSkywalk C) + repeatedControls (skywalk C) =
      toffoliCount (skywalk C) := normalize_toffoli_exact _

theorem normalizedValueWalk_toffoli_exact (C : Point) :
    toffoliCount (normalizedValueWalk C) + repeatedControls (valueWalk C) =
      toffoliCount (valueWalk C) := normalize_toffoli_exact _

theorem normalizedSkywalk_qubits (C : Point) : qubits (normalizedSkywalk C) ≤ 1899 := by
  rw [normalizedSkywalk, normalize_qubits]
  exact skywalk_qubits C

theorem normalizedValueWalk_qubits (C : Point) : qubits (normalizedValueWalk C) ≤ 3134 := by
  rw [normalizedValueWalk, normalize_qubits]
  exact valueWalk_qubits C

end ECDSAAdd.Baselines
end

-- source: ECDSAAdd/Baselines/SlotAlgebra.lean
noncomputable section

namespace ECDSAAdd.Baselines
open Challenge Arithmetic

@[simp] theorem gateSlots_nil : gateSlots [] = 0 := rfl
@[simp] theorem gateSlots_cons (i : Instr) (p : Program) :
    gateSlots (i :: p) = instructionSlots i + gateSlots p := rfl

@[simp] theorem normalize_gateSlots (p : Program) :
    gateSlots (normalizeProgram p) = gateSlots p := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    cases i with
    | CCX a b t => by_cases h : a = b <;>
        simp [normalizeProgram, normalizeInstr, h, gateSlots_cons, instructionSlots] at ih ⊢ <;> exact ih
    | measureX t cs ds =>
        simpa [normalizeProgram, normalizeInstr, gateSlots_cons, instructionSlots] using congrArg (fun n => 1 + cs.length + ds.length + n) ih
    | X t => simpa [normalizeProgram, normalizeInstr, gateSlots_cons, instructionSlots] using ih
    | CX c t => simpa [normalizeProgram, normalizeInstr, gateSlots_cons, instructionSlots] using ih

@[simp] theorem gateSlots_flatMap {α : Type} (f : α → Program) (xs : List α) :
    gateSlots (xs.flatMap f) = (xs.map (fun x => gateSlots (f x))).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

 theorem xorConstant_gateSlots_le (r : List Wire) (k : Nat) :
    gateSlots (xorConstant r k) ≤ r.length := by
  induction r generalizing k with
  | nil => simp [xorConstant]
  | cons w ws ih =>
    simp only [xorConstant, gateSlots_append, List.length_cons]
    split <;> simp only [gateSlots_cons, gateSlots_nil, instructionSlots] <;> have := ih (k / 2) <;> omega

 theorem maskedConstant_gateSlots_le (c : Wire) (r : List Wire) (k : Nat) :
    gateSlots (maskedConstant c r k) ≤ r.length := by
  induction r generalizing k with
  | nil => simp [maskedConstant]
  | cons w ws ih =>
    simp only [maskedConstant, gateSlots_append, List.length_cons]
    split <;> simp only [gateSlots_cons, gateSlots_nil, instructionSlots] <;> have := ih (k / 2) <;> omega

@[simp] theorem zeroControlled_gateSlots (c t : Wire) (bs : List ZeroBit) :
    gateSlots (zeroControlled c t bs) = 7 * bs.length + 1 := by
  induction bs generalizing c with
  | nil => rfl
  | cons b bs ih =>
    change gateSlots ([.X b.input, .CCX c b.input b.work, .X b.input] ++
      zeroControlled b.work t bs ++ [.X b.input, .measureX b.work [] [.CZ c b.input], .X b.input]) = _
    simp [ih, gateSlots_cons, instructionSlots]
    omega

theorem equalConstant_gateSlots_le (c t : Wire) (bs : List ZeroBit) (k : Nat) :
    gateSlots (equalConstant c t bs k) ≤ 9 * bs.length + 1 := by
  have h := xorConstant_gateSlots_le (bs.map ZeroBit.input) k
  simp only [List.length_map] at h
  simp only [equalConstant, gateSlots_append, zeroControlled_gateSlots]
  omega

@[simp] theorem copyRegister_gateSlots (c : Option Wire) (a b : List Wire) :
    gateSlots (copyRegister c a b) = min a.length b.length := by
  induction a generalizing b with
  | nil => simp [copyRegister]
  | cons a as ih =>
    cases b with
    | nil => simp [copyRegister]
    | cons b bs => cases c <;> simp [copyRegister, copyGate, gateSlots_cons, instructionSlots, ih, Nat.add_comm]

@[simp] theorem swapRegisters_gateSlots (c : Wire) (a b : List Wire) :
    gateSlots (swapRegisters c a b) = 3 * min a.length b.length := by
  simp [swapRegisters, Nat.min_comm]; omega

@[simp] theorem exchangeRegisters_gateSlots (a b : List Wire) :
    gateSlots (exchangeRegisters a b) = 3 * min a.length b.length := by
  simp [exchangeRegisters, Nat.min_comm]; omega

@[simp] theorem notRegister_gateSlots (r : List Wire) :
    gateSlots (notRegister r) = r.length := by
  induction r with
  | nil => rfl
  | cons w r ih =>
      change 1 + gateSlots (notRegister r) = r.length + 1
      omega

@[simp] theorem majority_gateSlots (a b c t : Wire) : gateSlots (majority a b c t) = 6 := rfl
@[simp] theorem eraseCarry_gateSlots (a b c t : Wire) : gateSlots (eraseCarry a b c t) = 4 := rfl
@[simp] theorem fullAdder_gateSlots (a b c o t : Wire) : gateSlots (fullAdder a b c o t) = 9 := rfl

@[simp] theorem rippleAdder_gateSlots (bs : List AddBit) (c : Wire) :
    gateSlots (rippleAdder bs c) = 13 * bs.length := by
  induction bs generalizing c with
  | nil => rfl
  | cons b bs ih => simp [rippleAdder, ih]; omega

 theorem addInPlace_gateSlots_le (x y cs : List Wire) (c : Wire) :
    gateSlots (addInPlace x y cs c) ≤ 12 * x.length := by
  induction x, y, cs, c using addInPlace.induct with
  | case1 a a' as b b' bs d ds c ih =>
      simp only [addInPlace, gateSlots_append, majority_gateSlots, eraseCarry_gateSlots,
        gateSlots_cons, gateSlots_nil, instructionSlots, List.length_cons] at *
      omega
  | case2 a b cs c => simp [addInPlace, gateSlots_cons, instructionSlots]
  | case3 x y cs c h => simp [addInPlace]

 theorem subInPlace_gateSlots_le (x y cs : List Wire) (c : Wire) :
    gateSlots (subInPlace x y cs c) ≤ 12 * x.length + 2 * y.length := by
  have h := addInPlace_gateSlots_le x y cs c
  simp only [subInPlace, gateSlots_append, notRegister_gateSlots]; omega

@[simp] theorem eraseMask_gateSlots (c : Wire) (a b : List Wire) :
    gateSlots (eraseMask c a b) = 2 * min a.length b.length := by
  induction a generalizing b with
  | nil => simp [eraseMask]
  | cons a as ih =>
    cases b with
    | nil => simp [eraseMask]
    | cons b bs => simp [eraseMask, gateSlots_cons, instructionSlots, ih]; omega

 theorem compareChain_gateSlots_le (ctrl : Option Wire) (x y cs : List Wire) (c t : Wire) :
    gateSlots (compareChain ctrl x y cs c t) ≤ 10 * x.length + 2 := by
  induction x generalizing y cs c with
  | nil => cases y <;> cases cs <;> cases ctrl <;> simp [compareChain, flipBelow, gateSlots_cons, instructionSlots]
  | cons a as ih =>
    cases y with
    | nil => simp [compareChain]
    | cons b bs =>
      cases cs with
      | nil => simp [compareChain]
      | cons d ds =>
        have h := ih bs ds d
        simp only [compareChain, gateSlots_append, majority_gateSlots, eraseCarry_gateSlots, List.length_cons]
        omega

 theorem compareLt_gateSlots_le (ctrl : Option Wire) (x y cs : List Wire) (c t : Wire) :
    gateSlots (compareLt ctrl x y cs c t) ≤ 10 * x.length + 2 * y.length + 4 := by
  have h := compareChain_gateSlots_le ctrl x y cs c t
  simp only [compareLt, gateSlots_append, notRegister_gateSlots, List.length_cons]; omega

 theorem compareLtConst_gateSlots_le (ctrl : Option Wire) (x y cs : List Wire) (c t k : Nat) :
    gateSlots (compareLtConst ctrl x y cs c t k) ≤ 10 * x.length + 4 * y.length + 4 := by
  have h := compareLt_gateSlots_le ctrl x y cs c t
  have hk := xorConstant_gateSlots_le y k
  simp only [compareLtConst, gateSlots_append]; omega

theorem shift_gateSlots (c : Wire) (r : List Wire) :
    gateSlots (shiftRight c r) = 3 * (r.length - 1) ∧
    gateSlots (shiftLeft c r) = 3 * (r.length - 1) := by
  induction r with
  | nil => constructor <;> rfl
  | cons a as ih =>
    cases as with
    | nil => constructor <;> rfl
    | cons b bs =>
      simp only [shiftRight, shiftLeft, gateSlots_append, ih.1, ih.2, List.length_cons]
      have h : gateSlots (cswap c a b) = 3 := rfl
      rw [h]; constructor <;> omega

theorem measuredMasked_gateSlots_le (c : Wire) (src t y cs : List Wire) (cin : Wire) :
    gateSlots (measuredMaskedAddInPlace c src t y cs cin) ≤ 15 * t.length ∧
    gateSlots (measuredMaskedSubInPlace c src t y cs cin) ≤ 15 * t.length + 2 * y.length := by
  have ha := addInPlace_gateSlots_le t y cs cin
  have hs := subInPlace_gateSlots_le t y cs cin
  have hm := Nat.min_le_right src.length t.length
  simp only [measuredMaskedAddInPlace, measuredMaskedSubInPlace, gateSlots_append,
    copyRegister_gateSlots, eraseMask_gateSlots]
  constructor <;> omega

theorem maskedConst_gateSlots_le (c : Wire) (t y cs : List Wire) (cin k : Nat) :
    gateSlots (maskedAddConst c t y cs cin k) ≤ 14 * t.length ∧
    gateSlots (maskedSubConst c t y cs cin k) ≤ 14 * t.length + 2 * y.length := by
  have ha := addInPlace_gateSlots_le t y cs cin
  have hs := subInPlace_gateSlots_le t y cs cin
  have hm := maskedConstant_gateSlots_le c t k
  simp only [maskedAddConst, maskedSubConst, gateSlots_append]
  constructor <;> omega

theorem modAddCore_gateSlots_le (L : ModAddCoreLayout) (p : Nat) :
    gateSlots (modAddCore L p) ≤
      14 * L.a.length + 14 * L.constant.length + 26 * L.low.length + 7 := by
  have ha := addInPlace_gateSlots_le L.a L.z L.carry L.cin
  have hs := subInPlace_gateSlots_le L.constant L.z L.carry L.cin
  have hx := xorConstant_gateSlots_le L.constant p
  have hm := (maskedConst_gateSlots_le L.high (L.constant.take L.low.length) L.low
    (L.carry.take (L.low.length-1)) L.cin p).1
  have hc := compareLt_gateSlots_le none L.low (L.a.take L.low.length) L.carry L.cin L.high
  simp only [List.length_take] at hm hc
  have h1 := Nat.min_le_right L.low.length L.constant.length
  have h2 := Nat.min_le_left L.low.length L.constant.length
  have h3 := Nat.min_le_right L.low.length L.a.length
  have hz : L.z.length = L.low.length + 1 := by simp [ModAddCoreLayout.z]
  simp only [modAddCore, gateSlots_append, gateSlots_cons, gateSlots_nil, instructionSlots]
  omega

theorem negRaw_gateSlots_le (L : ModInPlaceLayout) (p : Nat) :
    gateSlots (negRaw L p) ≤ L.a.length + 14 * L.constant.length := by
  have ha := addInPlace_gateSlots_le L.constant L.a L.carry L.cin
  have hx := xorConstant_gateSlots_le L.constant (p+1)
  simp only [negRaw, gateSlots_append, notRegister_gateSlots]; omega

end ECDSAAdd.Baselines
end

-- source: ECDSAAdd/Baselines/SlotMapped.lean
noncomputable section

namespace ECDSAAdd.Baselines
open Arithmetic Challenge

@[simp] theorem rename_gateSlots (f : Wire → Wire) (p : Program) :
    gateSlots (renameProgram f p) = gateSlots p := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    cases i <;> simpa only [renameProgram, List.map_cons, renameInstr, gateSlots_cons,
      instructionSlots, List.length_map] using congrArg (_ + ·) ih

theorem mappedBit_gateSlots_le (b : MappedBit) (y c t : Wire) :
    gateSlots (mappedMajority b y c t) ≤ 8 ∧
    gateSlots (mappedEraseCarry b y c t) ≤ 6 ∧
    gateSlots (mappedSum b y c) ≤ 3 := by
  cases b with
  | mk w f => cases w <;> cases f <;>
      simp [mappedMajority, mappedEraseCarry, mappedSum, borrowMajority, eraseBorrow,
        gateSlots_cons, instructionSlots]

theorem mappedAdd_gateSlots_le (xs : List MappedBit) (ys cs : List Wire) (c : Wire) :
    gateSlots (mappedAdd xs ys cs c) ≤ 17*xs.length := by
  induction xs, ys, cs, c using mappedAdd.induct with
  | case1 b b' bs y y' ys d ds c ih =>
    simp only [List.length_cons] at ih
    have h := mappedBit_gateSlots_le b y c d
    simp only [mappedAdd, gateSlots_append, List.length_cons]
    omega
  | case2 b y cs c =>
    have h := (mappedBit_gateSlots_le b y c c).2.2
    simpa only [mappedAdd, List.length_singleton] using h.trans (by decide : 3 ≤ 17)
  | case3 xs ys cs c h => simp [mappedAdd]

theorem mappedConst_gateSlots_le (ctrl : Option Wire) (ys cs : List Wire) (c k : Nat) :
    gateSlots (mappedConstAdd ctrl ys cs c k) ≤ 17*ys.length := by
  simpa only [mappedConstAdd, mappedConstant_length] using
    mappedAdd_gateSlots_le (mappedConstant ctrl ys.length k) ys cs c

theorem eraseLt_gateSlots_le (xs ys cs : List Wire) (c t : Wire) :
    gateSlots (eraseLtChain xs ys cs c t) ≤ 14*xs.length := by
  induction xs, ys, cs, c, t using eraseLtChain.induct with
  | case1 a a' as b b' bs d ds c t ih =>
    simp only [List.length_cons] at ih
    simp only [eraseLtChain, gateSlots_append, borrowMajority, eraseBorrow, majority_gateSlots,
      eraseCarry_gateSlots, gateSlots_cons, gateSlots_nil, instructionSlots, List.length_cons]
    omega
  | case2 a b cs c t => simp [eraseLtChain, eraseBorrow, gateSlots_cons, instructionSlots]
  | case3 xs ys cs c t h => simp [eraseLtChain]

theorem compareConstant_gateSlots_le (xs cs : List Wire) (c t k : Nat) :
    gateSlots (compareConstantLt xs cs c t k) ≤ 18*xs.length := by
  induction xs, cs, c, t, k using compareConstantLt.induct with
  | case1 x x' xs d ds c t k ih =>
    have h := mappedBit_gateSlots_le {wire:=none,flip:=decide (k%2=1)} x c d
    simp only [List.length_cons] at ih
    simp only [compareConstantLt, constantBorrow, constantBorrowErase, gateSlots_append,
      gateSlots_cons, gateSlots_nil, instructionSlots, List.length_cons]
    omega
  | case2 x cs c t k =>
    have h := (mappedBit_gateSlots_le {wire:=none,flip:=decide (k%2=1)} x c t).1
    simp only [compareConstantLt, constantBorrow, gateSlots_append,
      gateSlots_cons, gateSlots_nil, instructionSlots, List.length_cons, List.length_nil]
    omega
  | case3 xs cs c t k h => simp [compareConstantLt]

theorem canonicalMod_gateSlots_le (L : MeasuredCanonicalModLayout) (n c p : Nat) (hw : L.Widths n) :
    gateSlots (L.program c p) ≤ 66*n+37 := by
  have he : L.extended.length = n+1 := by simp [MeasuredCanonicalModLayout.extended, hw.out]
  have hs := mappedAdd_gateSlots_le (mappedRead L.src false++[{wire:=none,flip:=false}]) L.extended L.carry L.cin
  simp only [List.length_append, List.length_cons, List.length_nil, mappedRead_length, hw.src] at hs
  have hc := compareConstant_gateSlots_le L.out (L.carry.take (L.out.length-1)) L.cin L.flag p
  have hm := mappedConst_gateSlots_le (some L.flag) L.extended L.carry L.cin c
  have hb := eraseLt_gateSlots_le L.out L.src (L.carry.take (L.out.length-1)) L.cin L.flag
  rw [hw.out] at hc hb
  rw [he] at hm
  simp only [MeasuredCanonicalModLayout.program, MeasuredCanonicalModLayout.sum,
    compareConstantGe, gateSlots_append, gateSlots_cons, gateSlots_nil, instructionSlots, hw.out]
  omega

end ECDSAAdd.Baselines
end

-- source: ECDSAAdd/Baselines/SlotSignedInteger.lean
noncomputable section

namespace ECDSAAdd.Baselines
open Arithmetic Challenge

theorem signComplement_gateSlots (q : Wire) (xs : List Wire) :
    gateSlots (signComplement q xs) = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [signComplement, List.map_cons, gateSlots_cons,
      instructionSlots, List.length_cons] at *; omega

theorem signedWord_gateSlots_le (q : Wire) (xs ys cs : List Wire) :
    gateSlots (signedAdd q xs ys cs) ≤ 14*xs.length ∧
    gateSlots (signedSub q xs ys cs) ≤ 14*xs.length+2*ys.length := by
  have h := addInPlace_gateSlots_le xs ys cs q
  simp only [signedAdd, signedSub, gateSlots_append, signComplement_gateSlots,
    notRegister_gateSlots]; omega

theorem signedRecord_gateSlots_le (sx sy q : Wire) (xs ys cs : List Wire) :
    gateSlots (signedRecord sx sy q xs ys cs) ≤ 14*xs.length+6 ∧
    gateSlots (signedUnrecord sx sy q xs ys cs) ≤ 14*xs.length+2*ys.length+6 := by
  have h := signedWord_gateSlots_le q xs ys cs
  simp only [signedRecord, signedUnrecord, skywalkSignToggle, gateSlots_append,
    gateSlots_cons, gateSlots_nil, instructionSlots]; omega

theorem narrowRecord_gateSlots_le (L : NarrowSignedRecordLayout) (n : Nat) :
    gateSlots (narrowSignedRecord L n) ≤ 14*L.x.length+L.y.length+6 ∧
    gateSlots (narrowSignedUnrecord L n) ≤ 14*L.x.length+3*L.y.length+6 := by
  have h := signedRecord_gateSlots_le L.sx L.sy L.q (L.x.take n) (L.y.take n) (L.carry.take (n-1))
  simp only [List.length_take] at h
  simp only [narrowSignedRecord,narrowSignedUnrecord,gateSlots_append,
    signComplement_gateSlots,List.length_drop]
  omega

theorem narrowTick_gateSlots_le (L : SkywalkIntegerLayout) (n : Nat) :
    gateSlots (narrowSkywalkTick L n) ≤ 3*L.ah.length+14*L.half.length+3*L.b.length+26 ∧
    gateSlots (narrowSkywalkUntick L n) ≤ 3*L.ah.length+14*L.half.length+3*L.b.length+26 := by
  have h := narrowRecord_gateSlots_le (narrowSkywalkRecordLayout L n) n
  have hx : (narrowSkywalkRecordLayout L n).x.length ≤ L.half.length+1 := by
    simp only [narrowSkywalkRecordLayout,NarrowSignedRecordLayout.x,NarrowSignedRecordLayout.xp,
      List.length_append,List.length_take,List.length_drop,List.length_singleton]; omega
  have hy : (narrowSkywalkRecordLayout L n).y.length ≤ L.b.length+1 := by
    simp only [narrowSkywalkRecordLayout,NarrowSignedRecordLayout.y,NarrowSignedRecordLayout.yp,
      List.length_append,List.length_take,List.length_drop,List.length_singleton]; omega
  have hm := Nat.min_le_left L.ah.length L.bh.length
  simp only [narrowSkywalkTick,narrowSkywalkUntick,skywalkRoute,skywalkSignedHalf,
    gateSlots_append,swapRegisters_gateSlots,gateSlots_cons,gateSlots_nil,instructionSlots]
  omega

theorem compactTick_gateSlots_le (w : Nat → Wire) (i : Nat) (hi : i < 512) :
    gateSlots (compactSkywalkTick w i) ≤ 6000 ∧
    gateSlots (compactSkywalkReverseTick w i) ≤ 6000 := by
  have h := narrowTick_gateSlots_le (compactSkywalkTickLayout w i) (compactSkywalkTickPostWidth i)
  have hb := compactSkywalkTick_width_bounds i hi
  rw [compactSkywalkTick_ah w i hi, compactSkywalkTick_half w i hi,
    compactSkywalkTick_b w i hi, wireBlock_length, wireBlock_length, wireBlock_length] at h
  have hc : gateSlots (compactSkywalkTickCleanup w i) ≤ 516 := by
    simp only [compactSkywalkTickCleanup,compactSkywalkTickARelease,compactSkywalkTickBRelease,
      compactSkywalkSignRelease,compactSkywalkSignWord,gateSlots_append,signComplement_gateSlots,
      List.length_drop,compactSkywalkTick_half w i hi,compactSkywalkTick_b w i hi,wireBlock_length]
    omega
  have he : gateSlots (compactSkywalkReverseExpand w i) = gateSlots (compactSkywalkTickCleanup w i) := by
    simp only [compactSkywalkReverseExpand,compactSkywalkTickCleanup,compactSkywalkSignExpand,
      compactSkywalkSignRelease,gateSlots_append,signComplement_gateSlots]; omega
  simp only [compactSkywalkTick,compactSkywalkReverseTick,gateSlots_append]
  omega

end ECDSAAdd.Baselines
end

-- source: ECDSAAdd/Baselines/SlotCodec.lean
noncomputable section

namespace ECDSAAdd.Baselines
open Arithmetic Challenge

theorem codec_gateSlots_le (w : Nat → Wire) (start : Nat) :
    gateSlots (compressedHistoryEncode w start) ≤ 200 ∧
    gateSlots (compressedHistoryDecode w start) ≤ 200 := by
  simp only [compressedHistoryEncode,compressedHistoryDecode,TranscriptCodec3.encode,
    TranscriptCodec3.decode,rename_gateSlots]
  constructor <;> decide

theorem scheduledCodec_gateSlots_le (w : Nat → Wire) (i : Nat) :
    gateSlots (compressedPackAfter w i) ≤ 200 ∧
    gateSlots (compressedDecodeBefore w i) ≤ 200 := by
  have h := codec_gateSlots_le w (i-3)
  unfold compressedPackAfter compressedDecodeBefore
  split <;> simp_all only [gateSlots_nil, Nat.zero_le, and_self]

theorem compactLoops_gateSlots_le (w : Nat → Wire) (i n : Nat) (hn : i+n ≤ 512) :
    gateSlots (compressedCompactForward w i n) ≤ n*6200 ∧
    gateSlots (compressedCompactReverse w i n) ≤ n*6200 := by
  induction n generalizing i with
  | zero => simp only [compressedCompactForward,compressedCompactReverse,
      gateSlots_nil,Nat.zero_mul,Nat.le_refl,and_self]
  | succ n ih =>
    have h := compactTick_gateSlots_le w i (by omega)
    have hc := scheduledCodec_gateSlots_le w i
    have ht := ih (i+1) (by omega)
    simp only [compressedCompactForward,compressedCompactReverse,gateSlots_append,
      Nat.succ_mul]
    omega

end ECDSAAdd.Baselines
end

-- source: ECDSAAdd/Baselines/SlotNativeFirst.lean
noncomputable section

namespace ECDSAAdd.Baselines
open Arithmetic Challenge

theorem rotate_gateSlots_le (xs : List Wire) :
    gateSlots (rotateRight xs) ≤ 3*xs.length ∧ gateSlots (rotateLeft xs) ≤ 3*xs.length := by
  induction xs using List.twoStepInduction with
  | nil => simp [rotateRight,rotateLeft]
  | singleton x => simp [rotateRight,rotateLeft]
  | cons_cons x y xs ih ih' =>
    have ht := ih' y
    simp only [rotateRight,rotateLeft,gateSlots_append,swapBits,gateSlots_cons,
      gateSlots_nil,instructionSlots,List.length_cons] at *
    omega

theorem knownXor_gateSlots_le (b : MappedBit) (t : Wire) :
    gateSlots (KnownOutputAdder.xorBit b t) ≤ 2 := by
  cases b with
  | mk w f => cases w <;> cases f <;>
      simp [KnownOutputAdder.xorBit,gateSlots_cons,instructionSlots]

theorem knownAdder_gateSlots_le (xs ds : List MappedBit) (ys cs : List Wire) (c : Wire) :
    gateSlots (KnownOutputAdder.program xs ys ds cs c) ≤ 14*xs.length := by
  induction xs, ys, ds, cs, c using KnownOutputAdder.program.induct with
  | case1 b b' bs y y' ys d d' ds t ts c ih =>
    have h := mappedBit_gateSlots_le b y c t
    have h1 := knownXor_gateSlots_le b' t
    have h2 := knownXor_gateSlots_le d' t
    simp only [KnownOutputAdder.program,KnownOutputAdder.prepare,gateSlots_append,
      gateSlots_cons,gateSlots_nil,instructionSlots,List.length_cons] at *
    omega
  | case2 b y d cs c =>
    have h := (mappedBit_gateSlots_le b y c c).2.2
    simpa only [KnownOutputAdder.program,List.length_singleton] using h.trans (by decide : 3 ≤ 14)
  | case3 xs ys ds cs c h => simp [KnownOutputAdder.program]

theorem nativeFirst_gateSlots_le (w : Nat → Wire) :
    gateSlots (NativeFirstDirect.forward w) ≤ 10000 ∧
    gateSlots (NativeFirstKnown.inverse w) ≤ 10000 := by
  have hh := mappedAdd_gateSlots_le (NativeFirstDirect.hBits w false)
    (wireBlock w 4 253) (wireBlock w 1540 252) (w 1797)
  have hk (b : Bool) := mappedAdd_gateSlots_le (NativeFirstDirect.kBits w b)
    (wireBlock w 771 257) (wireBlock w 1540 256) (w 770)
  have hr := rotate_gateSlots_le (wireBlock w 770 258)
  have hn := knownAdder_gateSlots_le (NativeFirstDirect.hBits w true) (NativeFirstKnown.desired w)
    (wireBlock w 4 253) (wireBlock w 1540 252) (w 1797)
  simp only [NativeFirstDirect.hBits_length,NativeFirstDirect.kBits_length,wireBlock_length] at hh hk hn hr
  have hkf := hk false
  have hkt := hk true
  simp only [NativeFirstDirect.forward,NativeFirstKnown.inverse,NativeFirstKnown.hReceiver,
    sealedProgram_eq,NativeFirstDirect.hAdd,NativeFirstDirect.kAdd,NativeFirstDirect.lowCopy,
    NativeFirstDirect.inverseUnmiddle,NativeFirstDirect.inverseBack,gateSlots_append,
    copyRegister_gateSlots,wireBlock_length,gateSlots_cons,gateSlots_nil,instructionSlots]
  omega

end ECDSAAdd.Baselines
end

-- source: ECDSAAdd/Baselines/SlotSignedSquare.lean
noncomputable section

namespace ECDSAAdd.Baselines
open Arithmetic Challenge

@[simp] theorem reverse_gateSlots (p : Program) : gateSlots p.reverse = gateSlots p := by
  simp [gateSlots, List.map_reverse]

@[simp] theorem xorWhenFalse_gateSlots (c : Wire) (ys : List Wire) :
    gateSlots (xorWhenFalse c ys) = 2*ys.length := by
  induction ys with
  | nil => rfl
  | cons y ys ih => simp [xorWhenFalse, gateSlots_cons, instructionSlots, ih]; omega

theorem signedRow_gateSlots_le (c : Wire) (xs dst pad carry : List Wire) :
    gateSlots (signedSquareRow c xs dst pad carry) ≤ 12*(xs.length+1)+6*dst.length ∧
    gateSlots (signedSquareRowClear c xs dst pad carry) ≤ 12*(xs.length+1)+6*dst.length := by
  have ha := addInPlace_gateSlots_le (xs++pad.take 1) dst (carry.take xs.length) c
  simp only [List.length_append, List.length_take] at ha
  simp only [signedSquareRow, signedSquareRowClear, gateSlots_append, xorWhenFalse_gateSlots,
    notRegister_gateSlots, List.length_take]
  constructor <;> omega

theorem signedRows_gateSlots_le (xs dst pad carry : List Wire) :
    gateSlots (signedSquareRows xs dst pad carry) ≤ xs.length*(12*(xs.length+1)+6*dst.length) ∧
    gateSlots (signedSquareRowsClear xs dst pad carry) ≤ xs.length*(12*(xs.length+1)+6*dst.length) := by
  induction xs using List.twoStepInduction generalizing dst with
  | nil => simp [signedSquareRows, signedSquareRowsClear]
  | singleton x => simp [signedSquareRows, signedSquareRowsClear]
  | cons_cons x y xs ih ih' =>
    have ht := ih' y (dst.drop 2)
    have hr := signedRow_gateSlots_le x (y::xs) ((dst.drop 1).take ((y::xs).length+1)) pad carry
    simp only [List.length_drop, List.length_take, List.length_cons] at ht hr
    simp only [signedSquareRows, signedSquareRowsClear, gateSlots_append, List.length_cons]
    have hd : (dst.drop 2).length ≤ dst.length := by simp
    constructor <;> nlinarith [ht.1,ht.2,hr.1,hr.2, Nat.min_le_right (xs.length+1+1) (dst.length-1), Nat.sub_le dst.length 1, Nat.sub_le dst.length 2]

theorem signedTop_gateSlots_le (xs dst : List Wire) : gateSlots (signedSquareTop xs dst) ≤ 1 := by
  induction xs, dst using signedSquareTop.induct with
  | case1 dst => simp [signedSquareTop]
  | case2 x a z ds => simp [signedSquareTop, gateSlots_cons, instructionSlots]
  | case3 a x xs b c dst ih => simpa only [signedSquareTop] using ih
  | case4 xs dst h => simp [signedSquareTop]

theorem mappedSigned_gateSlots_le (xs dst pad carry : List Wire) (cin : Wire) :
    gateSlots (mappedSignedSquare xs dst pad carry cin) ≤
      xs.length*(12*(xs.length+1)+6*dst.length)+34*xs.length+2*dst.length+18 ∧
    gateSlots (mappedSignedSquareClear xs dst pad carry cin) ≤
      xs.length*(12*(xs.length+1)+6*dst.length)+34*xs.length+2*dst.length+18 := by
  have hr := signedRows_gateSlots_le xs dst pad carry
  have ht := signedTop_gateSlots_le xs dst
  have hm := mappedAdd_gateSlots_le (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin
  have hl : (mappedDiagonal xs).length ≤ 2*xs.length+1 := by
    simp only [mappedDiagonal, List.length_append, mappedRead_length, List.length_take, List.length_cons, List.length_nil]; omega
  simp only [mappedSignedSquare, mappedSignedSquareClear, mappedDiagSub, mappedDiagAdd,
    mappedSub, gateSlots_append, notRegister_gateSlots]
  constructor <;> omega

end ECDSAAdd.Baselines
end

-- source: ECDSAAdd/Baselines/SlotBalanced.lean
noncomputable section

namespace ECDSAAdd.Baselines
open Arithmetic Challenge

theorem literalCells_gateSlots_le (b : Bool) (x c t one : Wire) :
    gateSlots (literalConstStep b x c t) ≤ 6 ∧
    gateSlots (literalConstErase b x c t one) ≤ 6 ∧
    gateSlots (literalConstSum b x c) ≤ 2 := by
  cases b <;> simp [literalConstStep,literalConstSum,literalConstCarry,literalConstErase,
    gateSlots_cons,instructionSlots]

theorem literalAdd_gateSlots_le (xs cs : List Wire) (c one k : Nat) :
    gateSlots (literalConstAdd xs cs c one k) ≤ 12*xs.length := by
  induction xs, cs, c, one, k using literalConstAdd.induct with
  | case1 x x' xs d ds c one k ih =>
    have h := literalCells_gateSlots_le (decide (k%2=1)) x c d one
    simp only [literalConstAdd,gateSlots_append,List.length_cons] at *; omega
  | case2 x cs c one k =>
    have h := (literalCells_gateSlots_le (decide (k%2=1)) x c c one).2.2
    simpa only [literalConstAdd,List.length_singleton] using h.trans (by decide : 2 ≤ 12)
  | case3 xs cs c one k h => simp [literalConstAdd]

theorem mappedSub_gateSlots_le (xs : List MappedBit) (ys cs : List Wire) (c : Wire) :
    gateSlots (mappedSub xs ys cs c) ≤ 17*xs.length+2*ys.length := by
  have h := mappedAdd_gateSlots_le xs ys cs c
  simp only [mappedSub,gateSlots_append,notRegister_gateSlots]; omega

theorem balancedConvert_gateSlots_le (L : BalancedConvert.Layout) (hw : L.Widths) :
    gateSlots (BalancedConvert.center L) ≤ 12000 ∧
    gateSlots (BalancedConvert.canonical L) ≤ 12000 := by
  have hl : L.word.length = 256 := by simp [BalancedConvert.Layout.word,hw.1]
  have hc : (BalancedConvert.correction L).length = 256 := by simp [BalancedConvert.correction]
  have a := literalAdd_gateSlots_le L.word L.carry L.cin L.one BalancedConvert.bias
  have b := literalAdd_gateSlots_le L.word L.carry L.cin L.one BalancedConvert.inverseBias
  have c := mappedAdd_gateSlots_le (BalancedConvert.correction L) L.word L.carry L.cin
  have d := mappedSub_gateSlots_le (BalancedConvert.correction L) L.word L.carry L.cin
  rw [hl] at a b
  rw [hc] at c
  rw [hc,hl] at d
  simp only [BalancedConvert.center,BalancedConvert.canonical,BalancedConvert.predicate,
    gateSlots_append,gateSlots_cons,gateSlots_nil,instructionSlots]; omega

theorem balancedCore_gateSlots_le (L : BalancedCircuit.Layout) (hw : L.Widths) :
    gateSlots (BalancedCircuit.coreProgram L) ≤ 10000 ∧
    gateSlots (OffsetBorrowedInverse.tail L) ≤ 11000 := by
  have hl := BalancedCleanup.widths L.toLayout hw
  have hs : (BalancedCircuit.rawSource L).length = 257 := by
    simp only [BalancedCircuit.rawSource,List.length_append,List.length_singleton,hl.2.2.1]
  have ht : (BalancedCircuit.rawTarget L).length = 257 := by
    simp only [BalancedCircuit.rawTarget,List.length_append,List.length_singleton,hl.2.1]
  have hf : (BalancedCircuit.foldTarget L++[L.cout]).length = 257 := by
    simp only [BalancedCircuit.foldTarget,List.length_append,List.length_cons,List.length_nil,hw.1]
  have hb : (BalancedCircuit.foldBits L).length = 257 := by simp [BalancedCircuit.foldBits]
  have a := addInPlace_gateSlots_le (BalancedCircuit.rawSource L) (BalancedCircuit.rawTarget L) L.carry L.sign
  have b := subInPlace_gateSlots_le (BalancedCircuit.rawSource L) (BalancedCircuit.rawTarget L) L.carry L.sign
  have c := mappedAdd_gateSlots_le (BalancedCircuit.foldBits L) (BalancedCircuit.foldTarget L++[L.cout]) L.carry L.parity
  have d := mappedSub_gateSlots_le (BalancedCircuit.foldBits L) (BalancedCircuit.foldTarget L++[L.cout]) L.carry L.parity
  have r := rotate_gateSlots_le (BalancedCircuit.rawTarget L)
  rw [hs] at a
  rw [hs,ht] at b
  rw [hb] at c
  rw [hb,hf] at d
  rw [ht] at r
  simp only [BalancedCircuit.coreProgram,OffsetBorrowedInverse.tail,
    BalancedCircuit.seedViews,BalancedCircuit.rawAdd,BalancedCircuit.prepareFold,
    BalancedCircuit.fold,BalancedCircuit.releaseSelectors,BalancedInverse.recoverSelectors,
    BalancedInverse.undoFold,BalancedInverse.undoPreparation,BalancedInverse.rawSubtract,
    gateSlots_append,reverse_gateSlots,signComplement_gateSlots,hs,
    gateSlots_cons,gateSlots_nil,instructionSlots,List.length_cons,List.length_nil]
  omega

end ECDSAAdd.Baselines
end

-- source: ECDSAAdd/Baselines/SlotParity.lean
noncomputable section

namespace ECDSAAdd.Baselines
open Arithmetic Challenge

theorem parityHeads_gateSlots_le (b : MappedBit) (a y cc cb c d : Wire) :
    gateSlots (BalancedCleanupOffset.prepareHead b a y cc cb c d) ≤ 18 ∧
    gateSlots (BalancedCleanupOffset.releaseHead b a y cc cb c d) ≤ 14 := by
  have h := mappedBit_gateSlots_le b y cc c
  simp only [BalancedCleanupOffset.prepareHead,BalancedCleanupOffset.releaseHead,
    gateSlots_append,majority_gateSlots,eraseCarry_gateSlots,gateSlots_cons,
    gateSlots_nil,instructionSlots]; omega

theorem parityChain_gateSlots_le (bs : List MappedBit) (xs ys cs ds : List Wire) (cc cb t : Wire) :
    gateSlots (TerminalParityMeasure.chain bs xs ys cs ds cc cb t) ≤ 40*bs.length+2 := by
  induction bs,xs,ys,cs,ds,cc,cb,t using TerminalParityMeasure.chain.induct with
  | case1 b a y c d cc cb t =>
    have h := (mappedBit_gateSlots_le b y cc c).2.2
    simp only [TerminalParityMeasure.chain,TerminalParityMeasure.leaf,TerminalParityMeasure.program,
      gateSlots_append,gateSlots_cons,gateSlots_nil,instructionSlots,eraseCarry_gateSlots,List.length_singleton]; omega
  | case2 b bs a xs y ys c cs d ds cc cb t hcond ih =>
    have h := parityHeads_gateSlots_le b a y cc cb c d
    simp only [TerminalParityMeasure.chain,gateSlots_append,List.length_cons] at *
    omega
  | case3 cc cb t => simp [TerminalParityMeasure.chain,flipBelow,gateSlots_cons,instructionSlots]
  | case4 bs xs ys cs ds cc cb t h => simp [TerminalParityMeasure.chain]

theorem slimChain_gateSlots_le (bs : List MappedBit) (xs ys cs ds : List Wire) (cc cb t : Wire) :
    gateSlots (BalancedCleanupOffsetSlim.chain bs xs ys cs ds cc cb t) ≤ 40*bs.length+2 := by
  induction bs,xs,ys,cs,ds,cc,cb,t using BalancedCleanupOffsetSlim.chain.induct with
  | case1 b a y c d cc cb t =>
    have h := (mappedBit_gateSlots_le b y cc c).2.2
    have hc := compareChain_gateSlots_le none [a] [y] [d] cb t
    simp only [List.length_singleton] at hc
    simp only [BalancedCleanupOffsetSlim.chain,gateSlots_append,gateSlots_cons,
      gateSlots_nil,instructionSlots,List.length_singleton]; omega
  | case2 b bs a xs y ys c cs d ds cc cb t hcond ih =>
    have h := parityHeads_gateSlots_le b a y cc cb c d
    simp only [BalancedCleanupOffsetSlim.chain,gateSlots_append,List.length_cons] at *
    omega
  | case3 cc cb t => simp [BalancedCleanupOffsetSlim.chain,flipBelow,gateSlots_cons,instructionSlots]
  | case4 bs xs ys cs ds cc cb t h => simp [BalancedCleanupOffsetSlim.chain]

theorem offsetFront_gateSlots_le (L : BalancedCleanupOffset.Layout) (hw : L.Widths) :
    gateSlots (BalancedCleanupOffset.front L) ≤ 1600 := by
  have hl := BalancedCleanup.widths L.toCircuit.toLayout hw.1
  have hr := rotate_gateSlots_le L.r
  have hx : L.r.length = 256 := hl.2.1
  have hy : L.y.length = 256 := hl.2.2.1
  rw [hx] at hr
  simp only [BalancedCleanupOffset.front,BalancedCleanup.prepareSign,BalancedCleanupOffset.view,
    gateSlots_append,signComplement_gateSlots,gateSlots_cons,gateSlots_nil,instructionSlots]
  change 1 + L.r.length + (gateSlots (rotateLeft L.r) + 3 + L.y.length + L.y.length + 1) + 1 ≤ _
  omega

theorem offsetParity_gateSlots_le (L : BalancedCleanupOffset.Layout) (hw : L.Widths) :
    gateSlots (TerminalParityOffset.program L) ≤ 14000 ∧
    gateSlots (BalancedCleanupOffsetZero.program L) ≤ 14000 := by
  have hf := offsetFront_gateSlots_le L hw
  have h1 := parityChain_gateSlots_le (BalancedCleanupOffset.offsetBits L).tail L.y.tail L.r.tail
    L.offsetCarry.tail L.carry.tail L.one (L.carry.headD 0) L.parity
  have h2 := slimChain_gateSlots_le (BalancedCleanupOffset.offsetBits L).tail L.y.tail L.r.tail
    L.offsetCarry.tail L.carry.tail L.one (L.carry.headD 0) L.parity
  simp only [List.length_tail,BalancedCleanupOffset.offsetBits_length] at h1 h2
  simp only [TerminalParityOffset.program,TerminalParityOffset.core,TerminalParityZeroHead.program,
    BalancedCleanupOffsetZero.program,BalancedCleanupOffsetZero.core,BalancedCleanupOffsetZeroHead.program,
    gateSlots_append,reverse_gateSlots,gateSlots_cons,gateSlots_nil,instructionSlots,
    majority_gateSlots,eraseCarry_gateSlots]
  omega

end ECDSAAdd.Baselines
end

-- source: ECDSAAdd/Baselines/SlotField.lean
noncomputable section

namespace ECDSAAdd.Baselines
open Arithmetic Challenge
attribute [local irreducible] renameProgram copyRegister mixedTranscriptUnitTrace MappedCompressed.logicalCell
  MappedCompressed.mappedGroup MappedCompressed.mappedGroups
  OffsetBorrowedField.program OffsetBorrowedInverse.program
  compressedHistoryEncode compressedHistoryDecode
  EntryMappedFieldSegmentTrim.logicalZero EntryMappedFieldSegmentTrim.firstGroup
  PenultimateSwapIdentity.cell MappedCompressed.converterPair
  transcriptSelectWindow OffsetBorrowedCanonical.body OffsetBorrowedInverseCanonical.body

theorem selectWindow_gateSlots_le (b s f : Wire) (c : Bool) (p : Program) :
    gateSlots (transcriptSelectWindow b s f c p) ≤ gateSlots p+8 := by
  cases c <;> simp [transcriptSelectWindow,transcriptSelectCompute,transcriptSelectExpose,
    transcriptSelectErase,gateSlots_cons,instructionSlots] <;> omega

theorem borrowedField_gateSlots_le (w : Nat → Wire) (sign : Wire) :
    gateSlots (OffsetBorrowedField.program w sign) ≤ 26000 ∧
    gateSlots (OffsetBorrowedInverse.program w sign) ≤ 26000 := by
  have h := balancedCore_gateSlots_le (balancedSharedPorts w sign) (balancedSharedPorts_widths w sign)
  have p := offsetParity_gateSlots_le (OffsetCleanupBorrowedCaller.layout w sign) (OffsetCleanupBorrowedCaller.widths w sign)
  simp only [OffsetBorrowedField.program,OffsetBorrowedInverse.program,OffsetBorrowedInverse.recoverParity,
    gateSlots_append,gateSlots_cons,gateSlots_nil,instructionSlots]
  omega

theorem borrowedCell_gateSlots_le (w : Nat → Wire) (b g sw sign eff : Wire) (ig is : Bool) :
    gateSlots (OffsetBorrowedCanonical.cell w b g sw sign eff ig is) ≤ 27000 ∧
    gateSlots (OffsetBorrowedInverseCanonical.cell w b g sw sign eff ig is) ≤ 27000 := by
  have h := borrowedField_gateSlots_le w sign
  have len := (BalancedCleanup.widths (balancedSharedPorts w sign).toLayout (balancedSharedPorts_widths w sign)).2.1
  have hs : gateSlots (swapRegisters eff (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y) ≤ 768 := by
    rw [swapRegisters_gateSlots]
    rw [len]; omega
  have a := selectWindow_gateSlots_le b sw eff is (OffsetBorrowedCanonical.body w sign eff)
  have aa := selectWindow_gateSlots_le b g sign ig (transcriptSelectWindow b sw eff is (OffsetBorrowedCanonical.body w sign eff))
  have z := selectWindow_gateSlots_le b sw eff is (OffsetBorrowedInverseCanonical.body w sign eff)
  have zz := selectWindow_gateSlots_le b g sign ig (transcriptSelectWindow b sw eff is (OffsetBorrowedInverseCanonical.body w sign eff))
  simp only [OffsetBorrowedCanonical.cell,OffsetBorrowedInverseCanonical.cell,
    OffsetBorrowedCanonical.body,OffsetBorrowedInverseCanonical.body,OffsetBorrowedInverseCanonical.double,
    gateSlots_append,gateSlots_cons,gateSlots_nil,instructionSlots] at a z aa zz ⊢
  omega

theorem logicalCell_gateSlots_le (divide : Bool) (i : Nat) :
    gateSlots (MappedCompressed.logicalCell divide i) ≤ 27000 := by
  have h := borrowedCell_gateSlots_le id 2400 i (1028+i) 2409 2410
    (mixedTranscriptUnitTrace.getD i (false,false)).1 (mixedTranscriptUnitTrace.getD i (false,false)).2
  cases divide <;> simp only [MappedCompressed.logicalCell,Bool.false_eq_true,↓reduceIte]
  · exact h.2
  · exact h.1

theorem mappedGroup_gateSlots_le (divide : Bool) (j : Nat) :
    gateSlots (MappedCompressed.mappedGroup divide j) ≤ 82000 := by
  have a := logicalCell_gateSlots_le divide (3*j)
  have b := logicalCell_gateSlots_le divide (3*j+1)
  have c := logicalCell_gateSlots_le divide (3*j+2)
  have h := codec_gateSlots_le (MappedCompressed.placed j) (3*j)
  cases divide <;> simp only [MappedCompressed.mappedGroup,Bool.false_eq_true,↓reduceIte,
    gateSlots_append,rename_gateSlots] <;> omega

theorem mappedGroups_gateSlots_le (divide : Bool) (j n : Nat) :
    gateSlots (MappedCompressed.mappedGroups divide j n) ≤ n*82000 := by
  induction n generalizing j with
  | zero => simp only [MappedCompressed.mappedGroups,gateSlots_nil,Nat.zero_mul,Nat.le_refl]
  | succ n ih =>
    have h := mappedGroup_gateSlots_le divide j
    have ht := ih (j+1)
    cases divide <;> simp only [MappedCompressed.mappedGroups,Bool.false_eq_true,↓reduceIte,
      gateSlots_append,Nat.succ_mul] <;> omega

theorem firstGroup_gateSlots_le (divide : Bool) :
    gateSlots (EntryMappedFieldSegmentTrim.firstGroup divide) ≤ 56000 := by
  have a := logicalCell_gateSlots_le divide 1
  have b := logicalCell_gateSlots_le divide 2
  have hc := codec_gateSlots_le (MappedCompressed.placed 0) 0
  have hz : gateSlots EntryMappedFieldSegmentTrim.logicalZero ≤ 800 := by
    have h := selectWindow_gateSlots_le 2400 1028 2410
      (mixedTranscriptUnitTrace.getD 0 (false,false)).2
      (swapRegisters 2410 (balancedSharedPorts id 2409).r (balancedSharedPorts id 2409).y)
    have hl := (BalancedCleanup.widths (balancedSharedPorts id 2409).toLayout (balancedSharedPorts_widths id 2409)).2.1
    rw [swapRegisters_gateSlots] at h
    change _ ≤ 3*min (balancedSharedPorts id 2409).toLayout.r.length _ + 8 at h
    rw [hl] at h
    have hb : gateSlots (transcriptSelectWindow 2400 1028 2410
        (mixedTranscriptUnitTrace.getD 0 (false,false)).2
        (swapRegisters 2410 (balancedSharedPorts id 2409).r (balancedSharedPorts id 2409).y)) ≤ 800 := by omega
    simpa only [EntryMappedFieldSegmentTrim.logicalZero,EntryFieldSeedCancellation.selectedSwap] using hb
  cases divide <;> simp only [EntryMappedFieldSegmentTrim.firstGroup,Bool.false_eq_true,↓reduceIte,
    gateSlots_append,rename_gateSlots] <;> omega

theorem endpointCell_gateSlots_le (w : Nat → Wire) (b g flag : Wire) (ig : Bool) :
    gateSlots (EndpointSwapTrim.forward w b g flag ig) ≤ 27000 ∧
    gateSlots (EndpointSwapTrim.inverse w b g flag ig) ≤ 27000 := by
  have h := borrowedField_gateSlots_le w flag
  have a := selectWindow_gateSlots_le b g flag ig
    ([.X flag]++OffsetBorrowedField.program w flag++[.X flag])
  have z := selectWindow_gateSlots_le b g flag ig
    ([.X flag]++OffsetBorrowedInverse.program w flag++[.X flag])
  simp only [EndpointSwapTrim.forward,EndpointSwapTrim.inverse,gateSlots_append,
    gateSlots_cons,gateSlots_nil,instructionSlots] at a z ⊢
  omega

theorem penultimateCell_gateSlots_le (divide : Bool) :
    gateSlots (PenultimateSwapIdentity.cell divide) ≤ 27000 := by
  have bound (unit : Bool × Bool) : gateSlots
      (if divide then EndpointSwapTrim.forward id 2400 510 2409 unit.1
        else EndpointSwapTrim.inverse id 2400 510 2409 unit.1) ≤ 27000 := by
    have h := endpointCell_gateSlots_le id 2400 510 2409 unit.1
    cases divide
    · exact h.2
    · exact h.1
  simpa only [PenultimateSwapIdentity.cell] using bound (mixedTranscriptUnitTrace.getD 510 (false,false))

theorem converterPair_gateSlots_le (canonical : Bool) :
    gateSlots (MappedCompressed.converterPair canonical) ≤ 24000 := by
  have a := balancedConvert_gateSlots_le (balancedSharedTargetConvert id) (balancedSharedTargetConvert_widths id)
  have b := balancedConvert_gateSlots_le (balancedSharedSourceConvert id) (balancedSharedSourceConvert_widths id)
  cases canonical <;> simp only [MappedCompressed.converterPair,Bool.false_eq_true,↓reduceIte,
    gateSlots_append] <;> omega

theorem fieldSegment_gateSlots_le (divide : Bool) :
    gateSlots (MappedCompressed.selectedFieldSegment divide) ≤ 14100000 := by
  have g := mappedGroups_gateSlots_le divide 1 169
  have f := firstGroup_gateSlots_le divide
  have p := penultimateCell_gateSlots_le divide
  have a := converterPair_gateSlots_le false
  have b := converterPair_gateSlots_le true
  have hcopy : gateSlots (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a) ≤ 257 := by
    rw [copyRegister_gateSlots]
    have hl : (skywalkSharedField id).z.length = 257 := by simp only [ModInPlaceLayout.z,ModAddCoreLayout.z,skywalkSharedField,List.length_append,List.length_singleton,wireBlock_length]
    rw [hl]; omega
  have replayEq (A B C : Program) (d : Bool) :
      gateSlots (if d then A++B++C else C++B++A) = gateSlots A+gateSlots B+gateSlots C := by
    cases d <;> simp only [Bool.false_eq_true,↓reduceIte,gateSlots_append]
    omega
  have rep : gateSlots (PenultimateMapped.replay divide) ≤ 13941000 := by
    rw [PenultimateMapped.replay, replayEq,rename_gateSlots]
    omega
  have segmentEq (P Q R S : Program) (d : Bool) :
      gateSlots ((if d then [] else P)++Q++R++S++(if d then P else [])) =
        gateSlots P+gateSlots Q+gateSlots R+gateSlots S := by
    cases d <;> simp only [Bool.false_eq_true,↓reduceIte,gateSlots_append,gateSlots_nil] <;> omega
  rw [MappedCompressed.selectedFieldSegment,PenultimateMapped.fieldSegment,segmentEq,
    rename_gateSlots,rename_gateSlots,rename_gateSlots]
  omega

end ECDSAAdd.Baselines
end

-- source: ECDSAAdd/Baselines/SlotCompressed.lean
noncomputable section

namespace ECDSAAdd.Baselines
open Arithmetic Challenge MappedCompressed
attribute [local irreducible] renameProgram MappedCompressed.controlled NativeFirstDirect.forward NativeFirstKnown.inverse
  compressedCompactForward compressedCompactReverse MappedCompressed.selectedFieldSegment
  MappedCompressed.kernel ZeroSeededConstantCompare.program maskedConstant

theorem zeroCompare_gateSlots_le (xs cs : List Wire) (c t : Wire) :
    gateSlots (ZeroSeededConstantCompare.program xs cs c t) ≤ 18*xs.length+4 := by
  cases xs with
  | nil => simp [ZeroSeededConstantCompare.program]
  | cons x xs =>
    cases xs with
    | nil => simp [ZeroSeededConstantCompare.program,ZeroSeededConstantCompare.prepare,gateSlots_cons,instructionSlots]
    | cons y ys =>
      cases cs with
      | nil => simp [ZeroSeededConstantCompare.program]
      | cons d ds =>
        have h := compareConstant_gateSlots_le (y::ys) ds d t 0
        simp only [ZeroSeededConstantCompare.program,ZeroSeededConstantCompare.prepare,
          ZeroSeededConstantCompare.release,gateSlots_append,gateSlots_cons,gateSlots_nil,
          instructionSlots,List.length_cons] at *; omega

theorem compressedKernel_gateSlots_le (divide : Bool) :
    gateSlots (MappedCompressed.kernel divide) ≤ 20500000 := by
  have hn := nativeFirst_gateSlots_le MappedCompressed.base
  have hi := compactLoops_gateSlots_le MappedCompressed.base 1 511 (by omega)
  have hf := fieldSegment_gateSlots_le divide
  have hc : gateSlots (skywalkArithmeticClear MappedCompressed.base) = 3 := rfl
  rw [MappedCompressed.kernel]
  simp only [gateSlots_append, hc]
  omega

theorem compressedControlled_gateSlots_le (divide : Bool) :
    gateSlots (MappedCompressed.controlled divide) ≤ 20600000 := by
  have hk := compressedKernel_gateSlots_le divide
  have hz := zeroCompare_gateSlots_le (wireBlock MappedCompressed.base 770 256)
    (wireBlock MappedCompressed.base 0 255) (MappedCompressed.base 2313) (MappedCompressed.base 2411)
  have hm := maskedConstant_gateSlots_le (MappedCompressed.base 2411) (wireBlock MappedCompressed.base 770 256) 1
  simp only [wireBlock_length] at hz hm
  simp only [MappedCompressed.controlled,directZeroControlled,directZeroDivisorEnter,directZeroDivisorLeave,
    gateSlots_append]; omega

theorem pointCompressedArithmetic_gateSlots_le (L : ControlledPointLayout) (multiply : Bool) :
    gateSlots (pointCompressedArithmetic L multiply) ≤ 20600000 := by
  simpa only [pointCompressedArithmetic,rename_gateSlots] using compressedControlled_gateSlots_le (!multiply)

end ECDSAAdd.Baselines
end

-- source: ECDSAAdd/Baselines/SlotRecovery.lean
noncomputable section

namespace ECDSAAdd.Baselines
open Arithmetic Challenge Secp256k1

theorem recoveryConstant_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths)
    (r : List Wire) (hr : r.length = 256) (k : Fp) :
    gateSlots (pointDialogConstantAdd L r k) ≤ 18000 := by
  have hl := L.recoveryConstant_widths hw r hr
  have hp := canonicalMod_gateSlots_le (L.recoveryConstant r) 256 SquareReduction.c p hl
  have hm := maskedConstant_gateSlots_le L.core.generic (L.recoveryConstant r).src k.val
  rw [hl.src] at hm
  simp only [pointDialogConstantAdd, pointRecoveryConstantAdd, compactRecoveryConstant, gateSlots_append]
  omega

theorem recoveryReflection_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths) :
    gateSlots (pointRecoveryReflection L) ≤ 4608 := by
  have hm := maskedConstant_gateSlots_le L.core.generic L.recoveryNegate.word (2^L.recoveryNegate.word.length-1)
  have ha := mappedConst_gateSlots_le (some L.core.generic) L.recoveryNegate.word L.recoveryNegate.carries L.recoveryNegate.cin p
  have hl : L.recoveryNegate.word.length = 256 := hw.inputX
  rw [hl] at hm ha
  simp only [pointRecoveryReflection, CompactRecoveryNegateLayout.reflection,
    CompactRecoveryNegateLayout.complement, CompactRecoveryNegateLayout.add, gateSlots_append]
  -- The exponent is only a classical mask argument and has already been bounded.
  rw [hl]
  omega

theorem recoveryStage_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    gateSlots (pointRecoveryStage L cx cy) ≤ 40608 := by
  have hr := recoveryReflection_gateSlots_le L hw
  have hx := recoveryConstant_gateSlots_le L hw L.point.x hw.inputX (cx+1)
  have hy := recoveryConstant_gateSlots_le L hw L.point.y hw.inputY (-cy)
  simp only [pointRecoveryStage, gateSlots_append]; omega

end ECDSAAdd.Baselines
end

-- source: ECDSAAdd/Baselines/SlotStreamedSquare.lean
noncomputable section

namespace ECDSAAdd.Baselines
open Arithmetic Challenge

theorem cuccaroAdd_gateSlots_le (xs ys : List Wire) (c : Wire) :
    gateSlots (cuccaroAdd xs ys c) ≤ 6*xs.length := by
  induction xs, ys, c using cuccaroAdd.induct with
  | case1 c => simp [cuccaroAdd]
  | case2 a b c => simp [cuccaroAdd, gateSlots_cons, instructionSlots]
  | case3 a a' xs b b' ys c ih =>
    simp only [List.length_cons] at ih
    simp only [cuccaroAdd, gateSlots_append, cuccaroMaj, cuccaroUma, gateSlots_cons,
      gateSlots_nil, instructionSlots, List.length_cons]; omega
  | case4 xs ys c h => simp [cuccaroAdd]

theorem streamedFrames_gateSlots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    gateSlots L.normalizeSource ≤ 8961 ∧ gateSlots L.restoreSource ≤ 8961 ∧
    gateSlots L.reflectOutput ≤ 4608 := by
  have hc := compareConstant_gateSlots_le L.core.work L.shortCarry L.core.cin L.core.normFlag SquareReduction.p
  have hm k := mappedConst_gateSlots_le (some L.core.normFlag) L.core.work L.shortCarry L.core.cin k
  have h1 := hm SquareReduction.c
  have h2 := hm SquareReduction.p
  have h3 := mappedConst_gateSlots_le none L.core.out L.shortCarry L.core.cin SquareReduction.p
  rw [hw.core.work] at hc h1 h2
  rw [hw.core.out] at h3
  simp only [CuccaroStreamedSquareWideLayout.normalizeSource, CuccaroStreamedSquareWideLayout.restoreSource,
    CuccaroStreamedSquareWideLayout.reflectOutput, compareConstantGe, gateSlots_append,
    notRegister_gateSlots, hw.core.out, gateSlots_cons, gateSlots_nil, instructionSlots]
  omega

theorem measuredFold_gateSlots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (f : MeasuredSquareFold) :
    gateSlots (L.measuredFold f) ≤ 36000 := by
  have hf := streamedFrames_gateSlots_le L hw
  have hc := canonicalMod_gateSlots_le L.measuredCore 256 SquareReduction.c SquareReduction.p (L.measuredCore_widths hw)
  have hd : (L.foldDestination f).length ≤ 256 := by
    simp only [CuccaroStreamedSquareWideLayout.foldDestination, List.length_take, List.length_drop, hw.core.work]; omega
  have hcopy := Nat.min_le_right f.src.length (L.foldDestination f).length
  simp only [CuccaroStreamedSquareWideLayout.measuredFold, gateSlots_append, copyRegister_gateSlots]
  cases f.canonical <;> simp only [Bool.false_eq_true, ↓reduceIte, gateSlots_nil] <;> omega

theorem measuredFolds_gateSlots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (orientation : Bool) (fs : List MeasuredSquareFold) :
    gateSlots (L.measuredFolds orientation fs) ≤ fs.length*41000 := by
  induction fs generalizing orientation with
  | nil => simp only [CuccaroStreamedSquareWideLayout.measuredFolds, gateSlots_nil, List.length_nil, Nat.zero_mul, Nat.le_refl]
  | cons f fs ih =>
    have h := measuredFold_gateSlots_le L hw f
    have hr := (streamedFrames_gateSlots_le L hw).2.2
    have ht := ih f.negative
    simp only [CuccaroStreamedSquareWideLayout.measuredFolds, gateSlots_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    by_cases he : orientation = f.negative
    · simp only [he, ↓reduceIte, gateSlots_nil]; omega
    · simp only [he, ↓reduceIte]; omega

theorem withMeasuredSquare_gateSlots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (src dst : List Wire) (body : Program) (hd : dst.length ≤ 258) :
    gateSlots (L.withMeasuredSquare control src dst body) ≤ 820000 + gateSlots body := by
  have hs := mappedSigned_gateSlots_le (L.inputBank.take src.length) dst L.leafPad L.leafCarry L.core.cin
  have hl : (L.inputBank.take src.length).length ≤ 129 := by
    simp only [CuccaroStreamedSquareWideLayout.inputBank, List.length_take, hw.core.work]; omega
  have hcopy := Nat.min_le_right src.length (L.inputBank.take src.length).length
  have hb : (L.inputBank.take src.length).length * (12*((L.inputBank.take src.length).length+1)+6*dst.length) ≤ 400932 := by
    nlinarith
  simp only [CuccaroStreamedSquareWideLayout.withMeasuredSquare, gateSlots_append,
    copyRegister_gateSlots, eraseMask_gateSlots]
  omega

theorem measuredProgram_gateSlots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) : gateSlots (L.measuredProgram control) ≤ 5000000 := by
  have ha := measuredFolds_gateSlots_le L hw false L.measuredAItems
  have hb := measuredFolds_gateSlots_le L hw false L.measuredBItems
  have hc := measuredFolds_gateSlots_le L hw true L.measuredCItems
  have la : L.measuredAItems.length = 6 := by rfl
  have lb : L.measuredBItems.length = 26 := by rfl
  have lc : L.measuredCItems.length = 6 := by rfl
  rw [la] at ha
  rw [lb] at hb
  rw [lc] at hc
  have hd : (L.core.product.take 256).length ≤ 258 := by
    simp only [List.length_take]; omega
  have a := withMeasuredSquare_gateSlots_le L hw control L.core.low _
    (L.measuredFolds false L.measuredAItems) hd
  have b := withMeasuredSquare_gateSlots_le L hw control L.core.high _
    (L.measuredFolds false L.measuredBItems) hd
  have c := withMeasuredSquare_gateSlots_le L hw control L.core.sum L.core.product
    (L.measuredFolds true L.measuredCItems) (by rw [hw.core.product])
  have hp := cuccaroAdd_gateSlots_le (L.core.low++[L.core.pad.getD 0 0]) L.core.sum L.core.cin
  have hl := L.core.low_length hw.core
  simp only [List.length_append, List.length_cons, List.length_nil, hl] at hp
  change gateSlots L.core.prepareSum ≤ _ at hp
  have hr := (streamedFrames_gateSlots_le L hw).2.2
  simp only [CuccaroStreamedSquareWideLayout.measuredProgram,
    CuccaroStreamedSquareWideLayout.measuredBranchA,
    CuccaroStreamedSquareWideLayout.measuredBranchB,
    CuccaroStreamedSquareWideLayout.measuredBranchC,
    CuccaroStreamedSquareLayout.clearSum, gateSlots_append, reverse_gateSlots]
  omega

end ECDSAAdd.Baselines
end

-- source: ECDSAAdd/Baselines/SlotModular.lean
noncomputable section

namespace ECDSAAdd.Baselines
open Arithmetic Challenge

theorem controlledMod_gateSlots_le (c : Wire) (L : ModInPlaceLayout) (n p : Nat)
    (hw : L.Widths n) :
    gateSlots (controlledModAdd c L p) ≤ 56*n+35 ∧
    gateSlots (controlledModSub c L p) ≤ 86*n+65 := by
  have hm := modAddCore_gateSlots_le L.maskedCore p
  change gateSlots (modAddCore L.maskedCore p) ≤
    14 * L.mask.length + 14 * L.constant.length + 26 * L.low.length + 7 at hm
  rw [hw.mask, hw.core.constant, hw.core.low] at hm
  have hn := negRaw_gateSlots_le L p
  rw [hw.core.a, hw.core.constant] at hn
  have hc : gateSlots (copyRegister (some c) (L.a.take L.low.length) (L.mask.take L.low.length)) = n := by
    simp [hw.core.a, hw.core.low, hw.mask]
  have ha : gateSlots (controlledModAdd c L p) ≤ 56*n+35 := by
    simp only [controlledModAdd, gateSlots_append, hc]; omega
  refine ⟨ha, ?_⟩
  simp only [controlledModSub, gateSlots_append]; omega

theorem controlledUnary_gateSlots_le (c : Wire) (U : ModUnaryLayout) (n p : Nat)
    (hw : U.Widths n) :
    gateSlots (controlledHalf c U p) ≤ 31*n+20 ∧
    gateSlots (controlledDouble c U p) ≤ 33*n+21 := by
  have hz : U.z.length = n+1 := by simp [ModUnaryLayout.z, hw.low]
  have hm := maskedConst_gateSlots_le U.flag U.constant U.z U.carry U.cin p
  have hm' := maskedConst_gateSlots_le c U.constant U.z U.carry U.cin p
  have hl := (maskedConst_gateSlots_le U.high (U.constant.take U.low.length) U.low
    (U.carry.take (U.low.length-1)) U.cin p).1
  have hs := shift_gateSlots c U.z
  have hc := compareLtConst_gateSlots_le (some c) U.low (U.constant.take U.low.length) U.carry U.cin U.flag ((p+1)/2)
  rw [hw.constant, hz] at hm hm'
  rw [hz] at hs
  simp only [List.length_take, hw.constant, hw.low, Nat.min_eq_left (Nat.le_succ n)] at hl hc
  simp only [controlledHalf, controlledDouble, gateSlots_append, gateSlots_cons, gateSlots_nil, instructionSlots, hw.low]
  constructor <;> omega

theorem replayCell_gateSlots_le (a sw su : Wire) (L : ModInPlaceLayout) (n p : Nat)
    (hw : L.Widths n) :
    gateSlots (replayCell a sw su L p) ≤ 123*n+85 ∧
    gateSlots (replayUncell a sw su L p) ≤ 95*n+56 := by
  have hm := controlledMod_gateSlots_le su L n p hw
  have hu := controlledUnary_gateSlots_le a L.unary n p (L.unary_widths n hw)
  have hz : L.z.length = n+1 := by simp [ModInPlaceLayout.z, ModAddCoreLayout.z, hw.core.low]
  have hs : gateSlots (swapRegisters sw (L.z.take L.low.length) (L.a.take L.low.length)) = 3*n := by
    simp [hw.core.low, hw.core.a, hz]
  simp only [replayCell, replayUncell, gateSlots_append, hs]
  constructor <;> omega

end ECDSAAdd.Baselines
end

-- source: ECDSAAdd/Baselines/SlotRounds.lean
noncomputable section

namespace ECDSAAdd.Baselines
open Arithmetic Challenge

theorem counter_gateSlots (L : AdderLayout) :
    gateSlots (counterInc L) = 28 * L.width + 2 ∧
    gateSlots (counterDec L) = 28 * L.width + 2 := by
  have hd (A : AdderLayout) : gateSlots (counterDecXor A) = 15 * A.width + 2 := by
    change gateSlots (notRegister (A.cin :: A.y) ++ add A ++ notRegister (A.cin :: A.y)) = _
    simp [add, AdderLayout.width, AdderLayout.y]; omega
  simp [counterInc, counterDec, counterIncXor, hd, add, AdderLayout.swapCounter, AdderLayout.width]
  omega

theorem counterActive_gateSlots_le (L : AdderLayout) (t i : Nat) :
    gateSlots (counterActiveXor L t i) ≤ 14 * L.width + 5 := by
  have h := compareLtConst_gateSlots_le none L.x L.y L.carry L.cin t (i+1)
  have hx : L.x.length = L.width := by simp [AdderLayout.x, AdderLayout.width]
  have hy : L.y.length = L.width := by simp [AdderLayout.y, AdderLayout.width]
  rw [hx, hy] at h
  simp only [counterActiveXor, gateSlots_append, gateSlots_cons, gateSlots_nil, instructionSlots]
  omega

theorem valueBody_gateSlots_le (L : RoundDataLayout) (a sw su : Wire) :
    gateSlots (valueBodyProgram L a sw su) ≤ 26 * L.width ∧
    gateSlots (valueUnbodyProgram L a sw su) ≤ 26 * L.width := by
  have hm := measuredMasked_gateSlots_le su (L.reg .v) (L.reg .y) (L.reg .u)
    ((L.reg .carry).take (L.width-1)) L.cin
  simp only [L.reg_length] at hm
  have hs := shift_gateSlots a L.u
  simp only [RoundDataLayout.u, L.reg_length] at hs
  simp only [valueBodyProgram, valueUnbodyProgram, inplaceArithmetic, ↓reduceIte,
    Bool.false_eq_true, gateSlots_append, swapRegisters_gateSlots,
    RoundDataLayout.u, RoundDataLayout.v, L.reg_length, Nat.min_self]
  constructor <;> omega

theorem recordRound_gateSlots_le (L : KaliskiRoundLayout) :
    gateSlots (recordRound L) ≤ 12 * L.data.width + 10 := by
  have h := compareLt_gateSlots_le (some L.bothWork) L.v L.u (L.data.reg .carry) L.cin L.swap
  have hu : L.u.length = L.data.width := L.data.reg_length .u
  have hv : L.v.length = L.data.width := L.data.reg_length .v
  rw [hu, hv] at h
  simp only [recordRound, gateSlots_append, gateSlots_cons, gateSlots_nil, instructionSlots]
  omega

theorem valueRound_gateSlots_le (L : KaliskiRoundLayout) (i : Nat) :
    gateSlots (valueRound L i) ≤ 45 * L.data.width + 42 * L.counter.width + 20 ∧
    gateSlots (valueUnround L i) ≤ 45 * L.data.width + 42 * L.counter.width + 20 := by
  have hb := valueBody_gateSlots_le L.data L.active L.swap L.subtract
  have hr := recordRound_gateSlots_le L
  have hc := counter_gateSlots L.counter
  have hd := counter_gateSlots L.counter.swapCounter
  have ha := counterActive_gateSlots_le L.comparator L.active i
  rw [L.comparator_fields.2.2.2.2.2] at ha
  rw [L.counter.swapCounter_fields.2.2.2.2.2] at hd
  have hz := zeroControlled_gateSlots L.active L.done (L.data.zeroBits .v)
  have hzl : (L.data.zeroBits .v).length = L.data.width := by simp [RoundDataLayout.zeroBits, RoundDataLayout.width]
  rw [hzl] at hz
  simp only [valueRound, valueUnround, roundActiveXor, gateSlots_append,
    loadActive, gateSlots_cons, gateSlots_nil, instructionSlots]
  constructor <;> omega

theorem valueLoop_gateSlots_le (L : KaliskiRoundLayout) (i : Nat) (rs : List RoundRecord)
    (hw : 2 ≤ L.data.width) :
    gateSlots (valueLoop L i rs) ≤ rs.length * (45 * L.data.width + 42 * L.counter.width + 20) ∧
    gateSlots (valueUnloop L i rs) ≤ rs.length * (45 * L.data.width + 42 * L.counter.width + 20) := by
  induction rs generalizing L i with
  | nil => simp [valueLoop, valueUnloop]
  | cons r rs ih =>
    have hd : L.swapCounter.data = L.data := rfl
    have hc : L.swapCounter.counter.width = L.counter.width := by
      simp [KaliskiRoundLayout.swapCounter, KaliskiRoundLayout.counter, AdderLayout.width]
    have ht := ih L.swapCounter (i+1) (by simpa [hd] using hw)
    rw [hd, hc] at ht
    have hv := valueWidth_bounds L.data.width i hw
    have hb := valueRound_gateSlots_le ((L.withRecord r).narrow (valueWidth L.data.width i)) i
    have hnw : ((L.withRecord r).narrow (valueWidth L.data.width i)).data.width = valueWidth L.data.width i :=
      (L.withRecord r).narrow_width _ (by omega) hv.2
    have hnc : ((L.withRecord r).narrow (valueWidth L.data.width i)).counter = L.counter := rfl
    rw [hnw, hnc] at hb
    simp only [valueLoop, valueUnloop, gateSlots_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    constructor <;> omega

end ECDSAAdd.Baselines
end

-- source: ECDSAAdd/Baselines/SlotDialog.lean
noncomputable section

namespace ECDSAAdd.Baselines
open Arithmetic Challenge

theorem replayLoop_gateSlots_le (L : ReplayLayout) (n p i : Nat) (rs : List RoundRecord)
    (hw : L.payload.Widths n) (hc : L.counter.width = 10) :
    gateSlots (replayLoop L p i rs) ≤ rs.length * (123*n+375) ∧
    gateSlots (replayUnloop L p i rs) ≤ rs.length * (95*n+346) := by
  induction rs generalizing i with
  | nil => simp [replayLoop, replayUnloop]
  | cons r rs ih =>
    have hm := replayCell_gateSlots_le L.active r.swap r.subtract L.payload n p hw
    have ha := counterActive_gateSlots_le L.counter L.active i
    rw [hc] at ha
    have ht := ih (i+1)
    simp only [replayLoop, replayUnloop, replayRound, replayUnround, gateSlots_append,
      List.length_cons, Nat.add_mul, Nat.one_mul]
    constructor <;> omega

theorem dialogLoad_gateSlots_le (L : DialogLayout) (p : Nat) (hw : L.Widths) :
    gateSlots (dialogLoad L p) ≤ 515 := by
  have hu : L.first.u.length = 257 := by
    simp [KaliskiRoundLayout.u, RoundDataLayout.u, KaliskiRoundLayout.data, RoundDataLayout.reg, hw.low]
  have hx : L.x.length = 256 := by simp [DialogLayout.x, hw.low]
  have h := xorConstant_gateSlots_le L.first.u p
  rw [hu] at h
  unfold dialogLoad
  split
  · simpa using h.trans (by omega : 257 ≤ 515)
  · simp only [gateSlots_append, safeDivisor, gateSlots_cons, instructionSlots,
      gateSlots_nil, copyRegister_gateSlots, hx]
    have hm := Nat.min_le_left 256 (1 + List.length ‹List Wire›)
    omega

theorem dialog_gateSlots_le (L : DialogLayout) (p : Nat) (hw : L.Widths) :
    gateSlots (dialogDivide L p) ≤ 29000000 ∧
    gateSlots (dialogMultiply L p) ≤ 25000000 := by
  have hd : L.first.data.width = 257 := by
    simp [KaliskiRoundLayout.data, RoundDataLayout.width, hw.low]
  have hv := valueLoop_gateSlots_le L.first 0 L.records (by omega)
  rw [hd, hw.counter, hw.records] at hv
  have hc : L.replay.counter.width = 10 := by
    exact hw.counter
  have hr := replayLoop_gateSlots_le L.replay 256 p 0 L.records (L.payload_widths hw) hc
  rw [hw.records] at hr
  have hl := dialogLoad_gateSlots_le L p hw
  have hy : L.y.length = 257 := by
    change (L.first.data.reg .s).length = 257
    rw [L.first.data.reg_length, hd]
  have hz : L.z.length = 257 := by
    change (L.first.data.reg .out).length = 257
    rw [L.first.data.reg_length, hd]
  simp only [dialogDivide, dialogMultiply, gateSlots_append, exchangeRegisters_gateSlots, hy, hz]
  constructor <;> omega

end ECDSAAdd.Baselines
end

-- source: ECDSAAdd/Baselines/SlotSquare.lean
noncomputable section

namespace ECDSAAdd.Baselines
open Arithmetic Challenge

theorem squareRow_gateSlots_le (sub : Bool) (c : Wire) (xs pad mask dst carry : List Wire) (cin : Wire) :
    gateSlots (squareRow sub c xs pad mask dst carry cin) ≤ 15*mask.length + 2*dst.length := by
  have h := measuredMasked_gateSlots_le c (xs ++ pad.take xs.length) (mask.take (2*xs.length)) dst
    (carry.take (2*xs.length-1)) cin
  have hm : (mask.take (2*xs.length)).length ≤ mask.length := by simp only [List.length_take]; exact Nat.min_le_right _ _
  cases sub <;> simp only [squareRow, Bool.false_eq_true, ↓reduceIte] <;> omega

theorem triangular_gateSlots_le (xs dst pad mask carry : List Wire) (cin : Wire) :
    gateSlots (triangularSquare xs dst pad mask carry cin) ≤ xs.length*(15*mask.length+2*dst.length+1) ∧
    gateSlots (triangularSquareClear xs dst pad mask carry cin) ≤ xs.length*(15*mask.length+2*dst.length+1) := by
  induction xs generalizing dst with
  | nil => simp [triangularSquare, triangularSquareClear]
  | cons c xs ih =>
    cases dst with
    | nil => simp [triangularSquare, triangularSquareClear]
    | cons a ds =>
      cases ds with
      | nil => simp [triangularSquare, triangularSquareClear]
      | cons b dst =>
        have ht := ih dst
        have hf := squareRow_gateSlots_le false c xs pad mask dst carry cin
        have hr := squareRow_gateSlots_le true c xs pad mask dst carry cin
        simp only [triangularSquare, triangularSquareClear, gateSlots_append,
          gateSlots_cons, gateSlots_nil, instructionSlots, List.length_cons]
        by_cases he : xs = []
        · subst xs; simp [triangularSquare, triangularSquareClear]
        · simp only [he, ↓reduceIte]
          constructor <;> nlinarith [ht.1, ht.2]

theorem karatsuba_gateSlots_le (L : KaratsubaSquareLayout) (hw : L.Valid) :
    gateSlots (karatsubaSquare L) ≤ 3000000 ∧ gateSlots (karatsubaSquareClear L) ≤ 3000000 := by
  have hlow := triangular_gateSlots_le L.low L.a L.pad L.mask L.carry L.cin
  have hhigh := triangular_gateSlots_le L.high L.d L.pad L.mask L.carry L.cin
  have hsum := triangular_gateSlots_le L.sum L.c L.pad L.mask L.carry L.cin
  have hprep := addInPlace_gateSlots_le (L.high++L.pad.take 1) L.sum (L.carry.take 128) L.cin
  have hclear := subInPlace_gateSlots_le (L.high++L.pad.take 1) L.sum (L.carry.take 128) L.cin
  have hadda := addInPlace_gateSlots_le (L.a++L.pad) (L.z.drop 128) L.carry L.cin
  have hsuba := subInPlace_gateSlots_le (L.a++L.pad) (L.z.drop 128) L.carry L.cin
  have haddd := addInPlace_gateSlots_le (L.d++L.pad) (L.z.drop 128) L.carry L.cin
  have hsubd := subInPlace_gateSlots_le (L.d++L.pad) (L.z.drop 128) L.carry L.cin
  have haddc := addInPlace_gateSlots_le (L.c++L.pad.take 126) (L.z.drop 128) L.carry L.cin
  have hsubc := subInPlace_gateSlots_le (L.c++L.pad.take 126) (L.z.drop 128) L.carry L.cin
  simp only [List.length_append, List.length_take, List.length_drop,
    hw.low_length, hw.high_length, hw.a_length, hw.d_length, hw.c_length,
    hw.z_length, hw.sum_length, hw.pad_length, hw.mask_length] at *
  simp only [karatsubaSquare, karatsubaSquareClear, KaratsubaSquareLayout.squareLow,
    KaratsubaSquareLayout.squareHigh, KaratsubaSquareLayout.squareSum, KaratsubaSquareLayout.clearLow,
    KaratsubaSquareLayout.clearHigh, KaratsubaSquareLayout.clearSquareSum,
    KaratsubaSquareLayout.prepareSum, KaratsubaSquareLayout.clearSum, KaratsubaSquareLayout.copySquares,
    KaratsubaSquareLayout.combine, KaratsubaSquareLayout.uncombine, gateSlots_append, copyRegister_gateSlots,
    List.length_take, List.length_drop, hw.low_length, hw.a_length, hw.d_length, hw.z_length, hw.sum_length]
  constructor <;> omega

theorem squareFold_gateSlots_le (src dst pad carry : List Wire) (cin : Wire) (js : List Nat) :
    gateSlots (squareFoldAdd src dst pad carry cin js) ≤ js.length*(12*(src.length+2*pad.length)+2*dst.length) ∧
    gateSlots (squareFoldClear src dst pad carry cin js) ≤ js.length*(12*(src.length+2*pad.length)+2*dst.length) := by
  induction js with
  | nil => simp [squareFoldAdd, squareFoldClear]
  | cons j js ih =>
    have hl : (shiftedSource src pad j dst.length).length ≤ src.length + 2*pad.length := by
      simp only [shiftedSource, List.length_append, List.length_take, List.length_drop]; omega
    have ha := addInPlace_gateSlots_le (shiftedSource src pad j dst.length) dst (carry.take (dst.length-1)) cin
    have hs := subInPlace_gateSlots_le (shiftedSource src pad j dst.length) dst (carry.take (dst.length-1)) cin
    simp only [squareFoldAdd, squareFoldClear, gateSlots_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    constructor <;> omega

theorem squareReduce_gateSlots_le (L : SquareReduceLayout) (hw : L.Widths) :
    gateSlots (squareReduce L) ≤ 200000 ∧ gateSlots (squareReduceClear L) ≤ 200000 := by
  have hv : L.value.length = 256 := by simp [SquareReduceLayout.value, hw.r]
  have hq : L.quotient.length = 33 := by simp [SquareReduceLayout.quotient, hw.r]
  have he : L.extended.length = 257 := by simp [SquareReduceLayout.extended, hv]
  have hf := squareFold_gateSlots_le L.high L.r L.pad L.carry L.cin squareFoldShifts
  have hg := squareFold_gateSlots_le L.quotient L.extended L.pad L.carry L.cin squareFoldShifts
  have hb := maskedConst_gateSlots_le L.b L.mask L.value (L.carry.take 255) L.cin SquareReduction.c
  have hn := maskedConst_gateSlots_le L.flag L.mask L.value (L.carry.take 255) L.cin SquareReduction.p
  have hc := compareLtConst_gateSlots_le none L.value L.mask (L.carry.take 256) L.cin L.flag SquareReduction.p
  have hlen : squareFoldShifts.length = 7 := rfl
  rw [hlen, hw.high, hw.r, hw.pad] at hf
  rw [hlen, hq, he, hw.pad] at hg
  rw [hw.mask, hv] at hb hn
  rw [hv, hw.mask] at hc
  simp only [squareReduce, squareReduceClear, squareNormalize, squareDenormalize,
    gateSlots_append, copyRegister_gateSlots, hw.low, hv, gateSlots_cons, gateSlots_nil, instructionSlots]
  constructor <;> omega

theorem squareSub_gateSlots_le (L : SquareSubLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    gateSlots (squareSub L) ≤ 6500000 := by
  have hi := karatsuba_gateSlots_le L.integer (L.integer_valid hw hn)
  have hr := squareReduce_gateSlots_le L.reduction (L.reduction_widths hw)
  have hw' := L.output_widths hw
  have ha := modAddCore_gateSlots_le L.output.toModAddCoreLayout SquareReduction.p
  have hb := negRaw_gateSlots_le L.output SquareReduction.p
  rw [hw'.core.a, hw'.core.constant, hw'.core.low] at ha
  rw [hw'.core.a, hw'.core.constant] at hb
  simp only [squareSub, modSubInPlace, modAddInPlace, gateSlots_append]
  omega

end ECDSAAdd.Baselines
end

-- source: ECDSAAdd/Baselines/ValueWalkSlots.lean
noncomputable section

namespace ECDSAAdd.Baselines
open Arithmetic Challenge Secp256k1

theorem valueWalkConstant_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths)
    (r : List Wire) (hr : r.length = 256) (k : Fp) :
    gateSlots (valueWalkPointDialogConstantAdd L r k) ≤ 14500 := by
  have hl := L.dialogUnary_widths hw r hr
  have ha := modAddCore_gateSlots_le (L.dialogUnary r).toModAddCoreLayout p
  have hm := maskedConstant_gateSlots_le L.core.generic (L.dialogUnary r).a k.val
  rw [hl.core.a, hl.core.constant, hl.core.low] at ha
  rw [hl.core.a] at hm
  simp only [valueWalkPointDialogConstantAdd, modAddInPlace, gateSlots_append]; omega

theorem valueWalkNegate_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths) :
    gateSlots (valueWalkPointDialogNegate L) ≤ 38000 := by
  have hl := L.dialogNegate_widths hw
  have hm := controlledMod_gateSlots_le L.core.generic L.dialogNegate 256 p hl
  simp only [valueWalkPointDialogNegate, gateSlots_append, swapRegisters_gateSlots, hl.core.low]
  omega

theorem valueWalkSquare_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    gateSlots (valueWalkPointDialogSquare L) ≤ 6500512 := by
  have h := squareSub_gateSlots_le L.dialogSquare (L.dialogSquare_widths hw) (L.dialogSquare_nodup hw hn)
  simp only [valueWalkPointDialogSquare, gateSlots_append, copyRegister_gateSlots,
    List.length_take, L.dialogPool_length hw]
  omega

theorem valueWalkGeneric_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : gateSlots (valueWalkPointDialogGeneric L cx cy) ≤ 60700000 := by
  have hx k := valueWalkConstant_gateSlots_le L hw L.point.x hw.inputX k
  have hy k := valueWalkConstant_gateSlots_le L hw L.point.y hw.inputY k
  have hd := dialog_gateSlots_le L.dialogPort p (DialogLayout.fromPool_widths _ _ _ _)
  have hs := valueWalkSquare_gateSlots_le L hw hn
  have hn' := valueWalkNegate_gateSlots_le L hw
  have h1 := hx (-cx); have h2 := hy (-cy); have h3 := hx (3*cx); have h4 := hx cx
  simp only [valueWalkPointDialogGeneric, gateSlots_append]
  omega

theorem maskedPoint_gateSlots_le (c : Wire) (r : PointReg) (C : Point) :
    gateSlots (maskedPointConstant c r C) ≤ 1 + r.x.length + r.y.length := by
  have hf := maskedConstant_gateSlots_le c [r.finite] (pointFinite C).toNat
  have hx := maskedConstant_gateSlots_le c r.x (pointX C)
  have hy := maskedConstant_gateSlots_le c r.y (pointY C)
  simp only [maskedPointConstant, gateSlots_append]
  simp only [List.length_cons, List.length_nil] at hf
  omega

theorem valueWalkFinite_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (cx cy : Fp) : gateSlots (valueWalkPointDialogFinite L C cx cy) ≤ 61000000 := by
  have hg := valueWalkGeneric_gateSlots_le L hw hn cx cy
  have hx : L.point.x.length = 256 := hw.inputX
  have hy : L.point.y.length = 256 := hw.inputY
  have hpl : (PointAddLayout.pointWires L.point).length = 513 := by
    simp [PointAddLayout.pointWires, hx, hy]
  have hzl : L.dialogPointZero.length = 513 := by
    have he := (zeroPorts_maps (PointAddLayout.pointWires L.point) (L.dialogPool.take 513)
      (by simp only [List.length_take,L.dialogPool_length hw]; exact hpl)).1
    simpa only [List.length_map,hpl] using congrArg List.length he
  have hz c t k : gateSlots (equalConstant c t L.dialogPointZero k) ≤ 4618 := by
    have h := equalConstant_gateSlots_le c t L.dialogPointZero k
    rw [hzl] at h; exact h
  have hm c P : gateSlots (maskedPointConstant c L.point P) ≤ 513 := by
    have h := maskedPoint_gateSlots_le c L.point P
    rw [hx,hy] at h; exact h
  have he : gateSlots (pointInPlaceDoubleEnable L cy) ≤ 1 := by
    unfold pointInPlaceDoubleEnable; split <;> simp [gateSlots_cons, instructionSlots]
  have hh : gateSlots (pointDialogExceptionEnable L C) ≤ 1 := by
    unfold pointDialogExceptionEnable; split <;> simp [gateSlots_cons, instructionSlots]
  have hf : gateSlots (pointDialogGenericFlag L) = 5 := rfl
  have z1 := hz L.control L.infinitySelect (pointCode 0)
  have z2 := hz L.core.double L.doubleSelect (pointCode C)
  have z3 := hz L.control L.genericSelect (pointCode (-C))
  have z4 := hz L.core.equalX L.core.equalNegY (pointCode (dialogExceptionPoint C))
  have z5 := hz L.control L.infinitySelect (pointCode C)
  have z6 := hz L.core.double L.doubleSelect (pointCode (C+C))
  have z7 := hz L.control L.genericSelect (pointCode 0)
  have z8 := hz L.core.equalX L.core.equalNegY (pointCode (-C))
  have m1 := hm L.infinitySelect C
  have m2 := hm L.doubleSelect C
  have m3 := hm L.doubleSelect (C+C)
  have m4 := hm L.genericSelect (-C)
  have m5 := hm L.core.equalNegY (dialogExceptionPoint C)
  have m6 := hm L.core.equalNegY (-C)
  simp only [valueWalkPointDialogFinite, pointDialogCorners, pointInPlaceCorners, gateSlots_append, hf]
  omega

theorem normalizedValueWalk_gateSlots_le (C : Point) :
    gateSlots (normalizedValueWalk C) ≤ 61000000 := by
  rw [normalizedValueWalk, normalize_gateSlots]
  cases C with
  | zero => simp [valueWalk, Submissions.ValueWalk.program]
  | some hp => exact valueWalkFinite_gateSlots_le layout layout_widths layout_nodup _ _ _

end ECDSAAdd.Baselines
end

-- source: ECDSAAdd/Baselines/SkywalkSlots.lean
noncomputable section

namespace ECDSAAdd.Baselines
open Arithmetic Challenge Secp256k1 MappedCompressed

theorem skywalkSquare_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths) :
    gateSlots (CompressedPointSquare.computableProgram L) ≤ 5000000 := by
  simpa only [CompressedPointSquare.computableProgram,rename_gateSlots,pointMeasuredSquareCandidate]
    using measuredProgram_gateSlots_le L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw) L.core.generic

theorem skywalkGeneric_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths)
    (cx cy : Fp) : gateSlots (pointCompressedDialogGeneric L cx cy) ≤ 46300000 := by
  have a := recoveryConstant_gateSlots_le L hw L.point.x hw.inputX (-cx)
  have b := recoveryConstant_gateSlots_le L hw L.point.y hw.inputY (-cy)
  have c := recoveryConstant_gateSlots_le L hw L.point.x hw.inputX (3*cx)
  have d := pointCompressedArithmetic_gateSlots_le L false
  have e := pointCompressedArithmetic_gateSlots_le L true
  have f := skywalkSquare_gateSlots_le L hw
  have g := recoveryStage_gateSlots_le L hw cx cy
  simp only [pointCompressedDialogGeneric,gateSlots_append]; omega

theorem skywalkFinite_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths)
    (C : Point) (cx cy : Fp) : gateSlots (pointCompressedDialogFinite L C cx cy) ≤ 47000000 := by
  have hg := skywalkGeneric_gateSlots_le L hw cx cy
  have hx : L.point.x.length = 256 := hw.inputX
  have hy : L.point.y.length = 256 := hw.inputY
  have hpl : (PointAddLayout.pointWires L.point).length = 513 := by
    simp [PointAddLayout.pointWires, hx, hy]
  have hzl : L.dialogPointZero.length = 513 := by
    have he := (zeroPorts_maps (PointAddLayout.pointWires L.point) (L.dialogPool.take 513)
      (by simp only [List.length_take,L.dialogPool_length hw]; exact hpl)).1
    simpa only [List.length_map,hpl] using congrArg List.length he
  have hz c t k : gateSlots (equalConstant c t L.dialogPointZero k) ≤ 4618 := by
    have h := equalConstant_gateSlots_le c t L.dialogPointZero k
    rw [hzl] at h; exact h
  have hm c P : gateSlots (maskedPointConstant c L.point P) ≤ 513 := by
    have h := maskedPoint_gateSlots_le c L.point P
    rw [hx,hy] at h; exact h
  have he : gateSlots (pointInPlaceDoubleEnable L cy) ≤ 1 := by
    unfold pointInPlaceDoubleEnable; split <;> simp [gateSlots_cons, instructionSlots]
  have hh : gateSlots (pointDialogExceptionEnable L C) ≤ 1 := by
    unfold pointDialogExceptionEnable; split <;> simp [gateSlots_cons, instructionSlots]
  have hf : gateSlots (pointDialogGenericFlag L) = 5 := rfl
  have z1 := hz L.control L.infinitySelect (pointCode 0)
  have z2 := hz L.core.double L.doubleSelect (pointCode C)
  have z3 := hz L.control L.genericSelect (pointCode (-C))
  have z4 := hz L.core.equalX L.core.equalNegY (pointCode (dialogExceptionPoint C))
  have z5 := hz L.control L.infinitySelect (pointCode C)
  have z6 := hz L.core.double L.doubleSelect (pointCode (C+C))
  have z7 := hz L.control L.genericSelect (pointCode 0)
  have z8 := hz L.core.equalX L.core.equalNegY (pointCode (-C))
  have m1 := hm L.infinitySelect C
  have m2 := hm L.doubleSelect C
  have m3 := hm L.doubleSelect (C+C)
  have m4 := hm L.genericSelect (-C)
  have m5 := hm L.core.equalNegY (dialogExceptionPoint C)
  have m6 := hm L.core.equalNegY (-C)
  simp only [pointCompressedDialogFinite, pointDialogCorners, pointInPlaceCorners, gateSlots_append, hf]
  omega

theorem normalizedSkywalk_gateSlots_le (C : Point) :
    gateSlots (normalizedSkywalk C) ≤ 47000000 := by
  rw [normalizedSkywalk, normalize_gateSlots]
  cases C with
  | zero => simp [skywalk, Submissions.Skywalk.program, controlledPointAdd]
  | some hp => exact skywalkFinite_gateSlots_le layout layout_widths _ _ _

end ECDSAAdd.Baselines
end

-- source: ECDSAAdd/Submission/Entrant/ArithAvoid.lean
noncomputable section

/-! The mapped Skywalk arithmetic never touches the logical labels `2313` or
`2401`–`2408`.

The published support certificate for the arithmetic (`controlled_support`)
places it inside the full 1,899-label inventory.  The arithmetic's actual
gates come from the integer universe (labels below 1,798), from the field
sites (`fieldSite`) and from the history packets, all relocated by the
allocation permutations, which only move labels inside the work/hole region.
None of these is one of the labels above, so their physical images (the
auxiliary carry-in and eight classification/control metadata sites) are not
in the arithmetic's support. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed CompressedAllocation Secp256k1
attribute [local irreducible] wires OffsetBorrowedCanonical.cell OffsetBorrowedInverseCanonical.cell
attribute [local irreducible] compressedHistoryEncode compressedHistoryDecode
attribute [local irreducible] dblInPlace halfInPlace copyRegister
attribute [local irreducible] addInPlace subInPlace compareLt
attribute [local irreducible] compactSkywalkTick compactSkywalkReverseTick
attribute [local irreducible] literalSkywalkSeed literalSkywalkUnseed
  NativeFirstDirect.forward NativeFirstDirect.inverse NativeFirstKnown.inverse

/-- Logical labels avoided by the arithmetic. -/
def badIdx (q : Nat) : Prop := q = 2313 ∨ (2401 ≤ q ∧ q ≤ 2408)

/-- A physical wire that is not the image (under `base`) of a bad label. -/
def goodW (q : Wire) : Prop := ¬ (q = 2313 + 16 ∨ (2401 + 16 ≤ q ∧ q ≤ 2408 + 16))

def Avoid (P : Program) : Prop := ∀ q ∈ wires P, goodW q

theorem avoid_append {P Q : Program} : Avoid (P ++ Q) ↔ Avoid P ∧ Avoid Q := by
  simp only [Avoid, wires_append, Finset.mem_union]
  constructor
  · intro h; exact ⟨fun q hq => h q (Or.inl hq), fun q hq => h q (Or.inr hq)⟩
  · intro h q hq; rcases hq with hq | hq
    · exact h.1 q hq
    · exact h.2 q hq

theorem avoid_sub {P Q : Program} (h : wires P ⊆ wires Q) (hq : Avoid Q) : Avoid P :=
  fun q hp => hq q (h hp)

theorem avoid_nil : Avoid [] := by intro q hq; simp [wires] at hq

theorem base_good (q : Nat) (h : ¬ badIdx q) : goodW (base q) := by
  show ¬ (q + 16 = 2313 + 16 ∨ (2401 + 16 ≤ q + 16 ∧ q + 16 ≤ 2408 + 16))
  unfold badIdx at h; omega

theorem bad_not_zero (q : Nat) (h : badIdx q) : ¬ zeroRegion q := by
  unfold badIdx at h; unfold zeroRegion workRegion holeRegion; omega

theorem pi0_good (q : Nat) (h : ¬ badIdx q) : ¬ badIdx (pi0 q) := by
  intro hb
  have fix := pi0_outside (pi0 q) (bad_not_zero _ hb)
  have := pi0.injective fix
  exact h (this ▸ hb)

theorem pi_good (j q : Nat) (hj : j < 170) (h : ¬ badIdx q) : ¬ badIdx (pi j q) := by
  intro hb
  have fix := pi_outside j (pi j q) hj (bad_not_zero _ hb)
  have := (pi j).injective fix
  exact h (this ▸ hb)

theorem allPlaced_good (q : Nat) (h : ¬ badIdx q) : goodW (allPlaced q) :=
  base_good _ (pi0_good q h)

theorem placed_good (j q : Nat) (hj : j < 170) (h : ¬ badIdx q) : goodW (placed j q) :=
  base_good _ (pi_good j q hj h)

theorem field_not_bad (q : Nat) (h : fieldSite q) : ¬ badIdx q := by
  unfold fieldSite at h; unfold badIdx; omega

theorem shared_site' (q : Nat) (h : q∈CompressedFieldSupport.sharedSites id 2409) : fieldSite q := by
  simp only [CompressedFieldSupport.sharedSites,balancedSharedPorts,BalancedCircuit.Layout.wires,
    BalancedCleanup.Layout.wires,OffsetCleanupBorrowedCaller.carry,wireBlock,List.map_id,
    List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at h
  dsimp only [id] at h
  unfold fieldSite
  omega

theorem packet_not_bad (j q : Nat) (hj : j < 170) (h : q∈packetSites j) : ¬ badIdx q := by
  simp only [packetSites,List.mem_cons,List.not_mem_nil,or_false] at h
  unfold badIdx; unfold H at h
  omega

theorem inventory_not_bad (j q : Nat) (hj : j < 170) (h : q∈groupInventory j) : ¬ badIdx q := by
  simp only [groupInventory,List.mem_append] at h
  rcases h with (h|h)|h
  · exact field_not_bad q (shared_site' q h)
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    unfold badIdx; omega
  · exact packet_not_bad j q hj h

/-! Field side. -/

theorem cell_avoid (divide : Bool) (j i : Nat) (hj : j < 170)
    (hi0 : 3*j ≤ i) (hi : i < 3*j+3) :
    Avoid (renameProgram (placed j) (logicalCell divide i)) := by
  have g : i∈packetSites j := by
    simp only [packetSites,List.mem_cons,List.not_mem_nil,or_false]
    omega
  have s : 1028+i∈packetSites j := by
    simp only [packetSites,List.mem_cons,List.not_mem_nil,or_false]
    unfold H
    omega
  have body := CompressedFieldSupport.cells_active id 2400 i (1028+i) 2409 2410
    (mixedTranscriptUnitTrace.getD i (false,false)).1
    (mixedTranscriptUnitTrace.getD i (false,false)).2 (groupInventory j).toFinset
    (by intro q hq; simp only [groupInventory,List.mem_toFinset,List.mem_append];
        exact Or.inl (Or.inl (List.mem_toFinset.mp hq)))
    (by simp [groupInventory]) (by simp [groupInventory,g])
    (by simp [groupInventory,s]) (by simp [groupInventory])
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨old,hraw,rfl⟩ := Finset.mem_image.mp hq
  have belongs : old∈groupInventory j := by
    cases divide
    · exact List.mem_toFinset.mp (body.2 (by simpa only [logicalCell,Bool.false_eq_true,if_false] using hraw))
    · exact List.mem_toFinset.mp (body.1 (by simpa only [logicalCell,if_true] using hraw))
  exact placed_good j old hj (inventory_not_bad j old hj belongs)

theorem codec_avoid (j : Nat) (hj : j < 170) :
    Avoid (compressedHistoryEncode (placed j) (3*j)) ∧
    Avoid (compressedHistoryDecode (placed j) (3*j)) := by
  constructor
  · intro q hq
    obtain ⟨u,rfl⟩ := compressedHistory_gate_mem (placed j) (placed_pool_nodup j)
      (placed_above j) (3*j) (by omega) _ (Or.inl rfl) q hq
    exact placed_good j _ hj (packet_not_bad j _ hj (history_packet j u))
  · intro q hq
    obtain ⟨u,rfl⟩ := compressedHistory_gate_mem (placed j) (placed_pool_nodup j)
      (placed_above j) (3*j) (by omega) _ (Or.inr rfl) q hq
    exact placed_good j _ hj (packet_not_bad j _ hj (history_packet j u))

theorem group_avoid (divide : Bool) (j : Nat) (hj : j < 170) : Avoid (mappedGroup divide j) := by
  have codec := codec_avoid j hj
  have a := cell_avoid divide j (3*j) hj (by omega) (by omega)
  have b := cell_avoid divide j (3*j+1) hj (by omega) (by omega)
  have c := cell_avoid divide j (3*j+2) hj (by omega) (by omega)
  cases divide <;> simp only [mappedGroup,Bool.false_eq_true,if_false,if_true,avoid_append]
  · exact ⟨⟨codec.2,⟨⟨c,b⟩,a⟩⟩,codec.1⟩
  · exact ⟨⟨codec.2,⟨⟨a,b⟩,c⟩⟩,codec.1⟩

theorem groups_avoid (divide : Bool) (j n : Nat) (h : j+n ≤ 170) :
    Avoid (mappedGroups divide j n) := by
  induction n generalizing j with
  | zero => simp only [mappedGroups]; exact avoid_nil
  | succ n ih =>
    have current := group_avoid divide j (by omega)
    have rest := ih (j+1) (by omega)
    cases divide <;> simp only [mappedGroups,Bool.false_eq_true,if_false,if_true,avoid_append]
    · exact ⟨rest,current⟩
    · exact ⟨current,rest⟩

theorem tail_avoid (divide : Bool) (i : Nat) (hi : i=510 ∨ i=511) :
    Avoid (renameProgram allPlaced (logicalCell divide i)) := by
  let W := (CompressedFieldSupport.sharedSites id 2409++[2400,2410,i,1028+i]).toFinset
  have body := CompressedFieldSupport.cells_active id 2400 i (1028+i) 2409 2410
    (mixedTranscriptUnitTrace.getD i (false,false)).1
    (mixedTranscriptUnitTrace.getD i (false,false)).2 W
    (by intro q hq; simp only [W,List.mem_toFinset,List.mem_append]; exact Or.inl (List.mem_toFinset.mp hq))
    (by simp [W]) (by simp [W]) (by simp [W]) (by simp [W])
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨old,hraw,rfl⟩ := Finset.mem_image.mp hq
  have belongs : old∈W := by
    cases divide
    · exact body.2 (by simpa only [logicalCell,Bool.false_eq_true,if_false] using hraw)
    · exact body.1 (by simpa only [logicalCell,if_true] using hraw)
  simp only [W,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,
    or_false,or_assoc] at belongs
  apply allPlaced_good
  rcases belongs with h|rfl|rfl|rfl|rfl
  · exact field_not_bad old (shared_site' old h)
  all_goals unfold badIdx; omega

theorem mappedReplay_avoid (divide : Bool) : Avoid (mappedReplay divide) := by
  have groups := groups_avoid divide 0 170 (by omega)
  have a := tail_avoid divide 510 (by omega)
  have b := tail_avoid divide 511 (by omega)
  cases divide <;> simp only [mappedReplay,Bool.false_eq_true,if_false,if_true,avoid_append]
  · exact ⟨⟨b,a⟩,groups⟩
  · exact ⟨⟨groups,a⟩,b⟩

theorem convert_site' (target : Bool) (q : Nat)
    (h : q∈(if target then balancedSharedTargetConvert id else balancedSharedSourceConvert id).wires) :
    fieldSite q := by
  cases target <;> simp only [Bool.false_eq_true,if_false,if_true,
    balancedSharedTargetConvert,balancedSharedSourceConvert,BalancedConvert.Layout.wires,
    wireBlock,List.map_id,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at h
  all_goals dsimp only [id] at h; unfold fieldSite; omega

theorem converters_avoid (canonical : Bool) :
    Avoid (renameProgram allPlaced (converterPair canonical)) := by
  have target := BalancedConvert.support (balancedSharedTargetConvert id)
  have source := BalancedConvert.support (balancedSharedSourceConvert id)
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨old,hraw,rfl⟩ := Finset.mem_image.mp hq
  have site : fieldSite old := by
    cases canonical <;> simp only [converterPair,Bool.false_eq_true,if_false,if_true,
      wires_append,Finset.mem_union] at hraw
    · rcases hraw with h|h
      · exact convert_site' true old (List.mem_toFinset.mp (target.1 h))
      · exact convert_site' false old (List.mem_toFinset.mp (source.1 h))
    · rcases hraw with h|h
      · exact convert_site' true old (List.mem_toFinset.mp (target.2 h))
      · exact convert_site' false old (List.mem_toFinset.mp (source.2 h))
  exact allPlaced_good old (field_not_bad old site)

theorem unary_avoid (divide : Bool) :
    Avoid (renameProgram allPlaced (if divide then dblInPlace (borrowedSkywalkUnary id) p
      else halfInPlace (borrowedSkywalkUnary id) p)) := by
  have u := modUnary_wires (borrowedSkywalkUnary id) 256 p (borrowedSkywalkUnary_widths id) (by omega)
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨old,hraw,rfl⟩ := Finset.mem_image.mp hq
  have member : old∈((borrowedSkywalkUnary id).z++(borrowedSkywalkUnary id).core.work++
      [(borrowedSkywalkUnary id).flag]).toFinset := by
    cases divide
    · simp only [Bool.false_eq_true,if_false] at hraw
      rw [u.2] at hraw
      exact hraw
    · simp only [if_true] at hraw
      rw [u.1] at hraw
      exact List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp hraw))
  have site : fieldSite old := by
    change old∈((wireBlock id 2056 256++[id 2312])++
      (wireBlock id 512 257++wireBlock id 1540 256++[id 1797])++[id 769]).toFinset at member
    simp only [List.mem_toFinset,wireBlock,List.map_id,List.mem_append,List.mem_cons,List.not_mem_nil,
      List.mem_range'_1,or_false] at member
    dsimp only [id] at member
    simp only [or_assoc] at member
    rcases member with h|rfl|h|h|rfl|rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
    · norm_num [fieldSite]
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inr (Or.inl (by omega)))
    · norm_num [fieldSite]
    · norm_num [fieldSite]
  exact allPlaced_good old (field_not_bad old site)

theorem copy_avoid : Avoid (renameProgram allPlaced
    (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a)) := by
  have zword : (skywalkSharedField id).z=wireBlock id 2056 257 := skywalkShared_field_z id
  have aword : (skywalkSharedField id).a=wireBlock id 770 257 := rfl
  have cp := copyRegister_wires_subset none (skywalkSharedField id).z (skywalkSharedField id).a
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨old,hraw,rfl⟩ := Finset.mem_image.mp hq
  have member := cp hraw
  rw [zword,aword] at member
  have site : fieldSite old := by
    simp only [List.mem_toFinset,Option.toList_none,List.nil_append,wireBlock,List.map_id,
      List.mem_append,List.mem_range'_1] at member
    unfold fieldSite
    omega
  exact allPlaced_good old (field_not_bad old site)

theorem terminalFieldSegment_avoid (divide : Bool) :
    Avoid (EntryMappedFieldSegmentTrim.terminalFieldSegment divide) := by
  have rp : Avoid (EntryMappedFieldSegmentTrim.terminalReplay divide) :=
    avoid_sub ((EntryMappedFieldSegmentTrim.terminalReplay_support_sub divide).trans
      (EntryMappedFieldSegmentTrim.replay_support_sub divide)) (mappedReplay_avoid divide)
  have a := converters_avoid false
  have b := converters_avoid true
  cases divide <;> simp only [EntryMappedFieldSegmentTrim.terminalFieldSegment,Bool.false_eq_true,
    if_false,if_true,avoid_append]
  · exact ⟨⟨⟨⟨copy_avoid,a⟩,rp⟩,b⟩,avoid_nil⟩
  · exact ⟨⟨⟨⟨avoid_nil,a⟩,rp⟩,b⟩,copy_avoid⟩

theorem selectedFieldSegment_avoid (divide : Bool) : Avoid (selectedFieldSegment divide) :=
  avoid_sub (PenultimateMapped.fieldSegment_support_sub divide) (terminalFieldSegment_avoid divide)

/-! Integer side. -/

theorem integer_good (q : Nat) (h : q < 1798) : goodW (base q) := by
  apply base_good; unfold badIdx; omega

theorem tick_layout_avoid (i : Nat) (hi : i < 512) :
    ∀ q ∈ (compactSkywalkTickLayout base i).wires.toFinset, goodW q := by
  have width := compactSkywalkTick_width_bounds i hi
  have view : (compactSkywalkTickLayout base i).wires =
      ([skywalkPoolPreviousId i,1028+i,i+compactSkywalkTickPreWidth i,i,770]++
      List.range' (i+1) (compactSkywalkTickPreWidth i-1)++
      List.range' 771 (compactSkywalkTickPreWidth i-1)++
      List.range' 1540 (compactSkywalkTickPreWidth i-1)).map base := by
    change base (skywalkPoolPreviousId i)::base (1028+i)::
      base (i+compactSkywalkTickPreWidth i)::base i::base 770::
      ((compactSkywalkTickLayout base i).ah++(compactSkywalkTickLayout base i).bh++
      wireBlock base 1540 (compactSkywalkTickPreWidth i-1)) = _
    rw [compactSkywalkTick_ah base i hi,compactSkywalkTick_bh base i hi]
    simp [wireBlock,List.map_append,List.append_assoc]
  intro q hq
  rw [List.mem_toFinset,view] at hq
  obtain ⟨old,h,rfl⟩ := List.mem_map.mp hq
  apply integer_good
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at h
  by_cases hz : i=0
  · simp only [skywalkPoolPreviousId,if_pos hz] at h; omega
  · simp only [skywalkPoolPreviousId,if_neg hz] at h; omega

theorem ticks_avoid (i : Nat) (hi : i < 512) :
    Avoid (compactSkywalkTick base i) ∧ Avoid (compactSkywalkReverseTick base i) :=
  ⟨fun q hq => tick_layout_avoid i hi q (compactSkywalkTick_support base i hi base_pool_nodup hq),
   fun q hq => tick_layout_avoid i hi q (compactSkywalkReverseTick_support base i hi base_pool_nodup hq)⟩

theorem base_codec_avoid (start : Nat) (hs : start+3 ≤ 512) :
    Avoid (compressedHistoryEncode base start) ∧ Avoid (compressedHistoryDecode base start) := by
  have lift (P : Program) (he : P=compressedHistoryEncode base start ∨
      P=compressedHistoryDecode base start) : Avoid P := by
    intro q hq
    obtain ⟨u,rfl⟩ := compressedHistory_gate_mem base base_pool_nodup base_above start hs P he q hq
    have region := compressedHistoryId_region start hs u
    apply integer_good
    omega
  exact ⟨lift _ (Or.inl rfl),lift _ (Or.inr rfl)⟩

theorem delayed_codec_avoid (i : Nat) (hi : i < 512) :
    Avoid (compressedPackAfter base i) ∧ Avoid (compressedDecodeBefore base i) := by
  cases h : compressedPackDue i
  · simp only [compressedPackAfter,compressedDecodeBefore,h,Bool.false_eq_true,if_false]
    exact ⟨avoid_nil, avoid_nil⟩
  · have due := compressedPackDue_true i h
    have support := base_codec_avoid (i-3) (by omega)
    simpa only [compressedPackAfter,compressedDecodeBefore,h,if_true] using support

theorem integer_avoid (i n : Nat) (h : i+n ≤ 512) :
    Avoid (compressedCompactForward base i n) ∧ Avoid (compressedCompactReverse base i n) := by
  induction n generalizing i with
  | zero => simp only [compressedCompactForward,compressedCompactReverse]; exact ⟨avoid_nil, avoid_nil⟩
  | succ n ih =>
    have rest := ih (i+1) (by omega)
    have tick := ticks_avoid i (by omega)
    have codec := delayed_codec_avoid i (by omega)
    simp only [compressedCompactForward,compressedCompactReverse,avoid_append]
    exact ⟨⟨⟨tick.1,codec.1⟩,rest.1⟩,⟨⟨rest.2,codec.2⟩,tick.2⟩⟩

theorem prefixSites_avoid : ∀ q ∈ (NativeFirstDirect.prefixSites base).toFinset, goodW q := by
  intro q hq
  simp only [NativeFirstDirect.prefixSites,List.mem_toFinset,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false,wireBlock,List.mem_map,List.mem_range'_1] at hq
  rcases hq with ((h|h)|h)|(rfl|rfl)
  all_goals first
    | obtain ⟨i,hi,rfl⟩ := h
      exact integer_good _ (by omega)
    | exact integer_good _ (by omega)

theorem clear_avoid : Avoid (skywalkArithmeticClear base) := by
  intro q hq
  rw [skywalkArithmeticClear,skywalkTerminalClear_wires] at hq
  simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl
  all_goals exact integer_good _ (by omega)

theorem kernel_avoid (divide : Bool) : Avoid (kernel divide) := by
  have native := NativeFirstDirect.prefix_support base
  have integer := integer_avoid 1 511 (by omega)
  have known := NativeFirstKnown.inverse_support base
  simp only [kernel,avoid_append]
  exact ⟨⟨⟨⟨⟨⟨fun q hq => prefixSites_avoid q (native.1 hq),integer.1⟩,clear_avoid⟩,
    selectedFieldSegment_avoid divide⟩,clear_avoid⟩,integer.2⟩,
    fun q hq => prefixSites_avoid q (known hq)⟩

/-! The zero-divisor wrapper never uses its auxiliary carry-in. -/

theorem zeroCompare_avoid (x x' : Wire) (xs : List Wire) (c : Wire) (cs : List Wire) (cin target : Wire)
    (good : ∀ q ∈ x :: x' :: xs ++ c :: cs ++ [target], goodW q) :
    Avoid (ZeroSeededConstantCompare.program (x::x'::xs) (c::cs) cin target) := by
  intro q hq
  simp only [ZeroSeededConstantCompare.program, wires_append, Finset.mem_union] at hq
  rcases hq with (h|h)|h
  · simp [ZeroSeededConstantCompare.prepare, wires, Instr.wires] at h
    rcases h with rfl|rfl <;> exact good _ (by simp)
  · have h' := List.mem_toFinset.mp (compareConstantLt_wires_subset _ _ _ _ _ h)
    apply good
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h' ⊢
    tauto
  · simp [ZeroSeededConstantCompare.release, wires, Instr.wires] at h
    rcases h with rfl|rfl <;> exact good _ (by simp)

theorem controlled_avoid (divide : Bool) : Avoid (controlled divide) := by
  have xs : wireBlock base 770 256 = base 770 :: base 771 :: wireBlock base 772 254 := by
    simp [wireBlock, List.range'_succ]
  have cs : wireBlock base 0 255 = base 0 :: wireBlock base 1 254 := by
    simp [wireBlock, List.range'_succ]
  have good : ∀ q ∈ base 770 :: base 771 :: wireBlock base 772 254 ++ base 0 :: wireBlock base 1 254 ++
      [base 2411], goodW q := by
    intro q hq
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, wireBlock, List.mem_map,
      List.mem_range'_1] at hq
    rcases hq with ((rfl|rfl|⟨i,hi,rfl⟩)|(rfl|⟨i,hi,rfl⟩))|rfl
    all_goals apply base_good; unfold badIdx; omega
  have cmp := zeroCompare_avoid _ _ _ _ _ (base 2313) (base 2411) good
  have mask : Avoid (maskedConstant (base 2411) (wireBlock base 770 256) 1) := by
    intro q hq
    have h := List.mem_toFinset.mp (maskedConstant_wires_subset _ _ _ hq)
    rw [xs] at h
    exact good q (by simp only [List.mem_cons, List.mem_append] at h ⊢; tauto)
  simp only [controlled, directZeroControlled, directZeroDivisorEnter, directZeroDivisorLeave,
    avoid_append, xs, cs]
  rw [xs] at mask
  exact ⟨⟨cmp, mask⟩, kernel_avoid divide, mask, cmp⟩

end ECDSAAdd.Entrant
end

-- source: ECDSAAdd/Submission/Entrant/ZeroFlag.lean
noncomputable section

/-! Infinity tests read the finite flag.

Under the canonical encoding, `R = O` exactly when the finite flag of `R` is
clear (infinity is encoded with a clear flag, every finite point with a set
flag).  The two full-register comparisons against `pointCode 0` used by the
Skywalk classification are therefore replaced by a single controlled flag test
`t ^= c ∧ ¬finite`, which has the same effect on every boundary state. -/
namespace ECDSAAdd.Entrant
open Arithmetic Secp256k1 ControlledPointLayout

/-- `t ^= c ∧ ¬f`. -/
def zeroFlag (f c t : Wire) : Program := [.X f, .CCX c f t, .X f]

theorem zeroFlag_run (f c t : Wire) (hcf : c ≠ f) (hft : f ≠ t)
    (s : State) (m : List Bool) :
    run (zeroFlag f c t) m s =
      ⟨s.phase, writeBit s.basis t (s.basis t ^^ (s.basis c && !s.basis f))⟩ := by
  simp only [zeroFlag, run]
  congr 1
  funext q
  by_cases hq : q = t
  · subst q
    simp [writeBit, Function.update, hft.symm, hcf]
  · by_cases hqf : q = f
    · subst q
      simp [writeBit, Function.update, hft]
    · simp [writeBit, Function.update, hq, hqf]

theorem pointEqual_zero (R : Point) : pointEqual R 0 = !pointFinite R := by
  cases R with
  | zero =>
    have h0 : pointEqual WeierstrassCurve.Affine.Point.zero 0 = true := (pointEqual_true_iff _ _).mpr rfl
    rw [h0]
    rfl
  | some h =>
    have hne : (WeierstrassCurve.Affine.Point.some h : Point) ≠ 0 :=
      WeierstrassCurve.Affine.Point.some_ne_zero h
    have hf : pointEqual (WeierstrassCurve.Affine.Point.some h) 0 = false := by
      cases hh : pointEqual (WeierstrassCurve.Affine.Point.some h) 0
      · rfl
      · exact absurd ((pointEqual_true_iff _ _).mp hh) hne
    rw [hf]
    simp [pointFinite, coordinates]

section
variable (L : ControlledPointLayout) (hn : L.wires.Nodup)
include hn

theorem zeroFlag_boundary (R : Point) (b : Bool) (f : BasisState) (c t : Wire)
    (hc : c=L.control ∨ c∈L.inPlaceFlags) (ht : t∈L.inPlaceFlags) (hct : c≠t) (B : Bool)
    (hb : (if c=L.control then b else f c)=B) :
    Triple (PointDialogBoundary L R b f)
      (zeroFlag L.point.finite c t)
      (PointDialogBoundary L R b (writeBit f t (f t ^^ (B && pointEqual R 0)))) := by
  have hnd := L.dialogPointZero_nodup hn c t hct hc ht
  simp only [PointAddLayout.pointWires, List.cons_append, List.nodup_cons, List.mem_cons,
    List.mem_append, not_or] at hnd
  have hcf : c ≠ L.point.finite := hnd.1.2.1
  have hft : L.point.finite ≠ t := fun h => hnd.2.1.1 h.symm
  intro s m v
  have hh := zeroFlag_run L.point.finite c t hcf hft s m
  have hfin : s.basis L.point.finite = pointFinite R := ((point_holds _ _ _).mp v.point).1
  have hcval : s.basis c=B := by
    rw [← hb]
    split_ifs with h
    · subst c; exact v.control
    · exact v.flags c (hc.resolve_left h)
  rw [hfin, ← pointEqual_zero] at hh
  refine ⟨by rw [hh], v.withFlags hn ?_ ?_⟩
  · intro q hq
    rw [hh]
    by_cases he : q=t
    · subst q; simp [writeBit,hcval,v.flags t ht]
    · simp [writeBit,he,v.flags q hq]
  · intro q hq
    rw [hh]
    have hqt : q≠t := fun he => hq (he ▸ ht)
    simp [writeBit,hqt]

theorem zeroFlag_equalO (R : Point) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (zeroFlag L.point.finite L.control L.infinitySelect)
      (PointDialogBoundary L R b (dialogFlagState L (O ^^ (b && pointEqual R 0)) D I G E H K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := zeroFlag_boundary L hn R b (dialogFlagState L O D I G E H K) L.control L.infinitySelect
    (Or.inl rfl)
    (by simp [inPlaceFlags]) (by tauto) b
    (by simp)
  simp only [hr.1] at hh
  exact hh.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).1)

theorem zeroFlag_equalI (R : Point) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (zeroFlag L.point.finite L.control L.genericSelect)
      (PointDialogBoundary L R b (dialogFlagState L O D (I ^^ (b && pointEqual R 0)) G E H K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := zeroFlag_boundary L hn R b (dialogFlagState L O D I G E H K) L.control L.genericSelect
    (Or.inl rfl)
    (by simp [inPlaceFlags]) (by tauto) b
    (by simp)
  simp only [hr.2.2.1] at hh
  exact hh.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).2.2.1)

end

end ECDSAAdd.Entrant
end

-- source: ECDSAAdd/Submission/Entrant/ShortEqual.lean
noncomputable section

/-! Short point comparison.

On the curve, two finite points with the same abscissa have ordinates `y` and
`±y`; since `p` is odd, `y` and `p - y` differ in parity unless `y = 0`.  So a
valid encoded point is determined by its finite flag, its full `x` register and
the lowest bit of `y`.  `shortEqual` compares only those 258 wires against the
matching prefix of the classical constant, using the unchanged `equalConstant`
gadget on the first 258 zero ports of the shared pool. -/
namespace ECDSAAdd.Entrant
open Arithmetic Secp256k1 ControlledPointLayout Challenge Baselines

/-- Finite flag, `x`, and the low bit of `y`. -/
def shortSrc (L : ControlledPointLayout) : List Wire :=
  L.point.finite :: L.point.x ++ L.point.y.take 1

/-- The matching prefix of `pointCode`. -/
def shortCode (R : Point) : Nat :=
  (pointFinite R).toNat + 2 * (pointX R + 2^256 * (pointY R % 2))

/-- `t ^= c ∧ (point = C)` on 258 compared wires. -/
def shortEqual (L : ControlledPointLayout) (c t : Wire) (C : Point) : Program :=
  equalConstant c t (zeroPorts (shortSrc L) (L.dialogPool.take 258)) (shortCode C)

theorem shortCode_lt (R : Point) : shortCode R < 2^258 := by
  have hp : p < 2^256 := by norm_num [p]
  have hx := (point_coordinates_lt R).1
  have hf : (pointFinite R).toNat ≤ 1 := by cases pointFinite R <;> decide
  have hy : pointY R % 2 < 2 := Nat.mod_lt _ (by decide)
  unfold shortCode
  omega

theorem shortCode_eq_iff (R C : Point) : shortCode R = shortCode C ↔ R = C := by
  constructor
  · intro h
    have hp : p < 2^256 := by norm_num [p]
    have hxr := (point_coordinates_lt R).1
    have hxc := (point_coordinates_lt C).1
    have hf : pointFinite R = pointFinite C := by
      unfold shortCode at h
      cases hr : pointFinite R <;> cases hc : pointFinite C <;>
        simp_all only [Bool.toNat_false, Bool.toNat_true] <;> omega
    have hxy : pointX R = pointX C ∧ pointY R % 2 = pointY C % 2 := by
      unfold shortCode at h
      rw [hf] at h
      omega
    cases R with
    | zero => cases C <;> simp_all [pointFinite, coordinates]
    | @some x y hr =>
      cases C with
      | zero => simp [pointFinite, coordinates] at hf
      | @some u v hc =>
        have heX : x = u := ZMod.val_injective p hxy.1
        have hpar : y.val % 2 = v.val % 2 := hxy.2
        have heY : y = v := by
          by_cases hyv : y = -v
          · by_cases hv0 : v = 0
            · rw [hyv, hv0, neg_zero]
            · exfalso
              have hneg : y.val = p - v.val := by
                rw [hyv, ZMod.neg_val, if_neg hv0]
              have hvl : v.val < p := ZMod.val_lt v
              have hodd : p % 2 = 1 := by norm_num [p]
              omega
          · exact y_eq_of_x_eq_of_not_inverse hr hc heX hyv
        subst u; subst v; rfl
  · rintro rfl; rfl

theorem regValue_take_one (y : List Wire) (s : BasisState) :
    regValue (y.take 1) s = regValue y s % 2 := by
  cases y with
  | nil => simp [regValue]
  | cons w ys =>
    simp only [List.take_succ_cons, List.take_zero]
    change (if s w then 1 else 0) + 2 * 0 = ((if s w then 1 else 0) + 2 * regValue ys s) % 2
    split <;> omega

theorem shortSrc_value (L : ControlledPointLayout) (hw : L.Widths) (R : Point) (s : BasisState)
    (hp : Holds.holds s L.point R) : regValue (shortSrc L) s = shortCode R := by
  have hv := (point_holds L.point R s).mp hp
  change (if s L.point.finite then 1 else 0) + 2 * regValue (L.point.x ++ L.point.y.take 1) s = _
  rw [regValue_append, show L.point.x.length = 256 from hw.inputX, regValue_take_one,
    hv.1, hv.2.1, hv.2.2]
  unfold shortCode
  cases pointFinite R <;> rfl

theorem shortSrc_length (L : ControlledPointLayout) (hw : L.Widths) :
    (shortSrc L).length = 258 := by
  simp [shortSrc, show L.point.x.length = 256 from hw.inputX,
    show L.point.y.length = 256 from hw.inputY]

theorem shortWork_length (L : ControlledPointLayout) (hw : L.Widths) :
    (L.dialogPool.take 258).length = 258 := by
  simp [L.dialogPool_length hw]

theorem short_sublist_inner (L : ControlledPointLayout) :
    (shortSrc L ++ L.dialogPool.take 258).Sublist
      (PointAddLayout.pointWires L.point ++ L.dialogPool.take 513) := by
  have h1 : (shortSrc L).Sublist (PointAddLayout.pointWires L.point) := by
    simp only [shortSrc, PointAddLayout.pointWires]
    exact (List.Sublist.refl _).append (List.take_sublist 1 _)
  have h2 : (L.dialogPool.take 258).Sublist (L.dialogPool.take 513) := by
    have he : L.dialogPool.take 258 = (L.dialogPool.take 513).take 258 := by
      rw [List.take_take]; rfl
    rw [he]; exact List.take_sublist _ _
  exact h1.append h2

theorem short_sublist (L : ControlledPointLayout) (c t : Wire) :
    (c :: t :: shortSrc L ++ L.dialogPool.take 258).Sublist
      (c :: t :: PointAddLayout.pointWires L.point ++ L.dialogPool.take 513) :=
  ((short_sublist_inner L).cons_cons t).cons_cons c

theorem short_nodup (L : ControlledPointLayout) (hn : L.wires.Nodup) (c t : Wire) (hct : c ≠ t)
    (hc : c = L.control ∨ c ∈ L.inPlaceFlags) (ht : t ∈ L.inPlaceFlags) :
    (c :: t :: shortSrc L ++ L.dialogPool.take 258).Nodup :=
  (L.dialogPointZero_nodup hn c t hct hc ht).sublist (short_sublist L c t)

theorem shortEqual_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (c t : Wire) (hct : c ≠ t) (hc : c = L.control ∨ c ∈ L.inPlaceFlags) (ht : t ∈ L.inPlaceFlags)
    (R C : Point) (s : State) (m : List Bool) (hp : Holds.holds s.basis L.point R)
    (hz : regValue (L.dialogPool.take 258) s.basis = 0) :
    run (shortEqual L c t C) m s =
      ⟨s.phase, writeBit s.basis t (s.basis t ^^ (s.basis c && pointEqual R C))⟩ := by
  have hh := equalPorts_correct c t (shortSrc L) (L.dialogPool.take 258) (shortCode C)
    ((shortSrc_length L hw).trans (shortWork_length L hw).symm) (short_nodup L hn c t hct hc ht)
    (by rw [shortSrc_length L hw]; exact shortCode_lt C) s m hz
  rw [shortSrc_value L hw R s.basis hp] at hh
  have he : decide (shortCode R = shortCode C) = pointEqual R C := by
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq, shortCode_eq_iff, pointEqual_true_iff]
  rw [he] at hh
  exact hh

/-- Support of the short comparison is inside the support of the full comparison. -/
theorem shortEqual_wires_subset (L : ControlledPointLayout) (hw : L.Widths) (c t : Wire)
    (C : Point) (k : Nat) :
    wires (shortEqual L c t C) ⊆ wires (equalConstant c t L.dialogPointZero k) := by
  have hpl : (PointAddLayout.pointWires L.point).length = (L.dialogPool.take 513).length := by
    simp [PointAddLayout.pointWires, L.dialogPool_length hw,
      show L.point.x.length = 256 from hw.inputX, show L.point.y.length = 256 from hw.inputY]
  have hsl := (shortSrc_length L hw).trans (shortWork_length L hw).symm
  rw [shortEqual, equalConstant_wires, equalConstant_wires]
  intro q hq
  simp only [List.mem_toFinset, List.mem_cons] at hq ⊢
  rcases hq with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · have hm := (zeroPorts_perm _ _ hsl).subset h
    exact Or.inr (Or.inr ((zeroPorts_perm _ _ hpl).symm.subset ((short_sublist_inner L).subset hm)))

theorem shortEqual_counts (L : ControlledPointLayout) (hw : L.Widths) (c t : Wire) (C : Point) :
    toffoliCount (shortEqual L c t C) = 258 ∧ measurementCount (shortEqual L c t C) = 258 := by
  have hl : (zeroPorts (shortSrc L) (L.dialogPool.take 258)).length = 258 := by
    have he := (zeroPorts_maps (shortSrc L) (L.dialogPool.take 258)
      ((shortSrc_length L hw).trans (shortWork_length L hw).symm)).1
    simpa only [List.length_map, shortSrc_length L hw] using congrArg List.length he
  have h := equalConstant_counts c t (zeroPorts (shortSrc L) (L.dialogPool.take 258)) (shortCode C)
  rw [hl] at h
  exact h

theorem shortEqual_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (c t : Wire) (hct : c ≠ t) (hc : c = L.control ∨ c ∈ L.inPlaceFlags) (ht : t ∈ L.inPlaceFlags)
    (C : Point) : GatePhysical (shortEqual L c t C) := by
  have hsl := (shortSrc_length L hw).trans (shortWork_length L hw).symm
  apply equalConstant_physical
  have hperm := ((zeroPorts_perm _ _ hsl).cons t).cons c
  exact hperm.nodup_iff.mpr (short_nodup L hn c t hct hc ht)

theorem shortEqual_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths) (c t : Wire)
    (C : Point) : gateSlots (shortEqual L c t C) ≤ 2323 := by
  have hl : (zeroPorts (shortSrc L) (L.dialogPool.take 258)).length = 258 := by
    have he := (zeroPorts_maps (shortSrc L) (L.dialogPool.take 258)
      ((shortSrc_length L hw).trans (shortWork_length L hw).symm)).1
    simpa only [List.length_map, shortSrc_length L hw] using congrArg List.length he
  have h := Baselines.equalConstant_gateSlots_le c t
    (zeroPorts (shortSrc L) (L.dialogPool.take 258)) (shortCode C)
  rw [hl] at h
  exact h

section
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem shortBoundary_equal (R C : Point) (b : Bool) (f : BasisState) (c t : Wire)
    (hc : c=L.control ∨ c∈L.inPlaceFlags) (ht : t∈L.inPlaceFlags) (hct : c≠t) (B : Bool)
    (hb : (if c=L.control then b else f c)=B) :
    Triple (PointDialogBoundary L R b f)
      (shortEqual L c t C)
      (PointDialogBoundary L R b (writeBit f t (f t ^^ (B && pointEqual R C)))) := by
  intro s m v
  have hclean : regValue (L.dialogPool.take 258) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq=>(regValue_zero _ _).mp v.clean q (List.take_subset _ _ hq))
  have hh := shortEqual_correct L hw hn c t hct hc ht R C s m v.point hclean
  have hcval : s.basis c=B := by
    rw [← hb]
    split_ifs with h
    · subst c; exact v.control
    · exact v.flags c (hc.resolve_left h)
  refine ⟨by rw [hh],v.withFlags hn ?_ ?_⟩
  · intro q hq
    rw [hh]
    by_cases he : q=t
    · subst q; simp [writeBit,hcval,v.flags t ht]
    · simp [writeBit,he,v.flags q hq]
  · intro q hq
    rw [hh]
    have hqt : q≠t := fun he => hq (he ▸ ht)
    simp [writeBit,hqt]

theorem shortFlag_equalO (R C : Point) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (shortEqual L L.control L.infinitySelect C)
      (PointDialogBoundary L R b (dialogFlagState L (O ^^ (b && pointEqual R C)) D I G E H K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := shortBoundary_equal L hw hn R C b (dialogFlagState L O D I G E H K) L.control L.infinitySelect
    (Or.inl rfl)
    (by simp [inPlaceFlags]) (by tauto) b
    (by simp)
  simp only [hr.1] at hh
  exact hh.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).1)

theorem shortFlag_equalD (R C : Point) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (shortEqual L L.core.double L.doubleSelect C)
      (PointDialogBoundary L R b (dialogFlagState L O (D ^^ (K && pointEqual R C)) I G E H K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := shortBoundary_equal L hw hn R C b (dialogFlagState L O D I G E H K) L.core.double L.doubleSelect
    (Or.inr (by simp [inPlaceFlags]))
    (by simp [inPlaceFlags]) (by tauto) K
    (by rw [if_neg (by tauto)]; exact hr.2.2.2.2.2.2)
  simp only [hr.2.1] at hh
  exact hh.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).2.1)

theorem shortFlag_equalI (R C : Point) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (shortEqual L L.control L.genericSelect C)
      (PointDialogBoundary L R b (dialogFlagState L O D (I ^^ (b && pointEqual R C)) G E H K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := shortBoundary_equal L hw hn R C b (dialogFlagState L O D I G E H K) L.control L.genericSelect
    (Or.inl rfl)
    (by simp [inPlaceFlags]) (by tauto) b
    (by simp)
  simp only [hr.2.2.1] at hh
  exact hh.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).2.2.1)

theorem shortFlag_equalH (R C : Point) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (shortEqual L L.core.equalX L.core.equalNegY C)
      (PointDialogBoundary L R b (dialogFlagState L O D I G E (H ^^ (E && pointEqual R C)) K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := shortBoundary_equal L hw hn R C b (dialogFlagState L O D I G E H K) L.core.equalX L.core.equalNegY
    (Or.inr (by simp [inPlaceFlags]))
    (by simp [inPlaceFlags]) (by tauto) E
    (by rw [if_neg (by tauto)]; exact hr.2.2.2.2.1)
  simp only [hr.2.2.2.2.2.1] at hh
  exact hh.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).2.2.2.2.2.1)

end

end ECDSAAdd.Entrant
end

-- source: ECDSAAdd/Submission/Entrant/PairEqual.lean
noncomputable section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Paired point comparison against `C` and `-C`.

`C` and `-C` share the finite flag and the abscissa, and (by `shortCode_eq_iff`)
the low bit of `y` then decides which of the two a valid point equals.  The
257-wire flag/abscissa test is computed once by the zero-detection AND chain,
both targets read the chain output together with the low `y` bit, and only then
is the chain erased by measurement.  Each target costs one Toffoli instead of a
separate 258-Toffoli comparison. -/
namespace ECDSAAdd.Entrant
open Arithmetic Secp256k1 ControlledPointLayout Challenge Baselines RecordedQuantum

/-- The two chain steps of `ZeroControl` (`t := c ∧ ¬a`, and its measured erase). -/
def chainAnd (c a t : Wire) : Program := [.X a, .CCX c a t, .X a]

def chainErase (c a t : Wire) : Program :=
  [.X a, .measureX t [] [.CZ c a], .X a]

theorem chainAnd_run (c a t : Wire) (hca : c≠a) (hat : a≠t)
    (s : State) (m : List Bool) :
    run (chainAnd c a t) m s =
      ⟨s.phase, writeBit s.basis t (s.basis t ^^ (s.basis c && !s.basis a))⟩ := by
  simp only [chainAnd, run]
  apply congrArg (State.mk s.phase)
  funext w
  by_cases hw : w=a
  · subst w; simp [writeBit, hca, hat]
  · by_cases ht : w=t
    · subst w; simp [writeBit, hca, Ne.symm hat]
    · simp [writeBit, hw, ht, hca]

theorem chainErase_run (c a t : Wire) (hca : c≠a) (hat : a≠t)
    (hct : c≠t) (s : State) (m : List Bool)
    (hq : s.basis t = (s.basis c && !s.basis a)) :
    run (chainErase c a t) m s = ⟨s.phase, writeBit s.basis t false⟩ := by
  simp only [chainErase, run]
  cases hm : m.headD false <;>
    simp [measureAndCorrect, correct, writeBit, hca, hat, hat.symm, hct, hq]
  all_goals
    funext w
    by_cases hw : w=a
    · subst w; simp [hat]
    · simp [Function.update_apply, hw]

/-- `t ^= w ∧ (y = a)`. -/
def bitTest (w y t : Wire) (a : Bool) : Program :=
  if a then [.CCX w y t] else zeroFlag y w t

theorem bitTest_run (w y t : Wire) (a : Bool) (hwy : w≠y) (hyt : y≠t) (hwt : w≠t)
    (s : State) (m : List Bool) :
    run (bitTest w y t a) m s =
      ⟨s.phase, writeBit s.basis t (s.basis t ^^ (s.basis w && (s.basis y == a)))⟩ := by
  cases a with
  | false =>
    simp only [bitTest, Bool.false_eq_true, if_false]
    rw [zeroFlag_run y w t hwy hyt s m]
    cases s.basis y <;> rfl
  | true =>
    simp only [bitTest, if_true, run]
    apply congrArg (State.mk s.phase)
    funext q
    by_cases hq : q=t
    · subst q; cases s.basis y <;> simp [writeBit]
    · simp [writeBit, hq]

/-- Both enabled targets read the chain output `w` and the low `y` bit. -/
def pairTail (y t₁ t₂ : Wire) (e₁ a₁ e₂ a₂ : Bool) (w : Wire) : Program :=
  (if e₁ then bitTest w y t₁ a₁ else []) ++ (if e₂ then bitTest w y t₂ a₂ else [])

def pairEffect (y t₁ t₂ : Wire) (e₁ a₁ e₂ a₂ : Bool) (v : Bool) (s : BasisState) : BasisState :=
  writeBit (writeBit s t₁ (s t₁ ^^ (e₁ && v && (s y == a₁)))) t₂
    (s t₂ ^^ (e₂ && v && (s y == a₂)))

theorem pairTail_counts (y t₁ t₂ : Wire) (e₁ a₁ e₂ a₂ : Bool) (w : Wire) :
    toffoliCount (pairTail y t₁ t₂ e₁ a₁ e₂ a₂ w) = e₁.toNat + e₂.toNat ∧
    measurementCount (pairTail y t₁ t₂ e₁ a₁ e₂ a₂ w) = 0 := by
  cases e₁ <;> cases e₂ <;> cases a₁ <;> cases a₂ <;>
    simp [pairTail, bitTest, zeroFlag, toffoliCount, measurementCount]

theorem pairTail_run (y t₁ t₂ : Wire) (e₁ a₁ e₂ a₂ : Bool) (w : Wire)
    (hwy : w≠y) (hw1 : w≠t₁) (hw2 : w≠t₂) (hy1 : y≠t₁) (hy2 : y≠t₂) (h12 : t₁≠t₂)
    (s : State) (m : List Bool) :
    run (pairTail y t₁ t₂ e₁ a₁ e₂ a₂ w) m s =
      ⟨s.phase, pairEffect y t₁ t₂ e₁ a₁ e₂ a₂ (s.basis w) s.basis⟩ := by
  have hfirst : run (if e₁ then bitTest w y t₁ a₁ else []) m s =
      ⟨s.phase, writeBit s.basis t₁ (s.basis t₁ ^^ (e₁ && s.basis w && (s.basis y == a₁)))⟩ := by
    cases e₁
    · simp only [Bool.false_eq_true, if_false, run, Bool.false_and, Bool.xor_false]
      cases s; simp [writeBit]
    · simp only [if_true, Bool.true_and]
      exact bitTest_run w y t₁ a₁ hwy hy1 hw1 s m
  have hm1 : measurementCount (if e₁ then bitTest w y t₁ a₁ else []) = 0 := by
    cases e₁ <;> cases a₁ <;> simp [bitTest, zeroFlag, measurementCount]
  rw [pairTail, run_append, run_take, hfirst, hm1, List.drop_zero]
  cases e₂
  · simp only [Bool.false_eq_true, if_false, run]
    congr 1
    funext q
    simp only [pairEffect, writeBit, Function.update_apply, Bool.false_and, Bool.xor_false]
    by_cases hq2 : q = t₂
    · subst hq2; simp [Ne.symm h12]
    · simp [hq2]
  · simp only [if_true]
    rw [bitTest_run w y t₂ a₂ hwy hy2 hw2]
    congr 1
    funext q
    simp only [pairEffect, writeBit, Function.update_apply, Bool.true_and]
    by_cases hq2 : q=t₂
    · subst q; simp [Ne.symm h12, Ne.symm hw1, hy1.symm, hw1, hy1]
    · by_cases hq1 : q=t₁
      · subst q; simp [h12, hw1, hy1]
      · simp [hq1, hq2]

/-- Zero chain whose innermost step is `T` applied to the chain output. -/
def zeroWith (T : Wire → Program) (c : Wire) : List ZeroBit → Program
  | [] => T c
  | b::bs => chainAnd c b.input b.work ++ zeroWith T b.work bs ++ chainErase c b.input b.work

theorem zeroWith_counts (T : Wire → Program) (n : Nat)
    (hT : ∀ w, toffoliCount (T w) = n ∧ measurementCount (T w) = 0) (c : Wire) (bs : List ZeroBit) :
    toffoliCount (zeroWith T c bs) = bs.length + n ∧
    measurementCount (zeroWith T c bs) = bs.length := by
  induction bs generalizing c with
  | nil => simpa [zeroWith] using hT c
  | cons b bs ih =>
    have h := ih b.work
    simp only [zeroWith, chainAnd, chainErase, toffoliCount_append, measurementCount_append,
      List.length_cons]
    simp [toffoliCount, measurementCount] at h ⊢
    omega

theorem zeroWith_pair_run (y t₁ t₂ : Wire) (e₁ a₁ e₂ a₂ : Bool) (c : Wire) (bs : List ZeroBit)
    (hnd : (c::y::t₁::t₂::bs.flatMap ZeroBit.wires).Nodup)
    (s : State) (m : List Bool) (hz : ∀ b∈bs, s.basis b.work=false) :
    run (zeroWith (pairTail y t₁ t₂ e₁ a₁ e₂ a₂) c bs) m s =
      ⟨s.phase, pairEffect y t₁ t₂ e₁ a₁ e₂ a₂
        (s.basis c && bs.all (fun b => !s.basis b.input)) s.basis⟩ := by
  induction bs generalizing c s m with
  | nil =>
    have hni := hnd
    simp only [List.flatMap_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or,
      or_false] at hni
    obtain ⟨⟨hcy, hc1, hc2⟩, ⟨hy1, hy2⟩, h12, -⟩ := hni
    simp only [zeroWith, List.all_nil, Bool.and_true]
    exact pairTail_run y t₁ t₂ e₁ a₁ e₂ a₂ c hcy hc1 hc2 hy1 hy2 h12 s m
  | cons b bs ih =>
    have hnames : (c::y::t₁::t₂::b.input::b.work::bs.flatMap ZeroBit.wires).Nodup := hnd
    have hni := hnames
    simp only [List.nodup_cons, List.mem_cons, not_or] at hni
    obtain ⟨⟨hcy, hc1, hc2, hci, hcw, hcR⟩, ⟨hy1, hy2, hyi, hyw, hyR⟩, ⟨h12, h1i, h1w, h1R⟩,
      ⟨h2i, h2w, h2R⟩, ⟨hiw, hiR⟩, hwR, hR⟩ := hni
    have hchild : (b.work::y::t₁::t₂::bs.flatMap ZeroBit.wires).Nodup := by
      simp only [List.nodup_cons, List.mem_cons, not_or]
      exact ⟨⟨Ne.symm hyw, Ne.symm h1w, Ne.symm h2w, hwR⟩, ⟨hy1, hy2, hyR⟩, ⟨h12, h1R⟩, h2R, hR⟩
    let q := s.basis c && !s.basis b.input
    let t : State := ⟨s.phase, writeBit s.basis b.work q⟩
    have hp : run (chainAnd c b.input b.work) m s=t := by
      rw [chainAnd_run c b.input b.work hci hiw]
      simp [t, q, hz b (by simp), writeBit]
    have htail (d : ZeroBit) (hd : d∈bs) : d.work≠b.work ∧ d.input≠b.work := by
      constructor <;> intro he <;> apply hwR <;>
        apply List.mem_flatMap.mpr <;> refine ⟨d,hd,?_⟩ <;> simp [ZeroBit.wires, he]
    have hz' : ∀ d∈bs, t.basis d.work=false := by
      intro d hd
      simpa [t, writeBit, (htail d hd).1] using hz d (by simp [hd])
    have hall : bs.all (fun d => !t.basis d.input) = bs.all (fun d => !s.basis d.input) := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true]
      constructor <;> intro h d hd <;> simpa [t, writeBit, (htail d hd).2] using h d hd
    have hcnt := (zeroWith_counts (pairTail y t₁ t₂ e₁ a₁ e₂ a₂) (e₁.toNat + e₂.toNat)
      (pairTail_counts y t₁ t₂ e₁ a₁ e₂ a₂) b.work bs).2
    change run (chainAnd c b.input b.work ++ zeroWith (pairTail y t₁ t₂ e₁ a₁ e₂ a₂) b.work bs ++
      chainErase c b.input b.work) m s = _
    rw [run_append, run_take, run_append, run_take]
    simp only [measurementCount_append, hcnt,
      show measurementCount (chainAnd c b.input b.work)=0 from rfl, Nat.zero_add, List.drop_zero]
    rw [hp, ih b.work hchild t m hz']
    rw [chainErase_run c b.input b.work hci hiw hcw _ _ (by
      simp only [pairEffect, t, writeBit, Function.update_apply]
      simp [Ne.symm h1w, Ne.symm h2w, hcw, hc1, hc2, hiw, Ne.symm h1i, Ne.symm h2i, q])]
    simp only [hall, List.all_cons]
    apply congrArg (State.mk s.phase)
    funext w
    simp only [pairEffect, writeBit, Function.update_apply]
    by_cases hw2 : w=t₂
    · subst w
      simp [h2w, Ne.symm h12, hyw, t, q, writeBit, Function.update_apply, Bool.and_assoc]
    · by_cases hw1 : w=t₁
      · subst w
        simp [hw2, h1w, hyw, t, q, writeBit, Function.update_apply, Bool.and_assoc]
      · by_cases hww : w=b.work
        · subst w
          simp [hw1, hw2, hz b (by simp)]
        · simp [hww, hw1, hw2, t, writeBit, Function.update_apply]


/-! ### Layout instance -/

/-- Finite flag and abscissa (the part shared by `C` and `-C`). -/
def pairSrc (L : ControlledPointLayout) : List Wire := L.point.finite :: L.point.x

def pairCode (R : Point) : Nat := (pointFinite R).toNat + 2 * pointX R

def pairPorts (L : ControlledPointLayout) : List ZeroBit :=
  zeroPorts (pairSrc L) (L.dialogPool.take 257)

/-- The low bit of the in-place `y` register. -/
def yLow (L : ControlledPointLayout) : Wire := L.point.y.headD L.control

def yBit (R : Point) : Bool := decide (pointY R % 2 = 1)

/-- `t₁ ^= e₁ ∧ control ∧ point = C` and `t₂ ^= e₂ ∧ control ∧ point = D`, where `D`
must share the flag/abscissa code of `C` (used with `D = -C`). -/
def pairEqual (L : ControlledPointLayout) (t₁ t₂ : Wire) (e₁ e₂ : Bool) (C D : Point) : Program :=
  xorConstant (pairSrc L) (pairCode C) ++
  zeroWith (pairTail (yLow L) t₁ t₂ e₁ (yBit C) e₂ (yBit D)) L.control (pairPorts L) ++
  xorConstant (pairSrc L) (pairCode C)

theorem pairCode_lt (R : Point) : pairCode R < 2 * 2^256 := by
  have hp : p < 2^256 := by norm_num [p]
  have hx := (point_coordinates_lt R).1
  have hf : (pointFinite R).toNat ≤ 1 := by cases pointFinite R <;> decide
  unfold pairCode
  omega

theorem pairCode_neg (C : Point) : pairCode (-C) = pairCode C := by
  cases C with
  | zero => rfl
  | @some x y h =>
    rw [WeierstrassCurve.Affine.Point.neg_some]
    rfl

theorem shortCode_pair (R : Point) : shortCode R = pairCode R + 2 * 2^256 * (pointY R % 2) := by
  unfold shortCode pairCode
  ring

theorem pair_value_eq (R C : Point) :
    (decide (pairCode R = pairCode C) && (yBit R == yBit C)) = pointEqual R C := by
  apply Bool.eq_iff_iff.mpr
  rw [pointEqual_true_iff, ← shortCode_eq_iff, shortCode_pair, shortCode_pair]
  have h1 := pairCode_lt R
  have h2 := pairCode_lt C
  have hyR : pointY R % 2 < 2 := Nat.mod_lt _ (by decide)
  have hyC : pointY C % 2 < 2 := Nat.mod_lt _ (by decide)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, yBit]
  constructor
  · rintro ⟨ha, hb⟩
    rw [ha]
    have : pointY R % 2 = pointY C % 2 := by
      by_cases hr : pointY R % 2 = 1 <;> by_cases hc : pointY C % 2 = 1 <;>
        simp_all <;> omega
    rw [this]
  · intro h
    have ha : pairCode R = pairCode C := by omega
    have hb : pointY R % 2 = pointY C % 2 := by omega
    exact ⟨ha, by rw [hb]⟩

theorem pairSrc_length (L : ControlledPointLayout) (hw : L.Widths) : (pairSrc L).length = 257 := by
  simp [pairSrc, show L.point.x.length = 256 from hw.inputX]

theorem pairWork_length (L : ControlledPointLayout) (hw : L.Widths) :
    (L.dialogPool.take 257).length = 257 := by
  simp [L.dialogPool_length hw]

theorem pairSrc_value (L : ControlledPointLayout) (hw : L.Widths) (R : Point) (s : BasisState)
    (hp : Holds.holds s L.point R) : regValue (pairSrc L) s = pairCode R := by
  have hv := (point_holds L.point R s).mp hp
  change (if s L.point.finite then 1 else 0) + 2 * regValue L.point.x s = _
  rw [hv.1, hv.2.1]
  unfold pairCode
  cases pointFinite R <;> rfl

theorem yLow_mem (L : ControlledPointLayout) (hw : L.Widths) : yLow L ∈ L.point.y := by
  have hl : L.point.y.length = 256 := hw.inputY
  unfold yLow
  cases hy : L.point.y with
  | nil => rw [hy] at hl; simp at hl
  | cons w ys => simp

theorem yLow_value (L : ControlledPointLayout) (hw : L.Widths) (R : Point) (s : BasisState)
    (hp : Holds.holds s L.point R) : s (yLow L) = yBit R := by
  have hv := (point_holds L.point R s).mp hp
  have hl : L.point.y.length = 256 := hw.inputY
  have hy := hv.2.2
  unfold yLow yBit
  cases hc : L.point.y with
  | nil => rw [hc] at hl; simp at hl
  | cons w ys =>
    rw [hc] at hy
    change (if s w then 1 else 0) + 2 * regValue ys s = pointY R at hy
    simp only [List.headD_cons]
    rw [← hy]
    cases s w <;> simp <;> omega

theorem pair_nodup (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (t₁ t₂ : Wire) (ht1 : t₁ ∈ L.inPlaceFlags) (ht2 : t₂ ∈ L.inPlaceFlags) (h12 : t₁ ≠ t₂) :
    (L.control :: yLow L :: t₁ :: t₂ :: (pairSrc L ++ L.dialogPool.take 257)).Nodup := by
  have sep := dialogFlag_separation L hn
  have hc1 : L.control ≠ t₁ := fun h => (List.nodup_cons.mp sep).1 (h ▸ ht1)
  have hc2 : L.control ≠ t₂ := fun h => (List.nodup_cons.mp sep).1 (h ▸ ht2)
  have hA : (L.control :: t₁ :: (PointAddLayout.pointWires L.point ++ L.dialogPool.take 513)).Nodup := by
    simpa only [List.cons_append] using L.dialogPointZero_nodup hn L.control t₁ hc1 (Or.inl rfl) ht1
  have hB : (L.control :: t₂ :: (PointAddLayout.pointWires L.point ++ L.dialogPool.take 513)).Nodup := by
    simpa only [List.cons_append] using L.dialogPointZero_nodup hn L.control t₂ hc2 (Or.inl rfl) ht2
  have a1 := (List.nodup_cons.mp hA).1
  have a2 := (List.nodup_cons.mp (List.nodup_cons.mp hA).2).1
  have b2 := (List.nodup_cons.mp (List.nodup_cons.mp hB).2).1
  have hPP := (List.nodup_cons.mp (List.nodup_cons.mp hA).2).2
  have hsub : (pairSrc L ++ L.dialogPool.take 257).Sublist
      (PointAddLayout.pointWires L.point ++ L.dialogPool.take 513) := by
    have h1 : (pairSrc L).Sublist (PointAddLayout.pointWires L.point) := by
      simp only [pairSrc, PointAddLayout.pointWires]
      exact List.sublist_append_left _ _
    have h2 : (L.dialogPool.take 257).Sublist (L.dialogPool.take 513) := by
      have he : L.dialogPool.take 257 = (L.dialogPool.take 513).take 257 := by
        rw [List.take_take]; rfl
      rw [he]; exact List.take_sublist _ _
    exact h1.append h2
  have sub := hsub.subset
  have hyPW : yLow L ∈ PointAddLayout.pointWires L.point := by
    simp [PointAddLayout.pointWires, yLow_mem L hw]
  have hyP : yLow L ∈ PointAddLayout.pointWires L.point ++ L.dialogPool.take 513 :=
    List.mem_append.mpr (Or.inl hyPW)
  have hPWnd := (List.nodup_append.mp hPP)
  have hy_notsrc : yLow L ∉ pairSrc L := by
    intro h
    have hnd : (pairSrc L ++ L.point.y).Nodup := by
      simpa only [pairSrc, PointAddLayout.pointWires, List.cons_append] using hPWnd.1
    exact (List.nodup_append.mp hnd).2.2 _ h _ (yLow_mem L hw) rfl
  have h2' : (L.dialogPool.take 257).Sublist (L.dialogPool.take 513) := by
    have he : L.dialogPool.take 257 = (L.dialogPool.take 513).take 257 := by
      rw [List.take_take]; rfl
    rw [he]; exact List.take_sublist _ _
  have hy_notwork : yLow L ∉ L.dialogPool.take 257 := fun h =>
    hPWnd.2.2 _ hyPW _ (h2'.subset h) rfl
  refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_,
    List.nodup_cons.mpr ⟨?_, hPP.sublist hsub⟩⟩⟩⟩
  · intro h
    simp only [List.mem_cons] at h
    rcases h with h | h | h | h
    · exact a1 (List.mem_cons_of_mem _ (h ▸ hyP))
    · exact hc1 h
    · exact hc2 h
    · exact a1 (List.mem_cons_of_mem _ (sub h))
  · intro h
    simp only [List.mem_cons, List.mem_append] at h
    rcases h with h | h | h | h
    · exact a2 (h ▸ hyP)
    · exact b2 (h ▸ hyP)
    · exact hy_notsrc h
    · exact hy_notwork h
  · intro h
    simp only [List.mem_cons] at h
    rcases h with h | h
    · exact h12 h
    · exact a2 (sub h)
  · exact fun h => b2 (sub h)

theorem pairPorts_maps (L : ControlledPointLayout) (hw : L.Widths) :
    (pairPorts L).map ZeroBit.input = pairSrc L ∧
    (pairPorts L).map ZeroBit.work = L.dialogPool.take 257 :=
  zeroPorts_maps _ _ ((pairSrc_length L hw).trans (pairWork_length L hw).symm)

theorem pairPorts_length (L : ControlledPointLayout) (hw : L.Widths) : (pairPorts L).length = 257 := by
  have h := congrArg List.length (pairPorts_maps L hw).1
  simpa only [List.length_map, pairSrc_length L hw] using h

theorem pairEqual_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (t₁ t₂ : Wire) (ht1 : t₁ ∈ L.inPlaceFlags) (ht2 : t₂ ∈ L.inPlaceFlags) (h12 : t₁ ≠ t₂)
    (e₁ e₂ : Bool) (C D R : Point) (s : State) (m : List Bool)
    (hp : Holds.holds s.basis L.point R) (hz : regValue (L.dialogPool.take 257) s.basis = 0) :
    run (pairEqual L t₁ t₂ e₁ e₂ C D) m s =
      ⟨s.phase, pairEffect (yLow L) t₁ t₂ e₁ (yBit C) e₂ (yBit D)
        (s.basis L.control && decide (pairCode R = pairCode C)) s.basis⟩ := by
  have hnd := pair_nodup L hw hn t₁ t₂ ht1 ht2 h12
  have hn4 := hnd
  simp only [List.nodup_cons, List.mem_cons, List.mem_append, not_or] at hn4
  obtain ⟨⟨hcy, hc1, hc2, hcs, hcw⟩, ⟨hy1, hy2, hys, hyw⟩, ⟨h12', h1s, h1w⟩, ⟨h2s, h2w⟩, hsw⟩ := hn4
  have hsrc : (pairSrc L).Nodup := (List.nodup_append.mp hsw).1
  have hdisj : ∀ q ∈ L.dialogPool.take 257, q ∉ pairSrc L := by
    intro q hq hs
    exact (List.nodup_append.mp hsw).2.2 q hs q hq rfl
  have hmaps := pairPorts_maps L hw
  have hperm := zeroPorts_perm (pairSrc L) (L.dialogPool.take 257)
    ((pairSrc_length L hw).trans (pairWork_length L hw).symm)
  have hchain : (L.control :: yLow L :: t₁ :: t₂ :: (pairPorts L).flatMap ZeroBit.wires).Nodup :=
    ((((hperm.cons _).cons _).cons _).cons _).nodup_iff.mpr hnd
  have hk : pairCode C < 2^(pairSrc L).length := by
    rw [pairSrc_length L hw, show (257:ℕ) = 256 + 1 from rfl, Nat.pow_succ, mul_comm]
    exact pairCode_lt C
  have hval : regValue (pairSrc L) s.basis = pairCode R := pairSrc_value L hw R s.basis hp
  obtain ⟨hup, hue, huv⟩ := xorConstant_correct (pairSrc L) hsrc (pairCode C) hk s m
  generalize hu : run (xorConstant (pairSrc L) (pairCode C)) m s = u at hup hue huv
  have hwork (b : ZeroBit) (hb : b ∈ pairPorts L) : b.work ∈ L.dialogPool.take 257 := by
    rw [← hmaps.2]; exact List.mem_map.mpr ⟨b, hb, rfl⟩
  have huz : ∀ b ∈ pairPorts L, u.basis b.work = false := by
    intro b hb
    rw [hue _ (hdisj _ (hwork b hb))]
    exact (regValue_zero _ _).mp hz _ (hwork b hb)
  have hh := zeroWith_pair_run (yLow L) t₁ t₂ e₁ (yBit C) e₂ (yBit D) L.control (pairPorts L)
    hchain u m huz
  have hall : (pairPorts L).all (fun b => !u.basis b.input) =
      decide (regValue (pairSrc L) s.basis = pairCode C) := by
    apply Bool.eq_iff_iff.mpr
    rw [List.all_eq_true]
    simp only [Bool.not_eq_true']
    have heq : (∀ b ∈ pairPorts L, u.basis b.input = false) ↔ regValue (pairSrc L) u.basis = 0 := by
      rw [regValue_zero, ← hmaps.1]
      simp
    rw [heq, huv]
    simp
  have hcu : u.basis L.control = s.basis L.control := hue _ hcs
  rw [hall, hcu, hval] at hh
  have hcnt := (zeroWith_counts (pairTail (yLow L) t₁ t₂ e₁ (yBit C) e₂ (yBit D)) (e₁.toNat + e₂.toNat)
    (pairTail_counts (yLow L) t₁ t₂ e₁ (yBit C) e₂ (yBit D)) L.control (pairPorts L)).2
  rw [pairPorts_length L hw] at hcnt
  rw [pairEqual, run_append, run_take, run_append, run_take]
  simp only [measurementCount_append, (xorConstant_counts _ _).2, hcnt, Nat.zero_add, List.drop_zero]
  rw [hu, hh]
  generalize hvdef : (⟨u.phase, pairEffect (yLow L) t₁ t₂ e₁ (yBit C) e₂ (yBit D)
    (s.basis L.control && decide (pairCode R = pairCode C)) u.basis⟩ : State) = v
  have hvb : v.basis = pairEffect (yLow L) t₁ t₂ e₁ (yBit C) e₂ (yBit D)
      (s.basis L.control && decide (pairCode R = pairCode C)) u.basis := by rw [← hvdef]
  have hvph : v.phase = u.phase := by rw [← hvdef]
  obtain ⟨hvp, hve, hvv⟩ := xorConstant_correct (pairSrc L) hsrc (pairCode C) hk v (m.drop 257)
  have hvs : regValue (pairSrc L) v.basis = regValue (pairSrc L) u.basis := by
    rw [hvb]
    apply regValue_congr
    intro w hw'
    have hw1 : w ≠ t₁ := fun he => h1s (he ▸ hw')
    have hw2 : w ≠ t₂ := fun he => h2s (he ▸ hw')
    simp [pairEffect, writeBit, Function.update_apply, hw1, hw2]
  have hrestore : regValue (pairSrc L) (run (xorConstant (pairSrc L) (pairCode C)) (m.drop 257) v).basis =
      regValue (pairSrc L) s.basis := by
    rw [hvv, hvs, huv, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  apply (show ∀ a b : State, a.phase = b.phase → a.basis = b.basis → a = b from
    fun ⟨ap, ab⟩ ⟨bp, bb⟩ hp hb => by cases hp; cases hb; rfl)
  · rw [hvp, hvph, hup]
  · funext w
    by_cases hw' : w ∈ pairSrc L
    · rw [(regValue_eq_iff (pairSrc L) _ _).mp hrestore w hw']
      have hw1 : w ≠ t₁ := fun he => h1s (he ▸ hw')
      have hw2 : w ≠ t₂ := fun he => h2s (he ▸ hw')
      simp [pairEffect, writeBit, Function.update_apply, hw1, hw2]
    · rw [hve w hw', hvb]
      have hyu : u.basis (yLow L) = s.basis (yLow L) := hue _ hys
      have h1u : u.basis t₁ = s.basis t₁ := hue _ h1s
      have h2u : u.basis t₂ = s.basis t₂ := hue _ h2s
      have hwu : u.basis w = s.basis w := hue _ hw'
      simp only [pairEffect, writeBit, Function.update_apply, hyu, h1u, h2u]
      split_ifs <;> simp [hwu]

section
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem pairBoundary (R C : Point) (b : Bool) (f : BasisState) (t₁ t₂ : Wire)
    (ht1 : t₁ ∈ L.inPlaceFlags) (ht2 : t₂ ∈ L.inPlaceFlags) (h12 : t₁ ≠ t₂)
    (e₁ e₂ B₁ B₂ : Bool) (hB₁ : B₁ = (b && e₁)) (hB₂ : B₂ = (b && e₂)) :
    Triple (PointDialogBoundary L R b f) (pairEqual L t₁ t₂ e₁ e₂ C (-C))
      (PointDialogBoundary L R b (writeBit (writeBit f t₁ (f t₁ ^^ (B₁ && pointEqual R C))) t₂
        (f t₂ ^^ (B₂ && pointEqual R (-C))))) := by
  intro s m v
  have hclean : regValue (L.dialogPool.take 257) s.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp v.clean q (List.take_subset _ _ hq))
  have hh := pairEqual_correct L hw hn t₁ t₂ ht1 ht2 h12 e₁ e₂ C (-C) R s m v.point hclean
  have hy := yLow_value L hw R s.basis v.point
  have hb := v.control
  have k1 : (e₁ && (s.basis L.control && decide (pairCode R = pairCode C)) &&
      (s.basis (yLow L) == yBit C)) = (B₁ && pointEqual R C) := by
    rw [hB₁, hy, hb, ← pair_value_eq R C]
    generalize decide (pairCode R = pairCode C) = d
    generalize (yBit R == yBit C) = g
    cases e₁ <;> cases b <;> cases d <;> cases g <;> rfl
  have k2 : (e₂ && (s.basis L.control && decide (pairCode R = pairCode C)) &&
      (s.basis (yLow L) == yBit (-C))) = (B₂ && pointEqual R (-C)) := by
    rw [hB₂, hy, hb, ← pair_value_eq R (-C), pairCode_neg]
    generalize decide (pairCode R = pairCode C) = d
    generalize (yBit R == yBit (-C)) = g
    cases e₂ <;> cases b <;> cases d <;> cases g <;> rfl
  have hfin : (run (pairEqual L t₁ t₂ e₁ e₂ C (-C)) m s).basis =
      writeBit (writeBit s.basis t₁ (s.basis t₁ ^^ (B₁ && pointEqual R C))) t₂
        (s.basis t₂ ^^ (B₂ && pointEqual R (-C))) := by
    rw [hh]
    simp only [pairEffect]
    rw [k1, k2]
  refine ⟨by rw [hh], v.withFlags hn ?_ ?_⟩
  · intro q hq
    rw [hfin]
    simp only [writeBit, Function.update_apply]
    by_cases q2 : q = t₂
    · subst q2; simp [v.flags _ ht2]
    · by_cases q1 : q = t₁
      · subst q1; simp [q2, v.flags _ ht1]
      · simp [q1, q2, v.flags q hq]
  · intro q hq
    rw [hfin]
    have q1 : q ≠ t₁ := fun he => hq (he ▸ ht1)
    have q2 : q ≠ t₂ := fun he => hq (he ▸ ht2)
    simp [writeBit, q1, q2]

/-- Input side: `double ^= K ∧ R = C` and `genericSelect ^= b ∧ R = -C`. -/
theorem pairFlag_input (R C : Point) (cy : Fp) (b O D I G E H K : Bool)
    (hK : K = (b && decide (cy ≠ -cy))) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (pairEqual L L.doubleSelect L.genericSelect (decide (cy ≠ -cy)) true C (-C))
      (PointDialogBoundary L R b
        (dialogFlagState L O (D ^^ (K && pointEqual R C)) (I ^^ (b && pointEqual R (-C))) G E H K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := pairBoundary L hw hn R C b (dialogFlagState L O D I G E H K) L.doubleSelect L.genericSelect
    (by simp [inPlaceFlags]) (by simp [inPlaceFlags]) (by tauto)
    (decide (cy ≠ -cy)) true K b hK (by simp)
  simp only [hr.2.1, hr.2.2.1] at hh
  refine hh.conseq (fun _ h => h) (fun _ h => h.congrFlags ?_)
  intro q hq
  have u1 := (dialogFlagState_update L hn O D I G E H K (D ^^ (K && pointEqual R C))).2.1
  have u2 := (dialogFlagState_update L hn O (D ^^ (K && pointEqual R C)) I G E H K
    (I ^^ (b && pointEqual R (-C)))).2.2.1
  rw [← u2 q hq]
  simp only [writeBit, Function.update_apply]
  rw [← u1 q hq]
  simp only [writeBit, Function.update_apply]

/-- Output side: `infinitySelect ^= b ∧ S = C` and `equalNegY ^= E ∧ S = -C`. -/
theorem pairFlag_output (S C : Point) (en : Bool) (b O D I G E H K : Bool)
    (hE : E = (b && en)) :
    Triple (PointDialogBoundary L S b (dialogFlagState L O D I G E H K))
      (pairEqual L L.infinitySelect L.core.equalNegY true en C (-C))
      (PointDialogBoundary L S b
        (dialogFlagState L (O ^^ (b && pointEqual S C)) D I G E (H ^^ (E && pointEqual S (-C))) K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := pairBoundary L hw hn S C b (dialogFlagState L O D I G E H K) L.infinitySelect L.core.equalNegY
    (by simp [inPlaceFlags]) (by simp [inPlaceFlags]) (by tauto)
    true en b E (by simp) hE
  simp only [hr.1, hr.2.2.2.2.2.1] at hh
  refine hh.conseq (fun _ h => h) (fun _ h => h.congrFlags ?_)
  intro q hq
  have u1 := (dialogFlagState_update L hn O D I G E H K (O ^^ (b && pointEqual S C))).1
  have u2 := (dialogFlagState_update L hn (O ^^ (b && pointEqual S C)) D I G E H K
    (H ^^ (E && pointEqual S (-C)))).2.2.2.2.2.1
  rw [← u2 q hq]
  simp only [writeBit, Function.update_apply]
  rw [← u1 q hq]
  simp only [writeBit, Function.update_apply]

end

theorem pairEqual_counts (L : ControlledPointLayout) (hw : L.Widths) (t₁ t₂ : Wire) (e₁ e₂ : Bool)
    (C D : Point) :
    toffoliCount (pairEqual L t₁ t₂ e₁ e₂ C D) ≤ 259 ∧
    measurementCount (pairEqual L t₁ t₂ e₁ e₂ C D) = 257 := by
  have h := zeroWith_counts (pairTail (yLow L) t₁ t₂ e₁ (yBit C) e₂ (yBit D)) (e₁.toNat + e₂.toNat)
    (pairTail_counts (yLow L) t₁ t₂ e₁ (yBit C) e₂ (yBit D)) L.control (pairPorts L)
  rw [pairPorts_length L hw] at h
  have x := xorConstant_counts (pairSrc L) (pairCode C)
  simp only [pairEqual, toffoliCount_append, measurementCount_append, x.1, x.2, h.1, h.2]
  have h1 : e₁.toNat ≤ 1 := by cases e₁ <;> decide
  have h2 : e₂.toNat ≤ 1 := by cases e₂ <;> decide
  refine ⟨?_, ?_⟩
  · omega
  · simp

theorem pairTail_wires (y t₁ t₂ : Wire) (e₁ a₁ e₂ a₂ : Bool) (w : Wire) :
    wires (pairTail y t₁ t₂ e₁ a₁ e₂ a₂ w) ⊆ ({w, y, t₁, t₂} : Finset Wire) := by
  intro q hq
  cases e₁ <;> cases e₂ <;> cases a₁ <;> cases a₂ <;>
    simp [pairTail, bitTest, zeroFlag, wires, Instr.wires, wires_append] at hq ⊢ <;> tauto

theorem zeroWith_pair_wires (y t₁ t₂ : Wire) (e₁ a₁ e₂ a₂ : Bool) (c : Wire) (bs : List ZeroBit) :
    wires (zeroWith (pairTail y t₁ t₂ e₁ a₁ e₂ a₂) c bs) ⊆
      (c :: y :: t₁ :: t₂ :: bs.flatMap ZeroBit.wires).toFinset := by
  induction bs generalizing c with
  | nil =>
    intro q hq
    have := pairTail_wires y t₁ t₂ e₁ a₁ e₂ a₂ c (by simpa [zeroWith] using hq)
    simp at this ⊢; tauto
  | cons b bs ih =>
    intro q hq
    simp only [zeroWith, wires_append, Finset.mem_union] at hq
    have hsub := @ih b.work q
    simp [chainAnd, chainErase, wires, Instr.wires, correctionWires, ZeroBit.wires] at hq hsub ⊢
    rcases hq with ((h | h | h) | h) | (h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · rcases hsub h with h' | h' | h' | h' | h'
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h')))))
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr (Or.inl h'))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h')))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h')))))
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem pairEqual_wires (L : ControlledPointLayout) (hw : L.Widths) (t₁ t₂ : Wire) (e₁ e₂ : Bool)
    (C D : Point) :
    wires (pairEqual L t₁ t₂ e₁ e₂ C D) ⊆
      (L.control :: yLow L :: t₁ :: t₂ :: (pairSrc L ++ L.dialogPool.take 257)).toFinset := by
  have hperm := zeroPorts_perm (pairSrc L) (L.dialogPool.take 257)
    ((pairSrc_length L hw).trans (pairWork_length L hw).symm)
  have hx := xorConstant_wires_subset (pairSrc L) (pairCode C)
  have hz := zeroWith_pair_wires (yLow L) t₁ t₂ e₁ (yBit C) e₂ (yBit D) L.control (pairPorts L)
  intro q hq
  simp only [pairEqual, wires_append, Finset.mem_union] at hq
  simp only [List.mem_toFinset, List.mem_cons, List.mem_append]
  rcases hq with (h | h) | h
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_toFinset.mp (hx h))))))
  · have h' := hz h
    simp only [List.mem_toFinset, List.mem_cons] at h'
    rcases h' with h' | h' | h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h')))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (List.mem_append.mp (hperm.subset h')))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_toFinset.mp (hx h))))))

theorem pairEqual_sites (L : ControlledPointLayout) (hw : L.Widths) (t₁ t₂ : Wire)
    (ht1 : t₁ ∈ L.inPlaceFlags) (ht2 : t₂ ∈ L.inPlaceFlags) (e₁ e₂ : Bool) (C D : Point) :
    wires (pairEqual L t₁ t₂ e₁ e₂ C D) ⊆ (CompressedPointDialog.sites L).toFinset := by
  intro q hq
  have h := pairEqual_wires L hw t₁ t₂ e₁ e₂ C D hq
  have hy := yLow_mem L hw
  have hpool := CompressedPointDialog.prefix_small L hw 257 (by decide)
  simp only [List.mem_toFinset, List.mem_cons, List.mem_append, pairSrc] at h
  simp only [CompressedPointDialog.sites, CompressedPointSquare.residents,
    PointAddLayout.pointWires, List.mem_toFinset, List.mem_append, List.mem_cons]
  rcases h with rfl | rfl | rfl | rfl | (rfl | h) | h
  · simp
  · simp [hy]
  · simp [ht1]
  · simp [ht2]
  · simp
  · simp [h]
  · exact Or.inr (hpool h)

theorem pairEqual_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (t₁ t₂ : Wire) (ht1 : t₁ ∈ L.inPlaceFlags) (ht2 : t₂ ∈ L.inPlaceFlags) (h12 : t₁ ≠ t₂)
    (e₁ e₂ : Bool) (C D : Point) : GatePhysical (pairEqual L t₁ t₂ e₁ e₂ C D) := by
  have hnd := pair_nodup L hw hn t₁ t₂ ht1 ht2 h12
  have hperm := zeroPorts_perm (pairSrc L) (L.dialogPool.take 257)
    ((pairSrc_length L hw).trans (pairWork_length L hw).symm)
  have hchain : (L.control :: yLow L :: t₁ :: t₂ :: (pairPorts L).flatMap ZeroBit.wires).Nodup :=
    ((((hperm.cons _).cons _).cons _).cons _).nodup_iff.mpr hnd
  simp only [pairEqual, gatePhysical_append]
  refine ⟨⟨xorConstant_physical _ _, ?_⟩, xorConstant_physical _ _⟩
  clear hnd hperm
  generalize L.control = c at hchain ⊢
  generalize pairPorts L = bs at hchain ⊢
  generalize yLow L = y at hchain ⊢
  induction bs generalizing c with
  | nil =>
    simp only [List.flatMap_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or,
      or_false] at hchain
    obtain ⟨⟨hcy, hc1, hc2⟩, ⟨hy1, hy2⟩, -, -⟩ := hchain
    simp only [zeroWith]
    cases e₁ <;> cases e₂ <;> cases (yBit C) <;> cases (yBit D) <;>
      simp [pairTail, bitTest, zeroFlag, GatePhysical, PhysicalInstr, ProperGate, gatePhysical_append,
        hc1, hc2, hy1, hy2]
  | cons b bs ih =>
    have hnames : (c::y::t₁::t₂::b.input::b.work::bs.flatMap ZeroBit.wires).Nodup := hchain
    have hni := hnames
    simp only [List.nodup_cons, List.mem_cons, not_or] at hni
    obtain ⟨⟨hcy, hc1, hc2, hci, hcw, hcR⟩, ⟨hy1, hy2, hyi, hyw, hyR⟩, ⟨h12, h1i, h1w, h1R⟩,
      ⟨h2i, h2w, h2R⟩, ⟨hiw, hiR⟩, hwR, hR⟩ := hni
    have hchild : (b.work::y::t₁::t₂::bs.flatMap ZeroBit.wires).Nodup := by
      simp only [List.nodup_cons, List.mem_cons, not_or]
      exact ⟨⟨Ne.symm hyw, Ne.symm h1w, Ne.symm h2w, hwR⟩, ⟨hy1, hy2, hyR⟩, ⟨h12, h1R⟩, h2R, hR⟩
    simp only [zeroWith, gatePhysical_append]
    exact ⟨⟨by simp [chainAnd, GatePhysical, PhysicalInstr, ProperGate, hcw, hiw], ih b.work hchild⟩,
      by simp [chainErase, GatePhysical, PhysicalInstr, ProperGate]⟩

theorem zeroWith_pair_slots (y t₁ t₂ : Wire) (e₁ a₁ e₂ a₂ : Bool) (c : Wire) (bs : List ZeroBit) :
    gateSlots (zeroWith (pairTail y t₁ t₂ e₁ a₁ e₂ a₂) c bs) ≤ 7 * bs.length + 6 := by
  induction bs generalizing c with
  | nil =>
    cases e₁ <;> cases e₂ <;> cases a₁ <;> cases a₂ <;>
      simp [zeroWith, pairTail, bitTest, zeroFlag, gateSlots_append, gateSlots_cons, instructionSlots]
  | cons b bs ih =>
    have h := ih b.work
    simp only [zeroWith, chainAnd, chainErase, gateSlots_append, List.length_cons]
    simp only [gateSlots_cons, gateSlots_nil, instructionSlots, List.length_nil, List.length_cons] at h ⊢
    omega

theorem pairEqual_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths) (t₁ t₂ : Wire)
    (e₁ e₂ : Bool) (C D : Point) : gateSlots (pairEqual L t₁ t₂ e₁ e₂ C D) ≤ 2319 := by
  have hx := Baselines.xorConstant_gateSlots_le (pairSrc L) (pairCode C)
  have hz := zeroWith_pair_slots (yLow L) t₁ t₂ e₁ (yBit C) e₂ (yBit D) L.control (pairPorts L)
  rw [pairSrc_length L hw] at hx
  rw [pairPorts_length L hw] at hz
  simp only [pairEqual, gateSlots_append]
  omega

end ECDSAAdd.Entrant
end

-- source: ECDSAAdd/Submission/Entrant/Program.lean
noncomputable section

/-! The Skywalk finite-addend circuit with both infinity comparisons replaced
by `zeroFlag`.  Every other block is the unchanged Skywalk block. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic Secp256k1 ControlledPointLayout CompressedPointDialog

/-- Classical enable bit of the exception comparison (as in `pointDialogExceptionEnable`). -/
def exceptionBit (C : Point) : Bool :=
  !pointEqual (dialogExceptionPoint C) 0 && !pointEqual (dialogExceptionPoint C) C &&
    !pointEqual (dialogExceptionPoint C) (-C)

def finiteProgram (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  pointInPlaceDoubleEnable L cy ++ pointDialogExceptionEnable L C ++
  zeroFlag L.point.finite L.control L.infinitySelect ++
  pairEqual L L.doubleSelect L.genericSelect (decide (cy≠-cy)) true C (-C) ++
  shortEqual L L.core.equalX L.core.equalNegY (dialogExceptionPoint C) ++
  pointDialogGenericFlag L ++ pointCompressedDialogGeneric L cx cy ++ pointDialogCorners L C ++
  pointDialogGenericFlag L ++
  pairEqual L L.infinitySelect L.core.equalNegY true (exceptionBit C) C (-C) ++
  shortEqual L L.core.double L.doubleSelect (C+C) ++
  zeroFlag L.point.finite L.control L.genericSelect ++
  pointDialogExceptionEnable L C ++ pointInPlaceDoubleEnable L cy

section Spec
attribute [local irreducible] run wires shortEqual pairEqual pointCompressedDialogGeneric pointDialogGeneric
  MappedCompressed.pointCompressedArithmetic CompressedPointSquare.computableProgram

private theorem equal_simp [DecidableEq Point] (R C : Point) : pointEqual R C=decide (R=C) := by
  simp only [pointEqual,pointCode_injective.eq_iff]

theorem finiteProgram_spec (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) :
    Triple (PointDialogBoundary L R b (fun _=>false)) (finiteProgram L (.some hc) cx cy)
      (PointDialogBoundary L (if b then R+.some hc else R) b (fun _=>false)) := by
  classical
  let C : Point := .some hc
  let O := dialogInfinity b R
  let D := dialogDouble b R C
  let I := dialogInversePoint b R C
  let H := dialogException b R C
  let G := dialogOrdinary b R C
  let E := b && decide (dialogExceptionEnabled C)
  let K := b && decide (cy≠-cy)
  let S := if b then R+C else R
  have hC : C≠0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  have hK : K=(b && decide (C≠-C)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [K,Bool.and_eq_true,decide_eq_true_eq]
    exact and_congr_right (fun _=>doubling_enabled_iff hc)
  have hE : (!pointEqual (dialogExceptionPoint C) 0 && !pointEqual (dialogExceptionPoint C) C &&
      !pointEqual (dialogExceptionPoint C) (-C))=decide (dialogExceptionEnabled C) := by
    simp [equal_simp,dialogExceptionEnabled,Bool.and_assoc]
  have hO : (b && pointEqual R 0)=O := by simp only [O,dialogInfinity,equal_simp]
  have hD : (K && pointEqual R C)=D := by rw [hK]; simp only [D,dialogDouble,equal_simp]
  have hI : (b && pointEqual R (-C))=I := by simp only [I,dialogInversePoint,equal_simp]
  have hH : (E && pointEqual R (dialogExceptionPoint C))=H := by
    simp [E,H,dialogException,dialogExceptionEnabled,equal_simp]
  have h0 := dialogFlag_doubleEnable L hn R b false false false false false false false cy
  simp only [Bool.false_xor] at h0
  have h1 := dialogFlag_exceptionEnable L hn R b false false false false false false K C
  rw [hE,Bool.false_xor] at h1
  have h2 := zeroFlag_equalO L hn R b false false false false E false K
  rw [hO,Bool.false_xor] at h2
  have h3 := pairFlag_input L hw hn R C cy b O false false false E false K rfl
  rw [hD,hI,Bool.false_xor,Bool.false_xor] at h3
  have h5 := shortFlag_equalH L hw hn R (dialogExceptionPoint C) b O D I false E false K
  rw [hH,Bool.false_xor] at h5
  have h6 := dialogFlag_generic L hw hn R b O D I false E H K
  simp only [Bool.false_xor] at h6
  have read := dialogFlagState_read L hn O D I G E H K
  have h7 := boundary_generic L hw hn R b (dialogFlagState L O D I G E H K) hc
    (fun hg => ((dialogOrdinary_true b R C hC).mp (read.2.2.2.1.symm.trans hg)).2)
  rw [read.2.2.2.1] at h7
  have h8 := dialogBoundary_corners L hw hn R C hC b (dialogFlagState L O D I G E H K)
    read.1 read.2.1 read.2.2.1 read.2.2.2.2.2.1
  have h9 := dialogFlag_generic L hw hn S b O D I G E H K
  have hgclear : (((((G ^^ b) ^^ O) ^^ D) ^^ I) ^^ H)=false := by
    dsimp only [G,dialogOrdinary,O,D,I,H]
    generalize dialogInfinity b R=o,dialogDouble b R C=d,dialogInversePoint b R C=i,
      dialogException b R C=h
    cases b <;> cases o <;> cases d <;> cases i <;> cases h <;> rfl
  rw [hgclear] at h9
  have hf := dialogFlags_output b R C
  have heout : (E && pointEqual S (-C))=H := by
    simpa [E,H,S,dialogExceptionEnabled,equal_simp] using hf.2.2.2
  have h10 := pairFlag_output L hw hn S C (exceptionBit C) b O D I false E H K (by
    simp only [E, exceptionBit, hE])
  rw [heout,Bool.xor_self] at h10
  simp only [equal_simp] at h10
  rw [hf.1,Bool.xor_self] at h10
  have h11 := shortFlag_equalD L hw hn S (C+C) b false D I false E false K
  have hdo : (K && pointEqual S (C+C))=D := by
    rw [hK]; simpa only [equal_simp] using hf.2.1
  rw [hdo,Bool.xor_self] at h11
  have h12 := zeroFlag_equalI L hn S b false false I false E false K
  simp only [equal_simp] at h12
  rw [hf.2.2.1,Bool.xor_self] at h12
  have h14 := dialogFlag_exceptionEnable L hn S b false false false false E false K C
  rw [hE,show (E ^^ (b && decide (dialogExceptionEnabled C)))=false from Bool.xor_self E] at h14
  have h15 := dialogFlag_doubleEnable L hn S b false false false false false false K cy
  rw [show (K ^^ (b && decide (cy≠-cy)))=false from Bool.xor_self K] at h15
  have h := ((((((((((((h0.seq h1).seq h2).seq h3).seq h5).seq h6).seq h7).seq h8).seq h9).seq h10).seq h11).seq h12).seq h14).seq h15
  simpa only [finiteProgram,List.append_assoc,dialogFlagState_zero] using h

end Spec

section Support
attribute [local irreducible] wires pointCompressedDialogGeneric

theorem zeroFlag_wires (f c t : Wire) : wires (zeroFlag f c t) = {f, c, t} := by
  ext q
  simp only [zeroFlag, wires, Instr.wires, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton, Finset.notMem_empty]
  tauto

/-- Support is contained in the unchanged Skywalk static-site certificate. -/
theorem finiteProgram_support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (cx cy : Fp) :
    wires (finiteProgram L C cx cy) ⊆ (CompressedPointDialog.sites L).toFinset := by
  have h := CompressedPointDialog.finite_support L hw hn C cx cy
  simp only [pointCompressedDialogFinite, wires_append, Finset.union_subset_iff] at h
  have hz (t : Wire) (ht : t ∈ L.inPlaceFlags) :
      wires (zeroFlag L.point.finite L.control t) ⊆ (CompressedPointDialog.sites L).toFinset := by
    rw [zeroFlag_wires]
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    simp only [CompressedPointDialog.sites, CompressedPointSquare.residents,
      PointAddLayout.pointWires, List.mem_toFinset, List.mem_append, List.mem_cons]
    rcases hq with rfl | rfl | rfl
    · simp
    · simp
    · simp [ht]
  have z1 := hz L.infinitySelect (by simp [inPlaceFlags])
  have z2 := hz L.genericSelect (by simp [inPlaceFlags])
  have q3 := shortEqual_wires_subset L hw L.core.equalX L.core.equalNegY (dialogExceptionPoint C)
    (pointCode (dialogExceptionPoint C))
  have q5 := shortEqual_wires_subset L hw L.core.double L.doubleSelect (C+C) (pointCode (C+C))
  have p1 := pairEqual_sites L hw L.doubleSelect L.genericSelect (by simp [inPlaceFlags])
    (by simp [inPlaceFlags]) (decide (cy≠-cy)) true C (-C)
  have p2 := pairEqual_sites L hw L.infinitySelect L.core.equalNegY (by simp [inPlaceFlags])
    (by simp [inPlaceFlags]) true (exceptionBit C) C (-C)
  simp only [finiteProgram, wires_append, Finset.union_subset_iff]
  have r (A B : Program) (hAB : wires A ⊆ wires B) :
      wires B ⊆ (CompressedPointDialog.sites L).toFinset →
        wires A ⊆ (CompressedPointDialog.sites L).toFinset := fun h' => hAB.trans h'
  have r3 := r _ _ q3
  have r5 := r _ _ q5
  clear r q3 q5
  tauto

theorem sites_used (L : ControlledPointLayout) (hw : L.Widths) :
    (CompressedPointDialog.sites L).toFinset ⊆ L.dialogUsedWires.toFinset := by
  intro q hq
  exact List.mem_toFinset.mpr (CompressedPointDialog.sites_subset L hw (List.mem_toFinset.mp hq))

end Support

section Frame
attribute [local irreducible] run wires

private theorem boundary_frame_values (L : ControlledPointLayout) (P : Program)
    (hP : wires P⊆L.dialogUsedWires.toFinset) (R R' : Point) (b : Bool) (s : State) (m : List Bool)
    (hi : PointDialogBoundary L R b (fun _ => false) s.basis)
    (ho : PointDialogBoundary L R' b (fun _ => false) (run P m s).basis)
    (q : Wire) (hp : q∉PointAddLayout.pointWires L.point) : (run P m s).basis q=s.basis q := by
  by_cases hc : q=L.control
  · subst q; exact ho.control.trans hi.control.symm
  by_cases hf : q∈L.inPlaceFlags
  · exact (ho.flags q hf).trans (hi.flags q hf).symm
  by_cases hw : q∈L.dialogPool
  · exact (regValue_eq_iff _ _ _).mp (ho.clean.trans hi.clean.symm) q hw
  apply run_preserves_outside
  apply mt (@hP q)
  simp [dialogUsedWires,hp,hc,hf,hw]

private theorem boundary_work_subset (L : ControlledPointLayout) :
    L.inPlaceFlags++L.dialogPool ⊆ L.work := by
  intro q hq
  have h1 := List.count_pos_iff.mpr hq
  have ht := (List.take_sublist 2613 L.core.pool).count_le q
  apply List.count_pos_iff.mp
  simp only [dialogPool,List.count_append] at h1
  simp only [work,outWork,temporary,inPlaceFlags,selectors,PointAddLayout.work,PointAddLayout.words,
    PointAddLayout.flags,List.flatten_cons,List.flatten_nil,List.append_nil,List.count_append,List.count_cons,List.count_nil] at h1 ht ⊢
  omega

private theorem work_not_point (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.work) : q∉PointAddLayout.pointWires L.point := by
  intro hp
  have hh := List.nodup_iff_count.mp hn q
  have h1 := List.count_pos_iff.mpr hq
  have h2 := List.count_pos_iff.mpr hp
  simp only [ControlledPointLayout.wires,work,outWork,temporary,point,extras,selectors,PointAddLayout.wires,
    List.count_append,List.count_cons,List.count_nil] at hh h1 h2
  omega

theorem finiteProgram_full_spec (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) :
    (Triple (fun st => (Holds.holds st L.control b ∧ Holds.holds st L.point R) ∧ Holds.holds st L.work 0) (finiteProgram L (.some hc) cx cy)
      (fun st => (Holds.holds st L.control b ∧ Holds.holds st L.point (if b then R+.some hc else R)) ∧ Holds.holds st L.work 0)) := by
  intro s m hs
  have hz : regValue L.work s.basis=0 := hs.2
  have clean (q : Wire) (hq : q∈L.inPlaceFlags++L.dialogPool) : s.basis q=false :=
    (regValue_zero _ _).mp hz q (boundary_work_subset L hq)
  have hi : PointDialogBoundary L R b (fun _ => false) s.basis := by
    refine ⟨hs.1.2,hs.1.1,fun q hq => clean q (by simp [hq]),?_⟩
    · exact (regValue_zero _ _).mpr (fun q hq => clean q (by simp [hq]))
  obtain ⟨hp,ho⟩ := finiteProgram_spec L hw hn R hc b s m hi
  refine ⟨hp,⟨ho.control,ho.point⟩,?_⟩
  apply (regValue_zero _ _).mpr
  intro q hq
  have hsup := (finiteProgram_support L hw hn (.some hc) cx cy).trans (sites_used L hw)
  rw [boundary_frame_values L _ hsup R _ b s m hi ho q (work_not_point L hn q hq)]
  exact (regValue_zero _ _).mp hz q hq

end Frame

section Counts

theorem zeroFlag_counts (f c t : Wire) :
    toffoliCount (zeroFlag f c t) = 1 ∧ measurementCount (zeroFlag f c t) = 0 := by
  simp [zeroFlag, toffoliCount, measurementCount]

theorem finiteProgram_counts (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (C : Point) (cx cy : Fp) :
    toffoliCount (finiteProgram L C cx cy)≤2214318 ∧
    measurementCount (finiteProgram L C cx cy)=1554854 := by
  have h := CompressedPointDialog.finite_counts L hw hn C cx cy
  have hpl : (PointAddLayout.pointWires L.point).length=513 := by
    simp only [PointAddLayout.pointWires,List.length_cons,List.length_append,
      show L.point.x.length=256 from hw.inputX,show L.point.y.length=256 from hw.inputY]
  have hzl : L.dialogPointZero.length=513 := by
    have he := (zeroPorts_maps (PointAddLayout.pointWires L.point) (L.dialogPool.take 513)
      (by simp only [List.length_take,L.dialogPool_length hw]; exact hpl)).1
    simpa only [List.length_map,hpl] using congrArg List.length he
  have e1 := equalConstant_counts L.control L.infinitySelect L.dialogPointZero (pointCode 0)
  have e2 := equalConstant_counts L.control L.genericSelect L.dialogPointZero (pointCode 0)
  have e3 := equalConstant_counts L.core.double L.doubleSelect L.dialogPointZero (pointCode C)
  have e4 := equalConstant_counts L.control L.genericSelect L.dialogPointZero (pointCode (-C))
  have e5 := equalConstant_counts L.core.equalX L.core.equalNegY L.dialogPointZero
    (pointCode (dialogExceptionPoint C))
  have e6 := equalConstant_counts L.control L.infinitySelect L.dialogPointZero (pointCode C)
  have e7 := equalConstant_counts L.core.double L.doubleSelect L.dialogPointZero (pointCode (C+C))
  have e8 := equalConstant_counts L.core.equalX L.core.equalNegY L.dialogPointZero (pointCode (-C))
  have s5 := shortEqual_counts L hw L.core.equalX L.core.equalNegY (dialogExceptionPoint C)
  have s7 := shortEqual_counts L hw L.core.double L.doubleSelect (C+C)
  have p1 := pairEqual_counts L hw L.doubleSelect L.genericSelect (decide (cy≠-cy)) true C (-C)
  have p2 := pairEqual_counts L hw L.infinitySelect L.core.equalNegY true (exceptionBit C) C (-C)
  have z1 := zeroFlag_counts L.point.finite L.control L.infinitySelect
  have z2 := zeroFlag_counts L.point.finite L.control L.genericSelect
  rw [hzl] at e1 e2 e3 e4 e5 e6 e7 e8
  simp only [pointCompressedDialogFinite, toffoliCount_append, measurementCount_append] at h
  simp only [finiteProgram, toffoliCount_append, measurementCount_append]
  omega

end Counts

section Physical
open MappedCompressed

theorem zeroFlag_physical (f c t : Wire) (hft : f ≠ t) (hct : c ≠ t) :
    GatePhysical (zeroFlag f c t) := by
  intro i hi
  simp only [zeroFlag, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact trivial
  · exact ⟨hct, hft⟩
  · exact trivial

theorem finiteProgram_physical (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (C : Point) (cx cy : Fp) :
    GatePhysical (finiteProgram L C cx cy) := by
  have orig := skywalkFinite_physical L hw hn C cx cy
  simp only [pointCompressedDialogFinite, gatePhysical_append] at orig
  have hz (t : Wire) (ht : t∈L.inPlaceFlags) : GatePhysical (zeroFlag L.point.finite L.control t) := by
    have hct : L.control ≠ t := by
      have sep := dialogFlag_separation (L:=L) hn
      intro h
      exact (List.nodup_cons.mp sep).1 (h ▸ ht)
    have hnd := L.dialogPointZero_nodup hn L.control t hct (Or.inl rfl) ht
    simp only [PointAddLayout.pointWires, List.cons_append, List.nodup_cons, List.mem_cons,
      List.mem_append, not_or] at hnd
    exact zeroFlag_physical _ _ _ (fun h => hnd.2.1.1 h.symm) hct
  have z1 := hz L.infinitySelect (by simp [inPlaceFlags])
  have z2 := hz L.genericSelect (by simp [inPlaceFlags])
  have sep := dialogFlag_separation (L:=L) hn
  simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
  have q3 := shortEqual_physical L hw hn L.core.equalX L.core.equalNegY (by tauto)
    (Or.inr (by simp [inPlaceFlags])) (by simp [inPlaceFlags]) (dialogExceptionPoint C)
  have q5 := shortEqual_physical L hw hn L.core.double L.doubleSelect (by tauto)
    (Or.inr (by simp [inPlaceFlags])) (by simp [inPlaceFlags]) (C+C)
  have p1 := pairEqual_physical L hw hn L.doubleSelect L.genericSelect (by simp [inPlaceFlags])
    (by simp [inPlaceFlags]) (by tauto) (decide (cy≠-cy)) true C (-C)
  have p2 := pairEqual_physical L hw hn L.infinitySelect L.core.equalNegY (by simp [inPlaceFlags])
    (by simp [inPlaceFlags]) (by tauto) true (exceptionBit C) C (-C)
  simp only [finiteProgram, gatePhysical_append]
  tauto

end Physical

section Slots
open Challenge MappedCompressed Baselines

theorem finiteProgram_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths)
    (C : Point) (cx cy : Fp) : gateSlots (finiteProgram L C cx cy) ≤ 47000000 := by
  have hg := skywalkGeneric_gateSlots_le L hw cx cy
  have hx : L.point.x.length = 256 := hw.inputX
  have hy : L.point.y.length = 256 := hw.inputY
  have hpl : (PointAddLayout.pointWires L.point).length = 513 := by
    simp [PointAddLayout.pointWires, hx, hy]
  have hzl : L.dialogPointZero.length = 513 := by
    have he := (zeroPorts_maps (PointAddLayout.pointWires L.point) (L.dialogPool.take 513)
      (by simp only [List.length_take,L.dialogPool_length hw]; exact hpl)).1
    simpa only [List.length_map,hpl] using congrArg List.length he
  have hz c t k : gateSlots (equalConstant c t L.dialogPointZero k) ≤ 4618 := by
    have h := equalConstant_gateSlots_le c t L.dialogPointZero k
    rw [hzl] at h; exact h
  have hm c P : gateSlots (maskedPointConstant c L.point P) ≤ 513 := by
    have h := maskedPoint_gateSlots_le c L.point P
    rw [hx,hy] at h; exact h
  have he : gateSlots (pointInPlaceDoubleEnable L cy) ≤ 1 := by
    unfold pointInPlaceDoubleEnable; split <;> simp [gateSlots_cons, instructionSlots]
  have hh : gateSlots (pointDialogExceptionEnable L C) ≤ 1 := by
    unfold pointDialogExceptionEnable; split <;> simp [gateSlots_cons, instructionSlots]
  have hf : gateSlots (pointDialogGenericFlag L) = 5 := rfl
  have hzf (t : Wire) : gateSlots (zeroFlag L.point.finite L.control t) = 3 := rfl
  have z2 := pairEqual_gateSlots_le L hw L.doubleSelect L.genericSelect (decide (cy≠-cy)) true C (-C)
  have z4 := shortEqual_gateSlots_le L hw L.core.equalX L.core.equalNegY (dialogExceptionPoint C)
  have z5 := pairEqual_gateSlots_le L hw L.infinitySelect L.core.equalNegY true (exceptionBit C) C (-C)
  have z6 := shortEqual_gateSlots_le L hw L.core.double L.doubleSelect (C+C)
  have m1 := hm L.infinitySelect C
  have m2 := hm L.doubleSelect C
  have m3 := hm L.doubleSelect (C+C)
  have m4 := hm L.genericSelect (-C)
  have m5 := hm L.core.equalNegY (dialogExceptionPoint C)
  have m6 := hm L.core.equalNegY (-C)
  simp only [finiteProgram, pointDialogCorners, pointInPlaceCorners, gateSlots_append, hf, hzf]
  omega

end Slots

end ECDSAAdd.Entrant
end

-- source: ECDSAAdd/Submission/Entrant/QSupport.lean
noncomputable section

/-! Pool site 1801 is never touched.

The published Skywalk support certificate charges the five pool sites
1800–1804 to the arithmetic.  Site 1801 is the image of logical label 2313,
which the arithmetic avoids (`controlled_avoid`).  Every other block works on
resident sites, on a short pool prefix, or (the square) on relabelled sites
below 945.  So the whole finite-addend program lives in the certified site
inventory with site 1801 removed. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed Secp256k1 ControlledPointLayout
attribute [local irreducible] wires controlled kernel pointMeasuredSquareCandidate
  CompressedPointSquare.computableProgram pointRecoveryConstantAdd pointRecoveryReflection

/-- The certified pool inventory without site 1801. -/
def sharedPoolQ (L : ControlledPointLayout) : List Wire :=
  wireBlock L.core.poolWire 0 515 ++ wireBlock L.core.poolWire 684 858 ++
    [L.core.poolWire 1800] ++ wireBlock L.core.poolWire 1802 3

def sitesQ (L : ControlledPointLayout) : List Wire :=
  CompressedPointSquare.residents L ++ sharedPoolQ L

theorem sitesQ_length (L : ControlledPointLayout) (hw : L.Widths) : (sitesQ L).length = 1898 := by
  simp only [sitesQ, sharedPoolQ, List.length_append, wireBlock_length, List.length_cons,
    List.length_nil, CompressedPointSquare.residents_length L hw]

section
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

omit hn in
theorem pool_block (n : Nat) (hn' : n ≤ 2613) : L.dialogPool.take n = wireBlock L.core.poolWire 0 n := by
  simp only [dialogPool, List.take_take, Nat.min_eq_left hn']
  exact (L.core.pool_prefix hw n (by omega)).symm

theorem pool_inj (i j : Nat) (hi : i < 2613) (hj : j < 2613)
    (h : L.core.poolWire i = L.core.poolWire j) : i = j := by
  have nd : (wireBlock L.core.poolWire 0 2613).Nodup := by
    rw [← pool_block L hw 2613 (le_refl _)]
    exact (List.take_sublist _ _).nodup (List.nodup_append.mp (L.dialogUsed_nodup hn)).2.1
  have := List.inj_on_of_nodup_map nd (x := i) (y := j)
    (by simp [List.mem_range'_1]; omega) (by simp [List.mem_range'_1]; omega) h
  exact this

omit hn in
theorem p1801_pool : L.core.poolWire 1801 ∈ L.dialogPool := by
  have : L.core.poolWire 1801 ∈ L.dialogPool.take 2613 := by
    rw [pool_block L hw 2613 (le_refl _)]
    exact List.mem_map.mpr ⟨1801, by simp [List.mem_range'_1], rfl⟩
  exact List.mem_of_mem_take this

theorem p1801_not_resident : L.core.poolWire 1801 ∉ CompressedPointSquare.residents L := by
  intro h
  have dis := (List.nodup_append.mp (L.dialogUsed_nodup hn)).2.2
  exact dis _ (by simpa [dialogUsedWires, CompressedPointSquare.residents] using h) _
    (p1801_pool L hw) rfl

theorem p1801_not_take (k : Nat) (hk : k ≤ 1801) : L.core.poolWire 1801 ∉ L.dialogPool.take k := by
  rw [pool_block L hw k (by omega)]
  intro h
  obtain ⟨i, hi, he⟩ := List.mem_map.mp h
  simp only [List.mem_range'_1] at hi
  have := pool_inj L hw hn i 1801 (by omega) (by omega) he
  omega

/-- Any block confined to residents and a short pool prefix avoids site 1801. -/
theorem p1801_of_subset (P : Program) (k : Nat) (hk : k ≤ 1801)
    (h : wires P ⊆ (CompressedPointSquare.residents L ++ L.dialogPool.take k).toFinset) :
    L.core.poolWire 1801 ∉ wires P := by
  intro hp
  have := List.mem_toFinset.mp (h hp)
  rcases List.mem_append.mp this with h1 | h1
  · exact p1801_not_resident L hw hn h1
  · exact p1801_not_take L hw hn k hk h1

theorem p1801_arith (multiply : Bool) :
    L.core.poolWire 1801 ∉ wires (pointCompressedArithmetic L multiply) := by
  intro hq
  rw [pointCompressedArithmetic, renameProgram_support] at hq
  obtain ⟨old, used, he⟩ := Finset.mem_image.mp hq
  have hslot := controlled_support (!multiply) used
  have hgood := controlled_avoid (!multiply) old used
  have hbase : base 2313 ∈ slots.toFinset := by
    apply slot_mem
    · unfold live; omega
    · unfold CompressedAllocation.omitted; omega
  have himg : pointWireFn L (base 2313) = L.core.poolWire 1801 := by
    simp only [pointWireFn_base, pointIndexWire, show (2313:Nat) < 2314 by omega, if_true]
    simp [skywalkDirectMap, skywalkPointWire]
  have := pointWireFn_injective_slots L hw hn old hslot (base 2313) hbase (he.trans himg.symm)
  subst this
  exact hgood (by simp [base])

theorem p1801_square : L.core.poolWire 1801 ∉ wires (CompressedPointSquare.computableProgram L) := by
  rw [CompressedPointSquare.computableProgram_eq L hw hn]
  intro hq
  rw [CompressedPointSquare.program, renameProgram_support] at hq
  obtain ⟨old, used, he⟩ := Finset.mem_image.mp hq
  have supp := pointMeasuredSquareCandidate_support L hw hn used
  simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at supp
  have res : old ∈ CompressedPointSquare.residents L ∨ old ∈ L.dialogPool.take 776 := by
    simp only [CompressedPointSquare.residents, PointAddLayout.pointWires, inPlaceFlags,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    tauto
  rcases res with res | mem
  · rw [CompressedPointSquare.resident_fixed L hw hn old res] at he
    subst he
    exact p1801_not_resident L hw hn res
  · rw [pool_block L hw 776 (by omega)] at mem
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp mem
    have bound : i < 776 := by simp only [List.mem_range'_1] at hi; omega
    rw [show CompressedPointSquare.poolPermutation L.core.poolWire
        (CompressedPointSquare.layout_bounded_injective L hw hn) (L.core.poolWire i) =
        L.core.poolWire (CompressedPointSquare.indexPermutation i) from
      CompressedPointSquare.wire_apply L.core.poolWire
        (CompressedPointSquare.layout_bounded_injective L hw hn) i (by omega)] at he
    have hb := CompressedPointSquare.index_bounded i (by omega)
    have := pool_inj L hw hn _ 1801 (by omega) (by omega) he
    omega

theorem p1801_constAdd (r : List Wire) (hr : r = L.point.x ∨ r = L.point.y) (k : Fp) :
    L.core.poolWire 1801 ∉ wires (pointDialogConstantAdd L r k) := by
  apply p1801_of_subset L hw hn _ 515 (by omega)
  intro q hq
  have h := List.mem_toFinset.mp (pointRecoveryConstantAdd_support L hw r k hq)
  apply List.mem_toFinset.mpr
  simp only [List.mem_cons, List.mem_append] at h
  simp only [CompressedPointSquare.residents, PointAddLayout.pointWires, inPlaceFlags,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  rcases hr with rfl | rfl <;> tauto

theorem p1801_recovery (cx cy : Fp) :
    L.core.poolWire 1801 ∉ wires (pointRecoveryStage L cx cy) := by
  apply p1801_of_subset L hw hn _ 515 (by omega)
  intro q hq
  have h := List.mem_toFinset.mp (pointRecoveryStage_support L hw cx cy hq)
  apply List.mem_toFinset.mpr
  simp only [recoveryStageSites, List.mem_append] at h
  simp only [CompressedPointSquare.residents, List.mem_append]
  tauto

theorem p1801_generic (cx cy : Fp) :
    L.core.poolWire 1801 ∉ wires (pointCompressedDialogGeneric L cx cy) := by
  have a1 := p1801_constAdd L hw hn L.point.x (Or.inl rfl) (-cx)
  have a2 := p1801_constAdd L hw hn L.point.y (Or.inr rfl) (-cy)
  have a3 := p1801_constAdd L hw hn L.point.x (Or.inl rfl) (3*cx)
  have d := p1801_arith L hw hn false
  have m := p1801_arith L hw hn true
  have s := p1801_square L hw hn
  have r := p1801_recovery L hw hn cx cy
  simp only [pointCompressedDialogGeneric, wires_append, Finset.mem_union, not_or]
  exact ⟨⟨⟨⟨⟨⟨a1, a2⟩, d⟩, s⟩, a3⟩, m⟩, r⟩

omit hw hn in
/-- A site of the original inventory other than pool site 1801 is in `sitesQ`. -/
theorem sitesQ_of_sites (q : Wire) (hq : q ∈ CompressedPointDialog.sites L)
    (hne : q ≠ L.core.poolWire 1801) : q ∈ sitesQ L := by
  simp only [CompressedPointDialog.sites, sitesQ, CompressedPointSquare.sharedPool, sharedPoolQ,
    List.mem_append] at hq ⊢
  rcases hq with h | ((h | h) | h)
  · exact Or.inl h
  · exact Or.inr (Or.inl (Or.inl (Or.inl h)))
  · exact Or.inr (Or.inl (Or.inl (Or.inr h)))
  · have h' : q ∈ [L.core.poolWire 1800, L.core.poolWire 1801, L.core.poolWire 1802,
        L.core.poolWire 1803, L.core.poolWire 1804] := by
      simpa [wireBlock, List.range'_succ] using h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
    rcases h' with h' | h' | h' | h' | h'
    · exact Or.inr (Or.inl (Or.inr (by simp [h'])))
    · exact absurd h' hne
    · exact Or.inr (Or.inr (by simp [wireBlock, List.range'_succ, h']))
    · exact Or.inr (Or.inr (by simp [wireBlock, List.range'_succ, h']))
    · exact Or.inr (Or.inr (by simp [wireBlock, List.range'_succ, h']))

end

end ECDSAAdd.Entrant
end

-- source: ECDSAAdd/Submission/Entrant/QProgram.lean
noncomputable section

/-! The finite-addend program avoids pool site 1801, so its support lies in
`sitesQ`, the certified inventory without that site. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed Secp256k1 ControlledPointLayout
attribute [local irreducible] pointCompressedDialogGeneric shortEqual pairEqual

section
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

omit hw hn in
theorem flag_resident (t : Wire) (ht : t ∈ L.inPlaceFlags) : t ∈ CompressedPointSquare.residents L := by
  simp [CompressedPointSquare.residents, ht]

omit hw hn in
theorem control_resident : L.control ∈ CompressedPointSquare.residents L := by
  simp [CompressedPointSquare.residents]

omit hw hn in
theorem point_resident (q : Wire) (hq : q ∈ PointAddLayout.pointWires L.point) :
    q ∈ CompressedPointSquare.residents L := by
  simp [CompressedPointSquare.residents, hq]

theorem p1801_flags (P : Program) (S : List Wire)
    (hS : ∀ q ∈ S, q = L.control ∨ q ∈ L.inPlaceFlags ∨ q ∈ PointAddLayout.pointWires L.point)
    (h : wires P ⊆ S.toFinset) : L.core.poolWire 1801 ∉ wires P := by
  apply p1801_of_subset L hw hn P 0 (by omega)
  intro q hq
  apply List.mem_toFinset.mpr
  apply List.mem_append_left
  rcases hS q (List.mem_toFinset.mp (h hq)) with rfl | h' | h'
  · exact control_resident L
  · exact flag_resident L q h'
  · exact point_resident L q h'

theorem p1801_short (c t : Wire) (hc : c = L.control ∨ c ∈ L.inPlaceFlags) (ht : t ∈ L.inPlaceFlags)
    (C : Point) : L.core.poolWire 1801 ∉ wires (shortEqual L c t C) := by
  apply p1801_of_subset L hw hn _ 513 (by omega)
  intro q hq
  have h := shortEqual_wires_subset L hw c t C (pointCode C) hq
  rw [equalConstant_wires] at h
  have hp := (zeroPorts_perm (PointAddLayout.pointWires L.point) (L.dialogPool.take 513)
    (by simp [PointAddLayout.pointWires, L.dialogPool_length hw,
      show L.point.x.length = 256 from hw.inputX, show L.point.y.length = 256 from hw.inputY]))
  simp only [List.mem_toFinset, List.mem_cons] at h
  apply List.mem_toFinset.mpr
  rcases h with rfl | rfl | h
  · rcases hc with rfl | hc
    · exact List.mem_append_left _ (control_resident L)
    · exact List.mem_append_left _ (flag_resident L _ hc)
  · exact List.mem_append_left _ (flag_resident L _ ht)
  · rcases List.mem_append.mp (hp.mem_iff.mp (by simpa [dialogPointZero] using h)) with h' | h'
    · exact List.mem_append_left _ (point_resident L _ h')
    · exact List.mem_append_right _ h'

theorem p1801_pair (t₁ t₂ : Wire) (h1 : t₁ ∈ L.inPlaceFlags) (h2 : t₂ ∈ L.inPlaceFlags)
    (e₁ e₂ : Bool) (C D : Point) : L.core.poolWire 1801 ∉ wires (pairEqual L t₁ t₂ e₁ e₂ C D) := by
  apply p1801_of_subset L hw hn _ 257 (by omega)
  intro q hq
  have h := pairEqual_wires L hw t₁ t₂ e₁ e₂ C D hq
  have hy := yLow_mem L hw
  simp only [List.mem_toFinset, List.mem_cons, List.mem_append, pairSrc] at h
  apply List.mem_toFinset.mpr
  rcases h with rfl | rfl | rfl | rfl | (rfl | h) | h
  · exact List.mem_append_left _ (control_resident L)
  · exact List.mem_append_left _ (point_resident L _ (by simp [PointAddLayout.pointWires, hy]))
  · exact List.mem_append_left _ (flag_resident L _ h1)
  · exact List.mem_append_left _ (flag_resident L _ h2)
  · exact List.mem_append_left _ (point_resident L _ (by simp [PointAddLayout.pointWires]))
  · exact List.mem_append_left _ (point_resident L _ (by simp [PointAddLayout.pointWires, h]))
  · exact List.mem_append_right _ h

theorem finiteProgram_p1801 (C : Point) (cx cy : Fp) :
    L.core.poolWire 1801 ∉ wires (finiteProgram L C cx cy) := by
  have e1 : L.core.poolWire 1801 ∉ wires (pointInPlaceDoubleEnable L cy) := by
    apply p1801_flags L hw hn _ [L.control, L.core.double] (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl (by simp [inPlaceFlags])))
    by_cases hh : cy≠-cy <;> simp [pointInPlaceDoubleEnable,hh,wires,Instr.wires]
  have e2 : L.core.poolWire 1801 ∉ wires (pointDialogExceptionEnable L C) := by
    apply p1801_flags L hw hn _ [L.control, L.core.equalX] (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl (by simp [inPlaceFlags])))
    unfold pointDialogExceptionEnable
    split <;> simp [wires,Instr.wires]
  have z (t : Wire) (ht : t ∈ L.inPlaceFlags) :
      L.core.poolWire 1801 ∉ wires (zeroFlag L.point.finite L.control t) := by
    apply p1801_flags L hw hn _ [L.point.finite, L.control, t] (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact Or.inr (Or.inr (by simp [PointAddLayout.pointWires]))
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ht))
    rw [zeroFlag_wires]; intro q hq; simpa using hq
  have g : L.core.poolWire 1801 ∉ wires (pointDialogGenericFlag L) := by
    apply p1801_flags L hw hn _ [L.control, L.infinitySelect, L.doubleSelect, L.genericSelect,
      L.core.generic, L.core.equalNegY] (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      all_goals exact Or.inr (Or.inl (by simp [inPlaceFlags])))
    intro q hq
    simp [pointDialogGenericFlag, pointInPlaceGenericFlag, wires, Instr.wires] at hq
    simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
    tauto
  have m (c : Wire) (hc : c ∈ L.inPlaceFlags) (P : Point) :
      L.core.poolWire 1801 ∉ wires (maskedPointConstant c L.point P) := by
    apply p1801_flags L hw hn _ (c :: PointAddLayout.pointWires L.point) (by
      intro q hq; simp only [List.mem_cons] at hq
      rcases hq with rfl | h
      · exact Or.inr (Or.inl hc)
      · exact Or.inr (Or.inr h))
    exact maskedPointConstant_support c L.point P
  have fS : L.inPlaceFlags = [L.infinitySelect,L.doubleSelect,L.genericSelect,L.core.generic,
      L.core.equalX,L.core.equalNegY,L.core.double] := rfl
  have s1 := p1801_pair L hw hn L.doubleSelect L.genericSelect (by simp [fS]) (by simp [fS])
    (decide (cy≠-cy)) true C (-C)
  have s3 := p1801_short L hw hn L.core.equalX L.core.equalNegY (Or.inr (by simp [fS])) (by simp [fS])
    (dialogExceptionPoint C)
  have s4 := p1801_pair L hw hn L.infinitySelect L.core.equalNegY (by simp [fS]) (by simp [fS])
    true (exceptionBit C) C (-C)
  have s5 := p1801_short L hw hn L.core.double L.doubleSelect (Or.inr (by simp [fS])) (by simp [fS]) (C+C)
  have z1 := z L.infinitySelect (by simp [fS])
  have z2 := z L.genericSelect (by simp [fS])
  have m1 := m L.infinitySelect (by simp [fS]) C
  have m2 := m L.doubleSelect (by simp [fS]) C
  have m3 := m L.doubleSelect (by simp [fS]) (C+C)
  have m4 := m L.genericSelect (by simp [fS]) (-C)
  have m5 := m L.core.equalNegY (by simp [fS]) (dialogExceptionPoint C)
  have m6 := m L.core.equalNegY (by simp [fS]) (-C)
  have gen := p1801_generic L hw hn cx cy
  simp only [finiteProgram, pointDialogCorners, pointInPlaceCorners, wires_append, Finset.mem_union,
    not_or]
  tauto

theorem finiteProgram_supportQ (C : Point) (cx cy : Fp) :
    wires (finiteProgram L C cx cy) ⊆ (sitesQ L).toFinset := by
  intro q hq
  have h1 := List.mem_toFinset.mp (finiteProgram_support L hw hn C cx cy hq)
  have h2 : q ≠ L.core.poolWire 1801 := by
    intro e; subst e; exact finiteProgram_p1801 L hw hn C cx cy hq
  exact List.mem_toFinset.mpr (sitesQ_of_sites L q h1 h2)

end

end ECDSAAdd.Entrant
end
