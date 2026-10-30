import ShorECDLP.Submission.Entrant.Foundation
import ShorECDLP.Submission.Entrant.Catalyst
import ShorECDLP.Submission.«2607_13816».Challenge.Support
import ShorECDLP.Submission.Entrant.Single.Physical
import ShorECDLP.Submission.Entrant.Single.Fourier
import ShorECDLP.Challenge.Official
import ShorECDLP.Submission.«2607_13816».EEA.LengthPrimitiveCounts
import ShorECDLP.Framework.Quantum.InnerProduct
import ShorECDLP.Submission.«2607_13816».EEA.Preprocess
import ShorECDLP.Submission.«2607_13816».EEA.BlockAPrimitiveCounts
import ShorECDLP.Challenge.Contract
import ShorECDLP.Submission.«2607_13816».Challenge.OuterResources
import ShorECDLP.Submission.«2607_13816».Challenge.CursorShift


/-! EDITABLE. Single-trial entrant: protected certificate assembly.
Concatenated in dependency order to bound parallel kernel replay memory.
Original provenance comments are retained beside each source part. -/

-- ==== part: Single/Certificate ====

section
/-! Single-trial certificate for the 263/263-bit protected nearest-pair decoder.
The fixed-table packaging follows the Apache-2.0 VerifiedQC Streaming certificate
(PR #551), for the construction of arXiv:2607.13816v2. See LICENSE and NOTICE. -/
namespace ShorECDLP.Entrant.Single
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816.ChallengeMigration

/-- Generic packaging avoids unfolding a large coefficient table to transport its length. -/
def fixedEntry {n e : Nat} (f : Fin n → PointCoeff) (p : Straight n 0 e) : StraightEntry where
  coefficients := List.ofFn f
  finalCursor := e
  program := reindexStraight (Fin.cast List.length_ofFn.symm) p

private theorem ofFn_read {n : Nat} (f : Fin n → PointCoeff) (Q : Point) :
    (fun r : ConstantBit n => readConstant (List.ofFn f).get Q
      ⟨Fin.cast (List.length_ofFn).symm r.point, r.field, r.bit⟩) =
      readConstant f Q := by
  funext r
  simp only [readConstant,List.get_eq_getElem,List.getElem_ofFn,Fin.val_cast,Fin.eta]

theorem fixedEntry_instantiate {n e : Nat} (f : Fin n → PointCoeff)
    (p : Straight n 0 e) (Q : Point) :
    (fixedEntry f p).instantiate Q = p.instantiate (readConstant f Q) Fin.elim0 := by
  dsimp only [fixedEntry,StraightEntry.instantiate]
  rw [reindexStraight_instantiate]
  simp only [Function.comp_def,reindexBit]
  rw [ofFn_read]

theorem fixedEntry_slots {n e : Nat} (f : Fin n → PointCoeff)
    (p : Straight n 0 e) : (fixedEntry f p).program.gateSlots = p.gateSlots :=
  reindexStraight_gateSlots _ _

theorem fixedEntry_wellFormed {n e : Nat} (f : Fin n → PointCoeff)
    (p : Straight n 0 e) : (fixedEntry f p).program.WellFormed ↔ p.WellFormed :=
  reindexStraight_wellFormed _ _

theorem fixedEntry_cursor {n e : Nat} (f : Fin n → PointCoeff)
    (p : Straight n 0 e) : (fixedEntry f p).finalCursor = e := rfl

theorem fixedEntry_rows {n e : Nat} (f : Fin n → PointCoeff)
    (p : Straight n 0 e) : (fixedEntry f p).coefficients.length = n := List.length_ofFn


end ShorECDLP.Entrant.Single
end


namespace ShorECDLP.Entrant.NeighborReadout
open Quantum ShorECDLP.Challenge RoundedReadout
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

/-- Literal specialization of the already verified two-record full-adder at true,true.
The first output is a true carry record; the second is false. Both scratch wires reset. -/
def constantStep (n start : Nat) : Straight n start (start+2) :=
  .gate (.literal (.X 0))
    (.gate (.literal (.CX 0 1))
      (.gate (.literal (.H 1))
        (.measure 1
          (.gate (.literal (.X 0))
            (.gate (.literal (.X 1))
              (.gate (.literal (.X 1))
                (.gate (.literal (.H 1)) (.measure 1 .done))))))))

theorem constantStep_instantiate (n start : Nat) (read : ConstantBit n→Bool)
    (history : Fin start→Bool) :
    (constantStep n start).instantiate read history=stepSource true true := by
  simp only [constantStep,Straight.instantiate,TemplateGate.instantiate,stepSource,stepTail,
    ite_true]

theorem constantStep_wellFormed (n start : Nat) : (constantStep n start).WellFormed := by
  simp [constantStep,Straight.WellFormed,TemplateGate.WellFormed,Gate.WellFormed]

theorem constantStep_slots (n start : Nat) : (constantStep n start).gateSlots=7 := rfl

theorem constantStep_t (n start : Nat) (read : ConstantBit n→Bool) (history : Fin start→Bool) :
    ((constantStep n start).instantiate read history).tCount=0 := by
  simp [constantStep,Straight.instantiate,TemplateGate.instantiate,AdaptiveCircuit.tCount,
    ShorECDLP.tCount,tCost]

theorem constantStep_support (n start : Nat) (read : ConstantBit n→Bool) (history : Fin start→Bool) :
    ((constantStep n start).instantiate read history).wires⊆[0,1] := by
  simp [constantStep,Straight.instantiate,TemplateGate.instantiate,AdaptiveCircuit.wires,
    circuitWires,gateWires,List.subset_def]

theorem constantStep_branch (n start : Nat) (read : ConstantBit n→Bool) (history : Fin start→Bool)
    (ψ : State) (hψ : SupportedOn CleanReadout ψ) (b : InstrumentBranch)
    (hb : b∈((constantStep n start).instantiate read history).run) (hn : b.kraus ψ≠0) :
    b.kraus ψ=ψ ∧ b.history=[true,false] := by
  rw [constantStep_instantiate,stepSource_run] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl
  all_goals simp_all [LinearMap.comp_apply,stepMap_state _ _ _ _ ψ hψ]

/-- Positions of the sum records of a full-adder word. -/
def sumPositions (start width : Nat) : Vector Nat width :=
  Vector.ofFn fun i=>start+2*i.val+1

private theorem word_eq (bits : List Bool) : fourierWordLSB bits=boolWordToNat bits := by
  induction bits with
  | nil=>rfl
  | cons b bits ih=>simp only [fourierWordLSB,boolWordToNat_cons,ih]

theorem sumPositions_read (before : List Bool) (carry : Bool) (bits : List Bool) :
    readWord (before++carryBits carry bits) (sumPositions before.length bits.length).toList =
      some ((carry.toNat+boolWordToNat bits)%2^bits.length) := by
  have hactual : (sumPositions before.length bits.length).toList.map
      (fun i=>(before++carryBits carry bits)[i]?)=(sumBits carry bits).map some := by
    apply List.ext_getElem
    · simp only [List.length_map,sumPositions,Vector.toList_ofFn,List.length_ofFn,sumBits_length]
    · intro i hi hj
      simp only [List.length_map,sumPositions,Vector.toList_ofFn,List.length_ofFn] at hi
      simp only [List.getElem_map,sumPositions,Vector.toList_ofFn,List.getElem_ofFn]
      rw [List.getElem?_append_right (by omega)]
      rw [show before.length+2*i+1-before.length=2*i+1 by omega]
      rw [carryBits_odd,List.getElem?_eq_getElem (by simpa [sumBits_length] using hi)]
  rw [readWord_of_actual_bits _ _ _ hactual,word_eq,sumBits_value]

theorem addWord_reads_increment {n start : Nat} (carry : Fin start) (bits : List (Fin start))
    (read : ConstantBit n→Bool) (history : Fin start→Bool) (hc : history carry=true)
    (ψ : State) (hψ : SupportedOn CleanReadout ψ) (b : InstrumentBranch)
    (hb : b∈((addWord start carry bits).instantiate read history).run) (hn : b.kraus ψ≠0) :
    b.kraus ψ=ψ ∧
      readWord (List.ofFn history++b.history) (sumPositions start bits.length).toList=
        some ((1+boolWordToNat (bits.map history))%2^bits.length) := by
  obtain ⟨he,hh⟩:=addWord_branch start carry bits read history ψ hψ b hb hn
  refine ⟨he,?_⟩
  rw [hh,hc]
  simpa only [sumPositions,Vector.toList_ofFn,List.length_ofFn,List.length_map,Bool.toNat_true] using
    sumPositions_read (List.ofFn history) true (bits.map history)

/-- Complement arithmetic, proved without any division estimates. -/
theorem word_complement_sum (bits : List Bool) :
    boolWordToNat bits+boolWordToNat (bits.map Bool.not)=2^bits.length-1 := by
  induction bits with
  | nil=>rfl
  | cons bit bits ih=>
    have hp : 0<2^bits.length := by positivity
    cases bit <;> simp only [List.map_cons,List.length_cons,boolWordToNat_cons,
      Bool.not_false,Bool.not_true,Bool.toNat_false,Bool.toNat_true,pow_succ] <;> omega

end
end ShorECDLP.Entrant.NeighborReadout
/- Append after ReadoutBase. -/
namespace ShorECDLP.Entrant.NeighborReadout
open Quantum ShorECDLP.Challenge RoundedReadout
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Reusing addStep at a fixed true carry complements each bit. -/
def complementWord {n : Nat} : (start : Nat) → Fin start → (bits : List (Fin start)) →
    Straight n start (start+2*bits.length)
  | _,_,[]=>.done
  | start,carry,bit::bits=>castFinish (by simp;omega)
      ((addStep carry bit).append
        (complementWord (start+2) (liftTwo carry) (bits.map liftTwo)))
termination_by _ _ bits=>bits.length

def complementRecords : List Bool→List Bool
  | []=>[]
  | bit::bits=>bit::(!bit)::complementRecords bits

theorem complementRecords_length (bits : List Bool) :
    (complementRecords bits).length=2*bits.length := by
  induction bits with
  | nil=>rfl
  | cons bit bits ih=>simp only [complementRecords,List.length_cons,ih];omega

theorem complementRecords_odd (bits : List Bool) (i : Nat) :
    (complementRecords bits)[2*i+1]?=(bits.map Bool.not)[i]? := by
  induction bits generalizing i with
  | nil=>simp [complementRecords]
  | cons bit bits ih=>
    cases i with
    | zero=>simp [complementRecords]
    | succ i=>
      simp only [complementRecords,List.map_cons]
      rw [show 2*(i+1)+1=(2*i+1)+2 by omega]
      simpa only [List.getElem?_cons_succ,Nat.add_assoc] using ih i

theorem complementWord_wellFormed {n : Nat} : ∀(start : Nat)(carry : Fin start)(bits : List (Fin start)),
    (complementWord (n:=n) start carry bits).WellFormed
  | _,_,[]=>by simp [complementWord,Straight.WellFormed]
  | start,carry,bit::bits=>by
    rw [complementWord,castFinish_wellFormed]
    exact straight_append_wellFormed _ _ (addStep_wellFormed _ _)
      (complementWord_wellFormed (start+2) _ _)
termination_by _ _ bits=>bits.length

theorem complementWord_slots {n : Nat} : ∀(start : Nat)(carry : Fin start)(bits : List (Fin start)),
    (complementWord (n:=n) start carry bits).gateSlots=7*bits.length
  | _,_,[]=>by simp [complementWord,Straight.gateSlots]
  | start,carry,bit::bits=>by
    rw [complementWord,castFinish_gateSlots,Straight.gateSlots_append,addStep_slots,
      complementWord_slots (start+2)]
    simp
    omega
termination_by _ _ bits=>bits.length

theorem complementWord_t {n : Nat} : ∀(start : Nat)(carry : Fin start)(bits : List (Fin start))
    (read : ConstantBit n→Bool)(history : Fin start→Bool),
    ((complementWord start carry bits).instantiate read history).tCount=0
  | _,_,[],_,_=>by simp [complementWord,Straight.instantiate,AdaptiveCircuit.tCount]
  | start,carry,bit::bits,read,history=>by
    rw [complementWord,castFinish_instantiate]
    apply Nat.eq_zero_of_le_zero
    have h:=outer_append_t_le (addStep carry bit)
      (complementWord (start+2) (liftTwo carry) (bits.map liftTwo)) read history 0
      (fun h=>le_of_eq (complementWord_t _ _ _ read h))
    simpa only [addStep_t,Nat.add_zero] using h
termination_by _ _ bits=>bits.length

theorem complementWord_support {n : Nat} : ∀(start : Nat)(carry : Fin start)(bits : List (Fin start))
    (read : ConstantBit n→Bool)(history : Fin start→Bool),
    ((complementWord start carry bits).instantiate read history).wires⊆[0,1]
  | _,_,[],_,_=>by simp [complementWord,Straight.instantiate,AdaptiveCircuit.wires]
  | start,carry,bit::bits,read,history=>by
    rw [complementWord,castFinish_instantiate]
    exact outer_append_support _ _ read history ([0,1] : List Wire) (addStep_support _ _ _ _)
      (fun h=>complementWord_support (start+2) _ _ read h)
termination_by _ _ bits=>bits.length

theorem complementWord_branch {n : Nat} : ∀(start : Nat)(carry : Fin start)
    (bits : List (Fin start))(read : ConstantBit n→Bool)(history : Fin start→Bool),
    history carry=true→∀(ψ : State)(_hψ : SupportedOn CleanReadout ψ)(b : InstrumentBranch),
    b∈((complementWord start carry bits).instantiate read history).run→b.kraus ψ≠0→
    b.kraus ψ=ψ ∧ b.history=complementRecords (bits.map history)
  | _,_,[],_,_,_,_,_,b,hb,_=>by
    simp only [complementWord,Straight.instantiate,run_done_data,List.mem_singleton] at hb
    subst b
    simp [complementRecords]
  | start,carry,bit::bits,read,history,hcarry,ψ,hψ,b,hb,hn=>by
    rw [complementWord,castFinish_instantiate] at hb
    obtain ⟨mid,a,c,ha,hc,he,rfl⟩:=straight_append_branch _ _ read history b hb
    have han : a.kraus ψ≠0 := by
      intro h
      apply hn
      simp only [InstrumentBranch.seq,LinearMap.comp_apply,h,map_zero]
    obtain ⟨hastate,hahist⟩:=addStep_branch carry bit read history ψ hψ a ha han
    have hcn : c.kraus ψ≠0 := by
      simpa only [InstrumentBranch.seq,LinearMap.comp_apply,hastate] using hn
    have hold (i : Fin start) : mid (liftTwo i)=history i := by
      have h:=congrArg (fun xs : List Bool=>xs[i.val]?) he
      dsimp only at h
      have hlt : i.val<start+2 := by omega
      rw [List.getElem?_append_left (by simp)] at h
      simpa only [List.getElem?_ofFn,i.isLt,hlt,↓reduceDIte,Fin.eta,Option.some.injEq,liftTwo] using h
    have hi:=complementWord_branch (start+2) (liftTwo carry) (bits.map liftTwo)
      read mid (by rw [hold,hcarry]) ψ hψ c hc hcn
    have hbits : (bits.map liftTwo).map mid=bits.map history := by
      rw [List.map_map]
      apply List.map_congr_left
      intro i _
      exact hold i
    constructor
    · simpa only [InstrumentBranch.seq,LinearMap.comp_apply,hastate] using hi.1
    · simp only [InstrumentBranch.seq,hahist,hi.2,hbits,hcarry,List.map_cons,
        complementRecords,List.cons_append,List.nil_append,Bool.true_and,Bool.xor_true]
termination_by _ _ bits=>bits.length

theorem complementPositions_read (before : List Bool) (bits : List Bool) :
    readWord (before++complementRecords bits) (sumPositions before.length bits.length).toList=
      some (boolWordToNat (bits.map Bool.not)) := by
  have hactual : (sumPositions before.length bits.length).toList.map
      (fun i=>(before++complementRecords bits)[i]?)=(bits.map Bool.not).map some := by
    apply List.ext_getElem
    · simp only [List.length_map,sumPositions,Vector.toList_ofFn,List.length_ofFn]
    · intro i hi hj
      simp only [List.length_map,sumPositions,Vector.toList_ofFn,List.length_ofFn] at hi
      simp only [List.getElem_map,sumPositions,Vector.toList_ofFn,List.getElem_ofFn]
      rw [List.getElem?_append_right (by omega)]
      rw [show before.length+2*i+1-before.length=2*i+1 by omega]
      rw [complementRecords_odd,List.getElem?_eq_getElem (by simpa using hi)]
      simp only [List.getElem_map]
  rw [readWord_of_actual_bits _ _ _ hactual]
  have hw (bs : List Bool) : fourierWordLSB bs=boolWordToNat bs := by
    induction bs with
    | nil=>rfl
    | cons bit bs ih=>simp only [fourierWordLSB,boolWordToNat_cons,ih]
  rw [hw]

end
end ShorECDLP.Entrant.NeighborReadout
/- Append after ReadoutBase+Complement. Static recorded-word programs only. -/
namespace ShorECDLP.Entrant.NeighborReadout
open Quantum ShorECDLP.Challenge RoundedReadout
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- All data here are measurement indices, never a callback on their values. -/
structure WordCursor (start width : Nat) where
  carry : Fin start
  bits : Vector (Fin start) width

def WordCursor.lift {start width : Nat} (c : WordCursor start width) (extra : Nat) :
    WordCursor (start+extra) width where
  carry:=⟨c.carry.val,by have h:=c.carry.isLt;omega⟩
  bits:=c.bits.map fun i=>⟨i.val,by have h:=i.isLt;omega⟩

def incrementStep (n : Nat) {start width : Nat} (c : WordCursor start width) :
    Straight n start (start+2*width) :=
  castFinish (by simp) (addWord start c.carry c.bits.toList)

def complementStep (n : Nat) {start width : Nat} (c : WordCursor start width) :
    Straight n start (start+2*width) :=
  castFinish (by simp) (complementWord start c.carry c.bits.toList)

def WordCursor.next {start width : Nat} (c : WordCursor start width) :
    WordCursor (start+2*width) width where
  carry:=⟨c.carry.val,by have h:=c.carry.isLt;omega⟩
  bits:=Vector.ofFn fun i=>⟨start+2*i.val+1,by have h:=i.isLt;omega⟩

/-- Record the next increasing word at every step. -/
def positiveWords (n : Nat) : (steps start width : Nat) → WordCursor start width →
    Straight n start (start+steps*(2*width))
  | 0,start,width,_=>castFinish (show start=start+0*(2*width) by simp) (.done)
  | steps+1,start,width,c=>castFinish (by ring)
      ((incrementStep n c).append (positiveWords n steps (start+2*width) width c.next))

/-- Increment a complemented word, then explicitly record its complement.
The state remains unchanged and the next complemented word stays available. -/
def negativeStep (n : Nat) {start width : Nat} (c : WordCursor start width) :
    Straight n start (start+4*width) :=
  castFinish (by omega) ((incrementStep n c).append (complementStep n c.next))

def WordCursor.nextNegative {start width : Nat} (c : WordCursor start width) :
    WordCursor (start+4*width) width where
  carry:=⟨c.carry.val,by have h:=c.carry.isLt;omega⟩
  bits:=Vector.ofFn fun i=>⟨start+2*i.val+1,by have h:=i.isLt;omega⟩

/-- The initial input word is complemented. Outputs are the decreasing original words. -/
def negativeWords (n : Nat) : (steps start width : Nat) → WordCursor start width →
    Straight n start (start+steps*(4*width))
  | 0,start,width,_=>castFinish (show start=start+0*(4*width) by simp) (.done)
  | steps+1,start,width,c=>castFinish (by ring)
      ((negativeStep n c).append (negativeWords n steps (start+4*width) width c.nextNegative))

theorem incrementStep_wellFormed (n : Nat) {start width : Nat} (c : WordCursor start width) :
    (incrementStep n c).WellFormed := by
  rw [incrementStep,castFinish_wellFormed]
  exact addWord_wellFormed _ _ _

theorem complementStep_wellFormed (n : Nat) {start width : Nat} (c : WordCursor start width) :
    (complementStep n c).WellFormed := by
  rw [complementStep,castFinish_wellFormed]
  exact complementWord_wellFormed _ _ _

theorem incrementStep_slots (n : Nat) {start width : Nat} (c : WordCursor start width) :
    (incrementStep n c).gateSlots=7*width := by
  simp only [incrementStep,castFinish_gateSlots,addWord_slots,Vector.length_toList]

theorem complementStep_slots (n : Nat) {start width : Nat} (c : WordCursor start width) :
    (complementStep n c).gateSlots=7*width := by
  simp only [complementStep,castFinish_gateSlots,complementWord_slots,Vector.length_toList]

theorem positiveWords_wellFormed (n : Nat) : ∀(steps start width : Nat)(c : WordCursor start width),
    (positiveWords n steps start width c).WellFormed
  | 0,_,_,_=>by simp [positiveWords,castFinish_wellFormed,Straight.WellFormed]
  | steps+1,start,width,c=>by
    rw [positiveWords,castFinish_wellFormed]
    exact straight_append_wellFormed _ _ (incrementStep_wellFormed n c)
      (positiveWords_wellFormed n steps _ _ _)

theorem positiveWords_slots (n : Nat) : ∀(steps start width : Nat)(c : WordCursor start width),
    (positiveWords n steps start width c).gateSlots=steps*(7*width)
  | 0,_,_,_=>by simp [positiveWords,castFinish_gateSlots,Straight.gateSlots]
  | steps+1,start,width,c=>by
    rw [positiveWords,castFinish_gateSlots,Straight.gateSlots_append,incrementStep_slots,
      positiveWords_slots n steps]
    ring

theorem negativeStep_wellFormed (n : Nat) {start width : Nat} (c : WordCursor start width) :
    (negativeStep n c).WellFormed := by
  rw [negativeStep,castFinish_wellFormed]
  exact straight_append_wellFormed _ _ (incrementStep_wellFormed n c)
    (complementStep_wellFormed n c.next)

theorem negativeStep_slots (n : Nat) {start width : Nat} (c : WordCursor start width) :
    (negativeStep n c).gateSlots=14*width := by
  rw [negativeStep,castFinish_gateSlots,Straight.gateSlots_append,incrementStep_slots,
    complementStep_slots]
  ring

theorem negativeWords_wellFormed (n : Nat) : ∀(steps start width : Nat)(c : WordCursor start width),
    (negativeWords n steps start width c).WellFormed
  | 0,_,_,_=>by simp [negativeWords,castFinish_wellFormed,Straight.WellFormed]
  | steps+1,start,width,c=>by
    rw [negativeWords,castFinish_wellFormed]
    exact straight_append_wellFormed _ _ (negativeStep_wellFormed n c)
      (negativeWords_wellFormed n steps _ _ _)

theorem negativeWords_slots (n : Nat) : ∀(steps start width : Nat)(c : WordCursor start width),
    (negativeWords n steps start width c).gateSlots=steps*(14*width)
  | 0,_,_,_=>by simp [negativeWords,castFinish_gateSlots,Straight.gateSlots]
  | steps+1,start,width,c=>by
    rw [negativeWords,castFinish_gateSlots,Straight.gateSlots_append,negativeStep_slots,
      negativeWords_slots n steps]
    ring


theorem incrementStep_t (n : Nat) {start width : Nat} (c : WordCursor start width)
    (read : ConstantBit n→Bool)(history : Fin start→Bool) :
    ((incrementStep n c).instantiate read history).tCount=0 := by
  rw [incrementStep,castFinish_instantiate]
  exact addWord_t _ _ _ _ _

theorem complementStep_t (n : Nat) {start width : Nat} (c : WordCursor start width)
    (read : ConstantBit n→Bool)(history : Fin start→Bool) :
    ((complementStep n c).instantiate read history).tCount=0 := by
  rw [complementStep,castFinish_instantiate]
  exact complementWord_t _ _ _ _ _

theorem incrementStep_support (n : Nat) {start width : Nat} (c : WordCursor start width)
    (read : ConstantBit n→Bool)(history : Fin start→Bool) :
    ((incrementStep n c).instantiate read history).wires⊆[0,1] := by
  rw [incrementStep,castFinish_instantiate]
  exact addWord_support _ _ _ _ _

theorem complementStep_support (n : Nat) {start width : Nat} (c : WordCursor start width)
    (read : ConstantBit n→Bool)(history : Fin start→Bool) :
    ((complementStep n c).instantiate read history).wires⊆[0,1] := by
  rw [complementStep,castFinish_instantiate]
  exact complementWord_support _ _ _ _ _

theorem positiveWords_t (n : Nat) : ∀(steps start width : Nat)(c : WordCursor start width)
    (read : ConstantBit n→Bool)(history : Fin start→Bool),
    ((positiveWords n steps start width c).instantiate read history).tCount=0
  | 0,_,_,_,_,_=>by simp [positiveWords,castFinish_instantiate,Straight.instantiate,AdaptiveCircuit.tCount]
  | steps+1,start,width,c,read,history=>by
    rw [positiveWords,castFinish_instantiate]
    apply Nat.eq_zero_of_le_zero
    have h:=outer_append_t_le (incrementStep n c)
      (positiveWords n steps (start+2*width) width c.next) read history 0
      (fun h=>le_of_eq (positiveWords_t n steps _ _ _ read h))
    simpa only [incrementStep_t,Nat.add_zero] using h

theorem positiveWords_support (n : Nat) : ∀(steps start width : Nat)(c : WordCursor start width)
    (read : ConstantBit n→Bool)(history : Fin start→Bool),
    ((positiveWords n steps start width c).instantiate read history).wires⊆[0,1]
  | 0,_,_,_,_,_=>by simp [positiveWords,castFinish_instantiate,Straight.instantiate,AdaptiveCircuit.wires]
  | steps+1,start,width,c,read,history=>by
    rw [positiveWords,castFinish_instantiate]
    exact outer_append_support _ _ read history ([0,1] : List Wire) (incrementStep_support _ _ _ _)
      (fun h=>positiveWords_support n steps _ _ _ read h)

theorem negativeStep_t (n : Nat) {start width : Nat} (c : WordCursor start width)
    (read : ConstantBit n→Bool)(history : Fin start→Bool) :
    ((negativeStep n c).instantiate read history).tCount=0 := by
  rw [negativeStep,castFinish_instantiate]
  apply Nat.eq_zero_of_le_zero
  have h:=outer_append_t_le (incrementStep n c) (complementStep n c.next) read history 0
    (fun h=>le_of_eq (complementStep_t n c.next read h))
  simpa only [incrementStep_t,Nat.add_zero] using h

theorem negativeStep_support (n : Nat) {start width : Nat} (c : WordCursor start width)
    (read : ConstantBit n→Bool)(history : Fin start→Bool) :
    ((negativeStep n c).instantiate read history).wires⊆[0,1] := by
  rw [negativeStep,castFinish_instantiate]
  exact outer_append_support _ _ read history ([0,1] : List Wire) (incrementStep_support _ _ _ _)
    (fun h=>complementStep_support n c.next read h)

theorem negativeWords_t (n : Nat) : ∀(steps start width : Nat)(c : WordCursor start width)
    (read : ConstantBit n→Bool)(history : Fin start→Bool),
    ((negativeWords n steps start width c).instantiate read history).tCount=0
  | 0,_,_,_,_,_=>by simp [negativeWords,castFinish_instantiate,Straight.instantiate,AdaptiveCircuit.tCount]
  | steps+1,start,width,c,read,history=>by
    rw [negativeWords,castFinish_instantiate]
    apply Nat.eq_zero_of_le_zero
    have h:=outer_append_t_le (negativeStep n c)
      (negativeWords n steps (start+4*width) width c.nextNegative) read history 0
      (fun h=>le_of_eq (negativeWords_t n steps _ _ _ read h))
    simpa only [negativeStep_t,Nat.add_zero] using h

theorem negativeWords_support (n : Nat) : ∀(steps start width : Nat)(c : WordCursor start width)
    (read : ConstantBit n→Bool)(history : Fin start→Bool),
    ((negativeWords n steps start width c).instantiate read history).wires⊆[0,1]
  | 0,_,_,_,_,_=>by simp [negativeWords,castFinish_instantiate,Straight.instantiate,AdaptiveCircuit.wires]
  | steps+1,start,width,c,read,history=>by
    rw [negativeWords,castFinish_instantiate]
    exact outer_append_support _ _ read history ([0,1] : List Wire) (negativeStep_support _ _ _ _)
      (fun h=>negativeWords_support n steps _ _ _ read h)

end
end ShorECDLP.Entrant.NeighborReadout
/- Append after WordPrograms. -/
namespace ShorECDLP.Entrant.NeighborReadout
open Quantum ShorECDLP.Challenge RoundedReadout
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def initialCursor {start width : Nat} (bits : Vector (Fin start) width) :
    WordCursor (start+2) width where
  carry:=⟨start,by omega⟩
  bits:=bits.map fun i=>⟨i.val,by have h:=i.isLt;omega⟩

/--28 candidate words from one sample: center,14 positive shifts,13 negative shifts.
The arithmetic is carried out by explicit permitted record-controlled Clifford gates. -/
def neighborSuffix (n start width : Nat) (bits : Vector (Fin start) width) :
    Straight n start (start+2+82*width) :=
  let c:=initialCursor bits
  let q:=c.lift (14*(2*width))
  castFinish (by omega)
    ((constantStep n start).append
      ((positiveWords n 14 (start+2) width c).append
        ((complementStep n q).append
          (negativeWords n 13 (start+2+14*(2*width)+2*width) width q.next))))

def rightWords {start width : Nat} (bits : Vector (Fin start) width) : List (Vector Nat width) :=
  bits.map Fin.val ::
    List.ofFn (fun i : Fin 14=>sumPositions (start+2+i.val*(2*width)) width) ++
    List.ofFn (fun i : Fin 13=>sumPositions
      (start+2+14*(2*width)+2*width+i.val*(4*width)+2*width) width)

theorem rightWords_length {start width : Nat} (bits : Vector (Fin start) width) :
    (rightWords bits).length=28 := by simp [rightWords]

attribute [local irreducible] positiveWords negativeWords incrementStep complementStep

theorem neighborSuffix_wellFormed (n start width : Nat) (bits : Vector (Fin start) width) :
    (neighborSuffix n start width bits).WellFormed := by
  unfold neighborSuffix
  rw [castFinish_wellFormed]
  apply straight_append_wellFormed _ _ (constantStep_wellFormed _ _)
  apply straight_append_wellFormed _ _ (positiveWords_wellFormed _ _ _ _ _)
  exact straight_append_wellFormed _ _ (complementStep_wellFormed _ _)
    (negativeWords_wellFormed _ _ _ _ _)

theorem neighborSuffix_slots (n start width : Nat) (bits : Vector (Fin start) width) :
    (neighborSuffix n start width bits).gateSlots=7+287*width := by
  simp only [neighborSuffix,castFinish_gateSlots,Straight.gateSlots_append,
    constantStep_slots,positiveWords_slots,complementStep_slots,negativeWords_slots]
  ring

private theorem append_zero {n a b c : Nat} (p : Straight n a b) (q : Straight n b c)
    (read : ConstantBit n→Bool)
    (hp : ∀h, (p.instantiate read h).tCount=0)
    (hq : ∀h, (q.instantiate read h).tCount=0) (history : Fin a→Bool) :
    ((p.append q).instantiate read history).tCount=0 := by
  apply Nat.eq_zero_of_le_zero
  have h:=outer_append_t_le p q read history 0 (fun h=>le_of_eq (hq h))
  simpa only [hp,Nat.add_zero] using h

theorem neighborSuffix_t (n start width : Nat) (bits : Vector (Fin start) width)
    (read : ConstantBit n→Bool)(history : Fin start→Bool) :
    ((neighborSuffix n start width bits).instantiate read history).tCount=0 := by
  unfold neighborSuffix
  rw [castFinish_instantiate]
  apply append_zero _ _ read (constantStep_t _ _ _)
  intro h
  apply append_zero _ _ read (positiveWords_t _ _ _ _ _ _)
  intro h
  exact append_zero _ _ read (complementStep_t _ _ _)
    (negativeWords_t _ _ _ _ _ _) h

theorem neighborSuffix_support (n start width : Nat) (bits : Vector (Fin start) width)
    (read : ConstantBit n→Bool)(history : Fin start→Bool) :
    ((neighborSuffix n start width bits).instantiate read history).wires⊆[0,1] := by
  unfold neighborSuffix
  rw [castFinish_instantiate]
  apply outer_append_support _ _ read history ([0,1] : List Wire) (constantStep_support _ _ _ _)
  intro h
  apply outer_append_support _ _ read h ([0,1] : List Wire) (positiveWords_support _ _ _ _ _ _ _)
  intro h
  exact outer_append_support _ _ read h ([0,1] : List Wire) (complementStep_support _ _ _ _)
    (fun hh=>negativeWords_support _ _ _ _ _ _ hh)

end
end ShorECDLP.Entrant.NeighborReadout
/- Append after WordPrograms. -/
namespace ShorECDLP.Entrant.NeighborReadout
open Quantum ShorECDLP.Challenge RoundedReadout
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

def cursorValue {start width : Nat} (c : WordCursor start width) (history : Fin start→Bool) : Nat :=
  boolWordToNat (c.bits.toList.map history)

def cursorPositions {start width : Nat} (c : WordCursor start width) : List Nat :=
  c.bits.toList.map Fin.val

theorem cursorValue_lt {start width : Nat} (c : WordCursor start width) (history : Fin start→Bool) :
    cursorValue c history<2^width := by
  have h:=word_complement_sum (c.bits.toList.map history)
  simp only [List.length_map,Vector.length_toList] at h
  have hp : 0<2^width := by positivity
  unfold cursorValue
  omega

theorem cursor_read {start width : Nat} (c : WordCursor start width) (history : Fin start→Bool) :
    readWord (List.ofFn history) (cursorPositions c)=some (cursorValue c history) := by
  have h:=readWord_of_actual_bits (List.ofFn history) (c.bits.toList.map Fin.val)
    (c.bits.toList.map history) (by simp only [List.map_map,List.getElem?_ofFn,
      Fin.isLt,↓reduceDIte,Fin.eta,Function.comp_def])
  have hw (bs : List Bool) : fourierWordLSB bs=boolWordToNat bs := by
    induction bs with
    | nil=>rfl
    | cons bit bs ih=>simp only [fourierWordLSB,boolWordToNat_cons,ih]
  simpa only [hw] using h

theorem next_positions {start width : Nat} (c : WordCursor start width) :
    cursorPositions c.next=(sumPositions start width).toList := by
  simp only [cursorPositions,WordCursor.next,sumPositions,Vector.toList_ofFn,List.map_ofFn,Function.comp_def]

theorem nextNegative_positions {start width : Nat} (c : WordCursor start width) :
    cursorPositions c.nextNegative=(sumPositions start width).toList := by
  simp only [cursorPositions,WordCursor.nextNegative,sumPositions,Vector.toList_ofFn,List.map_ofFn,Function.comp_def]

theorem lift_positions {start width : Nat} (c : WordCursor start width) (extra : Nat) :
    cursorPositions (c.lift extra)=cursorPositions c := by
  simp only [cursorPositions,WordCursor.lift,Vector.toList_map,List.map_map,Function.comp_def]

/-- Old records retain exactly their values after any straight-program append. -/
theorem prefix_value {s e : Nat} (history : Fin s→Bool) (mid : Fin e→Bool) (ys : List Bool)
    (he : List.ofFn mid=List.ofFn history++ys) (i : Fin s) (hi : i.val<e) :
    mid ⟨i.val,hi⟩=history i := by
  have h:=congrArg (fun xs : List Bool=>xs[i.val]?) he
  dsimp only at h
  rw [List.getElem?_append_left (by simp)] at h
  simpa only [List.getElem?_ofFn,i.isLt,hi,↓reduceDIte,Fin.eta,Option.some.injEq] using h

theorem lift_value {start width : Nat} (c : WordCursor start width) (extra : Nat)
    (history : Fin start→Bool) (mid : Fin (start+extra)→Bool) (ys : List Bool)
    (he : List.ofFn mid=List.ofFn history++ys) :
    cursorValue (c.lift extra) mid=cursorValue c history := by
  unfold cursorValue
  simp only [WordCursor.lift,Vector.toList_map,List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact prefix_value history mid ys he i _

theorem lift_carry {start width : Nat} (c : WordCursor start width) (extra : Nat)
    (history : Fin start→Bool) (mid : Fin (start+extra)→Bool) (ys : List Bool)
    (he : List.ofFn mid=List.ofFn history++ys) :
    mid (c.lift extra).carry=history c.carry :=
  prefix_value history mid ys he c.carry _

theorem next_carry {start width : Nat} (c : WordCursor start width)
    (history : Fin start→Bool) (mid : Fin (start+2*width)→Bool) (ys : List Bool)
    (he : List.ofFn mid=List.ofFn history++ys) :
    mid c.next.carry=history c.carry :=
  prefix_value history mid ys he c.carry _

theorem readWord_append_left (before after : List Bool) (ps : List Nat)
    (hp : ∀i∈ps,i<before.length) : readWord (before++after) ps=readWord before ps := by
  induction ps with
  | nil=>rfl
  | cons i ps ih=>
    simp only [readWord,List.getElem?_append_left (hp i (by simp))]
    rw [ih (fun j hj=>hp j (List.mem_cons_of_mem i hj))]

theorem sumPositions_bound (start width i : Nat) (hi : i∈(sumPositions start width).toList) :
    i<start+2*width := by
  simp only [sumPositions,Vector.toList_ofFn,List.mem_ofFn] at hi
  obtain ⟨j,rfl⟩:=hi
  have hj:=j.isLt
  omega

theorem incrementStep_post (n : Nat) {start width : Nat} (c : WordCursor start width)
    (read : ConstantBit n→Bool) (history : Fin start→Bool) (hcarry : history c.carry=true)
    (ψ : State) (hψ : SupportedOn CleanReadout ψ) (b : InstrumentBranch)
    (hb : b∈((incrementStep n c).instantiate read history).run) (hn : b.kraus ψ≠0)
    (mid : Fin (start+2*width)→Bool) (he : List.ofFn mid=List.ofFn history++b.history) :
    b.kraus ψ=ψ ∧ mid c.next.carry=true ∧
      cursorValue c.next mid=(1+cursorValue c history)%2^width := by
  rw [incrementStep,castFinish_instantiate] at hb
  obtain ⟨hs,hread⟩:=addWord_reads_increment c.carry c.bits.toList read history hcarry ψ hψ b hb hn
  refine ⟨hs,(next_carry c history mid b.history he).trans hcarry,?_⟩
  have hv:=cursor_read c.next mid
  rw [next_positions,he] at hv
  have hh : readWord (List.ofFn history++b.history) (sumPositions start width).toList=
      some ((1+cursorValue c history)%2^width) := by
    simpa only [sumPositions,Vector.toList_ofFn,Vector.length_toList,cursorValue] using hread
  exact Option.some.inj (hv.symm.trans hh)

theorem complementStep_post (n : Nat) {start width : Nat} (c : WordCursor start width)
    (read : ConstantBit n→Bool) (history : Fin start→Bool) (hcarry : history c.carry=true)
    (ψ : State) (hψ : SupportedOn CleanReadout ψ) (b : InstrumentBranch)
    (hb : b∈((complementStep n c).instantiate read history).run) (hn : b.kraus ψ≠0)
    (mid : Fin (start+2*width)→Bool) (he : List.ofFn mid=List.ofFn history++b.history) :
    b.kraus ψ=ψ ∧ mid c.next.carry=true ∧
      cursorValue c.next mid=2^width-1-cursorValue c history := by
  rw [complementStep,castFinish_instantiate] at hb
  obtain ⟨hs,hh⟩:=complementWord_branch start c.carry c.bits.toList read history hcarry ψ hψ b hb hn
  refine ⟨hs,(next_carry c history mid b.history he).trans hcarry,?_⟩
  have hv:=cursor_read c.next mid
  rw [next_positions,he,hh] at hv
  have hc:=complementPositions_read (List.ofFn history) (c.bits.toList.map history)
  have hc' : readWord (List.ofFn history++complementRecords (c.bits.toList.map history))
      (sumPositions start width).toList=some (boolWordToNat ((c.bits.toList.map history).map Bool.not)) := by
    simpa only [sumPositions,Vector.toList_ofFn,List.length_ofFn,List.length_map,Vector.length_toList] using hc
  have hvalue:=Option.some.inj (hv.symm.trans hc')
  have hsum:=word_complement_sum (c.bits.toList.map history)
  simp only [List.length_map,Vector.length_toList] at hsum
  unfold cursorValue at hvalue ⊢
  omega


theorem complementStep_reads (n : Nat) {start width : Nat} (c : WordCursor start width)
    (read : ConstantBit n→Bool) (history : Fin start→Bool) (hcarry : history c.carry=true)
    (ψ : State) (hψ : SupportedOn CleanReadout ψ) (b : InstrumentBranch)
    (hb : b∈((complementStep n c).instantiate read history).run) (hn : b.kraus ψ≠0) :
    b.kraus ψ=ψ ∧ readWord (List.ofFn history++b.history) (sumPositions start width).toList=
      some (2^width-1-cursorValue c history) := by
  rw [complementStep,castFinish_instantiate] at hb
  obtain ⟨hs,hh⟩:=complementWord_branch start c.carry c.bits.toList read history hcarry ψ hψ b hb hn
  refine ⟨hs,?_⟩
  rw [hh]
  have hc:=complementPositions_read (List.ofFn history) (c.bits.toList.map history)
  have hsum:=word_complement_sum (c.bits.toList.map history)
  simp only [List.length_map,Vector.length_toList] at hsum
  have hv : boolWordToNat ((c.bits.toList.map history).map Bool.not)=
      2^width-1-cursorValue c history := by unfold cursorValue;omega
  rw [hv] at hc
  simpa only [sumPositions,Vector.toList_ofFn,List.length_ofFn,List.length_map,Vector.length_toList] using hc

end
end ShorECDLP.Entrant.NeighborReadout
/- Append after CursorSemantics. -/
namespace ShorECDLP.Entrant.NeighborReadout
open Quantum ShorECDLP.Challenge RoundedReadout
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

theorem positiveWords_branch (n : Nat) :
    ∀(steps start width : Nat)(c : WordCursor start width)
      (read : ConstantBit n→Bool)(history : Fin start→Bool),
    history c.carry=true→∀(ψ : State)(_hψ : SupportedOn CleanReadout ψ)(b : InstrumentBranch),
    b∈((positiveWords n steps start width c).instantiate read history).run→b.kraus ψ≠0→
    b.kraus ψ=ψ ∧ ∀i : Fin steps,
      readWord (List.ofFn history++b.history)
        (sumPositions (start+i.val*(2*width)) width).toList=
        some ((i.val+1+cursorValue c history)%2^width)
  | 0,_,_,_,_,_,_,_,_,b,hb,_=>by
    simp only [positiveWords,castFinish_instantiate,Straight.instantiate,run_done_data,List.mem_singleton] at hb
    subst b
    exact ⟨rfl,fun i=>Fin.elim0 i⟩
  | steps+1,start,width,c,read,history,hcarry,ψ,hψ,b,hb,hn=>by
    rw [positiveWords,castFinish_instantiate] at hb
    obtain ⟨mid,a,t,ha,ht,he,rfl⟩:=straight_append_branch _ _ read history b hb
    have han : a.kraus ψ≠0 := by
      intro h
      apply hn
      simp only [InstrumentBranch.seq,LinearMap.comp_apply,h,map_zero]
    have hp:=incrementStep_post n c read history hcarry ψ hψ a ha han mid he
    have htn : t.kraus ψ≠0 := by
      simpa only [InstrumentBranch.seq,LinearMap.comp_apply,hp.1] using hn
    have ih:=positiveWords_branch n steps (start+2*width) width c.next read mid hp.2.1 ψ hψ t ht htn
    refine ⟨by simpa only [InstrumentBranch.seq,LinearMap.comp_apply,hp.1] using ih.1,?_⟩
    intro i
    have hfull : List.ofFn history++(a.seq t).history=List.ofFn mid++t.history := by
      rw [he]
      simp only [InstrumentBranch.seq,List.append_assoc]
    by_cases hiz : i.val=0
    · simp only [hiz,Nat.zero_mul,Nat.add_zero,Nat.zero_add]
      rw [hfull,readWord_append_left (List.ofFn mid) t.history _ (by
        intro j hj
        simpa only [List.length_ofFn] using sumPositions_bound start width j hj)]
      have hf:=cursor_read c.next mid
      rw [next_positions,hp.2.2] at hf
      exact hf
    · let j : Fin steps:=⟨i.val-1,by have hi:=i.isLt;omega⟩
      have hij : i.val=j.val+1 := by dsimp [j];omega
      have hindex : start+i.val*(2*width)=start+2*width+j.val*(2*width) := by rw [hij];ring
      rw [hfull,hindex]
      have ht':=ih.2 j
      rw [hp.2.2] at ht'
      have hm : (j.val+1+(1+cursorValue c history)%2^width)%2^width=
          (i.val+1+cursorValue c history)%2^width := by
        rw [Nat.add_comm (j.val+1) ((1+cursorValue c history)%2^width),Nat.mod_add_mod]
        congr 1
        omega
      exact ht'.trans (congrArg some hm)

end
end ShorECDLP.Entrant.NeighborReadout
/- Append after CursorSemantics+PositiveSemantics. -/
namespace ShorECDLP.Entrant.NeighborReadout
open Quantum ShorECDLP.Challenge RoundedReadout
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

theorem negativeStep_post (n : Nat) {start width : Nat} (c : WordCursor start width)
    (read : ConstantBit n→Bool) (history : Fin start→Bool) (hcarry : history c.carry=true)
    (ψ : State) (hψ : SupportedOn CleanReadout ψ) (b : InstrumentBranch)
    (hb : b∈((negativeStep n c).instantiate read history).run) (hn : b.kraus ψ≠0)
    (mid : Fin (start+4*width)→Bool) (he : List.ofFn mid=List.ofFn history++b.history) :
    b.kraus ψ=ψ ∧ mid c.nextNegative.carry=true ∧
      cursorValue c.nextNegative mid=(1+cursorValue c history)%2^width ∧
      readWord (List.ofFn history++b.history) (sumPositions (start+2*width) width).toList=
        some (2^width-1-((1+cursorValue c history)%2^width)) := by
  rw [negativeStep,castFinish_instantiate] at hb
  obtain ⟨h₁,a,t,ha,ht,he₁,rfl⟩:=straight_append_branch _ _ read history b hb
  have han : a.kraus ψ≠0 := by
    intro h
    apply hn
    simp only [InstrumentBranch.seq,LinearMap.comp_apply,h,map_zero]
  have hp:=incrementStep_post n c read history hcarry ψ hψ a ha han h₁ he₁
  have htn : t.kraus ψ≠0 := by
    simpa only [InstrumentBranch.seq,LinearMap.comp_apply,hp.1] using hn
  have hq:=complementStep_reads n c.next read h₁ hp.2.1 ψ hψ t ht htn
  have hfull : List.ofFn history++(a.seq t).history=List.ofFn h₁++t.history := by
    rw [he₁]
    simp only [InstrumentBranch.seq,List.append_assoc]
  refine ⟨by simpa only [InstrumentBranch.seq,LinearMap.comp_apply,hp.1] using hq.1,?_,?_,?_⟩
  · exact (prefix_value history mid (a.seq t).history he c.carry _).trans hcarry
  · have hv:=cursor_read c.nextNegative mid
    rw [nextNegative_positions,he,hfull,readWord_append_left (List.ofFn h₁) t.history _ (by
      intro j hj
      simpa only [List.length_ofFn] using sumPositions_bound start width j hj)] at hv
    have hi:=cursor_read c.next h₁
    rw [next_positions,hp.2.2] at hi
    exact Option.some.inj (hv.symm.trans hi)
  · rw [hfull]
    simpa only [hp.2.2] using hq.2

theorem negativeWords_branch (n : Nat) :
    ∀(steps start width : Nat)(c : WordCursor start width)
      (read : ConstantBit n→Bool)(history : Fin start→Bool),
    history c.carry=true→∀(ψ : State)(_hψ : SupportedOn CleanReadout ψ)(b : InstrumentBranch),
    b∈((negativeWords n steps start width c).instantiate read history).run→b.kraus ψ≠0→
    b.kraus ψ=ψ ∧ ∀i : Fin steps,
      readWord (List.ofFn history++b.history)
        (sumPositions (start+i.val*(4*width)+2*width) width).toList=
        some (2^width-1-((i.val+1+cursorValue c history)%2^width))
  | 0,_,_,_,_,_,_,_,_,b,hb,_=>by
    simp only [negativeWords,castFinish_instantiate,Straight.instantiate,run_done_data,List.mem_singleton] at hb
    subst b
    exact ⟨rfl,fun i=>Fin.elim0 i⟩
  | steps+1,start,width,c,read,history,hcarry,ψ,hψ,b,hb,hn=>by
    rw [negativeWords,castFinish_instantiate] at hb
    obtain ⟨mid,a,t,ha,ht,he,rfl⟩:=straight_append_branch _ _ read history b hb
    have han : a.kraus ψ≠0 := by
      intro h
      apply hn
      simp only [InstrumentBranch.seq,LinearMap.comp_apply,h,map_zero]
    have hp:=negativeStep_post n c read history hcarry ψ hψ a ha han mid he
    have htn : t.kraus ψ≠0 := by
      simpa only [InstrumentBranch.seq,LinearMap.comp_apply,hp.1] using hn
    have ih:=negativeWords_branch n steps (start+4*width) width c.nextNegative read mid hp.2.1 ψ hψ t ht htn
    refine ⟨by simpa only [InstrumentBranch.seq,LinearMap.comp_apply,hp.1] using ih.1,?_⟩
    intro i
    have hfull : List.ofFn history++(a.seq t).history=List.ofFn mid++t.history := by
      rw [he]
      simp only [InstrumentBranch.seq,List.append_assoc]
    by_cases hiz : i.val=0
    · simp only [hiz,Nat.zero_mul,Nat.add_zero,Nat.zero_add]
      rw [hfull,readWord_append_left (List.ofFn mid) t.history _ (by
        intro j hj
        have hj':=sumPositions_bound (start+2*width) width j hj
        simp only [List.length_ofFn]
        omega)]
      rw [he]
      exact hp.2.2.2
    · let j : Fin steps:=⟨i.val-1,by have hi:=i.isLt;omega⟩
      have hij : i.val=j.val+1 := by dsimp [j];omega
      have hindex : start+i.val*(4*width)+2*width=start+4*width+j.val*(4*width)+2*width := by
        rw [hij]
        ring
      rw [hfull,hindex]
      have ht':=ih.2 j
      rw [hp.2.2.1] at ht'
      have hm : (j.val+1+(1+cursorValue c history)%2^width)%2^width=
          (i.val+1+cursorValue c history)%2^width := by
        rw [Nat.add_comm (j.val+1) ((1+cursorValue c history)%2^width),Nat.mod_add_mod]
        congr 1
        omega
      exact ht'.trans (congrArg (fun v=>some (2^width-1-v)) hm)


set_option exponentiation.threshold 300

theorem positive_word_mod (b i : Nat) :
    (i+b)%2^207=(((b : ℤ)+(i : ℤ))%(2^207 : Nat)).toNat := by
  simp only [←Int.natCast_add,←Int.natCast_mod,Int.toNat_natCast,Nat.add_comm]

theorem negative_word_mod (b i : Nat) (hb : b<2^207) :
    2^207-1-((i+(2^207-1-b))%2^207)=(((b : ℤ)-(i : ℤ))%(2^207 : Nat)).toNat := by
  norm_num at hb ⊢
  omega

end
end ShorECDLP.Entrant.NeighborReadout
namespace ShorECDLP.Entrant.NeighborReadout
open Quantum ShorECDLP.Challenge RoundedReadout
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def inputValue {start width : Nat} (bits : Vector (Fin start) width) (h : Fin start→Bool) : Nat :=
  boolWordToNat (bits.toList.map h)

theorem initial_value {start width : Nat} (bits : Vector (Fin start) width)
    (h : Fin start→Bool) (mid : Fin (start+2)→Bool) (ys : List Bool)
    (he : List.ofFn mid=List.ofFn h++ys) :
    cursorValue (initialCursor bits) mid=inputValue bits h := by
  unfold cursorValue initialCursor inputValue
  simp only [Vector.toList_map,List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact prefix_value h mid ys he i _

theorem initial_carry {start width : Nat} (bits : Vector (Fin start) width)
    (h : Fin start→Bool) (mid : Fin (start+2)→Bool)
    (he : List.ofFn mid=List.ofFn h++[true,false]) :
    mid (initialCursor bits).carry=true := by
  have hh:=congrArg (fun xs : List Bool=>xs[start]?) he
  dsimp only at hh
  rw [List.getElem?_append_right (by simp),List.length_ofFn,Nat.sub_self] at hh
  simpa only [initialCursor,List.getElem?_ofFn,show start<start+2 by omega,↓reduceDIte,List.getElem?_cons_zero,Option.some.injEq] using hh

/-- Every nonzero readout branch writes all 28 neighboring residues explicitly. -/
theorem neighborSuffix_branch (n start : Nat) (bits : Vector (Fin start) 207)
    (read : ConstantBit n→Bool) (history : Fin start→Bool)
    (ψ : State) (hψ : SupportedOn CleanReadout ψ) (b : InstrumentBranch)
    (hb : b∈((neighborSuffix n start 207 bits).instantiate read history).run)
    (hn : b.kraus ψ≠0) :
    b.kraus ψ=ψ ∧
      (∀i : Fin 14, readWord (List.ofFn history++b.history)
        (sumPositions (start+2+i.val*414) 207).toList=
        some ((i.val+1+inputValue bits history)%2^207)) ∧
      (∀i : Fin 13, readWord (List.ofFn history++b.history)
        (sumPositions (start+2+5796+414+i.val*828+414) 207).toList=
        some (2^207-1-((i.val+1+(2^207-1-inputValue bits history))%2^207))) := by
  unfold neighborSuffix at hb
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
  have hpos:=positiveWords_branch n 14 (start+2) 207 (initialCursor bits)
    read h₁ hcarr ψ hψ p hp hpn
  have hvn : v.kraus ψ≠0 := by
    simpa only [InstrumentBranch.seq,LinearMap.comp_apply,hpos.1] using hun
  let q:=(initialCursor bits).lift (14*(2*207))
  have hqc : h₂ q.carry=true := (lift_carry (initialCursor bits) _ h₁ h₂ p.history he₂).trans hcarr
  have hqv : cursorValue q h₂=inputValue bits history :=
    (lift_value (initialCursor bits) _ h₁ h₂ p.history he₂).trans hval
  obtain ⟨h₃,c,t,hc',ht,he₃,rfl⟩:=straight_append_branch _ _ read h₂ v hv
  have hcn : c.kraus ψ≠0 := by
    intro h;apply hvn;simp only [InstrumentBranch.seq,LinearMap.comp_apply,h,map_zero]
  have hcomp:=complementStep_post n q read h₂ hqc ψ hψ c hc' hcn h₃ he₃
  have htn : t.kraus ψ≠0 := by
    simpa only [InstrumentBranch.seq,LinearMap.comp_apply,hcomp.1] using hvn
  have hneg:=negativeWords_branch n 13 (start+2+14*(2*207)+2*207) 207 q.next
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
      have hj':=sumPositions_bound (start+2+i.val*414) 207 j hj
      have hi:=i.isLt
      simp only [List.length_ofFn]
      omega),he₂]
    simpa only [hval] using hpos.2 i
  · intro i
    rw [hfull₃]
    simpa only [hcomp.2.2,hqv] using hneg.2 i

end
end ShorECDLP.Entrant.NeighborReadout
namespace ShorECDLP.Entrant.NeighborReadout
open Quantum ShorECDLP.Challenge RoundedReadout
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

theorem input_read {start width : Nat} (bits : Vector (Fin start) width) (h : Fin start→Bool) :
    readWord (List.ofFn h) (bits.map Fin.val).toList=some (inputValue bits h) := by
  have hh:=readWord_of_actual_bits (List.ofFn h) (bits.toList.map Fin.val)
    (bits.toList.map h) (by simp only [List.map_map,List.getElem?_ofFn,
      Fin.isLt,↓reduceDIte,Fin.eta,Function.comp_def])
  have hw (bs : List Bool) : fourierWordLSB bs=boolWordToNat bs := by
    induction bs with
    | nil=>rfl
    | cons bit bs ih=>simp only [fourierWordLSB,boolWordToNat_cons,ih]
  simpa only [hw,inputValue,Vector.toList_map] using hh

theorem input_lt {start width : Nat} (bits : Vector (Fin start) width) (h : Fin start→Bool) :
    inputValue bits h<2^width := by
  have hh:=word_complement_sum (bits.toList.map h)
  simp only [List.length_map,Vector.length_toList] at hh
  have hp : 0<2^width := by positivity
  unfold inputValue
  omega

/-- The physical word list contains a correct explicit record for every offset -13..14. -/
theorem neighborSuffix_reads (n start : Nat) (bits : Vector (Fin start) 207)
    (read : ConstantBit n→Bool) (history : Fin start→Bool)
    (ψ : State) (hψ : SupportedOn CleanReadout ψ) (b : InstrumentBranch)
    (hb : b∈((neighborSuffix n start 207 bits).instantiate read history).run)
    (hn : b.kraus ψ≠0) (j : ℤ) (hj : -13≤j ∧ j≤14) :
    ∃ps∈rightWords bits, readWord (List.ofFn history++b.history) ps.toList=
      some ((((inputValue bits history : Nat) : ℤ)+j)%(2^207 : Nat)).toNat := by
  have hs:=neighborSuffix_branch n start bits read history ψ hψ b hb hn
  by_cases hz : j=0
  · subst j
    refine ⟨bits.map Fin.val,by simp [rightWords],?_⟩
    rw [readWord_append_left (List.ofFn history) b.history _ (by
      intro i hi
      simp only [Vector.toList_map,List.mem_map] at hi
      obtain ⟨k,_,rfl⟩:=hi
      simpa only [List.length_ofFn] using k.isLt),input_read]
    congr 1
    simpa only [Nat.zero_add,Int.natCast_zero,Nat.mod_eq_of_lt (input_lt bits history)] using
      (positive_word_mod (inputValue bits history) 0)
  · by_cases hp : 0<j
    · let i : Fin 14:=⟨j.toNat-1,by omega⟩
      have hi : (i.val+1 : ℤ)=j := by dsimp [i];omega
      refine ⟨sumPositions (start+2+i.val*414) 207,?_,?_⟩
      · unfold rightWords
        apply List.mem_cons_of_mem
        apply List.mem_append_left
        exact List.mem_ofFn.mpr ⟨i,rfl⟩
      · rw [hs.2.1 i,positive_word_mod]
        congr 2
        exact congrArg (fun z : ℤ=>(((inputValue bits history : Nat) : ℤ)+z)%(2^207 : Nat)) hi
    · let i : Fin 13:=⟨(-j).toNat-1,by omega⟩
      have hi : -((i.val+1 : Nat) : ℤ)=j := by dsimp [i];omega
      refine ⟨sumPositions (start+2+5796+414+i.val*828+414) 207,?_,?_⟩
      · unfold rightWords
        apply List.mem_cons_of_mem
        apply List.mem_append_right
        exact List.mem_ofFn.mpr ⟨i,rfl⟩
      · rw [hs.2.2 i,negative_word_mod _ _ (input_lt bits history)]
        congr 2
        rw [sub_eq_add_neg,hi]

end
end ShorECDLP.Entrant.NeighborReadout
namespace ShorECDLP.Entrant.Rounded
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open RoundedReadout
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def finePositions : List (Fin 886826276) :=
  Single.trialPositions.right.toList.attach.map fun i=>
    ⟨i.val,(Single.right_position_bound i.val i.property).2.trans (by decide)⟩
theorem finePositions_length : finePositions.length=207 := by
  simp [finePositions,Single.params]
def fineBits : Vector (Fin 886826276) 207 := Vector.ofFn fun i=>
  finePositions[i.val]'(by rw [finePositions_length];exact i.isLt)

def readout : Straight 851968 886826276 886843252 :=
  NeighborReadout.neighborSuffix 851968 886826276 207 fineBits

def program : Straight 851968 0 886843252 := Single.program.append readout

def positions (ps : Vector Nat 207) : TrialPositions NeighborReadout.params where
  left:=Single.trialPositions.left
  right:=ps

def layout : DecodeLayout := ⟨.wrappedShift,NeighborReadout.params,
  (NeighborReadout.rightWords fineBits).map positions,by
    simp only [List.length_map,NeighborReadout.rightWords_length];decide⟩

theorem readout_wellFormed : readout.WellFormed :=
  NeighborReadout.neighborSuffix_wellFormed _ _ _ _
theorem readout_t (read : ConstantBit 851968→Bool) (h : Fin 886826276→Bool) :
    (readout.instantiate read h).tCount=0 := NeighborReadout.neighborSuffix_t _ _ _ _ _ _
theorem readout_support (read : ConstantBit 851968→Bool) (h : Fin 886826276→Bool) :
    (readout.instantiate read h).wires⊆resetWires := by
  apply (NeighborReadout.neighborSuffix_support _ _ _ _ _ _).trans
  simp [List.subset_def,resetWires]

theorem fineBits_vals : fineBits.map Fin.val=Single.trialPositions.right := by
  apply Vector.ext
  intro i hi
  simp [fineBits,finePositions]
  rfl

theorem program_clean (read : ConstantBit 851968 → Bool) (b : InstrumentBranch)
    (hb : b ∈ (Single.program.instantiate read Fin.elim0).run) (ψ : State) :
    SupportedOn CleanReadout (b.kraus ψ) := by
  rw [Single.Distribution.program_run_data] at hb
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
  obtain ⟨a, _, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
  simp only [Single.Distribution.terminalInstrument, AdaptiveCircuit.run] at hc
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
  have h := resetRegister_clean resetWires resetWires_nodup e he
    (Quantum.run [.X 836] (a.kraus (Quantum.run [.X 836] ψ)))
  intro s hs
  exact ⟨h s hs 0 (by simp [resetWires]), h s hs 1 (by simp [resetWires])⟩

theorem pairAccept_value (left right : List Nat) (accept : Nat → Nat → Bool)
    (before : List Bool) (v : Nat) (hr : readWord before right = some v)
    (hf : Single.Distribution.pairAccept left right accept before = true) :
    ∃ a, readWord before left = some a ∧ accept a v = true := by
  unfold Single.Distribution.pairAccept at hf
  rw [hr] at hf
  cases ha : readWord before left with
  | none => simp only [ha, Option.bind_none, Option.getD_none, Bool.false_eq_true] at hf
  | some a =>
    exact ⟨a, rfl, by simpa only [ha, Option.bind_some, Option.map_some, Option.getD_some] using hf⟩


theorem verified_of_reads (ps : Vector Nat 207) (hps : ps∈NeighborReadout.rightWords fineBits)
    (Q : Point) (d : Nat) (hd : Q=d•G) (hist : List Bool) (a b : Nat)
    (hl : readWord hist Single.trialPositions.left.toList=some a)
    (hr : readWord hist ps.toList=some b)
    (hm : (d : ZMod order)∈fixedCandidates NeighborReadout.params a b) :
    (verifiedCandidate layout Q hist).isSome := by
  classical
  apply List.find?_isSome.mpr
  refine ⟨(d : ZMod order),?_,?_⟩
  · unfold candidates
    apply List.mem_flatMap.mpr
    refine ⟨positions ps,List.mem_map.mpr ⟨ps,hps,rfl⟩,?_⟩
    simpa only [decodeTrial,trialCandidates,positions,layout,hl,hr,fixedCandidates_take,Finset.mem_toList] using hm
  · simp only [decide_eq_true_eq,ZMod.val_natCast]
    rw [hd]
    exact nsmul_eq_nsmul_iff_modEq.mpr (by rw [generator_order];exact Nat.mod_mod _ _)

theorem suffix_accept (Q : Point) (d : Nat) (hd : Q=d•G)
    (read : ConstantBit 851968→Bool) (history : Fin 886826276→Bool)
    (ψ : State) (hψ : SupportedOn CleanReadout ψ)
    (hf : Single.Distribution.fineEvent (NeighborReadout.pairRecovered d) (List.ofFn history)=true)
    (b : InstrumentBranch) (hb : b∈(readout.instantiate read history).run)
    (hn : b.kraus ψ≠0) :
    (verifiedCandidate layout Q (List.ofFn history++b.history)).isSome := by
  have hr:=NeighborReadout.input_read fineBits history
  rw [fineBits_vals] at hr
  obtain ⟨a,ha,hp⟩:=pairAccept_value _ _ _ _ _ hr hf
  obtain ⟨i,hi⟩:=of_decide_eq_true hp
  obtain ⟨ps,hps,hread⟩:=NeighborReadout.neighborSuffix_reads 851968 886826276 fineBits
    read history ψ hψ b hb hn ((i.val : ℤ)-13) (by have h:=i.isLt;omega)
  apply verified_of_reads ps hps Q d hd _ a _ _ hread hi
  rw [NeighborReadout.readWord_append_left]
  · exact ha
  · intro j hj
    have h:=Single.left_position_bound j hj
    simpa only [List.length_ofFn] using h.trans (by decide : 487999958<886826276)

theorem normSq_ge_zero (ψ : State) : 0 ≤ normSq ψ := by
  have h := normSq_interference (0 : State) ψ
  have hz : normSq (0 : State) = 0 := by simp [normSq]
  simp only [zero_add, hz, mul_zero, zero_add] at h
  linarith [h.2]

theorem mass_ge_zero (I : Instrument) (ψ : State) : 0 ≤ I.bornMass ψ :=
  List.sum_nonneg (fun x hx => by
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
    exact normSq_ge_zero _)

theorem mass_filter_eq (I : Instrument) (p : InstrumentBranch → Bool) (ψ : State)
    (h : ∀ b ∈ I, b.kraus ψ ≠ 0 → p b = true) :
    Instrument.bornMass (I.filter p) ψ = I.bornMass ψ := by
  induction I with
  | nil => rfl
  | cons b I ih =>
    have ht := ih (fun c hc => h c (by simp [hc]))
    by_cases hb : p b = true
    · simpa [Instrument.bornMass, hb] using congrArg (normSq (b.kraus ψ) + ·) ht
    · have hz : b.kraus ψ = 0 := by
        by_contra hn
        exact hb (h b (by simp) hn)
      simpa [Instrument.bornMass, hb, hz, normSq] using ht

theorem appended_mass_lower (I : Instrument) (J : InstrumentBranch → Instrument)
    (p : InstrumentBranch → Bool) (q : InstrumentBranch → Bool) (ψ : State)
    (hn : ∀ a ∈ I, (J a).bornMass (a.kraus ψ) = normSq (a.kraus ψ))
    (hq : ∀ a ∈ I, p a = true → ∀ b ∈ J a,
      b.kraus (a.kraus ψ) ≠ 0 → q (a.seq b) = true) :
    Instrument.bornMass (I.filter p) ψ ≤
      Instrument.bornMass ((I.flatMap fun a => (J a).map a.seq).filter q) ψ := by
  induction I with
  | nil => simp [Instrument.bornMass]
  | cons a I ih =>
    have ht := ih (fun c hc => hn c (by simp [hc]))
      (fun c hc => hq c (by simp [hc]))
    have he : Instrument.bornMass (((J a).map a.seq).filter q) ψ =
        Instrument.bornMass ((J a).filter (fun b => q (a.seq b))) (a.kraus ψ) := by
      simp only [List.filter_map, Instrument.bornMass, List.map_map,
        InstrumentBranch.seq, LinearMap.comp_apply, Function.comp_def]
    simp only [List.flatMap_cons, List.filter_append, Instrument.bornMass,
      List.map_append, List.sum_append] at ht ⊢
    by_cases hp : p a = true
    · have heq := mass_filter_eq (J a) (fun b => q (a.seq b)) (a.kraus ψ)
        (hq a (by simp) hp)
      simp only [Instrument.bornMass] at he heq
      rw [he, heq]
      have hna := hn a (by simp)
      simp only [Instrument.bornMass] at hna
      rw [hna]
      simpa [Instrument.bornMass, hp] using add_le_add_left ht (normSq (a.kraus ψ))
    · have hpos := mass_ge_zero (((J a).map a.seq).filter q) ψ
      simp only [Instrument.bornMass] at hpos
      simpa [hp] using ht.trans (le_add_of_nonneg_left hpos)

theorem program_success (Q : Point) (d : Nat) (hn : Q ≠ 0) (hd : Q = d • G) :
    (99/100 : ℝ) ≤ Instrument.bornMass ((program.instantiate (readConstant Single.mixedCoefficientAt Q) Fin.elim0).run.filter
      (fun b => (verifiedCandidate layout Q b.history).isSome)) (ket zeroBasisState) := by
  apply (Single.Distribution.program_neighbor_success Q d hn hd).trans
  unfold program
  rw [Single.append_run_history]
  apply appended_mass_lower
  · intro a ha
    exact AdaptiveCircuit.run_preservesBornMass _
      (readout.instantiate_wellFormed _ _ readout_wellFormed) _
  · intro a ha hf b hb hne
    have hlen : a.history.length = 886826276 := by
      have h := straight_history_length Single.program (readConstant Single.mixedCoefficientAt Q) Fin.elim0 a ha
      omega
    have hh : List.ofFn (Single.historyAfter 886826276 Fin.elim0 a.history) = a.history := by
      simpa only [List.ofFn_zero, List.nil_append] using Single.historyAfter_list Fin.elim0 a.history (by simpa only [Nat.zero_add] using hlen)
    have h := suffix_accept Q d hd (readConstant Single.mixedCoefficientAt Q)
      (Single.historyAfter 886826276 Fin.elim0 a.history) (a.kraus (ket zeroBasisState))
      (program_clean _ a ha _) (by simpa only [hh] using hf) b hb hne
    simpa only [hh, InstrumentBranch.seq] using h

def entry : StraightEntry := Single.fixedEntry Single.mixedCoefficientAt program

def bounds : Bounds := ⟨854, 14712037779, 886843252⟩

theorem program_wellFormed : program.WellFormed :=
  straight_append_wellFormed _ _ Single.program_wellFormed readout_wellFormed

theorem program_support (read : ConstantBit 851968 → Bool) :
    (program.instantiate read Fin.elim0).wires ⊆ resetWires :=
  outer_append_support _ _ read Fin.elim0 resetWires (Single.program_support read)
    (readout_support read)

theorem program_qubits (read : ConstantBit 851968 → Bool) :
    (program.instantiate read Fin.elim0).qubitCount ≤ 854 := by
  have hs : (program.instantiate read Fin.elim0).wires.dedup.toFinset ⊆
      resetWires.toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (program_support read (by simpa using hw))
  have hc := (Finset.card_le_card hs).trans (List.toFinset_card_le _)
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
  simpa only [AdaptiveCircuit.qubitCount, resetWires_length] using hc

attribute [local irreducible] readout

theorem program_t (Q : Point) :
    (program.instantiate (readConstant Single.mixedCoefficientAt Q) Fin.elim0).tCount ≤ 14712037779 := by
  have h := outer_append_t_le Single.program readout (readConstant Single.mixedCoefficientAt Q)
    Fin.elim0 0 (fun history => le_of_eq (readout_t _ history))
  rw [Nat.add_zero] at h
  change ((Single.program.append readout).instantiate (readConstant Single.mixedCoefficientAt Q) Fin.elim0).tCount ≤ 14712037779
  exact h.trans (Single.program_t Q)

theorem program_slots : program.gateSlots ≤ 90000176648 := by
  unfold program
  rw [Straight.gateSlots_append]
  have hr : readout.gateSlots=59416 := by
    unfold readout
    exact NeighborReadout.neighborSuffix_slots 851968 886826276 207 fineBits
  rw [hr]
  have h := Single.program_slots
  omega

theorem certificate : Certificate officialLimits layout entry bounds where
  gateBudget := by
    rw [entry, Single.fixedEntry_slots]
    exact program_slots.trans (by decide)
  recordBudget := by
    change 886843252 ≤ officialLimits.measurements
    decide
  tableBudget := by
    rw [entry, Single.fixedEntry_rows]
    decide
  candidateBudget := by
    change 28 * (2*(order/2^207+2)) ≤ 56*(2^49+2)
    exact NeighborReadout.decoder_budget
  wellFormed := by
    rw [entry, Single.fixedEntry_wellFormed]
    exact program_wellFormed
  resources := by
    intro Q
    rw [entry, Single.fixedEntry_instantiate]
    exact ⟨program_qubits _, program_t Q, (program.measurementCount _ _).le⟩
  success := by
    intro Q d hn hd
    rw [entry, Single.fixedEntry_instantiate]
    exact program_success Q d hn hd

end
end ShorECDLP.Entrant.Rounded


section


/-! Exact cancellation of reversible gates across commuting classical operations.
The rewrite preserves the full quantum operator, including on nonzero workspace. -/
namespace ShorECDLP.Entrant.Cancellation
open Quantum
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000

def controls : Gate → List Wire
  | .CX a _ => [a]
  | .CCX a b _ => [a,b]
  | _ => []

def target : Gate → Wire
  | .X t | .H t | .CX _ t | .CCX _ _ t | .P _ _ t => t

def classicalGate : Gate → Bool
  | .X _ | .CX _ _ | .CCX _ _ _ => true
  | _ => false

def commutes (a b : Gate) : Bool :=
  classicalGate a && classicalGate b &&
    !(controls a).contains (target b) && !(controls b).contains (target a)

private theorem classical_commute (a b : Gate) (hc : commutes a b = true)
    (s : BasisState) :
    Classical.applyGate a (Classical.applyGate b s) =
      Classical.applyGate b (Classical.applyGate a s) := by
  cases a <;> cases b <;>
    simp_all [commutes, classicalGate, controls, target]
  all_goals
    funext w
    simp only [Classical.applyGate, upd]
    split_ifs <;> subst_vars <;> try contradiction
  all_goals simp only [eq_self, not_true_eq_false, false_and, and_false] at *
  all_goals try simp only [Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm, Bool.xor_not]

private theorem quantum_commute (a b : Gate) (hc : commutes a b = true)
    (ψ : State) :
    Quantum.applyGate a (Quantum.applyGate b ψ) =
      Quantum.applyGate b (Quantum.applyGate a ψ) := by
  have ha : Classical.IsClassicalGate a := by
    cases a <;> simp_all [commutes, classicalGate, Classical.IsClassicalGate]
  have hb : Classical.IsClassicalGate b := by
    cases b <;> simp_all [commutes, classicalGate, Classical.IsClassicalGate]
  have hk (s : BasisState) :
      Quantum.applyGate a (Quantum.applyGate b (ket s)) =
        Quantum.applyGate b (Quantum.applyGate a (ket s)) := by
    simp only [applyGate_ket_agrees_classical _ _ ha,
      applyGate_ket_agrees_classical _ _ hb, classical_commute a b hc]
  induction ψ using Finsupp.induction with
  | zero => simp only [map_zero]
  | @single_add s c ψ hs hc ih =>
    have he : Finsupp.single s c = c • ket s := by simp [ket]
    simp only [map_add, he, map_smul, ih, hk]

/-- Search only through commuting gates. Failure leaves the input untouched. -/
def erase (g : Gate) : Circuit → Option Circuit
  | [] => none
  | h :: hs =>
    if g = h ∧ g.adjoint = g then some hs
    else if commutes g h then (erase g hs).map (List.cons h)
    else none

/-- Append one gate to a reverse-order accumulation, cancelling when possible. -/
def push (g : Gate) (gs : Circuit) : Circuit :=
  match erase g gs with
  | some rest => rest
  | none => g :: gs

/-- The list is processed from right to left. -/
def optimize : Circuit → Circuit
  | [] => []
  | g :: gs => push g (optimize gs)

theorem erase_sublist (g : Gate) (xs ys : Circuit) (h : erase g xs = some ys) :
    ys.Sublist xs := by
  induction xs generalizing ys with
  | nil => simp [erase] at h
  | cons a xs ih =>
    simp only [erase] at h
    split at h
    · cases h
      exact List.Sublist.cons _ (List.Sublist.refl _)
    · split at h
      · cases he : erase g xs with
        | none => simp [he] at h
        | some zs =>
          simp only [he, Option.map_some, Option.some.injEq] at h
          subst ys
          exact List.Sublist.cons₂ _ (ih zs he)
      · simp at h

theorem push_sublist (g : Gate) (xs : Circuit) : (push g xs).Sublist (g :: xs) := by
  unfold push
  cases h : erase g xs with
  | none => exact List.Sublist.refl _
  | some ys => exact List.Sublist.cons _ (erase_sublist g xs ys h)

theorem optimize_sublist (xs : Circuit) : (optimize xs).Sublist xs := by
  induction xs with
  | nil => exact List.Sublist.refl _
  | cons g xs ih =>
    exact (push_sublist g (optimize xs)).trans (List.Sublist.cons₂ g ih)

private theorem erase_mem (g : Gate) (xs ys : Circuit) (h : erase g xs = some ys) :
    ∀ a ∈ ys, a ∈ xs := by
  induction xs generalizing ys with
  | nil => simp [erase] at h
  | cons a xs ih =>
    simp only [erase] at h
    split at h
    · cases h
      exact fun b hb => List.mem_cons_of_mem _ hb
    · split at h
      · cases he : erase g xs with
        | none => simp [he] at h
        | some zs =>
          simp only [he, Option.map_some, Option.some.injEq] at h
          subst ys
          intro b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih zs he b hb)
      · simp at h

theorem push_mem (g : Gate) (xs : Circuit) :
    ∀ a ∈ push g xs, a ∈ g :: xs := by
  unfold push
  cases h : erase g xs with
  | none => exact fun _ ha => ha
  | some ys => exact fun a ha => List.mem_cons_of_mem _ (erase_mem g xs ys h a ha)

theorem optimize_mem (xs : Circuit) : ∀ a ∈ optimize xs, a ∈ xs := by
  induction xs with
  | nil => simp [optimize]
  | cons g xs ih =>
    intro a ha
    rcases List.mem_cons.mp (push_mem g (optimize xs) a ha) with rfl | hh
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih a hh)

theorem optimize_wellFormed (xs : Circuit) (h : CircuitWellFormed xs) :
    CircuitWellFormed (optimize xs) :=
  fun a ha => h a (optimize_mem xs a ha)

private theorem erase_run (g : Gate) (xs ys : Circuit)
    (hg : g.WellFormed) (h : erase g xs = some ys) (ψ : State) :
    Quantum.run (g :: xs) ψ = Quantum.run ys ψ := by
  induction xs generalizing ys ψ with
  | nil => simp [erase] at h
  | cons a xs ih =>
    simp only [erase] at h
    split at h
    · rename_i he
      rcases he with ⟨rfl, hadj⟩
      cases h
      simp only [Quantum.run_cons]
      have hi := applyGate_adjoint_applyGate g hg ψ
      rw [hadj] at hi
      rw [hi]
    · split at h
      · rename_i hc
        cases he : erase g xs with
        | none => simp [he] at h
        | some zs =>
          simp only [he, Option.map_some, Option.some.injEq] at h
          subst ys
          simp only [Quantum.run_cons]
          rw [← quantum_commute g a hc]
          exact ih zs he (Quantum.applyGate a ψ)
      · simp at h

theorem push_run (g : Gate) (xs : Circuit) (hg : g.WellFormed) (ψ : State) :
    Quantum.run (push g xs) ψ = Quantum.run (g :: xs) ψ := by
  unfold push
  cases h : erase g xs with
  | none => rfl
  | some ys => exact (erase_run g xs ys hg h ψ).symm

theorem optimize_run (xs : Circuit) (h : CircuitWellFormed xs) :
    Quantum.run (optimize xs) = Quantum.run xs := by
  induction xs with
  | nil => rfl
  | cons g xs ih =>
    have hg := h g (by simp)
    have ht : CircuitWellFormed xs := fun a ha => h a (by simp [ha])
    apply LinearMap.ext
    intro ψ
    rw [optimize, push_run _ _ hg, Quantum.run_cons, ih ht, Quantum.run_cons]

end ShorECDLP.Entrant.Cancellation

namespace ShorECDLP.Entrant.Cancellation
open Paper2607_13816

/-- The terminal-epoch restore has two redundant traversals of its predicate v-chain. -/
def epochSource : Circuit := blockCForward indexedStepProductionRegisters

def reducedEpoch : Circuit := optimize epochSource

private instance gateWellFormedDecidable (g : Gate) : Decidable g.WellFormed := by
  cases g <;> unfold Gate.WellFormed <;> infer_instance

theorem epochSource_wellFormed : CircuitWellFormed epochSource := by
  unfold CircuitWellFormed
  decide +kernel

theorem reducedEpoch_run : Quantum.run reducedEpoch = Quantum.run epochSource :=
  optimize_run epochSource epochSource_wellFormed

theorem reducedEpoch_sublist : reducedEpoch.Sublist epochSource := optimize_sublist epochSource

theorem reducedEpoch_counts : ShorECDLP.tCount epochSource = 245 ∧
    ShorECDLP.tCount reducedEpoch = 133 ∧ reducedEpoch.length = 24 := by
  decide +kernel

end ShorECDLP.Entrant.Cancellation


namespace ShorECDLP.Entrant.Optimization
open Quantum Challenge Paper2607_13816.ChallengeMigration

/-- A syntactic subsequence retaining every measurement and classical control. -/
inductive Drops {n : Nat} : {s e : Nat} → Straight n s e → Straight n s e → Nat → Prop
  | refl {s e} (p : Straight n s e) : Drops p p 0
  | skip {s e} (g : Gate) {p q : Straight n s e} {d : Nat} :
      Drops p q d → Drops (.gate (.literal g) p) q (tCost g + d)
  | gate {s e} (g : TemplateGate n) {p q : Straight n s e} {d : Nat} :
      Drops p q d → Drops (.gate g p) (.gate g q) d
  | record {s e} (i : Fin s) (v : Bool) (g : Gate) {p q : Straight n s e} {d : Nat} :
      Drops p q d → Drops (.recordGate i v g p) (.recordGate i v g q) d
  | measure {s e} (w : Wire) {p q : Straight n (s+1) e} {d : Nat} :
      Drops p q d → Drops (.measure w p) (.measure w q) d

theorem Drops.wellFormed {n s e d} {p q : Straight n s e}
    (h : Drops p q d) (hp : p.WellFormed) : q.WellFormed := by
  induction h with
  | refl => exact hp
  | skip g h ih => exact ih hp.2
  | gate g h ih => exact ⟨hp.1, ih hp.2⟩
  | record i v g h ih => exact ⟨hp.1, ih hp.2⟩
  | measure w h ih => exact ih hp

theorem Drops.slots {n s e d} {p q : Straight n s e}
    (h : Drops p q d) : q.gateSlots ≤ p.gateSlots := by
  induction h <;> simp_all [Straight.gateSlots]; omega

theorem Drops.tCount {n s e d} {p q : Straight n s e}
    (h : Drops p q d) (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    (q.instantiate read history).tCount + d = (p.instantiate read history).tCount := by
  induction h with
  | refl => omega
  | skip g h ih =>
    simp only [Straight.instantiate, TemplateGate.instantiate, AdaptiveCircuit.tCount,
      ShorECDLP.tCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    have hh := ih history
    omega
  | gate g h ih =>
    simp only [Straight.instantiate, AdaptiveCircuit.tCount]
    have hh := ih history
    omega
  | record i v g h ih =>
    simp only [Straight.instantiate, AdaptiveCircuit.tCount]
    have hh := ih history
    omega
  | measure w h ih =>
    simp only [Straight.instantiate, AdaptiveCircuit.tCount]
    have hf := ih (Fin.lastCases false history)
    have ht := ih (Fin.lastCases true history)
    omega

theorem Drops.wires {n s e d} {p q : Straight n s e}
    (h : Drops p q d) (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    ∀ w ∈ (q.instantiate read history).wires, w ∈ (p.instantiate read history).wires := by
  induction h with
  | refl => exact fun _ hw => hw
  | skip g h ih =>
    intro w hw
    exact List.mem_append_right _ (ih history w hw)
  | gate g h ih =>
    intro w hw
    simp only [Straight.instantiate, AdaptiveCircuit.wires, List.mem_append] at hw ⊢
    exact hw.imp id (ih history w)
  | record i v g h ih =>
    intro w hw
    simp only [Straight.instantiate, AdaptiveCircuit.wires, List.mem_append] at hw ⊢
    exact hw.imp id (ih history w)
  | measure v h ih =>
    intro w hw
    simp only [Straight.instantiate, AdaptiveCircuit.wires, List.mem_cons, List.mem_append] at hw ⊢
    rcases hw with he | hf | ht
    · exact Or.inl he
    · exact Or.inr (Or.inl (ih (Fin.lastCases false history) w hf))
    · exact Or.inr (Or.inr (ih (Fin.lastCases true history) w ht))

private theorem Drops.append_right {n a b c d} (p : Straight n a b)
    {q q' : Straight n b c} (h : Drops q q' d) : Drops (p.append q) (p.append q') d := by
  induction p with
  | done => exact h
  | gate g p ih => exact Drops.gate g (ih h)
  | recordGate i v g p ih => exact Drops.record i v g (ih h)
  | measure w p ih => exact Drops.measure w (ih h)

theorem Drops.append {n a b c d f} {p p' : Straight n a b} {q q' : Straight n b c}
    (hp : Drops p p' d) (hq : Drops q q' f) :
    Drops (p.append q) (p'.append q') (d+f) := by
  induction hp with
  | refl p => simpa using Drops.append_right p hq
  | skip g h ih => simpa [Nat.add_assoc] using Drops.skip g (ih hq)
  | gate g h ih => exact Drops.gate g (ih hq)
  | record i v g h ih => exact Drops.record i v g (ih hq)
  | measure w h ih => exact Drops.measure w (ih hq)

private theorem tCount_le_of_sublist {xs ys : Circuit} (h : xs.Sublist ys) :
    ShorECDLP.tCount xs ≤ ShorECDLP.tCount ys := by
  induction h <;> simp_all [ShorECDLP.tCount]; omega

theorem Drops.literal {n s} {xs ys : Circuit} (h : ys.Sublist xs) :
    Drops (literalProgram xs : Straight n s s) (literalProgram ys)
      (ShorECDLP.tCount xs - ShorECDLP.tCount ys) := by
  induction h with
  | slnil => exact Drops.refl _
  | cons a h ih =>
    have ht := tCount_le_of_sublist h
    simpa [literalProgram, gateProgram, ShorECDLP.tCount_cons, Nat.add_sub_assoc ht]
      using Drops.skip a ih
  | cons₂ a h ih =>
    simpa [literalProgram, gateProgram, ShorECDLP.tCount_cons, Nat.add_sub_add_left] using Drops.gate (.literal a) ih

/-- Structural circuit rewrites, with exact operator equality at unitary leaves. -/
inductive Rewrites {n : Nat} : {s e : Nat} → Straight n s e → Straight n s e → Prop
  | refl {s e} (p : Straight n s e) : Rewrites p p
  | literal {s} (xs ys : Circuit) : Quantum.run xs = Quantum.run ys →
      Rewrites (literalProgram xs : Straight n s s) (literalProgram ys)
  | gate {s e} (g : TemplateGate n) {p q : Straight n s e} :
      Rewrites p q → Rewrites (.gate g p) (.gate g q)
  | record {s e} (i : Fin s) (v : Bool) (g : Gate) {p q : Straight n s e} :
      Rewrites p q → Rewrites (.recordGate i v g p) (.recordGate i v g q)
  | measure {s e} (w : Wire) {p q : Straight n (s+1) e} :
      Rewrites p q → Rewrites (.measure w p) (.measure w q)
  | append {a b c} {p p' : Straight n a b} {q q' : Straight n b c} :
      Rewrites p p' → Rewrites q q' → Rewrites (p.append q) (p'.append q')

private noncomputable def branchPrefix (history : List Bool) (u : State →ₗ[ℂ] State)
    (branches : Instrument) : Instrument :=
  branches.map fun b => ⟨history ++ b.history, b.kraus.comp u⟩

private theorem prefix_prefix (a b : List Bool) (u v : State →ₗ[ℂ] State) (bs : Instrument) :
    branchPrefix a u (branchPrefix b v bs) = branchPrefix (a++b) (v.comp u) bs := by
  simp only [branchPrefix, List.map_map]
  congr 1
  funext branch
  simp only [Function.comp_apply, List.append_assoc, LinearMap.comp_assoc]

/-- Continuation evaluator used only to prove context closure, never as submitted data. -/
private noncomputable def evaluate {n s e} (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool)
    (tail : (Fin e → Bool) → Instrument) : Instrument :=
  match p with
  | .done => tail history
  | .gate g p => branchPrefix [] (Quantum.run (g.instantiate read)) (evaluate p read history tail)
  | .recordGate i v g p => branchPrefix [] (Quantum.run (if history i=v then [g] else []))
      (evaluate p read history tail)
  | .measure w p =>
      branchPrefix [false] (xResetKraus w false) (evaluate p read (Fin.lastCases false history) tail) ++
      branchPrefix [true] (xResetKraus w true) (evaluate p read (Fin.lastCases true history) tail)

private theorem evaluate_append {n a b c} (p : Straight n a b) (q : Straight n b c)
    (read : ConstantBit n → Bool) (history : Fin a → Bool)
    (tail : (Fin c → Bool) → Instrument) :
    evaluate (p.append q) read history tail =
      evaluate p read history (fun h => evaluate q read h tail) := by
  induction p with
  | done => rfl
  | gate g p ih => simp only [Straight.append, evaluate, ih]
  | recordGate i v g p ih => simp only [Straight.append, evaluate, ih]
  | measure w p ih => simp only [Straight.append, evaluate, ih]

private theorem evaluate_literal {n s} (xs : Circuit) (read : ConstantBit n → Bool)
    (history : Fin s → Bool) (tail : (Fin s → Bool) → Instrument) :
    evaluate (literalProgram xs) read history tail = branchPrefix [] (Quantum.run xs) (tail history) := by
  induction xs with
  | nil => simp [literalProgram, gateProgram, evaluate, branchPrefix, Quantum.run]
  | cons g xs ih =>
    simp only [literalProgram, List.map_cons, gateProgram, evaluate, TemplateGate.instantiate] at ⊢
    change branchPrefix [] (Quantum.run [g]) (evaluate (literalProgram xs) read history tail) = _
    rw [ih, prefix_prefix]
    simp [Quantum.run]

private theorem Rewrites.eval_eq {n s e} {p q : Straight n s e} (h : Rewrites p q)
    (read : ConstantBit n → Bool) (history : Fin s → Bool)
    (tail : (Fin e → Bool) → Instrument) : evaluate p read history tail = evaluate q read history tail := by
  induction h with
  | refl => rfl
  | literal xs ys he => simp only [evaluate_literal, he]
  | gate g h ih =>
    simp only [evaluate, ih]
  | record i v g h ih =>
    simp only [evaluate, ih]
  | measure w h ih =>
    simp only [evaluate, ih]
  | append hp hq ip iq =>
    simp only [evaluate_append]
    rw [ip]
    congr 1
    funext hist
    exact iq hist tail

private theorem evaluate_run {n s e} (p : Straight n s e) (read : ConstantBit n → Bool)
    (history : Fin s → Bool) :
    evaluate p read history (fun _ => [{history := [], kraus := LinearMap.id}]) =
      (p.instantiate read history).run := by
  induction p with
  | done => rfl
  | gate g p ih => simp only [evaluate, Straight.instantiate, AdaptiveCircuit.run, ih]; rfl
  | recordGate i v g p ih => simp only [evaluate, Straight.instantiate, AdaptiveCircuit.run, ih]; rfl
  | measure w p ih => simp only [evaluate, Straight.instantiate, AdaptiveCircuit.run, ih]; rfl

theorem Rewrites.run {n s e} {p q : Straight n s e} (h : Rewrites p q)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    (p.instantiate read history).run = (q.instantiate read history).run := by
  rw [← evaluate_run, ← evaluate_run]
  exact h.eval_eq read history _

private theorem reindex_append {n m a b c} (f : Fin n → Fin m)
    (p : Straight n a b) (q : Straight n b c) :
    reindexStraight f (p.append q) = (reindexStraight f p).append (reindexStraight f q) := by
  induction p <;> simp_all [reindexStraight, Straight.append]

private theorem reindex_literal {n m s} (f : Fin n → Fin m) (xs : Circuit) :
    reindexStraight f (literalProgram xs : Straight n s s) = literalProgram xs := by
  induction xs <;> simp_all [literalProgram, gateProgram, reindexStraight, reindexGate]

theorem Rewrites.reindex {n m s e} {p q : Straight n s e} (h : Rewrites p q)
    (f : Fin n → Fin m) : Rewrites (reindexStraight f p) (reindexStraight f q) := by
  induction h with
  | refl => exact Rewrites.refl _
  | literal xs ys he => simpa only [reindex_literal] using Rewrites.literal (n := m) xs ys he
  | gate g h ih => exact Rewrites.gate _ ih
  | record i v g h ih => exact Rewrites.record _ _ _ ih
  | measure w h ih => exact Rewrites.measure _ ih
  | append hp hq ip iq => simpa only [reindex_append] using Rewrites.append ip iq

theorem Drops.reindex {n m s e d} {p q : Straight n s e} (h : Drops p q d)
    (f : Fin n → Fin m) : Drops (reindexStraight f p) (reindexStraight f q) d := by
  induction h with
  | refl => exact Drops.refl _
  | skip g h ih => exact Drops.skip _ ih
  | gate g h ih => exact Drops.gate _ ih
  | record i v g h ih => exact Drops.record _ _ _ ih
  | measure w h ih => exact Drops.measure _ ih

private theorem relabel_append {n a b c} (f : Wire ≃ Wire)
    (p : Straight n a b) (q : Straight n b c) :
    relabelStraight f (p.append q) = (relabelStraight f p).append (relabelStraight f q) := by
  induction p <;> simp_all [relabelStraight, Straight.append]

private theorem relabel_literal {n s} (f : Wire ≃ Wire) (xs : Circuit) :
    relabelStraight f (literalProgram xs : Straight n s s) = literalProgram (xs.map (Gate.relabel f)) := by
  induction xs <;> simp_all [literalProgram, gateProgram, relabelStraight, relabelTemplateGate]

private theorem relabel_run_eq (f : Wire ≃ Wire) (xs ys : Circuit)
    (h : Quantum.run xs = Quantum.run ys) :
    Quantum.run (xs.map (Gate.relabel f)) = Quantum.run (ys.map (Gate.relabel f)) := by
  apply LinearMap.ext
  intro ψ
  have hx := Quantum.run_relabel f xs (relabelState f.symm ψ)
  have hy := Quantum.run_relabel f ys (relabelState f.symm ψ)
  simp only [relabelState_symm_right] at hx hy
  rw [hx, hy, h]

theorem Rewrites.relabel {n s e} {p q : Straight n s e} (h : Rewrites p q)
    (f : Wire ≃ Wire) : Rewrites (relabelStraight f p) (relabelStraight f q) := by
  induction h with
  | refl => exact Rewrites.refl _
  | literal xs ys he =>
    simpa only [relabel_literal] using Rewrites.literal (n := n)
      (xs.map (Gate.relabel f)) (ys.map (Gate.relabel f)) (relabel_run_eq f xs ys he)
  | gate g h ih => exact Rewrites.gate _ ih
  | record i v g h ih => exact Rewrites.record _ _ _ ih
  | measure w h ih => exact Rewrites.measure _ ih
  | append hp hq ip iq => simpa only [relabel_append] using Rewrites.append ip iq

theorem Drops.relabel {n s e d} {p q : Straight n s e} (h : Drops p q d)
    (f : Wire ≃ Wire) : Drops (relabelStraight f p) (relabelStraight f q) d := by
  induction h with
  | refl => exact Drops.refl _
  | skip g h ih =>
    have he : tCost (g.relabel f) = tCost g := by cases g <;> rfl
    simpa only [he] using Drops.skip (g.relabel f) ih
  | gate g h ih => exact Drops.gate _ ih
  | record i v g h ih => exact Drops.record _ _ _ ih
  | measure w h ih => exact Drops.measure _ ih

private theorem shift_append {n a b c} (offset : Nat)
    (p : Straight n a b) (q : Straight n b c) :
    shiftStraight offset (p.append q) = (shiftStraight offset p).append (shiftStraight offset q) := by
  induction p <;> simp_all [shiftStraight, Straight.append]

private theorem shift_literal {n s} (offset : Nat) (xs : Circuit) :
    shiftStraight offset (literalProgram xs : Straight n s s) = literalProgram xs := by
  induction xs <;> simp_all [literalProgram, gateProgram, shiftStraight]

theorem Rewrites.shift {n s e} {p q : Straight n s e} (h : Rewrites p q)
    (offset : Nat) : Rewrites (shiftStraight offset p) (shiftStraight offset q) := by
  induction h with
  | refl => exact Rewrites.refl _
  | literal xs ys he => simpa only [shift_literal] using Rewrites.literal (n := n) xs ys he
  | gate g h ih => exact Rewrites.gate _ ih
  | record i v g h ih => exact Rewrites.record _ _ _ ih
  | measure w h ih => exact Rewrites.measure _ ih
  | append hp hq ip iq => simpa only [shift_append] using Rewrites.append ip iq

theorem Drops.shift {n s e d} {p q : Straight n s e} (h : Drops p q d)
    (offset : Nat) : Drops (shiftStraight offset p) (shiftStraight offset q) d := by
  induction h with
  | refl => exact Drops.refl _
  | skip g h ih => exact Drops.skip _ ih
  | gate g h ih => exact Drops.gate _ ih
  | record i v g h ih => exact Drops.record _ _ _ ih
  | measure w h ih => exact Drops.measure _ ih

theorem Rewrites.castFinish {n s e f} {p q : Straight n s e} (h : Rewrites p q)
    (he : e=f) : Rewrites (castFinish he p) (castFinish he q) := by
  subst f
  exact h

theorem Drops.castFinish {n s e f d} {p q : Straight n s e} (h : Drops p q d)
    (he : e=f) : Drops (castFinish he p) (castFinish he q) d := by
  subst f
  exact h

private theorem qubitCount_mono (a b : AdaptiveCircuit)
    (h : ∀ w ∈ a.wires, w ∈ b.wires) : a.qubitCount ≤ b.qubitCount := by
  have hh : a.wires.toFinset ⊆ b.wires.toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (h w (List.mem_toFinset.mp hw))
  simpa only [AdaptiveCircuit.qubitCount, List.card_toFinset] using Finset.card_le_card hh

/-- Retain the exact table and decoder cursor while substituting an equivalent program. -/
def replaceEntry (e : StraightEntry) (p : Straight e.coefficients.length 0 e.finalCursor) : StraightEntry :=
  ⟨e.coefficients,e.finalCursor,p⟩

/-- Transport the protected certificate along a verified gate deletion with exact T savings. -/
theorem replacement_certificate {limits : Limits} {layout : DecodeLayout}
    {entry : StraightEntry} {bounds : Bounds} (original : Certificate limits layout entry bounds)
    {p : Straight entry.coefficients.length 0 entry.finalCursor} {saving : Nat}
    (hd : Drops entry.program p saving) (he : Rewrites entry.program p) :
    Certificate limits layout (replaceEntry entry p)
      ⟨bounds.qubits,bounds.tModel-saving,bounds.measurements⟩ := by
  refine ⟨hd.slots.trans original.gateBudget, original.recordBudget, original.tableBudget,
    original.candidateBudget, hd.wellFormed original.wellFormed, ?_, ?_⟩
  · intro Q
    have ho := original.resources Q
    have hq := qubitCount_mono (p.instantiate (readConstant entry.coefficients.get Q) Fin.elim0)
      (entry.instantiate Q) (hd.wires _ _)
    have ht := hd.tCount (readConstant entry.coefficients.get Q) Fin.elim0
    have hm := Straight.measurementCount p (readConstant entry.coefficients.get Q) Fin.elim0
    have hm' := Straight.measurementCount entry.program (readConstant entry.coefficients.get Q) Fin.elim0
    change (entry.instantiate Q).qubitCount ≤ bounds.qubits ∧
      (entry.instantiate Q).tCount ≤ bounds.tModel ∧
      (entry.instantiate Q).measurementCount ≤ bounds.measurements at ho
    change (p.instantiate (readConstant entry.coefficients.get Q) Fin.elim0).qubitCount ≤ bounds.qubits ∧
      (p.instantiate (readConstant entry.coefficients.get Q) Fin.elim0).tCount ≤ bounds.tModel-saving ∧
      (p.instantiate (readConstant entry.coefficients.get Q) Fin.elim0).measurementCount ≤ bounds.measurements
    exact ⟨hq.trans ho.1, by dsimp only [StraightEntry.instantiate] at ho; omega,
      by dsimp only [StraightEntry.instantiate] at ho; omega⟩
  · intro Q d hQ hdQ
    have hh := he.run (readConstant entry.coefficients.get Q) Fin.elim0
    change (99 : ℝ)/100 ≤ Instrument.bornMass
      (((p.instantiate (readConstant entry.coefficients.get Q) Fin.elim0).run).filter _) (ket zeroBasisState)
    rw [← hh]
    exact original.success Q d hQ hdQ

/-- A program together with the exact proof needed to replace a fixed source context. -/
structure Patch {n s e : Nat} (source : Straight n s e) (saving : Nat) where
  program : Straight n s e
  drops : Drops source program saving
  rewrites : Rewrites source program

namespace Patch
noncomputable section

def refl {n s e} (p : Straight n s e) : Patch p 0 := ⟨p, Drops.refl p, Rewrites.refl p⟩

def castSaving {n s e a b} {p : Straight n s e} (h : Patch p a) (he : a=b) : Patch p b := he ▸ h

def literal {n s d} (xs ys : Circuit) (hs : ys.Sublist xs)
    (hr : Quantum.run xs = Quantum.run ys)
    (ht : ShorECDLP.tCount ys + d = ShorECDLP.tCount xs) :
    Patch (literalProgram xs : Straight n s s) d := by
  refine ⟨literalProgram ys, ?_, Rewrites.literal xs ys hr⟩
  have hd : ShorECDLP.tCount xs - ShorECDLP.tCount ys = d := by omega
  simpa only [hd] using Drops.literal (n := n) (s := s) hs

def append {n a b c d f} {p : Straight n a b} {q : Straight n b c}
    (hp : Patch p d) (hq : Patch q f) : Patch (p.append q) (d+f) :=
  ⟨hp.program.append hq.program, hp.drops.append hq.drops, hp.rewrites.append hq.rewrites⟩

def castFinish {n s e f d} {p : Straight n s e} (hp : Patch p d) (he : e=f) :
    Patch (Paper2607_13816.ChallengeMigration.castFinish he p) d :=
  ⟨Paper2607_13816.ChallengeMigration.castFinish he hp.program, hp.drops.castFinish he, hp.rewrites.castFinish he⟩

def appendCompiled {n start d f}
    (p : (count : Nat) × Straight n start (start+count))
    (q : (count : Nat) × Straight n (start+p.1) (start+p.1+count))
    (hp : Patch p.2 d) (hq : Patch q.2 f) :
    Patch (Paper2607_13816.ChallengeMigration.appendCompiled p q).2 (d+f) :=
  (hp.append hq).castFinish (Nat.add_assoc start p.1 q.1)

def sequenceCons {n start d f} (head : FixedSegment n) (tail : List (FixedSegment n))
    (hp : Patch (head start).2 d)
    (hq : Patch (sequenceProgram n tail (start+(head start).1)).2 f) :
    Patch (sequenceProgram n (head::tail) start).2 (d+f) :=
  appendCompiled (head start) (sequenceProgram n tail (start+(head start).1)) hp hq

def gate {n s e d} (g : TemplateGate n) {p : Straight n s e} (hp : Patch p d) :
    Patch (.gate g p) d := ⟨.gate g hp.program, Drops.gate g hp.drops, Rewrites.gate g hp.rewrites⟩

def record {n s e d} (i : Fin s) (v : Bool) (g : Gate) {p : Straight n s e}
    (hp : Patch p d) : Patch (.recordGate i v g p) d :=
  ⟨.recordGate i v g hp.program, Drops.record i v g hp.drops, Rewrites.record i v g hp.rewrites⟩

def measure {n s e d} (w : Wire) {p : Straight n (s+1) e} (hp : Patch p d) :
    Patch (.measure w p) d :=
  ⟨.measure w hp.program, Drops.measure w hp.drops, Rewrites.measure w hp.rewrites⟩

def reindex {n m s e d} {p : Straight n s e} (hp : Patch p d) (f : Fin n → Fin m) :
    Patch (reindexStraight f p) d :=
  ⟨reindexStraight f hp.program, hp.drops.reindex f, hp.rewrites.reindex f⟩

def relabel {n s e d} {p : Straight n s e} (hp : Patch p d) (f : Wire ≃ Wire) :
    Patch (relabelStraight f p) d :=
  ⟨relabelStraight f hp.program, hp.drops.relabel f, hp.rewrites.relabel f⟩

def shift {n s e d} {p : Straight n s e} (hp : Patch p d) (offset : Nat) :
    Patch (shiftStraight offset p) d :=
  ⟨shiftStraight offset hp.program, hp.drops.shift offset, hp.rewrites.shift offset⟩

end
end Patch

end ShorECDLP.Entrant.Optimization


namespace ShorECDLP.Entrant.Optimization
open Quantum Challenge Paper2607_13816.ChallengeMigration
open Paper2607_13816
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 200000
set_option Elab.async false
attribute [local irreducible] sequenceProgram appendCompiled literalProgram
  remainderBlockProgram coefficientBlockProgram phaseProgram hProgram intervalProgram coefficientProgram
  preprocessProgram productionParityProgram measuredStepProgram measuredScheduleProgram
  measuredEEAForwardProgram measuredForwardWrapperProgram multiplyWorkProgram divisionAfterResetProgram
  divisionProgram zeroDivisionProgram fieldLookupAddProgram signedFieldProgram pointSquareProgram
  zeroMultiplicationProgram xNegateProgram coordinateProgram
  measuredInverseStepProgram measuredEEAReverseProgram measuredReverseWrapperProgram
  hInverseProgram phaseInverseProgram coefficientInverseProgram intervalInverseProgram
  measuredForwardDataBankProgram measuredReverseDataBankProgram multiplicationProgram
  multiplicationAfterResetProgram multiplicationCorrectionProgram multiplicationCleanupProgram
  multiplyDataProgram unmultiplyDataProgram divisionCorrectionProgram collectProgram


def Patch.prependCompiled {n start d} (gs : Circuit)
    (p : (count : Nat) × Straight n start (start+count)) (hp : Patch p.2 d) :
    Patch (Paper2607_13816.ChallengeMigration.prependCompiled gs p).2 d := by
  unfold Paper2607_13816.ChallengeMigration.prependCompiled
  exact ((Patch.refl (literalProgram gs)).append hp).castSaving (Nat.zero_add d)

def Patch.surroundCompiled {n start d} (before after : Circuit)
    (p : (count : Nat) × Straight n start (start+count)) (hp : Patch p.2 d) :
    Patch (Paper2607_13816.ChallengeMigration.surroundCompiled before after p).2 d := by
  unfold Paper2607_13816.ChallengeMigration.surroundCompiled Paper2607_13816.ChallengeMigration.prependCompiled
  exact ((Patch.refl (literalProgram before)).append
    ((Patch.appendCompiled p ⟨0, literalProgram after⟩ hp (Patch.refl _)).castSaving (Nat.add_zero d))).castSaving (Nat.zero_add d)

/-- Rewrite one terminal-epoch restore inside an otherwise untouched literal segment. -/
def epochPatch (n s : Nat) (tail : Circuit) :
    Patch (literalProgram (Cancellation.epochSource ++ tail) : Straight n s s) 112 := by
  apply Patch.literal _ (Cancellation.reducedEpoch ++ tail)
  · exact Cancellation.reducedEpoch_sublist.append (List.Sublist.refl _)
  · simp only [Quantum.run_append_map, Cancellation.reducedEpoch_run]
  · have h := Cancellation.reducedEpoch_counts
    simp only [ShorECDLP.tCount_append, h.1, h.2.1]
    omega



set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def aSource : Circuit := blockAForward indexedStepProductionRegisters
def aMiddle : Circuit := (aSource.drop 837).take 33
def aReduced : Circuit := aSource.take 837 ++ Cancellation.optimize aMiddle ++ aSource.drop 870

private theorem split_three (xs : Circuit) (a b : Nat) :
    xs = xs.take a ++ (xs.drop a).take b ++ xs.drop (a+b) := by
  rw [List.append_assoc, ← List.drop_drop]
  rw [List.take_append_drop, List.take_append_drop]

private theorem aSplit : aSource = aSource.take 837 ++ aMiddle ++ aSource.drop 870 :=
  split_three aSource 837 33

private theorem aMiddle_wellFormed : CircuitWellFormed aMiddle := by
  unfold CircuitWellFormed
  decide +kernel

private theorem aMiddle_counts : ShorECDLP.tCount aMiddle = 105 ∧
    ShorECDLP.tCount (Cancellation.optimize aMiddle) = 7 := by
  decide +kernel

def aPatch (n start : Nat) : Patch (literalProgram aSource : Straight n start start) 98 := by
  apply Patch.literal _ aReduced
  · conv_rhs => rw [aSplit]
    exact ((List.Sublist.refl _).append (Cancellation.optimize_sublist aMiddle)).append (List.Sublist.refl _)
  · have h := Cancellation.optimize_run aMiddle aMiddle_wellFormed
    conv_lhs => rw [aSplit]
    simp only [aReduced, Quantum.run_append_map, h]
  · conv_rhs => rw [aSplit]
    have h := aMiddle_counts
    simp only [aReduced, ShorECDLP.tCount_append, h.1, h.2]
    omega


set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def b2Source : Circuit := blockB2 indexedStepProductionRegisters
private theorem b2_wellFormed : CircuitWellFormed b2Source := by
  unfold CircuitWellFormed
  decide +kernel
private theorem b2_counts : ShorECDLP.tCount b2Source = 462 ∧
    ShorECDLP.tCount (Cancellation.optimize b2Source) = 238 := by
  decide +kernel

def b2Patch (n start : Nat) : Patch (literalProgram b2Source : Straight n start start) 224 := by
  apply Patch.literal _ (Cancellation.optimize b2Source)
  · exact Cancellation.optimize_sublist b2Source
  · exact (Cancellation.optimize_run b2Source b2_wellFormed).symm
  · have h := b2_counts
    omega

def remainderPatch (n start width : Nat) (w : ActiveWindow) :
    Patch (remainderBlockProgram n start indexedStepProductionRegisters width w).2 224 := by
  unfold remainderBlockProgram remainderBlockSegments
  refine (Patch.sequenceCons (d := 0) (f := 224) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 224) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 224) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := 224) (f := 0) _ _ (b2Patch n _) (Patch.refl _)).castSaving (by omega)

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def b1Source : Circuit :=
  let r := indexedStepProductionRegisters
  rControlNonterminal [r.phase1] 0 r.control r.lengthRPrime r.terminal r.blockScratch
private theorem b1_wellFormed : CircuitWellFormed b1Source := by
  unfold CircuitWellFormed
  decide +kernel
private theorem b1_counts : ShorECDLP.tCount b1Source = 217 ∧
    ShorECDLP.tCount (Cancellation.optimize b1Source) = 119 := by decide +kernel

def b1Patch (n start : Nat) : Patch (literalProgram b1Source : Straight n start start) 98 := by
  apply Patch.literal _ (Cancellation.optimize b1Source)
  · exact Cancellation.optimize_sublist b1Source
  · exact (Cancellation.optimize_run b1Source b1_wellFormed).symm
  · have h := b1_counts; omega

/-- Literal concatenation supports mirrored segments without changing their context. -/
private theorem literal_append {n s : Nat} (xs ys : Circuit) :
    (literalProgram (xs ++ ys) : Straight n s s) =
      (literalProgram xs).append (literalProgram ys) := by
  induction xs with
  | nil => simp only [List.nil_append, literalProgram, List.map_nil, gateProgram, Straight.append]
  | cons g xs ih => simpa only [literalProgram, List.map_cons, gateProgram, Straight.append] using congrArg (Straight.gate (.literal g)) ih

def Patch.joinLiteral {n s d f} {xs ys : Circuit}
    (hp : Patch (literalProgram xs : Straight n s s) d)
    (hq : Patch (literalProgram ys : Straight n s s) f) :
    Patch (literalProgram (xs ++ ys) : Straight n s s) (d+f) := by
  rw [literal_append]
  exact hp.append hq

def optimizedLiteralPatch (n s d : Nat) (xs : Circuit)
    (hw : CircuitWellFormed xs)
    (ht : ShorECDLP.tCount (Cancellation.optimize xs) + d = ShorECDLP.tCount xs) :
    Patch (literalProgram xs : Straight n s s) d :=
  Patch.literal xs (Cancellation.optimize xs) (Cancellation.optimize_sublist xs)
    (Cancellation.optimize_run xs hw).symm ht

private theorem straight_append_assoc {n a b c d : Nat} (p : Straight n a b) (q : Straight n b c)
    (r : Straight n c d) : (p.append q).append r = p.append (q.append r) := by
  induction p with
  | done => rfl
  | gate g next ih => simp only [Straight.append, ih]
  | recordGate i v g next ih => simp only [Straight.append, ih]
  | measure w next ih => simp only [Straight.append, ih]

private theorem literal_append_cast {n s e f : Nat} (xs ys : Circuit) (R : Straight n s e) (h : e = f) :
    (literalProgram xs : Straight n s s).append (castFinish h ((literalProgram ys : Straight n s s).append R)) =
      castFinish h ((literalProgram (xs ++ ys) : Straight n s s).append R) := by
  subst h
  show (literalProgram xs : Straight n s s).append ((literalProgram ys : Straight n s s).append R) =
    (literalProgram (xs ++ ys) : Straight n s s).append R
  rw [literal_append, straight_append_assoc]

/-- Two adjacent literal segments are optimized as one literal. -/
def Patch.literalPair {n start d f} (xs ys : Circuit) (tail : List (FixedSegment n))
    (hp : Patch (literalProgram (xs ++ ys) : Straight n start start) d)
    (hq : Patch (sequenceProgram n tail start).2 f) :
    Patch (sequenceProgram n ((fun _ => ⟨0, literalProgram xs⟩) ::
      (fun _ => ⟨0, literalProgram ys⟩) :: tail) start).2 (d+f) := by
  rw [sequenceProgram, sequenceProgram]
  unfold Paper2607_13816.ChallengeMigration.appendCompiled
  dsimp only
  rw [literal_append_cast]
  exact ((hp.append hq).castFinish _).castFinish _

private theorem b12_wellFormed : CircuitWellFormed (b1Source ++ b2Source) := by
  unfold CircuitWellFormed
  decide +kernel
private theorem b12_saving : ShorECDLP.tCount (Cancellation.optimize (b1Source ++ b2Source)) + 434 =
    ShorECDLP.tCount (b1Source ++ b2Source) := by decide +kernel

def b12Patch (n start : Nat) : Patch (literalProgram (b1Source ++ b2Source) : Straight n start start) 434 :=
  Patch.literal _ (Cancellation.optimize (b1Source ++ b2Source)) (Cancellation.optimize_sublist _)
    (Cancellation.optimize_run _ b12_wellFormed).symm b12_saving

/-! Fixed endpoint arithmetic around each remainder interval.  The offset-dependent
constant updates stay verbatim; only the window-independent prefix and suffix are reduced. -/

def endpointPrefix (lT lQ lS sc : List Wire) (c : Wire) : Circuit :=
  cuccaroAdd lT lQ c ++ (addConstant lQ (endpointScratch lQ sc) c 4 ++
    constMinus lS (endpointScratch lS sc) c (256 + 2))

def endpointSuffix (lT lQ lS sc : List Wire) (c : Wire) : Circuit :=
  constMinus lS (endpointScratch lS sc) c (256 + 2) ++
    (subConstant lQ (endpointScratch lQ sc) c 4 ++ cuccaroSub lT lQ c)

/-- Exact cancellation facts for the fixed endpoint arithmetic and the four offset-adder cores. -/
def EndpointFacts (lT lQ lS sc : List Wire) (c : Wire) : Prop :=
  (CircuitWellFormed (endpointPrefix lT lQ lS sc c) ∧
    ShorECDLP.tCount (Cancellation.optimize (endpointPrefix lT lQ lS sc c)) + 42 =
      ShorECDLP.tCount (endpointPrefix lT lQ lS sc c)) ∧
  (CircuitWellFormed (endpointSuffix lT lQ lS sc c) ∧
    ShorECDLP.tCount (Cancellation.optimize (endpointSuffix lT lQ lS sc c)) + 42 =
      ShorECDLP.tCount (endpointSuffix lT lQ lS sc c)) ∧
  (CircuitWellFormed (cuccaroSub (endpointScratch lQ sc) lQ c) ∧
    ShorECDLP.tCount (Cancellation.optimize (cuccaroSub (endpointScratch lQ sc) lQ c)) + 14 =
      ShorECDLP.tCount (cuccaroSub (endpointScratch lQ sc) lQ c)) ∧
  (CircuitWellFormed (cuccaroSub (endpointScratch lS sc) lS c) ∧
    ShorECDLP.tCount (Cancellation.optimize (cuccaroSub (endpointScratch lS sc) lS c)) + 14 =
      ShorECDLP.tCount (cuccaroSub (endpointScratch lS sc) lS c)) ∧
  (CircuitWellFormed (cuccaroAdd (endpointScratch lS sc) lS c) ∧
    ShorECDLP.tCount (Cancellation.optimize (cuccaroAdd (endpointScratch lS sc) lS c)) + 14 =
      ShorECDLP.tCount (cuccaroAdd (endpointScratch lS sc) lS c)) ∧
  (CircuitWellFormed (cuccaroAdd (endpointScratch lQ sc) lQ c) ∧
    ShorECDLP.tCount (Cancellation.optimize (cuccaroAdd (endpointScratch lQ sc) lQ c)) + 14 =
      ShorECDLP.tCount (cuccaroAdd (endpointScratch lQ sc) lQ c))

private theorem endpoint_facts : ∀ c ∈ List.range' 568 10,
    EndpointFacts (List.range' 522 9) (List.range' 531 9) (List.range' 540 9) (List.range' 559 9) c := by
  unfold EndpointFacts CircuitWellFormed
  decide +kernel

def subConstantPatch (n s : Nat) (register constants : List Wire) (c : Wire) (k : Nat)
    (hw : CircuitWellFormed (cuccaroSub constants register c))
    (ht : ShorECDLP.tCount (Cancellation.optimize (cuccaroSub constants register c)) + 14 =
      ShorECDLP.tCount (cuccaroSub constants register c)) :
    Patch (literalProgram (subConstant register constants c k) : Straight n s s) 14 := by
  unfold subConstant
  exact (((Patch.refl _).joinLiteral (optimizedLiteralPatch n s 14 _ hw ht)).joinLiteral
    (Patch.refl _)).castSaving (by omega)

def addConstantPatch (n s : Nat) (register constants : List Wire) (c : Wire) (k : Nat)
    (hw : CircuitWellFormed (cuccaroAdd constants register c))
    (ht : ShorECDLP.tCount (Cancellation.optimize (cuccaroAdd constants register c)) + 14 =
      ShorECDLP.tCount (cuccaroAdd constants register c)) :
    Patch (literalProgram (addConstant register constants c k) : Straight n s s) 14 := by
  unfold addConstant
  exact (((Patch.refl _).joinLiteral (optimizedLiteralPatch n s 14 _ hw ht)).joinLiteral
    (Patch.refl _)).castSaving (by omega)

def prepareEndpointPatch (n s : Nat) (lT lQ lS sc : List Wire) (c : Wire) (k : Nat)
    (h : EndpointFacts lT lQ lS sc c) :
    Patch (literalProgram (prepareIntervalEndpoints lT lQ lS sc c 256 k) : Straight n s s) 70 := by
  have he : prepareIntervalEndpoints lT lQ lS sc c 256 k = endpointPrefix lT lQ lS sc c ++
      (subConstant lQ (endpointScratch lQ sc) c k ++ subConstant lS (endpointScratch lS sc) c k) := by
    simp only [prepareIntervalEndpoints, endpointPrefix, List.append_assoc]
  rw [he]
  exact ((optimizedLiteralPatch n s 42 _ h.1.1 h.1.2).joinLiteral
    ((subConstantPatch n s _ _ c k h.2.2.1.1 h.2.2.1.2).joinLiteral
      (subConstantPatch n s _ _ c k h.2.2.2.1.1 h.2.2.2.1.2))).castSaving (by omega)

def restoreEndpointPatch (n s : Nat) (lT lQ lS sc : List Wire) (c : Wire) (k : Nat)
    (h : EndpointFacts lT lQ lS sc c) :
    Patch (literalProgram (restoreIntervalEndpoints lT lQ lS sc c 256 k) : Straight n s s) 70 := by
  have he : restoreIntervalEndpoints lT lQ lS sc c 256 k =
      (addConstant lS (endpointScratch lS sc) c k ++ addConstant lQ (endpointScratch lQ sc) c k) ++
        endpointSuffix lT lQ lS sc c := by
    simp only [restoreIntervalEndpoints, endpointSuffix, List.append_assoc]
  rw [he]
  exact (((addConstantPatch n s _ _ c k h.2.2.2.2.1.1 h.2.2.2.2.1.2).joinLiteral
      (addConstantPatch n s _ _ c k h.2.2.2.2.2.1 h.2.2.2.2.2.2)).joinLiteral
    (optimizedLiteralPatch n s 42 _ h.2.1.1 h.2.1.2)).castSaving (by omega)

def Patch.prependLiteral {n start d f} (gs : Circuit)
    (p : (count : Nat) × Straight n start (start+count))
    (hg : Patch (literalProgram gs : Straight n start start) d) (hp : Patch p.2 f) :
    Patch (Paper2607_13816.ChallengeMigration.prependCompiled gs p).2 (d+f) := by
  unfold Paper2607_13816.ChallengeMigration.prependCompiled
  exact hg.append hp

def intervalEndpointPatch (n start : Nat) (r : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget)
    (h : EndpointFacts r.lengthT r.lengthQ r.lengthS r.endpointScratch (r.carry k K)) :
    Patch (intervalProgram n start r 256 k K mode signUpdate target).2 140 := by
  unfold intervalProgram
  refine (Patch.prependLiteral (d := 70) (f := 70) _ _
    (prepareEndpointPatch n _ _ _ _ _ _ k h) ?_).castSaving (by omega)
  refine (Patch.appendCompiled (d := 0) (f := 70) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.appendCompiled (d := 0) (f := 70) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine Patch.prependCompiled _ _ ?_
  refine (Patch.appendCompiled (d := 0) (f := 70) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.appendCompiled (d := 0) (f := 70) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact restoreEndpointPatch n _ _ _ _ _ _ k h

private theorem mainLabel_lt_laneCount
    {k K label : Nat} (hlabel : label ∈ (intervalMainLabels k K).toFinset) :
    label < intervalLaneCount k K := by
  have hmain : label ∈ intervalMainLabels k K := by simpa using hlabel
  by_cases hspecial : intervalHasTopSpecial k K = true
  · simp [intervalMainLabels, hspecial] at hmain
    omega
  · simpa [intervalMainLabels, hspecial] using hmain

private theorem remainderTreeDepth_le_nine
    (registers : IntervalRegisters) {k K : Nat}
    (hcount : intervalLaneCount k K ≤ 259) :
    intervalTreeDepth registers k K ≤ 9 := by
  have hwidth : DualUnaryActionTree.sourceWidth (intervalMainLabels k K).toFinset ≤ 9 := by
    apply DualUnaryActionTree.sourceWidth_le _ 9 (by decide)
    intro label hlabel
    have hlt := mainLabel_lt_laneCount hlabel
    norm_num
    omega
  exact (DualUnaryActionTree.buildSource_pathDepth_le
    registers.rightIndex registers.leftIndex
    (intervalMainLabels k K).toFinset (intervalTree registers k K) (by
      simpa [DualUnaryActionTree.buildSourceFromList] using
        intervalTree_built registers k K)).trans hwidth

private theorem endpoint_base_cases : ∀ b, 9 ≤ b → b ≤ 18 →
    ((List.range' 559 21).take (b+3)).getD b 0 ∈ List.range' 568 10 ∧
      ((List.range' 559 21).take (b+3)).take 9 = List.range' 559 9 := by
  intro b h1 h2
  interval_cases b <;> decide

private theorem remainder_endpoint_facts (w : ActiveWindow)
    (hw : intervalLaneCount w.start w.stop ≤ 259) :
    (indexedStepProductionRegisters.remainder w).carry w.start w.stop ∈ List.range' 568 10 ∧
      (indexedStepProductionRegisters.remainder w).endpointScratch = List.range' 559 9 := by
  have hd := remainderTreeDepth_le_nine (indexedStepProductionRegisters.remainder w) hw
  have hb1 : 9 ≤ intervalScratchBase (indexedStepProductionRegisters.remainder w) w.start w.stop := by
    change 9 ≤ max (2 * intervalTreeDepth (indexedStepProductionRegisters.remainder w) w.start w.stop) (max 9 9)
    omega
  have hb2 : intervalScratchBase (indexedStepProductionRegisters.remainder w) w.start w.stop ≤ 18 := by
    change max (2 * intervalTreeDepth (indexedStepProductionRegisters.remainder w) w.start w.stop) (max 9 9) ≤ 18
    omega
  have hcarry : (indexedStepProductionRegisters.remainder w).carry w.start w.stop =
      ((List.range' 559 21).take (intervalScratchBase (indexedStepProductionRegisters.remainder w)
        w.start w.stop + 3)).getD (intervalScratchBase (indexedStepProductionRegisters.remainder w)
          w.start w.stop) 0 := rfl
  have hscratch : (indexedStepProductionRegisters.remainder w).endpointScratch =
      ((List.range' 559 21).take (intervalScratchBase (indexedStepProductionRegisters.remainder w)
        w.start w.stop + 3)).take 9 := rfl
  rw [hcarry, hscratch]
  exact endpoint_base_cases _ hb1 hb2

def remainderIntervalPatch (n start : Nat) (w : ActiveWindow)
    (hw : intervalLaneCount w.start w.stop ≤ 259)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget) :
    Patch (intervalProgram n start (indexedStepProductionRegisters.remainder w) 256 w.start w.stop
      mode signUpdate target).2 140 := by
  have hf := remainder_endpoint_facts w hw
  have hs := endpoint_facts _ hf.1
  have hT : (indexedStepProductionRegisters.remainder w).lengthT = List.range' 522 9 := rfl
  have hQ : (indexedStepProductionRegisters.remainder w).lengthQ = List.range' 531 9 := rfl
  have hS : (indexedStepProductionRegisters.remainder w).lengthS = List.range' 540 9 := rfl
  rw [← hT, ← hQ, ← hS, ← hf.2] at hs
  exact intervalEndpointPatch n start _ _ _ mode signUpdate target hs

theorem certified_remainder_count (T : Nat) :
    intervalLaneCount (certifiedActiveWindows 256 T).remainder.start
      (certifiedActiveWindows 256 T).remainder.stop ≤ 259 := by
  simp only [certifiedActiveWindows, certifiedRemainderWindow, intervalLaneCount]
  omega

def remainderPatchAll (n start : Nat) (w : ActiveWindow) (hw : intervalLaneCount w.start w.stop ≤ 259) :
    Patch (remainderBlockProgram n start indexedStepProductionRegisters 256 w).2 812 := by
  unfold remainderBlockProgram remainderBlockSegments
  refine (Patch.sequenceCons (d := 98) (f := 714) _ _ (b1Patch n _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 140) (f := 574) _ _ (remainderIntervalPatch n _ w hw _ _ _) ?_).castSaving (by omega)
  refine (Patch.literalPair (d := 434) (f := 140) b1Source b2Source _ (b12Patch n _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 140) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := 140) (f := 0) _ _ (remainderIntervalPatch n _ w hw _ _ _) (Patch.refl _)).castSaving (by omega)

def ePrepSource : Circuit :=
  let r := indexedStepProductionRegisters
  ((computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++
    computeControl [r.phase1,r.terminal] 1 r.control r.blockScratch) ++
    computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch) ++ prepareLatestPaperTBoundary r.tBoundary 256

def eCleanSource : Circuit :=
  let r := indexedStepProductionRegisters
  computeControl [r.phase1] 1 r.control r.blockScratch ++ restoreLatestPaperTBoundary r.tBoundary 256

private theorem ePrep_wellFormed : CircuitWellFormed ePrepSource := by
  unfold CircuitWellFormed
  decide +kernel
private theorem eClean_wellFormed : CircuitWellFormed eCleanSource := by
  unfold CircuitWellFormed
  decide +kernel
private theorem ePrep_counts : ShorECDLP.tCount ePrepSource = 560 ∧
    ShorECDLP.tCount (Cancellation.optimize ePrepSource) = 518 := by decide +kernel
private theorem eClean_counts : ShorECDLP.tCount eCleanSource = 539 ∧
    ShorECDLP.tCount (Cancellation.optimize eCleanSource) = 497 := by decide +kernel

def ePrepPatch (n start : Nat) : Patch (literalProgram ePrepSource : Straight n start start) 42 := by
  apply Patch.literal _ (Cancellation.optimize ePrepSource)
  · exact Cancellation.optimize_sublist ePrepSource
  · exact (Cancellation.optimize_run ePrepSource ePrep_wellFormed).symm
  · have h := ePrep_counts; omega

def eCleanPatch (n start : Nat) : Patch (literalProgram eCleanSource : Straight n start start) 42 := by
  apply Patch.literal _ (Cancellation.optimize eCleanSource)
  · exact Cancellation.optimize_sublist eCleanSource
  · exact (Cancellation.optimize_run eCleanSource eClean_wellFormed).symm
  · have h := eClean_counts; omega

def coefficientPatch (n start : Nat) (w : ActiveWindow) :
    Patch (coefficientBlockProgram n start indexedStepProductionRegisters 256 w).2 84 := by
  unfold coefficientBlockProgram coefficientBlockSegments
  refine (Patch.sequenceCons (d := 42) (f := 42) _ _ (ePrepPatch n _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 42) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 42) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 42) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := 42) (f := 0) _ _ (eCleanPatch n _) (Patch.refl _)).castSaving (by omega)

def candidateStepPatch (n start T : Nat) :
    Patch (measuredStepProgram n start indexedStepProductionRegisters 256 T).2 1106 := by
  unfold measuredStepProgram measuredStepSegments
  refine (Patch.sequenceCons (d := 98) (f := 1008) _ _ (aPatch n _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 812) (f := 196) _ _ (remainderPatchAll n _ _ (certified_remainder_count T)) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 112) (f := 84) _ _ (epochPatch n _ _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := 84) (f := 0) _ _ (coefficientPatch n _ _) (Patch.refl _)).castSaving (by omega)

/-- Optimize the fixed A, remainder-control, epoch and coefficient-boundary literals. -/
def stepPatch (n start T : Nat) :
    Patch (measuredStepProgram n start indexedStepProductionRegisters 256 T).2 1106 :=
  candidateStepPatch n start T

/-- Exact per-step savings accumulate through the fixed 1,620-step schedule. -/

def schedulePatch (n : Nat) : (count first start : Nat) →
    Patch (measuredScheduleProgram n indexedStepProductionRegisters 256 count first start).2 (count*1106)
  | 0, _, _ => Patch.refl _
  | count+1, first, start => by
    simp only [measuredScheduleProgram]
    exact (Patch.appendCompiled _ _ (stepPatch n start first)
      (schedulePatch n count (first+1) _)).castSaving (by omega)


def eeaForwardPatch (n start : Nat) :
    Patch (measuredEEAForwardProgram n start indexedStepProductionRegisters).2 1791720 := by
  unfold measuredEEAForwardProgram
  exact schedulePatch n 1620 1 start


def wrapperPatch (n start : Nat) :
    Patch (measuredForwardWrapperProgram n start).2 1791720 := by
  unfold measuredForwardWrapperProgram measuredForwardWrapperSegments
  refine (Patch.sequenceCons (d := 0) (f := 1791720) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := 1791720) (f := 0) _ _ (eeaForwardPatch n _) (Patch.refl _)).castSaving (by omega)


def reverseCleanSource : Circuit :=
  let r := indexedStepProductionRegisters
  prepareLatestPaperTBoundary r.tBoundary 256 ++ computeControl [r.phase1] 1 r.control r.blockScratch

def reversePrepSource : Circuit :=
  let r := indexedStepProductionRegisters
  computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++
    computeControl [r.phase1,r.terminal] 1 r.control r.blockScratch ++
    computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++ restoreLatestPaperTBoundary r.tBoundary 256

def reverseCleanPatch (n s : Nat) : Patch (literalProgram reverseCleanSource : Straight n s s) 42 :=
  optimizedLiteralPatch n s 42 reverseCleanSource (by unfold CircuitWellFormed; decide +kernel) (by decide +kernel)

def reversePrepPatch (n s : Nat) : Patch (literalProgram reversePrepSource : Straight n s s) 42 :=
  optimizedLiteralPatch n s 42 reversePrepSource (by unfold CircuitWellFormed; decide +kernel) (by decide +kernel)

def reverseEpochPatch (n s : Nat) :
    Patch (literalProgram (blockCInverse indexedStepProductionRegisters) : Straight n s s) 112 :=
  optimizedLiteralPatch n s 112 _ (by unfold CircuitWellFormed; decide +kernel) (by decide +kernel)

/-- The reverse A literal is split around the terminal-padding epoch test.
Source arithmetic: VerifiedQC/ShorECDLP PR #551, Apache-2.0. -/
def aTerminalSource : Circuit :=
  let r := indexedStepProductionRegisters
  computeControl (r.phase1 :: r.lengthRPrime) (2 ^ (r.lengthRPrime.length + 1) - 2) r.terminal r.blockScratch

def aInverseBefore : Circuit :=
  let r := indexedStepProductionRegisters
  aTerminalSource ++ terminalEpochRestore r.terminal r.shiftEpoch r.quotientLow ++
    [.CX r.terminal r.phase1] ++ (preShiftUnitary r.preShift).adjoint ++ [.CX r.terminal r.phase1]

def aInverseEpoch : Circuit := terminalPaddingEpochUpdate indexedStepProductionRegisters.terminalPadding

def aInverseAfter : Circuit :=
  let r := indexedStepProductionRegisters.terminalPadding
  controlledDecrement r.terminal r.lengthS r.carries ++ controlledRotateRightOne r.terminal r.work2 ++ aTerminalSource

private theorem aInverseEpoch_wellFormed : CircuitWellFormed aInverseEpoch := by
  unfold CircuitWellFormed
  decide +kernel
private theorem aInverseEpoch_saving :
    ShorECDLP.tCount (Cancellation.optimize aInverseEpoch) + 98 = ShorECDLP.tCount aInverseEpoch := by
  decide +kernel

def aInversePatch (n s : Nat) :
    Patch (literalProgram (blockAInverse indexedStepProductionRegisters) : Straight n s s) 98 := by
  have hp := (((Patch.refl (literalProgram aInverseBefore : Straight n s s)).joinLiteral
    (optimizedLiteralPatch n s 98 aInverseEpoch aInverseEpoch_wellFormed aInverseEpoch_saving)).joinLiteral
    (Patch.refl (literalProgram aInverseAfter : Straight n s s))).castSaving (show 0+98+0=98 by omega)
  simpa only [aInverseBefore, aInverseAfter, aInverseEpoch, aTerminalSource,
    blockAInverse, terminalPaddingInverse, List.append_assoc] using hp

def b3Source : Circuit :=
  let r := indexedStepProductionRegisters
  ([.CCX r.phase2 r.sign r.terminal] ++ rControlNonterminal [r.phase1,r.terminal] 0 r.control r.lengthRPrime (r.blockScratch.getD 0 0) (r.blockScratch.drop 1)) ++ [.CCX r.phase2 r.sign r.terminal]

def reverseFrontPatch (n s : Nat) :
    Patch (literalProgram ((blockFForward indexedStepProductionRegisters).adjoint ++
      prepareLatestPaperTBoundary indexedStepProductionRegisters.tBoundary 256 ++
      computeControl [indexedStepProductionRegisters.phase1] 1 indexedStepProductionRegisters.control indexedStepProductionRegisters.blockScratch) : Straight n s s) 42 := by
  have hp := ((Patch.refl (literalProgram (blockFForward indexedStepProductionRegisters).adjoint : Straight n s s)).joinLiteral
    (reverseCleanPatch n s)).castSaving (show 0+42=42 by omega)
  simpa only [reverseCleanSource, List.append_assoc] using hp

def reverseCombinedPatch (n s : Nat) (w : ActiveWindow) :
    Patch (literalProgram (let r := indexedStepProductionRegisters;
      computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++
      computeControl [r.phase1,r.terminal] 1 r.control r.blockScratch ++
      computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++ restoreLatestPaperTBoundary r.tBoundary 256 ++
      blockDInverse r w ++ blockCInverse r ++
      (([.CCX r.phase2 r.sign r.terminal] ++ rControlNonterminal [r.phase1,r.terminal] 0 r.control r.lengthRPrime (r.blockScratch.getD 0 0) (r.blockScratch.drop 1)) ++ [.CCX r.phase2 r.sign r.terminal])) : Straight n s s) 154 := by
  have hp := ((((reversePrepPatch n s).joinLiteral
    (Patch.refl (literalProgram (blockDInverse indexedStepProductionRegisters w) : Straight n s s))).joinLiteral
    (reverseEpochPatch n s)).joinLiteral (Patch.refl (literalProgram b3Source : Straight n s s))).castSaving
    (show 42+0+112+0=154 by omega)
  simpa only [reversePrepSource, b3Source, List.append_assoc] using hp

def reverseRemainderPatch (n s : Nat) :
    Patch (literalProgram (b3Source ++ b2Source ++ b1Source) : Straight n s s) 434 :=
  optimizedLiteralPatch n s 434 _ (by unfold CircuitWellFormed; decide +kernel) (by decide +kernel)

def reverseStepPatch (n start T : Nat) :
    Patch (measuredInverseStepProgram n start indexedStepProductionRegisters T).2 1106 := by
  unfold measuredInverseStepProgram measuredInverseStepSegments
  refine (Patch.sequenceCons (d := 0) (f := 1106) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 1106) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 42) (f := 1064) _ _ ?_ ?_).castSaving (by omega)
  · exact reverseFrontPatch n _
  refine (Patch.sequenceCons (d := 0) (f := 1064) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 1064) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 1064) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 154) (f := 910) _ _ ?_ ?_).castSaving (by omega)
  · exact reverseCombinedPatch n _ (certifiedActiveWindows 256 T).quotientSwap
  refine (Patch.sequenceCons (d := 140) (f := 770) _ _ ?_ ?_).castSaving (by omega)
  · unfold intervalInverseProgram
    exact remainderIntervalPatch n _ _ (certified_remainder_count T) _ _ _
  refine (Patch.sequenceCons (d := 434) (f := 336) _ _ ?_ ?_).castSaving (by omega)
  · exact reverseRemainderPatch n _
  refine (Patch.sequenceCons (d := 140) (f := 196) _ _ ?_ ?_).castSaving (by omega)
  · unfold intervalInverseProgram
    exact remainderIntervalPatch n _ _ (certified_remainder_count T) _ _ _
  exact (Patch.sequenceCons (d := 196) (f := 0) _ _
    (((b1Patch n _).joinLiteral (aInversePatch n _)).castSaving (by omega)) (Patch.refl _)).castSaving (by omega)

def reverseSchedulePatch (n : Nat) : (count first start : Nat) →
    Patch (measuredInverseScheduleProgram n indexedStepProductionRegisters count first start).2 (count*1106)
  | 0, _, _ => Patch.refl _
  | count+1, first, start => by
    simp only [measuredInverseScheduleProgram]
    exact (Patch.appendCompiled _ _ (reverseSchedulePatch n count (first+1) start)
      (reverseStepPatch n _ first)).castSaving (by omega)

def eeaReversePatch (n start : Nat) :
    Patch (measuredEEAReverseProgram n start indexedStepProductionRegisters).2 1791720 := by
  unfold measuredEEAReverseProgram
  exact reverseSchedulePatch n 1620 1 start

def reverseWrapperPatch (n start : Nat) :
    Patch (measuredReverseWrapperProgram n start).2 1791720 := by
  unfold measuredReverseWrapperProgram measuredReverseWrapperSegments
  refine (Patch.sequenceCons (d := 0) (f := 1791720) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 1791720) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 1791720) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := 1791720) (f := 0) _ _ (eeaReversePatch n _) (Patch.refl _)).castSaving (by omega)

def Patch.relabelCompiled {n start d} (e : Wire ≃ Wire)
    (p : (count : Nat) × Straight n start (start+count)) (hp : Patch p.2 d) :
    Patch (Paper2607_13816.ChallengeMigration.relabelCompiled e p).2 d :=
  hp.relabel e

def forwardDataPatch (n start : Nat) : Patch (measuredForwardDataBankProgram n start).2 1791720 := by
  unfold measuredForwardDataBankProgram
  exact Patch.relabelCompiled eeaWorkspaceExchange _ (wrapperPatch n start)

def reverseDataPatch (n start : Nat) : Patch (measuredReverseDataBankProgram n start).2 1791720 := by
  unfold measuredReverseDataBankProgram
  exact Patch.relabelCompiled eeaWorkspaceExchange _ (reverseWrapperPatch n start)

def collectPatch {n d}
    (next : (cursor : Nat) → List (Fin cursor) → (count : Nat) × Straight n cursor (cursor+count))
    (hp : ∀ cursor prior, Patch (next cursor prior).2 d) :
    (ws : List Wire) → (start : Nat) → (prior : List (Fin start)) →
      Patch (collectProgram n next ws start prior).2 d
  | [], start, prior => by simpa only [collectProgram] using hp start prior
  | w::ws, start, prior => by
    simp only [collectProgram]
    exact (Patch.measure w (collectPatch next hp ws (start+1) _)).castFinish _

def divisionAfterResetPatch (n start : Nat) (prior : List (Fin start)) :
    Patch (divisionAfterResetProgram n start prior).2 1791720 := by
  unfold divisionAfterResetProgram appendRetaining
  exact (Patch.appendCompiled (d := 1791720) (f := 0) _ _
    ((Patch.appendCompiled (d := 1791720) (f := 0) _ _ (reverseDataPatch n start) (Patch.refl _)).castSaving (by omega))
    (Patch.refl _)).castSaving (by omega)

def divisionPatch (n start : Nat) : Patch (divisionProgram n start).2 3583440 := by
  unfold divisionProgram
  exact (Patch.appendCompiled (d := 1791720) (f := 1791720) _ _
    ((Patch.appendCompiled (d := 1791720) (f := 0) _ _ (wrapperPatch n start) (Patch.refl _)).castSaving (by omega))
    (collectPatch _ (divisionAfterResetPatch n) _ _ _)).castSaving (by omega)

def multiplicationCleanupPatch (n start : Nat) :
    Patch (multiplicationCleanupProgram n start).2 1791720 := by
  unfold multiplicationCleanupProgram appendLiteral
  exact (Patch.appendCompiled (d := 0) (f := 1791720) _ _ (Patch.refl _)
    ((Patch.appendCompiled (d := 1791720) (f := 0) _ _ (reverseDataPatch n _) (Patch.refl _)).castSaving (by omega))).castSaving (by omega)

def multiplicationCorrectionPatch (n start : Nat) (prior : List (Fin start)) :
    Patch (multiplicationCorrectionProgram n start prior).2 1791720 := by
  unfold multiplicationCorrectionProgram
  exact (Patch.appendCompiled (d := 0) (f := 1791720)
    (correctionCompiled n start (List.range' 580 256) prior) (multiplicationCleanupProgram n start)
    (Patch.refl _) (multiplicationCleanupPatch n start)).castSaving (show 0+1791720=1791720 by omega)

def multiplicationAfterResetPatch (n start : Nat) (prior : List (Fin start)) :
    Patch (multiplicationAfterResetProgram n start prior).2 3583440 := by
  unfold multiplicationAfterResetProgram appendRetaining
  exact (Patch.appendCompiled (d := 1791720) (f := 1791720) _ _
    ((Patch.appendCompiled (d := 1791720) (f := 0) _ _ (forwardDataPatch n _) (Patch.refl _)).castSaving (by omega))
    (multiplicationCorrectionPatch n _ _)).castSaving (by omega)

def multiplicationPatch (n start : Nat) : Patch (multiplicationProgram n start).2 3583440 := by
  unfold multiplicationProgram
  exact (Patch.appendCompiled (d := 0) (f := 3583440) _ _ (Patch.refl _)
    (collectPatch _ (multiplicationAfterResetPatch n) _ _ _)).castSaving (by omega)



end
end ShorECDLP.Entrant.Optimization
namespace ShorECDLP.Entrant.Optimization
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] sequenceProgram appendCompiled literalProgram ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateProgram ShorECDLP.Entrant.BorrowFlag.divisionProgram ShorECDLP.Entrant.BorrowFlag.multiplicationProgram
  Single.axis Rounded.entry

def borrowedFieldPatch {saving : Nat} (n start : Nat) (arithmetic : FixedSegment n)
    (hp : ∀ cursor, Patch (arithmetic cursor).2 saving) :
    Patch (ShorECDLP.Entrant.BorrowFlag.fieldProgram n start arithmetic).2 saving := by
  unfold ShorECDLP.Entrant.BorrowFlag.fieldProgram
  apply Patch.surroundCompiled
  unfold ShorECDLP.Entrant.BorrowFlag.coreSegments
  refine (Patch.sequenceCons (d := 0) (f := saving) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := saving) (f := 0) _ _ (hp _) (Patch.refl _)).castSaving (by omega)

def zeroDivisionPatch (n start : Nat) :
    Patch (ShorECDLP.Entrant.BorrowFlag.divisionProgram n start).2 3583440 := by
  unfold ShorECDLP.Entrant.BorrowFlag.divisionProgram
  exact borrowedFieldPatch n start (divisionProgram n) (divisionPatch n)

def zeroMultiplicationPatch (n start : Nat) :
    Patch (ShorECDLP.Entrant.BorrowFlag.multiplicationProgram n start).2 3583440 := by
  unfold ShorECDLP.Entrant.BorrowFlag.multiplicationProgram
  exact borrowedFieldPatch n start (multiplicationProgram n) (multiplicationPatch n)

def coordinatePatch (start : Nat) : Patch (ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateProgram start).2 7166880 := by
  unfold ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateProgram ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateSegments
  refine (Patch.sequenceCons (d := 0) (f := 7166880) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 7166880) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 3583440) (f := 3583440) _ _ (zeroDivisionPatch 32768 _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 3583440) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 3583440) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := 3583440) (f := 0) _ _ (zeroMultiplicationPatch 32768 _) (Patch.refl _)).castSaving (by omega)

-- Append within Optimization after borrowed division/multiplication patches.
attribute [local irreducible] NarrowQrom.coordinateProgram NarrowQrom.coreProgram NarrowQrom.preparedProgram

def narrowCoordinatePatch {d : Nat}
    (hd : ∀start,Patch (BorrowFlag.divisionProgram 32768 start).2 d)
    (hm : ∀start,Patch (BorrowFlag.multiplicationProgram 32768 start).2 d)
    (start : Nat) : Patch (NarrowQrom.coordinateProgram start).2 (d+d) := by
  unfold NarrowQrom.coordinateProgram NarrowQrom.coordinateSegments
  refine (Patch.sequenceCons (d:=0) (f:=d+d) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d:=0) (f:=d+d) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d:=d) (f:=d) _ _ (hd _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d:=0) (f:=d) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d:=0) (f:=d) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d:=d) (f:=0) _ _ (hm _) (Patch.refl _)).castSaving (by omega)

def narrowCorePatch {d : Nat}
    (hc : ∀start,Patch (NarrowQrom.coordinateProgram start).2 d) (start : Nat) :
    Patch (NarrowQrom.coreProgram start).2 d := by
  unfold NarrowQrom.coreProgram NarrowQrom.coreSegments
  exact (Patch.sequenceCons (d:=d) (f:=0) _ _ (hc _) (Patch.refl _)).castSaving (by omega)

def narrowPreparedPatch {d : Nat}
    (hc : ∀start,Patch (NarrowQrom.coordinateProgram start).2 d) (start : Nat) :
    Patch (NarrowQrom.preparedProgram start).2 d := by
  unfold NarrowQrom.preparedProgram
  exact Patch.surroundCompiled _ _ _ (narrowCorePatch hc start)

def narrowActualPatch {d : Nat}
    (hc : ∀start,Patch (NarrowQrom.coordinateProgram start).2 d) (start : Nat) :
    Patch (NarrowQrom.actual.program start) d := by
  unfold NarrowQrom.actual closedWindow
  exact (((narrowPreparedPatch hc 0).relabel (windowAddressPerm 855 (by decide))).castFinish _).shift start

def corePatch (start : Nat) : Patch (Single.Physical.core start).2 7166880 := by
  unfold Single.Physical.core Single.Physical.segments
  exact (Patch.sequenceCons (d := 7166880) (f := 0) _ _ (coordinatePatch start) (Patch.refl _)).castSaving (by omega)

def preparedPatch (start : Nat) : Patch (Single.Physical.prepared start).2 7166880 := by
  unfold Single.Physical.prepared
  exact Patch.surroundCompiled _ _ _ (corePatch start)

def actualPatch (start : Nat) : Patch (Single.Physical.actual.program start) 7166880 := by
  unfold Single.Physical.actual closedWindow
  exact (((preparedPatch 0).relabel (windowAddressPerm 855 (by decide))).castFinish _).shift start

def signedPatch (w : Single.SignedWindow) (start : Nat) :
    Patch ((Single.signedWindow w).program start) 7166880 := by
  unfold Single.signedWindow
  cases w <;> simp only [Single.SignedWindow.width]
  all_goals first
    | exact (narrowActualPatch (narrowCoordinatePatch (zeroDivisionPatch 32768) (zeroMultiplicationPatch 32768)) start).reindex (Single.signedRow _)
    | exact (actualPatch start).reindex (Single.signedRow _)

def preparePatch {n s e d} (ws : List Wire) {p : Straight n s e} (hp : Patch p d) :
    Patch (prepareOuterBank ws p) d := by
  induction ws with
  | nil => exact hp
  | cons w ws ih => exact Patch.gate (.literal (.H w)) ih

structure PatchedWindow (n : Nat) where
  source : Single.Window n
  saving : Nat
  patch : ∀ start, Patch (source.program start) saving

def leftPatches : List (PatchedWindow 851968) :=
  ⟨Single.firstWindow,0,fun _ => Patch.refl _⟩ ::
    Single.leftSigned.map (fun w => ⟨Single.signedWindow w,7166880,signedPatch w⟩)
def rightPatches : List (PatchedWindow 851968) :=
  Single.rightSigned.map (fun w => ⟨Single.signedWindow w,7166880,signedPatch w⟩)
private theorem leftPatches_source : leftPatches.map PatchedWindow.source = Single.leftWindows := by
  simp [leftPatches, Single.leftWindows]
private theorem rightPatches_source : rightPatches.map PatchedWindow.source = Single.rightWindows := by
  simp [rightPatches, Single.rightWindows]
private theorem leftPatches_saving : (leftPatches.map PatchedWindow.saving).sum = 114670080 := by
  simp [leftPatches, Single.leftSigned]
private theorem rightPatches_saving : (rightPatches.map PatchedWindow.saving).sum = 93169440 := by
  simp [rightPatches, Single.rightSigned]

def axisPatch {n} : (ps : List (PatchedWindow n)) → (start : Nat) → (prior : List (Fin start)) →
    Patch (Single.axis (ps.map PatchedWindow.source) start prior) ((ps.map PatchedWindow.saving).sum)
  | [], _, _ => Patch.refl _
  | p::ps, start, prior => by
    simp only [List.map_cons, List.sum_cons, Single.axis]
    refine Patch.castFinish ?_ _
    refine Patch.castSaving (Patch.append (f := (ps.map PatchedWindow.saving).sum) (preparePatch _ (p.patch start)) ?_) (by omega)
    exact (Patch.append (Patch.refl _) (axisPatch ps _ (Single.nextPrior p.source.count p.source.wires.length prior))).castSaving (by omega)

def axisPatchFor {n} (ps : List (PatchedWindow n)) (ws : List (Single.Window n))
    (he : ps.map PatchedWindow.source = ws) (start : Nat) (prior : List (Fin start)) :
    Patch (Single.axis ws start prior) ((ps.map PatchedWindow.saving).sum) := by
  subst ws
  exact axisPatch ps start prior

def Patch.framed {n s m k e f dl dr} (p : Straight n s m) (q : Straight n m k)
    (r : Straight n k e) (h : e=f) (hp : Patch p dl) (hq : Patch q dr) :
    Patch (Single.framed p q r h) (dl+dr) := by
  unfold Single.framed
  exact Patch.gate _ ((Patch.append hp ((Patch.append hq (Patch.gate _ (Patch.refl _))).castSaving (Nat.add_zero dr))).castFinish h)

def trialPatch (start : Nat) : Patch (Single.trial start) 207839520 := by
  have hl := (axisPatchFor leftPatches Single.leftWindows leftPatches_source start List.nil).castSaving leftPatches_saving
  have hr := (axisPatchFor rightPatches Single.rightWindows rightPatches_source
    (start+Single.axisCount Single.leftWindows) List.nil).castSaving rightPatches_saving
  unfold Single.trial
  exact (Patch.framed _ _ _ _ hl hr).castSaving (by decide)

def programPatch : Patch Single.program 207839520 := by
  unfold Single.program
  exact (trialPatch 0).castFinish _

def Patch.fixedEntry {n e d} (f : Fin n → PointCoeff) (p : Straight n 0 e) (hp : Patch p d) :
    Patch (Single.fixedEntry f p).program d := by
  unfold Single.fixedEntry
  exact hp.reindex _

def entryPatch : Patch Rounded.entry.program 207839520 := by
  unfold Rounded.entry Rounded.program
  exact Patch.fixedEntry Single.mixedCoefficientAt _
    ((Patch.append programPatch (Patch.refl Rounded.readout)).castSaving (by omega))
end
end ShorECDLP.Entrant.Optimization

namespace ShorECDLP.Entrant.Parent
open Challenge
noncomputable def entry : StraightEntry := Optimization.replaceEntry Rounded.entry Optimization.entryPatch.program
def layout : DecodeLayout := Rounded.layout
def bounds : Bounds := ⟨Rounded.bounds.qubits, Rounded.bounds.tModel - 207839520, Rounded.bounds.measurements⟩
theorem certificate : Certificate officialLimits layout entry bounds :=
  Optimization.replacement_certificate Rounded.certificate Optimization.entryPatch.drops Optimization.entryPatch.rewrites
end ShorECDLP.Entrant.Parent
end

section
namespace ShorECDLP.Entrant.AndGadget
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
@[simp] theorem residue_doublesProgram (n k start : Nat) (acc dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) :
    residue (ShorECDLP.Entrant.SquareInPlace.doublesProgram n k start acc dirty bits p c r t f).2 = 0 := by
  induction k generalizing start with
  | zero => simp only [ShorECDLP.Entrant.SquareInPlace.doublesProgram, residue_done]
  | succ k ih => simp [ShorECDLP.Entrant.SquareInPlace.doublesProgram, residue_compiled, ih]

@[simp] theorem residue_padsProgram (n k start : Nat) (w : Wire) :
    residue (ShorECDLP.Entrant.SquareInPlace.padsProgram n k start w).2 = 0 := by
  induction k generalizing start with
  | zero => simp only [ShorECDLP.Entrant.SquareInPlace.padsProgram, residue_done]
  | succ k ih => simp [ShorECDLP.Entrant.SquareInPlace.padsProgram, residue_compiled, residue, ih]

@[simp] theorem residue_paddedSquare (n start : Nat) :
    residue (ShorECDLP.Entrant.SquareInPlace.paddedSquareProgram n start).2 = 0 := by
  unfold ShorECDLP.Entrant.SquareInPlace.paddedSquareProgram ShorECDLP.Entrant.SquareInPlace.inPlaceSquareProgram
  simp only [residue_compiled, FullCredit.residue_squareInverse, residue_doublesProgram, residue_padsProgram]

attribute [local irreducible] ShorECDLP.Entrant.SquareInPlace.paddedSquareProgram in
theorem paddedSquareCount (n start : Nat) :
    AtLeast (ShorECDLP.Entrant.SquareInPlace.paddedSquareProgram n start).2 1500938 := by
  have hr := residue_t (ShorECDLP.Entrant.SquareInPlace.paddedSquareProgram n start).2 (fun _ => false) (fun _ => false)
  have ht := ShorECDLP.Entrant.SquareInPlace.paddedSquareProgram_tCount n start (fun _ => false) (fun _ => false)
  rw [ShorECDLP.Entrant.SquareInPlace.paddedSquare_counts.1] at ht
  have hz := residue_paddedSquare n start
  unfold AtLeast compiledTCount at *
  omega

end
end ShorECDLP.Entrant.AndGadget

namespace ShorECDLP.Entrant.FullCredit
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration ShorECDLP.Entrant.AndGadget
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

@[simp] theorem residue_borrowPrepare (n start : Nat) :
    residue (BorrowFlag.prepareProgram n start).2 = 0 := by
  simp [BorrowFlag.prepareProgram,residue_compiled,residue_equality,residue_literal,
    ZeroAdaptive.cx,primitivePhaseCost]
@[simp] theorem residue_borrowRestore (n start : Nat) :
    residue (BorrowFlag.restoreProgram n start).2 = 0 := by
  simp [BorrowFlag.restoreProgram,residue_prepend,residue_equality,
    ZeroAdaptive.cx,primitivePhaseCost]

theorem residue_borrowField (n start : Nat) (arithmetic : FixedSegment n)
    (ha : ∀ s, residue (arithmetic s).2 = 0) :
    residue (BorrowFlag.fieldProgram n start arithmetic).2 = 0 := by
  have hs : residue (sequenceProgram n (BorrowFlag.coreSegments n arithmetic) start).2 = 0 := by
    apply residue_sequence
    intro seg hseg cursor
    simp only [BorrowFlag.coreSegments,List.mem_cons,List.not_mem_nil,or_false] at hseg
    rcases hseg with rfl | rfl | rfl
    · simpa only [relabelCompiled,residue_relabel] using residue_borrowPrepare n cursor
    · exact ha cursor
    · simpa only [relabelCompiled,residue_relabel] using residue_borrowRestore n cursor
  unfold BorrowFlag.fieldProgram
  rw [residue_surround,hs]
  simp [BorrowFlag.flip,primitivePhaseCost]

theorem residue_borrowDivision (n start : Nat) : residue (BorrowFlag.divisionProgram n start).2 = 0 := by
  unfold BorrowFlag.divisionProgram
  exact residue_borrowField n start _ (residue_division n)
theorem residue_borrowMultiplication (n start : Nat) : residue (BorrowFlag.multiplicationProgram n start).2 = 0 := by
  unfold BorrowFlag.multiplicationProgram
  exact residue_borrowField n start _ (residue_multiplication n)

theorem residue_borrowCoordinate (start : Nat) : residue (BorrowFlag.adaptiveCoordinateProgram start).2 = 0 := by
  unfold BorrowFlag.adaptiveCoordinateProgram
  apply residue_sequence
  intro seg hseg s
  simp only [BorrowFlag.adaptiveCoordinateSegments,List.mem_cons,List.not_mem_nil,or_false] at hseg
  rcases hseg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact residue_fieldLookupAdd _ _ s
  · exact residue_signedField _ s
  · exact residue_borrowDivision _ s
  · exact AndGadget.residue_paddedSquare _ s
  · exact residue_fieldLookupAdd _ _ s
  · exact residue_borrowMultiplication _ s
  · exact residue_xNegate _ s
  · exact residue_fieldLookupAdd _ _ s
  · exact residue_signedField _ s
end
end ShorECDLP.Entrant.FullCredit
end

section
namespace ShorECDLP.Entrant.FullCredit
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration ShorECDLP.Entrant.AndGadget
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

theorem opsResidue_measuredTail {n : Nat} (a : Wire) (cs : List Wire) (t : Wire) (ws : List Wire) :
    ((@measuredTailOps n a cs t ws).map lookupOpResidue).sum = 0 := by
  induction cs generalizing a ws with
  | nil => simp [measuredTailOps]
  | cons c cs ih =>
    cases cs with
    | nil => simp [measuredTailOps,primitivePhaseCost]
    | cons d ds => cases ws <;> simp [measuredTailOps,List.map_append,List.sum_append,lookupOpResidue,ordinaryOp,templateResidue,ih,primitivePhaseCost]

theorem opsResidue_measuredChain {n : Nat} (cs : List Wire) (t : Wire) (ws : List Wire) :
    ((@measuredChainOps n cs t ws).map lookupOpResidue).sum = 0 := by
  cases cs with
  | nil => simp [measuredChainOps,primitivePhaseCost]
  | cons c cs => cases cs <;> simp [measuredChainOps,primitivePhaseCost,opsResidue_measuredTail]

theorem opsResidue_measuredEquality {n : Nat} (cs : List Wire) (v : Nat) (t : Wire) (ws : List Wire) :
    ((@measuredEqualityOps n cs v t ws).map lookupOpResidue).sum = 0 := by
  simp [measuredEqualityOps,List.map_append,List.sum_append,opsResidue_measuredChain]

theorem opsResidue_measuredTest {n : Nat} (k : Fin 4) :
    ((@ipxMeasuredTestOps n k).map lookupOpResidue).sum = 0 := by
  simp [ipxMeasuredTestOps,List.map_append,List.sum_append,opsResidue_measuredEquality]
end ShorECDLP.Entrant.FullCredit
end

/-! EDITABLE. Zero residue for complete signed windows.

The window bodies add lookups, the zero-allowed field guards and the endpoint correction block
around the arithmetic of `Credit`.  With every block free of phase instructions and of
constant- or record-controlled non-Clifford gates, each window's exact T-count is carried by
its literal Toffoli gates alone, which credits all of them to the lowering. -/

section
namespace ShorECDLP.Entrant.FullCredit
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration ShorECDLP.Secp256k1 ShorECDLP.Entrant.AndGadget
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

/-! ## Endpoint correction lookups -/

theorem tres_endpointSelectGate {n : Nat} (q : Wire) (port : Wire × EndpointBit n) :
    ((endpointSelectGate q port).map templateResidue).sum = 0 := by
  obtain ⟨w, b⟩ := port
  rcases b with b | r
  · cases b <;> rfl
  · rfl

theorem tres_endpointSelectGates {n : Nat} (q : Wire) (ports : List (Wire × EndpointBit n)) :
    ((endpointSelectGates q ports).map templateResidue).sum = 0 := by
  unfold endpointSelectGates
  induction ports with
  | nil => rfl
  | cons p ps ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, tres_endpointSelectGate, ih]

@[simp] theorem sum_ipxTest (k : Fin 4) : ((ipxTest k).map primitivePhaseCost).sum = 0 := by
  apply primitivePhaseCost_of_HPFree
  rw [ipxTest, Classical.hpFree_append, Classical.hpFree_append]
  exact ⟨⟨computeEqConst_HPFree _ _ _ _, computeEqConst_HPFree _ _ _ _⟩,
    computeEqConst_HPFree _ _ _ _⟩

theorem opsResidue_ipx {n : Nat} (rows : Nat → Fin n) (tree : UnaryActionTree) (paths : List Wire) :
    ∀ ops : List IpxOp, ((ipxOps rows tree paths ops).map lookupOpResidue).sum = 0
  | [] => rfl
  | .query c u v :: ops => by
    rw [ipxOps, List.map_append, List.sum_append, opsResidue_ipx rows tree paths ops,
      opsResidue_unary _ (fun l q => by
        rw [ipxLeaf, List.map_append, List.sum_append, tres_endpointSelectGates,
          tres_endpointSelectGates])]
  | .test k :: ops => by
    rw [ipxOps, List.map_append, List.sum_append, opsResidue_ipx rows tree paths ops,
      opsResidue_measuredTest]

/-! ## Window bodies -/

theorem residue_zeroDivision (n start : Nat) : residue (zeroDivisionProgram n start).2 = 0 := by
  unfold zeroDivisionProgram
  rw [residue_surround, residue_division, sum_fig15ZeroPrepare, sum_fig15ZeroRestore]

theorem residue_zeroMultiplication (n start : Nat) :
    residue (zeroMultiplicationProgram n start).2 = 0 := by
  unfold zeroMultiplicationProgram
  rw [residue_surround, residue_multiplication, sum_fig15ZeroPrepare, sum_fig15ZeroRestore]

theorem residue_coordinate (start : Nat) : residue (coordinateProgram start).2 = 0 := by
  unfold coordinateProgram
  apply residue_sequence
  intro p hp s
  simp only [coordinateSegments, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h | h | h | h | h | h | h | h | h <;> subst p
  · exact residue_fieldLookupAdd _ _ s
  · exact residue_signedField _ s
  · exact residue_zeroDivision _ s
  · exact residue_pointSquare _ s
  · exact residue_fieldLookupAdd _ _ s
  · exact residue_zeroMultiplication _ s
  · exact residue_xNegate _ s
  · exact residue_fieldLookupAdd _ _ s
  · exact residue_signedField _ s

theorem residue_placed (start : Nat) : residue (Single.Physical.placedProgram start).2 = 0 := by
  unfold Single.Physical.placedProgram ipxProgramOf
  exact (residue_lookup _ _ _).trans (opsResidue_ipx _ _ _ _)

theorem residue_core (start : Nat) : residue (Single.Physical.core start).2 = 0 := by
  unfold Single.Physical.core
  apply residue_sequence
  intro p hp s
  simp only [Single.Physical.segments, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h | h | h | h <;> subst p
  · exact residue_borrowCoordinate s
  · exact residue_yNegate s
  · exact residue_placed s
  · exact residue_yNegate s

theorem residue_prepared (start : Nat) : residue (Single.Physical.prepared start).2 = 0 := by
  unfold Single.Physical.prepared
  rw [residue_surround, residue_core, sum_signedAddressCircuit]

theorem residue_actual (start : Nat) : residue (Single.Physical.actual.program start) = 0 := by
  unfold Single.Physical.actual closedWindow
  exact ((residue_shift _ _).trans (residue_cast _ _)).trans
    ((residue_relabel _ _).trans (residue_prepared 0))

-- Append within FullCredit after its generic measured Ipx residue lemmas.
attribute [local irreducible] NarrowQrom.loadProgram NarrowQrom.fieldAddProgram
  NarrowQrom.signedProgram NarrowQrom.coordinateProgram NarrowQrom.correctionProgram
  NarrowQrom.coreProgram NarrowQrom.preparedProgram appendCompiled

theorem residue_narrowLoad (field : PointField) (start : Nat) :
    residue (NarrowQrom.loadProgram field start)=0 := by
  rw [NarrowQrom.loadProgram,residue_cast,residue_lookup,NarrowQrom.loadOps]
  exact opsResidue_unary _ (fun l q=>tres_lookupLeaf _ _) _ _ _

theorem residue_narrowField (field : PointField) (acc : List Wire) (start : Nat) :
    residue (NarrowQrom.fieldAddProgram field acc start).2=0 := by
  unfold NarrowQrom.fieldAddProgram
  simp only [residue_compiled,residue_narrowLoad,residue_modularAdd,Nat.zero_add]

theorem residue_narrowSigned (field : PointField) (start : Nat) :
    residue (NarrowQrom.signedProgram field start).2=0 := by
  unfold NarrowQrom.signedProgram
  simp only [residue_compiled,residue_yNegate,residue_narrowField,Nat.zero_add]

theorem residue_narrowCoordinate (start : Nat) :
    residue (NarrowQrom.coordinateProgram start).2=0 := by
  unfold NarrowQrom.coordinateProgram
  apply residue_sequence
  intro seg hseg cursor
  simp only [NarrowQrom.coordinateSegments,List.mem_cons,List.not_mem_nil,or_false] at hseg
  rcases hseg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact residue_narrowField _ _ _
  · exact residue_narrowSigned _ _
  · exact residue_borrowDivision _ _
  · exact AndGadget.residue_paddedSquare _ _
  · exact residue_narrowField _ _ _
  · exact residue_borrowMultiplication _ _
  · exact residue_xNegate _ _
  · exact residue_narrowField _ _ _
  · exact residue_narrowSigned _ _

theorem residue_narrowCorrection (start : Nat) :
    residue (NarrowQrom.correctionProgram start).2=0 := by
  unfold NarrowQrom.correctionProgram ipxProgramOf
  exact (residue_lookup _ _ _).trans (opsResidue_ipx _ _ _ _)

theorem residue_narrowCore (start : Nat) : residue (NarrowQrom.coreProgram start).2=0 := by
  unfold NarrowQrom.coreProgram
  apply residue_sequence
  intro seg hseg cursor
  simp only [NarrowQrom.coreSegments,List.mem_cons,List.not_mem_nil,or_false] at hseg
  rcases hseg with rfl|rfl|rfl|rfl
  · exact residue_narrowCoordinate _
  · exact residue_yNegate _
  · exact residue_narrowCorrection _
  · exact residue_yNegate _

theorem residue_narrowPrepared (start : Nat) : residue (NarrowQrom.preparedProgram start).2=0 := by
  unfold NarrowQrom.preparedProgram
  rw [residue_surround,residue_narrowCore,sum_signedAddressCircuit]

theorem residue_narrowActual (start : Nat) : residue (NarrowQrom.actual.program start)=0 := by
  unfold NarrowQrom.actual closedWindow
  exact ((residue_shift _ _).trans (residue_cast _ _)).trans
    ((residue_relabel _ _).trans (residue_narrowPrepared 0))

theorem narrowFullCount (start : Nat) : AtLeast (NarrowQrom.actual.program start) 72223668 := by
  have ht := NarrowQrom.actual_t (fun _=>coefficients 0 0) start 0 (fun _=>false)
  have hr := residue_t (NarrowQrom.actual.program start)
    (readConstant (fun _=>coefficients 0 0) 0) (fun _=>false)
  rw [ht,residue_narrowActual] at hr
  unfold AtLeast
  omega

theorem residue_signedWindow (w : Single.SignedWindow) (start : Nat) :
    residue ((Single.signedWindow w).program start) = 0 := by
  unfold Single.signedWindow
  rw [residue_reindex]
  cases w <;> simp only [Single.SignedWindow.width]
  all_goals first | exact residue_narrowActual start | exact residue_actual start

/-! ## Window credits -/

/-- Every T gate of a signed window comes from an unconditional literal Toffoli. -/
theorem signedFullCount (w : Single.SignedWindow) (start : Nat) :
    AtLeast ((Single.signedWindow w).program start) (if w.width=15 then 72223668 else 72600500) := by
  have ht := Single.signedWindow_t 0 w start (fun _ => false)
  have hr := residue_t ((Single.signedWindow w).program start)
    (readConstant Single.mixedCoefficientAt 0) (fun _ => false)
  rw [ht, residue_signedWindow] at hr
  unfold AtLeast
  split_ifs at * <;> omega


end
end ShorECDLP.Entrant.FullCredit
end

section
namespace ShorECDLP.Entrant.FullCredit
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration ShorECDLP.Entrant.AndGadget
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

theorem residue_firstWindow (start : Nat) : residue (Single.firstWindow.program start) = 0 := by
  unfold Single.firstWindow
  rw [residue_reindex]
  unfold firstLookupProgram
  rw [residue_cast, residue_lookup, firstLookupOps]
  exact opsResidue_unary _ (fun l q => tres_lookupLeaf _ _) _ _ _

theorem firstFullCount (start : Nat) : AtLeast (Single.firstWindow.program start) 65535 := by
  have ht := Single.firstWindow_t_uniform 0 start (fun _ => false)
  have hr := residue_t (Single.firstWindow.program start)
    (readConstant Single.mixedCoefficientAt 0) (fun _ => false)
  rw [ht, residue_firstWindow] at hr
  unfold AtLeast
  omega
end ShorECDLP.Entrant.FullCredit
end

section
namespace ShorECDLP.Entrant.AndGadget
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unnecessarySeqFocus false
set_option Elab.async false
attribute [local irreducible] sequenceProgram appendCompiled literalProgram ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateProgram
  ShorECDLP.Entrant.BorrowFlag.fieldProgram ShorECDLP.Entrant.BorrowFlag.divisionProgram
  ShorECDLP.Entrant.BorrowFlag.multiplicationProgram Single.axis Rounded.entry

theorem AtLeast.gate {n s e d} (g : TemplateGate n) {p : Straight n s e} (hp : AtLeast p d) :
    AtLeast (.gate g p) d := by
  cases g with
  | literal g => cases g <;> simp_all [AtLeast, added] <;> omega
  | whenBit => exact hp

def templateCCX {n} : List (TemplateGate n) → Nat
  | [] => 0
  | .literal (.CCX _ _ _) :: gs => 1 + templateCCX gs
  | _ :: gs => templateCCX gs

def lookupCCX {n} : List (LookupOp n) → Nat
  | [] => 0
  | .gates gs :: ops => templateCCX gs + lookupCCX ops
  | .erase _ _ _ :: ops => lookupCCX ops

theorem added_gateProgram {n s} (gs : List (TemplateGate n)) :
    added (gateProgram gs : Straight n s s) = templateCCX gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => cases g with
    | literal g => cases g <;> simp_all [gateProgram,added,templateCCX]
    | whenBit => simp_all [gateProgram,added,templateCCX]

theorem added_andErase (n s a b t : Nat) : added (andEraseProgram n s a b t) = 0 := by
  simp [andEraseProgram,recordGates,controlledZ,added]

theorem added_lookupProgram {n} (ops : List (LookupOp n)) (start : Nat) :
    added (lookupProgram n ops start) = lookupCCX ops := by
  induction ops generalizing start with
  | nil => rfl
  | cons op ops ih => cases op <;>
      simp [lookupProgram,lookupCCX,added_append,added_cast,added_gateProgram,added_andErase,ih]

theorem lookupCCX_append {n} (a b : List (LookupOp n)) :
    lookupCCX (a++b) = lookupCCX a + lookupCCX b := by
  induction a with
  | nil => simp [lookupCCX]
  | cons op ops ih => cases op <;> simp [lookupCCX,ih,Nat.add_assoc]

theorem templateCCX_literal {n} (gs : Circuit) :
    @templateCCX n (gs.map TemplateGate.literal) = ccxCount gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => cases g <;> simp [templateCCX,ccxCount,ih,Nat.add_comm]

theorem lookupCCX_unary_ge {n} (leaf : Nat → Wire → List (TemplateGate n))
    (tree : UnaryActionTree) (q : Wire) (anc : List Wire) (hl : tree.Layout q anc) :
    tree.internalNodes ≤ lookupCCX (unaryLookupOps leaf tree q anc) := by
  induction hl with
  | leaf l q anc hn => simp [unaryLookupOps,UnaryActionTree.internalNodes,lookupCCX]
  | node bit q path zero one rest hn hz ho ihz iho =>
    simp only [unaryLookupOps,lookupCCX_append,lookupCCX,ordinaryOp,templateCCX_literal,
      computeZeroAnd,ccxCount,UnaryActionTree.internalNodes] at *
    omega

theorem lookup_count {n} (leaf : Nat → Wire → List (TemplateGate n))
    (tree : UnaryActionTree) (q : Wire) (anc : List Wire) (hl : tree.Layout q anc) (start : Nat) :
    AtLeast (lookupProgram n (unaryLookupOps leaf tree q anc) start) tree.internalNodes := by
  unfold AtLeast
  rw [added_lookupProgram]
  exact lookupCCX_unary_ge leaf tree q anc hl


section
-- Append inside AndGadget after Core.lean.
attribute [local irreducible] added fieldLookupAddProgram signedFieldProgram fieldLoadProgram modularAddProgram yNegateProgram

theorem fieldLoadCount (field : PointField) (start : Nat) :
    AtLeast (fieldLoadProgram field start) 32767 := by
  unfold fieldLoadProgram AtLeast
  rw [added_cast]
  unfold fieldLoadOps
  rw [added_lookupProgram]
  have h := lookupCCX_unary_ge
    (fun l q => fieldLeaf ⟨l%32768,Nat.mod_lt _ (by decide)⟩ field q)
    (tableAddressTree pointLookupAddress 0 1) 836 pointLookupPath
    (tableAddressTree_layout _ _ _ _ _ (by decide) (by decide))
  have hn := batchWindowTree_nodes
  unfold batchWindowTree at hn
  omega

theorem fieldAddCount (field : PointField) (acc : List Wire) (start : Nat) :
    AtLeast (fieldLookupAddProgram field acc start).2 65534 := by
  unfold fieldLookupAddProgram
  dsimp only
  refine (AtLeast.appendCompiled (d := 32767) (f := 32767) _ _ (fieldLoadCount field _) ?_).castCount (by omega)
  exact (AtLeast.appendCompiled (d := 0) (f := 32767) _ _ (AtLeast.zero _) (fieldLoadCount field _)).castCount (by omega)

theorem signedFieldCount (field : PointField) (start : Nat) :
    AtLeast (signedFieldProgram field start).2 65534 := by
  unfold signedFieldProgram
  dsimp only
  refine (AtLeast.appendCompiled (d := 0) (f := 65534) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  exact (AtLeast.appendCompiled (d := 65534) (f := 0) _ _ (fieldAddCount field _ _) (AtLeast.zero _)).castCount (by omega)

theorem ipxLookupCount_ge {n} (rows : Nat → Fin n) (tree : UnaryActionTree)
    (paths : List Wire) (hl : ∀ c, tree.Layout (ipxControl c) paths) (ops : List IpxOp) :
    ipxQueries ops * tree.internalNodes ≤ lookupCCX (ipxOps rows tree paths ops) := by
  induction ops with
  | nil => simp [ipxQueries,ipxOps,lookupCCX]
  | cons op ops ih => cases op with
    | query c u v =>
      have h := lookupCCX_unary_ge (fun l q => ipxLeaf (rows l) q u v) tree (ipxControl c) paths (hl c)
      simp only [ipxOps,lookupCCX_append,ipxQueries,Nat.add_mul,Nat.one_mul]
      omega
    | test k =>
      simp only [ipxOps,lookupCCX_append,ipxQueries]
      omega

theorem correctionQueryCount (start : Nat) :
    AtLeast (Single.Physical.placedProgram start).2 425971 := by
  unfold Single.Physical.placedProgram ipxProgramOf AtLeast
  rw [added_lookupProgram]
  have h := ipxLookupCount_ge Single.Physical.tableRows batchWindowTree pointLookupPath ipxTree_layout ipxSchedule
  rw [ipxSchedule_queries,batchWindowTree_nodes] at h
  exact h

end
attribute [local irreducible] fieldLookupAddProgram signedFieldProgram fieldLoadProgram modularAddProgram yNegateProgram
section
set_option linter.unusedSimpArgs false
attribute [local irreducible] residue

@[simp] theorem phase_constant (q : Wire) (g : Gate) :
    primitivePhaseCost (constantControlGate q g) = primitivePhaseCost g := by
  cases g with
  | CX c t => by_cases h : c=q <;> simp [constantControlGate,primitivePhaseCost,h]
  | _ => rfl
@[simp] theorem t_constant (q : Wire) (g : Gate) :
    tCost (constantControlGate q g) = tCost g := by
  cases g with
  | CX c t => by_cases h : c=q <;> simp [constantControlGate,tCost,h]
  | _ => rfl
@[simp] theorem residue_constant {n s e} (q : Wire) (p : Straight n s e) :
    residue (constantStraight q p) = residue p := by
  induction p with
  | done => rfl
  | gate g p ih => cases g <;> simp [constantStraight,constantTemplateGate,residue,ih]
  | recordGate => simp_all [constantStraight,residue]
  | measure => simp_all [constantStraight,residue]

@[simp] theorem residue_registerCorrection {n s e} (ws : List Wire) (indices : List (Fin s)) (p : Straight n s e) :
    residue (registerCorrectionProgram ws indices p) = residue p := by
  induction ws generalizing indices with
  | nil => rfl
  | cons w ws ih => cases indices <;> simp [registerCorrectionProgram,residue_recordGates,pauliZ,tCount,tCost,ih]

theorem residue_deferred (n : Nat) (ws : List Wire) (cleanup : Circuit)
    (hc : (cleanup.map primitivePhaseCost).sum = 0)
    (cells : List (Circuit × Wire))
    (hcell : ∀ cell ∈ cells, (cell.1.map primitivePhaseCost).sum = 0)
    (start : Nat) (prior : List (Fin start)) :
    residue (deferredCorrectionProgram n ws cleanup cells start prior) = 0 := by
  induction cells generalizing start with
  | nil => simp [deferredCorrectionProgram,residue_append,residue_literal,hc]
  | cons cell cells ih =>
    simp only [deferredCorrectionProgram,residue_cast,residue_append,residue_literal]
    have h := hcell cell (by simp)
    have ht := ih (by intro c hm; exact hcell c (by simp [hm]))
      (start+1) (prior.map Fin.castSucc ++ [Fin.last start])
    simpa [residue,h] using ht

@[simp] theorem phase_controlledCarry (input dirty : List Wire) (bits : List Bool) (q c : Wire) :
    ((controlledConstCarryXor input dirty bits q c).map primitivePhaseCost).sum = 0 := by
  exact controlledConstCarryXor_cost_zero primitivePhaseCost (by intros; rfl) (by intros; rfl) _ _ _ _ _

@[simp] theorem phase_flipWord (input : List Wire) :
    ((gidneyFlipWord input).map primitivePhaseCost).sum = 0 := by
  induction input with
  | nil => rfl
  | cons a input ih => simpa [gidneyFlipWord,primitivePhaseCost] using ih

@[simp] theorem phase_addCleanup (input dirty : List Wire) (bits : List Bool) (q c : Wire) :
    ((gidneyAddCleanup input dirty bits q c).map primitivePhaseCost).sum = 0 := by
  simp [gidneyAddCleanup,List.map_append,List.sum_append]

@[simp] theorem phase_addCell (q c r t a d : Wire) (k : Bool) :
    ((gidneyAddCarryCell q c r t a d k).map primitivePhaseCost).sum = 0 := by
  cases k <;> simp [gidneyAddCarryCell,primitivePhaseCost]

@[simp] theorem phase_compareCell (q c r t a d f : Wire) (k last : Bool) :
    ((gidneyCompareCarryCell q c r t a d f k last).map primitivePhaseCost).sum = 0 := by
  cases k <;> cases last <;> simp [gidneyCompareCarryCell,primitivePhaseCost]

-- Inside AndGadget after Core.
theorem phase_addCells (q current spare ancilla : Wire) (input dirty : List Wire) (bits : List Bool) :
    ∀ cell ∈ gidneyCarryCells q current spare ancilla input dirty bits,
      (cell.1.map primitivePhaseCost).sum = 0 := by
  induction input generalizing current spare dirty bits with
  | nil => simp [gidneyCarryCells]
  | cons a as ih =>
    cases as with
    | nil =>
      cases dirty <;> cases bits with
      | nil => simp [gidneyCarryCells]
      | cons k ks => cases ks <;> cases k <;> simp [gidneyCarryCells,primitivePhaseCost]
    | cons b bs =>
      cases dirty <;> cases bits <;> simp_all [gidneyCarryCells]
      exact ih spare current _ _

@[simp] theorem residue_gidneyNontrivial (n start : Nat) (a d q carry spare ancilla : Wire)
    (as ds : List Wire) (k : Bool) (ks : List Bool) :
    residue (gidneyNontrivialProgram n start a d q carry spare ancilla as ds k ks) = 0 := by
  unfold gidneyNontrivialProgram
  rw [residue_append,residue_literal,phase_addCell,Nat.zero_add]
  exact residue_deferred n _ _ (phase_addCleanup _ _ _ _ _) _ (phase_addCells _ _ _ _ _ _ _) start List.nil

@[simp] theorem residue_gidney (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (q carry spare ancilla : Wire) :
    residue (gidneyProgram n start input dirty bits q carry spare ancilla).2 = 0 := by
  by_cases h : bits.all (fun k => !k) = true
  · simp [gidneyProgram,h,residue]
  · unfold gidneyProgram
    rw [if_neg h]
    cases input with
    | nil => cases dirty <;> cases bits <;> simp [residue]
    | cons a as =>
      cases dirty with
      | nil => cases as <;> cases bits with
        | nil => simp [residue]
        | cons k ks => cases ks <;> cases k <;> simp [residue_literal,primitivePhaseCost,residue]
      | cons d ds => cases as <;> cases bits <;> simp [residue]
-- Inside AndGadget after AddParts.
theorem phase_compareCells (q current spare ancilla flag : Wire) (input dirty : List Wire) (bits : List Bool) :
    ∀ cell ∈ compareCarryCells q current spare ancilla flag input dirty bits,
      (cell.1.map primitivePhaseCost).sum = 0 := by
  induction input generalizing current spare dirty bits with
  | nil => cases dirty <;> cases bits <;> simp [compareCarryCells]
  | cons a as ih =>
    cases dirty <;> cases bits <;> simp_all [compareCarryCells]
    exact ih spare current _ _

@[simp] theorem residue_compareCarry (n start : Nat) (a d q carry spare ancilla flag : Wire)
    (input dirty : List Wire) (k : Bool) (bits : List Bool) :
    residue (compareCarryProgram n start a d q carry spare ancilla flag input dirty k bits) = 0 := by
  unfold compareCarryProgram
  rw [residue_append,residue_literal,phase_compareCell,Nat.zero_add]
  exact residue_deferred n _ _ (phase_controlledCarry _ _ _ _ _) _
    (phase_compareCells _ _ _ _ _ _ _ _) start List.nil

@[simp] theorem residue_compareCore (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (q carry spare ancilla flag : Wire) :
    residue (compareCoreProgram n start input dirty bits q carry spare ancilla flag).2 = 0 := by
  cases input <;> cases dirty <;> cases bits <;> simp [compareCoreProgram,residue]

@[simp] theorem residue_compareGE (n start : Nat) (input dirty : List Wire) (threshold : Nat)
    (q carry spare ancilla flag : Wire) :
    residue (compareGEProgram n start input dirty threshold q carry spare ancilla flag).2 = 0 := by
  unfold compareGEProgram
  by_cases h : threshold=0
  · simp [h,residue_literal,primitivePhaseCost]
  · rw [if_neg h]
    by_cases h2 : 2^input.length ≤ threshold
    · simp [h2,residue]
    · rw [if_neg h2]; exact residue_compareCore _ _ _ _ _ _ _ _ _ _

@[simp] theorem residue_uncontrolledCompare (n start : Nat) (input dirty : List Wire) (threshold : Nat)
    (carry spare ancilla flag : Wire) :
    residue (uncontrolledCompareProgram n start input dirty threshold carry spare ancilla flag).2 = 0 := by
  unfold uncontrolledCompareProgram
  rw [residue_constant]
  exact residue_compareGE _ _ _ _ _ _ _ _ _ _

@[simp] theorem phase_addCarry (input acc : List Wire) (q c f : Wire) :
    ((controlledAddCarry input acc q c f).map primitivePhaseCost).sum = 0 := by
  exact primitivePhaseCost_of_HPFree _ (controlledAddCarry_HPFree _ _ _ _ _)
@[simp] theorem phase_subCarry (input acc : List Wire) (q c f : Wire) :
    ((controlledSubCarry input acc q c f).map primitivePhaseCost).sum = 0 := by
  exact primitivePhaseCost_of_HPFree _ (controlledSubCarry_HPFree _ _ _ _ _)
@[simp] theorem phase_compareLT (input acc : List Wire) (q c f : Wire) :
    ((controlledCompareLT input acc q c f).map primitivePhaseCost).sum = 0 := by
  exact primitivePhaseCost_of_HPFree _ (controlledCompareLT_HPFree _ _ _ _ _)

attribute [local irreducible] gidneyProgram uncontrolledCompareProgram
@[simp] theorem residue_modularAdd (n start : Nat) (input acc : List Wire) (correction : List Bool)
    (modulus : Nat) (q c r t f : Wire) :
    residue (modularAddProgram n start input acc correction modulus q c r t f).2 = 0 := by
  simp [modularAddProgram,residue_compiled,residue_append,residue_literal]

@[simp] theorem residue_modularSub (n start : Nat) (input acc : List Wire) (modulus : List Bool)
    (p : Nat) (q c r t f : Wire) :
    residue (modularSubProgram n start input acc modulus p q c r t f).2 = 0 := by
  simp [modularSubProgram,residue_compiled,residue_prepend,residue_literal]
-- Inside AndGadget after CompareParts.
@[simp] theorem phase_adjoint (gs : Circuit) :
    (gs.adjoint.map primitivePhaseCost).sum = (gs.map primitivePhaseCost).sum := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rw [circuit_adjoint_cons,List.map_append,List.sum_append,ih]
    cases g <;> simp [Gate.adjoint,primitivePhaseCost,Nat.add_comm]

@[simp] theorem phase_doubleShift (acc : List Wire) (f : Wire) :
    ((doublingShift acc f).map primitivePhaseCost).sum = 0 :=
  primitivePhaseCost_of_HPFree _ (doublingShift_HPFree _ _)

@[simp] theorem residue_modularDouble (n start : Nat) (acc dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) :
    residue (modularDoubleProgram n start acc dirty bits p c r t f).2 = 0 := by
  cases acc <;> simp [modularDoubleProgram,residue_prepend,residue_compiled,residue_literal,primitivePhaseCost,residue]

@[simp] theorem residue_modularHalve (n start : Nat) (acc dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) :
    residue (modularHalveProgram n start acc dirty bits p c r t f).2 = 0 := by
  cases acc <;> simp [modularHalveProgram,residue_prepend,residue_compiled,residue_literal,primitivePhaseCost,residue]

attribute [local irreducible] modularSubProgram modularDoubleProgram modularHalveProgram
@[simp] theorem residue_squareAdd (n start : Nat) (input acc : List Wire) (bits : List Bool)
    (p : Nat) (q copied c r t f : Wire) :
    residue (squareAddProgram n start input acc bits p q copied c r t f).2 = 0 := by
  simp [squareAddProgram,residue_prepend,residue_compiled,residue_literal,primitivePhaseCost]
@[simp] theorem residue_squareSub (n start : Nat) (input acc : List Wire) (bits : List Bool)
    (p : Nat) (q copied c r t f : Wire) :
    residue (squareSubProgram n start input acc bits p q copied c r t f).2 = 0 := by
  simp [squareSubProgram,residue_prepend,residue_compiled,residue_literal,primitivePhaseCost]

attribute [local irreducible] squareAddProgram squareSubProgram
@[simp] theorem residue_square (n start : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (copied c r t f : Wire) :
    residue (squareProgram n start controls input acc bits p copied c r t f).2 = 0 := by
  change compiledResidue (squareProgram n start controls input acc bits p copied c r t f) = 0
  induction controls generalizing start with
  | nil => simp [squareProgram,compiledResidue,residue]
  | cons q qs ih =>
    rw [squareProgram]
    simp only [compiledResidue] at ih ⊢
    simp only [residue_compiled,ih,Nat.zero_add,residue_ite]
    split <;> simp [residue_compiled]

@[simp] theorem residue_squareInverse (n start : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (copied c r t f : Wire) :
    residue (squareInverseProgram n start controls input acc bits p copied c r t f).2 = 0 := by
  change compiledResidue (squareInverseProgram n start controls input acc bits p copied c r t f) = 0
  induction controls generalizing start with
  | nil => simp [squareInverseProgram,compiledResidue,residue]
  | cons q qs ih =>
    rw [squareInverseProgram]
    simp only [compiledResidue] at ih ⊢
    simp only [residue_compiled,residue_squareSub,Nat.zero_add,residue_ite]
    split <;> simp [residue_compiled,residue,ih]

attribute [local irreducible] squareProgram squareInverseProgram
@[simp] theorem residue_squareSubtract (n start : Nat) (x y acc : List Wire) (correction modulus : List Bool)
    (p : Nat) (q copied c r t f : Wire) :
    residue (squareSubtractProgram n start x y acc correction modulus p q copied c r t f).2 = 0 := by
  simp [squareSubtractProgram,residue_compiled]

@[simp] theorem residue_pointSquare (n start : Nat) : residue (pointSquareProgram n start).2 = 0 := by
  unfold pointSquareProgram
  exact residue_squareSubtract _ _ _ _ _ _ _ _ _ _ _ _ _ _

attribute [local irreducible] added pointSquareProgram
-- Exact arithmetic T count is already protected by the imported source theorem.
theorem pointSquareCount (n start : Nat) : AtLeast (pointSquareProgram n start).2 2223879 := by
  have hr := residue_t (pointSquareProgram n start).2 (fun _ => false) (fun _ => false)
  have ht := pointSquareProgram_tCount n start (fun _ => false) (fun _ => false)
  rw [fig14SquareSubtract_counts.1] at ht
  have hz := residue_pointSquare n start
  unfold AtLeast compiledTCount at *
  omega

end
section
set_option linter.unusedSimpArgs false
attribute [local irreducible] added residue modularSubProgram modularDoubleProgram modularHalveProgram
-- Inside AndGadget, after SquareParts; generic source only.
@[simp] theorem residue_horner (n start : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) :
    residue (hornerProgram n start controls input acc bits p c r t f).2 = 0 := by
  change compiledResidue (hornerProgram n start controls input acc bits p c r t f) = 0
  induction controls generalizing start with
  | nil => simp [hornerProgram,compiledResidue,residue]
  | cons q qs ih =>
    rw [hornerProgram]
    simp only [compiledResidue] at ih ⊢
    simp only [residue_compiled,ih,Nat.zero_add,residue_ite]
    split <;> simp [residue_compiled]

@[simp] theorem residue_hornerInverse (n start : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) :
    residue (hornerInverseProgram n start controls input acc bits p c r t f).2 = 0 := by
  change compiledResidue (hornerInverseProgram n start controls input acc bits p c r t f) = 0
  induction controls generalizing start with
  | nil => simp [hornerInverseProgram,compiledResidue,residue]
  | cons q qs ih =>
    rw [hornerInverseProgram]
    simp only [compiledResidue] at ih ⊢
    simp only [residue_compiled,residue_modularSub,Nat.zero_add,residue_ite]
    split <;> simp [residue_compiled,residue,ih]

@[simp] theorem residue_multiplyWork (n start : Nat) : residue (multiplyWorkProgram n start).2 = 0 := by
  unfold multiplyWorkProgram
  exact residue_horner _ _ _ _ _ _ _ _ _ _ _
@[simp] theorem residue_multiplyData (n start : Nat) : residue (multiplyDataProgram n start).2 = 0 := by
  unfold multiplyDataProgram
  exact residue_horner _ _ _ _ _ _ _ _ _ _ _
@[simp] theorem residue_unmultiplyData (n start : Nat) : residue (unmultiplyDataProgram n start).2 = 0 := by
  unfold unmultiplyDataProgram
  exact residue_hornerInverse _ _ _ _ _ _ _ _ _ _ _

attribute [local irreducible] multiplyWorkProgram multiplyDataProgram unmultiplyDataProgram

theorem multiplyWorkCount (n start : Nat) : AtLeast (multiplyWorkProgram n start).2 1110533 := by
  have hr := residue_t (multiplyWorkProgram n start).2 (fun _ => false) (fun _ => false)
  have ht := multiplyWorkProgram_tCount n start (fun _ => false) (fun _ => false)
  rw [fig15MultiplyToWork_resources.1] at ht
  have hz := residue_multiplyWork n start
  unfold AtLeast compiledTCount at *
  omega

theorem multiplyDataCount (n start : Nat) : AtLeast (multiplyDataProgram n start).2 1110533 := by
  have hr := residue_t (multiplyDataProgram n start).2 (fun _ => false) (fun _ => false)
  have ht := multiplyDataProgram_tCount n start (fun _ => false) (fun _ => false)
  rw [fig15MultiplyToData_resources.1] at ht
  have hz := residue_multiplyData n start
  unfold AtLeast compiledTCount at *
  omega

theorem unmultiplyDataCount (n start : Nat) : AtLeast (unmultiplyDataProgram n start).2 1110533 := by
  have hr := residue_t (unmultiplyDataProgram n start).2 (fun _ => false) (fun _ => false)
  have ht := unmultiplyDataProgram_tCount n start (fun _ => false) (fun _ => false)
  rw [fig15MultiplyToDataInverse_resources.1] at ht
  have hz := residue_unmultiplyData n start
  unfold AtLeast compiledTCount at *
  omega
-- Inside AndGadget after HornerParts.
attribute [local irreducible] divisionCleanupProgram divisionCorrectionProgram
 divisionAfterResetProgram divisionProgram multiplicationAfterResetProgram
 multiplicationCleanupProgram multiplicationCorrectionProgram multiplicationProgram
 measuredForwardDataBankProgram measuredReverseDataBankProgram

theorem divisionCleanupStrongCount (n start : Nat) :
    AtLeast (divisionCleanupProgram n start).2 1110533 := by
  unfold divisionCleanupProgram appendLiteral
  exact (AtLeast.appendCompiled _ _ (unmultiplyDataCount n start) (AtLeast.zero _)).castCount (by omega)

theorem divisionCorrectionStrongCount (n start : Nat) (prior : List (Fin start)) :
    AtLeast (divisionCorrectionProgram n start prior).2 1110533 := by
  unfold divisionCorrectionProgram
  exact (AtLeast.appendCompiled _ _ (AtLeast.zero _) (divisionCleanupStrongCount n _)).castCount (by omega)

theorem divisionAfterStrongCount (n start : Nat) (prior : List (Fin start)) :
    AtLeast (divisionAfterResetProgram n start prior).2 17993555 := by
  unfold divisionAfterResetProgram appendRetaining
  refine (AtLeast.appendCompiled (d := 16883022) (f := 1110533) _ _ ?_ (divisionCorrectionStrongCount n _ _)).castCount (by omega)
  exact (AtLeast.appendCompiled _ _ (reverseBankCount n start) (multiplyDataCount n _)).castCount (by omega)

theorem divisionStrongCount (n start : Nat) : AtLeast (divisionProgram n start).2 34876577 := by
  unfold divisionProgram
  refine (AtLeast.appendCompiled (d := 16883022) (f := 17993555) _ _ ?_ ?_).castCount (by omega)
  · exact (AtLeast.appendCompiled _ _ (forwardWrapperFullCount n start) (multiplyWorkCount n _)).castCount (by omega)
  · exact AtLeast.collect (divisionAfterResetProgram n) (divisionAfterStrongCount n) _ _ _

theorem multiplicationCleanupStrongCount (n start : Nat) :
    AtLeast (multiplicationCleanupProgram n start).2 16883022 := by
  unfold multiplicationCleanupProgram appendLiteral
  refine (AtLeast.appendCompiled (d := 1110533) (f := 15772489) _ _ (unmultiplyDataCount n _) ?_).castCount (by omega)
  exact (AtLeast.appendCompiled _ _ (reverseBankCount n _) (AtLeast.zero _)).castCount (by omega)

theorem multiplicationCorrectionStrongCount (n start : Nat) (prior : List (Fin start)) :
    AtLeast (multiplicationCorrectionProgram n start prior).2 16883022 := by
  unfold multiplicationCorrectionProgram
  exact (AtLeast.appendCompiled _ _ (AtLeast.zero _) (multiplicationCleanupStrongCount n _)).castCount (by omega)

theorem multiplicationAfterStrongCount (n start : Nat) (prior : List (Fin start)) :
    AtLeast (multiplicationAfterResetProgram n start prior).2 33766044 := by
  unfold multiplicationAfterResetProgram appendRetaining
  refine (AtLeast.appendCompiled (d := 16883022) (f := 16883022) _ _ ?_ (multiplicationCorrectionStrongCount n _ _)).castCount (by omega)
  exact (AtLeast.appendCompiled _ _ (forwardBankCount n start) (multiplyDataCount n _)).castCount (by omega)

theorem multiplicationStrongCount (n start : Nat) : AtLeast (multiplicationProgram n start).2 34876577 := by
  unfold multiplicationProgram
  refine (AtLeast.appendCompiled (d := 1110533) (f := 33766044) _ _ (multiplyWorkCount n start) ?_).castCount (by omega)
  exact AtLeast.collect (multiplicationAfterResetProgram n) (multiplicationAfterStrongCount n) _ _ _

end
section
set_option linter.unusedSimpArgs false
open Classical
attribute [local irreducible] added residue gidneyProgram uncontrolledCompareProgram

@[simp] theorem phase_complement (input : List Wire) (q : Wire) :
    ((controlledComplement input q).map primitivePhaseCost).sum = 0 := by
  apply primitivePhaseCost_of_HPFree
  simp [controlledComplement,HPFree]

@[simp] theorem residue_constMinus (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (q c r t : Wire) : residue (constMinusProgram n start input dirty bits q c r t).2 = 0 := by
  simp [constMinusProgram,residue_prepend,residue_compiled]

attribute [local irreducible] constMinusProgram
@[simp] theorem residue_center (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t iter : Wire) : residue (eeaCenterProgram n start input dirty bits p c r t iter).2 = 0 := by
  simp [eeaCenterProgram,residue_compiled]
@[simp] theorem residue_uncenter (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t iter : Wire) : residue (eeaUncenterProgram n start input dirty bits p c r t iter).2 = 0 := by
  simp [eeaUncenterProgram,residue_compiled]
@[simp] theorem residue_parity (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (c r t iter : Wire) : residue (eeaParityProgram n start input dirty bits c r t iter).2 = 0 := by
  simp [eeaParityProgram,residue_prepend,residue_compiled,residue_literal,primitivePhaseCost]

@[simp] theorem phase_workPrepare : (workRegistersPrepare.map primitivePhaseCost).sum = 0 :=
  primitivePhaseCost_of_HPFree _ workRegistersPrepare_resources.2.1
@[simp] theorem phase_workRestore : (workRegistersRestore.map primitivePhaseCost).sum = 0 :=
  primitivePhaseCost_of_HPFree _ workRegistersRestore_resources.2.1
@[simp] theorem phase_lengthSetup : (eeaLengthSetup.map primitivePhaseCost).sum = 0 := by
  apply primitivePhaseCost_of_HPFree
  simp only [eeaLengthSetup,hpFree_append]
  exact ⟨⟨xorConstant_HPFree _ _,xorConstant_HPFree _ _⟩,lengthInitialize_HPFree _ _ _ _ _⟩
@[simp] theorem phase_lengthUndo : (eeaLengthUndo.map primitivePhaseCost).sum = 0 := by
  apply primitivePhaseCost_of_HPFree
  simp only [eeaLengthUndo,hpFree_append]
  exact ⟨⟨lengthInitialize_HPFree _ _ _ _ _,xorConstant_HPFree _ _⟩,xorConstant_HPFree _ _⟩

attribute [local irreducible] eeaCenterProgram eeaUncenterProgram eeaParityProgram
@[simp] theorem residue_preprocess (n start : Nat) : residue (preprocessProgram n start).2 = 0 := by
  simp [preprocessProgram,residue_surround]
@[simp] theorem residue_unpreprocess (n start : Nat) : residue (unpreprocessProgram n start).2 = 0 := by
  simp [unpreprocessProgram,residue_surround]
@[simp] theorem residue_productionParity (n start : Nat) : residue (productionParityProgram n start).2 = 0 := by
  unfold productionParityProgram
  exact residue_parity _ _ _ _ _ _ _ _ _

@[simp] theorem phase_canonical : (canonicalWork2Rotation.map primitivePhaseCost).sum = 0 :=
  primitivePhaseCost_of_HPFree _ canonicalWork2Rotation_HPFree
@[simp] theorem phase_inverseCanonical : (canonicalWork2InverseRotation.map primitivePhaseCost).sum = 0 :=
  primitivePhaseCost_of_HPFree _ canonicalWork2InverseRotation_HPFree
@[simp] theorem phase_epoch : (terminalEpochCompression.map primitivePhaseCost).sum = 0 := by
  apply primitivePhaseCost_of_HPFree
  simp [terminalEpochCompression,mcxVChain_HPFree]
@[simp] theorem phase_terminalClear : (terminalWork1Clear.map primitivePhaseCost).sum = 0 :=
  primitivePhaseCost_of_HPFree _ (xorConstant_HPFree _ _)

attribute [local irreducible] preprocessProgram unpreprocessProgram productionParityProgram
 measuredEEAForwardProgram measuredEEAReverseProgram
@[simp] theorem residue_forwardWrapper (n start : Nat) : residue (measuredForwardWrapperProgram n start).2 = 0 := by
  unfold measuredForwardWrapperProgram
  apply residue_sequence
  intro seg hseg cursor
  simp only [measuredForwardWrapperSegments,List.mem_cons,List.not_mem_nil,or_false] at hseg
  rcases hseg with rfl | rfl | rfl | rfl | rfl
  · exact residue_preprocess _ _
  · unfold measuredEEAForwardProgram; exact residue_measuredSchedule _ _ _ _ _ _
  · simp [residue_literal,List.map_append,List.sum_append]
  · exact residue_productionParity _ _
  · simp [residue_literal]

@[simp] theorem residue_reverseWrapper (n start : Nat) : residue (measuredReverseWrapperProgram n start).2 = 0 := by
  unfold measuredReverseWrapperProgram
  apply residue_sequence
  intro seg hseg cursor
  simp only [measuredReverseWrapperSegments,List.mem_cons,List.not_mem_nil,or_false] at hseg
  rcases hseg with rfl | rfl | rfl | rfl | rfl
  · simp [residue_literal]
  · exact residue_productionParity _ _
  · simp [residue_literal,List.map_append,List.sum_append]
  · unfold measuredEEAReverseProgram; exact residue_measuredInverseSchedule _ _ _ _ _
  · exact residue_unpreprocess _ _

attribute [local irreducible] measuredForwardWrapperProgram measuredReverseWrapperProgram

theorem forwardWrapperCompleteCount (n start : Nat) : AtLeast (measuredForwardWrapperProgram n start).2 15910015 := by
  have hs := secp256k1MeasuredEEAForwardWrapper_toffoli
  have hl := adaptive_ccx_cost_le secp256k1MeasuredEEAForwardWrapper
  have ht := measuredForwardWrapperProgram_tCount n start (fun _ => false) (fun _ => false)
  have hr := residue_t (measuredForwardWrapperProgram n start).2 (fun _ => false) (fun _ => false)
  have hz := residue_forwardWrapper n start
  unfold AtLeast compiledTCount at *
  omega

theorem reverseWrapperCompleteCount (n start : Nat) : AtLeast (measuredReverseWrapperProgram n start).2 15910015 := by
  have hs := secp256k1MeasuredEEAReverseWrapper_toffoli
  have hl := adaptive_ccx_cost_le secp256k1MeasuredEEAReverseWrapper
  have ht := measuredReverseWrapperProgram_tCount n start (fun _ => false) (fun _ => false)
  have hr := residue_t (measuredReverseWrapperProgram n start).2 (fun _ => false) (fun _ => false)
  have hz := residue_reverseWrapper n start
  unfold AtLeast compiledTCount at *
  omega

theorem forwardBankCompleteCount (n start : Nat) :
    AtLeast (measuredForwardDataBankProgram n start).2 15910015 :=
  AtLeast.relabelCompiled _ (forwardWrapperCompleteCount n start) eeaWorkspaceExchange

theorem reverseBankCompleteCount (n start : Nat) :
    AtLeast (measuredReverseDataBankProgram n start).2 15910015 :=
  AtLeast.relabelCompiled _ (reverseWrapperCompleteCount n start) eeaWorkspaceExchange

-- Inside AndGadget after HornerParts.
attribute [local irreducible] divisionCleanupProgram divisionCorrectionProgram
 divisionAfterResetProgram divisionProgram multiplicationAfterResetProgram
 multiplicationCleanupProgram multiplicationCorrectionProgram multiplicationProgram
 measuredForwardDataBankProgram measuredReverseDataBankProgram

theorem divisionCleanupCompleteCount (n start : Nat) :
    AtLeast (divisionCleanupProgram n start).2 1110533 := by
  unfold divisionCleanupProgram appendLiteral
  exact (AtLeast.appendCompiled _ _ (unmultiplyDataCount n start) (AtLeast.zero _)).castCount (by omega)

theorem divisionCorrectionCompleteCount (n start : Nat) (prior : List (Fin start)) :
    AtLeast (divisionCorrectionProgram n start prior).2 1110533 := by
  unfold divisionCorrectionProgram
  exact (AtLeast.appendCompiled _ _ (AtLeast.zero _) (divisionCleanupCompleteCount n _)).castCount (by omega)

theorem divisionAfterCompleteCount (n start : Nat) (prior : List (Fin start)) :
    AtLeast (divisionAfterResetProgram n start prior).2 18131081 := by
  unfold divisionAfterResetProgram appendRetaining
  refine (AtLeast.appendCompiled (d := 17020548) (f := 1110533) _ _ ?_ (divisionCorrectionCompleteCount n _ _)).castCount (by omega)
  exact (AtLeast.appendCompiled _ _ (reverseBankCompleteCount n start) (multiplyDataCount n _)).castCount (by omega)

theorem divisionCompleteCount (n start : Nat) : AtLeast (divisionProgram n start).2 35151629 := by
  unfold divisionProgram
  refine (AtLeast.appendCompiled (d := 17020548) (f := 18131081) _ _ ?_ ?_).castCount (by omega)
  · exact (AtLeast.appendCompiled _ _ (forwardWrapperCompleteCount n start) (multiplyWorkCount n _)).castCount (by omega)
  · exact AtLeast.collect (divisionAfterResetProgram n) (divisionAfterCompleteCount n) _ _ _

theorem multiplicationCleanupCompleteCount (n start : Nat) :
    AtLeast (multiplicationCleanupProgram n start).2 17020548 := by
  unfold multiplicationCleanupProgram appendLiteral
  refine (AtLeast.appendCompiled (d := 1110533) (f := 15910015) _ _ (unmultiplyDataCount n _) ?_).castCount (by omega)
  exact (AtLeast.appendCompiled _ _ (reverseBankCompleteCount n _) (AtLeast.zero _)).castCount (by omega)

theorem multiplicationCorrectionCompleteCount (n start : Nat) (prior : List (Fin start)) :
    AtLeast (multiplicationCorrectionProgram n start prior).2 17020548 := by
  unfold multiplicationCorrectionProgram
  exact (AtLeast.appendCompiled _ _ (AtLeast.zero _) (multiplicationCleanupCompleteCount n _)).castCount (by omega)

theorem multiplicationAfterCompleteCount (n start : Nat) (prior : List (Fin start)) :
    AtLeast (multiplicationAfterResetProgram n start prior).2 34041096 := by
  unfold multiplicationAfterResetProgram appendRetaining
  refine (AtLeast.appendCompiled (d := 17020548) (f := 17020548) _ _ ?_ (multiplicationCorrectionCompleteCount n _ _)).castCount (by omega)
  exact (AtLeast.appendCompiled _ _ (forwardBankCompleteCount n start) (multiplyDataCount n _)).castCount (by omega)

theorem multiplicationCompleteCount (n start : Nat) : AtLeast (multiplicationProgram n start).2 35151629 := by
  unfold multiplicationProgram
  refine (AtLeast.appendCompiled (d := 1110533) (f := 34041096) _ _ (multiplyWorkCount n start) ?_).castCount (by omega)
  exact AtLeast.collect (multiplicationAfterResetProgram n) (multiplicationAfterCompleteCount n) _ _ _


end
theorem borrowedFieldCount (n start d : Nat) (arithmetic : FixedSegment n)
    (hc : ∀ cursor, AtLeast (arithmetic cursor).2 d) :
    AtLeast (ShorECDLP.Entrant.BorrowFlag.fieldProgram n start arithmetic).2 d := by
  unfold ShorECDLP.Entrant.BorrowFlag.fieldProgram
  apply AtLeast.surroundCompiled
  unfold ShorECDLP.Entrant.BorrowFlag.coreSegments
  refine (AtLeast.sequenceCons (d := 0) (f := d) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  exact (AtLeast.sequenceCons (d := d) (f := 0) _ _ (hc _) (AtLeast.zero _)).castCount (by omega)

theorem borrowedDivisionCount (n start : Nat) :
    AtLeast (ShorECDLP.Entrant.BorrowFlag.divisionProgram n start).2 35151629 := by
  unfold ShorECDLP.Entrant.BorrowFlag.divisionProgram
  exact borrowedFieldCount n start 35151629 _ (divisionCompleteCount n)

theorem borrowedMultiplicationCount (n start : Nat) :
    AtLeast (ShorECDLP.Entrant.BorrowFlag.multiplicationProgram n start).2 35151629 := by
  unfold ShorECDLP.Entrant.BorrowFlag.multiplicationProgram
  exact borrowedFieldCount n start 35151629 _ (multiplicationCompleteCount n)

theorem borrowedCoordinateAllCount (start : Nat) : AtLeast (ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateProgram start).2 72131866 := by
  unfold ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateProgram ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateSegments
  refine (AtLeast.sequenceCons (d := 65534) (f := 72066332) _ _ (fieldAddCount _ _ _) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 65534) (f := 72000798) _ _ (signedFieldCount _ _) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 35151629) (f := 36849169) _ _ (borrowedDivisionCount _ _) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 1500938) (f := 35348231) _ _ (paddedSquareCount _ _) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 65534) (f := 35282697) _ _ (fieldAddCount _ _ _) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 35151629) (f := 131068) _ _ (borrowedMultiplicationCount _ _) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 0) (f := 131068) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 65534) (f := 65534) _ _ (fieldAddCount _ _ _) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 65534) (f := 0) _ _ (signedFieldCount _ _) ?_).castCount (by omega)
  exact AtLeast.zero _

theorem coreCount (start : Nat) : AtLeast (Single.Physical.core start).2 72557837 := by
  unfold Single.Physical.core Single.Physical.segments
  refine (AtLeast.sequenceCons (d := 72131866) (f := 425971) _ _ (borrowedCoordinateAllCount start) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 0) (f := 425971) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  exact (AtLeast.sequenceCons (d := 425971) (f := 0) _ _ (correctionQueryCount _) (AtLeast.zero _)).castCount (by omega)

theorem preparedCount (start : Nat) : AtLeast (Single.Physical.prepared start).2 72557837 := by
  unfold Single.Physical.prepared
  exact AtLeast.surroundCompiled _ _ _ (coreCount start)

theorem actualCount (start : Nat) : AtLeast (Single.Physical.actual.program start) 72557837 := by
  unfold Single.Physical.actual closedWindow
  exact (((preparedCount 0).relabel (windowAddressPerm 855 (by decide))).castFinish _).shift start

theorem signedCount (w : Single.SignedWindow) (start : Nat) :
    AtLeast ((Single.signedWindow w).program start) 72181005 := by
  have h := FullCredit.signedFullCount w start
  unfold AtLeast at *
  split_ifs at * <;> omega

theorem prepareCount {n s e d} (ws : List Wire) {p : Straight n s e} (hp : AtLeast p d) :
    AtLeast (prepareOuterBank ws p) d := by
  induction ws with
  | nil => exact hp
  | cons w ws ih => exact AtLeast.gate (.literal (.H w)) ih

structure CountedWindow (n : Nat) where
  source : Single.Window n
  saving : Nat
  countProof : ∀ start, AtLeast (source.program start) saving

def leftCountes : List (CountedWindow 851968) :=
  ⟨Single.firstWindow,65535,FullCredit.firstFullCount⟩ ::
    Single.leftSigned.map (fun w => ⟨Single.signedWindow w,(if w.width=15 then 72223668 else 72600500),FullCredit.signedFullCount w⟩)
def rightCountes : List (CountedWindow 851968) :=
  Single.rightSigned.map (fun w => ⟨Single.signedWindow w,(if w.width=15 then 72223668 else 72600500),FullCredit.signedFullCount w⟩)
private theorem leftCountes_source : leftCountes.map CountedWindow.source = Single.leftWindows := by
  simp [leftCountes, Single.leftWindows]
private theorem rightCountes_source : rightCountes.map CountedWindow.source = Single.rightWindows := by
  simp [rightCountes, Single.rightWindows]
private theorem leftCountes_saving : (leftCountes.map CountedWindow.saving).sum = 1158282047 := by
  simp [leftCountes, Single.leftSigned,Single.SignedWindow.width]
private theorem rightCountes_saving : (rightCountes.map CountedWindow.saving).sum = 943429668 := by
  simp [rightCountes, Single.rightSigned,Single.SignedWindow.width]

theorem axisCountProof {n} : (ps : List (CountedWindow n)) → (start : Nat) → (prior : List (Fin start)) →
    AtLeast (Single.axis (ps.map CountedWindow.source) start prior) ((ps.map CountedWindow.saving).sum)
  | [], _, _ => AtLeast.zero _
  | p::ps, start, prior => by
    simp only [List.map_cons, List.sum_cons, Single.axis]
    refine AtLeast.castFinish ?_ _
    refine AtLeast.castCount (AtLeast.append (f := (ps.map CountedWindow.saving).sum) (prepareCount _ (p.countProof start)) ?_) (by omega)
    exact (AtLeast.append (AtLeast.zero _) (axisCountProof ps _ (Single.nextPrior p.source.count p.source.wires.length prior))).castCount (by omega)

theorem axisCountFor {n} (ps : List (CountedWindow n)) (ws : List (Single.Window n))
    (he : ps.map CountedWindow.source = ws) (start : Nat) (prior : List (Fin start)) :
    AtLeast (Single.axis ws start prior) ((ps.map CountedWindow.saving).sum) := by
  subst ws
  exact axisCountProof ps start prior

theorem AtLeast.framed {n s m k e f dl dr} (p : Straight n s m) (q : Straight n m k)
    (r : Straight n k e) (h : e=f) (hp : AtLeast p dl) (hq : AtLeast q dr) :
    AtLeast (Single.framed p q r h) (dl+dr) := by
  unfold Single.framed
  exact AtLeast.gate _ ((AtLeast.append hp ((AtLeast.append hq (AtLeast.gate _ (AtLeast.zero _))).castCount (Nat.add_zero dr))).castFinish h)

theorem trialCount (start : Nat) : AtLeast (Single.trial start) 2101711715 := by
  have hl := (axisCountFor leftCountes Single.leftWindows leftCountes_source start List.nil).castCount leftCountes_saving
  have hr := (axisCountFor rightCountes Single.rightWindows rightCountes_source
    (start+Single.axisCount Single.leftWindows) List.nil).castCount rightCountes_saving
  unfold Single.trial
  exact (AtLeast.framed _ _ _ _ hl hr).castCount (by decide)

theorem programCount : AtLeast Single.program 2101711715 := by
  unfold Single.program
  exact (trialCount 0).castFinish _

theorem AtLeast.fixedEntry {n e d} (f : Fin n → PointCoeff) (p : Straight n 0 e) (hp : AtLeast p d) :
    AtLeast (Single.fixedEntry f p).program d := by
  unfold Single.fixedEntry
  exact hp.reindex _

theorem entryCount : AtLeast Rounded.entry.program 2101711715 := by
  unfold Rounded.entry Rounded.program
  apply AtLeast.fixedEntry
  exact ((AtLeast.append programCount (AtLeast.zero Rounded.readout)).castCount (by omega))

theorem dropped_added {n s e d} {p q : Straight n s e} (h : Optimization.Drops p q d) :
    7 * added p ≤ 7 * added q + d := by
  induction h with
  | refl => omega
  | skip g h ih => cases g <;> simp_all [added, tCost] <;> omega
  | gate g h ih =>
    cases g with
    | literal g => cases g <;> simp_all [added] <;> omega
    | whenBit => exact ih
  | record => assumption
  | measure => assumption

attribute [local irreducible] added lower lowerEntry lowerLayout Optimization.entryPatch



theorem entry_count_after_drop (e : StraightEntry) {d : Nat}
    (hp : Optimization.Patch e.program d) (c l : Nat)
    (hc : c≤added e.program) (hn : 7*l+d≤7*c) :
    l≤added (Optimization.replaceEntry e hp.program).program := by
  have h := dropped_added hp.drops
  change l≤added hp.program
  omega

theorem parent_added_lower : 2072020355 ≤ added Parent.entry.program :=
  entry_count_after_drop Rounded.entry Optimization.entryPatch
    2101711715 2072020355 entryCount (by decide)

theorem within_reindex {n m s e} (p : Straight n s e) (f : Fin n → Fin m) (ws : List Wire)
    (hp : Within ws p) : Within ws (reindexStraight f p) := by
  induction p with
  | done => trivial
  | gate g p ih => cases g <;> exact ⟨hp.1, ih hp.2⟩
  | recordGate => exact ⟨hp.1, by apply_assumption; exact hp.2⟩
  | measure => exact ⟨hp.1, by apply_assumption; exact hp.2⟩


theorem within_drops {n s e d} {p q : Straight n s e} (h : Optimization.Drops p q d)
    (ws : List Wire) (hp : Within ws p) : Within ws q := by
  induction h with
  | refl => exact hp
  | skip g h ih => exact ih hp.2
  | gate g h ih => cases g <;> exact ⟨hp.1, ih hp.2⟩
  | record i v g h ih => exact ⟨hp.1, ih hp.2⟩
  | measure w h ih => exact ⟨hp.1, ih hp.2⟩


theorem fixedEntry_within {n e} (f : Fin n → PointCoeff) (p : Straight n 0 e)
    (ws : List Wire) (hp : Within ws p) : Within ws (Single.fixedEntry f p).program :=
  within_reindex p _ ws hp


attribute [local irreducible] Within

theorem parent_within : Within resetWires Parent.entry.program := by
  unfold Parent.entry Optimization.replaceEntry
  apply within_drops Optimization.entryPatch.drops
  unfold Rounded.entry
  apply fixedEntry_within
  apply within_of_instantiate
  intro read history
  have he : history = Fin.elim0 := by funext i; exact Fin.elim0 i
  subst history
  exact Rounded.program_support read


set_option maxRecDepth 2000

theorem parent_added_upper : added Parent.entry.program ≤ 7375384892 := by
  have h := lower_t 1024 Parent.entry.program 0 Fin.elim0
    (readConstant Parent.entry.coefficients.get 0) Fin.elim0 Fin.elim0
    (by funext i; exact Fin.elim0 i)
  have ht := (Parent.certificate.resources 0).2.1
  change (Parent.entry.program.instantiate (readConstant Parent.entry.coefficients.get 0) Fin.elim0).tCount ≤ 14504198259 at ht
  omega


theorem parent_slots : Parent.entry.program.gateSlots ≤ 90000176648 := by
  have hs := Optimization.entryPatch.drops.slots
  have ho : Rounded.entry.program.gateSlots ≤ 90000176648 := by
    rw [Rounded.entry, Single.fixedEntry_slots]
    exact Rounded.program_slots
  unfold Parent.entry Optimization.replaceEntry
  exact hs.trans ho

end
end ShorECDLP.Entrant.AndGadget

namespace ShorECDLP.Entrant.Five
open Challenge AndGadget Paper2607_13816.ChallengeMigration
attribute [local irreducible] Within
set_option maxRecDepth 10000
attribute [local irreducible] added lower lowerEntry lowerLayout Optimization.entryPatch
noncomputable def entry : StraightEntry := lowerEntry 1024 Parent.entry
noncomputable def layout : DecodeLayout := lowerLayout 1024 Parent.entry Parent.layout
def bounds : Bounds := ⟨855, 10360157549, 8265980838⟩

private theorem resourceArithmetic (a slots cursor oldT newT maxSlots maxRecords newRecords : Nat)
    (ha : a ≤ 7375384892) (hl : 2072020355 ≤ a) (hs : slots ≤ 90000176648)
    (hc : cursor ≤ 886843252) (ho : oldT ≤ 14504198259) (hn : 10360157549 ≤ newT)
    (hls : 4000000000000000 ≤ maxSlots) (hlm : 47471340504 ≤ maxRecords)
    (hnm : 8265980838 ≤ newRecords) :
    slots + 18*a ≤ maxSlots ∧ cursor+a ≤ maxRecords ∧ oldT ≤ newT + 2*a ∧
    cursor+a ≤ newRecords := by omega

theorem certificate : Certificate officialLimits layout entry bounds := by
  have h := resourceArithmetic (added Parent.entry.program) Parent.entry.program.gateSlots
    Parent.entry.finalCursor Parent.bounds.tModel bounds.tModel officialLimits.gateSlots
    officialLimits.measurements bounds.measurements
    parent_added_upper parent_added_lower parent_slots (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  apply lower_certificate officialLimits Parent.layout Parent.entry Parent.bounds bounds
    1024 resetWires Parent.certificate parent_within
  · simp [resetWires]
  · exact h.1
  · exact h.2.1
  · change resetWires.length + 1 ≤ 855
    rw [resetWires_length]
  · exact h.2.2.1
  · exact h.2.2.2
end ShorECDLP.Entrant.Five
end

section
namespace ShorECDLP.Entrant.Previous23
open Challenge AndGadget Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
attribute [local irreducible] added lower lowerEntry lowerLayout Within
  Catalyst.saved Catalyst.compileEntry Optimization.entryPatch

private theorem cursor_bound (limits : Limits) (layout : DecodeLayout) (e : StraightEntry)
    (b : Bounds) (h : Certificate limits layout e b) : e.finalCursor ≤ b.measurements := by
  have hm := (h.resources 0).2.2
  have he := e.program.measurementCount (readConstant e.coefficients.get 0) Fin.elim0
  change (e.program.instantiate (readConstant e.coefficients.get 0) Fin.elim0).measurementCount ≤ b.measurements at hm
  omega

private theorem lowerEntry_within (q : Wire) (e : StraightEntry) (ws : List Wire)
    (hs : Within ws e.program) : Within (q::ws) (lowerEntry q e).program := by
  unfold lowerEntry
  exact lower_within q e.program ws hs 0 Fin.elim0

private theorem lowerEntry_saved (q : Wire) (e : StraightEntry) :
    Catalyst.saved (lowerEntry q e).program = added e.program + Catalyst.saved e.program := by
  unfold lowerEntry
  exact Catalyst.saved_lower q e.program 0 Fin.elim0

private theorem lowerEntry_slots (q : Wire) (e : StraightEntry) :
    (lowerEntry q e).program.gateSlots = e.program.gateSlots + 18 * added e.program := by
  unfold lowerEntry
  exact lower_slots q e.program 0 Fin.elim0

private theorem five_within : Within (1024 :: resetWires) Five.entry.program :=
  lowerEntry_within 1024 Parent.entry resetWires parent_within

private theorem saved_bound (a b s : Nat) (he : s = a+b) (hl : 2072020355 ≤ a) :
    2072020355 ≤ s := by omega

private theorem five_saved : 2072020355 ≤ Catalyst.saved Five.entry.program :=
  saved_bound (added Parent.entry.program) (Catalyst.saved Parent.entry.program)
    (Catalyst.saved Five.entry.program) (lowerEntry_saved 1024 Parent.entry) parent_added_lower

private theorem slots_bound (old new a : Nat) (he : new = old + 18*a)
    (hs : old ≤ 90000176648) (ha : a ≤ 7375384892) : new ≤ 230350301035 := by omega

private theorem five_slots : Five.entry.program.gateSlots ≤ 230350301035 :=
  slots_bound Parent.entry.program.gateSlots Five.entry.program.gateSlots
    (added Parent.entry.program) (lowerEntry_slots 1024 Parent.entry) parent_slots parent_added_upper

noncomputable def entry : StraightEntry := Catalyst.compileEntry 1025 Five.entry
noncomputable def layout : DecodeLayout := Five.layout
def bounds : Bounds := ⟨856, 8288137195, 8265980838⟩

private theorem resourceArithmetic (s a c oldT newT maxSlots m : Nat)
    (hs : s ≤ 230350301035) (ha : a ≤ s) (hl : 2072020355 ≤ a)
    (hc : c ≤ 8265980838) (ho : oldT ≤ 10360157549) (hn : 8288137195 ≤ newT)
    (hls : 4000000000000000 ≤ maxSlots) (hm : 8265980838 ≤ m) :
    s + 3*a + 2 ≤ maxSlots ∧ oldT + 1 ≤ newT + a ∧ c ≤ m := by omega

theorem certificate : Certificate officialLimits layout entry bounds := by
  have h := resourceArithmetic Five.entry.program.gateSlots (Catalyst.saved Five.entry.program)
    Five.entry.finalCursor Five.bounds.tModel bounds.tModel officialLimits.gateSlots bounds.measurements
    five_slots (Catalyst.saved_le_slots Five.entry.program) five_saved
    (cursor_bound officialLimits Five.layout Five.entry Five.bounds Five.certificate)
    (by decide) (by decide) (by decide) (by decide)
  apply Catalyst.compile_certificate officialLimits Five.layout Five.entry Five.bounds bounds
    1025 (1024 :: resetWires) Five.certificate five_within
  · simp [resetWires]
  · exact h.1
  · change (1024 :: resetWires).length + 1 ≤ 856
    simp [resetWires_length]
  · exact h.2.1
  · exact h.2.2
end
end ShorECDLP.Entrant.Previous23
end

namespace ShorECDLP.Entrant.TransportOptimization
open Quantum Challenge Paper2607_13816.ChallengeMigration
open Paper2607_13816
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 200000
set_option Elab.async false
set_option linter.unusedSimpArgs false
attribute [local irreducible] sequenceProgram appendCompiled literalProgram
  remainderBlockProgram coefficientBlockProgram phaseProgram hProgram intervalProgram coefficientProgram
  preprocessProgram productionParityProgram measuredStepProgram measuredScheduleProgram
  measuredEEAForwardProgram measuredForwardWrapperProgram multiplyWorkProgram divisionAfterResetProgram
  divisionProgram zeroDivisionProgram fieldLookupAddProgram signedFieldProgram pointSquareProgram
  zeroMultiplicationProgram xNegateProgram coordinateProgram
  measuredInverseStepProgram measuredEEAReverseProgram measuredReverseWrapperProgram
  hInverseProgram phaseInverseProgram coefficientInverseProgram intervalInverseProgram
  measuredForwardDataBankProgram measuredReverseDataBankProgram multiplicationProgram
  multiplicationAfterResetProgram multiplicationCorrectionProgram multiplicationCleanupProgram
  multiplyDataProgram unmultiplyDataProgram divisionCorrectionProgram collectProgram


def Patch.prependCompiled {n start d} (gs : Circuit)
    (p : (count : Nat) × Straight n start (start+count)) (hp : Patch p.2 d) :
    Patch (Paper2607_13816.ChallengeMigration.prependCompiled gs p).2 d := by
  unfold Paper2607_13816.ChallengeMigration.prependCompiled
  exact ((Patch.refl (literalProgram gs)).append hp).castSaving (Nat.zero_add d)

def Patch.surroundCompiled {n start d} (before after : Circuit)
    (p : (count : Nat) × Straight n start (start+count)) (hp : Patch p.2 d) :
    Patch (Paper2607_13816.ChallengeMigration.surroundCompiled before after p).2 d := by
  unfold Paper2607_13816.ChallengeMigration.surroundCompiled Paper2607_13816.ChallengeMigration.prependCompiled
  exact ((Patch.refl (literalProgram before)).append
    ((Patch.appendCompiled p ⟨0, literalProgram after⟩ hp (Patch.refl _)).castSaving (Nat.add_zero d))).castSaving (Nat.zero_add d)

/-- Rewrite one terminal-epoch restore inside an otherwise untouched literal segment. -/
def epochPatch (n s : Nat) (tail : Circuit) :
    Patch (literalProgram (Cancellation.epochSource ++ tail) : Straight n s s) 112 := by
  apply Patch.literal _ (Cancellation.reducedEpoch ++ tail)
  · exact Cancellation.reducedEpoch_sublist.append (List.Sublist.refl _)
  · simp only [Quantum.run_append_map, Cancellation.reducedEpoch_run]
  · have h := Cancellation.reducedEpoch_counts
    simp only [ShorECDLP.tCount_append, h.1, h.2.1]
    omega



set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- Literal concatenation supports mirrored segments without changing their context. -/
private theorem literal_append {n s : Nat} (xs ys : Circuit) :
    (literalProgram (xs ++ ys) : Straight n s s) =
      (literalProgram xs).append (literalProgram ys) := by
  induction xs with
  | nil => simp only [List.nil_append, literalProgram, List.map_nil, gateProgram, Straight.append]
  | cons g xs ih => simpa only [literalProgram, List.map_cons, gateProgram, Straight.append] using congrArg (Straight.gate (.literal g)) ih

def Patch.joinLiteral {n s d f} {xs ys : Circuit}
    (hp : Patch (literalProgram xs : Straight n s s) d)
    (hq : Patch (literalProgram ys : Straight n s s) f) :
    Patch (literalProgram (xs ++ ys) : Straight n s s) (d+f) := by
  rw [literal_append]
  exact hp.append hq

open Quantum Challenge Paper2607_13816.ChallengeMigration
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

theorem control_drops {xs ys : Circuit} (hr : ControlTransport.Reduction xs ys) (n start : Nat) :
    Drops (literalProgram xs : Straight n start start) (literalProgram ys)
      (ShorECDLP.tCount xs-ShorECDLP.tCount ys) := by
  induction hr with
  | nil=>exact Drops.refl _
  | @keep g xs ys h ih=>
    simpa only [literalProgram,gateProgram,List.map_cons,ShorECDLP.tCount_cons,
      Nat.add_sub_add_left] using Drops.gate (.literal g) ih
  | @fuse a b t hab hat hbt xs ys h ih=>
    have ht:=h.tle
    have hh:=Drops.control a b t ⟨hab,hat,hbt⟩ ih
    have hd : ShorECDLP.tCount (.CCX a b t :: .CX a b :: .CCX a b t :: xs)-
        ShorECDLP.tCount (.CX a b :: .CX a t :: ys)=
        14+(ShorECDLP.tCount xs-ShorECDLP.tCount ys) := by
      simp only [ShorECDLP.tCount_cons,tCost]
      omega
    rw [hd]
    simpa only [literalProgram, gateProgram, List.map_cons] using hh

noncomputable def controlPatch (n start d : Nat) (xs : Circuit)
    (ht : ShorECDLP.tCount (ControlTransport.optimize xs)+d=ShorECDLP.tCount xs) :
    Patch (literalProgram xs : Straight n start start) d := by
  refine ⟨literalProgram (ControlTransport.optimize xs),?_,
    Rewrites.literal xs (ControlTransport.optimize xs) (ControlTransport.optimize_rel xs).run⟩
  have hd : ShorECDLP.tCount xs-ShorECDLP.tCount (ControlTransport.optimize xs)=d := by omega
  simpa only [hd] using control_drops (ControlTransport.optimize_rel xs) n start



def smallPatch (n start d : Nat) (xs : Circuit) (hw : CircuitWellFormed xs)
    (ht : ShorECDLP.tCount (ControlTransport.optimize (Transport.optimize (Cancellation.optimize xs)))+d=
      ShorECDLP.tCount xs) : Patch (literalProgram xs : Straight n start start) d := by
  refine ⟨literalProgram (ControlTransport.optimize (Transport.optimize (Cancellation.optimize xs))),?_,?_⟩
  · have h1:=Drops.literal (n:=n) (s:=start) (Cancellation.optimize_sublist xs)
    have h2:=transport_drops (Transport.optimize_rel (Cancellation.optimize xs)) n start
    have h3:=control_drops (ControlTransport.optimize_rel (Transport.optimize (Cancellation.optimize xs))) n start
    have hl1 := Cancellation.optimize_sublist xs
    have hl2 := (Transport.optimize_rel (Cancellation.optimize xs)).tle
    have hl3 := (ControlTransport.optimize_rel (Transport.optimize (Cancellation.optimize xs))).tle
    have hc : ShorECDLP.tCount (Cancellation.optimize xs)≤ShorECDLP.tCount xs :=
      tCount_le_of_sublist hl1
    have hd : (ShorECDLP.tCount xs-ShorECDLP.tCount (Cancellation.optimize xs))+
        ((ShorECDLP.tCount (Cancellation.optimize xs)-ShorECDLP.tCount
          (Transport.optimize (Cancellation.optimize xs)))+
        (ShorECDLP.tCount (Transport.optimize (Cancellation.optimize xs))-ShorECDLP.tCount
          (ControlTransport.optimize (Transport.optimize (Cancellation.optimize xs)))))=d := by omega
    simpa only [hd] using Drops.trans h1 (Drops.trans h2 h3)
  · exact Rewrites.literal _ _ (((Cancellation.optimize_run xs hw).symm.trans
      (Transport.optimize_rel (Cancellation.optimize xs)).run).trans
      (ControlTransport.optimize_rel (Transport.optimize (Cancellation.optimize xs))).run)

noncomputable def acrossSmallPatch (n start d : Nat) (xs : Circuit) (hw : CircuitWellFormed xs)
    (ht : ShorECDLP.tCount (AcrossRight.optimize (AcrossLeft.optimize
      (ControlTransport.optimize (Transport.optimize (Cancellation.optimize xs)))))+d=
      ShorECDLP.tCount xs) : Patch (literalProgram xs : Straight n start start) d := by
  refine ⟨literalProgram (AcrossRight.optimize (AcrossLeft.optimize
    (ControlTransport.optimize (Transport.optimize (Cancellation.optimize xs))))),?_,?_⟩
  · have h1:=Drops.literal (n:=n) (s:=start) (Cancellation.optimize_sublist xs)
    have h2:=transport_drops (Transport.optimize_rel (Cancellation.optimize xs)) n start
    have h3:=control_drops (ControlTransport.optimize_rel (Transport.optimize (Cancellation.optimize xs))) n start
    have h4:=acrossLeft_drops (AcrossLeft.optimize_rel
      (ControlTransport.optimize (Transport.optimize (Cancellation.optimize xs)))) n start
    have h5:=acrossRight_drops (AcrossRight.optimize_rel (AcrossLeft.optimize
      (ControlTransport.optimize (Transport.optimize (Cancellation.optimize xs))))) n start
    have hl2 := (Transport.optimize_rel (Cancellation.optimize xs)).tle
    have hl3 := (ControlTransport.optimize_rel (Transport.optimize (Cancellation.optimize xs))).tle
    have hl4 := (AcrossLeft.optimize_rel (ControlTransport.optimize (Transport.optimize (Cancellation.optimize xs)))).tle
    have hl5 := (AcrossRight.optimize_rel (AcrossLeft.optimize
      (ControlTransport.optimize (Transport.optimize (Cancellation.optimize xs))))).tle
    have hc : ShorECDLP.tCount (Cancellation.optimize xs)≤ShorECDLP.tCount xs :=
      tCount_le_of_sublist (Cancellation.optimize_sublist xs)
    have hd : (ShorECDLP.tCount xs-ShorECDLP.tCount (Cancellation.optimize xs))+
        ((ShorECDLP.tCount (Cancellation.optimize xs)-ShorECDLP.tCount
          (Transport.optimize (Cancellation.optimize xs)))+
        ((ShorECDLP.tCount (Transport.optimize (Cancellation.optimize xs))-ShorECDLP.tCount
          (ControlTransport.optimize (Transport.optimize (Cancellation.optimize xs))))+
        ((ShorECDLP.tCount (ControlTransport.optimize (Transport.optimize (Cancellation.optimize xs)))-ShorECDLP.tCount
          (AcrossLeft.optimize (ControlTransport.optimize (Transport.optimize (Cancellation.optimize xs)))))+
        (ShorECDLP.tCount (AcrossLeft.optimize (ControlTransport.optimize (Transport.optimize (Cancellation.optimize xs))))-ShorECDLP.tCount
          (AcrossRight.optimize (AcrossLeft.optimize (ControlTransport.optimize (Transport.optimize (Cancellation.optimize xs)))))))))=d := by omega
    simpa only [hd] using Drops.trans h1 (Drops.trans h2 (Drops.trans h3 (Drops.trans h4 h5)))
  · exact Rewrites.literal _ _ (((((Cancellation.optimize_run xs hw).symm.trans
      (Transport.optimize_rel (Cancellation.optimize xs)).run).trans
      (ControlTransport.optimize_rel (Transport.optimize (Cancellation.optimize xs))).run).trans
      (AcrossLeft.optimize_rel (ControlTransport.optimize (Transport.optimize (Cancellation.optimize xs)))).run).trans
      (AcrossRight.optimize_rel (AcrossLeft.optimize (ControlTransport.optimize (Transport.optimize (Cancellation.optimize xs))))).run)

namespace DH32
set_option maxHeartbeats 1000000
def optimized (xs : Circuit) : Circuit := AcrossRight.optimize (AcrossLeft.optimize (ControlTransport.optimize (Transport.optimize (Cancellation.optimize xs))))
def Facts (xs : Circuit) (d : Nat) : Prop := CircuitWellFormed xs ∧ ShorECDLP.tCount (optimized xs)+d=ShorECDLP.tCount xs

def dPrefix (c : Wire) : Circuit := cuccaroAdd (List.range' 522 9) (List.range' 531 9) c ++ addConstant (List.range' 531 9) (List.range' 560 9) c 3
def dSuffix (c : Wire) : Circuit := subConstant (List.range' 531 9) (List.range' 560 9) c 3 ++ cuccaroSub (List.range' 522 9) (List.range' 531 9) c

theorem dPrefix_facts : ∀ c ∈ 0 :: List.range' 569 9, Facts (dPrefix c) 42 := by
  unfold Facts CircuitWellFormed optimized
  decide +kernel

theorem dSuffix_facts : ∀ c ∈ 0 :: List.range' 569 9, Facts (dSuffix c) 42 := by
  unfold Facts CircuitWellFormed optimized
  decide +kernel

def inverseFirst : Circuit :=
  let r := indexedStepProductionRegisters
  computeControl [r.phase1,r.phase2] 1 r.control r.sourceScratch ++
  controlledIncrement r.control r.lengthQ (r.sourceScratch.take (r.lengthQ.length-1)) ++
  computeControl [r.phase1,r.phase2] 1 r.control r.sourceScratch

def inverseLast : Circuit :=
  let r := indexedStepProductionRegisters
  computeControl [r.phase1,r.phase2] 2 r.control r.sourceScratch ++
  controlledDecrement r.control r.lengthQ (r.sourceScratch.take (r.lengthQ.length-1)) ++
  computeControl [r.phase1,r.phase2] 2 r.control r.sourceScratch

theorem d1_facts : Facts (blockD1Forward indexedStepProductionRegisters) 7 := by unfold Facts CircuitWellFormed optimized; decide +kernel
theorem d3_facts : Facts (blockD3Forward indexedStepProductionRegisters) 7 := by unfold Facts CircuitWellFormed optimized; decide +kernel
theorem di1_facts : Facts inverseFirst 7 := by unfold Facts CircuitWellFormed optimized; decide +kernel
theorem di3_facts : Facts inverseLast 7 := by unfold Facts CircuitWellFormed optimized; decide +kernel

theorem hUpper_facts : Facts (constMinus (List.range' 549 9) (List.range' 562 9) 571 258) 28 := by
  unfold Facts CircuitWellFormed optimized; decide +kernel
theorem hLowerAdd_facts : Facts (addConstant (List.range' 522 9) (List.range' 562 9) 571 3) 21 := by
  unfold Facts CircuitWellFormed optimized; decide +kernel
theorem hLowerSub_facts : Facts (subConstant (List.range' 522 9) (List.range' 562 9) 571 3) 21 := by
  unfold Facts CircuitWellFormed optimized; decide +kernel


private theorem qview_cases (b : Nat) (hb : 9≤b) :
    ((List.range' 560 18).take (b+1)).take 9 = List.range' 560 9 ∧
    ((List.range' 560 18).take (b+1)).getD b 0 ∈ 0 :: List.range' 569 9 := by
  by_cases h : b≤17
  · interval_cases b <;> decide
  · have ht : (List.range' 560 18).take (b+1) = List.range' 560 18 :=
      List.take_of_length_le (by simp; omega)
    rw [ht]
    refine ⟨by decide, ?_⟩
    rw [List.getD_eq_default _ _ (by simp; omega)]
    simp

theorem quotient_views (w : ActiveWindow) :
    (indexedStepProductionRegisters.quotient w).constantScratch = List.range' 560 9 ∧
    (indexedStepProductionRegisters.quotient w).carry w.start w.stop ∈ 0 :: List.range' 569 9 := by
  exact qview_cases (max 9 (quotientSwapUnaryDepth w.start w.stop)) (Nat.le_max_left _ _)

private theorem hview_cases (b : Nat) (hb : 10≤b) :
    ((List.range' 562 16).take b).take 9 = List.range' 562 9 ∧
    ((List.range' 562 16).take b).getD 9 0 = 571 := by
  by_cases h : b≤16
  · interval_cases b <;> decide
  · have ht : (List.range' 562 16).take b = List.range' 562 16 := List.take_of_length_le (by simp; omega)
    rw [ht]
    decide

theorem endpoint_views (T : Nat) :
    (indexedStepProductionRegisters.endIteration 256 T).constants = List.range' 562 9 ∧
    (indexedStepProductionRegisters.endIteration 256 T).carry = 571 := by
  apply hview_cases
  change 10≤max (max 10 _) (max 10 _)
  omega

def surroundPatch {n start a b c : Nat} (before after : Circuit)
    (p : (count : Nat) × Straight n start (start+count))
    (hb : Patch (literalProgram before : Straight n start start) a)
    (hp : Patch p.2 b)
    (ha : ∀ cursor, Patch (literalProgram after : Straight n cursor cursor) c) :
    Patch (surroundCompiled before after p).2 (a+b+c) := by
  unfold surroundCompiled prependCompiled
  exact (hb.append ((Patch.appendCompiled p ⟨0,literalProgram after⟩ hp (ha _)))).castSaving (by omega)

def dPrefixPatch (n start : Nat) (c : Wire) (hc : c ∈ 0 :: List.range' 569 9) :
    Patch (literalProgram (dPrefix c) : Straight n start start) 42 :=
  acrossSmallPatch n start 42 _ (dPrefix_facts c hc).1 (dPrefix_facts c hc).2

def dSuffixPatch (n start : Nat) (c : Wire) (hc : c ∈ 0 :: List.range' 569 9) :
    Patch (literalProgram (dSuffix c) : Straight n start start) 42 :=
  acrossSmallPatch n start 42 _ (dSuffix_facts c hc).1 (dSuffix_facts c hc).2

def quotientPatch (n start : Nat) (w : ActiveWindow) :
    Patch (literalProgram (quotientSwapUnitary (indexedStepProductionRegisters.quotient w) w.start w.stop) : Straight n start start) 84 := by
  let q := indexedStepProductionRegisters.quotient w
  let c := q.carry w.start w.stop
  have hv := quotient_views w
  have hp := ((dPrefixPatch n start c hv.2).joinLiteral
    ((Patch.refl (literalProgram (unaryActionUnitary .inc (quotientSwapLeaf q w.start)
      (quotientSwapTree q w.start w.stop) q.control (q.path w.start w.stop)) : Straight n start start)).joinLiteral
      (dSuffixPatch n start c hv.2))).castSaving (show 42+(0+42)=84 by omega)
  simpa only [quotientSwapUnitary,dPrefix,dSuffix,q,c,hv.1,List.append_assoc] using hp

def dForwardPatch (n start : Nat) (w : ActiveWindow) :
    Patch (literalProgram (blockDForward indexedStepProductionRegisters w) : Straight n start start) 98 := by
  let r := indexedStepProductionRegisters
  have hp := ((acrossSmallPatch n start 7 (blockD1Forward r) d1_facts.1 d1_facts.2).joinLiteral
    ((Patch.refl (literalProgram ([.CX r.phase1 r.control,.CX r.phase2 r.control]) : Straight n start start)).joinLiteral
      ((quotientPatch n start w).joinLiteral
        ((Patch.refl (literalProgram ([.CX r.phase2 r.control,.CX r.phase1 r.control]) : Straight n start start)).joinLiteral
          (acrossSmallPatch n start 7 (blockD3Forward r) d3_facts.1 d3_facts.2))))).castSaving (show 7+(0+(84+(0+7)))=98 by omega)
  simpa only [blockDForward,blockD2Forward,List.append_assoc] using hp

def dInversePatch (n start : Nat) (w : ActiveWindow) :
    Patch (literalProgram (blockDInverse indexedStepProductionRegisters w) : Straight n start start) 98 := by
  let r := indexedStepProductionRegisters
  have hp := ((acrossSmallPatch n start 7 inverseFirst di1_facts.1 di1_facts.2).joinLiteral
    ((Patch.refl (literalProgram ([.CX r.phase1 r.control,.CX r.phase2 r.control]) : Straight n start start)).joinLiteral
      ((quotientPatch n start w).joinLiteral
        ((Patch.refl (literalProgram ([.CX r.phase2 r.control,.CX r.phase1 r.control]) : Straight n start start)).joinLiteral
          (acrossSmallPatch n start 7 inverseLast di3_facts.1 di3_facts.2))))).castSaving (show 7+(0+(84+(0+7)))=98 by omega)
  simpa only [blockDInverse,inverseFirst,inverseLast,List.append_assoc] using hp

def upperPatch (n start T : Nat) :
    Patch (upperEndProgram n start (indexedStepProductionRegisters.endIteration 256 T) 256 (endIterationWindowsAt 256 T)).2 56 := by
  have hv := endpoint_views T
  unfold upperEndProgram ltUpdateProgram
  dsimp only
  refine (surroundPatch (a:=28) (b:=0) (c:=28) _ _ _ ?_ (Patch.refl _) ?_).castSaving (by omega)
  · simpa only [hv.1,hv.2] using (acrossSmallPatch n start 28 _ hUpper_facts.1 hUpper_facts.2)
  · intro cursor
    simpa only [hv.1,hv.2] using (acrossSmallPatch n cursor 28 _ hUpper_facts.1 hUpper_facts.2)

def lowerPatch (n start T : Nat) :
    Patch (lowerEndProgram n start (indexedStepProductionRegisters.endIteration 256 T) 256 (endIterationWindowsAt 256 T)).2 42 := by
  have hv := endpoint_views T
  unfold lowerEndProgram lrpUpdateProgram
  dsimp only
  refine (surroundPatch (a:=21) (b:=0) (c:=21) _ _ _ ?_ (Patch.refl _) ?_).castSaving (by omega)
  · simpa only [hv.1,hv.2] using (acrossSmallPatch n start 21 _ hLowerAdd_facts.1 hLowerAdd_facts.2)
  · intro cursor
    simpa only [hv.1,hv.2] using (acrossSmallPatch n cursor 21 _ hLowerSub_facts.1 hLowerSub_facts.2)

def endPatch (n start T : Nat) :
    Patch (endProgram n start (indexedStepProductionRegisters.endIteration 256 T) 256 (endIterationWindowsAt 256 T)).2 98 := by
  unfold endProgram
  exact (Patch.prependCompiled _ _ ((Patch.appendCompiled _ _ (upperPatch n start T) (lowerPatch n _ T)))).castSaving (by omega)

def endInversePatch (n start T : Nat) :
    Patch (endInverseProgram n start (indexedStepProductionRegisters.endIteration 256 T) 256 (endIterationWindowsAt 256 T)).2 98 := by
  unfold endInverseProgram
  exact (Patch.appendCompiled _ _ (lowerPatch n start T)
    ((Patch.appendCompiled (d:=56) (f:=0) _ _ (upperPatch n _ T) (Patch.refl _)).castSaving (show 56+0=56 by omega))).castSaving (by omega)

def hSaving (T : Nat) : Nat := if T%4=0 then 98 else 0

def hPatch (n start T : Nat) : Patch (hProgram n start indexedStepProductionRegisters 256 T).2 (hSaving T) := by
  by_cases ht : T%4=0
  · unfold hProgram
    rw [if_pos ht]
    simp only [hSaving,ht,if_pos]
    exact Patch.surroundCompiled _ _ _ (endPatch n start T)
  · unfold hProgram
    rw [if_neg ht]
    simp only [hSaving,ht,if_neg]
    exact Patch.refl _

def hInversePatch (n start T : Nat) : Patch (hInverseProgram n start indexedStepProductionRegisters 256 T).2 (hSaving T) := by
  by_cases ht : T%4=0
  · unfold hInverseProgram
    rw [if_pos ht]
    simp only [hSaving,ht,if_pos]
    exact Patch.surroundCompiled _ _ _ (endInversePatch n start T)
  · unfold hInverseProgram
    rw [if_neg ht]
    simp only [hSaving,ht,if_neg]
    exact Patch.refl _
end DH32

def epochDPatch (n start : Nat) (w : ActiveWindow) :
    Patch (literalProgram (blockCForward indexedStepProductionRegisters ++ blockDForward indexedStepProductionRegisters w) : Straight n start start) 210 := by
  simpa only [Cancellation.epochSource,List.append_nil] using
    ((epochPatch n start List.nil).joinLiteral (DH32.dForwardPatch n start w)).castSaving (show 112+98=210 by omega)

def shiftFlags (r : ShiftRegisters) : Circuit :=
  [.X r.phase1,.CX r.phase1 r.phase1IsZero,.X r.phase1]
def shiftedLiteral (c p2 : Wire) (work ls : List Wire) (both : Wire) (cs : List Wire) : Circuit :=
  controlledRotateLeftOne c work ++ controlledIncrement c ls cs ++
  [.CCX c p2 both] ++ controlledRotateRightTwo both work ++
  controlledDecrement both ls cs ++ controlledDecrement both ls cs ++ [.CCX c p2 both]
theorem preShift_expand (r : ShiftRegisters) : preShiftUnitary r =
    shiftFlags r ++ shiftedLiteral r.phase1IsZero r.phase2 r.work r.lengthS r.both r.carries ++
    shiftFlags r := rfl
theorem postShift_expand (r : ShiftRegisters) : postShiftUnitary r =
    shiftedLiteral r.phase1 r.phase2 r.work r.lengthS r.both r.carries := rfl

def aSource : Circuit := blockAForward indexedStepProductionRegisters
def aMiddle : Circuit := (aSource.drop 837).take 33
def aReduced : Circuit := aSource.take 837 ++ Cancellation.optimize aMiddle ++ aSource.drop 870

private theorem split_three (xs : Circuit) (a b : Nat) :
    xs = xs.take a ++ (xs.drop a).take b ++ xs.drop (a+b) := by
  rw [List.append_assoc, ← List.drop_drop]
  rw [List.take_append_drop, List.take_append_drop]

private theorem aSplit : aSource = aSource.take 837 ++ aMiddle ++ aSource.drop 870 :=
  split_three aSource 837 33

private theorem aMiddle_wellFormed : CircuitWellFormed aMiddle := by
  unfold CircuitWellFormed
  decide +kernel

private theorem aMiddle_counts : ShorECDLP.tCount aMiddle = 105 ∧
    ShorECDLP.tCount (Cancellation.optimize aMiddle) = 7 := by
  decide +kernel

def aPatch (n start : Nat) : Patch (literalProgram (aSource) : Straight n start start) 140 := by
  simpa only [aSource, blockAForward, terminalPaddingForward, terminalPaddingPrefix, preShift_expand, shiftedLiteral, shiftFlags, List.append_assoc, List.append_nil, circuit_adjoint_append] using ((Patch.refl (literalProgram (computeControl (indexedStepProductionRegisters.phase1 :: indexedStepProductionRegisters.lengthRPrime) (2^(indexedStepProductionRegisters.lengthRPrime.length+1)-2) indexedStepProductionRegisters.terminal indexedStepProductionRegisters.blockScratch) : Straight n start start)).joinLiteral ((Patch.refl (literalProgram (controlledRotateLeftOne indexedStepProductionRegisters.terminalPadding.terminal indexedStepProductionRegisters.terminalPadding.work2) : Straight n start start)).joinLiteral ((smallPatch n start 7 (controlledIncrement indexedStepProductionRegisters.terminalPadding.terminal indexedStepProductionRegisters.terminalPadding.lengthS indexedStepProductionRegisters.terminalPadding.carries) (by unfold CircuitWellFormed; decide +kernel) (by decide +kernel)).joinLiteral ((smallPatch n start 98 (terminalPaddingEpochUpdate indexedStepProductionRegisters.terminalPadding) (by unfold CircuitWellFormed; decide +kernel) (by decide +kernel)).joinLiteral ((Patch.refl (literalProgram (([.CX indexedStepProductionRegisters.terminal indexedStepProductionRegisters.phase1] : Circuit)) : Straight n start start)).joinLiteral ((Patch.refl (literalProgram (([.X indexedStepProductionRegisters.preShift.phase1, .CX indexedStepProductionRegisters.preShift.phase1 indexedStepProductionRegisters.preShift.phase1IsZero, .X indexedStepProductionRegisters.preShift.phase1] : Circuit)) : Straight n start start)).joinLiteral ((Patch.refl (literalProgram (controlledRotateLeftOne indexedStepProductionRegisters.preShift.phase1IsZero indexedStepProductionRegisters.preShift.work) : Straight n start start)).joinLiteral ((smallPatch n start 7 (controlledIncrement indexedStepProductionRegisters.preShift.phase1IsZero indexedStepProductionRegisters.preShift.lengthS indexedStepProductionRegisters.preShift.carries) (by unfold CircuitWellFormed; decide +kernel) (by decide +kernel)).joinLiteral ((Patch.refl (literalProgram (([.CCX indexedStepProductionRegisters.preShift.phase1IsZero indexedStepProductionRegisters.preShift.phase2 indexedStepProductionRegisters.preShift.both] : Circuit)) : Straight n start start)).joinLiteral ((Patch.refl (literalProgram (controlledRotateRightTwo indexedStepProductionRegisters.preShift.both indexedStepProductionRegisters.preShift.work) : Straight n start start)).joinLiteral ((smallPatch n start 28 ((controlledDecrement indexedStepProductionRegisters.preShift.both indexedStepProductionRegisters.preShift.lengthS indexedStepProductionRegisters.preShift.carries ++ controlledDecrement indexedStepProductionRegisters.preShift.both indexedStepProductionRegisters.preShift.lengthS indexedStepProductionRegisters.preShift.carries)) (by unfold CircuitWellFormed; decide +kernel) (by decide +kernel)).joinLiteral ((Patch.refl (literalProgram (([.CCX indexedStepProductionRegisters.preShift.phase1IsZero indexedStepProductionRegisters.preShift.phase2 indexedStepProductionRegisters.preShift.both] : Circuit)) : Straight n start start)).joinLiteral ((Patch.refl (literalProgram (([.X indexedStepProductionRegisters.preShift.phase1, .CX indexedStepProductionRegisters.preShift.phase1 indexedStepProductionRegisters.preShift.phase1IsZero, .X indexedStepProductionRegisters.preShift.phase1] : Circuit)) : Straight n start start)).joinLiteral ((Patch.refl (literalProgram (([.CX indexedStepProductionRegisters.terminal indexedStepProductionRegisters.phase1] : Circuit)) : Straight n start start)).joinLiteral ((Patch.refl (literalProgram (terminalEpochSpill indexedStepProductionRegisters.terminal indexedStepProductionRegisters.shiftEpoch indexedStepProductionRegisters.quotientLow) : Straight n start start)).joinLiteral ((Patch.refl (literalProgram (computeControl (indexedStepProductionRegisters.phase1 :: indexedStepProductionRegisters.lengthRPrime) (2^(indexedStepProductionRegisters.lengthRPrime.length+1)-2) indexedStepProductionRegisters.terminal indexedStepProductionRegisters.blockScratch) : Straight n start start)).joinLiteral (Patch.refl (literalProgram List.nil : Straight n start start))))))))))))))))))

def fSource : Circuit := blockFForward indexedStepProductionRegisters
def fPatch (n start : Nat) : Patch (literalProgram (fSource) : Straight n start start) 35 := by
  simpa only [fSource, blockFForward, postShift_expand, shiftedLiteral, shiftFlags, List.append_assoc, List.append_nil, circuit_adjoint_append] using ((Patch.refl (literalProgram (controlledRotateLeftOne indexedStepProductionRegisters.postShift.phase1 indexedStepProductionRegisters.postShift.work) : Straight n start start)).joinLiteral ((smallPatch n start 7 (controlledIncrement indexedStepProductionRegisters.postShift.phase1 indexedStepProductionRegisters.postShift.lengthS indexedStepProductionRegisters.postShift.carries) (by unfold CircuitWellFormed; decide +kernel) (by decide +kernel)).joinLiteral ((Patch.refl (literalProgram (([.CCX indexedStepProductionRegisters.postShift.phase1 indexedStepProductionRegisters.postShift.phase2 indexedStepProductionRegisters.postShift.both] : Circuit)) : Straight n start start)).joinLiteral ((Patch.refl (literalProgram (controlledRotateRightTwo indexedStepProductionRegisters.postShift.both indexedStepProductionRegisters.postShift.work) : Straight n start start)).joinLiteral ((smallPatch n start 28 ((controlledDecrement indexedStepProductionRegisters.postShift.both indexedStepProductionRegisters.postShift.lengthS indexedStepProductionRegisters.postShift.carries ++ controlledDecrement indexedStepProductionRegisters.postShift.both indexedStepProductionRegisters.postShift.lengthS indexedStepProductionRegisters.postShift.carries)) (by unfold CircuitWellFormed; decide +kernel) (by decide +kernel)).joinLiteral ((Patch.refl (literalProgram (([.CCX indexedStepProductionRegisters.postShift.phase1 indexedStepProductionRegisters.postShift.phase2 indexedStepProductionRegisters.postShift.both] : Circuit)) : Straight n start start)).joinLiteral (Patch.refl (literalProgram List.nil : Straight n start start))))))))

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def b2Source : Circuit := blockB2 indexedStepProductionRegisters
private theorem b2_wellFormed : CircuitWellFormed b2Source := by
  unfold CircuitWellFormed
  decide +kernel
private theorem b2_counts : ShorECDLP.tCount b2Source = 462 ∧
    ShorECDLP.tCount (Cancellation.optimize b2Source) = 238 := by
  decide +kernel

def b2Patch (n start : Nat) : Patch (literalProgram b2Source : Straight n start start) 224 := by
  apply Patch.literal _ (Cancellation.optimize b2Source)
  · exact Cancellation.optimize_sublist b2Source
  · exact (Cancellation.optimize_run b2Source b2_wellFormed).symm
  · have h := b2_counts
    omega

def remainderPatch (n start width : Nat) (w : ActiveWindow) :
    Patch (remainderBlockProgram n start indexedStepProductionRegisters width w).2 224 := by
  unfold remainderBlockProgram remainderBlockSegments
  refine (Patch.sequenceCons (d := 0) (f := 224) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 224) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 224) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := 224) (f := 0) _ _ (b2Patch n _) (Patch.refl _)).castSaving (by omega)

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def b1Source : Circuit :=
  let r := indexedStepProductionRegisters
  rControlNonterminal [r.phase1] 0 r.control r.lengthRPrime r.terminal r.blockScratch
private theorem b1_wellFormed : CircuitWellFormed b1Source := by
  unfold CircuitWellFormed
  decide +kernel
private theorem b1_counts : ShorECDLP.tCount b1Source = 217 ∧
    ShorECDLP.tCount (Cancellation.optimize b1Source) = 119 := by decide +kernel

def b1Patch (n start : Nat) : Patch (literalProgram b1Source : Straight n start start) 98 := by
  apply Patch.literal _ (Cancellation.optimize b1Source)
  · exact Cancellation.optimize_sublist b1Source
  · exact (Cancellation.optimize_run b1Source b1_wellFormed).symm
  · have h := b1_counts; omega

def optimizedLiteralPatch (n s d : Nat) (xs : Circuit)
    (hw : CircuitWellFormed xs)
    (ht : ShorECDLP.tCount (Cancellation.optimize xs) + d = ShorECDLP.tCount xs) :
    Patch (literalProgram xs : Straight n s s) d :=
  Patch.literal xs (Cancellation.optimize xs) (Cancellation.optimize_sublist xs)
    (Cancellation.optimize_run xs hw).symm ht

private theorem straight_append_assoc {n a b c d : Nat} (p : Straight n a b) (q : Straight n b c)
    (r : Straight n c d) : (p.append q).append r = p.append (q.append r) := by
  induction p with
  | done => rfl
  | gate g next ih => simp only [Straight.append, ih]
  | recordGate i v g next ih => simp only [Straight.append, ih]
  | measure w next ih => simp only [Straight.append, ih]

private theorem literal_append_cast {n s e f : Nat} (xs ys : Circuit) (R : Straight n s e) (h : e = f) :
    (literalProgram xs : Straight n s s).append (castFinish h ((literalProgram ys : Straight n s s).append R)) =
      castFinish h ((literalProgram (xs ++ ys) : Straight n s s).append R) := by
  subst h
  show (literalProgram xs : Straight n s s).append ((literalProgram ys : Straight n s s).append R) =
    (literalProgram (xs ++ ys) : Straight n s s).append R
  rw [literal_append, straight_append_assoc]

/-- Two adjacent literal segments are optimized as one literal. -/
def Patch.literalPair {n start d f} (xs ys : Circuit) (tail : List (FixedSegment n))
    (hp : Patch (literalProgram (xs ++ ys) : Straight n start start) d)
    (hq : Patch (sequenceProgram n tail start).2 f) :
    Patch (sequenceProgram n ((fun _ => ⟨0, literalProgram xs⟩) ::
      (fun _ => ⟨0, literalProgram ys⟩) :: tail) start).2 (d+f) := by
  rw [sequenceProgram, sequenceProgram]
  unfold Paper2607_13816.ChallengeMigration.appendCompiled
  dsimp only
  rw [literal_append_cast]
  exact ((hp.append hq).castFinish _).castFinish _

private theorem b12_wellFormed : CircuitWellFormed (b1Source ++ b2Source) := by
  unfold CircuitWellFormed
  decide +kernel
private theorem b12_saving : ShorECDLP.tCount (Cancellation.optimize (b1Source ++ b2Source)) + 434 =
    ShorECDLP.tCount (b1Source ++ b2Source) := by decide +kernel

def b12Patch (n start : Nat) : Patch (literalProgram (b1Source ++ b2Source) : Straight n start start) 434 :=
  Patch.literal _ (Cancellation.optimize (b1Source ++ b2Source)) (Cancellation.optimize_sublist _)
    (Cancellation.optimize_run _ b12_wellFormed).symm b12_saving

/-! Fixed endpoint arithmetic around each remainder interval.  The offset-dependent
constant updates stay verbatim; only the window-independent prefix and suffix are reduced. -/

def endpointPrefix (lT lQ lS sc : List Wire) (c : Wire) : Circuit :=
  cuccaroAdd lT lQ c ++ (addConstant lQ (endpointScratch lQ sc) c 4 ++
    constMinus lS (endpointScratch lS sc) c (256 + 2))

def endpointSuffix (lT lQ lS sc : List Wire) (c : Wire) : Circuit :=
  constMinus lS (endpointScratch lS sc) c (256 + 2) ++
    (subConstant lQ (endpointScratch lQ sc) c 4 ++ cuccaroSub lT lQ c)

/-- Exact cancellation facts for the fixed endpoint arithmetic and the four offset-adder cores. -/
def EndpointFacts (lT lQ lS sc : List Wire) (c : Wire) : Prop :=
  (CircuitWellFormed (endpointPrefix lT lQ lS sc c) ∧
    ShorECDLP.tCount (Cancellation.optimize (endpointPrefix lT lQ lS sc c)) + 42 =
      ShorECDLP.tCount (endpointPrefix lT lQ lS sc c)) ∧
  (CircuitWellFormed (endpointSuffix lT lQ lS sc c) ∧
    ShorECDLP.tCount (Cancellation.optimize (endpointSuffix lT lQ lS sc c)) + 42 =
      ShorECDLP.tCount (endpointSuffix lT lQ lS sc c)) ∧
  (CircuitWellFormed (cuccaroSub (endpointScratch lQ sc) lQ c) ∧
    ShorECDLP.tCount (Cancellation.optimize (cuccaroSub (endpointScratch lQ sc) lQ c)) + 14 =
      ShorECDLP.tCount (cuccaroSub (endpointScratch lQ sc) lQ c)) ∧
  (CircuitWellFormed (cuccaroSub (endpointScratch lS sc) lS c) ∧
    ShorECDLP.tCount (Cancellation.optimize (cuccaroSub (endpointScratch lS sc) lS c)) + 14 =
      ShorECDLP.tCount (cuccaroSub (endpointScratch lS sc) lS c)) ∧
  (CircuitWellFormed (cuccaroAdd (endpointScratch lS sc) lS c) ∧
    ShorECDLP.tCount (Cancellation.optimize (cuccaroAdd (endpointScratch lS sc) lS c)) + 14 =
      ShorECDLP.tCount (cuccaroAdd (endpointScratch lS sc) lS c)) ∧
  (CircuitWellFormed (cuccaroAdd (endpointScratch lQ sc) lQ c) ∧
    ShorECDLP.tCount (Cancellation.optimize (cuccaroAdd (endpointScratch lQ sc) lQ c)) + 14 =
      ShorECDLP.tCount (cuccaroAdd (endpointScratch lQ sc) lQ c))

private theorem endpoint_facts : ∀ c ∈ List.range' 568 10,
    EndpointFacts (List.range' 522 9) (List.range' 531 9) (List.range' 540 9) (List.range' 559 9) c := by
  unfold EndpointFacts CircuitWellFormed
  decide +kernel

def subConstantPatch (n s : Nat) (register constants : List Wire) (c : Wire) (k : Nat)
    (hw : CircuitWellFormed (cuccaroSub constants register c))
    (ht : ShorECDLP.tCount (Cancellation.optimize (cuccaroSub constants register c)) + 14 =
      ShorECDLP.tCount (cuccaroSub constants register c)) :
    Patch (literalProgram (subConstant register constants c k) : Straight n s s) 14 := by
  unfold subConstant
  exact (((Patch.refl _).joinLiteral (optimizedLiteralPatch n s 14 _ hw ht)).joinLiteral
    (Patch.refl _)).castSaving (by omega)

def addConstantPatch (n s : Nat) (register constants : List Wire) (c : Wire) (k : Nat)
    (hw : CircuitWellFormed (cuccaroAdd constants register c))
    (ht : ShorECDLP.tCount (Cancellation.optimize (cuccaroAdd constants register c)) + 14 =
      ShorECDLP.tCount (cuccaroAdd constants register c)) :
    Patch (literalProgram (addConstant register constants c k) : Straight n s s) 14 := by
  unfold addConstant
  exact (((Patch.refl _).joinLiteral (optimizedLiteralPatch n s 14 _ hw ht)).joinLiteral
    (Patch.refl _)).castSaving (by omega)

def prepareEndpointPatch (n s : Nat) (lT lQ lS sc : List Wire) (c : Wire) (k : Nat)
    (h : EndpointFacts lT lQ lS sc c) :
    Patch (literalProgram (prepareIntervalEndpoints lT lQ lS sc c 256 k) : Straight n s s) 70 := by
  have he : prepareIntervalEndpoints lT lQ lS sc c 256 k = endpointPrefix lT lQ lS sc c ++
      (subConstant lQ (endpointScratch lQ sc) c k ++ subConstant lS (endpointScratch lS sc) c k) := by
    simp only [prepareIntervalEndpoints, endpointPrefix, List.append_assoc]
  rw [he]
  exact ((optimizedLiteralPatch n s 42 _ h.1.1 h.1.2).joinLiteral
    ((subConstantPatch n s _ _ c k h.2.2.1.1 h.2.2.1.2).joinLiteral
      (subConstantPatch n s _ _ c k h.2.2.2.1.1 h.2.2.2.1.2))).castSaving (by omega)

def restoreEndpointPatch (n s : Nat) (lT lQ lS sc : List Wire) (c : Wire) (k : Nat)
    (h : EndpointFacts lT lQ lS sc c) :
    Patch (literalProgram (restoreIntervalEndpoints lT lQ lS sc c 256 k) : Straight n s s) 70 := by
  have he : restoreIntervalEndpoints lT lQ lS sc c 256 k =
      (addConstant lS (endpointScratch lS sc) c k ++ addConstant lQ (endpointScratch lQ sc) c k) ++
        endpointSuffix lT lQ lS sc c := by
    simp only [restoreIntervalEndpoints, endpointSuffix, List.append_assoc]
  rw [he]
  exact (((addConstantPatch n s _ _ c k h.2.2.2.2.1.1 h.2.2.2.2.1.2).joinLiteral
      (addConstantPatch n s _ _ c k h.2.2.2.2.2.1 h.2.2.2.2.2.2)).joinLiteral
    (optimizedLiteralPatch n s 42 _ h.2.1.1 h.2.1.2)).castSaving (by omega)

def Patch.prependLiteral {n start d f} (gs : Circuit)
    (p : (count : Nat) × Straight n start (start+count))
    (hg : Patch (literalProgram gs : Straight n start start) d) (hp : Patch p.2 f) :
    Patch (Paper2607_13816.ChallengeMigration.prependCompiled gs p).2 (d+f) := by
  unfold Paper2607_13816.ChallengeMigration.prependCompiled
  exact hg.append hp

def intervalEndpointPatch (n start : Nat) (r : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget)
    (h : EndpointFacts r.lengthT r.lengthQ r.lengthS r.endpointScratch (r.carry k K)) :
    Patch (intervalProgram n start r 256 k K mode signUpdate target).2 140 := by
  unfold intervalProgram
  refine (Patch.prependLiteral (d := 70) (f := 70) _ _
    (prepareEndpointPatch n _ _ _ _ _ _ k h) ?_).castSaving (by omega)
  refine (Patch.appendCompiled (d := 0) (f := 70) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.appendCompiled (d := 0) (f := 70) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine Patch.prependCompiled _ _ ?_
  refine (Patch.appendCompiled (d := 0) (f := 70) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.appendCompiled (d := 0) (f := 70) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact restoreEndpointPatch n _ _ _ _ _ _ k h

private theorem mainLabel_lt_laneCount
    {k K label : Nat} (hlabel : label ∈ (intervalMainLabels k K).toFinset) :
    label < intervalLaneCount k K := by
  have hmain : label ∈ intervalMainLabels k K := by simpa using hlabel
  by_cases hspecial : intervalHasTopSpecial k K = true
  · simp [intervalMainLabels, hspecial] at hmain
    omega
  · simpa [intervalMainLabels, hspecial] using hmain

private theorem remainderTreeDepth_le_nine
    (registers : IntervalRegisters) {k K : Nat}
    (hcount : intervalLaneCount k K ≤ 259) :
    intervalTreeDepth registers k K ≤ 9 := by
  have hwidth : DualUnaryActionTree.sourceWidth (intervalMainLabels k K).toFinset ≤ 9 := by
    apply DualUnaryActionTree.sourceWidth_le _ 9 (by decide)
    intro label hlabel
    have hlt := mainLabel_lt_laneCount hlabel
    norm_num
    omega
  exact (DualUnaryActionTree.buildSource_pathDepth_le
    registers.rightIndex registers.leftIndex
    (intervalMainLabels k K).toFinset (intervalTree registers k K) (by
      simpa [DualUnaryActionTree.buildSourceFromList] using
        intervalTree_built registers k K)).trans hwidth

private theorem endpoint_base_cases : ∀ b, 9 ≤ b → b ≤ 18 →
    ((List.range' 559 21).take (b+3)).getD b 0 ∈ List.range' 568 10 ∧
      ((List.range' 559 21).take (b+3)).take 9 = List.range' 559 9 := by
  intro b h1 h2
  interval_cases b <;> decide

private theorem remainder_endpoint_facts (w : ActiveWindow)
    (hw : intervalLaneCount w.start w.stop ≤ 259) :
    (indexedStepProductionRegisters.remainder w).carry w.start w.stop ∈ List.range' 568 10 ∧
      (indexedStepProductionRegisters.remainder w).endpointScratch = List.range' 559 9 := by
  have hd := remainderTreeDepth_le_nine (indexedStepProductionRegisters.remainder w) hw
  have hb1 : 9 ≤ intervalScratchBase (indexedStepProductionRegisters.remainder w) w.start w.stop := by
    change 9 ≤ max (2 * intervalTreeDepth (indexedStepProductionRegisters.remainder w) w.start w.stop) (max 9 9)
    omega
  have hb2 : intervalScratchBase (indexedStepProductionRegisters.remainder w) w.start w.stop ≤ 18 := by
    change max (2 * intervalTreeDepth (indexedStepProductionRegisters.remainder w) w.start w.stop) (max 9 9) ≤ 18
    omega
  have hcarry : (indexedStepProductionRegisters.remainder w).carry w.start w.stop =
      ((List.range' 559 21).take (intervalScratchBase (indexedStepProductionRegisters.remainder w)
        w.start w.stop + 3)).getD (intervalScratchBase (indexedStepProductionRegisters.remainder w)
          w.start w.stop) 0 := rfl
  have hscratch : (indexedStepProductionRegisters.remainder w).endpointScratch =
      ((List.range' 559 21).take (intervalScratchBase (indexedStepProductionRegisters.remainder w)
        w.start w.stop + 3)).take 9 := rfl
  rw [hcarry, hscratch]
  exact endpoint_base_cases _ hb1 hb2

def remainderIntervalPatch (n start : Nat) (w : ActiveWindow)
    (hw : intervalLaneCount w.start w.stop ≤ 259)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget) :
    Patch (intervalProgram n start (indexedStepProductionRegisters.remainder w) 256 w.start w.stop
      mode signUpdate target).2 140 := by
  have hf := remainder_endpoint_facts w hw
  have hs := endpoint_facts _ hf.1
  have hT : (indexedStepProductionRegisters.remainder w).lengthT = List.range' 522 9 := rfl
  have hQ : (indexedStepProductionRegisters.remainder w).lengthQ = List.range' 531 9 := rfl
  have hS : (indexedStepProductionRegisters.remainder w).lengthS = List.range' 540 9 := rfl
  rw [← hT, ← hQ, ← hS, ← hf.2] at hs
  exact intervalEndpointPatch n start _ _ _ mode signUpdate target hs

theorem certified_remainder_count (T : Nat) :
    intervalLaneCount (certifiedActiveWindows 256 T).remainder.start
      (certifiedActiveWindows 256 T).remainder.stop ≤ 259 := by
  simp only [certifiedActiveWindows, certifiedRemainderWindow, intervalLaneCount]
  omega

def remainderPatchAll (n start : Nat) (w : ActiveWindow) (hw : intervalLaneCount w.start w.stop ≤ 259) :
    Patch (remainderBlockProgram n start indexedStepProductionRegisters 256 w).2 812 := by
  unfold remainderBlockProgram remainderBlockSegments
  refine (Patch.sequenceCons (d := 98) (f := 714) _ _ (b1Patch n _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 140) (f := 574) _ _ (remainderIntervalPatch n _ w hw _ _ _) ?_).castSaving (by omega)
  refine (Patch.literalPair (d := 434) (f := 140) b1Source b2Source _ (b12Patch n _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 140) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := 140) (f := 0) _ _ (remainderIntervalPatch n _ w hw _ _ _) (Patch.refl _)).castSaving (by omega)

section CrossBoundary
attribute [local semireducible] sequenceProgram appendCompiled literalProgram intervalProgram
  remainderBlockProgram intervalInverseProgram

inductive FlatOp (n : Nat) where
  | gate (g : TemplateGate n)
  | record (i : Nat) (v : Bool) (g : Gate)
  | measure (w : Wire)

def flat {n s e : Nat} : Straight n s e → List (FlatOp n)
  | .done => []
  | .gate g p => .gate g :: flat p
  | .recordGate i v g p => .record i.val v g :: flat p
  | .measure w p => .measure w :: flat p

theorem flat_inj {n : Nat} : ∀ {s e : Nat} (p q : Straight n s e), flat p = flat q → p = q := by
  intro s e p
  induction p with
  | done => intro q h; cases q <;> simp_all [flat]
  | gate g p ih =>
    intro q h
    cases q <;> simp only [flat, List.cons.injEq, reduceCtorEq, false_and, FlatOp.gate.injEq] at h
    rcases h with ⟨rfl, h⟩
    rw [ih _ h]
  | recordGate i v g p ih =>
    intro q h
    cases q <;> simp only [flat, List.cons.injEq, reduceCtorEq, false_and, FlatOp.record.injEq] at h
    rcases h with ⟨⟨hi, rfl, rfl⟩, h⟩
    rw [Fin.ext hi, ih _ h]
  | measure w p ih =>
    intro q h
    cases q <;> simp only [flat, List.cons.injEq, reduceCtorEq, false_and, FlatOp.measure.injEq] at h
    rcases h with ⟨rfl, h⟩
    rw [ih _ h]

theorem flat_append {n a b c : Nat} (p : Straight n a b) (q : Straight n b c) :
    flat (p.append q) = flat p ++ flat q := by
  induction p with
  | done => rfl
  | gate g p ih => simp [Straight.append, flat, ih]
  | recordGate i v g p ih => simp [Straight.append, flat, ih]
  | measure w p ih => simp [Straight.append, flat, ih]

theorem flat_castFinish {n s e f : Nat} (h : e = f) (p : Straight n s e) :
    flat (castFinish h p) = flat p := by
  subst h
  rfl

theorem flat_literal {n s : Nat} (xs : Circuit) :
    flat (literalProgram xs : Straight n s s) = xs.map (fun g => FlatOp.gate (.literal g)) := by
  induction xs with
  | nil => rfl
  | cons g xs ih =>
    change FlatOp.gate (.literal g) :: flat (literalProgram xs : Straight n s s) = _
    rw [ih]; rfl

theorem flat_done {n s : Nat} : flat (Straight.done : Straight n s s) = [] := rfl

def Patch.congr {n s e d} {p q : Straight n s e} (hp : Patch p d) (h : p = q) : Patch q d := h ▸ hp

def intervalCore (n start : Nat) (r : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget) :
    (count : Nat) × Straight n start (start+count) :=
  let top1 := intervalTopFirstProgram n start r k K mode target
  let pass1 := traversalFirstProgram n (start+top1.1) mode (intervalHasTopSpecial k K) (r.rightTop k K) (r.leftTop k K) (r.accumulator k K) (r.carry k K) (r.cellScratch k K) (r.targetAt target) (r.addendAt target) (intervalTree r k K) r.control r.control (r.rightPaths k K) (r.leftPaths k K)
  let pass2 := traversalSecondProgram n (start+top1.1+pass1.1) mode (intervalHasTopSpecial k K) (r.rightTop k K) (r.leftTop k K) (r.accumulator k K) (r.carry k K) (r.cellScratch k K) (r.targetAt target) (r.addendAt target) (intervalTree r k K) r.control r.control (r.rightPaths k K) (r.leftPaths k K)
  let top2 := intervalTopSecondProgram n (start+top1.1+pass1.1+pass2.1) r k K mode target
  appendCompiled top1 (appendCompiled pass1 (prependCompiled (intervalSignUpdate r k K signUpdate)
    (appendCompiled pass2 top2)))

theorem interval_flat (n start : Nat) (r : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget) :
    flat (intervalProgram n start r 256 k K mode signUpdate target).2 =
      flat (literalProgram (prepareIntervalEndpoints r.lengthT r.lengthQ r.lengthS r.endpointScratch (r.carry k K) 256 k) : Straight n start start) ++
      flat (intervalCore n start r k K mode signUpdate target).2 ++
      flat (literalProgram (restoreIntervalEndpoints r.lengthT r.lengthQ r.lengthS r.endpointScratch (r.carry k K) 256 k) : Straight n (start + (intervalCore n start r k K mode signUpdate target).1) _) := by
  unfold intervalProgram intervalCore
  simp only [prependCompiled, appendCompiled, flat_append, flat_castFinish, flat_literal, List.append_assoc]

theorem interval_count (n start : Nat) (r : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget) :
    (intervalProgram n start r 256 k K mode signUpdate target).1 =
      (intervalCore n start r k K mode signUpdate target).1 := rfl


/-- Cross-boundary core: endpoint suffix of one remainder interval, the fixed middle literals,
and the endpoint prefix of the next interval, as one literal. -/
def crossCore (M : Circuit) (c : Wire) : Circuit :=
  endpointSuffix (List.range' 522 9) (List.range' 531 9) (List.range' 540 9) (List.range' 559 9) c ++ M ++
    endpointPrefix (List.range' 522 9) (List.range' 531 9) (List.range' 540 9) (List.range' 559 9) c

def CrossFacts (M : Circuit) (c : Wire) : Prop :=
  CircuitWellFormed (crossCore M c) ∧
    ShorECDLP.tCount (Cancellation.optimize (crossCore M c)) + 756 = ShorECDLP.tCount (crossCore M c)

def b3Source : Circuit :=
  let r := indexedStepProductionRegisters
  ([.CCX r.phase2 r.sign r.terminal] ++ rControlNonterminal [r.phase1,r.terminal] 0 r.control r.lengthRPrime (r.blockScratch.getD 0 0) (r.blockScratch.drop 1)) ++ [.CCX r.phase2 r.sign r.terminal]

def forwardMiddle : Circuit := (b1Source ++ b2Source) ++ b3Source

theorem forward_cross_facts : ∀ c ∈ List.range' 569 9, CrossFacts forwardMiddle c := by
  unfold CrossFacts CircuitWellFormed
  decide +kernel


/-- Patch of the merged boundary literal `restore ++ M ++ prepare`. -/
def crossLiteralPatch (n s : Nat) (M : Circuit) (c : Wire) (k : Nat)
    (h : EndpointFacts (List.range' 522 9) (List.range' 531 9) (List.range' 540 9) (List.range' 559 9) c)
    (hx : CrossFacts M c) :
    Patch (literalProgram (restoreIntervalEndpoints (List.range' 522 9) (List.range' 531 9) (List.range' 540 9)
        (List.range' 559 9) c 256 k ++ M ++ prepareIntervalEndpoints (List.range' 522 9) (List.range' 531 9)
        (List.range' 540 9) (List.range' 559 9) c 256 k) : Straight n s s) 812 := by
  have he : restoreIntervalEndpoints (List.range' 522 9) (List.range' 531 9) (List.range' 540 9)
        (List.range' 559 9) c 256 k ++ M ++ prepareIntervalEndpoints (List.range' 522 9) (List.range' 531 9)
        (List.range' 540 9) (List.range' 559 9) c 256 k =
      (addConstant (List.range' 540 9) (endpointScratch (List.range' 540 9) (List.range' 559 9)) c k ++
        addConstant (List.range' 531 9) (endpointScratch (List.range' 531 9) (List.range' 559 9)) c k) ++
      (crossCore M c ++
      (subConstant (List.range' 531 9) (endpointScratch (List.range' 531 9) (List.range' 559 9)) c k ++
        subConstant (List.range' 540 9) (endpointScratch (List.range' 540 9) (List.range' 559 9)) c k)) := by
    simp only [restoreIntervalEndpoints, prepareIntervalEndpoints, crossCore, endpointSuffix,
      endpointPrefix, List.append_assoc]
  rw [he]
  exact (((addConstantPatch n s _ _ c k h.2.2.2.2.1.1 h.2.2.2.2.1.2).joinLiteral
      (addConstantPatch n s _ _ c k h.2.2.2.2.2.1 h.2.2.2.2.2.2)).joinLiteral
    ((optimizedLiteralPatch n s 756 _ hx.1 hx.2).joinLiteral
      ((subConstantPatch n s _ _ c k h.2.2.1.1 h.2.2.1.2).joinLiteral
        (subConstantPatch n s _ _ c k h.2.2.2.1.1 h.2.2.2.1.2)))).castSaving (by omega)


def remainderCrossPatch (n start : Nat) (w : ActiveWindow)
    (h : EndpointFacts (List.range' 522 9) (List.range' 531 9) (List.range' 540 9) (List.range' 559 9)
      ((indexedStepProductionRegisters.remainder w).carry w.start w.stop))
    (hx : CrossFacts forwardMiddle ((indexedStepProductionRegisters.remainder w).carry w.start w.stop))
    (hE : (indexedStepProductionRegisters.remainder w).endpointScratch = List.range' 559 9) :
    Patch (remainderBlockProgram n start indexedStepProductionRegisters 256 w).2 1050 := by
  let rg := indexedStepProductionRegisters.remainder w
  have hT : rg.lengthT = List.range' 522 9 := rfl
  have hQ : rg.lengthQ = List.range' 531 9 := rfl
  have hS : rg.lengthS = List.range' 540 9 := rfl
  let c := rg.carry w.start w.stop
  let core1 := intervalCore n start rg w.start w.stop .sub true .work1
  let core2 := intervalCore n (start + core1.1) rg w.start w.stop .add false .work1
  let P := prepareIntervalEndpoints (List.range' 522 9) (List.range' 531 9) (List.range' 540 9) (List.range' 559 9) c 256 w.start
  let R := restoreIntervalEndpoints (List.range' 522 9) (List.range' 531 9) (List.range' 540 9) (List.range' 559 9) c 256 w.start
  let X : Straight n start (start + core1.1 + core2.1) :=
    (literalProgram (b1Source ++ P)).append (core1.2.append
      ((literalProgram (R ++ forwardMiddle ++ P)).append (core2.2.append (literalProgram (R ++ b3Source)))))
  have hX : Patch X 1050 :=
    (((b1Patch n start).joinLiteral (prepareEndpointPatch n start _ _ _ _ c w.start h)).append
      ((Patch.refl core1.2).append ((crossLiteralPatch n _ forwardMiddle c w.start h hx).append
        ((Patch.refl core2.2).append ((restoreEndpointPatch n _ _ _ _ _ c w.start h).joinLiteral
          (Patch.refl (literalProgram b3Source))))))).castSaving (by omega)
  have hcount : start + core1.1 + core2.1 = start + (remainderBlockProgram n start indexedStepProductionRegisters 256 w).1 := by
    unfold remainderBlockProgram remainderBlockSegments
    simp only [sequenceProgram, appendCompiled, interval_count, Nat.add_zero, core1, core2, rg]
    omega
  refine (hX.castFinish hcount).congr ?_
  apply flat_inj
  unfold remainderBlockProgram remainderBlockSegments
  simp only [sequenceProgram, appendCompiled, flat_castFinish, flat_append, interval_flat, flat_literal,
    X, List.map_append, List.append_assoc, flat_done, List.append_nil, Nat.add_zero, core1, core2, rg, hE, P, R, c,
    b1Source, b2Source, b3Source, forwardMiddle]
  have hT' : (indexedStepProductionRegisters.remainder w).lengthT = List.range' 522 9 := rfl
  have hQ' : (indexedStepProductionRegisters.remainder w).lengthQ = List.range' 531 9 := rfl
  have hS' : (indexedStepProductionRegisters.remainder w).lengthS = List.range' 540 9 := rfl
  simp only [hT', hQ', hS']
  rfl


def reverseMiddle : Circuit := b3Source ++ b2Source ++ b1Source

theorem reverse_cross_facts : ∀ c ∈ List.range' 569 9, CrossFacts reverseMiddle c := by
  unfold CrossFacts CircuitWellFormed
  decide +kernel

def reverseCombinedSource (T : Nat) : Circuit :=
  let r := indexedStepProductionRegisters
  computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++ computeControl [r.phase1,r.terminal] 1 r.control r.blockScratch ++ computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++ restoreLatestPaperTBoundary r.tBoundary 256 ++ blockDInverse r (certifiedActiveWindows 256 T).quotientSwap ++ blockCInverse r ++ (([.CCX r.phase2 r.sign r.terminal] ++ rControlNonterminal [r.phase1,r.terminal] 0 r.control r.lengthRPrime (r.blockScratch.getD 0 0) (r.blockScratch.drop 1)) ++ [.CCX r.phase2 r.sign r.terminal])

def reverseEndSource : Circuit :=
  let r := indexedStepProductionRegisters
  rControlNonterminal [r.phase1] 0 r.control r.lengthRPrime r.terminal r.blockScratch ++ blockAInverse r

def reverseTailCrossPatch (n start : Nat) (w : ActiveWindow) (C E : Circuit) {dC dE : Nat}
    (h : EndpointFacts (List.range' 522 9) (List.range' 531 9) (List.range' 540 9) (List.range' 559 9)
      ((indexedStepProductionRegisters.remainder w).carry w.start w.stop))
    (hx : CrossFacts reverseMiddle ((indexedStepProductionRegisters.remainder w).carry w.start w.stop))
    (hE : (indexedStepProductionRegisters.remainder w).endpointScratch = List.range' 559 9)
    (hC : Patch (literalProgram C : Straight n start start) dC)
    (hEnd : ∀ s, Patch (literalProgram E : Straight n s s) dE) :
    Patch (sequenceProgram n
      ([(fun _ => ⟨0, literalProgram C⟩),
       (fun cursor => intervalInverseProgram n cursor (indexedStepProductionRegisters.remainder w) 256 w.start w.stop .add false .work1),
       (fun _ => ⟨0, literalProgram reverseMiddle⟩),
       (fun cursor => intervalInverseProgram n cursor (indexedStepProductionRegisters.remainder w) 256 w.start w.stop .sub true .work1),
       (fun _ => ⟨0, literalProgram E⟩)] : List (FixedSegment n)) start).2 (dC + 952 + dE) := by
  let rg := indexedStepProductionRegisters.remainder w
  let c := rg.carry w.start w.stop
  let core1 := intervalCore n start rg w.start w.stop RippleMode.add.inverse false .work1
  let core2 := intervalCore n (start + core1.1) rg w.start w.stop RippleMode.sub.inverse true .work1
  let P := prepareIntervalEndpoints (List.range' 522 9) (List.range' 531 9) (List.range' 540 9) (List.range' 559 9) c 256 w.start
  let R := restoreIntervalEndpoints (List.range' 522 9) (List.range' 531 9) (List.range' 540 9) (List.range' 559 9) c 256 w.start
  let X : Straight n start (start + core1.1 + core2.1) :=
    (literalProgram (C ++ P)).append (core1.2.append
      ((literalProgram (R ++ reverseMiddle ++ P)).append (core2.2.append (literalProgram (R ++ E)))))
  have hX : Patch X (dC + 952 + dE) :=
    ((hC.joinLiteral (prepareEndpointPatch n start _ _ _ _ c w.start h)).append
      ((Patch.refl core1.2).append ((crossLiteralPatch n _ reverseMiddle c w.start h hx).append
        ((Patch.refl core2.2).append ((restoreEndpointPatch n _ _ _ _ _ c w.start h).joinLiteral
          (hEnd _)))))).castSaving (by omega)
  have hcount : start + core1.1 + core2.1 = start + (sequenceProgram n
      ([(fun _ => ⟨0, literalProgram C⟩),
       (fun cursor => intervalInverseProgram n cursor rg 256 w.start w.stop .add false .work1),
       (fun _ => ⟨0, literalProgram reverseMiddle⟩),
       (fun cursor => intervalInverseProgram n cursor rg 256 w.start w.stop .sub true .work1),
       (fun _ => ⟨0, literalProgram E⟩)] : List (FixedSegment n)) start).1 := by
    simp only [sequenceProgram, appendCompiled, intervalInverseProgram, interval_count, Nat.add_zero, core1, core2, rg]
    omega
  refine (hX.castFinish hcount).congr ?_
  apply flat_inj
  have hT' : rg.lengthT = List.range' 522 9 := rfl
  have hQ' : rg.lengthQ = List.range' 531 9 := rfl
  have hS' : rg.lengthS = List.range' 540 9 := rfl
  simp only [sequenceProgram, appendCompiled, intervalInverseProgram, flat_castFinish, flat_append, interval_flat,
    flat_literal, X, List.map_append, List.append_assoc, flat_done, List.append_nil, Nat.add_zero, core1, core2,
    P, R, c, hT', hQ', hS', hE, rg]
  rfl


private theorem lanes_large : ∀ T < 1542, 18 ≤ intervalLaneCount (certifiedActiveWindows 256 T).remainder.start
    (certifiedActiveWindows 256 T).remainder.stop := by
  decide +kernel

private theorem labels_le (t : DualUnaryActionTree) : t.labels.length ≤ 2 ^ t.pathDepth := by
  induction t with
  | leaf => simp [DualUnaryActionTree.labels, DualUnaryActionTree.pathDepth]
  | node a b z o ihz iho =>
    simp only [DualUnaryActionTree.labels, DualUnaryActionTree.pathDepth, List.length_append]
    have hz : 2 ^ z.pathDepth ≤ 2 ^ max z.pathDepth o.pathDepth := Nat.pow_le_pow_right (by omega) (le_max_left _ _)
    have ho : 2 ^ o.pathDepth ≤ 2 ^ max z.pathDepth o.pathDepth := Nat.pow_le_pow_right (by omega) (le_max_right _ _)
    rw [Nat.add_comm 1, pow_succ]
    omega

private theorem carry_base_cases : ∀ b, 10 ≤ b → b ≤ 18 →
    ((List.range' 559 21).take (b+3)).getD b 0 ∈ List.range' 569 9 := by
  intro b h1 h2
  interval_cases b <;> decide

private theorem mainLabels_length (k K : Nat) : intervalLaneCount k K - 1 ≤ (intervalMainLabels k K).toFinset.card := by
  unfold intervalMainLabels
  split <;> simp [List.toFinset_range]

theorem remainder_carry_large (T : Nat) (hT : T < 1542) :
    (indexedStepProductionRegisters.remainder (certifiedActiveWindows 256 T).remainder).carry
      (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop
      ∈ List.range' 569 9 := by
  set w := (certifiedActiveWindows 256 T).remainder
  set rg := indexedStepProductionRegisters.remainder w
  have hl : 18 ≤ intervalLaneCount w.start w.stop := lanes_large T hT
  have hw : intervalLaneCount w.start w.stop ≤ 259 := by
    simp only [w, certifiedActiveWindows, certifiedRemainderWindow, intervalLaneCount]
    omega
  have hlab := labels_le (intervalTree rg w.start w.stop)
  rw [intervalTree_labels, Finset.length_sort] at hlab
  have hm := mainLabels_length w.start w.stop
  have hdepth : 5 ≤ intervalTreeDepth rg w.start w.stop := by
    unfold intervalTreeDepth
    by_contra hc
    have : 2 ^ (intervalTree rg w.start w.stop).pathDepth ≤ 2 ^ 4 :=
      Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hd9 : intervalTreeDepth rg w.start w.stop ≤ 9 := by
    have hwidth : DualUnaryActionTree.sourceWidth (intervalMainLabels w.start w.stop).toFinset ≤ 9 := by
      apply DualUnaryActionTree.sourceWidth_le _ 9 (by decide)
      intro label hlabel
      have hmain : label ∈ intervalMainLabels w.start w.stop := by simpa using hlabel
      have hlt : label < intervalLaneCount w.start w.stop := by
        by_cases hspecial : intervalHasTopSpecial w.start w.stop = true
        · simp [intervalMainLabels, hspecial] at hmain; omega
        · simpa [intervalMainLabels, hspecial] using hmain
      norm_num
      omega
    exact (DualUnaryActionTree.buildSource_pathDepth_le rg.rightIndex rg.leftIndex
      (intervalMainLabels w.start w.stop).toFinset (intervalTree rg w.start w.stop) (by
        simpa [DualUnaryActionTree.buildSourceFromList] using intervalTree_built rg w.start w.stop)).trans hwidth
  have hb1 : 10 ≤ intervalScratchBase rg w.start w.stop := by
    change 10 ≤ max (2 * intervalTreeDepth rg w.start w.stop) (max 9 9)
    omega
  have hb2 : intervalScratchBase rg w.start w.stop ≤ 18 := by
    change max (2 * intervalTreeDepth rg w.start w.stop) (max 9 9) ≤ 18
    omega
  have hcarry : rg.carry w.start w.stop =
      ((List.range' 559 21).take (intervalScratchBase rg w.start w.stop + 3)).getD
        (intervalScratchBase rg w.start w.stop) 0 := rfl
  rw [hcarry]
  exact carry_base_cases _ hb1 hb2

end CrossBoundary

/-- All window-independent cross facts for remainder steps before the late schedule. -/
private theorem early_cross_inputs (T : Nat) (hT : T < 1542) :
    let w := (certifiedActiveWindows 256 T).remainder
    EndpointFacts (List.range' 522 9) (List.range' 531 9) (List.range' 540 9) (List.range' 559 9)
        ((indexedStepProductionRegisters.remainder w).carry w.start w.stop) ∧
      CrossFacts forwardMiddle ((indexedStepProductionRegisters.remainder w).carry w.start w.stop) ∧
      CrossFacts reverseMiddle ((indexedStepProductionRegisters.remainder w).carry w.start w.stop) ∧
      (indexedStepProductionRegisters.remainder w).endpointScratch = List.range' 559 9 := by
  intro w
  have hc : (indexedStepProductionRegisters.remainder w).carry w.start w.stop ∈ List.range' 569 9 :=
    remainder_carry_large T hT
  have hc' : (indexedStepProductionRegisters.remainder w).carry w.start w.stop ∈ List.range' 568 10 := by
    simp only [List.mem_range'_1] at hc ⊢
    omega
  exact ⟨endpoint_facts _ hc', forward_cross_facts _ hc, reverse_cross_facts _ hc,
    (remainder_endpoint_facts w (certified_remainder_count T)).2⟩

def ePrepSource : Circuit :=
  let r := indexedStepProductionRegisters
  ((computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++
    computeControl [r.phase1,r.terminal] 1 r.control r.blockScratch) ++
    computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch) ++ prepareLatestPaperTBoundary r.tBoundary 256

def eCleanSource : Circuit :=
  let r := indexedStepProductionRegisters
  computeControl [r.phase1] 1 r.control r.blockScratch ++ restoreLatestPaperTBoundary r.tBoundary 256

private theorem ePrep_wellFormed : CircuitWellFormed ePrepSource := by
  unfold CircuitWellFormed
  decide +kernel
private theorem eClean_wellFormed : CircuitWellFormed eCleanSource := by
  unfold CircuitWellFormed
  decide +kernel
private theorem ePrep_counts : ShorECDLP.tCount ePrepSource = 560 ∧
    ShorECDLP.tCount (Cancellation.optimize ePrepSource) = 518 := by decide +kernel
private theorem eClean_counts : ShorECDLP.tCount eCleanSource = 539 ∧
    ShorECDLP.tCount (Cancellation.optimize eCleanSource) = 497 := by decide +kernel

def ePrepPatch (n start : Nat) : Patch (literalProgram ePrepSource : Straight n start start) 70 :=
  acrossSmallPatch n start 70 ePrepSource (by unfold CircuitWellFormed; decide +kernel) (by decide +kernel)

def eCleanPatch (n start : Nat) : Patch (literalProgram eCleanSource : Straight n start start) 70 :=
  acrossSmallPatch n start 70 eCleanSource (by unfold CircuitWellFormed; decide +kernel) (by decide +kernel)

def coefficientPatch (n start : Nat) (w : ActiveWindow) :
    Patch (coefficientBlockProgram n start indexedStepProductionRegisters 256 w).2 140 := by
  unfold coefficientBlockProgram coefficientBlockSegments
  refine (Patch.sequenceCons (d := 70) (f := 70) _ _ (ePrepPatch n _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 70) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 70) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 70) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := 70) (f := 0) _ _ (eCleanPatch n _) (Patch.refl _)).castSaving (by omega)

def candidateStepPatch (n start T : Nat) :
    Patch (measuredStepProgram n start indexedStepProductionRegisters 256 T).2 (1337+DH32.hSaving T) := by
  unfold measuredStepProgram measuredStepSegments
  refine (Patch.sequenceCons (d := 140) (f := 1197+DH32.hSaving T) _ _ (aPatch n _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 812) (f := 385+DH32.hSaving T) _ _ (remainderPatchAll n _ _ (certified_remainder_count T)) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 210) (f := 175+DH32.hSaving T) _ _ (epochDPatch n _ _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 140) (f := 35+DH32.hSaving T) _ _ (coefficientPatch n _ _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 35) (f := DH32.hSaving T) _ _ (fPatch n _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := DH32.hSaving T) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := DH32.hSaving T) (f := 0) _ _ (DH32.hPatch n _ T) (Patch.refl _)).castSaving (by omega)

/- Optimize the fixed A, remainder-control, epoch and coefficient-boundary literals. -/
/-- The remainder block with its two intervals cancelled across their shared boundary. -/
def crossStepPatch (n start T : Nat) (hT : T < 1542) :
    Patch (measuredStepProgram n start indexedStepProductionRegisters 256 T).2 (1575+DH32.hSaving T) := by
  have hi := early_cross_inputs T hT
  unfold measuredStepProgram measuredStepSegments
  refine (Patch.sequenceCons (d := 140) (f := 1435+DH32.hSaving T) _ _ (aPatch n _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 1050) (f := 385+DH32.hSaving T) _ _ (remainderCrossPatch n _ _ hi.1 hi.2.1 hi.2.2.2) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 210) (f := 175+DH32.hSaving T) _ _ (epochDPatch n _ _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 140) (f := 35+DH32.hSaving T) _ _ (coefficientPatch n _ _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 35) (f := DH32.hSaving T) _ _ (fPatch n _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := DH32.hSaving T) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := DH32.hSaving T) (f := 0) _ _ (DH32.hPatch n _ T) (Patch.refl _)).castSaving (by omega)

/-- Exact per-step saving.  The late steps use a remainder carry wire shared with the fixed
remainder controls, so their cross-boundary cancellation is not claimed. -/
def stepSaving (T : Nat) : Nat := (if T < 1542 then 1575 else 1337)+DH32.hSaving T

/-- Optimize the fixed A, remainder-control, epoch and coefficient-boundary literals. -/
def stepPatch (n start T : Nat) :
    Patch (measuredStepProgram n start indexedStepProductionRegisters 256 T).2 (stepSaving T) :=
  if hT : T < 1542 then (crossStepPatch n start T hT).castSaving (by simp [stepSaving, hT])
  else (candidateStepPatch n start T).castSaving (by simp [stepSaving, hT])

def scheduleSaving : Nat → Nat → Nat
  | 0, _ => 0
  | count+1, first => stepSaving first + scheduleSaving count (first+1)

/-- Exact per-step savings accumulate through the fixed 1,620-step schedule. -/

def schedulePatch (n : Nat) : (count first start : Nat) →
    Patch (measuredScheduleProgram n indexedStepProductionRegisters 256 count first start).2
      (scheduleSaving count first)
  | 0, _, _ => Patch.refl _
  | count+1, first, start => by
    simp only [measuredScheduleProgram]
    exact (Patch.appendCompiled _ _ (stepPatch n start first)
      (schedulePatch n count (first+1) _)).castSaving (by simp only [scheduleSaving])

private theorem scheduleSaving_full : scheduleSaving 1620 1 = 2572388 := by decide

def eeaForwardPatch (n start : Nat) :
    Patch (measuredEEAForwardProgram n start indexedStepProductionRegisters).2 2572388 := by
  unfold measuredEEAForwardProgram
  exact (schedulePatch n 1620 1 start).castSaving scheduleSaving_full


attribute [local irreducible] lengthInitialize Initializer.tight
theorem initRun : Quantum.run (lengthInitialize (List.range' 266 256) (List.range' 549 9) 558
    ((List.range' 7 256).reverse.take 254) (2^256-2^32-977)) = Quantum.run (Initializer.tight Initializer.rows) :=
  Initializer.initializer_tight_run

theorem initSublist : (Initializer.tight Initializer.rows).Sublist
    (lengthInitialize (List.range' 266 256) (List.range' 549 9) 558
      ((List.range' 7 256).reverse.take 254) (2^256-2^32-977)) := Initializer.initializer_tight_sublist

theorem initT : ShorECDLP.tCount (Initializer.tight Initializer.rows) + 910350 =
    ShorECDLP.tCount (lengthInitialize (List.range' 266 256) (List.range' 549 9) 558
      ((List.range' 7 256).reverse.take 254) (2^256-2^32-977)) := Initializer.initializer_tight_t

def setupReduced : Circuit :=
  xorConstant (List.range' 531 9) 511 ++ xorConstant (List.range' 540 9) 511 ++
    Initializer.tight Initializer.rows

def undoReduced : Circuit :=
  Initializer.tight Initializer.rows ++ xorConstant (List.range' 531 9) 511 ++
    xorConstant (List.range' 540 9) 511

def setupPatch (n start : Nat) : Patch (literalProgram eeaLengthSetup : Straight n start start) 910350 := by
  apply Patch.literal eeaLengthSetup setupReduced
  · exact ((List.Sublist.refl _).append (List.Sublist.refl _)).append initSublist
  · simpa only [eeaLengthSetup,setupReduced,Quantum.run_append_map] using
      congrArg (fun f => f ∘ₗ Quantum.run (xorConstant (List.range' 531 9) 511 ++ xorConstant (List.range' 540 9) 511)) initRun
  · have h := initT
    simpa only [eeaLengthSetup,setupReduced,ShorECDLP.tCount_append,xorConstant_tCount,Nat.zero_add] using h

private theorem initializerLiteral_append {n s : Nat} (xs ys : Circuit) :
    (literalProgram (xs ++ ys) : Straight n s s) =
      (literalProgram xs).append (literalProgram ys) := by
  induction xs with
  | nil => simp only [List.nil_append,literalProgram,List.map_nil,gateProgram,Straight.append]
  | cons g xs ih => simpa only [literalProgram,List.map_cons,gateProgram,Straight.append] using congrArg (Straight.gate (.literal g)) ih

def Patch.joinInitializerLiteral {n s d f} {xs ys : Circuit}
    (hp : Patch (literalProgram xs : Straight n s s) d)
    (hq : Patch (literalProgram ys : Straight n s s) f) :
    Patch (literalProgram (xs ++ ys) : Straight n s s) (d+f) := by
  rw [initializerLiteral_append]
  exact hp.append hq

def initialPatch (n start : Nat) :
    Patch (literalProgram (lengthInitialize (List.range' 266 256) (List.range' 549 9) 558
      ((List.range' 7 256).reverse.take 254) (2^256-2^32-977)) : Straight n start start) 910350 :=
  Patch.literal _ _ initSublist initRun initT

def undoPatch (n start : Nat) : Patch (literalProgram eeaLengthUndo : Straight n start start) 910350 := by
  exact (((initialPatch n start).joinInitializerLiteral
    (Patch.refl (literalProgram (xorConstant (List.range' 531 9) 511) : Straight n start start))).joinInitializerLiteral
    (Patch.refl (literalProgram (xorConstant (List.range' 540 9) 511) : Straight n start start))).castSaving (by omega)

def preprocessPatch (n start : Nat) : Patch (preprocessProgram n start).2 910350 := by
  unfold preprocessProgram surroundCompiled prependCompiled
  exact ((Patch.refl _).append
    (Patch.appendCompiled _ _ (Patch.refl _) (setupPatch n _))).castSaving (by omega)

def unpreprocessPatch (n start : Nat) : Patch (unpreprocessProgram n start).2 910350 := by
  unfold unpreprocessProgram surroundCompiled prependCompiled
  exact ((undoPatch n start).append (Patch.refl _)).castSaving (by omega)

def wrapperPatch (n start : Nat) :
    Patch (measuredForwardWrapperProgram n start).2 3482738 := by
  unfold measuredForwardWrapperProgram measuredForwardWrapperSegments
  refine (Patch.sequenceCons (d := 910350) (f := 2572388) _ _ (preprocessPatch n _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := 2572388) (f := 0) _ _ (eeaForwardPatch n _) (Patch.refl _)).castSaving (by omega)


def reverseCleanSource : Circuit :=
  let r := indexedStepProductionRegisters
  prepareLatestPaperTBoundary r.tBoundary 256 ++ computeControl [r.phase1] 1 r.control r.blockScratch

def reversePrepSource : Circuit :=
  let r := indexedStepProductionRegisters
  computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++
    computeControl [r.phase1,r.terminal] 1 r.control r.blockScratch ++
    computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++ restoreLatestPaperTBoundary r.tBoundary 256

def reverseCleanPatch (n s : Nat) : Patch (literalProgram reverseCleanSource : Straight n s s) 70 :=
  acrossSmallPatch n s 70 reverseCleanSource (by unfold CircuitWellFormed; decide +kernel) (by decide +kernel)

def reversePrepPatch (n s : Nat) : Patch (literalProgram reversePrepSource : Straight n s s) 70 :=
  acrossSmallPatch n s 70 reversePrepSource (by unfold CircuitWellFormed; decide +kernel) (by decide +kernel)

def reverseEpochPatch (n s : Nat) :
    Patch (literalProgram (blockCInverse indexedStepProductionRegisters) : Straight n s s) 112 :=
  optimizedLiteralPatch n s 112 _ (by unfold CircuitWellFormed; decide +kernel) (by decide +kernel)

/-- The reverse A literal is split around the terminal-padding epoch test.
Source arithmetic: VerifiedQC/ShorECDLP PR #551, Apache-2.0. -/
def aTerminalSource : Circuit :=
  let r := indexedStepProductionRegisters
  computeControl (r.phase1 :: r.lengthRPrime) (2 ^ (r.lengthRPrime.length + 1) - 2) r.terminal r.blockScratch

def aInverseBefore : Circuit :=
  let r := indexedStepProductionRegisters
  aTerminalSource ++ terminalEpochRestore r.terminal r.shiftEpoch r.quotientLow ++
    [.CX r.terminal r.phase1] ++ (preShiftUnitary r.preShift).adjoint ++ [.CX r.terminal r.phase1]

def aInverseEpoch : Circuit := terminalPaddingEpochUpdate indexedStepProductionRegisters.terminalPadding

def aInverseAfter : Circuit :=
  let r := indexedStepProductionRegisters.terminalPadding
  controlledDecrement r.terminal r.lengthS r.carries ++ controlledRotateRightOne r.terminal r.work2 ++ aTerminalSource

private theorem aInverseEpoch_wellFormed : CircuitWellFormed aInverseEpoch := by
  unfold CircuitWellFormed
  decide +kernel
private theorem aInverseEpoch_saving :
    ShorECDLP.tCount (Cancellation.optimize aInverseEpoch) + 98 = ShorECDLP.tCount aInverseEpoch := by
  decide +kernel

def aInversePatch (n start : Nat) : Patch (literalProgram (blockAInverse indexedStepProductionRegisters) : Straight n start start) 140 := by
  simpa only [blockAInverse, terminalPaddingInverse, preShift_expand, shiftedLiteral, shiftFlags, List.append_assoc, List.append_nil, circuit_adjoint_append] using ((Patch.refl (literalProgram (computeControl (indexedStepProductionRegisters.phase1 :: indexedStepProductionRegisters.lengthRPrime) (2^(indexedStepProductionRegisters.lengthRPrime.length+1)-2) indexedStepProductionRegisters.terminal indexedStepProductionRegisters.blockScratch) : Straight n start start)).joinLiteral ((Patch.refl (literalProgram (terminalEpochRestore indexedStepProductionRegisters.terminal indexedStepProductionRegisters.shiftEpoch indexedStepProductionRegisters.quotientLow) : Straight n start start)).joinLiteral ((Patch.refl (literalProgram (([.CX indexedStepProductionRegisters.terminal indexedStepProductionRegisters.phase1] : Circuit)) : Straight n start start)).joinLiteral ((Patch.refl (literalProgram (Circuit.adjoint (([.X indexedStepProductionRegisters.preShift.phase1, .CX indexedStepProductionRegisters.preShift.phase1 indexedStepProductionRegisters.preShift.phase1IsZero, .X indexedStepProductionRegisters.preShift.phase1] : Circuit))) : Straight n start start)).joinLiteral ((Patch.refl (literalProgram (Circuit.adjoint (([.CCX indexedStepProductionRegisters.preShift.phase1IsZero indexedStepProductionRegisters.preShift.phase2 indexedStepProductionRegisters.preShift.both] : Circuit))) : Straight n start start)).joinLiteral ((smallPatch n start 28 (Circuit.adjoint ((controlledDecrement indexedStepProductionRegisters.preShift.both indexedStepProductionRegisters.preShift.lengthS indexedStepProductionRegisters.preShift.carries ++ controlledDecrement indexedStepProductionRegisters.preShift.both indexedStepProductionRegisters.preShift.lengthS indexedStepProductionRegisters.preShift.carries))) (by unfold CircuitWellFormed; decide +kernel) (by decide +kernel)).joinLiteral ((Patch.refl (literalProgram (Circuit.adjoint (controlledRotateRightTwo indexedStepProductionRegisters.preShift.both indexedStepProductionRegisters.preShift.work)) : Straight n start start)).joinLiteral ((Patch.refl (literalProgram (Circuit.adjoint (([.CCX indexedStepProductionRegisters.preShift.phase1IsZero indexedStepProductionRegisters.preShift.phase2 indexedStepProductionRegisters.preShift.both] : Circuit))) : Straight n start start)).joinLiteral ((smallPatch n start 7 (Circuit.adjoint (controlledIncrement indexedStepProductionRegisters.preShift.phase1IsZero indexedStepProductionRegisters.preShift.lengthS indexedStepProductionRegisters.preShift.carries)) (by unfold CircuitWellFormed; decide +kernel) (by decide +kernel)).joinLiteral ((Patch.refl (literalProgram (Circuit.adjoint (controlledRotateLeftOne indexedStepProductionRegisters.preShift.phase1IsZero indexedStepProductionRegisters.preShift.work)) : Straight n start start)).joinLiteral ((Patch.refl (literalProgram (Circuit.adjoint (([.X indexedStepProductionRegisters.preShift.phase1, .CX indexedStepProductionRegisters.preShift.phase1 indexedStepProductionRegisters.preShift.phase1IsZero, .X indexedStepProductionRegisters.preShift.phase1] : Circuit))) : Straight n start start)).joinLiteral ((Patch.refl (literalProgram (([.CX indexedStepProductionRegisters.terminal indexedStepProductionRegisters.phase1] : Circuit)) : Straight n start start)).joinLiteral ((smallPatch n start 98 (terminalPaddingEpochUpdate indexedStepProductionRegisters.terminalPadding) (by unfold CircuitWellFormed; decide +kernel) (by decide +kernel)).joinLiteral ((smallPatch n start 7 (controlledDecrement indexedStepProductionRegisters.terminalPadding.terminal indexedStepProductionRegisters.terminalPadding.lengthS indexedStepProductionRegisters.terminalPadding.carries) (by unfold CircuitWellFormed; decide +kernel) (by decide +kernel)).joinLiteral ((Patch.refl (literalProgram (controlledRotateRightOne indexedStepProductionRegisters.terminalPadding.terminal indexedStepProductionRegisters.terminalPadding.work2) : Straight n start start)).joinLiteral ((Patch.refl (literalProgram (computeControl (indexedStepProductionRegisters.phase1 :: indexedStepProductionRegisters.lengthRPrime) (2^(indexedStepProductionRegisters.lengthRPrime.length+1)-2) indexedStepProductionRegisters.terminal indexedStepProductionRegisters.blockScratch) : Straight n start start)).joinLiteral (Patch.refl (literalProgram List.nil : Straight n start start))))))))))))))))))

def fInversePatch (n start : Nat) : Patch (literalProgram ((blockFForward indexedStepProductionRegisters).adjoint) : Straight n start start) 35 := by
  simpa only [blockFForward, postShift_expand, shiftedLiteral, shiftFlags, List.append_assoc, List.append_nil, circuit_adjoint_append] using ((Patch.refl (literalProgram (Circuit.adjoint (([.CCX indexedStepProductionRegisters.postShift.phase1 indexedStepProductionRegisters.postShift.phase2 indexedStepProductionRegisters.postShift.both] : Circuit))) : Straight n start start)).joinLiteral ((smallPatch n start 28 (Circuit.adjoint ((controlledDecrement indexedStepProductionRegisters.postShift.both indexedStepProductionRegisters.postShift.lengthS indexedStepProductionRegisters.postShift.carries ++ controlledDecrement indexedStepProductionRegisters.postShift.both indexedStepProductionRegisters.postShift.lengthS indexedStepProductionRegisters.postShift.carries))) (by unfold CircuitWellFormed; decide +kernel) (by decide +kernel)).joinLiteral ((Patch.refl (literalProgram (Circuit.adjoint (controlledRotateRightTwo indexedStepProductionRegisters.postShift.both indexedStepProductionRegisters.postShift.work)) : Straight n start start)).joinLiteral ((Patch.refl (literalProgram (Circuit.adjoint (([.CCX indexedStepProductionRegisters.postShift.phase1 indexedStepProductionRegisters.postShift.phase2 indexedStepProductionRegisters.postShift.both] : Circuit))) : Straight n start start)).joinLiteral ((smallPatch n start 7 (Circuit.adjoint (controlledIncrement indexedStepProductionRegisters.postShift.phase1 indexedStepProductionRegisters.postShift.lengthS indexedStepProductionRegisters.postShift.carries)) (by unfold CircuitWellFormed; decide +kernel) (by decide +kernel)).joinLiteral ((Patch.refl (literalProgram (Circuit.adjoint (controlledRotateLeftOne indexedStepProductionRegisters.postShift.phase1 indexedStepProductionRegisters.postShift.work)) : Straight n start start)).joinLiteral (Patch.refl (literalProgram List.nil : Straight n start start))))))))

def reverseFrontPatch (n s : Nat) :
    Patch (literalProgram ((blockFForward indexedStepProductionRegisters).adjoint ++
      prepareLatestPaperTBoundary indexedStepProductionRegisters.tBoundary 256 ++
      computeControl [indexedStepProductionRegisters.phase1] 1 indexedStepProductionRegisters.control indexedStepProductionRegisters.blockScratch) : Straight n s s) 105 := by
  have hp := ((fInversePatch n s).joinLiteral
    (reverseCleanPatch n s)).castSaving (show 35+70=105 by omega)
  simpa only [reverseCleanSource, List.append_assoc] using hp

def reverseCombinedPatch (n s : Nat) (w : ActiveWindow) :
    Patch (literalProgram (let r := indexedStepProductionRegisters;
      computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++
      computeControl [r.phase1,r.terminal] 1 r.control r.blockScratch ++
      computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++ restoreLatestPaperTBoundary r.tBoundary 256 ++
      blockDInverse r w ++ blockCInverse r ++
      (([.CCX r.phase2 r.sign r.terminal] ++ rControlNonterminal [r.phase1,r.terminal] 0 r.control r.lengthRPrime (r.blockScratch.getD 0 0) (r.blockScratch.drop 1)) ++ [.CCX r.phase2 r.sign r.terminal])) : Straight n s s) 280 := by
  have hp := ((((reversePrepPatch n s).joinLiteral
    (DH32.dInversePatch n s w)).joinLiteral
    (reverseEpochPatch n s)).joinLiteral (Patch.refl (literalProgram b3Source : Straight n s s))).castSaving
    (show 70+98+112+0=280 by omega)
  simpa only [reversePrepSource, b3Source, List.append_assoc] using hp

def reverseRemainderPatch (n s : Nat) :
    Patch (literalProgram (b3Source ++ b2Source ++ b1Source) : Straight n s s) 434 :=
  optimizedLiteralPatch n s 434 _ (by unfold CircuitWellFormed; decide +kernel) (by decide +kernel)

def reverseStepPatch (n start T : Nat) :
    Patch (measuredInverseStepProgram n start indexedStepProductionRegisters T).2 (1337+DH32.hSaving T) := by
  unfold measuredInverseStepProgram measuredInverseStepSegments
  refine (Patch.sequenceCons (d := DH32.hSaving T) (f := 1337) _ _ (DH32.hInversePatch n _ T) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 1337) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 105) (f := 1232) _ _ ?_ ?_).castSaving (by omega)
  · exact reverseFrontPatch n _
  refine (Patch.sequenceCons (d := 0) (f := 1232) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 1232) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 1232) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 280) (f := 952) _ _ ?_ ?_).castSaving (by omega)
  · exact reverseCombinedPatch n _ (certifiedActiveWindows 256 T).quotientSwap
  refine (Patch.sequenceCons (d := 140) (f := 812) _ _ ?_ ?_).castSaving (by omega)
  · unfold intervalInverseProgram
    exact remainderIntervalPatch n _ _ (certified_remainder_count T) _ _ _
  refine (Patch.sequenceCons (d := 434) (f := 378) _ _ ?_ ?_).castSaving (by omega)
  · exact reverseRemainderPatch n _
  refine (Patch.sequenceCons (d := 140) (f := 238) _ _ ?_ ?_).castSaving (by omega)
  · unfold intervalInverseProgram
    exact remainderIntervalPatch n _ _ (certified_remainder_count T) _ _ _
  exact (Patch.sequenceCons (d := 238) (f := 0) _ _
    (((b1Patch n _).joinLiteral (aInversePatch n _)).castSaving (by omega)) (Patch.refl _)).castSaving (by omega)

def reverseCrossStepPatch (n start T : Nat) (hT : T < 1542) :
    Patch (measuredInverseStepProgram n start indexedStepProductionRegisters T).2 (1575+DH32.hSaving T) := by
  have hi := early_cross_inputs T hT
  unfold measuredInverseStepProgram measuredInverseStepSegments
  refine (Patch.sequenceCons (d := DH32.hSaving T) (f := 1575) _ _ (DH32.hInversePatch n _ T) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 1575) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 105) (f := 1470) _ _ ?_ ?_).castSaving (by omega)
  · exact reverseFrontPatch n _
  refine (Patch.sequenceCons (d := 0) (f := 1470) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 1470) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 1470) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact reverseTailCrossPatch n _ _ _ _ hi.1 hi.2.2.1 hi.2.2.2
    (reverseCombinedPatch n _ (certifiedActiveWindows 256 T).quotientSwap)
    (fun s => ((b1Patch n s).joinLiteral (aInversePatch n s)).castSaving (show 98 + 140 = 238 by omega))

def reverseStepPatchT (n start T : Nat) :
    Patch (measuredInverseStepProgram n start indexedStepProductionRegisters T).2 (stepSaving T) :=
  if hT : T < 1542 then (reverseCrossStepPatch n start T hT).castSaving (by simp [stepSaving, hT])
  else (reverseStepPatch n start T).castSaving (by simp [stepSaving, hT])

def reverseSchedulePatch (n : Nat) : (count first start : Nat) →
    Patch (measuredInverseScheduleProgram n indexedStepProductionRegisters count first start).2
      (scheduleSaving count first)
  | 0, _, _ => Patch.refl _
  | count+1, first, start => by
    simp only [measuredInverseScheduleProgram]
    exact (Patch.appendCompiled _ _ (reverseSchedulePatch n count (first+1) start)
      (reverseStepPatchT n _ first)).castSaving (by simp only [scheduleSaving]; omega)

def eeaReversePatch (n start : Nat) :
    Patch (measuredEEAReverseProgram n start indexedStepProductionRegisters).2 2572388 := by
  unfold measuredEEAReverseProgram
  exact (reverseSchedulePatch n 1620 1 start).castSaving scheduleSaving_full

def reverseWrapperPatch (n start : Nat) :
    Patch (measuredReverseWrapperProgram n start).2 3482738 := by
  unfold measuredReverseWrapperProgram measuredReverseWrapperSegments
  refine (Patch.sequenceCons (d := 0) (f := 3482738) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 3482738) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 3482738) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 2572388) (f := 910350) _ _ (eeaReversePatch n _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := 910350) (f := 0) _ _ (unpreprocessPatch n _) (Patch.refl _)).castSaving (by omega)

def Patch.relabelCompiled {n start d} (e : Wire ≃ Wire)
    (p : (count : Nat) × Straight n start (start+count)) (hp : Patch p.2 d) :
    Patch (Paper2607_13816.ChallengeMigration.relabelCompiled e p).2 d :=
  hp.relabel e

def forwardDataPatch (n start : Nat) : Patch (measuredForwardDataBankProgram n start).2 3482738 := by
  unfold measuredForwardDataBankProgram
  exact Patch.relabelCompiled eeaWorkspaceExchange _ (wrapperPatch n start)

def reverseDataPatch (n start : Nat) : Patch (measuredReverseDataBankProgram n start).2 3482738 := by
  unfold measuredReverseDataBankProgram
  exact Patch.relabelCompiled eeaWorkspaceExchange _ (reverseWrapperPatch n start)

def collectPatch {n d}
    (next : (cursor : Nat) → List (Fin cursor) → (count : Nat) × Straight n cursor (cursor+count))
    (hp : ∀ cursor prior, Patch (next cursor prior).2 d) :
    (ws : List Wire) → (start : Nat) → (prior : List (Fin start)) →
      Patch (collectProgram n next ws start prior).2 d
  | [], start, prior => by simpa only [collectProgram] using hp start prior
  | w::ws, start, prior => by
    simp only [collectProgram]
    exact (Patch.measure w (collectPatch next hp ws (start+1) _)).castFinish _

def divisionAfterResetPatch (n start : Nat) (prior : List (Fin start)) :
    Patch (divisionAfterResetProgram n start prior).2 3482738 := by
  unfold divisionAfterResetProgram appendRetaining
  exact (Patch.appendCompiled (d := 3482738) (f := 0) _ _
    ((Patch.appendCompiled (d := 3482738) (f := 0) _ _ (reverseDataPatch n start) (Patch.refl _)).castSaving (by omega))
    (Patch.refl _)).castSaving (by omega)

def divisionPatch (n start : Nat) : Patch (divisionProgram n start).2 6965476 := by
  unfold divisionProgram
  exact (Patch.appendCompiled (d := 3482738) (f := 3482738) _ _
    ((Patch.appendCompiled (d := 3482738) (f := 0) _ _ (wrapperPatch n start) (Patch.refl _)).castSaving (by omega))
    (collectPatch _ (divisionAfterResetPatch n) _ _ _)).castSaving (by omega)

def multiplicationCleanupPatch (n start : Nat) :
    Patch (multiplicationCleanupProgram n start).2 3482738 := by
  unfold multiplicationCleanupProgram appendLiteral
  exact (Patch.appendCompiled (d := 0) (f := 3482738) _ _ (Patch.refl _)
    ((Patch.appendCompiled (d := 3482738) (f := 0) _ _ (reverseDataPatch n _) (Patch.refl _)).castSaving (by omega))).castSaving (by omega)

def multiplicationCorrectionPatch (n start : Nat) (prior : List (Fin start)) :
    Patch (multiplicationCorrectionProgram n start prior).2 3482738 := by
  unfold multiplicationCorrectionProgram
  exact (Patch.appendCompiled (d := 0) (f := 3482738)
    (correctionCompiled n start (List.range' 580 256) prior) (multiplicationCleanupProgram n start)
    (Patch.refl _) (multiplicationCleanupPatch n start)).castSaving (show 0+3482738=3482738 by omega)

def multiplicationAfterResetPatch (n start : Nat) (prior : List (Fin start)) :
    Patch (multiplicationAfterResetProgram n start prior).2 6965476 := by
  unfold multiplicationAfterResetProgram appendRetaining
  exact (Patch.appendCompiled (d := 3482738) (f := 3482738) _ _
    ((Patch.appendCompiled (d := 3482738) (f := 0) _ _ (forwardDataPatch n _) (Patch.refl _)).castSaving (by omega))
    (multiplicationCorrectionPatch n _ _)).castSaving (by omega)

def multiplicationPatch (n start : Nat) : Patch (multiplicationProgram n start).2 6965476 := by
  unfold multiplicationProgram
  exact (Patch.appendCompiled (d := 0) (f := 6965476) _ _ (Patch.refl _)
    (collectPatch _ (multiplicationAfterResetPatch n) _ _ _)).castSaving (by omega)



end
end ShorECDLP.Entrant.TransportOptimization
namespace ShorECDLP.Entrant.TransportOptimization
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] sequenceProgram appendCompiled literalProgram ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateProgram ShorECDLP.Entrant.BorrowFlag.divisionProgram ShorECDLP.Entrant.BorrowFlag.multiplicationProgram
  Single.axis Rounded.entry

def borrowedFieldPatch {saving : Nat} (n start : Nat) (arithmetic : FixedSegment n)
    (hp : ∀ cursor, Patch (arithmetic cursor).2 saving) :
    Patch (ShorECDLP.Entrant.BorrowFlag.fieldProgram n start arithmetic).2 saving := by
  unfold ShorECDLP.Entrant.BorrowFlag.fieldProgram
  apply Patch.surroundCompiled
  unfold ShorECDLP.Entrant.BorrowFlag.coreSegments
  refine (Patch.sequenceCons (d := 0) (f := saving) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := saving) (f := 0) _ _ (hp _) (Patch.refl _)).castSaving (by omega)

def zeroDivisionPatch (n start : Nat) :
    Patch (ShorECDLP.Entrant.BorrowFlag.divisionProgram n start).2 6965476 := by
  unfold ShorECDLP.Entrant.BorrowFlag.divisionProgram
  exact borrowedFieldPatch n start (divisionProgram n) (divisionPatch n)

def zeroMultiplicationPatch (n start : Nat) :
    Patch (ShorECDLP.Entrant.BorrowFlag.multiplicationProgram n start).2 6965476 := by
  unfold ShorECDLP.Entrant.BorrowFlag.multiplicationProgram
  exact borrowedFieldPatch n start (multiplicationProgram n) (multiplicationPatch n)

def coordinatePatch (start : Nat) : Patch (ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateProgram start).2 13930952 := by
  unfold ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateProgram ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateSegments
  refine (Patch.sequenceCons (d := 0) (f := 13930952) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 13930952) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 6965476) (f := 6965476) _ _ (zeroDivisionPatch 32768 _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 6965476) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 6965476) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := 6965476) (f := 0) _ _ (zeroMultiplicationPatch 32768 _) (Patch.refl _)).castSaving (by omega)

-- Append within Optimization after borrowed division/multiplication patches.
attribute [local irreducible] NarrowQrom.coordinateProgram NarrowQrom.coreProgram NarrowQrom.preparedProgram

def narrowCoordinatePatch {d : Nat}
    (hd : ∀start,Patch (BorrowFlag.divisionProgram 32768 start).2 d)
    (hm : ∀start,Patch (BorrowFlag.multiplicationProgram 32768 start).2 d)
    (start : Nat) : Patch (NarrowQrom.coordinateProgram start).2 (d+d) := by
  unfold NarrowQrom.coordinateProgram NarrowQrom.coordinateSegments
  refine (Patch.sequenceCons (d:=0) (f:=d+d) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d:=0) (f:=d+d) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d:=d) (f:=d) _ _ (hd _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d:=0) (f:=d) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d:=0) (f:=d) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d:=d) (f:=0) _ _ (hm _) (Patch.refl _)).castSaving (by omega)

def narrowCorePatch {d : Nat}
    (hc : ∀start,Patch (NarrowQrom.coordinateProgram start).2 d) (start : Nat) :
    Patch (NarrowQrom.coreProgram start).2 d := by
  unfold NarrowQrom.coreProgram NarrowQrom.coreSegments
  exact (Patch.sequenceCons (d:=d) (f:=0) _ _ (hc _) (Patch.refl _)).castSaving (by omega)

def narrowPreparedPatch {d : Nat}
    (hc : ∀start,Patch (NarrowQrom.coordinateProgram start).2 d) (start : Nat) :
    Patch (NarrowQrom.preparedProgram start).2 d := by
  unfold NarrowQrom.preparedProgram
  exact Patch.surroundCompiled _ _ _ (narrowCorePatch hc start)

def narrowActualPatch {d : Nat}
    (hc : ∀start,Patch (NarrowQrom.coordinateProgram start).2 d) (start : Nat) :
    Patch (NarrowQrom.actual.program start) d := by
  unfold NarrowQrom.actual closedWindow
  exact (((narrowPreparedPatch hc 0).relabel (windowAddressPerm 855 (by decide))).castFinish _).shift start

def corePatch (start : Nat) : Patch (Single.Physical.core start).2 13930952 := by
  unfold Single.Physical.core Single.Physical.segments
  exact (Patch.sequenceCons (d := 13930952) (f := 0) _ _ (coordinatePatch start) (Patch.refl _)).castSaving (by omega)

def preparedPatch (start : Nat) : Patch (Single.Physical.prepared start).2 13930952 := by
  unfold Single.Physical.prepared
  exact Patch.surroundCompiled _ _ _ (corePatch start)

def actualPatch (start : Nat) : Patch (Single.Physical.actual.program start) 13930952 := by
  unfold Single.Physical.actual closedWindow
  exact (((preparedPatch 0).relabel (windowAddressPerm 855 (by decide))).castFinish _).shift start

def signedPatch (w : Single.SignedWindow) (start : Nat) :
    Patch ((Single.signedWindow w).program start) 13930952 := by
  unfold Single.signedWindow
  cases w <;> simp only [Single.SignedWindow.width]
  all_goals first
    | exact (narrowActualPatch (narrowCoordinatePatch (zeroDivisionPatch 32768) (zeroMultiplicationPatch 32768)) start).reindex (Single.signedRow _)
    | exact (actualPatch start).reindex (Single.signedRow _)

def preparePatch {n s e d} (ws : List Wire) {p : Straight n s e} (hp : Patch p d) :
    Patch (prepareOuterBank ws p) d := by
  induction ws with
  | nil => exact hp
  | cons w ws ih => exact Patch.gate (.literal (.H w)) ih

structure PatchedWindow (n : Nat) where
  source : Single.Window n
  saving : Nat
  patch : ∀ start, Patch (source.program start) saving

def leftPatches : List (PatchedWindow 851968) :=
  ⟨Single.firstWindow,0,fun _ => Patch.refl _⟩ ::
    Single.leftSigned.map (fun w => ⟨Single.signedWindow w,13930952,signedPatch w⟩)
def rightPatches : List (PatchedWindow 851968) :=
  Single.rightSigned.map (fun w => ⟨Single.signedWindow w,13930952,signedPatch w⟩)
private theorem leftPatches_source : leftPatches.map PatchedWindow.source = Single.leftWindows := by
  simp [leftPatches, Single.leftWindows]
private theorem rightPatches_source : rightPatches.map PatchedWindow.source = Single.rightWindows := by
  simp [rightPatches, Single.rightWindows]
private theorem leftPatches_saving : (leftPatches.map PatchedWindow.saving).sum = 222895232 := by
  simp [leftPatches, Single.leftSigned]
private theorem rightPatches_saving : (rightPatches.map PatchedWindow.saving).sum = 181102376 := by
  simp [rightPatches, Single.rightSigned]

def axisPatch {n} : (ps : List (PatchedWindow n)) → (start : Nat) → (prior : List (Fin start)) →
    Patch (Single.axis (ps.map PatchedWindow.source) start prior) ((ps.map PatchedWindow.saving).sum)
  | [], _, _ => Patch.refl _
  | p::ps, start, prior => by
    simp only [List.map_cons, List.sum_cons, Single.axis]
    refine Patch.castFinish ?_ _
    refine Patch.castSaving (Patch.append (f := (ps.map PatchedWindow.saving).sum) (preparePatch _ (p.patch start)) ?_) (by omega)
    exact (Patch.append (Patch.refl _) (axisPatch ps _ (Single.nextPrior p.source.count p.source.wires.length prior))).castSaving (by omega)

def axisPatchFor {n} (ps : List (PatchedWindow n)) (ws : List (Single.Window n))
    (he : ps.map PatchedWindow.source = ws) (start : Nat) (prior : List (Fin start)) :
    Patch (Single.axis ws start prior) ((ps.map PatchedWindow.saving).sum) := by
  subst ws
  exact axisPatch ps start prior

def Patch.framed {n s m k e f dl dr} (p : Straight n s m) (q : Straight n m k)
    (r : Straight n k e) (h : e=f) (hp : Patch p dl) (hq : Patch q dr) :
    Patch (Single.framed p q r h) (dl+dr) := by
  unfold Single.framed
  exact Patch.gate _ ((Patch.append hp ((Patch.append hq (Patch.gate _ (Patch.refl _))).castSaving (Nat.add_zero dr))).castFinish h)

def trialPatch (start : Nat) : Patch (Single.trial start) 403997608 := by
  have hl := (axisPatchFor leftPatches Single.leftWindows leftPatches_source start List.nil).castSaving leftPatches_saving
  have hr := (axisPatchFor rightPatches Single.rightWindows rightPatches_source
    (start+Single.axisCount Single.leftWindows) List.nil).castSaving rightPatches_saving
  unfold Single.trial
  exact (Patch.framed _ _ _ _ hl hr).castSaving (by decide)

def programPatch : Patch Single.program 403997608 := by
  unfold Single.program
  exact (trialPatch 0).castFinish _

def Patch.fixedEntry {n e d} (f : Fin n → PointCoeff) (p : Straight n 0 e) (hp : Patch p d) :
    Patch (Single.fixedEntry f p).program d := by
  unfold Single.fixedEntry
  exact hp.reindex _

def entryPatch : Patch Rounded.entry.program 403997608 := by
  unfold Rounded.entry Rounded.program
  exact Patch.fixedEntry Single.mixedCoefficientAt _
    ((Patch.append programPatch (Patch.refl Rounded.readout)).castSaving (by omega))
end
end ShorECDLP.Entrant.TransportOptimization


namespace ShorECDLP.Entrant.Compressed
open Challenge
noncomputable def entry : StraightEntry := TransportOptimization.replaceEntry Rounded.entry TransportOptimization.entryPatch.program
def layout : DecodeLayout := Rounded.layout
def bounds : Bounds := ⟨Rounded.bounds.qubits, Rounded.bounds.tModel - 403997608, Rounded.bounds.measurements⟩
theorem certificate : Certificate officialLimits layout entry bounds :=
  TransportOptimization.replacement_certificate Rounded.certificate TransportOptimization.entryPatch.drops TransportOptimization.entryPatch.rewrites
end ShorECDLP.Entrant.Compressed
namespace ShorECDLP.Entrant.CompressedCredit
open Quantum Challenge AndGadget Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
theorem dropped_added {n s e d} {p q : Straight n s e} (h : TransportOptimization.Drops p q d) :
    7 * added p ≤ 7 * added q + d := by
  induction h with
  | refl => omega
  | skip g h ih => cases g <;> simp_all [added, tCost] <;> omega
  | gate g h ih =>
    cases g with
    | literal g => cases g <;> simp_all [added] <;> omega
    | whenBit => exact ih
  | record => assumption
  | measure => assumption

  | transport a b t u hh h ih=>simp only [added]; omega
  | control a b t hh h ih=>simp only [added]; omega
  | swap g k h ih => cases g <;> cases k <;> simp_all [added] <;> omega
  | trans h k ih ik=>omega

theorem count_after_drop {n s e : Nat} (p q : Straight n s e) (d c l : Nat)
    (hd : TransportOptimization.Drops p q d) (hc : c≤added p)
    (hn : 7*l+d≤7*c) : l≤added q := by
  have h:=dropped_added hd
  omega

theorem entry_count_after_drop (e : StraightEntry) {d : Nat}
    (hp : TransportOptimization.Patch e.program d) (c l : Nat)
    (hc : c≤added e.program) (hn : 7*l+d≤7*c) :
    l≤added (TransportOptimization.replaceEntry e hp.program).program := by
  exact count_after_drop e.program hp.program d c l hp.drops hc hn

attribute [local irreducible] added lower lowerEntry lowerLayout TransportOptimization.entryPatch



theorem parent_added_lower : 2043997771≤added Compressed.entry.program :=
  entry_count_after_drop Rounded.entry TransportOptimization.entryPatch
    2101711715 2043997771 AndGadget.entryCount (by decide)

theorem within_reindex {n m s e} (p : Straight n s e) (f : Fin n → Fin m) (ws : List Wire)
    (hp : Within ws p) : Within ws (reindexStraight f p) := by
  induction p with
  | done => trivial
  | gate g p ih => cases g <;> exact ⟨hp.1, ih hp.2⟩
  | recordGate => exact ⟨hp.1, by apply_assumption; exact hp.2⟩
  | measure => exact ⟨hp.1, by apply_assumption; exact hp.2⟩


theorem within_drops {n s e d} {p q : Straight n s e} (h : TransportOptimization.Drops p q d)
    (ws : List Wire) (hp : Within ws p) : Within ws q := by
  induction h with
  | refl => exact hp
  | skip g h ih => exact ih hp.2
  | gate g h ih => cases g <;> exact ⟨hp.1, ih hp.2⟩
  | record i v g h ih => exact ⟨hp.1, ih hp.2⟩
  | measure w h ih => exact ⟨hp.1, ih hp.2⟩


  | transport a b t u hh h ih=>
    simp only [Within,gateWires,List.cons_subset,List.nil_subset,and_true] at hp ⊢
    exact ⟨hp.2.1,⟨⟨hp.1.1,hp.1.2.1,hp.2.1.2⟩,ih hp.2.2.2⟩⟩
  | control a b t hh h ih=>
    simp only [Within,gateWires,List.cons_subset,List.nil_subset,and_true] at hp ⊢
    exact ⟨hp.2.1,⟨⟨hp.1.1,hp.1.2.2⟩,ih hp.2.2.2⟩⟩
  | swap g k h ih => exact ⟨hp.2.1,hp.1,ih hp.2.2⟩
  | trans h k ih ik=>exact ik (ih hp)

theorem fixedEntry_within {n e} (f : Fin n → PointCoeff) (p : Straight n 0 e)
    (ws : List Wire) (hp : Within ws p) : Within ws (Single.fixedEntry f p).program :=
  within_reindex p _ ws hp


attribute [local irreducible] Within

theorem entry_within_after_drop (e : StraightEntry) {d : Nat}
    (hp : TransportOptimization.Patch e.program d) (ws : List Wire)
    (hc : Within ws e.program) :
    Within ws (TransportOptimization.replaceEntry e hp.program).program :=
  within_drops hp.drops ws hc

theorem parent_within : Within resetWires Compressed.entry.program := by
  apply entry_within_after_drop Rounded.entry TransportOptimization.entryPatch resetWires
  unfold Rounded.entry
  apply fixedEntry_within
  apply within_of_instantiate
  intro read history
  have he : history = Fin.elim0 := by funext i; exact Fin.elim0 i
  subst history
  exact Rounded.program_support read

set_option maxRecDepth 2000

theorem entry_added_upper_bound (limits : Limits) (layout : DecodeLayout)
    (e : StraightEntry) (b : Bounds) (upper : Nat)
    (hc : Certificate limits layout e b) (hn : b.tModel≤2*upper+1) :
    added e.program≤upper := by
  have h := lower_t 1024 e.program 0 Fin.elim0
    (readConstant e.coefficients.get 0) Fin.elim0 Fin.elim0
    (by funext i; exact Fin.elim0 i)
  have ht := (hc.resources 0).2.1
  change (e.program.instantiate (readConstant e.coefficients.get 0) Fin.elim0).tCount≤b.tModel at ht
  omega

theorem parent_added_upper : added Compressed.entry.program≤7375384892 :=
  entry_added_upper_bound officialLimits Compressed.layout Compressed.entry Compressed.bounds
    7375384892 Compressed.certificate (by decide)

theorem entry_slots_after_drop (e : StraightEntry) {d : Nat}
    (hp : TransportOptimization.Patch e.program d) (slots : Nat)
    (hc : e.program.gateSlots≤slots) :
    (TransportOptimization.replaceEntry e hp.program).program.gateSlots≤slots :=
  hp.drops.slots.trans hc

theorem parent_slots : Compressed.entry.program.gateSlots≤90000176648 := by
  apply entry_slots_after_drop Rounded.entry TransportOptimization.entryPatch 90000176648
  rw [Rounded.entry,Single.fixedEntry_slots]
  exact Rounded.program_slots

end
end ShorECDLP.Entrant.CompressedCredit


namespace ShorECDLP.Entrant.CompressedFive
open Challenge AndGadget CompressedCredit Paper2607_13816.ChallengeMigration
attribute [local irreducible] Within
set_option maxRecDepth 10000
attribute [local irreducible] added lower lowerEntry lowerLayout TransportOptimization.entryPatch
noncomputable def entry : StraightEntry := lowerEntry 1024 Compressed.entry
noncomputable def layout : DecodeLayout := lowerLayout 1024 Compressed.entry Compressed.layout
def bounds : Bounds := ⟨855, 10220044629, 8265980838⟩

private theorem resourceArithmetic (a slots cursor oldT newT maxSlots maxRecords newRecords : Nat)
    (ha : a ≤ 7375384892) (hl : 2043997771 ≤ a) (hs : slots ≤ 90000176648)
    (hc : cursor ≤ 886843252) (ho : oldT ≤ 14308040171) (hn : 10220044629 ≤ newT)
    (hls : 4000000000000000 ≤ maxSlots) (hlm : 47471340504 ≤ maxRecords)
    (hnm : 8265980838 ≤ newRecords) :
    slots + 18*a ≤ maxSlots ∧ cursor+a ≤ maxRecords ∧ oldT ≤ newT + 2*a ∧
    cursor+a ≤ newRecords := by omega

theorem certificate : Certificate officialLimits layout entry bounds := by
  have h := resourceArithmetic (added Compressed.entry.program) Compressed.entry.program.gateSlots
    Compressed.entry.finalCursor Compressed.bounds.tModel bounds.tModel officialLimits.gateSlots
    officialLimits.measurements bounds.measurements
    CompressedCredit.parent_added_upper CompressedCredit.parent_added_lower CompressedCredit.parent_slots (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  apply lower_certificate officialLimits Compressed.layout Compressed.entry Compressed.bounds bounds
    1024 resetWires Compressed.certificate CompressedCredit.parent_within
  · simp [resetWires]
  · exact h.1
  · exact h.2.1
  · change resetWires.length + 1 ≤ 855
    rw [resetWires_length]
  · exact h.2.2.1
  · exact h.2.2.2
end ShorECDLP.Entrant.CompressedFive
section
namespace ShorECDLP.Entrant.PreviousCurrent
open Challenge AndGadget Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
attribute [local irreducible] added lower lowerEntry lowerLayout Within
  Catalyst.saved Catalyst.compileEntry TransportOptimization.entryPatch

private theorem cursor_bound (limits : Limits) (layout : DecodeLayout) (e : StraightEntry)
    (b : Bounds) (h : Certificate limits layout e b) : e.finalCursor ≤ b.measurements := by
  have hm := (h.resources 0).2.2
  have he := e.program.measurementCount (readConstant e.coefficients.get 0) Fin.elim0
  change (e.program.instantiate (readConstant e.coefficients.get 0) Fin.elim0).measurementCount ≤ b.measurements at hm
  omega

private theorem lowerEntry_within (q : Wire) (e : StraightEntry) (ws : List Wire)
    (hs : Within ws e.program) : Within (q::ws) (lowerEntry q e).program := by
  unfold lowerEntry
  exact lower_within q e.program ws hs 0 Fin.elim0

private theorem lowerEntry_saved (q : Wire) (e : StraightEntry) :
    Catalyst.saved (lowerEntry q e).program = added e.program + Catalyst.saved e.program := by
  unfold lowerEntry
  exact Catalyst.saved_lower q e.program 0 Fin.elim0

private theorem lowerEntry_slots (q : Wire) (e : StraightEntry) :
    (lowerEntry q e).program.gateSlots = e.program.gateSlots + 18 * added e.program := by
  unfold lowerEntry
  exact lower_slots q e.program 0 Fin.elim0

private theorem five_within : Within (1024 :: resetWires) CompressedFive.entry.program :=
  lowerEntry_within 1024 Compressed.entry resetWires CompressedCredit.parent_within

private theorem saved_bound (a b s : Nat) (he : s = a+b) (hl : 2043997771 ≤ a) :
    2043997771 ≤ s := by omega

private theorem five_saved : 2043997771 ≤ Catalyst.saved CompressedFive.entry.program :=
  saved_bound (added Compressed.entry.program) (Catalyst.saved Compressed.entry.program)
    (Catalyst.saved CompressedFive.entry.program) (lowerEntry_saved 1024 Compressed.entry) CompressedCredit.parent_added_lower

private theorem slots_bound (old new a : Nat) (he : new = old + 18*a)
    (hs : old ≤ 90000176648) (ha : a ≤ 7375384892) : new ≤ 230350301035 := by omega

private theorem five_slots : CompressedFive.entry.program.gateSlots ≤ 230350301035 :=
  slots_bound Compressed.entry.program.gateSlots CompressedFive.entry.program.gateSlots
    (added Compressed.entry.program) (lowerEntry_slots 1024 Compressed.entry) CompressedCredit.parent_slots CompressedCredit.parent_added_upper

noncomputable def entry : StraightEntry := Catalyst.compileEntry 1025 CompressedFive.entry
noncomputable def layout : DecodeLayout := CompressedFive.layout
def bounds : Bounds := ⟨856, 8176046859, 8265980838⟩

private theorem resourceArithmetic (s a c oldT newT maxSlots m : Nat)
    (hs : s ≤ 230350301035) (ha : a ≤ s) (hl : 2043997771 ≤ a)
    (hc : c ≤ 8265980838) (ho : oldT ≤ 10220044629) (hn : 8176046859 ≤ newT)
    (hls : 4000000000000000 ≤ maxSlots) (hm : 8265980838 ≤ m) :
    s + 3*a + 2 ≤ maxSlots ∧ oldT + 1 ≤ newT + a ∧ c ≤ m := by omega

theorem certificate : Certificate officialLimits layout entry bounds := by
  have h := resourceArithmetic CompressedFive.entry.program.gateSlots (Catalyst.saved CompressedFive.entry.program)
    CompressedFive.entry.finalCursor CompressedFive.bounds.tModel bounds.tModel officialLimits.gateSlots bounds.measurements
    five_slots (Catalyst.saved_le_slots CompressedFive.entry.program) five_saved
    (cursor_bound officialLimits CompressedFive.layout CompressedFive.entry CompressedFive.bounds CompressedFive.certificate)
    (by decide) (by decide) (by decide) (by decide)
  apply Catalyst.compile_certificate officialLimits CompressedFive.layout CompressedFive.entry CompressedFive.bounds bounds
    1025 (1024 :: resetWires) CompressedFive.certificate five_within
  · simp [resetWires]
  · exact h.1
  · change (1024 :: resetWires).length + 1 ≤ 856
    simp [resetWires_length]
  · exact h.2.1
  · exact h.2.2
end
end ShorECDLP.Entrant.PreviousCurrent
end
