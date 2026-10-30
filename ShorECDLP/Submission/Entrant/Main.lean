import ShorECDLP.Submission.«2607_13816».Window.TableLookup
import ShorECDLP.Submission.«2607_13816».Challenge.SignedWindow
import ShorECDLP.Submission.«2607_13816».EEA.MeasuredAnd
import ShorECDLP.Challenge.StraightLine
import ShorECDLP.Framework.Quantum.AdaptiveFrame
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import ShorECDLP.Challenge.Contract
import ShorECDLP.Submission.«2607_13816».Challenge.Records
import ShorECDLP.Submission.«2607_13816».EEA.BlockAPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».Challenge.Coordinate
import ShorECDLP.Submission.«2607_13816».Challenge.CursorShift
import ShorECDLP.Submission.«2607_13816».EEA.MeasuredWrapperCounts
import ShorECDLP.Framework.Quantum.AdaptiveDisjoint
import ShorECDLP.Submission.Entrant.Single.Physical
import ShorECDLP.Submission.«2607_13816».Challenge.Support
import ShorECDLP.Submission.Entrant.Single.Fourier
import ShorECDLP.Challenge.Official
import ShorECDLP.Submission.«2607_13816».EEA.LengthPrimitiveCounts
import ShorECDLP.Framework.Quantum.InnerProduct
import ShorECDLP.Submission.«2607_13816».EEA.Preprocess
import ShorECDLP.Submission.«2607_13816».Challenge.OuterResources

section


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

def finePositions : List (Fin 918678076) :=
  Single.trialPositions.right.toList.attach.map fun i=>
    ⟨i.val,(Single.right_position_bound i.val i.property).2.trans (by decide)⟩
theorem finePositions_length : finePositions.length=207 := by
  simp [finePositions,Single.params]
def fineBits : Vector (Fin 918678076) 207 := Vector.ofFn fun i=>
  finePositions[i.val]'(by rw [finePositions_length];exact i.isLt)

def readout : Straight 901120 918678076 918695052 :=
  NeighborReadout.neighborSuffix 901120 918678076 207 fineBits

def program : Straight 901120 0 918695052 := Single.program.append readout

def positions (ps : Vector Nat 207) : TrialPositions NeighborReadout.params where
  left:=Single.trialPositions.left
  right:=ps

def layout : DecodeLayout := ⟨.wrappedShift,NeighborReadout.params,
  (NeighborReadout.rightWords fineBits).map positions,by
    simp only [List.length_map,NeighborReadout.rightWords_length];decide⟩

theorem readout_wellFormed : readout.WellFormed :=
  NeighborReadout.neighborSuffix_wellFormed _ _ _ _
theorem readout_t (read : ConstantBit 901120→Bool) (h : Fin 918678076→Bool) :
    (readout.instantiate read h).tCount=0 := NeighborReadout.neighborSuffix_t _ _ _ _ _ _
theorem readout_support (read : ConstantBit 901120→Bool) (h : Fin 918678076→Bool) :
    (readout.instantiate read h).wires⊆resetWires := by
  apply (NeighborReadout.neighborSuffix_support _ _ _ _ _ _).trans
  simp [List.subset_def,resetWires]

theorem fineBits_vals : fineBits.map Fin.val=Single.trialPositions.right := by
  apply Vector.ext
  intro i hi
  simp [fineBits,finePositions]
  rfl

theorem program_clean (read : ConstantBit 901120 → Bool) (b : InstrumentBranch)
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
    (read : ConstantBit 901120→Bool) (history : Fin 918678076→Bool)
    (ψ : State) (hψ : SupportedOn CleanReadout ψ)
    (hf : Single.Distribution.fineEvent (NeighborReadout.pairRecovered d) (List.ofFn history)=true)
    (b : InstrumentBranch) (hb : b∈(readout.instantiate read history).run)
    (hn : b.kraus ψ≠0) :
    (verifiedCandidate layout Q (List.ofFn history++b.history)).isSome := by
  have hr:=NeighborReadout.input_read fineBits history
  rw [fineBits_vals] at hr
  obtain ⟨a,ha,hp⟩:=pairAccept_value _ _ _ _ _ hr hf
  obtain ⟨i,hi⟩:=of_decide_eq_true hp
  obtain ⟨ps,hps,hread⟩:=NeighborReadout.neighborSuffix_reads 901120 918678076 fineBits
    read history ψ hψ b hb hn ((i.val : ℤ)-13) (by have h:=i.isLt;omega)
  apply verified_of_reads ps hps Q d hd _ a _ _ hread hi
  rw [NeighborReadout.readWord_append_left]
  · exact ha
  · intro j hj
    have h:=Single.left_position_bound j hj
    simpa only [List.length_ofFn] using h.trans (by decide : 506915158<918678076)

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
    have hlen : a.history.length = 918678076 := by
      have h := straight_history_length Single.program (readConstant Single.mixedCoefficientAt Q) Fin.elim0 a ha
      omega
    have hh : List.ofFn (Single.historyAfter 918678076 Fin.elim0 a.history) = a.history := by
      simpa only [List.ofFn_zero, List.nil_append] using Single.historyAfter_list Fin.elim0 a.history (by simpa only [Nat.zero_add] using hlen)
    have h := suffix_accept Q d hd (readConstant Single.mixedCoefficientAt Q)
      (Single.historyAfter 918678076 Fin.elim0 a.history) (a.kraus (ket zeroBasisState))
      (program_clean _ a ha _) (by simpa only [hh] using hf) b hb hne
    simpa only [hh, InstrumentBranch.seq] using h

def entry : StraightEntry := Single.fixedEntry Single.mixedCoefficientAt program

def bounds : Bounds := ⟨854, 14542749163, 918695052⟩

theorem program_wellFormed : program.WellFormed :=
  straight_append_wellFormed _ _ Single.program_wellFormed readout_wellFormed

theorem program_support (read : ConstantBit 901120 → Bool) :
    (program.instantiate read Fin.elim0).wires ⊆ resetWires :=
  outer_append_support _ _ read Fin.elim0 resetWires (Single.program_support read)
    (readout_support read)

theorem program_qubits (read : ConstantBit 901120 → Bool) :
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
    (program.instantiate (readConstant Single.mixedCoefficientAt Q) Fin.elim0).tCount ≤ 14542749163 := by
  have h := outer_append_t_le Single.program readout (readConstant Single.mixedCoefficientAt Q)
    Fin.elim0 0 (fun history => le_of_eq (readout_t _ history))
  rw [Nat.add_zero] at h
  change ((Single.program.append readout).instantiate (readConstant Single.mixedCoefficientAt Q) Fin.elim0).tCount ≤ 14542749163
  exact h.trans (Single.program_t Q)

theorem program_slots : program.gateSlots ≤ 90000176648 := by
  unfold program
  rw [Straight.gateSlots_append]
  have hr : readout.gateSlots=59416 := by
    unfold readout
    exact NeighborReadout.neighborSuffix_slots 901120 918678076 207 fineBits
  rw [hr]
  have h := Single.program_slots
  omega

theorem certificate : Certificate officialLimits layout entry bounds where
  gateBudget := by
    rw [entry, Single.fixedEntry_slots]
    exact program_slots.trans (by decide)
  recordBudget := by
    change 918695052 ≤ officialLimits.measurements
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

theorem quantum_commute (a b : Gate) (hc : commutes a b = true)
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


namespace ShorECDLP.Entrant.Initializer
open Quantum Paper2607_13816
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def prefixTail (acc : Wire) : List Wire → List Wire → Circuit
  | [], _ => []
  | [_], _ => []
  | c :: d :: cs, s :: ss => .CCX c acc s :: prefixTail s (d :: cs) ss
  | _ :: _ :: _, [] => []

def leafTail (acc : Wire) : List Wire → Wire → List Wire → Circuit
  | [], _, _ => []
  | [c], t, _ => [.CCX c acc t]
  | _ :: d :: cs, t, s :: ss => leafTail s (d :: cs) t ss
  | _ :: _ :: _, _, [] => []

def chainPrefix : List Wire → List Wire → Circuit
  | a :: b :: cs, ss => prefixTail b (a :: cs) ss
  | _, _ => []

def leaf : List Wire → Wire → List Wire → Circuit
  | [], t, _ => [.X t]
  | [a], t, _ => [.CX a t]
  | a :: b :: cs, t, ss => leafTail b (a :: cs) t ss

theorem tail_factor (acc : Wire) (cs : List Wire) (t : Wire) (ss : List Wire) :
    mcxVChainTail acc cs t ss = prefixTail acc cs ss ++ leafTail acc cs t ss ++ (prefixTail acc cs ss).adjoint := by
  induction cs generalizing acc ss with
  | nil => rfl
  | cons c cs ih =>
    cases cs with
    | nil => rfl
    | cons d cs =>
      cases ss with
      | nil => rfl
      | cons s ss =>
        simp only [mcxVChainTail, prefixTail, leafTail, ih, circuit_adjoint_cons,
          Gate.adjoint, List.cons_append, List.append_assoc, List.nil_append]

theorem factor (cs : List Wire) (t : Wire) (ss : List Wire) :
    mcxVChain cs t ss = chainPrefix cs ss ++ leaf cs t ss ++ (chainPrefix cs ss).adjoint := by
  cases cs with
  | nil => rfl
  | cons a cs =>
    cases cs with
    | nil => rfl
    | cons b cs => exact tail_factor b (a::cs) t ss

def before (cs : List Wire) (pat : Nat) (ss : List Wire) (v : Nat) : Circuit :=
  zeroMask cs pat ++ xorConstant ss v ++ chainPrefix cs ss

def after (cs : List Wire) (pat : Nat) (ss : List Wire) (v : Nat) : Circuit :=
  (chainPrefix cs ss).adjoint ++ xorConstant ss v ++ (zeroMask cs pat).adjoint

theorem known_factor (cs : List Wire) (pat : Nat) (t : Wire) (ss : List Wire) (v : Nat) :
    knownScratchControl cs pat t ss v = before cs pat ss v ++ leaf cs t ss ++ after cs pat ss v := by
  simp only [knownScratchControl,knownScratchMCX,factor,before,after,List.append_assoc]

def pairwiseCommutes (a b : Circuit) : Bool :=
  a.all fun x => b.all fun y => Cancellation.commutes x y

theorem gate_circuit_commute (g : Gate) (c : Circuit)
    (h : ∀ a ∈ c, Cancellation.commutes g a = true) (ψ : State) :
    applyGate g (Quantum.run c ψ) = Quantum.run c (applyGate g ψ) := by
  induction c generalizing ψ with
  | nil => rfl
  | cons a c ih =>
    simp only [Quantum.run_cons]
    rw [ih (fun b hb => h b (by simp [hb])), Cancellation.quantum_commute g a (h a (by simp))]

theorem circuit_commute (a b : Circuit) (h : pairwiseCommutes a b = true) (ψ : State) :
    Quantum.run a (Quantum.run b ψ) = Quantum.run b (Quantum.run a ψ) := by
  induction a generalizing ψ with
  | nil => rfl
  | cons g a ih =>
    have hh : (∀ x ∈ b, Cancellation.commutes g x = true) ∧ pairwiseCommutes a b = true := by
      simpa only [pairwiseCommutes,List.all_cons,Bool.and_eq_true,List.all_eq_true] using h
    simp only [Quantum.run_cons]
    rw [gate_circuit_commute g b hh.1, ih hh.2]

theorem xor_twice (ss : List Wire) (v : Nat) (hn : ss.Nodup) (ψ : State) :
    Quantum.run (xorConstant ss v) (Quantum.run (xorConstant ss v) ψ) = ψ := by
  induction ψ using Finsupp.induction with
  | zero => simp only [map_zero]
  | @single_add s c ψ hs hc ih =>
    have he : Finsupp.single s c = c • ket s := by simp [ket]
    simp only [map_add,he,map_smul,run_ket_agrees_classical _ _ (xorConstant_HPFree ss v),run_xorConstant_twice ss v s hn,ih]

theorem before_after (cs : List Wire) (pat : Nat) (ss : List Wire) (v : Nat)
    (hn : ss.Nodup) (hp : CircuitWellFormed (chainPrefix cs ss)) (ψ : State) :
    Quantum.run (before cs pat ss v) (Quantum.run (after cs pat ss v) ψ) = ψ := by
  simp only [before,after,Quantum.run_append]
  rw [Quantum.run_run_adjoint _ (zeroMask_wellFormed cs pat),xor_twice ss v hn,
    Quantum.run_run_adjoint _ hp]

def reducedCase (cs : List Wire) (pat : Nat) (ts : List Wire) (encoded : Nat)
    (flag : Wire) (ss : List Wire) (v : Nat) : Circuit :=
  before cs pat ss v ++ leaf cs flag ss ++ controlledXorConstant flag ts encoded ++
    leaf cs flag ss ++ after cs pat ss v

theorem reducedCase_run (cs : List Wire) (pat : Nat) (ts : List Wire) (encoded : Nat)
    (flag : Wire) (ss : List Wire) (v : Nat)
    (hn : ss.Nodup) (hp : CircuitWellFormed (chainPrefix cs ss))
    (hc : pairwiseCommutes (after cs pat ss v) (controlledXorConstant flag ts encoded) = true) :
    Quantum.run (lengthInitializeCase cs pat ts encoded flag ss v) =
      Quantum.run (reducedCase cs pat ts encoded flag ss v) := by
  apply LinearMap.ext
  intro ψ
  simp only [lengthInitializeCase,known_factor,reducedCase,Quantum.run_append]
  rw [← circuit_commute _ _ hc, before_after cs pat ss v hn hp]

theorem reducedCase_sublist (cs : List Wire) (pat : Nat) (ts : List Wire) (encoded : Nat)
    (flag : Wire) (ss : List Wire) (v : Nat) :
    (reducedCase cs pat ts encoded flag ss v).Sublist (lengthInitializeCase cs pat ts encoded flag ss v) := by
  simp only [lengthInitializeCase,known_factor,reducedCase,List.append_assoc]
  apply List.Sublist.append_left
  apply List.Sublist.append_left
  apply List.Sublist.trans _ (List.sublist_append_right (after cs pat ss v) _)
  apply List.Sublist.append_left
  exact List.sublist_append_right (before cs pat ss v) _
end ShorECDLP.Entrant.Initializer
namespace ShorECDLP.Entrant.Initializer
open Quantum Paper2607_13816
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem reducedCase_t (cs : List Wire) (pat : Nat) (ts : List Wire) (encoded : Nat)
    (flag : Wire) (ss : List Wire) (v : Nat) :
    ShorECDLP.tCount (reducedCase cs pat ts encoded flag ss v) +
      2 * ShorECDLP.tCount (chainPrefix cs ss) =
      ShorECDLP.tCount (lengthInitializeCase cs pat ts encoded flag ss v) := by
  simp only [lengthInitializeCase,known_factor,reducedCase,before,after,
    ShorECDLP.tCount_append,ShorECDLP.tCount_adjoint,zeroMask_tCount,xorConstant_tCount]
  omega

def rows := lengthInitializeCases (List.range' 266 256) 9
def targets := List.range' 549 9
def scratch := (List.range' 7 256).reverse.take 254
def modulus := 2^256-2^32-977

def scan : List (List Wire × Nat × Nat) → Circuit
  | [] => []
  | (cs,pat,encoded)::rs => reducedCase cs pat targets encoded 558 scratch modulus ++ scan rs

def saving : List (List Wire × Nat × Nat) → Nat
  | [] => 0
  | (cs,_,_)::rs => 2 * ShorECDLP.tCount (chainPrefix cs scratch) + saving rs

def Good (row : List Wire × Nat × Nat) : Prop :=
  CircuitWellFormed (chainPrefix row.1 scratch) ∧
  pairwiseCommutes (after row.1 row.2.1 scratch modulus)
    (controlledXorConstant 558 targets row.2.2) = true

private theorem scratch_nodup : scratch.Nodup :=
  (List.take_sublist 254 (List.range' 7 256).reverse).nodup
    (List.nodup_reverse.mpr List.nodup_range')

private theorem scratch_bounds (w : Wire) (hw : w∈scratch) : 7≤w ∧ w<263 := by
  have h := List.mem_reverse.mp (List.mem_of_mem_take hw)
  simpa only [List.mem_range'_1] using h

theorem scan_run (rs : List (List Wire × Nat × Nat)) (h : ∀ row ∈ rs, Good row) :
    Quantum.run (lengthInitializeScan targets 558 scratch modulus rs) = Quantum.run (scan rs) := by
  induction rs with
  | nil => rfl
  | cons row rs ih =>
    obtain ⟨cs,pat,encoded⟩ := row
    simp only [lengthInitializeScan,scan,Quantum.run_append_map]
    rw [reducedCase_run cs pat targets encoded 558 scratch modulus scratch_nodup
      (h (cs,pat,encoded) (by simp)).1 (h (cs,pat,encoded) (by simp)).2,ih (fun row hr => h row (by simp [hr]))]

theorem scan_sublist (rs : List (List Wire × Nat × Nat)) :
    (scan rs).Sublist (lengthInitializeScan targets 558 scratch modulus rs) := by
  induction rs with
  | nil => exact List.Sublist.refl _
  | cons row rs ih => exact (reducedCase_sublist _ _ _ _ _ _ _).append ih

theorem scan_t (rs : List (List Wire × Nat × Nat)) :
    ShorECDLP.tCount (scan rs) + saving rs =
      ShorECDLP.tCount (lengthInitializeScan targets 558 scratch modulus rs) := by
  induction rs with
  | nil => rfl
  | cons row rs ih =>
    obtain ⟨cs,pat,encoded⟩ := row
    simp only [scan,saving,lengthInitializeScan,ShorECDLP.tCount_append]
    have hr := reducedCase_t cs pat targets encoded 558 scratch modulus
    omega

private instance gateWFDecidable (g : Gate) : Decidable g.WellFormed := by
  cases g <;> unfold Gate.WellFormed <;> infer_instance

end ShorECDLP.Entrant.Initializer
namespace ShorECDLP.Entrant.Initializer
open Quantum Paper2607_13816 Classical
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem prefix_sublist (cs : List Wire) (t : Wire) (ss : List Wire) :
    (chainPrefix cs ss).Sublist (mcxVChain cs t ss) := by
  rw [factor]
  exact (List.sublist_append_left _ _).trans (List.sublist_append_left _ _)

theorem prefix_support (cs ss : List Wire) : PaperCircuitUsesOnly (cs ++ ss) (chainPrefix cs ss) := by
  intro g hg w hw
  have h0 := mcxVChain_usesOnly cs 0 ss g ((prefix_sublist cs 0 ss).subset hg) w hw
  have h1 := mcxVChain_usesOnly cs 1 ss g ((prefix_sublist cs 1 ss).subset hg) w hw
  simp only [List.mem_append,List.mem_cons] at *
  aesop

theorem after_support (cs : List Wire) (pat : Nat) (ss : List Wire) (v : Nat) :
    PaperCircuitUsesOnly (cs ++ ss) (after cs pat ss v) := by
  unfold after
  exact (prefix_support cs ss).adjoint.append ((xorConstant_usesOnly ss v).mono
    (fun w hw => List.mem_append_right _ hw)) |>.append
      ((zeroMask_usesOnly cs pat).adjoint.mono (fun w hw => List.mem_append_left _ hw))

theorem after_classical (cs : List Wire) (pat : Nat) (ss : List Wire) (v : Nat) :
    HPFree (after cs pat ss v) := by
  have h := knownScratchControl_HPFree cs pat 0 ss v
  rw [known_factor] at h
  intro g hg
  exact h g (by simp [hg])

theorem disjoint_commutes (a b : Circuit) (xs ys : List Wire)
    (ha : HPFree a) (hb : HPFree b) (hsa : PaperCircuitUsesOnly xs a)
    (hsb : PaperCircuitUsesOnly ys b) (hd : List.Disjoint xs ys) :
    pairwiseCommutes a b = true := by
  simp only [pairwiseCommutes,List.all_eq_true]
  intro g hg k hk
  have hga := ha g hg
  have hkb := hb k hk
  have hdis : ∀ w ∈ gateWires g, w ∉ gateWires k := by
    intro w hw hn
    exact List.disjoint_left.mp hd (hsa g hg w hw) (hsb k hk w hn)
  cases g <;> cases k <;>
    simp_all [IsClassicalGate,Cancellation.commutes,Cancellation.classicalGate,
      Cancellation.controls,Cancellation.target,gateWires]
  all_goals aesop

private theorem full_layout : ((List.range' 266 256) ++ 558 :: scratch).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨List.nodup_range',?_,?_⟩
  · apply List.nodup_cons.mpr
    refine ⟨?_,scratch_nodup⟩
    intro h
    have hb := scratch_bounds 558 h
    dsimp only [Wire] at hb
    omega
  · intro a ha b hb he
    have ha' : 266≤a ∧ a<522 := by simpa only [List.mem_range'_1] using ha
    rcases List.mem_cons.mp hb with hb | hb
    · omega
    · have hb' := scratch_bounds b hb
      dsimp only [Wire] at *
      omega

theorem good_for (cs : List Wire) (pat enc : Nat) (hcs : cs.Sublist (List.range' 266 256)) :
    Good (cs,pat,enc) := by
  have hlen := hcs.length_le
  have hcap : cs.length-2 ≤ scratch.length := by
    have hs : scratch.length=254 := by decide
    simp only [List.length_range'] at hlen
    omega
  have hlay : McxVChainLayout cs 558 scratch :=
    (hcs.append (List.Sublist.refl _)).nodup full_layout
  constructor
  · intro g hg
    exact mcxVChain_wellFormed cs 558 scratch hcap hlay g ((prefix_sublist cs 558 scratch).subset hg)
  · apply disjoint_commutes _ _ (cs++scratch) (558::targets)
      (after_classical _ _ _ _) (controlledXorConstant_HPFree _ _ _)
      (after_support _ _ _ _) (controlledXorConstant_usesOnly _ _ _)
    apply List.disjoint_left.mpr
    intro w hw hn
    have hlo : w < 549 := by
      rcases List.mem_append.mp hw with hw | hw
      · have hh := hcs.subset hw
        simp only [List.mem_range',Nat.one_mul] at hh
        rcases hh with ⟨i, hi, rfl⟩
        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi _) (by decide)
      · have hh := List.mem_of_mem_take (show w ∈ (List.range' 7 256).reverse.take 254 from hw)
        simp only [List.mem_reverse,List.mem_range',Nat.one_mul] at hh
        rcases hh with ⟨i, hi, rfl⟩
        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi _) (by decide)
    simp only [List.mem_cons,targets,List.mem_range',Nat.one_mul] at hn
    rcases hn with rfl | ⟨i, hi, rfl⟩
    · exact (by decide : ¬ (558:Nat) < 549) hlo
    · exact Nat.not_lt_of_ge (Nat.le_add_right 549 i) hlo

theorem rows_good : ∀ row ∈ rows, Good row := by
  intro row hr
  simp only [rows,lengthInitializeCases,List.mem_append,List.mem_map,List.mem_range,
    List.mem_singleton] at hr
  rcases hr with ⟨i,hi,rfl⟩ | rfl
  · exact good_for _ _ _ (List.take_sublist _ _)
  · exact good_for _ _ _ (List.Sublist.refl _)


theorem initializer_run : Quantum.run (lengthInitialize (List.range' 266 256) targets 558 scratch modulus) =
    Quantum.run (scan rows) := scan_run rows rows_good

theorem initializer_sublist : (scan rows).Sublist (lengthInitialize (List.range' 266 256) targets 558 scratch modulus) := scan_sublist rows


end ShorECDLP.Entrant.Initializer
namespace ShorECDLP.Entrant.Initializer
open Quantum Paper2607_13816
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

abbrev Row := List Wire × Nat × Nat

def mid (r : Row) : Circuit := leaf r.1 558 scratch ++
  controlledXorConstant 558 targets r.2.2 ++ leaf r.1 558 scratch

def extension (a b : Row) : Circuit :=
  (chainPrefix b.1 scratch).drop (chainPrefix a.1 scratch).length

def transition (a b : Row) : Circuit := [.X (a.1.getLastD 0)] ++ extension a b

def Compatible (a b : Row) : Prop :=
  zeroMask b.1 b.2.1 = zeroMask a.1 a.2.1 ++ [.X (a.1.getLastD 0)] ∧
  chainPrefix b.1 scratch = chainPrefix a.1 scratch ++ extension a b ∧
  pairwiseCommutes [.X (a.1.getLastD 0)] (chainPrefix a.1 scratch) = true ∧
  pairwiseCommutes [.X (a.1.getLastD 0)] (xorConstant scratch modulus) = true

instance compatibleDecidable (a b : Row) : Decidable (Compatible a b) := by
  unfold Compatible
  infer_instance

theorem boundary_run (a b : Row) (hg : Good a) (h : Compatible a b) (ψ : State) :
    Quantum.run (after a.1 a.2.1 scratch modulus ++ before b.1 b.2.1 scratch modulus) ψ =
      Quantum.run (transition a b) ψ := by
  rcases h with ⟨hm,hp,hcp,hcx⟩
  simp only [after,before,transition,hm,hp,Quantum.run_append]
  rw [Quantum.run_run_adjoint _ (zeroMask_wellFormed _ _)]
  rw [← circuit_commute _ _ hcx]
  rw [xor_twice scratch modulus scratch_nodup]
  rw [← circuit_commute _ _ hcp]
  rw [Quantum.run_run_adjoint _ hg.1]

theorem boundary_sublist (a b : Row) (h : Compatible a b) :
    (transition a b).Sublist (after a.1 a.2.1 scratch modulus ++ before b.1 b.2.1 scratch modulus) := by
  rcases h with ⟨hm,hp,_,_⟩
  apply List.Sublist.trans _ (List.sublist_append_right _ _)
  simp only [transition,before,hm,hp,List.append_assoc]
  apply List.Sublist.trans _ (List.sublist_append_right _ _)
  exact (List.Sublist.refl _).append
    ((List.sublist_append_right _ _).trans (List.sublist_append_right _ _))

theorem boundary_t (a b : Row) (h : Compatible a b) :
    ShorECDLP.tCount (transition a b) + 2 * ShorECDLP.tCount (chainPrefix a.1 scratch) =
      ShorECDLP.tCount (after a.1 a.2.1 scratch modulus ++ before b.1 b.2.1 scratch modulus) := by
  rcases h with ⟨_,hp,_,_⟩
  simp only [transition,after,before,hp,ShorECDLP.tCount_append,
    ShorECDLP.tCount_adjoint,zeroMask_tCount,xorConstant_tCount]
  simp only [ShorECDLP.tCount,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,ShorECDLP.tCost]
  omega

/-- Emit the current row's middle, sharing adjacent chain prefixes. -/
def sharedTail (a : Row) : List Row → Circuit
  | [] => mid a ++ after a.1 a.2.1 scratch modulus
  | b::rs => mid a ++ transition a b ++ sharedTail b rs

def shared : List Row → Circuit
  | [] => []
  | a::rs => before a.1 a.2.1 scratch modulus ++ sharedTail a rs

def sharingSaving (a : Row) : List Row → Nat
  | [] => 0
  | b::rs => 2 * ShorECDLP.tCount (chainPrefix a.1 scratch) + sharingSaving b rs


theorem sharedTail_run (a : Row) (rs : List Row)
    (hg : ∀ r ∈ a::rs, Good r) (hc : (a::rs).IsChain Compatible) (ψ : State) :
    Quantum.run (sharedTail a rs) ψ =
      Quantum.run (mid a ++ after a.1 a.2.1 scratch modulus ++ scan rs) ψ := by
  induction rs generalizing a ψ with
  | nil => simp only [sharedTail,scan,List.append_nil]
  | cons b rs ih =>
    have hh := List.isChain_cons_cons.mp hc
    have hb : ∀ r ∈ b::rs, Good r := fun r hr => hg r (List.mem_cons_of_mem _ hr)
    simp only [sharedTail,Quantum.run_append]
    rw [ih b hb hh.2]
    simp only [scan,reducedCase,mid,Quantum.run_append]
    have he := boundary_run a b (hg a (by simp)) hh.1
    simp only [Quantum.run_append] at he
    rw [← he]

theorem sharedTail_sublist (a : Row) (rs : List Row)
    (hc : (a::rs).IsChain Compatible) :
    (sharedTail a rs).Sublist (mid a ++ after a.1 a.2.1 scratch modulus ++ scan rs) := by
  induction rs generalizing a with
  | nil => simp only [sharedTail,scan,List.append_nil];exact List.Sublist.refl _
  | cons b rs ih =>
    have hh := List.isChain_cons_cons.mp hc
    have hs := (List.Sublist.refl (mid a)).append
      ((boundary_sublist a b hh.1).append (ih b hh.2))
    simpa only [sharedTail,scan,reducedCase,mid,List.append_assoc] using hs

theorem scan_cons_t (r : Row) (rs : List Row) :
    ShorECDLP.tCount (scan (r::rs)) = ShorECDLP.tCount (before r.1 r.2.1 scratch modulus) +
      ShorECDLP.tCount (mid r) + ShorECDLP.tCount (after r.1 r.2.1 scratch modulus) + ShorECDLP.tCount (scan rs) := by
  obtain ⟨cs,pat,enc⟩ := r
  simp only [scan,reducedCase,mid,ShorECDLP.tCount_append]
  omega

theorem sharedTail_t (a : Row) (rs : List Row)
    (hc : (a::rs).IsChain Compatible) :
    ShorECDLP.tCount (sharedTail a rs) + sharingSaving a rs =
      ShorECDLP.tCount (mid a ++ after a.1 a.2.1 scratch modulus ++ scan rs) := by
  induction rs generalizing a with
  | nil => simp only [sharedTail,sharingSaving,scan,List.append_nil,Nat.add_zero]
  | cons b rs ih =>
    have hh := List.isChain_cons_cons.mp hc
    have ht := boundary_t a b hh.1
    have hi := ih b hh.2
    simp only [ShorECDLP.tCount_append] at ht hi
    simp only [sharedTail,sharingSaving,ShorECDLP.tCount_append,scan_cons_t]
    omega


def sharedSaving : List Row → Nat
  | [] => 0
  | a::rs => sharingSaving a rs

theorem shared_run (rs : List Row) (hg : ∀ r ∈ rs, Good r) (hc : rs.IsChain Compatible) :
    Quantum.run (shared rs) = Quantum.run (scan rs) := by
  apply LinearMap.ext
  intro ψ
  cases rs with
  | nil => rfl
  | cons a rs =>
    simp only [shared,Quantum.run_append]
    rw [sharedTail_run a rs hg hc]
    simp only [scan,reducedCase,mid,Quantum.run_append]

theorem shared_sublist (rs : List Row) (hc : rs.IsChain Compatible) :
    (shared rs).Sublist (scan rs) := by
  cases rs with
  | nil => exact List.Sublist.refl _
  | cons a rs =>
    have h := (List.Sublist.refl (before a.1 a.2.1 scratch modulus)).append (sharedTail_sublist a rs hc)
    simpa only [shared,scan,reducedCase,mid,List.append_assoc] using h

theorem shared_t (rs : List Row) (hc : rs.IsChain Compatible) :
    ShorECDLP.tCount (shared rs) + sharedSaving rs = ShorECDLP.tCount (scan rs) := by
  cases rs with
  | nil => rfl
  | cons a rs =>
    have h := sharedTail_t a rs hc
    simp only [ShorECDLP.tCount_append] at h
    simp only [shared,sharedSaving,ShorECDLP.tCount_append,scan_cons_t]
    omega

end ShorECDLP.Entrant.Initializer
namespace ShorECDLP.Entrant.Initializer
open Quantum Paper2607_13816
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-- A Boolean equality certificate for the X/CCX fragment used in chain boundaries. -/
def sameGate : Gate → Gate → Bool
  | .X a, .X b => a == b
  | .CCX a b c, .CCX d e f => (a == d) && (b == e) && (c == f)
  | _, _ => false

def sameCircuit : Circuit → Circuit → Bool
  | [], [] => true
  | a::as, b::bs => sameGate a b && sameCircuit as bs
  | _, _ => false

theorem sameGate_eq (a b : Gate) (h : sameGate a b = true) : a = b := by
  cases a <;> cases b <;> simp_all [sameGate,Bool.and_eq_true]

theorem sameCircuit_eq (a b : Circuit) (h : sameCircuit a b = true) : a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [sameCircuit]
  | cons a as ih =>
    cases b with
    | nil => simp [sameCircuit] at h
    | cons b bs =>
      simp only [sameCircuit,Bool.and_eq_true] at h
      rw [sameGate_eq a b h.1,ih bs h.2]

def compatibleCheck (a b : Row) : Bool :=
  sameCircuit (zeroMask b.1 b.2.1) (zeroMask a.1 a.2.1 ++ [.X (a.1.getLastD 0)]) &&
  sameCircuit (chainPrefix b.1 scratch) (chainPrefix a.1 scratch ++ extension a b) &&
  pairwiseCommutes [.X (a.1.getLastD 0)] (chainPrefix a.1 scratch) &&
  pairwiseCommutes [.X (a.1.getLastD 0)] (xorConstant scratch modulus)

theorem compatibleCheck_sound (a b : Row) (h : compatibleCheck a b = true) : Compatible a b := by
  simp only [compatibleCheck,Bool.and_eq_true] at h
  exact ⟨sameCircuit_eq _ _ h.1.1.1,sameCircuit_eq _ _ h.1.1.2,h.1.2,h.2⟩

def chainCheck : List Row → Bool
  | [] => true
  | [_] => true
  | a::b::rs => compatibleCheck a b && chainCheck (b::rs)

theorem chainCheck_sound (rs : List Row) (h : chainCheck rs = true) : rs.IsChain Compatible := by
  induction rs with
  | nil => exact List.isChain_nil
  | cons a rs ih =>
    cases rs with
    | nil => exact List.isChain_singleton _
    | cons b rs =>
      simp only [chainCheck,Bool.and_eq_true] at h
      exact List.isChain_cons_cons.mpr ⟨compatibleCheck_sound a b h.1,ih h.2⟩

private theorem rows_check : chainCheck rows = true := by decide +kernel

theorem rows_compatible_fast : rows.IsChain Compatible := chainCheck_sound rows rows_check
end ShorECDLP.Entrant.Initializer
namespace ShorECDLP.Entrant.Initializer
open Quantum Paper2607_13816
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

private theorem rows_compatible : rows.IsChain Compatible := rows_compatible_fast

theorem initializer_shared_run :
    Quantum.run (lengthInitialize (List.range' 266 256) targets 558 scratch modulus) =
      Quantum.run (shared rows) := initializer_run.trans (shared_run rows rows_good rows_compatible).symm

theorem initializer_shared_sublist : (shared rows).Sublist
    (lengthInitialize (List.range' 266 256) targets 558 scratch modulus) :=
  (shared_sublist rows rows_compatible).trans initializer_sublist


end ShorECDLP.Entrant.Initializer

namespace ShorECDLP.Entrant.Initializer
open Paper2607_13816 ShorECDLP.Classical
/-- On the classical gate fragment, the protected cost is seven per Toffoli. -/
theorem classical_toffoli_cost (c : Circuit) (hf : HPFree c) :
    ShorECDLP.tCount c = 7 * eeaToffoliCount c := by
  induction c with
  | nil => rfl
  | cons g c ih =>
    have hg : IsClassicalGate g := hf g (by simp)
    have ht : HPFree c := fun k hk => hf k (by simp [hk])
    cases g <;> simp_all [ShorECDLP.tCount,ShorECDLP.tCost,eeaToffoliCount]
    omega



end ShorECDLP.Entrant.Initializer

namespace ShorECDLP.Entrant.Optimization
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration

structure LiteralBound (xs ys : Circuit) (k : Nat) : Prop where
  wf : CircuitWellFormed ys
  slots : ys.length ≤ xs.length
  cost : tCount ys + k = tCount xs
  support : circuitWires ys ⊆ circuitWires xs
  eligible : 7 * eeaToffoliCount xs ≤ 7 * eeaToffoliCount ys + k

theorem literal_relabel_wires (f : Wire ≃ Wire) (xs : Circuit) :
    circuitWires (xs.map (Gate.relabel f)) = (circuitWires xs).map f := by
  induction xs with
  | nil => rfl
  | cons g gs ih => cases g <;> simp_all [circuitWires,gateWires,Gate.relabel]

theorem literal_relabel_t (f : Wire ≃ Wire) (xs : Circuit) :
    tCount (xs.map (Gate.relabel f)) = tCount xs := by
  induction xs with
  | nil => rfl
  | cons g gs ih => cases g <;> simp_all [tCount,tCost,Gate.relabel]

theorem literal_relabel_ccx (f : Wire ≃ Wire) (xs : Circuit) :
    eeaToffoliCount (xs.map (Gate.relabel f)) = eeaToffoliCount xs := by
  induction xs with
  | nil => rfl
  | cons g gs ih => cases g <;> simp_all [eeaToffoliCount,Gate.relabel]

theorem LiteralBound.relabel {xs ys : Circuit} {k : Nat} (h : LiteralBound xs ys k)
    (f : Wire ≃ Wire) : LiteralBound (xs.map (Gate.relabel f)) (ys.map (Gate.relabel f)) k := by
  refine ⟨?_,by simpa using h.slots,by simpa only [literal_relabel_t] using h.cost,?_,
    by simpa only [literal_relabel_ccx] using h.eligible⟩
  · intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    have hw := h.wf a ha
    cases a <;> simp_all [Gate.relabel,Gate.WellFormed,f.injective.eq_iff]
  · rw [literal_relabel_wires,literal_relabel_wires]
    intro w hw
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
    exact List.mem_map.mpr ⟨v,h.support hv,rfl⟩

def literalPrefix {n s e} (xs : Circuit) (p : Straight n s e) : Straight n s e :=
  (literalProgram xs).append p

theorem literalPrefix_done {n s} (xs : Circuit) :
    literalPrefix xs (Straight.done : Straight n s s) = literalProgram xs := by
  induction xs <;> simp_all [literalPrefix,literalProgram,gateProgram,Straight.append]

theorem literalPrefix_wf {n s e} (xs : Circuit) (p : Straight n s e) :
    (literalPrefix xs p).WellFormed ↔ CircuitWellFormed xs ∧ p.WellFormed := by
  induction xs with
  | nil => simp [literalPrefix,literalProgram,gateProgram,Straight.append,CircuitWellFormed]
  | cons g gs ih =>
    simp only [literalPrefix,literalProgram,List.map_cons,gateProgram,Straight.append,
      Straight.WellFormed,TemplateGate.WellFormed] at ih ⊢
    simp only [CircuitWellFormed,List.mem_cons,forall_eq_or_imp] at ih ⊢
    tauto

theorem literalPrefix_slots {n s e} (xs : Circuit) (p : Straight n s e) :
    (literalPrefix xs p).gateSlots = xs.length + p.gateSlots := by
  induction xs <;> simp_all [literalPrefix,literalProgram,gateProgram,Straight.append,Straight.gateSlots,Nat.add_assoc,Nat.add_left_comm]

theorem literalPrefix_t {n s e} (xs : Circuit) (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    ((literalPrefix xs p).instantiate read history).tCount = tCount xs + (p.instantiate read history).tCount := by
  induction xs <;> simp_all [literalPrefix,literalProgram,gateProgram,Straight.append,Straight.instantiate,TemplateGate.instantiate,AdaptiveCircuit.tCount,tCount,Nat.add_assoc]

theorem literalPrefix_wires {n s e} (xs : Circuit) (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    ((literalPrefix xs p).instantiate read history).wires = circuitWires xs ++ (p.instantiate read history).wires := by
  induction xs <;> simp_all [literalPrefix,literalProgram,gateProgram,Straight.append,Straight.instantiate,TemplateGate.instantiate,AdaptiveCircuit.wires,circuitWires,List.append_assoc]

theorem literalPrefix_append {n s e f} (xs : Circuit) (p : Straight n s e) (q : Straight n e f) :
    (literalPrefix xs p).append q = literalPrefix xs (p.append q) := by
  induction xs <;> simp_all [literalPrefix,literalProgram,gateProgram,Straight.append]

theorem literalPrefix_reindex {n m s e} (f : Fin n → Fin m) (xs : Circuit) (p : Straight n s e) :
    reindexStraight f (literalPrefix xs p) = literalPrefix xs (reindexStraight f p) := by
  induction xs <;> simp_all [literalPrefix,literalProgram,gateProgram,Straight.append,reindexStraight,reindexGate]

theorem literalPrefix_relabel {n s e} (f : Wire ≃ Wire) (xs : Circuit) (p : Straight n s e) :
    relabelStraight f (literalPrefix xs p) = literalPrefix (xs.map (Gate.relabel f)) (relabelStraight f p) := by
  induction xs <;> simp_all [literalPrefix,literalProgram,gateProgram,Straight.append,relabelStraight,relabelTemplateGate]

theorem literalPrefix_shift {n s e} (k : Nat) (xs : Circuit) (p : Straight n s e) :
    shiftStraight k (literalPrefix xs p) = literalPrefix xs (shiftStraight k p) := by
  induction xs <;> simp_all [literalPrefix,literalProgram,gateProgram,Straight.append,shiftStraight]
end ShorECDLP.Entrant.Optimization

namespace ShorECDLP.Entrant.Optimization
open Quantum Challenge Paper2607_13816.ChallengeMigration

/-- A certified resource reduction retaining every measurement and classical control. -/
inductive Drops {n : Nat} : {s e : Nat} → Straight n s e → Straight n s e → Nat → Prop
  | refl {s e} (p : Straight n s e) : Drops p p 0
  | skip {s e} (g : Gate) {p q : Straight n s e} {d : Nat} :
      Drops p q d → Drops (.gate (.literal g) p) q (tCost g + d)
  | skipRecord {s e} (i : Fin s) (v : Bool) (g : Gate) {p q : Straight n s e} {d : Nat} :
      tCost g = 0 → Drops p q d → Drops (.recordGate i v g p) q d
  | gate {s e} (g : TemplateGate n) {p q : Straight n s e} {d : Nat} :
      Drops p q d → Drops (.gate g p) (.gate g q) d
  | record {s e} (i : Fin s) (v : Bool) (g : Gate) {p q : Straight n s e} {d : Nat} :
      Drops p q d → Drops (.recordGate i v g p) (.recordGate i v g q) d
  | measure {s e} (w : Wire) {p q : Straight n (s+1) e} {d : Nat} :
      Drops p q d → Drops (.measure w p) (.measure w q) d
  | replaceLiteral {s e} (xs ys : Circuit) (k : Nat) (hb : LiteralBound xs ys k)
      {p q : Straight n s e} {d : Nat} (h : Drops p q d) :
      Drops (literalPrefix xs p) (literalPrefix ys q) (k+d)

theorem Drops.wellFormed {n s e d} {p q : Straight n s e}
    (h : Drops p q d) (hp : p.WellFormed) : q.WellFormed := by
  induction h with
  | replaceLiteral xs ys k hb h ih =>
    exact (literalPrefix_wf ys _).mpr ⟨hb.wf,ih ((literalPrefix_wf xs _).mp hp).2⟩
  | refl => exact hp
  | skip g h ih => exact ih hp.2
  | skipRecord i v g hz h ih => exact ih hp.2
  | gate g h ih => exact ⟨hp.1, ih hp.2⟩
  | record i v g h ih => exact ⟨hp.1, ih hp.2⟩
  | measure w h ih => exact ih hp

theorem Drops.slots {n s e d} {p q : Straight n s e}
    (h : Drops p q d) : q.gateSlots ≤ p.gateSlots := by
  induction h with
  | replaceLiteral xs ys k hb h ih =>
    rw [literalPrefix_slots,literalPrefix_slots]
    exact Nat.add_le_add hb.slots ih
  | _ => simp_all [Straight.gateSlots] <;> omega

theorem Drops.tCount {n s e d} {p q : Straight n s e}
    (h : Drops p q d) (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    (q.instantiate read history).tCount + d = (p.instantiate read history).tCount := by
  induction h with
  | replaceLiteral xs ys k hb h ih =>
    rw [literalPrefix_t,literalPrefix_t]
    have ht := ih history
    have hc := hb.cost
    omega
  | refl => omega
  | skip g h ih =>
    simp only [Straight.instantiate, TemplateGate.instantiate, AdaptiveCircuit.tCount,
      ShorECDLP.tCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    have hh := ih history
    omega
  | skipRecord i v g hz h ih =>
    have hh := ih history
    simp only [Straight.instantiate, AdaptiveCircuit.tCount]
    split <;> simp_all [ShorECDLP.tCount]
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
  | replaceLiteral xs ys k hb h ih =>
    intro w hw
    rw [literalPrefix_wires] at hw ⊢
    exact List.mem_append.mpr ((List.mem_append.mp hw).imp (fun hw => hb.support hw) (ih history w))
  | refl => exact fun _ hw => hw
  | skip g h ih =>
    intro w hw
    exact List.mem_append_right _ (ih history w hw)
  | skipRecord i v g hz h ih =>
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
  | replaceLiteral xs ys k hb h ih =>
    simpa only [literalPrefix_append,Nat.add_assoc] using Drops.replaceLiteral xs ys k hb (ih hq)
  | refl p => simpa using Drops.append_right p hq
  | skip g h ih => simpa [Nat.add_assoc] using Drops.skip g (ih hq)
  | skipRecord i v g hz h ih => exact Drops.skipRecord i v g hz (ih hq)
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
  | semantic {s e} (p q : Straight n s e) :
      (∀ (read : ConstantBit n → Bool) (history : Fin s → Bool),
        (p.instantiate read history).run = (q.instantiate read history).run) → Rewrites p q
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


private def finishHistory {s e : Nat} (h : Fin s → Bool) (xs : List Bool) : Fin e → Bool :=
  fun i => (List.ofFn h ++ xs).getD i.val false

private theorem finishHistory_empty {s : Nat} (h : Fin s → Bool) :
    finishHistory (e := s) h List.nil = h := by
  funext i
  simp [finishHistory, i.isLt]

private theorem finishHistory_step {s e : Nat} (h : Fin s → Bool) (b : Bool) (xs : List Bool) :
    finishHistory (e := e) (Fin.lastCases b h) xs = finishHistory h (b :: xs) := by
  funext i
  change (List.ofFn (Fin.lastCases b h) ++ xs).getD i.val false =
    (List.ofFn h ++ (b :: xs)).getD i.val false
  rw [List.ofFn_succ']
  simp only [Fin.lastCases_castSucc, Fin.lastCases_last,
    List.concat_eq_append, List.append_assoc, List.singleton_append]

private noncomputable def bindInstrument {s e : Nat} (history : Fin s → Bool)
    (tail : (Fin e → Bool) → Instrument) (branches : Instrument) : Instrument :=
  branches.flatMap fun b => branchPrefix b.history b.kraus (tail (finishHistory history b.history))

private theorem evaluate_bind {n s e} (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool)
    (tail : (Fin e → Bool) → Instrument) :
    evaluate p read history tail = bindInstrument history tail (p.instantiate read history).run := by
  induction p with
  | done =>
    simp only [evaluate, Straight.instantiate, AdaptiveCircuit.run, bindInstrument,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, finishHistory_empty, branchPrefix]
    simp
  | gate g p ih =>
    simp only [evaluate, Straight.instantiate, AdaptiveCircuit.run, ih, bindInstrument,
      branchPrefix, List.flatMap_map, List.map_flatMap, List.map_map]
    congr 1
  | recordGate i v g p ih =>
    simp only [evaluate, Straight.instantiate, AdaptiveCircuit.run, ih, bindInstrument,
      branchPrefix, List.flatMap_map, List.map_flatMap, List.map_map]
    congr 1
  | measure w p ih =>
    simp only [evaluate, Straight.instantiate, AdaptiveCircuit.run, ih, bindInstrument,
      List.flatMap_append, branchPrefix, List.flatMap_map, List.map_flatMap, List.map_map]
    congr 1 <;> congr 1 <;> funext b <;>
      simp only [finishHistory_step, List.singleton_append]
    all_goals rfl

private theorem Rewrites.eval_eq {n s e} {p q : Straight n s e} (h : Rewrites p q)
    (read : ConstantBit n → Bool) (history : Fin s → Bool)
    (tail : (Fin e → Bool) → Instrument) : evaluate p read history tail = evaluate q read history tail := by
  induction h with
  | refl => rfl
  | semantic p q he => rw [evaluate_bind, evaluate_bind, he read history]
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
  | semantic p q he =>
    apply Rewrites.semantic
    intro read history
    simp only [reindexStraight_instantiate]
    exact he _ _
  | literal xs ys he => simpa only [reindex_literal] using Rewrites.literal (n := m) xs ys he
  | gate g h ih => exact Rewrites.gate _ ih
  | record i v g h ih => exact Rewrites.record _ _ _ ih
  | measure w h ih => exact Rewrites.measure _ ih
  | append hp hq ip iq => simpa only [reindex_append] using Rewrites.append ip iq

theorem Drops.reindex {n m s e d} {p q : Straight n s e} (h : Drops p q d)
    (f : Fin n → Fin m) : Drops (reindexStraight f p) (reindexStraight f q) d := by
  induction h with
  | replaceLiteral xs ys k hb h ih =>
    simpa only [literalPrefix_reindex] using Drops.replaceLiteral _ _ k hb ih
  | refl => exact Drops.refl _
  | skipRecord i v g hz h ih => exact Drops.skipRecord _ _ _ hz ih
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
  | semantic p q he =>
    apply Rewrites.semantic
    intro read history
    simp only [relabelStraight_instantiate, AdaptiveCircuit.run_relabel, he read history]
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
  | replaceLiteral xs ys k hb h ih =>
    simpa only [literalPrefix_relabel] using Drops.replaceLiteral _ _ k (hb.relabel f) ih
  | refl => exact Drops.refl _
  | skipRecord i v g hz h ih =>
    apply Drops.skipRecord _ _ _ _ ih
    simpa only [show tCost (g.relabel f) = tCost g by cases g <;> rfl] using hz
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
  | semantic p q he =>
    apply Rewrites.semantic
    intro read history
    simp only [shiftStraight_instantiate]
    exact he _ _
  | literal xs ys he => simpa only [shift_literal] using Rewrites.literal (n := n) xs ys he
  | gate g h ih => exact Rewrites.gate _ ih
  | record i v g h ih => exact Rewrites.record _ _ _ ih
  | measure w h ih => exact Rewrites.measure _ ih
  | append hp hq ip iq => simpa only [shift_append] using Rewrites.append ip iq

theorem Drops.shift {n s e d} {p q : Straight n s e} (h : Drops p q d)
    (offset : Nat) : Drops (shiftStraight offset p) (shiftStraight offset q) d := by
  induction h with
  | replaceLiteral xs ys k hb h ih =>
    simpa only [literalPrefix_shift] using Drops.replaceLiteral _ _ k hb ih
  | refl => exact Drops.refl _
  | skipRecord i v g hz h ih => exact Drops.skipRecord _ _ _ hz ih
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

def literalChecked {n s d} (xs ys : Circuit) (hb : LiteralBound xs ys d)
    (hr : Quantum.run xs = Quantum.run ys) :
    Patch (literalProgram xs : Straight n s s) d := by
  refine ⟨literalProgram ys, ?_, Rewrites.literal xs ys hr⟩
  have h := Drops.replaceLiteral (n := n) xs ys d hb (Drops.refl (Straight.done (cursor := s)))
  simpa only [literalPrefix_done,Nat.add_zero] using h

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

 def appendLiteral {n start d}
     (p : (count : Nat) × Straight n start (start+count)) (gs : Circuit)
     (hp : Patch p.2 d) : Patch (Paper2607_13816.ChallengeMigration.appendLiteral p gs).2 d :=
   (appendCompiled p ⟨0,literalProgram gs⟩ hp (refl _)).castSaving (Nat.add_zero d)

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



namespace ShorECDLP.Entrant.AliasLookup
open Quantum Paper2607_13816
noncomputable section

private theorem upd_twice (s : BasisState) (p : Wire) (x y : Bool) :
    s[p ↦ x][p ↦ y] = s[p ↦ y] := by
  funext w
  by_cases h : w = p <;> simp [upd, h]

/-- Equality on all basis vectors extends to arbitrary, possibly entangled states. -/
theorem linear_basis (A B : State →ₗ[ℂ] State)
    (h : ∀ s, A (ket s) = B (ket s)) : A = B := by
  apply LinearMap.ext
  intro psi
  induction psi using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single s c =>
    have hs : Finsupp.single s c = c • ket s := by ext u; simp [ket]
    rw [hs, map_smul, map_smul, h]

/-- Computing an AND immediately before its corrected X erasure has the same
branch operator as directly measuring the old target. No clean-target premise. -/
theorem erase_compute (a b p : Wire) (hab : a ≠ b) (hap : a ≠ p) (hbp : b ≠ p)
    (out : Bool) (psi : State) :
    Quantum.run (if out then controlledZ a b else [])
      (xResetKraus p out (applyGate (.CCX a b p) psi)) = xResetKraus p out psi := by
  have he : (Quantum.run (if out then controlledZ a b else [])).comp
      ((xResetKraus p out).comp (applyGate (.CCX a b p))) = xResetKraus p out := by
    apply linear_basis
    intro s
    simp only [LinearMap.comp_apply, applyGate_CCX_ket, xResetKraus_ket, map_smul]
    rw [upd_twice]
    cases out with
    | false => simp [xResetCoeff]
    | true =>
      simp only [ite_true]
      rw [run_controlledZ_ket _ _ _ hab]
      cases ha : s a <;> cases hb : s b <;> cases hp : s p <;>
        simp [xResetCoeff, upd, hap, hbp, ha, hb]
  exact congrArg (fun f : State →ₗ[ℂ] State => f psi) he

/-- Two identical leaf actions and the path-control toggles collapse to one
leaf action controlled by the parent. -/
def leafCommutator (q p : Wire) (mask : List Wire) : Circuit :=
  tableXorGates p mask ++ [.CX q p] ++ tableXorGates p mask ++ [.CX q p]

theorem leafCommutator_classical (q p : Wire) (mask : List Wire)
    (hn : mask.Nodup) (hq : q ∉ mask) (hp : p ∉ mask) (hqp : q ≠ p)
    (s : BasisState) :
    Classical.run (leafCommutator q p mask) s = Classical.run (tableXorGates q mask) s := by
  simp only [leafCommutator, Classical.run_append, Classical.run_cons, Classical.run_nil,
    Classical.applyGate]
  rw [run_tableXorGates p mask s hn hp, run_tableXorGates p mask _ hn hp,
    run_tableXorGates q mask s hn hq]
  funext w
  by_cases hw : w = p
  · subst w
    cases hqv : s q <;> cases hpv : s p <;>
      simp [tableXorState, upd, hq, hp, hqp, hqv, hpv]
  · cases hqv : s q <;> cases hpv : s p <;> cases hmem : decide (w ∈ mask) <;>
      simp [tableXorState, upd, hq, hp, hw, hqv, hpv, hmem]


def nodePrefix (q b p : Wire) (mask : List Wire) : Circuit :=
  computeZeroAnd q b p ++ leafCommutator q p mask ++ [.X b]

def reorderedPrefix (q b p : Wire) (mask : List Wire) : Circuit :=
  [.X b] ++ tableXorGates q mask ++ [.CCX q b p]

theorem nodePrefix_classical (q b p : Wire) (mask : List Wire)
    (hn : mask.Nodup) (hq : q ∉ mask) (hb : b ∉ mask) (hp : p ∉ mask)
    (hqb : q ≠ b) (hqp : q ≠ p) (hbp : b ≠ p) (s : BasisState) :
    Classical.run (nodePrefix q b p mask) s =
      Classical.run (reorderedPrefix q b p mask) s := by
  simp only [nodePrefix, reorderedPrefix, Classical.run_append]
  rw [leafCommutator_classical q p mask hn hq hp hqp]
  simp only [computeZeroAnd, Classical.run_cons, Classical.run_nil, Classical.applyGate]
  rw [run_tableXorGates q mask _ hn hq, run_tableXorGates q mask _ hn hq]
  funext w
  by_cases hwp : w = p <;> by_cases hwb : w = b <;>
    cases hqv : s q <;> cases hbv : s b <;> cases hpv : s p <;>
    simp_all [tableXorState, upd]

theorem nodePrefix_run (q b p : Wire) (mask : List Wire)
    (hn : mask.Nodup) (hq : q ∉ mask) (hb : b ∉ mask) (hp : p ∉ mask)
    (hqb : q ≠ b) (hqp : q ≠ p) (hbp : b ≠ p) :
    Quantum.run (nodePrefix q b p mask) = Quantum.run (reorderedPrefix q b p mask) := by
  apply linear_basis
  intro s
  rw [run_ket_agrees_classical _ _ (by
    simp [nodePrefix, leafCommutator, computeZeroAnd, tableXorGates_HPFree])]
  rw [run_ket_agrees_classical _ _ (by
    simp [reorderedPrefix, tableXorGates_HPFree])]
  rw [nodePrefix_classical q b p mask hn hq hb hp hqb hqp hbp]

theorem xor_conjugate (q b : Wire) (mask : List Wire)
    (hn : mask.Nodup) (hq : q ∉ mask) (hb : b ∉ mask) (hqb : q ≠ b) :
    Quantum.run ([.X b] ++ tableXorGates q mask ++ [.X b]) = Quantum.run (tableXorGates q mask) := by
  apply linear_basis
  intro s
  rw [run_ket_agrees_classical _ _ (by simp [tableXorGates_HPFree]),
    run_ket_agrees_classical _ _ (tableXorGates_HPFree q mask)]
  congr 1
  simp only [Classical.run_append, Classical.run_cons, Classical.run_nil, Classical.applyGate]
  rw [run_tableXorGates q mask _ hn hq, run_tableXorGates q mask _ hn hq]
  funext w
  by_cases hwb : w = b <;> cases hbv : s b <;> simp_all [tableXorState, upd]

/-- The erased controls and their feed-forward correction can all be deleted.
The retained leaf commutator and the measurement occupy their original positions. -/
theorem node_branch (q b p : Wire) (mask : List Wire)
    (hn : mask.Nodup) (hq : q ∉ mask) (hb : b ∉ mask) (hp : p ∉ mask)
    (hqb : q ≠ b) (hqp : q ≠ p) (hbp : b ≠ p) (out : Bool) (psi : State) :
    applyGate (.X b) (Quantum.run (if out then controlledZ q b else [])
      (xResetKraus p out (Quantum.run (nodePrefix q b p mask) psi))) =
      xResetKraus p out (Quantum.run (leafCommutator q p mask) psi) := by
  rw [nodePrefix_run q b p mask hn hq hb hp hqb hqp hbp]
  simp only [reorderedPrefix, Quantum.run_append, Quantum.run_singleton]
  rw [erase_compute q b p hqb hqp hbp]
  rw [applyGate_reset_commute (.X b) p out (by simpa [gateWires, ne_comm] using hbp)]
  have hx := congrArg (fun f : State →ₗ[ℂ] State => f psi) (xor_conjugate q b mask hn hq hb hqb)
  simp only [Quantum.run_append, Quantum.run_singleton] at hx
  rw [hx]
  congr 1
  have hc : Quantum.run (leafCommutator q p mask) = Quantum.run (tableXorGates q mask) := by
    apply linear_basis
    intro s
    rw [run_ket_agrees_classical _ _ (by simp [leafCommutator, tableXorGates_HPFree]),
      run_ket_agrees_classical _ _ (tableXorGates_HPFree q mask),
      leafCommutator_classical q p mask hn hq hp hqp]
  rw [hc]

end
end ShorECDLP.Entrant.AliasLookup

namespace ShorECDLP.Entrant.AliasLookup
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration Optimization
noncomputable section
set_option maxHeartbeats 20000
set_option Elab.async false

/-- The unchanged two-leaf commutator, including all optional target gates. -/
def commutatorTemplates {n : Nat} (q p : Wire) (ports : List (ConstantBit n × Wire)) :
    List (TemplateGate n) :=
  lookupLeafGates p ports ++ [.literal (.CX q p)] ++
    lookupLeafGates p ports ++ [.literal (.CX q p)]

def sourceNode {n : Nat} (start : Nat) (q b p : Wire) (ports : List (ConstantBit n × Wire)) :
    Straight n start (start+1) :=
  (gateProgram ((computeZeroAnd q b p).map TemplateGate.literal ++
    commutatorTemplates q p ports ++ [.literal (.X b)])).append
      (.measure p (recordGates (Fin.last start) (controlledZ q b) (literalProgram [.X b])))

def retainedNode {n : Nat} (start : Nat) (q p : Wire) (ports : List (ConstantBit n × Wire)) :
    Straight n start (start+1) :=
  (gateProgram (commutatorTemplates q p ports)).append (.measure p .done)

def leafMask {n : Nat} (ports : List (ConstantBit n × Wire)) (read : ConstantBit n → Bool) : List Wire :=
  (ports.filter (fun port => read port.1)).map Prod.snd

theorem instantiate_commutator {n : Nat} (q p : Wire) (ports : List (ConstantBit n × Wire))
    (read : ConstantBit n → Bool) :
    (commutatorTemplates q p ports).flatMap (TemplateGate.instantiate read) =
      leafCommutator q p (leafMask ports read) := by
  simp only [commutatorTemplates, List.flatMap_append, lookupLeafGates_instantiate,
    List.flatMap_cons, List.flatMap_nil, TemplateGate.instantiate, List.append_nil,
    leafCommutator, tableXorGates, leafMask, List.map_map]
  rfl

theorem gateProgram_prefix_run {n s e} (gs : List (TemplateGate n)) (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    (((gateProgram gs).append p).instantiate read history).run =
      (AdaptiveCircuit.unitary (gs.flatMap (TemplateGate.instantiate read)) (p.instantiate read history)).run := by
  induction gs with
  | nil =>
    simp only [gateProgram, Straight.append, List.flatMap_nil, AdaptiveCircuit.run]
    symm
    apply List.map_id'
  | cons g gs ih =>
    simp only [gateProgram, Straight.append, Straight.instantiate, AdaptiveCircuit.run, ih,
      List.flatMap_cons, Quantum.run_append_map, List.map_map]
    rfl

/-- All branch maps of a single measured node are explicit and retain its one record. -/
theorem oneMeasure_run {n s} (gs : List (TemplateGate n)) (w : Wire) (cs fs : Circuit)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    (((gateProgram gs).append (.measure w
      (recordGates (Fin.last s) cs (literalProgram fs)))).instantiate read history).run =
      [⟨[false], (Quantum.run fs).comp ((xResetKraus w false).comp
        (Quantum.run (gs.flatMap (TemplateGate.instantiate read))))⟩,
       ⟨[true], (Quantum.run fs).comp ((Quantum.run cs).comp ((xResetKraus w true).comp
        (Quantum.run (gs.flatMap (TemplateGate.instantiate read)))))⟩] := by
  rw [gateProgram_prefix_run]
  simp only [AdaptiveCircuit.run, Straight.instantiate, recordGates_run, literalProgram_run,
    Fin.lastCases_last, Bool.false_eq_true, if_false, if_true,
    List.map_cons, List.map_nil, List.singleton_append]
  rfl

theorem leafMask_sublist {n : Nat} (ports : List (ConstantBit n × Wire)) (read : ConstantBit n → Bool) :
    (leafMask ports read).Sublist (ports.map Prod.snd) := by
  exact List.Sublist.map Prod.snd List.filter_sublist


/-- Factor branch comparison before specializing any table template. -/
theorem oneMeasure_congr {n s} (xs ys : List (TemplateGate n)) (w : Wire) (cs fs : Circuit)
    (read : ConstantBit n → Bool) (history : Fin s → Bool)
    (hf : ∀ psi, Quantum.run fs (xResetKraus w false
      (Quantum.run (xs.flatMap (TemplateGate.instantiate read)) psi)) =
      xResetKraus w false (Quantum.run (ys.flatMap (TemplateGate.instantiate read)) psi))
    (ht : ∀ psi, Quantum.run fs (Quantum.run cs (xResetKraus w true
      (Quantum.run (xs.flatMap (TemplateGate.instantiate read)) psi))) =
      xResetKraus w true (Quantum.run (ys.flatMap (TemplateGate.instantiate read)) psi)) :
    (((gateProgram xs).append (.measure w
      (recordGates (Fin.last s) cs (literalProgram fs)))).instantiate read history).run =
      (((gateProgram ys).append (.measure w .done)).instantiate read history).run := by
  have he : (.done : Straight n (s+1) (s+1)) =
      recordGates (Fin.last s) List.nil (literalProgram List.nil) := rfl
  rw [he, oneMeasure_run, oneMeasure_run]
  apply congrArg₂ List.cons
  · apply congrArg (fun k : State →ₗ[ℂ] State => (⟨[false], k⟩ : InstrumentBranch))
    apply LinearMap.ext
    intro psi
    simpa only [LinearMap.comp_apply, Quantum.run_nil, LinearMap.id_coe, id_eq] using hf psi
  · apply congrArg (fun k : State →ₗ[ℂ] State => [(⟨[true], k⟩ : InstrumentBranch)])
    apply LinearMap.ext
    intro psi
    simpa only [LinearMap.comp_apply, Quantum.run_nil, LinearMap.id_coe, id_eq] using ht psi

theorem instantiate_nodePrefix {n : Nat} (q b p : Wire) (ports : List (ConstantBit n × Wire))
    (read : ConstantBit n → Bool) :
    ((computeZeroAnd q b p).map TemplateGate.literal ++
      commutatorTemplates q p ports ++ [TemplateGate.literal (tableSize := n) (.X b)]).flatMap
        (TemplateGate.instantiate read) = nodePrefix q b p (leafMask ports read) := by
  simp only [List.flatMap_append, literal_gates, instantiate_commutator,
    List.flatMap_cons, List.flatMap_nil, TemplateGate.instantiate, List.append_nil, nodePrefix]

theorem sourceNode_run {n : Nat} (start : Nat) (q b p : Wire) (ports : List (ConstantBit n × Wire))
    (hn : (ports.map Prod.snd).Nodup)
    (hq : q ∉ ports.map Prod.snd) (hb : b ∉ ports.map Prod.snd) (hp : p ∉ ports.map Prod.snd)
    (hqb : q ≠ b) (hqp : q ≠ p) (hbp : b ≠ p)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((sourceNode start q b p ports).instantiate read history).run =
      ((retainedNode start q p ports).instantiate read history).run := by
  have hsub := leafMask_sublist ports read
  have hmask := hsub.nodup hn
  have hqm : q ∉ leafMask ports read := fun h => hq (hsub.subset h)
  have hbm : b ∉ leafMask ports read := fun h => hb (hsub.subset h)
  have hpm : p ∉ leafMask ports read := fun h => hp (hsub.subset h)
  unfold sourceNode retainedNode
  apply oneMeasure_congr
  · intro psi
    rw [instantiate_nodePrefix, instantiate_commutator, Quantum.run_singleton]
    simpa only [if_false, Quantum.run_nil, LinearMap.id_coe, id_eq] using
      node_branch q b p (leafMask ports read) hmask hqm hbm hpm hqb hqp hbp false psi
  · intro psi
    rw [instantiate_nodePrefix, instantiate_commutator, Quantum.run_singleton]
    simpa only [if_true] using
      node_branch q b p (leafMask ports read) hmask hqm hbm hpm hqb hqp hbp true psi



theorem gatePrefix_append {n s e} (xs ys : List (TemplateGate n)) (tail : Straight n s e) :
    (gateProgram (xs ++ ys)).append tail =
      (gateProgram xs).append ((gateProgram ys).append tail) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (Straight.gate x) ih

theorem Drops.gatePrefix {n s e d} (xs : List (TemplateGate n)) {p q : Straight n s e}
    (h : Optimization.Drops p q d) :
    Optimization.Drops ((gateProgram xs).append p) ((gateProgram xs).append q) d := by
  induction xs with
  | nil => exact h
  | cons x xs ih => exact Optimization.Drops.gate x ih

theorem correction_drops {n s} (i : Fin s) (q b : Wire) :
    Optimization.Drops (recordGates i (controlledZ q b) (literalProgram [.X b]) : Straight n s s) .done 0 := by
  apply Optimization.Drops.skipRecord i true (.H b) (by rfl)
  apply Optimization.Drops.skipRecord i true (.CX q b) (by rfl)
  apply Optimization.Drops.skipRecord i true (.H b) (by rfl)
  exact Optimization.Drops.skip (.X b) (Optimization.Drops.refl .done)

theorem sourceNode_drops {n : Nat} (start : Nat) (q b p : Wire) (ports : List (ConstantBit n × Wire)) :
    Optimization.Drops (sourceNode start q b p ports) (retainedNode start q p ports) 7 := by
  unfold sourceNode retainedNode
  rw [List.append_assoc, gatePrefix_append, gatePrefix_append]
  simp only [computeZeroAnd, List.map_cons, List.map_nil, gateProgram, Straight.append]
  refine (show 0 + 7 = 7 by decide) ▸ Optimization.Drops.skip (.X b) ?_
  refine (show 7 + 0 = 7 by decide) ▸ Optimization.Drops.skip (.CCX q b p) ?_
  refine Optimization.Drops.skip (.X b) (d := 0) ?_
  apply Drops.gatePrefix
  refine Optimization.Drops.skip (.X b) (d := 0) ?_
  exact Optimization.Drops.measure p (correction_drops (Fin.last start) q b)

def nodePatch {n : Nat} (start : Nat) (q b p : Wire) (ports : List (ConstantBit n × Wire))
    (hn : (ports.map Prod.snd).Nodup)
    (hq : q ∉ ports.map Prod.snd) (hb : b ∉ ports.map Prod.snd) (hp : p ∉ ports.map Prod.snd)
    (hqb : q ≠ b) (hqp : q ≠ p) (hbp : b ≠ p) :
    Optimization.Patch (sourceNode start q b p ports) 7 :=
  ⟨retainedNode start q p ports, sourceNode_drops start q b p ports,
    Optimization.Rewrites.semantic _ _
      (sourceNode_run start q b p ports hn hq hb hp hqb hqp hbp)⟩

end
end ShorECDLP.Entrant.AliasLookup

namespace ShorECDLP.Entrant.AliasLookup
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration Optimization
noncomputable section
set_option maxHeartbeats 100000
set_option Elab.async false

theorem append_assoc {n a b c d} (p : Straight n a b) (q : Straight n b c) (r : Straight n c d) :
    (p.append q).append r = p.append (q.append r) := by
  induction p with
  | done => rfl
  | gate g p ih => exact congrArg (Straight.gate g) (ih q)
  | recordGate i v g p ih => exact congrArg (Straight.recordGate i v g) (ih q)
  | measure w p ih => exact congrArg (Straight.measure w) (ih q)

theorem castFinish_heq {n s e f} (h : e = f) (p : Straight n s e) :
    HEq (castFinish h p) p := by cases h; rfl

theorem append_heq {n a b c b' c'} {p : Straight n a b} {p' : Straight n a b'}
    {q : Straight n b c} {q' : Straight n b' c'}
    (hb : b=b') (hc : c=c') (hp : HEq p p') (hq : HEq q q') :
    HEq (p.append q) (p'.append q') := by
  subst b'; subst c'; cases hp; cases hq; rfl

theorem lookupMeasurements_append {n} (xs ys : List (LookupOp n)) :
    lookupMeasurements (xs ++ ys) = lookupMeasurements xs + lookupMeasurements ys := by
  induction xs with
  | nil => simp only [List.nil_append, lookupMeasurements, Nat.zero_add]
  | cons x xs ih => cases x <;> simp only [List.cons_append, lookupMeasurements, ih, Nat.add_assoc]

theorem lookup_cursor_heq {n s t} (ops : List (LookupOp n)) (h : s=t) :
    HEq (lookupProgram n ops s) (lookupProgram n ops t) := by cases h; rfl

theorem lookupProgram_append_heq {n} (xs ys : List (LookupOp n)) (start : Nat) :
    HEq (lookupProgram n (xs ++ ys) start)
      ((lookupProgram n xs start).append (lookupProgram n ys (start + lookupMeasurements xs))) := by
  induction xs generalizing start with
  | nil => rfl
  | cons x xs ih =>
    cases x with
    | gates gs =>
      simp only [List.cons_append, lookupProgram, lookupMeasurements]
      apply HEq.trans (append_heq rfl (by rw [lookupMeasurements_append]; omega) (HEq.rfl) (ih start))
      exact heq_of_eq (append_assoc _ _ _).symm
    | erase a b t =>
      simp only [List.cons_append, lookupProgram, lookupMeasurements]
      apply HEq.trans (castFinish_heq _ _)
      apply HEq.trans (append_heq rfl (by rw [lookupMeasurements_append]; omega) (HEq.rfl) (ih (start+1)))
      apply HEq.trans (heq_of_eq (append_assoc _ _ _).symm)
      apply HEq.symm
      exact append_heq (by omega) (by omega) (castFinish_heq _ _) (lookup_cursor_heq ys (by omega))

theorem lookupProgram_append {n} (xs ys : List (LookupOp n)) (start : Nat) :
    lookupProgram n (xs ++ ys) start =
      castFinish (by rw [lookupMeasurements_append]; omega)
        ((lookupProgram n xs start).append (lookupProgram n ys (start + lookupMeasurements xs))) := by
  exact eq_of_heq ((lookupProgram_append_heq xs ys start).trans (castFinish_heq _ _).symm)


def lookupAppendPatch {n d e} (xs ys : List (LookupOp n)) (start : Nat)
    (hp : Patch (lookupProgram n xs start) d)
    (hq : Patch (lookupProgram n ys (start + lookupMeasurements xs)) e) :
    Patch (lookupProgram n (xs ++ ys) start) (d+e) := by
  rw [lookupProgram_append]
  exact (hp.append hq).castFinish _

theorem bottomNode_eq {n} (ports : Nat → List (ConstantBit n × Wire))
    (q b p l r start : Nat) (rest : List Wire) (he : ports l = ports r) :
    lookupProgram n (unaryLookupOps (fun l q => lookupLeafGates q (ports l))
      (.node b (.leaf l) (.leaf r)) q (p::rest)) start =
      sourceNode start q b p (ports l) := by
  simp only [unaryLookupOps, List.cons_append, List.nil_append,
    lookupProgram, ordinaryOp, lookupMeasurements, Nat.add_zero, ← he]
  simp only [sourceNode, commutatorTemplates, gatePrefix_append]
  rfl

/-- A finite plan chooses only aliased sibling pairs, preserving every traversal record. -/
inductive AliasPlan {n : Nat} (ports : Nat → List (ConstantBit n × Wire)) :
    UnaryActionTree → Wire → List Wire → Nat → Type where
  | keep (tree q anc) : AliasPlan ports tree q anc 0
  | bottom (q b p l r : Nat) (rest : List Wire)
      (he : ports l = ports r)
      (hn : ((ports l).map Prod.snd).Nodup)
      (hq : q ∉ (ports l).map Prod.snd) (hb : b ∉ (ports l).map Prod.snd)
      (hp : p ∉ (ports l).map Prod.snd)
      (hqb : q ≠ b) (hqp : q ≠ p) (hbp : b ≠ p) :
      AliasPlan ports (.node b (.leaf l) (.leaf r)) q (p::rest) 7
  | node {q b p : Wire} {z o : UnaryActionTree} {rest : List Wire} {dz do_ : Nat}
      (zero : AliasPlan ports z p rest dz) (one : AliasPlan ports o p rest do_) :
      AliasPlan ports (.node b z o) q (p::rest) (dz+do_)

def AliasPlan.patch {n} {ports : Nat → List (ConstantBit n × Wire)}
    {tree q anc d} (plan : AliasPlan ports tree q anc d) (start : Nat) :
    Patch (lookupProgram n (unaryLookupOps (fun l q => lookupLeafGates q (ports l)) tree q anc) start) d := by
  induction plan generalizing start with
  | keep tree q anc => exact Patch.refl _
  | bottom q b p l r rest he hn hq hb hp hqb hqp hbp =>
      rw [bottomNode_eq ports q b p l r start rest he]
      exact nodePatch start q b p (ports l) hn hq hb hp hqb hqp hbp
  | @node q b p z o rest dz do_ zero one ihz iho =>
      rw [unaryLookupOps]
      refine (lookupAppendPatch (d := dz+do_) (e := 0) _ _ start ?_ (Patch.refl _)).castSaving (Nat.add_zero _)
      refine lookupAppendPatch (d := dz) (e := do_) _ _ _ ?_ (iho _)
      refine (lookupAppendPatch (d := dz) (e := 0) _ _ _ ?_ (Patch.refl _)).castSaving (Nat.add_zero _)
      exact (lookupAppendPatch (d := 0) (e := dz) _ _ _ (Patch.refl _) (ihz _)).castSaving (Nat.zero_add _)


/-- Periodic tables admit a cancellation at every last-level sibling pair. -/
def periodicPlan {n : Nat} (ports : Nat → List (ConstantBit n × Wire))
    (bits : List Wire) (base stride q : Nat) (anc : List Wire)
    (hne : bits ≠ []) (hlen : bits.length ≤ anc.length)
    (hn : (q :: bits ++ anc).Nodup)
    (ht : ∀ l, ((ports l).map Prod.snd).Nodup)
    (hd : ∀ l w, w ∈ q :: bits ++ anc → w ∉ (ports l).map Prod.snd)
    (hp : ∀ l, ports l = ports (l + stride * 2^(bits.length-1))) :
    AliasPlan ports (tableAddressTree bits base stride) q anc (7 * 2^(bits.length-1)) := by
  induction bits generalizing base stride q anc with
  | nil => exact False.elim (hne rfl)
  | cons bit bits ih =>
      cases anc with
      | nil => simp at hlen
      | cons path rest =>
        have hdrop : (bits ++ path::rest).Nodup :=
          (List.nodup_cons.mp (List.nodup_cons.mp hn).2).2
        have hchild : (path::bits++rest).Nodup := List.perm_middle.nodup_iff.mp hdrop
        have hdchild : ∀ l w, w ∈ path::bits++rest → w ∉ (ports l).map Prod.snd := by
          intro l w hw
          apply hd l w
          simp only [List.mem_cons, List.mem_append] at hw ⊢
          tauto
        cases bits with
        | nil =>
            simp only [List.length_cons, List.length_nil, Nat.sub_self, pow_zero, Nat.mul_one,
              tableAddressTree] at hp ⊢
            apply AliasPlan.bottom q bit path base (base+stride) rest (hp base) (ht base)
            · exact hd base q (by simp)
            · exact hd base bit (by simp)
            · exact hd base path (by simp)
            · have h := (List.nodup_cons.mp hn).1; simpa using fun he => h (by simp [he])
            · have h := (List.nodup_cons.mp hn).1; simpa using fun he => h (by simp [he])
            · have h := (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
              simpa using fun he => h (by simp [he])
        | cons next tail =>
            have hperiod : ∀ l, ports l = ports (l + (2*stride) * 2^((next::tail).length-1)) := by
              intro l
              convert hp l using 2
              simp only [List.length_cons, Nat.add_sub_cancel, pow_succ]
              ring
            have hzero := ih base (2*stride) path rest (by simp) (by simpa using hlen)
              hchild hdchild hperiod
            have hone := ih (base+stride) (2*stride) path rest (by simp) (by simpa using hlen)
              hchild hdchild hperiod
            have he : 7 * 2^((bit::next::tail).length-1) =
                7 * 2^((next::tail).length-1) + 7 * 2^((next::tail).length-1) := by
              simp only [List.length_cons, Nat.add_sub_cancel, pow_succ]
              omega
            rw [he]
            exact AliasPlan.node hzero hone

end
end ShorECDLP.Entrant.AliasLookup

namespace ShorECDLP.Entrant.AliasLookup
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration Optimization
noncomputable section
set_option maxHeartbeats 100000
set_option Elab.async false

theorem reindex_append {n m a b c} (f : Fin n → Fin m)
    (p : Straight n a b) (q : Straight n b c) :
    reindexStraight f (p.append q) = (reindexStraight f p).append (reindexStraight f q) := by
  induction p <;> simp_all [reindexStraight, Straight.append]

theorem reindex_cast {n m s e z} (f : Fin n → Fin m) (h : e=z) (p : Straight n s e) :
    reindexStraight f (castFinish h p) = castFinish h (reindexStraight f p) := by
  subst z; rfl

theorem reindex_gateProgram {n m s} (f : Fin n → Fin m) (gs : List (TemplateGate n)) :
    reindexStraight f (gateProgram gs : Straight n s s) = gateProgram (gs.map (reindexGate f)) := by
  induction gs <;> simp_all only [gateProgram, reindexStraight, List.map_nil, List.map_cons]

def reindexOp {n m} (f : Fin n → Fin m) : LookupOp n → LookupOp m
  | .gates gs => .gates (gs.map (reindexGate f))
  | .erase a b t => .erase a b t

theorem reindexOp_measurements {n m} (f : Fin n → Fin m) (ops : List (LookupOp n)) :
    lookupMeasurements (ops.map (reindexOp f)) = lookupMeasurements ops := by
  induction ops with
  | nil => rfl
  | cons op ops ih => cases op <;> simp only [List.map_cons,reindexOp,lookupMeasurements,ih]

theorem reindex_recordGates {n m s e} (f : Fin n → Fin m) (i : Fin s) (gs : Circuit)
    (tail : Straight n s e) :
    reindexStraight f (recordGates i gs tail) = recordGates i gs (reindexStraight f tail) := by
  induction gs <;> simp_all only [recordGates,reindexStraight]

theorem reindex_andErase {n m} (f : Fin n → Fin m) (start a b p : Nat) :
    reindexStraight f (andEraseProgram n start a b p) = andEraseProgram m start a b p := by
  simp only [andEraseProgram,reindexStraight,reindex_recordGates]

theorem reindex_lookup_heq {n m} (f : Fin n → Fin m) (ops : List (LookupOp n)) (start : Nat) :
    HEq (reindexStraight f (lookupProgram n ops start))
      (lookupProgram m (ops.map (reindexOp f)) start) := by
  induction ops generalizing start with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | gates gs =>
        simp only [List.map_cons,reindexOp,lookupProgram,reindex_append,reindex_gateProgram]
        exact append_heq rfl (by simp only [lookupMeasurements,reindexOp_measurements]) (HEq.rfl) (ih start)
    | erase a b p =>
        simp only [List.map_cons,reindexOp,lookupProgram,reindex_cast,reindex_append,reindex_andErase]
        exact (castFinish_heq _ _).trans
          ((append_heq rfl (by rw [reindexOp_measurements]) (HEq.rfl) (ih (start+1))).trans
            (castFinish_heq _ _).symm)

def reindexPorts {n m} (f : Fin n → Fin m) (ports : List (ConstantBit n × Wire)) :=
  ports.map (fun x => (reindexBit f x.1, x.2))

theorem reindex_leaf {n m} (f : Fin n → Fin m) (q : Wire) (ports : List (ConstantBit n × Wire)) :
    (lookupLeafGates q ports).map (reindexGate f) = lookupLeafGates q (reindexPorts f ports) := by
  simp only [lookupLeafGates,reindexPorts,List.map_map]
  rfl

theorem reindex_unaryOps {n m} (f : Fin n → Fin m) (ports : Nat → List (ConstantBit n × Wire))
    (tree : UnaryActionTree) (q : Wire) (anc : List Wire) :
    (unaryLookupOps (fun l q => lookupLeafGates q (ports l)) tree q anc).map (reindexOp f) =
      unaryLookupOps (fun l q => lookupLeafGates q (reindexPorts f (ports l))) tree q anc := by
  induction tree generalizing q anc with
  | leaf l => simp only [unaryLookupOps,List.map_cons,List.map_nil,reindexOp,reindex_leaf]
  | node b z o ihz iho =>
      cases anc with
      | nil => rfl
      | cons p rest =>
          simp only [unaryLookupOps,List.map_append,List.map_cons,List.map_nil,ihz,iho,
            reindexOp,ordinaryOp,List.map_map]
          rfl


def castSource {n s e z d} {p : Straight n s e} {q : Straight n s z}
    (hp : Patch p d) (hz : e=z) (he : HEq p q) : Patch q d := by
  subst z
  cases he
  exact hp

def lookupReindexPatch {n m d} (f : Fin n → Fin m) (ops : List (LookupOp n)) (start : Nat)
    (hp : Patch (lookupProgram m (ops.map (reindexOp f)) start) d) :
    Patch (reindexStraight f (lookupProgram n ops start)) d :=
  castSource hp (by rw [reindexOp_measurements]) (reindex_lookup_heq f ops start).symm

def aliasRow (a : Fin 32768) : Fin 32768 :=
  ⟨a.val % 16384, by have h := Nat.mod_lt a.val (by decide : 0 < 16384); omega⟩

def rawFieldPorts (field : PointField) (label : Nat) : List (ConstantBit 32768 × Wire) :=
  (fieldRefs ⟨label % 32768, Nat.mod_lt _ (by decide)⟩ field).zip (List.range' 7 256)

theorem reindex_fieldRefs {n m} (f : Fin n → Fin m) (a : Fin n) (field : PointField) :
    (fieldRefs a field).map (reindexBit f) = fieldRefs (f a) field := by
  simp only [fieldRefs,List.map_ofFn]
  rfl

theorem reindex_fieldPorts {n m} (f : Fin n → Fin m) (a : Fin n) (field : PointField) (ws : List Wire) :
    reindexPorts f ((fieldRefs a field).zip ws) = (fieldRefs (f a) field).zip ws := by
  change ((fieldRefs a field).zip ws).map (Prod.map (reindexBit f) id) = _
  rw [← List.zip_map_left,reindex_fieldRefs]

theorem fieldPorts_targets (field : PointField) (label : Nat) :
    (reindexPorts aliasRow (rawFieldPorts field label)).map Prod.snd = List.range' 7 256 := by
  rw [rawFieldPorts,reindex_fieldPorts]
  exact List.map_snd_zip (by simp only [List.length_range',fieldRefs,List.length_ofFn]; omega)

theorem fieldPorts_periodic (field : PointField) (label : Nat) :
    reindexPorts aliasRow (rawFieldPorts field label) =
      reindexPorts aliasRow (rawFieldPorts field (label+16384)) := by
  simp only [rawFieldPorts,reindex_fieldPorts]
  have he : aliasRow ⟨label % 32768, Nat.mod_lt _ (by decide)⟩ =
      aliasRow ⟨(label+16384) % 32768, Nat.mod_lt _ (by decide)⟩ := by
    apply Fin.ext
    simp only [aliasRow, Nat.mod_mod_of_dvd _ (by decide : 16384 ∣ 32768)]
    omega
  rw [he]

def fieldLoadAliasPatch (field : PointField) (start : Nat) :
    Patch (reindexStraight aliasRow (fieldLoadProgram field start)) 114688 := by
  unfold fieldLoadProgram
  rw [reindex_cast]
  apply Patch.castFinish
  apply lookupReindexPatch
  unfold fieldLoadOps fieldLeaf
  rw [reindex_unaryOps]
  change Patch (lookupProgram 32768
    (unaryLookupOps (fun l q => lookupLeafGates q (reindexPorts aliasRow (rawFieldPorts field l)))
      (tableAddressTree pointLookupAddress 0 1) 836 pointLookupPath) start) 114688
  have plan := periodicPlan (fun l => reindexPorts aliasRow (rawFieldPorts field l))
    pointLookupAddress 0 1 836 pointLookupPath (by decide) (by decide) (by decide)
    (fun l => by rw [fieldPorts_targets]; exact List.nodup_range')
    (by intro l w hw; rw [fieldPorts_targets];
        simp only [pointLookupAddress,pointLookupPath,List.mem_cons,List.mem_append,List.mem_range'] at hw ⊢; omega)
    (by intro l; exact fieldPorts_periodic field l)
  exact plan.patch start


def reindexedAppendCompiled {n m start d e} (f : Fin n → Fin m)
    (p : (count : Nat) × Straight n start (start+count))
    (q : (count : Nat) × Straight n (start+p.1) (start+p.1+count))
    (hp : Patch (reindexStraight f p.2) d) (hq : Patch (reindexStraight f q.2) e) :
    Patch (reindexStraight f (appendCompiled p q).2) (d+e) := by
  unfold appendCompiled
  rw [reindex_cast,reindex_append]
  exact (hp.append hq).castFinish _

def reindexedSequenceCons {n m start d e} (f : Fin n → Fin m)
    (head : FixedSegment n) (tail : List (FixedSegment n))
    (hp : Patch (reindexStraight f (head start).2) d)
    (hq : Patch (reindexStraight f (sequenceProgram n tail (start+(head start).1)).2) e) :
    Patch (reindexStraight f (sequenceProgram n (head::tail) start).2) (d+e) :=
  reindexedAppendCompiled f (head start) (sequenceProgram n tail _) hp hq

attribute [local irreducible] fieldLoadProgram modularAddProgram appendCompiled yNegateProgram fieldLookupAddProgram reindexStraight

def fieldAddAliasPatch (field : PointField) (acc : List Wire) (start : Nat) :
    Patch (reindexStraight aliasRow (fieldLookupAddProgram field acc start).2) 229376 := by
  unfold fieldLookupAddProgram
  exact (reindexedAppendCompiled aliasRow _ _ (fieldLoadAliasPatch field start)
    ((reindexedAppendCompiled aliasRow _ _ (Patch.refl _) (fieldLoadAliasPatch field _)).castSaving
      (show 0+114688=114688 by rfl))).castSaving (by decide)

def signedFieldAliasPatch (field : PointField) (start : Nat) :
    Patch (reindexStraight aliasRow (signedFieldProgram field start).2) 229376 := by
  unfold signedFieldProgram
  exact (reindexedAppendCompiled aliasRow _ _ (Patch.refl _)
    ((reindexedAppendCompiled aliasRow _ _ (fieldAddAliasPatch field _ _) (Patch.refl _)).castSaving
      (show 229376+0=229376 by rfl))).castSaving (by decide)

theorem reindex_comp {n m k s e} (f : Fin n → Fin m) (g : Fin m → Fin k) (p : Straight n s e) :
    reindexStraight g (reindexStraight f p) = reindexStraight (g ∘ f) p := by
  induction p with
  | done => simp only [reindexStraight]
  | gate gate p ih => cases gate <;> simp only [reindexStraight,reindexGate,ih]; rfl
  | recordGate i v gate p ih => simp only [reindexStraight,ih]
  | measure w p ih => simp only [reindexStraight,ih]


theorem reindex_shift {n m s e} (f : Fin n → Fin m) (offset : Nat) (p : Straight n s e) :
    reindexStraight f (shiftStraight offset p) = shiftStraight offset (reindexStraight f p) := by
  induction p <;> simp_all only [shiftStraight,reindexStraight]

theorem reindex_relabel {n m s e} (f : Fin n → Fin m) (w : Wire ≃ Wire) (p : Straight n s e) :
    reindexStraight f (relabelStraight w p) = relabelStraight w (reindexStraight f p) := by
  induction p with
  | done => simp only [reindexStraight,relabelStraight]
  | gate g p ih => cases g <;> simp only [reindexStraight,relabelStraight,reindexGate,relabelTemplateGate,ih]
  | recordGate i v g p ih => simp only [reindexStraight,relabelStraight,ih]
  | measure w p ih => simp only [reindexStraight,relabelStraight,ih]

def reindexedSurround {n m start d} (f : Fin n → Fin m) (before after : Circuit)
    (p : (count : Nat) × Straight n start (start+count)) (hp : Patch (reindexStraight f p.2) d) :
    Patch (reindexStraight f (surroundCompiled before after p).2) d := by
  unfold surroundCompiled prependCompiled
  rw [reindex_append]
  exact ((Patch.refl _).append
    ((reindexedAppendCompiled f p ⟨0,literalProgram after⟩ hp (Patch.refl _)).castSaving
      (Nat.add_zero d))).castSaving (Nat.zero_add d)

end
end ShorECDLP.Entrant.AliasLookup

namespace ShorECDLP.Entrant.AliasLookup
open Quantum Paper2607_13816
noncomputable section
set_option maxHeartbeats 100000
set_option Elab.async false

def maskParity : List Wire → Wire → Bool
  | [], _ => false
  | t::ts, w => xor (decide (w=t)) (maskParity ts w)

theorem maskParity_outside (mask : List Wire) (w : Wire) (h : w ∉ mask) :
    maskParity mask w = false := by
  induction mask with
  | nil => rfl
  | cons t ts ih =>
      simp only [List.mem_cons,not_or] at h
      simp only [maskParity,decide_eq_false h.1,ih h.2,Bool.false_xor]

def parityState (mask : List Wire) (active : Bool) (s : BasisState) : BasisState :=
  fun w => xor (s w) (active && maskParity mask w)

theorem run_tableXorGates_parity (q : Wire) (mask : List Wire) (s : BasisState)
    (hq : q ∉ mask) :
    Classical.run (tableXorGates q mask) s = parityState mask (s q) s := by
  induction mask generalizing s with
  | nil => funext w; simp [tableXorGates,Classical.run,parityState,maskParity]
  | cons t ts ih =>
      simp only [List.mem_cons,not_or] at hq
      simp only [tableXorGates,List.map_cons,Classical.run_cons,Classical.applyGate]
      change Classical.run (tableXorGates q ts) _ = _
      rw [ih _ hq.2]
      funext w
      by_cases hw : w=t
      · subst w
        cases htv : s t <;> cases hqv : s q <;> cases hpv : maskParity ts t <;>
          simp [parityState,maskParity,upd,hq.1,htv,hqv,hpv]
      · cases hqv : s q <;> cases hwv : s w <;> cases hpv : maskParity ts w <;>
          simp [parityState,maskParity,upd,hq.1,hw,hqv,hwv,hpv]

theorem parity_leafCommutator_classical (q p : Wire) (mask : List Wire)
    (hq : q ∉ mask) (hp : p ∉ mask) (hqp : q ≠ p) (s : BasisState) :
    Classical.run (leafCommutator q p mask) s = Classical.run (tableXorGates q mask) s := by
  simp only [leafCommutator,Classical.run_append,Classical.run_cons,Classical.run_nil,
    Classical.applyGate]
  rw [run_tableXorGates_parity p mask s hp,run_tableXorGates_parity p mask _ hp,
    run_tableXorGates_parity q mask s hq]
  funext w
  by_cases hw : w=p
  · subst w
    cases hqv : s q <;> cases hpv : s p <;>
      simp [parityState,upd,maskParity_outside mask q hq,maskParity_outside mask p hp,hqp,hqv,hpv]
  · cases hqv : s q <;> cases hpv : s p <;> cases hpar : maskParity mask w <;>
      simp [parityState,upd,maskParity_outside mask q hq,maskParity_outside mask p hp,hw,hqv,hpv,hpar]

theorem parity_nodePrefix_classical (q b p : Wire) (mask : List Wire)
    (hq : q ∉ mask) (hb : b ∉ mask) (hp : p ∉ mask)
    (hqb : q ≠ b) (hqp : q ≠ p) (hbp : b ≠ p) (s : BasisState) :
    Classical.run (nodePrefix q b p mask) s = Classical.run (reorderedPrefix q b p mask) s := by
  simp only [nodePrefix,reorderedPrefix,Classical.run_append]
  rw [parity_leafCommutator_classical q p mask hq hp hqp]
  simp only [computeZeroAnd,Classical.run_cons,Classical.run_nil,Classical.applyGate]
  rw [run_tableXorGates_parity q mask _ hq,run_tableXorGates_parity q mask _ hq]
  funext w
  by_cases hwp : w=p <;> by_cases hwb : w=b <;>
    cases hqv : s q <;> cases hbv : s b <;> cases hpv : s p <;>
    simp_all [parityState,upd,maskParity_outside]

theorem parity_nodePrefix_run (q b p : Wire) (mask : List Wire)
    (hq : q ∉ mask) (hb : b ∉ mask) (hp : p ∉ mask)
    (hqb : q ≠ b) (hqp : q ≠ p) (hbp : b ≠ p) :
    Quantum.run (nodePrefix q b p mask) = Quantum.run (reorderedPrefix q b p mask) := by
  apply linear_basis
  intro s
  rw [run_ket_agrees_classical _ _ (by simp [nodePrefix,leafCommutator,computeZeroAnd,tableXorGates_HPFree])]
  rw [run_ket_agrees_classical _ _ (by simp [reorderedPrefix,tableXorGates_HPFree])]
  rw [parity_nodePrefix_classical q b p mask hq hb hp hqb hqp hbp]

theorem parity_xor_conjugate (q b : Wire) (mask : List Wire)
    (hq : q ∉ mask) (hb : b ∉ mask) (hqb : q ≠ b) :
    Quantum.run ([.X b] ++ tableXorGates q mask ++ [.X b]) = Quantum.run (tableXorGates q mask) := by
  apply linear_basis
  intro s
  rw [run_ket_agrees_classical _ _ (by simp [tableXorGates_HPFree]),
    run_ket_agrees_classical _ _ (tableXorGates_HPFree q mask)]
  congr 1
  simp only [Classical.run_append,Classical.run_cons,Classical.run_nil,Classical.applyGate]
  rw [run_tableXorGates_parity q mask _ hq,run_tableXorGates_parity q mask _ hq]
  funext w
  by_cases hwb : w=b <;> cases hbv : s b <;>
    simp_all [parityState,upd,maskParity_outside]

theorem parity_node_branch (q b p : Wire) (mask : List Wire)
    (hq : q ∉ mask) (hb : b ∉ mask) (hp : p ∉ mask)
    (hqb : q ≠ b) (hqp : q ≠ p) (hbp : b ≠ p) (out : Bool) (psi : State) :
    applyGate (.X b) (Quantum.run (if out then controlledZ q b else [])
      (xResetKraus p out (Quantum.run (nodePrefix q b p mask) psi))) =
      xResetKraus p out (Quantum.run (leafCommutator q p mask) psi) := by
  rw [parity_nodePrefix_run q b p mask hq hb hp hqb hqp hbp]
  simp only [reorderedPrefix,Quantum.run_append,Quantum.run_singleton]
  rw [erase_compute q b p hqb hqp hbp]
  rw [applyGate_reset_commute (.X b) p out (by simpa [gateWires,ne_comm] using hbp)]
  have hx := congrArg (fun f : State →ₗ[ℂ] State => f psi) (parity_xor_conjugate q b mask hq hb hqb)
  simp only [Quantum.run_append,Quantum.run_singleton] at hx
  rw [hx]
  congr 1
  have hc : Quantum.run (leafCommutator q p mask) = Quantum.run (tableXorGates q mask) := by
    apply linear_basis
    intro s
    rw [run_ket_agrees_classical _ _ (by simp [leafCommutator,tableXorGates_HPFree]),
      run_ket_agrees_classical _ _ (tableXorGates_HPFree q mask),
      parity_leafCommutator_classical q p mask hq hp hqp]
  rw [hc]

end
end ShorECDLP.Entrant.AliasLookup

namespace ShorECDLP.Entrant.AliasLookup
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration Optimization
noncomputable section
set_option maxHeartbeats 100000
set_option Elab.async false

/-- A finite XOR leaf with a table-uniform interpretation; target repetitions are allowed. -/
structure XorLeaf (n : Nat) where
  code : Wire → List (TemplateGate n)
  mask : (ConstantBit n → Bool) → List Wire
  wires : List Wire
  source : ∀ q read, (code q).flatMap (TemplateGate.instantiate read) = tableXorGates q (mask read)
  support : ∀ read, mask read ⊆ wires

def endpointLeaf {n : Nat} (ports : List (Wire × EndpointBit n)) : XorLeaf n where
  code q := endpointSelectGates q ports
  mask read := endpointRawMask read ports
  wires := ports.map Prod.fst
  source := fun q read => endpointSelectGates_source read q ports
  support := fun _ => (List.Sublist.map Prod.fst List.filter_sublist).subset

def xorCommutator {n} (leaf : XorLeaf n) (q p : Wire) : List (TemplateGate n) :=
  leaf.code p ++ [.literal (.CX q p)] ++ leaf.code p ++ [.literal (.CX q p)]

def xorSourceNode {n} (leaf : XorLeaf n) (start : Nat) (q b p : Wire) : Straight n start (start+1) :=
  (gateProgram ((computeZeroAnd q b p).map TemplateGate.literal ++
    xorCommutator leaf q p ++ [.literal (.X b)])).append
      (.measure p (recordGates (Fin.last start) (controlledZ q b) (literalProgram [.X b])))

def xorRetainedNode {n} (leaf : XorLeaf n) (start : Nat) (q p : Wire) : Straight n start (start+1) :=
  (gateProgram (xorCommutator leaf q p)).append (.measure p .done)

theorem xorCommutator_instantiate {n} (leaf : XorLeaf n) (q p : Wire) (read : ConstantBit n → Bool) :
    (xorCommutator leaf q p).flatMap (TemplateGate.instantiate read) = leafCommutator q p (leaf.mask read) := by
  simp only [xorCommutator,List.flatMap_append,leaf.source,List.flatMap_cons,List.flatMap_nil,
    TemplateGate.instantiate,List.append_nil,leafCommutator]

theorem xorPrefix_instantiate {n} (leaf : XorLeaf n) (q b p : Wire) (read : ConstantBit n → Bool) :
    ((computeZeroAnd q b p).map TemplateGate.literal ++ xorCommutator leaf q p ++
      [TemplateGate.literal (tableSize := n) (.X b)]).flatMap (TemplateGate.instantiate read) = nodePrefix q b p (leaf.mask read) := by
  simp only [List.flatMap_append,literal_gates,xorCommutator_instantiate,List.flatMap_cons,
    List.flatMap_nil,TemplateGate.instantiate,List.append_nil,nodePrefix]

theorem xorSourceNode_run {n} (leaf : XorLeaf n) (start : Nat) (q b p : Wire)
    (hq : q ∉ leaf.wires) (hb : b ∉ leaf.wires) (hp : p ∉ leaf.wires)
    (hqb : q ≠ b) (hqp : q ≠ p) (hbp : b ≠ p)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((xorSourceNode leaf start q b p).instantiate read history).run =
      ((xorRetainedNode leaf start q p).instantiate read history).run := by
  have hqm : q ∉ leaf.mask read := fun h => hq (leaf.support read h)
  have hbm : b ∉ leaf.mask read := fun h => hb (leaf.support read h)
  have hpm : p ∉ leaf.mask read := fun h => hp (leaf.support read h)
  unfold xorSourceNode xorRetainedNode
  apply oneMeasure_congr
  · intro psi
    rw [xorPrefix_instantiate,xorCommutator_instantiate,Quantum.run_singleton]
    simpa only [if_false,Quantum.run_nil,LinearMap.id_coe,id_eq] using
      parity_node_branch q b p (leaf.mask read) hqm hbm hpm hqb hqp hbp false psi
  · intro psi
    rw [xorPrefix_instantiate,xorCommutator_instantiate,Quantum.run_singleton]
    simpa only [if_true] using
      parity_node_branch q b p (leaf.mask read) hqm hbm hpm hqb hqp hbp true psi

theorem xorSourceNode_drops {n} (leaf : XorLeaf n) (start : Nat) (q b p : Wire) :
    Drops (xorSourceNode leaf start q b p) (xorRetainedNode leaf start q p) 7 := by
  unfold xorSourceNode xorRetainedNode
  rw [List.append_assoc,gatePrefix_append,gatePrefix_append]
  simp only [computeZeroAnd,List.map_cons,List.map_nil,gateProgram,Straight.append]
  refine (show 0+7=7 by decide) ▸ Drops.skip (.X b) ?_
  refine (show 7+0=7 by decide) ▸ Drops.skip (.CCX q b p) ?_
  refine Drops.skip (.X b) (d := 0) ?_
  apply Drops.gatePrefix
  refine Drops.skip (.X b) (d := 0) ?_
  exact Drops.measure p (correction_drops (Fin.last start) q b)

def xorNodePatch {n} (leaf : XorLeaf n) (start : Nat) (q b p : Wire)
    (hq : q ∉ leaf.wires) (hb : b ∉ leaf.wires) (hp : p ∉ leaf.wires)
    (hqb : q ≠ b) (hqp : q ≠ p) (hbp : b ≠ p) :
    Patch (xorSourceNode leaf start q b p) 7 :=
  ⟨xorRetainedNode leaf start q p,xorSourceNode_drops leaf start q b p,
    Rewrites.semantic _ _ (xorSourceNode_run leaf start q b p hq hb hp hqb hqp hbp)⟩

end
end ShorECDLP.Entrant.AliasLookup

namespace ShorECDLP.Entrant.AliasLookup
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration Optimization
noncomputable section
set_option maxHeartbeats 100000
set_option Elab.async false

theorem xorBottomNode_eq {n} (leaves : Nat → XorLeaf n)
    (q b p l r start : Nat) (rest : List Wire) (he : leaves l = leaves r) :
    lookupProgram n (unaryLookupOps (fun l q => (leaves l).code q)
      (.node b (.leaf l) (.leaf r)) q (p::rest)) start =
      xorSourceNode (leaves l) start q b p := by
  simp only [unaryLookupOps, List.cons_append, List.nil_append,
    lookupProgram, ordinaryOp, lookupMeasurements, Nat.add_zero, ← he]
  simp only [xorSourceNode, xorCommutator, gatePrefix_append]
  rfl

/-- A finite plan chooses only aliased sibling pairs, preserving every traversal record. -/
inductive XorAliasPlan {n : Nat} (leaves : Nat → XorLeaf n) :
    UnaryActionTree → Wire → List Wire → Nat → Type where
  | keep (tree q anc) : XorAliasPlan leaves tree q anc 0
  | bottom (q b p l r : Nat) (rest : List Wire)
      (he : leaves l = leaves r)
      (hq : q ∉ (leaves l).wires) (hb : b ∉ (leaves l).wires)
      (hp : p ∉ (leaves l).wires)
      (hqb : q ≠ b) (hqp : q ≠ p) (hbp : b ≠ p) :
      XorAliasPlan leaves (.node b (.leaf l) (.leaf r)) q (p::rest) 7
  | node {q b p : Wire} {z o : UnaryActionTree} {rest : List Wire} {dz do_ : Nat}
      (zero : XorAliasPlan leaves z p rest dz) (one : XorAliasPlan leaves o p rest do_) :
      XorAliasPlan leaves (.node b z o) q (p::rest) (dz+do_)

def XorAliasPlan.patch {n} {leaves : Nat → XorLeaf n}
    {tree q anc d} (plan : XorAliasPlan leaves tree q anc d) (start : Nat) :
    Patch (lookupProgram n (unaryLookupOps (fun l q => (leaves l).code q) tree q anc) start) d := by
  induction plan generalizing start with
  | keep tree q anc => exact Patch.refl _
  | bottom q b p l r rest he hq hb hp hqb hqp hbp =>
      rw [xorBottomNode_eq leaves q b p l r start rest he]
      exact xorNodePatch (leaves l) start q b p hq hb hp hqb hqp hbp
  | @node q b p z o rest dz do_ zero one ihz iho =>
      rw [unaryLookupOps]
      refine (lookupAppendPatch (d := dz+do_) (e := 0) _ _ start ?_ (Patch.refl _)).castSaving (Nat.add_zero _)
      refine lookupAppendPatch (d := dz) (e := do_) _ _ _ ?_ (iho _)
      refine (lookupAppendPatch (d := dz) (e := 0) _ _ _ ?_ (Patch.refl _)).castSaving (Nat.add_zero _)
      exact (lookupAppendPatch (d := 0) (e := dz) _ _ _ (Patch.refl _) (ihz _)).castSaving (Nat.zero_add _)


/-- Periodic tables admit a cancellation at every last-level sibling pair. -/
def periodicXorPlan {n : Nat} (leaves : Nat → XorLeaf n)
    (bits : List Wire) (base stride q : Nat) (anc : List Wire)
    (hne : bits ≠ []) (hlen : bits.length ≤ anc.length)
    (hn : (q :: bits ++ anc).Nodup)
    (hd : ∀ l w, w ∈ q :: bits ++ anc → w ∉ (leaves l).wires)
    (hp : ∀ l, leaves l = leaves (l + stride * 2^(bits.length-1))) :
    XorAliasPlan leaves (tableAddressTree bits base stride) q anc (7 * 2^(bits.length-1)) := by
  induction bits generalizing base stride q anc with
  | nil => exact False.elim (hne rfl)
  | cons bit bits ih =>
      cases anc with
      | nil => simp at hlen
      | cons path rest =>
        have hdrop : (bits ++ path::rest).Nodup :=
          (List.nodup_cons.mp (List.nodup_cons.mp hn).2).2
        have hchild : (path::bits++rest).Nodup := List.perm_middle.nodup_iff.mp hdrop
        have hdchild : ∀ l w, w ∈ path::bits++rest → w ∉ (leaves l).wires := by
          intro l w hw
          apply hd l w
          simp only [List.mem_cons, List.mem_append] at hw ⊢
          tauto
        cases bits with
        | nil =>
            simp only [List.length_cons, List.length_nil, Nat.sub_self, pow_zero, Nat.mul_one,
              tableAddressTree] at hp ⊢
            apply XorAliasPlan.bottom q bit path base (base+stride) rest (hp base)
            · exact hd base q (by simp)
            · exact hd base bit (by simp)
            · exact hd base path (by simp)
            · have h := (List.nodup_cons.mp hn).1; simpa using fun he => h (by simp [he])
            · have h := (List.nodup_cons.mp hn).1; simpa using fun he => h (by simp [he])
            · have h := (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
              simpa using fun he => h (by simp [he])
        | cons next tail =>
            have hperiod : ∀ l, leaves l = leaves (l + (2*stride) * 2^((next::tail).length-1)) := by
              intro l
              convert hp l using 2
              simp only [List.length_cons, Nat.add_sub_cancel, pow_succ]
              ring
            have hzero := ih base (2*stride) path rest (by simp) (by simpa using hlen)
              hchild hdchild hperiod
            have hone := ih (base+stride) (2*stride) path rest (by simp) (by simpa using hlen)
              hchild hdchild hperiod
            have he : 7 * 2^((bit::next::tail).length-1) =
                7 * 2^((next::tail).length-1) + 7 * 2^((next::tail).length-1) := by
              simp only [List.length_cons, Nat.add_sub_cancel, pow_succ]
              omega
            rw [he]
            exact XorAliasPlan.node hzero hone

end
end ShorECDLP.Entrant.AliasLookup

namespace ShorECDLP.Entrant.AliasLookup
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration Optimization
noncomputable section
set_option maxHeartbeats 100000
set_option Elab.async false

def reindexEndpoint {n m} (f : Fin n → Fin m) : EndpointBit n → EndpointBit m
  | .inl b => .inl b
  | .inr b => .inr (reindexBit f b)

def reindexEndpointPorts {n m} (f : Fin n → Fin m) (ports : List (Wire × EndpointBit n)) :=
  ports.map (fun x => (x.1, reindexEndpoint f x.2))

theorem reindex_endpointSelectGate {n m} (f : Fin n → Fin m) (q w : Wire) (b : EndpointBit n) :
    (endpointSelectGate q (w,b)).map (reindexGate f) = endpointSelectGate q (w,reindexEndpoint f b) := by
  cases b with
  | inl b => cases b <;> rfl
  | inr b => rfl

theorem reindex_endpointSelectGates {n m} (f : Fin n → Fin m) (q : Wire)
    (ports : List (Wire × EndpointBit n)) :
    (endpointSelectGates q ports).map (reindexGate f) =
      endpointSelectGates q (reindexEndpointPorts f ports) := by
  induction ports with
  | nil => rfl
  | cons x xs ih =>
    simp only [endpointSelectGates,reindexEndpointPorts,List.flatMap_cons,List.map_cons,
      List.map_append] at ih ⊢
    rw [reindex_endpointSelectGate,ih]

theorem reindex_endpointFieldWord {n m} (f : Fin n → Fin m) (row : Fin n)
    (tag : EndpointBit n) (fx fy : Option PointField) (i : Fin 513) :
    reindexEndpoint f (endpointFieldWord row tag fx fy i) =
      endpointFieldWord (f row) (reindexEndpoint f tag) fx fy i := by
  unfold endpointFieldWord
  split_ifs <;> cases fx <;> cases fy <;> rfl

theorem reindex_exceptionalEndpointWords {n m} (f : Fin n → Fin m) (row : Fin n)
    (j : Fin 8) (i : Fin 513) :
    reindexEndpoint f (exceptionalEndpointWords row j i) = exceptionalEndpointWords (f row) j i := by
  fin_cases j <;> simp [exceptionalEndpointWords]
  all_goals rw [reindex_endpointFieldWord]; rfl

theorem reindex_unaryOps_generic {n m} (f : Fin n → Fin m)
    (leaf : Nat → Wire → List (TemplateGate n)) (tree : UnaryActionTree) (q : Wire) (anc : List Wire) :
    (unaryLookupOps leaf tree q anc).map (reindexOp f) =
      unaryLookupOps (fun l q => (leaf l q).map (reindexGate f)) tree q anc := by
  induction tree generalizing q anc with
  | leaf l => rfl
  | node b z o ihz iho =>
    cases anc with
    | nil => rfl
    | cons p rest =>
      simp only [unaryLookupOps,List.map_append,List.map_cons,List.map_nil,ihz,iho,
        reindexOp,ordinaryOp,List.map_map]
      rfl

theorem aliasRow_periodic (label : Nat) :
    aliasRow ⟨label % 32768, Nat.mod_lt _ (by decide)⟩ =
      aliasRow ⟨(label+16384) % 32768, Nat.mod_lt _ (by decide)⟩ := by
  apply Fin.ext
  simp only [aliasRow,Nat.mod_mod_of_dvd _ (by decide : 16384 ∣ 32768)]
  omega

end
end ShorECDLP.Entrant.AliasLookup

namespace ShorECDLP.Entrant.AliasLookup
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration Optimization
noncomputable section
set_option maxHeartbeats 100000
set_option maxRecDepth 10000
set_option Elab.async false

theorem reindex_ipxPorts {n m} (f : Fin n → Fin m) (row : Fin n) (u : Fin 8) :
    reindexEndpointPorts f (ipxPorts row u) = ipxPorts (f row) u := by
  simp only [reindexEndpointPorts,ipxPorts,List.map_ofFn]
  congr 1
  funext i
  exact congrArg (fun b => (accumulatorPort i,b)) (reindex_exceptionalEndpointWords f row u i)

theorem reindex_ipxPortsOpt {n m} (f : Fin n → Fin m) (row : Fin n) (v : Option (Fin 8)) :
    reindexEndpointPorts f (ipxPortsOpt row v) = ipxPortsOpt (f row) v := by
  cases v with
  | none => rfl
  | some v => exact reindex_ipxPorts f row v

theorem reindex_ipxLeaf {n m} (f : Fin n → Fin m) (row : Fin n) (q : Wire)
    (u : Fin 8) (v : Option (Fin 8)) :
    (ipxLeaf row q u v).map (reindexGate f) = ipxLeaf (f row) q u v := by
  simp only [ipxLeaf,List.map_append,reindex_endpointSelectGates,reindex_ipxPorts,reindex_ipxPortsOpt]

def ipxXorLeaf {n} (row : Fin n) (u : Fin 8) (v : Option (Fin 8)) : XorLeaf n :=
  endpointLeaf (ipxPorts row u ++ ipxPortsOpt row v)

theorem ipxXorLeaf_code {n} (row : Fin n) (u : Fin 8) (v : Option (Fin 8)) (q : Wire) :
    (ipxXorLeaf row u v).code q = ipxLeaf row q u v := by
  simp only [ipxXorLeaf,endpointLeaf,endpointSelectGates,List.flatMap_append,ipxLeaf]

theorem ipxPorts_wires {n} (row : Fin n) (u : Fin 8) :
    (ipxPorts row u).map Prod.fst = List.ofFn accumulatorPort := by
  simp only [ipxPorts,List.map_ofFn]
  rfl

theorem ipxXorLeaf_wires {n} (row : Fin n) (u : Fin 8) (v : Option (Fin 8)) :
    (ipxXorLeaf row u v).wires ⊆ List.ofFn accumulatorPort := by
  change (ipxPorts row u ++ ipxPortsOpt row v).map Prod.fst ⊆ _
  cases v with
  | none =>
    simp only [ipxPortsOpt,List.append_nil,ipxPorts_wires]
    exact List.Subset.refl _
  | some v =>
    simp only [ipxPortsOpt,List.map_append,ipxPorts_wires]
    intro w hw
    exact (List.mem_append.mp hw).elim id id

theorem ipxControl_nodup (c : Option (Fin 4)) :
    (ipxControl c :: pointLookupAddress ++ pointLookupPath).Nodup := by
  cases c with
  | none => decide
  | some k => fin_cases k <;> decide

theorem ipxTarget_disjoint (c : Option (Fin 4)) (w : Wire)
    (hw : w ∈ ipxControl c :: pointLookupAddress ++ pointLookupPath) :
    w ∉ List.ofFn accumulatorPort := by
  intro ht
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp ht
  have hr : (263 ≤ w ∧ w < 519) ∨ (580 ≤ w ∧ w < 836) ∨ w = 838 := by
    rw [← hi]
    unfold accumulatorPort
    split_ifs <;> (try dsimp only [Wire] at *) <;> omega
  have hc : ipxControl c < 4 ∨ ipxControl c = 836 := by
    cases c with
    | none => exact Or.inr rfl
    | some k => exact Or.inl k.isLt
  simp only [pointLookupAddress,pointLookupPath,List.mem_cons,List.mem_append,List.mem_range'] at hw
  dsimp only [Wire] at *
  omega

attribute [local irreducible] lookupProgram unaryLookupOps batchWindowTree ipxLeaf ipxOps
  ipxMeasuredTestOps ipxProgramOf reindexStraight

def ipxQueryAliasPatch (c : Option (Fin 4)) (u : Fin 8) (v : Option (Fin 8)) (start : Nat) :
    Patch (lookupProgram 32768 ((unaryLookupOps
      (fun l q => ipxLeaf (Single.Physical.tableRows l) q u v)
      batchWindowTree (ipxControl c) pointLookupPath).map (reindexOp aliasRow)) start) 114688 := by
  rw [reindex_unaryOps_generic]
  have hmap : (fun l q => (ipxLeaf (Single.Physical.tableRows l) q u v).map (reindexGate aliasRow)) =
      (fun l q => ipxLeaf (aliasRow (Single.Physical.tableRows l)) q u v) := by
    funext l q
    exact reindex_ipxLeaf aliasRow _ q u v
  rw [hmap]
  let leaves := fun l => ipxXorLeaf (aliasRow (Single.Physical.tableRows l)) u v
  have he : (fun l q => ipxLeaf (aliasRow (Single.Physical.tableRows l)) q u v) =
      (fun l q => (leaves l).code q) := by
    funext l q
    exact (ipxXorLeaf_code _ u v q).symm
  rw [he]
  have plan := periodicXorPlan leaves pointLookupAddress 0 1 (ipxControl c) pointLookupPath
    (by decide) (by decide) (ipxControl_nodup c)
    (by intro l w hw ht; exact ipxTarget_disjoint c w hw (ipxXorLeaf_wires _ u v ht))
    (by
      intro l
      have hr : aliasRow (Single.Physical.tableRows l) =
          aliasRow (Single.Physical.tableRows (l+16384)) := aliasRow_periodic l
      exact congrArg (fun row => ipxXorLeaf row u v) hr)
  unfold batchWindowTree
  exact plan.patch start

def ipxOpsAliasPatch (ops : List IpxOp) (start : Nat) :
    Patch (lookupProgram 32768 ((ipxOps Single.Physical.tableRows batchWindowTree
      pointLookupPath ops).map (reindexOp aliasRow)) start) (114688 * ipxQueries ops) := by
  induction ops generalizing start with
  | nil => exact Patch.refl _
  | cons op ops ih =>
    cases op with
    | query c u v =>
      rw [ipxOps,List.map_append]
      exact (lookupAppendPatch _ _ start (ipxQueryAliasPatch c u v start) (ih _)).castSaving
        (by rw [ipxQueries]; omega)
    | test k =>
      rw [ipxOps,List.map_append]
      exact (lookupAppendPatch _ _ start (Patch.refl _) (ih _)).castSaving (Nat.zero_add _)

def placedAliasPatch (start : Nat) :
    Patch (reindexStraight aliasRow (Single.Physical.placedProgram start).2) 1490944 := by
  unfold Single.Physical.placedProgram ipxProgramOf
  apply lookupReindexPatch
  exact (ipxOpsAliasPatch ipxSchedule start).castSaving (by rw [ipxSchedule_queries])

end
end ShorECDLP.Entrant.AliasLookup

namespace ShorECDLP.Entrant.AliasLookup
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration Optimization
noncomputable section
set_option maxHeartbeats 200000
set_option Elab.async false
attribute [local irreducible] reindexStraight sequenceProgram appendCompiled fieldLookupAddProgram signedFieldProgram
  BorrowFlag.adaptiveCoordinateProgram BorrowFlag.divisionProgram BorrowFlag.multiplicationProgram
  pointSquareProgram xNegateProgram yNegateProgram

variable (hd : ∀ start, Patch (BorrowFlag.divisionProgram 32768 start).2 7772030)
  (hm : ∀ start, Patch (BorrowFlag.multiplicationProgram 32768 start).2 7772030)

def coordinateAliasPatch (start : Nat) :
    Patch (reindexStraight aliasRow (BorrowFlag.adaptiveCoordinateProgram start).2) 16690940 := by
  unfold BorrowFlag.adaptiveCoordinateProgram BorrowFlag.adaptiveCoordinateSegments
  refine (reindexedSequenceCons (d := 229376) (e := 16461564) aliasRow _ _ (fieldAddAliasPatch .negX _ _) ?_).castSaving (by decide)
  refine (reindexedSequenceCons (d := 229376) (e := 16232188) aliasRow _ _ (signedFieldAliasPatch .negY _) ?_).castSaving (by decide)
  refine (reindexedSequenceCons (d := 7772030) (e := 8460158) aliasRow _ _ ((hd _).reindex aliasRow) ?_).castSaving (by decide)
  refine (reindexedSequenceCons (d := 0) (e := 8460158) aliasRow _ _ (Patch.refl _) ?_).castSaving (by decide)
  refine (reindexedSequenceCons (d := 229376) (e := 8230782) aliasRow _ _ (fieldAddAliasPatch .tripleX _ _) ?_).castSaving (by decide)
  refine (reindexedSequenceCons (d := 7772030) (e := 458752) aliasRow _ _ ((hm _).reindex aliasRow) ?_).castSaving (by decide)
  refine (reindexedSequenceCons (d := 0) (e := 458752) aliasRow _ _ (Patch.refl _) ?_).castSaving (by decide)
  refine (reindexedSequenceCons (d := 229376) (e := 229376) aliasRow _ _ (fieldAddAliasPatch .x _ _) ?_).castSaving (by decide)
  refine (reindexedSequenceCons (d := 229376) (e := 0) aliasRow _ _ (signedFieldAliasPatch .negY _) ?_).castSaving (by decide)
  exact Patch.refl _

def coreAliasPatch (start : Nat) :
    Patch (reindexStraight aliasRow (Single.Physical.core start).2) 18181884 := by
  unfold Single.Physical.core Single.Physical.segments
  refine (reindexedSequenceCons (d := 16690940) (e := 1490944) aliasRow _ _
    (coordinateAliasPatch hd hm start) ?_).castSaving (by decide)
  refine (reindexedSequenceCons (d := 0) (e := 1490944) aliasRow _ _
    (Patch.refl _) ?_).castSaving (Nat.zero_add _)
  exact (reindexedSequenceCons (d := 1490944) (e := 0) aliasRow _ _
    (placedAliasPatch _) (Patch.refl _)).castSaving (Nat.add_zero _)

def preparedAliasPatch (start : Nat) :
    Patch (reindexStraight aliasRow (Single.Physical.prepared start).2) 18181884 := by
  unfold Single.Physical.prepared
  exact reindexedSurround aliasRow _ _ _ (coreAliasPatch hd hm start)

def actualAliasPatch (start : Nat) :
    Patch (reindexStraight aliasRow (Single.Physical.actual.program start)) 18181884 := by
  unfold Single.Physical.actual closedWindow
  rw [reindex_shift,reindex_cast,reindex_relabel]
  exact (((preparedAliasPatch hd hm 0).relabel (windowAddressPerm 855 (by decide))).castFinish _).shift start

def left15AliasPatch (j : Fin 10) (start : Nat) :
    Patch ((Single.signedWindow (.left15 j)).program start) 18181884 := by
  have h := (actualAliasPatch hd hm start).reindex (Single.signedRow (.left15 j))
  rw [reindex_comp] at h
  have he : Single.signedRow (.left15 j) ∘ aliasRow = Single.signedRow (.left15 j) := by
    funext a
    exact (Single.left15_alias j a).symm
  rw [he] at h
  unfold Single.signedWindow
  exact h

def right15AliasPatch (j : Fin 1) (start : Nat) :
    Patch ((Single.signedWindow (.right15 j)).program start) 18181884 := by
  have h := (actualAliasPatch hd hm start).reindex (Single.signedRow (.right15 j))
  rw [reindex_comp] at h
  have he : Single.signedRow (.right15 j) ∘ aliasRow = Single.signedRow (.right15 j) := by
    funext a
    exact (Single.right15_alias j a).symm
  rw [he] at h
  unfold Single.signedWindow
  exact h

end
end ShorECDLP.Entrant.AliasLookup





namespace ShorECDLP.Entrant.Fanout
open Quantum Classical Paper2607_13816
noncomputable section
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option Elab.async false

def before (a b flag : Wire) (mask : List Wire) : Circuit :=
  [.CCX a b flag] ++ tableXorGates flag mask ++ [.CCX a b flag]

def after (a b flag pivot : Wire) (rest : List Wire) : Circuit :=
  tableXorGates flag (pivot::rest) ++ tableXorGates pivot rest ++
    [.CCX a b pivot] ++ tableXorGates pivot rest

theorem before_HPFree (a b flag : Wire) (mask : List Wire) : HPFree (before a b flag mask) := by
  simp [before,tableXorGates_HPFree]

theorem after_HPFree (a b flag pivot : Wire) (rest : List Wire) : HPFree (after a b flag pivot rest) := by
  simp [after,tableXorGates_HPFree]

theorem merge_classical (a b flag pivot : Wire) (rest : List Wire)
    (hn : (pivot::rest).Nodup) (ha : a ∉ pivot::rest) (hb : b ∉ pivot::rest)
    (hf : flag ∉ pivot::rest) (hfa : flag ≠ a) (hfb : flag ≠ b) (s : BasisState) :
    Classical.run (before a b flag (pivot::rest)) s =
      Classical.run (after a b flag pivot rest) s := by
  have hr := (List.nodup_cons.mp hn).2
  have hp := (List.nodup_cons.mp hn).1
  have ham : a ≠ pivot ∧ a ∉ rest := by simpa using ha
  have hbm : b ≠ pivot ∧ b ∉ rest := by simpa using hb
  have hfm : flag ≠ pivot ∧ flag ∉ rest := by simpa using hf
  have hpa := ham.1.symm
  have hpb := hbm.1.symm
  have hpf := hfm.1.symm
  have haf := hfa.symm
  have hbf := hfb.symm
  simp only [before,after,Classical.run_append,Classical.run_cons,Classical.run_nil,Classical.applyGate]
  rw [run_tableXorGates flag (pivot::rest) _ hn hf]
  rw [run_tableXorGates flag (pivot::rest) _ hn hf]
  rw [run_tableXorGates pivot rest _ hr hp]
  rw [run_tableXorGates pivot rest _ hr hp]
  funext w
  by_cases hwf : w = flag <;> by_cases hwp : w = pivot <;>
    cases hva : s a <;> cases hvb : s b <;> cases hvf : s flag <;> cases hvp : s pivot <;>
    cases hmem : decide (w ∈ rest) <;> simp_all [tableXorState,upd]

theorem merge_run (a b flag pivot : Wire) (rest : List Wire)
    (hn : (pivot::rest).Nodup) (ha : a ∉ pivot::rest) (hb : b ∉ pivot::rest)
    (hf : flag ∉ pivot::rest) (hfa : flag ≠ a) (hfb : flag ≠ b) :
    Quantum.run (before a b flag (pivot::rest)) = Quantum.run (after a b flag pivot rest) := by
  apply AliasLookup.linear_basis
  intro s
  rw [run_ket_agrees_classical _ _ (before_HPFree a b flag (pivot::rest)),
    run_ket_agrees_classical _ _ (after_HPFree a b flag pivot rest),
    merge_classical a b flag pivot rest hn ha hb hf hfa hfb]

end
end ShorECDLP.Entrant.Fanout

namespace ShorECDLP.Entrant.FanoutInitializer
open Quantum Classical Paper2607_13816 Initializer
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 10000
set_option Elab.async false

def writeMask : List Wire → Nat → List Wire
  | [], _ => []
  | w::ws, v => (if v.testBit 0 then [w] else []) ++ writeMask ws (v/2)

theorem writeMask_eq (flag : Wire) (ws : List Wire) (v : Nat) :
    controlledXorConstant flag ws v = tableXorGates flag (writeMask ws v) := by
  induction ws generalizing v with
  | nil => rfl
  | cons w ws ih =>
    simp only [controlledXorConstant,writeMask,tableXorGates,List.map_append]
    rw [ih]
    split <;> rfl

def merged (a b flag : Wire) : List Wire → Circuit
  | [] => []
  | p::ps => Fanout.after a b flag p ps

theorem merged_run (a b flag : Wire) (mask : List Wire)
    (hn : (a::b::flag::mask).Nodup) :
    Quantum.run (Fanout.before a b flag mask) = Quantum.run (merged a b flag mask) := by
  have ha := (List.nodup_cons.mp hn).1
  have hb := (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
  have hrest := (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp hn).2).2)
  have hfa : flag ≠ a := by intro he; apply ha; simp [he]
  have hfb : flag ≠ b := by intro he; apply hb; simp [he]
  cases mask with
  | nil =>
    apply LinearMap.ext
    intro psi
    have hw : CircuitWellFormed [.CCX a b flag] := by
      simp only [CircuitWellFormed,List.mem_singleton]
      intro g hg
      subst g
      simp only [Gate.WellFormed]
      constructor
      · intro he; apply ha; simp [he]
      constructor
      · exact hfa.symm
      · exact hfb.symm
    have h := Quantum.run_run_adjoint [.CCX a b flag] hw psi
    simpa only [Fanout.before,merged,tableXorGates,List.map_nil,List.append_nil,
      Quantum.run_append,Quantum.run_nil,LinearMap.id_coe,id_eq,Circuit.adjoint,
      List.reverse_cons,List.reverse_nil,List.nil_append,List.map_cons,Gate.adjoint] using h
  | cons p ps =>
    exact Fanout.merge_run a b flag p ps hrest.2
      (fun h => ha (by simp [h])) (fun h => hb (by simp [h])) hrest.1 hfa hfb

def mid (r : Initializer.Row) : Circuit :=
  match Initializer.leaf r.1 558 Initializer.scratch with
  | [.CCX a b flag] =>
    let mask := writeMask Initializer.targets r.2.2
    if flag = 558 ∧ (a::b::flag::mask).Nodup then merged a b flag mask else Initializer.mid r
  | _ => Initializer.mid r

theorem mid_run (r : Initializer.Row) : Quantum.run (mid r) = Quantum.run (Initializer.mid r) := by
  unfold mid
  split
  next a b flag he =>
    dsimp only
    split
    next h =>
      have hm := merged_run a b flag (writeMask Initializer.targets r.2.2) h.2
      unfold Initializer.mid
      rw [he,writeMask_eq,← h.1]
      exact hm.symm
    next h => rfl
  next h => rfl

def tail (a : Initializer.Row) : List Initializer.Row → Circuit
  | [] => mid a ++ Initializer.after a.1 a.2.1 Initializer.scratch Initializer.modulus
  | b::rs => mid a ++ Initializer.transition a b ++ tail b rs

def program : List Initializer.Row → Circuit
  | [] => []
  | a::rs => Initializer.before a.1 a.2.1 Initializer.scratch Initializer.modulus ++ tail a rs

theorem tail_run (a : Initializer.Row) (rs : List Initializer.Row) :
    Quantum.run (tail a rs) = Quantum.run (Initializer.sharedTail a rs) := by
  induction rs generalizing a with
  | nil => simp only [tail,Initializer.sharedTail,Quantum.run_append_map,mid_run]
  | cons b rs ih => simp only [tail,Initializer.sharedTail,Quantum.run_append_map,mid_run,ih]

theorem program_run (rs : List Initializer.Row) : Quantum.run (program rs) = Quantum.run (Initializer.shared rs) := by
  cases rs with
  | nil => rfl
  | cons a rs => simp only [program,Initializer.shared,Quantum.run_append_map,tail_run]

theorem initializer_run :
    Quantum.run (lengthInitialize (List.range' 266 256) Initializer.targets 558 Initializer.scratch Initializer.modulus) =
      Quantum.run (program Initializer.rows) := Initializer.initializer_shared_run.trans (program_run _).symm

private instance gateWFDecidable (g : Gate) : Decidable g.WellFormed := by
  cases g <;> unfold Gate.WellFormed <;> infer_instance

private instance gateClassicalDecidable (g : Gate) : Decidable (IsClassicalGate g) := by
  cases g <;> unfold IsClassicalGate <;> infer_instance

private theorem program_checks :
    eeaToffoliCount (program Initializer.rows) = 763 ∧
    (program Initializer.rows).length = 4346 ∧
    CircuitWellFormed (program Initializer.rows) ∧ HPFree (program Initializer.rows) := by
  unfold CircuitWellFormed HPFree
  decide +kernel

theorem program_ccx : eeaToffoliCount (program Initializer.rows) = 763 := program_checks.1

theorem program_length : (program Initializer.rows).length = 4346 := program_checks.2.1

theorem program_wellFormed : CircuitWellFormed (program Initializer.rows) := program_checks.2.2.1

theorem program_HPFree : HPFree (program Initializer.rows) := program_checks.2.2.2

theorem program_t : ShorECDLP.tCount (program Initializer.rows) = 5341 := by
  rw [Initializer.classical_toffoli_cost _ program_HPFree,program_ccx]

private theorem source_t : ShorECDLP.tCount
    (lengthInitialize (List.range' 266 256) Initializer.targets 558 Initializer.scratch Initializer.modulus) = 917476 := by
  have h := lengthInitialize_counts (List.range' 266 256) Initializer.targets 558 Initializer.scratch Initializer.modulus
    (by decide +kernel)
  rw [h.2.2]
  decide +kernel

theorem initializer_t : ShorECDLP.tCount (program Initializer.rows) + 912135 =
    ShorECDLP.tCount (lengthInitialize (List.range' 266 256) Initializer.targets 558 Initializer.scratch Initializer.modulus) := by
  rw [program_t,source_t]

private theorem cost_le_length (gs : Circuit) : ShorECDLP.tCount gs ≤ 7 * gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    cases g <;> simp_all [ShorECDLP.tCount,ShorECDLP.tCost] <;> omega

theorem initializer_length : (program Initializer.rows).length ≤
    (lengthInitialize (List.range' 266 256) Initializer.targets 558 Initializer.scratch Initializer.modulus).length := by
  have h := cost_le_length (lengthInitialize (List.range' 266 256) Initializer.targets 558 Initializer.scratch Initializer.modulus)
  have ht := initializer_t
  rw [program_t] at ht
  rw [program_length]
  omega

end
end ShorECDLP.Entrant.FanoutInitializer

namespace ShorECDLP.Entrant.FanoutInitializer
open Quantum Classical Paper2607_13816 Initializer
noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option Elab.async false

theorem wires_append (xs ys : Circuit) : circuitWires (xs++ys) = circuitWires xs ++ circuitWires ys :=
  List.flatMap_append

theorem xor_wires (q : Wire) (mask : List Wire) (w : Wire) :
    w ∈ circuitWires (tableXorGates q mask) ↔ (w=q ∧ mask ≠ []) ∨ w ∈ mask := by
  induction mask with
  | nil => simp [tableXorGates,circuitWires]
  | cons x xs ih =>
    simp only [tableXorGates,List.map_cons,circuitWires,List.flatMap_cons,gateWires,List.mem_append,
      List.mem_cons,List.not_mem_nil,or_false] at ih ⊢
    tauto

theorem fanout_support (a b flag p : Wire) (ps : List Wire) :
    circuitWires (Fanout.after a b flag p ps) ⊆ circuitWires (Fanout.before a b flag (p::ps)) := by
  intro w hw
  simp only [Fanout.after,Fanout.before,wires_append,List.mem_append,xor_wires,
    show circuitWires [.CCX a b p] = [a,b,p] by rfl,
    show circuitWires [.CCX a b flag] = [a,b,flag] by rfl,
    List.mem_cons,List.not_mem_nil,or_false] at hw ⊢
  tauto

theorem merged_support (a b flag : Wire) (mask : List Wire) :
    circuitWires (merged a b flag mask) ⊆ circuitWires (Fanout.before a b flag mask) := by
  cases mask with
  | nil => simp [merged,circuitWires]
  | cons p ps => exact fanout_support a b flag p ps

theorem mid_support (r : Initializer.Row) : circuitWires (mid r) ⊆ circuitWires (Initializer.mid r) := by
  unfold mid
  split
  next a b flag he =>
    dsimp only
    split
    next h =>
      unfold Initializer.mid
      rw [he,writeMask_eq,← h.1]
      exact merged_support a b flag _
    next h => exact List.Subset.refl _
  next h => exact List.Subset.refl _

theorem append_support {a b c d : Circuit}
    (ha : circuitWires a ⊆ circuitWires b) (hb : circuitWires c ⊆ circuitWires d) :
    circuitWires (a++c) ⊆ circuitWires (b++d) := by
  rw [wires_append,wires_append]
  intro w hw
  exact List.mem_append.mpr ((List.mem_append.mp hw).imp (fun h => ha h) (fun h => hb h))

theorem tail_support (a : Initializer.Row) (rs : List Initializer.Row) :
    circuitWires (tail a rs) ⊆ circuitWires (Initializer.sharedTail a rs) := by
  induction rs generalizing a with
  | nil => exact append_support (mid_support a) (List.Subset.refl _)
  | cons b rs ih => exact append_support (append_support (mid_support a) (List.Subset.refl _)) (ih b)

theorem program_support (rs : List Initializer.Row) :
    circuitWires (program rs) ⊆ circuitWires (Initializer.shared rs) := by
  cases rs with
  | nil => exact List.Subset.refl _
  | cons a rs => exact append_support (List.Subset.refl _) (tail_support a rs)

theorem initializer_support : circuitWires (program Initializer.rows) ⊆
    circuitWires (lengthInitialize (List.range' 266 256) Initializer.targets 558 Initializer.scratch Initializer.modulus) := by
  intro w hw
  obtain ⟨g,hg,hwg⟩ := List.mem_flatMap.mp (program_support Initializer.rows hw)
  exact List.mem_flatMap.mpr ⟨g,Initializer.initializer_shared_sublist.subset hg,hwg⟩

end
end ShorECDLP.Entrant.FanoutInitializer

namespace ShorECDLP.Entrant.FanoutInitializer
open Quantum Classical Paper2607_13816 Optimization

theorem initializer_bound : LiteralBound
    (lengthInitialize (List.range' 266 256) Initializer.targets 558 Initializer.scratch Initializer.modulus)
    (program Initializer.rows) 912135 := by
  refine ⟨program_wellFormed,initializer_length,initializer_t,initializer_support,?_⟩
  have hf := lengthInitialize_HPFree (List.range' 266 256) Initializer.targets 558 Initializer.scratch Initializer.modulus
  rw [← Initializer.classical_toffoli_cost _ hf,
    ← Initializer.classical_toffoli_cost _ program_HPFree]
  exact Nat.le_of_eq initializer_t.symm
end ShorECDLP.Entrant.FanoutInitializer

/-! Adjacent target and control conjugation rewrites adapted from spariev's
2984615e-7dc0-4ff7-8dc3-897d9f9dc165 (GPT 6.1 Sol / Codex).
The literal resource certificates below connect them to the retained compiler. -/
namespace ShorECDLP.Entrant.Transport
open Quantum
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def source (a b t u : Wire) : Circuit := [.CCX a b t,.CX t u,.CCX a b t]
def reduced (a b t u : Wire) : Circuit := [.CX t u,.CCX a b u]

theorem classical_identity (a b t u : Wire)
    (hat : a≠t) (hbt : b≠t) (hau : a≠u) (hbu : b≠u) (htu : t≠u)
    (s : BasisState) : Classical.run (source a b t u) s=Classical.run (reduced a b t u) s := by
  funext w
  simp only [source,reduced,Classical.run,List.foldl_cons,List.foldl_nil,Classical.applyGate]
  by_cases hwu : w=u
  · subst w
    simp [upd,Ne.symm hat,Ne.symm hbt,Ne.symm hau,Ne.symm hbu,htu,Ne.symm htu,
      hat,hbt,hau,hbu,Bool.xor_assoc,Bool.xor_left_comm,Bool.xor_comm]
  · by_cases hwt : w=t
    · subst w
      simp [upd,Ne.symm hat,Ne.symm hbt,Ne.symm hau,Ne.symm hbu,htu,Ne.symm htu,
        hat,hbt,hau,hbu,Bool.xor_assoc]
    · simp [upd,hwu,hwt]

theorem run_identity (a b t u : Wire)
    (hat : a≠t) (hbt : b≠t) (hau : a≠u) (hbu : b≠u) (htu : t≠u) :
    Quantum.run (source a b t u)=Quantum.run (reduced a b t u) := by
  have hk (s : BasisState) : Quantum.run (source a b t u) (ket s)=
      Quantum.run (reduced a b t u) (ket s) := by
    rw [run_ket_agrees_classical _ _ (by simp [source,Classical.HPFree,Classical.IsClassicalGate]),
      run_ket_agrees_classical _ _ (by simp [reduced,Classical.HPFree,Classical.IsClassicalGate]),
      classical_identity a b t u hat hbt hau hbu htu]
  apply LinearMap.ext
  intro ψ
  induction ψ using Finsupp.induction with
  | zero=>simp only [map_zero]
  | @single_add s c ψ hs hc ih=>
    have he : Finsupp.single s c=c•ket s := by simp [ket]
    simp only [map_add,he,map_smul,ih,hk]

/-- Only adjacent exact conjugations are compressed; no clean-workspace premise. -/
def optimize : Circuit→Circuit
  | .CCX a b t :: .CX v u :: .CCX c d z :: rest=>
    if a=c ∧ b=d ∧ t=v ∧ t=z ∧ a≠u ∧ b≠u ∧ t≠u ∧ a≠t ∧ b≠t then
      .CX t u :: .CCX a b u :: optimize rest
    else .CCX a b t :: optimize (.CX v u :: .CCX c d z :: rest)
  | g::rest=>g::optimize rest
  | []=>[]

end ShorECDLP.Entrant.Transport
namespace ShorECDLP.Entrant.Transport
open Quantum
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

inductive Reduction : Circuit→Circuit→Prop where
  | nil : Reduction List.nil List.nil
  | keep (g : Gate) {xs ys : Circuit} : Reduction xs ys→Reduction (g::xs) (g::ys)
  | fuse (a b t u : Wire) (hat : a≠t) (hbt : b≠t) (hau : a≠u) (hbu : b≠u) (htu : t≠u)
      {xs ys : Circuit} : Reduction xs ys→
      Reduction (.CCX a b t :: .CX t u :: .CCX a b t :: xs) (.CX t u :: .CCX a b u :: ys)

theorem optimize_rel (xs : Circuit) : Reduction xs (optimize xs) := by
  induction xs using optimize.induct with
  | case1 a b t v u c d z rest h ih=>
    rw [optimize,if_pos h]
    rcases h with ⟨rfl,rfl,rfl,rfl,hau,hbu,htu,hat,hbt⟩
    exact Reduction.fuse _ _ _ _ hat hbt hau hbu htu ih
  | case2 a b t v u c d z rest h ih=>
    rw [optimize,if_neg h]
    exact Reduction.keep _ ih
  | case3 g rest h ih=>
    rw [optimize.eq_2 g rest h]
    exact Reduction.keep _ ih
  | case4=>exact Reduction.nil

theorem Reduction.run {xs ys : Circuit} (h : Reduction xs ys) : Quantum.run xs=Quantum.run ys := by
  induction h with
  | nil=>rfl
  | keep g h ih=>
    apply LinearMap.ext
    intro ψ
    simp only [Quantum.run_cons,ih]
  | fuse a b t u hat hbt hau hbu htu h ih=>
    have he:=run_identity a b t u hat hbt hau hbu htu
    apply LinearMap.ext
    intro ψ
    have hh:=congrArg (fun m : State→ₗ[ℂ]State=>m ψ) he
    simp only [source,reduced,Quantum.run_cons,Quantum.run_nil] at hh
    simpa only [Quantum.run_cons,ih] using congrArg (Quantum.run _) hh

end ShorECDLP.Entrant.Transport

namespace ShorECDLP.Entrant.ControlTransport
open Quantum
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def source (a b t : Wire) : Circuit := [.CCX a b t,.CX a b,.CCX a b t]
def reduced (a b t : Wire) : Circuit := [.CX a b,.CX a t]

theorem classical_identity (a b t : Wire) (hab : a≠b) (hat : a≠t) (hbt : b≠t)
    (s : BasisState) : Classical.run (source a b t) s=Classical.run (reduced a b t) s := by
  funext w
  simp only [source,reduced,Classical.run,List.foldl_cons,List.foldl_nil,Classical.applyGate]
  by_cases hwt : w=t
  · subst w
    cases ha:s a <;> cases hb:s b <;> cases ht:s t <;>
      simp_all [upd,Ne.symm hab,Ne.symm hat,Ne.symm hbt]
  · by_cases hwb : w=b
    · subst w
      simp [upd,Ne.symm hab,Ne.symm hat,Ne.symm hbt,hab,hat,hbt]
    · simp [upd,hwt,hwb]

theorem run_identity (a b t : Wire) (hab : a≠b) (hat : a≠t) (hbt : b≠t) :
    Quantum.run (source a b t)=Quantum.run (reduced a b t) := by
  have hk (s : BasisState) : Quantum.run (source a b t) (ket s)=
      Quantum.run (reduced a b t) (ket s) := by
    rw [run_ket_agrees_classical _ _ (by simp [source,Classical.HPFree,Classical.IsClassicalGate]),
      run_ket_agrees_classical _ _ (by simp [reduced,Classical.HPFree,Classical.IsClassicalGate]),
      classical_identity a b t hab hat hbt]
  apply LinearMap.ext
  intro ψ
  induction ψ using Finsupp.induction with
  | zero=>simp only [map_zero]
  | @single_add s c ψ hs hc ih=>
    have he : Finsupp.single s c=c•ket s := by simp [ket]
    simp only [map_add,he,map_smul,ih,hk]

set_option linter.unnecessarySeqFocus false
/-- Compress the adjacent control-fanout conjugation on arbitrary input states. -/
def optimize : Circuit→Circuit
  | .CCX a b t :: .CX v u :: .CCX c d z :: rest=>
    if a=c ∧ b=d ∧ t=z ∧ a=v ∧ b=u ∧ a≠b ∧ a≠t ∧ b≠t then
      .CX a b :: .CX a t :: optimize rest
    else .CCX a b t :: optimize (.CX v u :: .CCX c d z :: rest)
  | g::rest=>g::optimize rest
  | []=>[]

inductive Reduction : Circuit→Circuit→Prop where
  | nil : Reduction List.nil List.nil
  | keep (g : Gate) {xs ys : Circuit} : Reduction xs ys→Reduction (g::xs) (g::ys)
  | fuse (a b t : Wire) (hab : a≠b) (hat : a≠t) (hbt : b≠t)
      {xs ys : Circuit} : Reduction xs ys→
      Reduction (.CCX a b t :: .CX a b :: .CCX a b t :: xs) (.CX a b :: .CX a t :: ys)

theorem optimize_rel (xs : Circuit) : Reduction xs (optimize xs) := by
  induction xs using optimize.induct with
  | case1 a b t v u c d z rest h ih=>
    rw [optimize,if_pos h]
    rcases h with ⟨rfl,rfl,rfl,rfl,rfl,hab,hat,hbt⟩
    exact Reduction.fuse _ _ _ hab hat hbt ih
  | case2 a b t v u c d z rest h ih=>
    rw [optimize,if_neg h]
    exact Reduction.keep _ ih
  | case3 g rest h ih=>
    rw [optimize.eq_2 g rest h]
    exact Reduction.keep _ ih
  | case4=>exact Reduction.nil

theorem Reduction.run {xs ys : Circuit} (h : Reduction xs ys) : Quantum.run xs=Quantum.run ys := by
  induction h with
  | nil=>rfl
  | keep g h ih=>
    apply LinearMap.ext
    intro ψ
    simp only [Quantum.run_cons,ih]
  | fuse a b t hab hat hbt h ih=>
    have he:=run_identity a b t hab hat hbt
    apply LinearMap.ext
    intro ψ
    have hh:=congrArg (fun m : State→ₗ[ℂ]State=>m ψ) he
    simp only [source,reduced,Quantum.run_cons,Quantum.run_nil] at hh
    simpa only [Quantum.run_cons,ih] using congrArg (Quantum.run _) hh

theorem Reduction.tle {xs ys : Circuit} (h : Reduction xs ys) :
    ShorECDLP.tCount ys≤ShorECDLP.tCount xs := by
  induction h <;> simp_all [ShorECDLP.tCount_cons,tCost] <;> omega
end ShorECDLP.Entrant.ControlTransport


namespace ShorECDLP.Entrant.Transport
open Quantum Classical

theorem Reduction.slots {xs ys : Circuit} (h : Reduction xs ys) : ys.length ≤ xs.length := by
  induction h <;> simp_all only [List.length_nil,List.length_cons] <;> omega

theorem Reduction.support {xs ys : Circuit} (h : Reduction xs ys) : circuitWires ys ⊆ circuitWires xs := by
  induction h with
  | nil => exact List.Subset.refl _
  | keep g h ih =>
    intro w hw
    simp only [circuitWires,List.flatMap_cons,List.mem_append] at hw ⊢
    exact hw.imp id (fun hw => ih hw)
  | @fuse a b t u hat hbt hau hbu htu xs ys h ih =>
    intro w hw
    have hh : w ∈ circuitWires ys → w ∈ circuitWires xs := fun h => ih h
    dsimp only [circuitWires] at hh
    simp only [circuitWires,List.flatMap_cons,gateWires,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false] at hw ⊢
    tauto

theorem Reduction.wellFormed {xs ys : Circuit} (h : Reduction xs ys)
    (hw : CircuitWellFormed xs) : CircuitWellFormed ys := by
  induction h with
  | nil => exact hw
  | keep g h ih =>
    intro k hk
    rcases List.mem_cons.mp hk with rfl | hk
    · exact hw k (by simp)
    · exact ih (fun a ha => hw a (List.mem_cons_of_mem _ ha)) k hk
  | @fuse a b t u hat hbt hau hbu htu xs ys h ih =>
    have hx : CircuitWellFormed xs := fun g hg => hw g (by simp [hg])
    have hy := ih hx
    have hab : a ≠ b := (hw (.CCX a b t) (by simp)).1
    simp only [CircuitWellFormed,List.mem_cons,forall_eq_or_imp]
    exact ⟨htu,⟨hab,hau,hbu⟩,hy⟩

theorem Reduction.hpFree {xs ys : Circuit} (h : Reduction xs ys)
    (hf : HPFree xs) : HPFree ys := by
  induction h with
  | nil => exact hf
  | keep g h ih =>
    intro k hk
    rcases List.mem_cons.mp hk with rfl | hk
    · exact hf k (by simp)
    · exact ih (fun a ha => hf a (List.mem_cons_of_mem _ ha)) k hk
  | @fuse a b t u hat hbt hau hbu htu xs ys h ih =>
    have hx : HPFree xs := fun g hg => hf g (by simp [hg])
    have hy := ih hx
    simp only [HPFree,List.mem_cons,forall_eq_or_imp,IsClassicalGate]
    exact ⟨trivial,trivial,hy⟩
end ShorECDLP.Entrant.Transport

namespace ShorECDLP.Entrant.ControlTransport
open Quantum Classical

theorem Reduction.slots {xs ys : Circuit} (h : Reduction xs ys) : ys.length ≤ xs.length := by
  induction h <;> simp_all only [List.length_nil,List.length_cons] <;> omega

theorem Reduction.support {xs ys : Circuit} (h : Reduction xs ys) : circuitWires ys ⊆ circuitWires xs := by
  induction h with
  | nil => exact List.Subset.refl _
  | keep g h ih =>
    intro w hw
    simp only [circuitWires,List.flatMap_cons,List.mem_append] at hw ⊢
    exact hw.imp id (fun hw => ih hw)
  | @fuse a b t hab hat hbt xs ys h ih =>
    intro w hw
    have hh : w ∈ circuitWires ys → w ∈ circuitWires xs := fun h => ih h
    dsimp only [circuitWires] at hh
    simp only [circuitWires,List.flatMap_cons,gateWires,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false] at hw ⊢
    tauto

theorem Reduction.wellFormed {xs ys : Circuit} (h : Reduction xs ys)
    (hw : CircuitWellFormed xs) : CircuitWellFormed ys := by
  induction h with
  | nil => exact hw
  | keep g h ih =>
    intro k hk
    rcases List.mem_cons.mp hk with rfl | hk
    · exact hw k (by simp)
    · exact ih (fun a ha => hw a (List.mem_cons_of_mem _ ha)) k hk
  | @fuse a b t hab hat hbt xs ys h ih =>
    have hx : CircuitWellFormed xs := fun g hg => hw g (by simp [hg])
    have hy := ih hx
    simp only [CircuitWellFormed,List.mem_cons,forall_eq_or_imp]
    exact ⟨hab,hat,hy⟩

theorem Reduction.hpFree {xs ys : Circuit} (h : Reduction xs ys)
    (hf : HPFree xs) : HPFree ys := by
  induction h with
  | nil => exact hf
  | keep g h ih =>
    intro k hk
    rcases List.mem_cons.mp hk with rfl | hk
    · exact hf k (by simp)
    · exact ih (fun a ha => hf a (List.mem_cons_of_mem _ ha)) k hk
  | @fuse a b t hab hat hbt xs ys h ih =>
    have hx : HPFree xs := fun g hg => hf g (by simp [hg])
    have hy := ih hx
    simp only [HPFree,List.mem_cons,forall_eq_or_imp,IsClassicalGate]
    exact ⟨trivial,trivial,hy⟩
end ShorECDLP.Entrant.ControlTransport

namespace ShorECDLP.Entrant.Optimization
open Quantum Challenge Paper2607_13816 Classical Paper2607_13816.ChallengeMigration

def smallOptimized (xs : Circuit) : Circuit :=
  ControlTransport.optimize (Transport.optimize (Cancellation.optimize xs))

theorem smallOptimized_bound (xs : Circuit) (d : Nat) (hw : CircuitWellFormed xs)
    (hf : HPFree xs) (ht : tCount (smallOptimized xs)+d=tCount xs) :
    LiteralBound xs (smallOptimized xs) d := by
  have hc := Cancellation.optimize_sublist xs
  have htr := Transport.optimize_rel (Cancellation.optimize xs)
  have hct := ControlTransport.optimize_rel (Transport.optimize (Cancellation.optimize xs))
  have hwc : CircuitWellFormed (Cancellation.optimize xs) := fun g hg => hw g (hc.subset hg)
  have hfc : HPFree (Cancellation.optimize xs) := fun g hg => hf g (hc.subset hg)
  have hff : HPFree (smallOptimized xs) := hct.hpFree (htr.hpFree hfc)
  refine ⟨hct.wellFormed (htr.wellFormed hwc),hct.slots.trans (htr.slots.trans hc.length_le),ht,?_,?_⟩
  · intro w hw
    obtain ⟨g,hg,hwg⟩ := List.mem_flatMap.mp (htr.support (hct.support hw))
    exact List.mem_flatMap.mpr ⟨g,hc.subset hg,hwg⟩
  · rw [← Initializer.classical_toffoli_cost _ hf,← Initializer.classical_toffoli_cost _ hff]
    exact Nat.le_of_eq ht.symm

noncomputable def smallPatch (n start d : Nat) (xs : Circuit) (hw : CircuitWellFormed xs)
    (hf : HPFree xs) (ht : tCount (smallOptimized xs)+d=tCount xs) :
    Patch (literalProgram xs : Straight n start start) d :=
  Patch.literalChecked _ _ (smallOptimized_bound xs d hw hf ht)
    (((Cancellation.optimize_run xs hw).symm.trans
      (Transport.optimize_rel (Cancellation.optimize xs)).run).trans
      (ControlTransport.optimize_rel (Transport.optimize (Cancellation.optimize xs))).run)
end ShorECDLP.Entrant.Optimization

namespace ShorECDLP.Entrant.Optimization
open Quantum Challenge Paper2607_13816.ChallengeMigration
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


end ShorECDLP.Entrant.Optimization
/- One-commuting-gate target sandwiches adapted from public submission
69c8b9e8-a43f-4dfc-8223-84551067b989, GPT 6.1 Sol / Codex.
The support, slot, well-formedness, and literal-bound adapters below are new. -/
namespace ShorECDLP.Entrant.AcrossLeft
open Quantum
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def source (a b t u : Wire) (h : Gate) : Circuit := [.CCX a b t,h,.CX t u,.CCX a b t]
def reduced (a b t u : Wire) (h : Gate) : Circuit := [h,.CX t u,.CCX a b u]

theorem run_identity (a b t u : Wire) (h : Gate)
    (hat : a≠t) (hbt : b≠t) (hau : a≠u) (hbu : b≠u) (htu : t≠u)
    (hc : Cancellation.commutes (.CCX a b t) h = true) :
    Quantum.run (source a b t u h)=Quantum.run (reduced a b t u h) := by
  have he := Transport.run_identity a b t u hat hbt hau hbu htu
  have hc' (ϕ : State) : applyGate (.CCX a b t) (applyGate h ϕ) = applyGate h (applyGate (.CCX a b t) ϕ) := by
    simpa only [Quantum.run_cons,Quantum.run_nil] using
      Initializer.gate_circuit_commute (.CCX a b t) (h :: List.nil) (by
        intro k hk
        have heq : k=h := by simpa only [List.mem_singleton] using hk
        rw [heq]
        exact hc) ϕ
  apply LinearMap.ext
  intro ψ
  simp only [source,reduced,Quantum.run_cons,Quantum.run_nil]
  have hh := congrArg (fun m : State →ₗ[ℂ]State => m (applyGate h ψ)) he
  simp only [Transport.source,Transport.reduced,Quantum.run_cons,Quantum.run_nil] at hh
  rw [hc'] at hh
  exact hh

def optimize : Circuit → Circuit
  | .CCX a b t :: h :: .CX v u :: .CCX c d z :: rest =>
    if a=c ∧ b=d ∧ t=v ∧ t=z ∧ a≠u ∧ b≠u ∧ t≠u ∧ a≠t ∧ b≠t ∧
        Cancellation.commutes (.CCX a b t) h = true then
      h :: .CX t u :: .CCX a b u :: optimize rest
    else .CCX a b t :: optimize (h :: .CX v u :: .CCX c d z :: rest)
  | g::rest => g::optimize rest
  | [] => []

inductive Reduction : Circuit → Circuit → Prop where
  | nil : Reduction List.nil List.nil
  | keep (g : Gate) {xs ys : Circuit} : Reduction xs ys → Reduction (g::xs) (g::ys)
  | fuse (a b t u : Wire) (h : Gate)
      (hat : a≠t) (hbt : b≠t) (hau : a≠u) (hbu : b≠u) (htu : t≠u)
      (hc : Cancellation.commutes (.CCX a b t) h = true)
      {xs ys : Circuit} : Reduction xs ys →
      Reduction (.CCX a b t :: h :: .CX t u :: .CCX a b t :: xs) (h :: .CX t u :: .CCX a b u :: ys)

theorem optimize_rel (xs : Circuit) : Reduction xs (optimize xs) := by
  induction xs using optimize.induct with
  | case1 a b t h v u c d z rest hc ih =>
    rw [optimize,if_pos hc]
    rcases hc with ⟨rfl,rfl,rfl,rfl,hau,hbu,htu,hat,hbt,hcomm⟩
    exact Reduction.fuse _ _ _ _ _ hat hbt hau hbu htu hcomm ih
  | case2 a b t h v u c d z rest hc ih =>
    rw [optimize,if_neg hc]
    exact Reduction.keep _ ih
  | case3 g rest hc ih =>
    rw [optimize.eq_2 g rest hc]
    exact Reduction.keep _ ih
  | case4 => exact Reduction.nil

theorem Reduction.run {xs ys : Circuit} (h : Reduction xs ys) : Quantum.run xs=Quantum.run ys := by
  induction h with
  | nil => rfl
  | keep g h ih =>
    apply LinearMap.ext
    intro ψ
    simp only [Quantum.run_cons,ih]
  | fuse a b t u g hat hbt hau hbu htu hc h ih =>
    have he := run_identity a b t u g hat hbt hau hbu htu hc
    apply LinearMap.ext
    intro ψ
    have hh := congrArg (fun m : State→ₗ[ℂ]State => m ψ) he
    simp only [source,reduced,Quantum.run_cons,Quantum.run_nil] at hh
    simpa only [Quantum.run_cons,ih] using congrArg (Quantum.run _) hh

end ShorECDLP.Entrant.AcrossLeft

namespace ShorECDLP.Entrant.AcrossRight
open Quantum
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def source (a b t u : Wire) (h : Gate) : Circuit := [.CCX a b t,.CX t u,h,.CCX a b t]
def reduced (a b t u : Wire) (h : Gate) : Circuit := [.CX t u,.CCX a b u,h]

theorem run_identity (a b t u : Wire) (h : Gate)
    (hat : a≠t) (hbt : b≠t) (hau : a≠u) (hbu : b≠u) (htu : t≠u)
    (hc : Cancellation.commutes (.CCX a b t) h = true) :
    Quantum.run (source a b t u h)=Quantum.run (reduced a b t u h) := by
  have he := Transport.run_identity a b t u hat hbt hau hbu htu
  have hc' (ϕ : State) : applyGate (.CCX a b t) (applyGate h ϕ) = applyGate h (applyGate (.CCX a b t) ϕ) := by
    simpa only [Quantum.run_cons,Quantum.run_nil] using
      Initializer.gate_circuit_commute (.CCX a b t) (h :: List.nil) (by
        intro k hk
        have heq : k=h := by simpa only [List.mem_singleton] using hk
        rw [heq]
        exact hc) ϕ
  apply LinearMap.ext
  intro ψ
  simp only [source,reduced,Quantum.run_cons,Quantum.run_nil]
  have hh := congrArg (fun v : State => applyGate h v)
      (congrArg (fun m : State →ₗ[ℂ]State => m ψ) he)
  simp only [Transport.source,Transport.reduced,Quantum.run_cons,Quantum.run_nil] at hh
  rw [←hc'] at hh
  exact hh

def optimize : Circuit → Circuit
  | .CCX a b t :: .CX v u :: h :: .CCX c d z :: rest =>
    if a=c ∧ b=d ∧ t=v ∧ t=z ∧ a≠u ∧ b≠u ∧ t≠u ∧ a≠t ∧ b≠t ∧
        Cancellation.commutes (.CCX a b t) h = true then
      .CX t u :: .CCX a b u :: h :: optimize rest
    else .CCX a b t :: optimize (.CX v u :: h :: .CCX c d z :: rest)
  | g::rest => g::optimize rest
  | [] => []

inductive Reduction : Circuit → Circuit → Prop where
  | nil : Reduction List.nil List.nil
  | keep (g : Gate) {xs ys : Circuit} : Reduction xs ys → Reduction (g::xs) (g::ys)
  | fuse (a b t u : Wire) (h : Gate)
      (hat : a≠t) (hbt : b≠t) (hau : a≠u) (hbu : b≠u) (htu : t≠u)
      (hc : Cancellation.commutes (.CCX a b t) h = true)
      {xs ys : Circuit} : Reduction xs ys →
      Reduction (.CCX a b t :: .CX t u :: h :: .CCX a b t :: xs) (.CX t u :: .CCX a b u :: h :: ys)

theorem optimize_rel (xs : Circuit) : Reduction xs (optimize xs) := by
  induction xs using optimize.induct with
  | case1 a b t v u h c d z rest hc ih =>
    rw [optimize,if_pos hc]
    rcases hc with ⟨rfl,rfl,rfl,rfl,hau,hbu,htu,hat,hbt,hcomm⟩
    exact Reduction.fuse _ _ _ _ _ hat hbt hau hbu htu hcomm ih
  | case2 a b t v u h c d z rest hc ih =>
    rw [optimize,if_neg hc]
    exact Reduction.keep _ ih
  | case3 g rest hc ih =>
    rw [optimize.eq_2 g rest hc]
    exact Reduction.keep _ ih
  | case4 => exact Reduction.nil

theorem Reduction.run {xs ys : Circuit} (h : Reduction xs ys) : Quantum.run xs=Quantum.run ys := by
  induction h with
  | nil => rfl
  | keep g h ih =>
    apply LinearMap.ext
    intro ψ
    simp only [Quantum.run_cons,ih]
  | fuse a b t u g hat hbt hau hbu htu hc h ih =>
    have he := run_identity a b t u g hat hbt hau hbu htu hc
    apply LinearMap.ext
    intro ψ
    have hh := congrArg (fun m : State→ₗ[ℂ]State => m ψ) he
    simp only [source,reduced,Quantum.run_cons,Quantum.run_nil] at hh
    simpa only [Quantum.run_cons,ih] using congrArg (Quantum.run _) hh

end ShorECDLP.Entrant.AcrossRight

namespace ShorECDLP.Entrant.AcrossLeft
open Quantum

theorem Reduction.tle {xs ys : Circuit} (h : Reduction xs ys) :
    ShorECDLP.tCount ys ≤ ShorECDLP.tCount xs := by
  induction h <;> simp_all [ShorECDLP.tCount_cons,tCost]
  omega
end ShorECDLP.Entrant.AcrossLeft
namespace ShorECDLP.Entrant.AcrossRight
open Quantum

theorem Reduction.tle {xs ys : Circuit} (h : Reduction xs ys) :
    ShorECDLP.tCount ys ≤ ShorECDLP.tCount xs := by
  induction h <;> simp_all [ShorECDLP.tCount_cons,tCost]
  omega
end ShorECDLP.Entrant.AcrossRight

namespace ShorECDLP.Entrant.AcrossLeft
open Quantum Classical

theorem Reduction.slots {xs ys : Circuit} (h : Reduction xs ys) : ys.length ≤ xs.length := by
  induction h <;> simp_all only [List.length_nil,List.length_cons] <;> omega

theorem Reduction.support {xs ys : Circuit} (h : Reduction xs ys) : circuitWires ys ⊆ circuitWires xs := by
  induction h with
  | nil => exact List.Subset.refl _
  | keep g h ih =>
    intro w hw
    simp only [circuitWires,List.flatMap_cons,List.mem_append] at hw ⊢
    exact hw.imp id (fun hw => ih hw)
  | @fuse a b t u g hat hbt hau hbu htu hc xs ys h ih =>
    intro w hw
    have hh : w ∈ circuitWires ys → w ∈ circuitWires xs := fun h => ih h
    dsimp only [circuitWires] at hh
    simp only [circuitWires,List.flatMap_cons,gateWires,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false] at hw ⊢
    tauto

theorem Reduction.wellFormed {xs ys : Circuit} (h : Reduction xs ys)
    (hw : CircuitWellFormed xs) : CircuitWellFormed ys := by
  induction h with
  | nil => exact hw
  | keep g h ih =>
    intro k hk
    rcases List.mem_cons.mp hk with rfl | hk
    · exact hw k (by simp)
    · exact ih (fun a ha => hw a (List.mem_cons_of_mem _ ha)) k hk
  | @fuse a b t u g hat hbt hau hbu htu hc xs ys h ih =>
    have hx : CircuitWellFormed xs := fun k hk => hw k (by simp [hk])
    have hy := ih hx
    have hab : a ≠ b := (hw (.CCX a b t) (by simp)).1
    simp only [CircuitWellFormed,List.mem_cons,forall_eq_or_imp]
    exact ⟨hw g (by simp),htu,⟨hab,hau,hbu⟩,hy⟩

theorem Reduction.hpFree {xs ys : Circuit} (h : Reduction xs ys)
    (hf : HPFree xs) : HPFree ys := by
  induction h with
  | nil => exact hf
  | keep g h ih =>
    intro k hk
    rcases List.mem_cons.mp hk with rfl | hk
    · exact hf k (by simp)
    · exact ih (fun a ha => hf a (List.mem_cons_of_mem _ ha)) k hk
  | @fuse a b t u g hat hbt hau hbu htu hc xs ys h ih =>
    have hx : HPFree xs := fun k hk => hf k (by simp [hk])
    have hy := ih hx
    simp only [HPFree,List.mem_cons,forall_eq_or_imp,IsClassicalGate]
    exact ⟨hf g (by simp),trivial,trivial,hy⟩
end ShorECDLP.Entrant.AcrossLeft

namespace ShorECDLP.Entrant.AcrossRight
open Quantum Classical

theorem Reduction.slots {xs ys : Circuit} (h : Reduction xs ys) : ys.length ≤ xs.length := by
  induction h <;> simp_all only [List.length_nil,List.length_cons] <;> omega

theorem Reduction.support {xs ys : Circuit} (h : Reduction xs ys) : circuitWires ys ⊆ circuitWires xs := by
  induction h with
  | nil => exact List.Subset.refl _
  | keep g h ih =>
    intro w hw
    simp only [circuitWires,List.flatMap_cons,List.mem_append] at hw ⊢
    exact hw.imp id (fun hw => ih hw)
  | @fuse a b t u g hat hbt hau hbu htu hc xs ys h ih =>
    intro w hw
    have hh : w ∈ circuitWires ys → w ∈ circuitWires xs := fun h => ih h
    dsimp only [circuitWires] at hh
    simp only [circuitWires,List.flatMap_cons,gateWires,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false] at hw ⊢
    tauto

theorem Reduction.wellFormed {xs ys : Circuit} (h : Reduction xs ys)
    (hw : CircuitWellFormed xs) : CircuitWellFormed ys := by
  induction h with
  | nil => exact hw
  | keep g h ih =>
    intro k hk
    rcases List.mem_cons.mp hk with rfl | hk
    · exact hw k (by simp)
    · exact ih (fun a ha => hw a (List.mem_cons_of_mem _ ha)) k hk
  | @fuse a b t u g hat hbt hau hbu htu hc xs ys h ih =>
    have hx : CircuitWellFormed xs := fun k hk => hw k (by simp [hk])
    have hy := ih hx
    have hab : a ≠ b := (hw (.CCX a b t) (by simp)).1
    simp only [CircuitWellFormed,List.mem_cons,forall_eq_or_imp]
    exact ⟨htu,⟨hab,hau,hbu⟩,hw g (by simp),hy⟩

theorem Reduction.hpFree {xs ys : Circuit} (h : Reduction xs ys)
    (hf : HPFree xs) : HPFree ys := by
  induction h with
  | nil => exact hf
  | keep g h ih =>
    intro k hk
    rcases List.mem_cons.mp hk with rfl | hk
    · exact hf k (by simp)
    · exact ih (fun a ha => hf a (List.mem_cons_of_mem _ ha)) k hk
  | @fuse a b t u g hat hbt hau hbu htu hc xs ys h ih =>
    have hx : HPFree xs := fun k hk => hf k (by simp [hk])
    have hy := ih hx
    simp only [HPFree,List.mem_cons,forall_eq_or_imp,IsClassicalGate]
    exact ⟨trivial,trivial,hf g (by simp),hy⟩
end ShorECDLP.Entrant.AcrossRight

namespace ShorECDLP.Entrant.Optimization
open Quantum Classical Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration

def acrossOptimized (xs : Circuit) : Circuit :=
  AcrossRight.optimize (AcrossLeft.optimize (smallOptimized xs))

theorem acrossOptimized_bound (xs : Circuit) (d : Nat) (hw : CircuitWellFormed xs)
    (hf : HPFree xs) (ht : tCount (acrossOptimized xs)+d=tCount xs) :
    LiteralBound xs (acrossOptimized xs) d := by
  have hc := Cancellation.optimize_sublist xs
  have htr := Transport.optimize_rel (Cancellation.optimize xs)
  have hct := ControlTransport.optimize_rel (Transport.optimize (Cancellation.optimize xs))
  have hl := AcrossLeft.optimize_rel (smallOptimized xs)
  have hr := AcrossRight.optimize_rel (AcrossLeft.optimize (smallOptimized xs))
  have hwc : CircuitWellFormed (Cancellation.optimize xs) := fun g hg => hw g (hc.subset hg)
  have hfc : HPFree (Cancellation.optimize xs) := fun g hg => hf g (hc.subset hg)
  have hff : HPFree (acrossOptimized xs) := hr.hpFree (hl.hpFree (hct.hpFree (htr.hpFree hfc)))
  refine ⟨hr.wellFormed (hl.wellFormed (hct.wellFormed (htr.wellFormed hwc))),
    hr.slots.trans (hl.slots.trans (hct.slots.trans (htr.slots.trans hc.length_le))),ht,?_,?_⟩
  · intro w hw
    obtain ⟨g,hg,hwg⟩ := List.mem_flatMap.mp (htr.support (hct.support (hl.support (hr.support hw))))
    exact List.mem_flatMap.mpr ⟨g,hc.subset hg,hwg⟩
  · rw [← Initializer.classical_toffoli_cost _ hf,← Initializer.classical_toffoli_cost _ hff]
    exact Nat.le_of_eq ht.symm

noncomputable def acrossSmallPatch (n start d : Nat) (xs : Circuit) (hw : CircuitWellFormed xs)
    (hf : HPFree xs) (ht : tCount (acrossOptimized xs)+d=tCount xs) :
    Patch (literalProgram xs : Straight n start start) d :=
  Patch.literalChecked _ _ (acrossOptimized_bound xs d hw hf ht)
    (((((Cancellation.optimize_run xs hw).symm.trans
      (Transport.optimize_rel (Cancellation.optimize xs)).run).trans
      (ControlTransport.optimize_rel (Transport.optimize (Cancellation.optimize xs))).run).trans
      (AcrossLeft.optimize_rel (smallOptimized xs)).run).trans
      (AcrossRight.optimize_rel (AcrossLeft.optimize (smallOptimized xs))).run)
end ShorECDLP.Entrant.Optimization

namespace ShorECDLP.Entrant.AdjacentArithmetic
open Quantum Classical Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration Optimization
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] literalProgram
private instance classicalDecidable (g : Gate) : Decidable (IsClassicalGate g) := by
  cases g <;> unfold IsClassicalGate <;> infer_instance
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

def aPatch (n start : Nat) : Patch (literalProgram (aSource) : Straight n start start) 140 := by
  simpa only [aSource, blockAForward, terminalPaddingForward, terminalPaddingPrefix, preShift_expand, shiftedLiteral, shiftFlags, List.append_assoc, List.append_nil, circuit_adjoint_append] using ((Patch.refl (literalProgram (computeControl (indexedStepProductionRegisters.phase1 :: indexedStepProductionRegisters.lengthRPrime) (2^(indexedStepProductionRegisters.lengthRPrime.length+1)-2) indexedStepProductionRegisters.terminal indexedStepProductionRegisters.blockScratch) : Straight n start start)).joinLiteral ((Patch.refl (literalProgram (controlledRotateLeftOne indexedStepProductionRegisters.terminalPadding.terminal indexedStepProductionRegisters.terminalPadding.work2) : Straight n start start)).joinLiteral ((smallPatch n start 7 (controlledIncrement indexedStepProductionRegisters.terminalPadding.terminal indexedStepProductionRegisters.terminalPadding.lengthS indexedStepProductionRegisters.terminalPadding.carries) (by unfold CircuitWellFormed; decide +kernel) (by unfold HPFree; decide +kernel) (by decide +kernel)).joinLiteral ((smallPatch n start 98 (terminalPaddingEpochUpdate indexedStepProductionRegisters.terminalPadding) (by unfold CircuitWellFormed; decide +kernel) (by unfold HPFree; decide +kernel) (by decide +kernel)).joinLiteral ((Patch.refl (literalProgram (([.CX indexedStepProductionRegisters.terminal indexedStepProductionRegisters.phase1] : Circuit)) : Straight n start start)).joinLiteral ((Patch.refl (literalProgram (([.X indexedStepProductionRegisters.preShift.phase1, .CX indexedStepProductionRegisters.preShift.phase1 indexedStepProductionRegisters.preShift.phase1IsZero, .X indexedStepProductionRegisters.preShift.phase1] : Circuit)) : Straight n start start)).joinLiteral ((Patch.refl (literalProgram (controlledRotateLeftOne indexedStepProductionRegisters.preShift.phase1IsZero indexedStepProductionRegisters.preShift.work) : Straight n start start)).joinLiteral ((smallPatch n start 7 (controlledIncrement indexedStepProductionRegisters.preShift.phase1IsZero indexedStepProductionRegisters.preShift.lengthS indexedStepProductionRegisters.preShift.carries) (by unfold CircuitWellFormed; decide +kernel) (by unfold HPFree; decide +kernel) (by decide +kernel)).joinLiteral ((Patch.refl (literalProgram (([.CCX indexedStepProductionRegisters.preShift.phase1IsZero indexedStepProductionRegisters.preShift.phase2 indexedStepProductionRegisters.preShift.both] : Circuit)) : Straight n start start)).joinLiteral ((Patch.refl (literalProgram (controlledRotateRightTwo indexedStepProductionRegisters.preShift.both indexedStepProductionRegisters.preShift.work) : Straight n start start)).joinLiteral ((smallPatch n start 28 ((controlledDecrement indexedStepProductionRegisters.preShift.both indexedStepProductionRegisters.preShift.lengthS indexedStepProductionRegisters.preShift.carries ++ controlledDecrement indexedStepProductionRegisters.preShift.both indexedStepProductionRegisters.preShift.lengthS indexedStepProductionRegisters.preShift.carries)) (by unfold CircuitWellFormed; decide +kernel) (by unfold HPFree; decide +kernel) (by decide +kernel)).joinLiteral ((Patch.refl (literalProgram (([.CCX indexedStepProductionRegisters.preShift.phase1IsZero indexedStepProductionRegisters.preShift.phase2 indexedStepProductionRegisters.preShift.both] : Circuit)) : Straight n start start)).joinLiteral ((Patch.refl (literalProgram (([.X indexedStepProductionRegisters.preShift.phase1, .CX indexedStepProductionRegisters.preShift.phase1 indexedStepProductionRegisters.preShift.phase1IsZero, .X indexedStepProductionRegisters.preShift.phase1] : Circuit)) : Straight n start start)).joinLiteral ((Patch.refl (literalProgram (([.CX indexedStepProductionRegisters.terminal indexedStepProductionRegisters.phase1] : Circuit)) : Straight n start start)).joinLiteral ((Patch.refl (literalProgram (terminalEpochSpill indexedStepProductionRegisters.terminal indexedStepProductionRegisters.shiftEpoch indexedStepProductionRegisters.quotientLow) : Straight n start start)).joinLiteral ((Patch.refl (literalProgram (computeControl (indexedStepProductionRegisters.phase1 :: indexedStepProductionRegisters.lengthRPrime) (2^(indexedStepProductionRegisters.lengthRPrime.length+1)-2) indexedStepProductionRegisters.terminal indexedStepProductionRegisters.blockScratch) : Straight n start start)).joinLiteral (Patch.refl (literalProgram List.nil : Straight n start start))))))))))))))))))

def fSource : Circuit := blockFForward indexedStepProductionRegisters

def fPatch (n start : Nat) : Patch (literalProgram (fSource) : Straight n start start) 35 := by
  simpa only [fSource, blockFForward, postShift_expand, shiftedLiteral, shiftFlags, List.append_assoc, List.append_nil, circuit_adjoint_append] using ((Patch.refl (literalProgram (controlledRotateLeftOne indexedStepProductionRegisters.postShift.phase1 indexedStepProductionRegisters.postShift.work) : Straight n start start)).joinLiteral ((smallPatch n start 7 (controlledIncrement indexedStepProductionRegisters.postShift.phase1 indexedStepProductionRegisters.postShift.lengthS indexedStepProductionRegisters.postShift.carries) (by unfold CircuitWellFormed; decide +kernel) (by unfold HPFree; decide +kernel) (by decide +kernel)).joinLiteral ((Patch.refl (literalProgram (([.CCX indexedStepProductionRegisters.postShift.phase1 indexedStepProductionRegisters.postShift.phase2 indexedStepProductionRegisters.postShift.both] : Circuit)) : Straight n start start)).joinLiteral ((Patch.refl (literalProgram (controlledRotateRightTwo indexedStepProductionRegisters.postShift.both indexedStepProductionRegisters.postShift.work) : Straight n start start)).joinLiteral ((smallPatch n start 28 ((controlledDecrement indexedStepProductionRegisters.postShift.both indexedStepProductionRegisters.postShift.lengthS indexedStepProductionRegisters.postShift.carries ++ controlledDecrement indexedStepProductionRegisters.postShift.both indexedStepProductionRegisters.postShift.lengthS indexedStepProductionRegisters.postShift.carries)) (by unfold CircuitWellFormed; decide +kernel) (by unfold HPFree; decide +kernel) (by decide +kernel)).joinLiteral ((Patch.refl (literalProgram (([.CCX indexedStepProductionRegisters.postShift.phase1 indexedStepProductionRegisters.postShift.phase2 indexedStepProductionRegisters.postShift.both] : Circuit)) : Straight n start start)).joinLiteral (Patch.refl (literalProgram List.nil : Straight n start start))))))))

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def aInversePatch (n start : Nat) : Patch (literalProgram (blockAInverse indexedStepProductionRegisters) : Straight n start start) 140 := by
  simpa only [blockAInverse, terminalPaddingInverse, preShift_expand, shiftedLiteral, shiftFlags, List.append_assoc, List.append_nil, circuit_adjoint_append] using ((Patch.refl (literalProgram (computeControl (indexedStepProductionRegisters.phase1 :: indexedStepProductionRegisters.lengthRPrime) (2^(indexedStepProductionRegisters.lengthRPrime.length+1)-2) indexedStepProductionRegisters.terminal indexedStepProductionRegisters.blockScratch) : Straight n start start)).joinLiteral ((Patch.refl (literalProgram (terminalEpochRestore indexedStepProductionRegisters.terminal indexedStepProductionRegisters.shiftEpoch indexedStepProductionRegisters.quotientLow) : Straight n start start)).joinLiteral ((Patch.refl (literalProgram (([.CX indexedStepProductionRegisters.terminal indexedStepProductionRegisters.phase1] : Circuit)) : Straight n start start)).joinLiteral ((Patch.refl (literalProgram (Circuit.adjoint (([.X indexedStepProductionRegisters.preShift.phase1, .CX indexedStepProductionRegisters.preShift.phase1 indexedStepProductionRegisters.preShift.phase1IsZero, .X indexedStepProductionRegisters.preShift.phase1] : Circuit))) : Straight n start start)).joinLiteral ((Patch.refl (literalProgram (Circuit.adjoint (([.CCX indexedStepProductionRegisters.preShift.phase1IsZero indexedStepProductionRegisters.preShift.phase2 indexedStepProductionRegisters.preShift.both] : Circuit))) : Straight n start start)).joinLiteral ((smallPatch n start 28 (Circuit.adjoint ((controlledDecrement indexedStepProductionRegisters.preShift.both indexedStepProductionRegisters.preShift.lengthS indexedStepProductionRegisters.preShift.carries ++ controlledDecrement indexedStepProductionRegisters.preShift.both indexedStepProductionRegisters.preShift.lengthS indexedStepProductionRegisters.preShift.carries))) (by unfold CircuitWellFormed; decide +kernel) (by unfold HPFree; decide +kernel) (by decide +kernel)).joinLiteral ((Patch.refl (literalProgram (Circuit.adjoint (controlledRotateRightTwo indexedStepProductionRegisters.preShift.both indexedStepProductionRegisters.preShift.work)) : Straight n start start)).joinLiteral ((Patch.refl (literalProgram (Circuit.adjoint (([.CCX indexedStepProductionRegisters.preShift.phase1IsZero indexedStepProductionRegisters.preShift.phase2 indexedStepProductionRegisters.preShift.both] : Circuit))) : Straight n start start)).joinLiteral ((smallPatch n start 7 (Circuit.adjoint (controlledIncrement indexedStepProductionRegisters.preShift.phase1IsZero indexedStepProductionRegisters.preShift.lengthS indexedStepProductionRegisters.preShift.carries)) (by unfold CircuitWellFormed; decide +kernel) (by unfold HPFree; decide +kernel) (by decide +kernel)).joinLiteral ((Patch.refl (literalProgram (Circuit.adjoint (controlledRotateLeftOne indexedStepProductionRegisters.preShift.phase1IsZero indexedStepProductionRegisters.preShift.work)) : Straight n start start)).joinLiteral ((Patch.refl (literalProgram (Circuit.adjoint (([.X indexedStepProductionRegisters.preShift.phase1, .CX indexedStepProductionRegisters.preShift.phase1 indexedStepProductionRegisters.preShift.phase1IsZero, .X indexedStepProductionRegisters.preShift.phase1] : Circuit))) : Straight n start start)).joinLiteral ((Patch.refl (literalProgram (([.CX indexedStepProductionRegisters.terminal indexedStepProductionRegisters.phase1] : Circuit)) : Straight n start start)).joinLiteral ((smallPatch n start 98 (terminalPaddingEpochUpdate indexedStepProductionRegisters.terminalPadding) (by unfold CircuitWellFormed; decide +kernel) (by unfold HPFree; decide +kernel) (by decide +kernel)).joinLiteral ((smallPatch n start 7 (controlledDecrement indexedStepProductionRegisters.terminalPadding.terminal indexedStepProductionRegisters.terminalPadding.lengthS indexedStepProductionRegisters.terminalPadding.carries) (by unfold CircuitWellFormed; decide +kernel) (by unfold HPFree; decide +kernel) (by decide +kernel)).joinLiteral ((Patch.refl (literalProgram (controlledRotateRightOne indexedStepProductionRegisters.terminalPadding.terminal indexedStepProductionRegisters.terminalPadding.work2) : Straight n start start)).joinLiteral ((Patch.refl (literalProgram (computeControl (indexedStepProductionRegisters.phase1 :: indexedStepProductionRegisters.lengthRPrime) (2^(indexedStepProductionRegisters.lengthRPrime.length+1)-2) indexedStepProductionRegisters.terminal indexedStepProductionRegisters.blockScratch) : Straight n start start)).joinLiteral (Patch.refl (literalProgram List.nil : Straight n start start))))))))))))))))))

def fInversePatch (n start : Nat) : Patch (literalProgram ((blockFForward indexedStepProductionRegisters).adjoint) : Straight n start start) 35 := by
  simpa only [blockFForward, postShift_expand, shiftedLiteral, shiftFlags, List.append_assoc, List.append_nil, circuit_adjoint_append] using ((Patch.refl (literalProgram (Circuit.adjoint (([.CCX indexedStepProductionRegisters.postShift.phase1 indexedStepProductionRegisters.postShift.phase2 indexedStepProductionRegisters.postShift.both] : Circuit))) : Straight n start start)).joinLiteral ((smallPatch n start 28 (Circuit.adjoint ((controlledDecrement indexedStepProductionRegisters.postShift.both indexedStepProductionRegisters.postShift.lengthS indexedStepProductionRegisters.postShift.carries ++ controlledDecrement indexedStepProductionRegisters.postShift.both indexedStepProductionRegisters.postShift.lengthS indexedStepProductionRegisters.postShift.carries))) (by unfold CircuitWellFormed; decide +kernel) (by unfold HPFree; decide +kernel) (by decide +kernel)).joinLiteral ((Patch.refl (literalProgram (Circuit.adjoint (controlledRotateRightTwo indexedStepProductionRegisters.postShift.both indexedStepProductionRegisters.postShift.work)) : Straight n start start)).joinLiteral ((Patch.refl (literalProgram (Circuit.adjoint (([.CCX indexedStepProductionRegisters.postShift.phase1 indexedStepProductionRegisters.postShift.phase2 indexedStepProductionRegisters.postShift.both] : Circuit))) : Straight n start start)).joinLiteral ((smallPatch n start 7 (Circuit.adjoint (controlledIncrement indexedStepProductionRegisters.postShift.phase1 indexedStepProductionRegisters.postShift.lengthS indexedStepProductionRegisters.postShift.carries)) (by unfold CircuitWellFormed; decide +kernel) (by unfold HPFree; decide +kernel) (by decide +kernel)).joinLiteral ((Patch.refl (literalProgram (Circuit.adjoint (controlledRotateLeftOne indexedStepProductionRegisters.postShift.phase1 indexedStepProductionRegisters.postShift.work)) : Straight n start start)).joinLiteral (Patch.refl (literalProgram List.nil : Straight n start start))))))))

end
end ShorECDLP.Entrant.AdjacentArithmetic

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
def aPatch (n start : Nat) : Patch (literalProgram aSource : Straight n start start) 140 :=
  AdjacentArithmetic.aPatch n start

def fPatch (n start : Nat) : Patch (literalProgram (blockFForward indexedStepProductionRegisters) : Straight n start start) 35 :=
  AdjacentArithmetic.fPatch n start

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
private instance endpointClassicalDecidable (g : Gate) : Decidable (Classical.IsClassicalGate g) := by
  cases g <;> unfold Classical.IsClassicalGate <;> infer_instance

private theorem b12_saving : ShorECDLP.tCount (smallOptimized (b1Source ++ b2Source)) + 441 =
    ShorECDLP.tCount (b1Source ++ b2Source) := by decide +kernel

def b12Patch (n start : Nat) : Patch (literalProgram (b1Source ++ b2Source) : Straight n start start) 441 :=
  smallPatch n start 441 _ b12_wellFormed
    (by unfold Classical.HPFree; decide +kernel) b12_saving

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
    Classical.HPFree (endpointPrefix lT lQ lS sc c) ∧
    ShorECDLP.tCount (acrossOptimized (endpointPrefix lT lQ lS sc c)) + 70 =
      ShorECDLP.tCount (endpointPrefix lT lQ lS sc c)) ∧
  (CircuitWellFormed (endpointSuffix lT lQ lS sc c) ∧
    Classical.HPFree (endpointSuffix lT lQ lS sc c) ∧
    ShorECDLP.tCount (acrossOptimized (endpointSuffix lT lQ lS sc c)) + 70 =
      ShorECDLP.tCount (endpointSuffix lT lQ lS sc c)) ∧
  (CircuitWellFormed (cuccaroSub (endpointScratch lQ sc) lQ c) ∧
    ShorECDLP.tCount (acrossOptimized (cuccaroSub (endpointScratch lQ sc) lQ c)) + 21 =
      ShorECDLP.tCount (cuccaroSub (endpointScratch lQ sc) lQ c)) ∧
  (CircuitWellFormed (cuccaroSub (endpointScratch lS sc) lS c) ∧
    ShorECDLP.tCount (acrossOptimized (cuccaroSub (endpointScratch lS sc) lS c)) + 21 =
      ShorECDLP.tCount (cuccaroSub (endpointScratch lS sc) lS c)) ∧
  (CircuitWellFormed (cuccaroAdd (endpointScratch lS sc) lS c) ∧
    ShorECDLP.tCount (acrossOptimized (cuccaroAdd (endpointScratch lS sc) lS c)) + 21 =
      ShorECDLP.tCount (cuccaroAdd (endpointScratch lS sc) lS c)) ∧
  (CircuitWellFormed (cuccaroAdd (endpointScratch lQ sc) lQ c) ∧
    ShorECDLP.tCount (acrossOptimized (cuccaroAdd (endpointScratch lQ sc) lQ c)) + 21 =
      ShorECDLP.tCount (cuccaroAdd (endpointScratch lQ sc) lQ c))

private theorem endpoint_facts : ∀ c ∈ List.range' 568 10,
    EndpointFacts (List.range' 522 9) (List.range' 531 9) (List.range' 540 9) (List.range' 559 9) c := by
  unfold EndpointFacts CircuitWellFormed Classical.HPFree
  decide +kernel

def subConstantPatch (n s : Nat) (register constants : List Wire) (c : Wire) (k : Nat)
    (hw : CircuitWellFormed (cuccaroSub constants register c))
    (ht : ShorECDLP.tCount (acrossOptimized (cuccaroSub constants register c)) + 21 =
      ShorECDLP.tCount (cuccaroSub constants register c)) :
    Patch (literalProgram (subConstant register constants c k) : Straight n s s) 21 := by
  unfold subConstant
  exact (((Patch.refl _).joinLiteral (acrossSmallPatch n s 21 _ hw (cuccaroSub_HPFree constants register c) ht)).joinLiteral
    (Patch.refl _)).castSaving (by omega)

def addConstantPatch (n s : Nat) (register constants : List Wire) (c : Wire) (k : Nat)
    (hw : CircuitWellFormed (cuccaroAdd constants register c))
    (ht : ShorECDLP.tCount (acrossOptimized (cuccaroAdd constants register c)) + 21 =
      ShorECDLP.tCount (cuccaroAdd constants register c)) :
    Patch (literalProgram (addConstant register constants c k) : Straight n s s) 21 := by
  unfold addConstant
  exact (((Patch.refl _).joinLiteral (acrossSmallPatch n s 21 _ hw (cuccaroAdd_HPFree constants register c) ht)).joinLiteral
    (Patch.refl _)).castSaving (by omega)

def prepareEndpointPatch (n s : Nat) (lT lQ lS sc : List Wire) (c : Wire) (k : Nat)
    (h : EndpointFacts lT lQ lS sc c) :
    Patch (literalProgram (prepareIntervalEndpoints lT lQ lS sc c 256 k) : Straight n s s) 112 := by
  have he : prepareIntervalEndpoints lT lQ lS sc c 256 k = endpointPrefix lT lQ lS sc c ++
      (subConstant lQ (endpointScratch lQ sc) c k ++ subConstant lS (endpointScratch lS sc) c k) := by
    simp only [prepareIntervalEndpoints, endpointPrefix, List.append_assoc]
  rw [he]
  exact ((acrossSmallPatch n s 70 _ h.1.1 h.1.2.1 h.1.2.2).joinLiteral
    ((subConstantPatch n s _ _ c k h.2.2.1.1 h.2.2.1.2).joinLiteral
      (subConstantPatch n s _ _ c k h.2.2.2.1.1 h.2.2.2.1.2))).castSaving (by omega)

def restoreEndpointPatch (n s : Nat) (lT lQ lS sc : List Wire) (c : Wire) (k : Nat)
    (h : EndpointFacts lT lQ lS sc c) :
    Patch (literalProgram (restoreIntervalEndpoints lT lQ lS sc c 256 k) : Straight n s s) 112 := by
  have he : restoreIntervalEndpoints lT lQ lS sc c 256 k =
      (addConstant lS (endpointScratch lS sc) c k ++ addConstant lQ (endpointScratch lQ sc) c k) ++
        endpointSuffix lT lQ lS sc c := by
    simp only [restoreIntervalEndpoints, endpointSuffix, List.append_assoc]
  rw [he]
  exact (((addConstantPatch n s _ _ c k h.2.2.2.2.1.1 h.2.2.2.2.1.2).joinLiteral
      (addConstantPatch n s _ _ c k h.2.2.2.2.2.1 h.2.2.2.2.2.2)).joinLiteral
    (acrossSmallPatch n s 70 _ h.2.1.1 h.2.1.2.1 h.2.1.2.2)).castSaving (by omega)

def Patch.prependLiteral {n start d f} (gs : Circuit)
    (p : (count : Nat) × Straight n start (start+count))
    (hg : Patch (literalProgram gs : Straight n start start) d) (hp : Patch p.2 f) :
    Patch (Paper2607_13816.ChallengeMigration.prependCompiled gs p).2 (d+f) := by
  unfold Paper2607_13816.ChallengeMigration.prependCompiled
  exact hg.append hp

def intervalEndpointPatch (n start : Nat) (r : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget)
    (h : EndpointFacts r.lengthT r.lengthQ r.lengthS r.endpointScratch (r.carry k K)) :
    Patch (intervalProgram n start r 256 k K mode signUpdate target).2 224 := by
  unfold intervalProgram
  refine (Patch.prependLiteral (d := 112) (f := 112) _ _
    (prepareEndpointPatch n _ _ _ _ _ _ k h) ?_).castSaving (by omega)
  refine (Patch.appendCompiled (d := 0) (f := 112) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.appendCompiled (d := 0) (f := 112) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine Patch.prependCompiled _ _ ?_
  refine (Patch.appendCompiled (d := 0) (f := 112) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.appendCompiled (d := 0) (f := 112) _ _ (Patch.refl _) ?_).castSaving (by omega)
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

/- B3 ladder cancellation adapted from public submission 525ba7ba-fdab-4fe7-bcef-2769cac961c5. -/
def b3Source : Circuit :=
  let r := indexedStepProductionRegisters
  ([.CCX r.phase2 r.sign r.terminal] ++ rControlNonterminal [r.phase1,r.terminal] 0 r.control r.lengthRPrime (r.blockScratch.getD 0 0) (r.blockScratch.drop 1)) ++ [.CCX r.phase2 r.sign r.terminal]

def b3Core : Circuit :=
  [.CCX 0 560 562, .CCX 561 562 558, .CCX 0 560 562]

def b3Inner : Circuit :=
  [.X 0, .X 560, .X 561] ++ b3Core ++ [.X 561, .X 560, .X 0]

def b3K : Circuit :=
  [.CCX 549 550 562] ++ b3Inner ++ [.CCX 549 550 562]

def b3L : Circuit :=
  [.CCX 551 562 563, .CCX 552 563 564, .CCX 553 564 565,
   .CCX 554 565 566, .CCX 555 566 567, .CCX 556 567 568]

def b3Red : Circuit := b3Source.take 9 ++ b3K ++ b3Source.drop 32

theorem b3_decomp : b3Source = b3Source.take 9 ++ (b3L.reverse ++ b3K ++ b3L) ++ b3Source.drop 32 := by
  decide +kernel

theorem b3Red_sublist : b3Red.Sublist b3Source := by
  rw [b3_decomp, b3Red]
  refine List.Sublist.append (List.Sublist.append (List.Sublist.refl _) ?_) (List.Sublist.refl _)
  exact (List.sublist_append_right b3L.reverse b3K).trans (List.sublist_append_left (b3L.reverse ++ b3K) b3L)

theorem b3Red_t : ShorECDLP.tCount b3Red + 84 = ShorECDLP.tCount b3Source := by
  decide +kernel

private theorem b3Core_classical (s : BasisState) :
    Classical.run b3Core s = s[558 ↦ xor (s 558) (s 561 && xor (s 562) (s 0 && s 560))] := by
  funext w
  simp only [b3Core, Classical.run, List.foldl_cons, List.foldl_nil, Classical.applyGate]
  by_cases hw558 : w = 558
  · subst hw558; simp [upd]
  · by_cases hw562 : w = 562
    · subst hw562
      simp [upd, hw558]
    · simp [upd, hw558, hw562]

private theorem b3Inner_classical (s : BasisState) :
    Classical.run b3Inner s = s[558 ↦ xor (s 558) ((!s 561) && xor (s 562) ((!s 0) && (!s 560)))] := by
  funext w
  simp only [b3Inner, Classical.run_append, b3Core_classical]
  simp only [Classical.run, List.foldl_cons, List.foldl_nil, Classical.applyGate]
  by_cases hw0 : w = 0
  · subst hw0; simp [upd]
  · by_cases hw560 : w = 560
    · subst hw560; simp [upd]
    · by_cases hw561 : w = 561
      · subst hw561; simp [upd]
      · by_cases hw558 : w = 558
        · subst hw558; simp [upd]
        · simp [upd, hw0, hw560, hw561, hw558]

private theorem b3K_classical (s : BasisState) :
    Classical.run b3K s =
      s[558 ↦ xor (s 558) ((!s 561) && xor (xor (s 562) (s 549 && s 550)) ((!s 0) && (!s 560)))] := by
  funext w
  simp only [b3K, Classical.run_append, b3Inner_classical]
  simp only [Classical.run, List.foldl_cons, List.foldl_nil, Classical.applyGate]
  by_cases hw562 : w = 562
  · subst hw562
    simp [upd]
  · by_cases hw558 : w = 558
    · subst hw558; simp [upd]
    · simp [upd, hw562, hw558]

private theorem b3_step_classical (a b t : Wire)
    (ha558 : a ≠ 558) (hb558 : b ≠ 558) (ht558 : t ≠ 558)
    (hat : t ≠ a) (hbt : t ≠ b)
    (ht561 : t ≠ 561) (ht562 : t ≠ 562) (ht549 : t ≠ 549) (ht550 : t ≠ 550) (ht0 : t ≠ 0) (ht560 : t ≠ 560)
    (mid : Circuit) (hmid : ∀ s : BasisState, Classical.run mid s = Classical.run b3K s)
    (s : BasisState) :
    Classical.run ([.CCX a b t] ++ mid ++ [.CCX a b t]) s = Classical.run b3K s := by
  funext w
  simp only [Classical.run_append, hmid, b3K_classical]
  simp only [Classical.run, List.foldl_cons, List.foldl_nil, Classical.applyGate]
  by_cases hwt : w = t
  · subst hwt
    simp only [upd, ht558, ha558, hb558, hat.symm, hbt.symm, ↓reduceIte]
    cases s w <;> cases (s a && s b) <;> rfl
  · by_cases hw558 : w = 558
    · subst hw558
      simp only [upd, hwt, ht561.symm, ht562.symm, ht549.symm, ht550.symm, ht0.symm, ht560.symm, ↓reduceIte]
    · simp only [upd, hwt, hw558, ↓reduceIte]

def b3M1 : Circuit := [.CCX 551 562 563] ++ b3K ++ [.CCX 551 562 563]
def b3M2 : Circuit := [.CCX 552 563 564] ++ b3M1 ++ [.CCX 552 563 564]
def b3M3 : Circuit := [.CCX 553 564 565] ++ b3M2 ++ [.CCX 553 564 565]
def b3M4 : Circuit := [.CCX 554 565 566] ++ b3M3 ++ [.CCX 554 565 566]
def b3M5 : Circuit := [.CCX 555 566 567] ++ b3M4 ++ [.CCX 555 566 567]
def b3M6 : Circuit := [.CCX 556 567 568] ++ b3M5 ++ [.CCX 556 567 568]

private theorem b3M1_classical : ∀ s, Classical.run b3M1 s = Classical.run b3K s :=
  b3_step_classical 551 562 563 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) b3K (fun _ => rfl)
private theorem b3M2_classical : ∀ s, Classical.run b3M2 s = Classical.run b3K s :=
  b3_step_classical 552 563 564 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) b3M1 b3M1_classical
private theorem b3M3_classical : ∀ s, Classical.run b3M3 s = Classical.run b3K s :=
  b3_step_classical 553 564 565 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) b3M2 b3M2_classical
private theorem b3M4_classical : ∀ s, Classical.run b3M4 s = Classical.run b3K s :=
  b3_step_classical 554 565 566 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) b3M3 b3M3_classical
private theorem b3M5_classical : ∀ s, Classical.run b3M5 s = Classical.run b3K s :=
  b3_step_classical 555 566 567 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) b3M4 b3M4_classical
private theorem b3M6_classical : ∀ s, Classical.run b3M6 s = Classical.run b3K s :=
  b3_step_classical 556 567 568 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) b3M5 b3M5_classical

private theorem b3M6_eq : b3L.reverse ++ b3K ++ b3L = b3M6 := by decide +kernel
private theorem b3M6_hp : Classical.HPFree b3M6 := by simp [Classical.HPFree,Classical.IsClassicalGate,b3M6,b3M5,b3M4,b3M3,b3M2,b3M1,b3K,b3Inner,b3Core]
private theorem b3K_hp : Classical.HPFree b3K := by simp [Classical.HPFree,Classical.IsClassicalGate,b3K,b3Inner,b3Core]

private theorem b3_linear_basis (A B : State →ₗ[ℂ] State)
    (h : ∀ s, A (ket s) = B (ket s)) : A = B := by
  apply LinearMap.ext
  intro psi
  induction psi using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single s c =>
    have hs : Finsupp.single s c = c • ket s := by ext u; simp [ket]
    rw [hs, map_smul, map_smul, h]

private theorem b3M6_run :
    Quantum.run (b3L.reverse ++ b3K ++ b3L) = Quantum.run b3K := by
  apply b3_linear_basis
  intro s
  rw [b3M6_eq, Quantum.run_ket_agrees_classical _ _ b3M6_hp,
    Quantum.run_ket_agrees_classical _ _ b3K_hp, b3M6_classical]

private theorem b3_sub_run (A C M K : Circuit) (h : Quantum.run M = Quantum.run K) :
    Quantum.run (A ++ M ++ C) = Quantum.run (A ++ K ++ C) := by
  simp only [Quantum.run_append_map, h]

theorem b3Red_run : Quantum.run b3Red = Quantum.run b3Source := by
  unfold b3Red
  conv_rhs => rw [b3_decomp]
  exact (b3_sub_run _ _ _ _ b3M6_run).symm



def b3Patch (n s : Nat) : Patch (literalProgram b3Source : Straight n s s) 84 :=
  Patch.literal _ b3Red b3Red_sublist b3Red_run.symm b3Red_t

def remainderIntervalPatch (n start : Nat) (w : ActiveWindow)
    (hw : intervalLaneCount w.start w.stop ≤ 259)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget) :
    Patch (intervalProgram n start (indexedStepProductionRegisters.remainder w) 256 w.start w.stop
      mode signUpdate target).2 224 := by
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
    Patch (remainderBlockProgram n start indexedStepProductionRegisters 256 w).2 1155 := by
  unfold remainderBlockProgram remainderBlockSegments
  refine (Patch.sequenceCons (d := 98) (f := 1057) _ _ (b1Patch n _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 224) (f := 833) _ _ (remainderIntervalPatch n _ w hw _ _ _) ?_).castSaving (by omega)
  refine (Patch.literalPair (d := 441) (f := 392) b1Source b2Source _ (b12Patch n _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 84) (f := 308) _ _ (b3Patch n _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 224) (f := 84) _ _ (remainderIntervalPatch n _ w hw _ _ _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := 84) (f := 0) _ _ (b3Patch n _) (Patch.refl _)).castSaving (by omega)

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
  CircuitWellFormed (crossCore M c) ∧ Classical.HPFree (crossCore M c) ∧
    ShorECDLP.tCount (acrossOptimized (crossCore M c)) + 805 = ShorECDLP.tCount (crossCore M c)


def forwardMiddle : Circuit := (b1Source ++ b2Source) ++ b3Source

theorem forward_cross_facts : ∀ c ∈ List.range' 569 9, CrossFacts forwardMiddle c := by
  unfold CrossFacts CircuitWellFormed Classical.HPFree
  decide +kernel


/-- Patch of the merged boundary literal `restore ++ M ++ prepare`. -/
def crossLiteralPatch (n s : Nat) (M : Circuit) (c : Wire) (k : Nat)
    (h : EndpointFacts (List.range' 522 9) (List.range' 531 9) (List.range' 540 9) (List.range' 559 9) c)
    (hx : CrossFacts M c) :
    Patch (literalProgram (restoreIntervalEndpoints (List.range' 522 9) (List.range' 531 9) (List.range' 540 9)
        (List.range' 559 9) c 256 k ++ M ++ prepareIntervalEndpoints (List.range' 522 9) (List.range' 531 9)
        (List.range' 540 9) (List.range' 559 9) c 256 k) : Straight n s s) 889 := by
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
    ((acrossSmallPatch n s 805 _ hx.1 hx.2.1 hx.2.2).joinLiteral
      ((subConstantPatch n s _ _ c k h.2.2.1.1 h.2.2.1.2).joinLiteral
        (subConstantPatch n s _ _ c k h.2.2.2.1.1 h.2.2.2.1.2)))).castSaving (by omega)


def remainderCrossPatch (n start : Nat) (w : ActiveWindow)
    (h : EndpointFacts (List.range' 522 9) (List.range' 531 9) (List.range' 540 9) (List.range' 559 9)
      ((indexedStepProductionRegisters.remainder w).carry w.start w.stop))
    (hx : CrossFacts forwardMiddle ((indexedStepProductionRegisters.remainder w).carry w.start w.stop))
    (hE : (indexedStepProductionRegisters.remainder w).endpointScratch = List.range' 559 9) :
    Patch (remainderBlockProgram n start indexedStepProductionRegisters 256 w).2 1295 := by
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
  have hX : Patch X 1295 :=
    (((b1Patch n start).joinLiteral (prepareEndpointPatch n start _ _ _ _ c w.start h)).append
      ((Patch.refl core1.2).append ((crossLiteralPatch n _ forwardMiddle c w.start h hx).append
        ((Patch.refl core2.2).append ((restoreEndpointPatch n _ _ _ _ _ c w.start h).joinLiteral
          (b3Patch n _)))))).castSaving (by omega)
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
  unfold CrossFacts CircuitWellFormed Classical.HPFree
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
       (fun _ => ⟨0, literalProgram E⟩)] : List (FixedSegment n)) start).2 (dC + 1113 + dE) := by
  let rg := indexedStepProductionRegisters.remainder w
  let c := rg.carry w.start w.stop
  let core1 := intervalCore n start rg w.start w.stop RippleMode.add.inverse false .work1
  let core2 := intervalCore n (start + core1.1) rg w.start w.stop RippleMode.sub.inverse true .work1
  let P := prepareIntervalEndpoints (List.range' 522 9) (List.range' 531 9) (List.range' 540 9) (List.range' 559 9) c 256 w.start
  let R := restoreIntervalEndpoints (List.range' 522 9) (List.range' 531 9) (List.range' 540 9) (List.range' 559 9) c 256 w.start
  let X : Straight n start (start + core1.1 + core2.1) :=
    (literalProgram (C ++ P)).append (core1.2.append
      ((literalProgram (R ++ reverseMiddle ++ P)).append (core2.2.append (literalProgram (R ++ E)))))
  have hX : Patch X (dC + 1113 + dE) :=
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

namespace AcrossDHE
private instance classicalDecidable (g : Gate) : Decidable (Classical.IsClassicalGate g) := by
  cases g <;> unfold Classical.IsClassicalGate <;> infer_instance
set_option maxHeartbeats 1000000
def optimized (xs : Circuit) : Circuit := acrossOptimized xs
def Facts (xs : Circuit) (d : Nat) : Prop := CircuitWellFormed xs ∧ Classical.HPFree xs ∧ ShorECDLP.tCount (optimized xs)+d=ShorECDLP.tCount xs

def dPrefix (c : Wire) : Circuit := cuccaroAdd (List.range' 522 9) (List.range' 531 9) c ++ addConstant (List.range' 531 9) (List.range' 560 9) c 3
def dSuffix (c : Wire) : Circuit := subConstant (List.range' 531 9) (List.range' 560 9) c 3 ++ cuccaroSub (List.range' 522 9) (List.range' 531 9) c

theorem dPrefix_facts : ∀ c ∈ 0 :: List.range' 569 9, Facts (dPrefix c) 42 := by
  unfold Facts CircuitWellFormed Classical.HPFree optimized
  decide +kernel

theorem dSuffix_facts : ∀ c ∈ 0 :: List.range' 569 9, Facts (dSuffix c) 42 := by
  unfold Facts CircuitWellFormed Classical.HPFree optimized
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

theorem d1_facts : Facts (blockD1Forward indexedStepProductionRegisters) 7 := by unfold Facts CircuitWellFormed Classical.HPFree optimized; decide +kernel
theorem d3_facts : Facts (blockD3Forward indexedStepProductionRegisters) 7 := by unfold Facts CircuitWellFormed Classical.HPFree optimized; decide +kernel
theorem di1_facts : Facts inverseFirst 7 := by unfold Facts CircuitWellFormed Classical.HPFree optimized; decide +kernel
theorem di3_facts : Facts inverseLast 7 := by unfold Facts CircuitWellFormed Classical.HPFree optimized; decide +kernel

theorem hUpper_facts : Facts (constMinus (List.range' 549 9) (List.range' 562 9) 571 258) 28 := by
  unfold Facts CircuitWellFormed Classical.HPFree optimized; decide +kernel
theorem hLowerAdd_facts : Facts (addConstant (List.range' 522 9) (List.range' 562 9) 571 3) 21 := by
  unfold Facts CircuitWellFormed Classical.HPFree optimized; decide +kernel
theorem hLowerSub_facts : Facts (subConstant (List.range' 522 9) (List.range' 562 9) 571 3) 21 := by
  unfold Facts CircuitWellFormed Classical.HPFree optimized; decide +kernel


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
    Patch (Paper2607_13816.ChallengeMigration.surroundCompiled before after p).2 (a+b+c) := by
  unfold Paper2607_13816.ChallengeMigration.surroundCompiled Paper2607_13816.ChallengeMigration.prependCompiled
  exact (hb.append ((Patch.appendCompiled p ⟨0,literalProgram after⟩ hp (ha _)))).castSaving (by omega)

def dPrefixPatch (n start : Nat) (c : Wire) (hc : c ∈ 0 :: List.range' 569 9) :
    Patch (literalProgram (dPrefix c) : Straight n start start) 42 :=
  acrossSmallPatch n start 42 _ (dPrefix_facts c hc).1 (dPrefix_facts c hc).2.1 (dPrefix_facts c hc).2.2

def dSuffixPatch (n start : Nat) (c : Wire) (hc : c ∈ 0 :: List.range' 569 9) :
    Patch (literalProgram (dSuffix c) : Straight n start start) 42 :=
  acrossSmallPatch n start 42 _ (dSuffix_facts c hc).1 (dSuffix_facts c hc).2.1 (dSuffix_facts c hc).2.2

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
  have hp := ((acrossSmallPatch n start 7 (blockD1Forward r) d1_facts.1 d1_facts.2.1 d1_facts.2.2).joinLiteral
    ((Patch.refl (literalProgram ([.CX r.phase1 r.control,.CX r.phase2 r.control]) : Straight n start start)).joinLiteral
      ((quotientPatch n start w).joinLiteral
        ((Patch.refl (literalProgram ([.CX r.phase2 r.control,.CX r.phase1 r.control]) : Straight n start start)).joinLiteral
          (acrossSmallPatch n start 7 (blockD3Forward r) d3_facts.1 d3_facts.2.1 d3_facts.2.2))))).castSaving (show 7+(0+(84+(0+7)))=98 by omega)
  simpa only [blockDForward,blockD2Forward,List.append_assoc] using hp

def dInversePatch (n start : Nat) (w : ActiveWindow) :
    Patch (literalProgram (blockDInverse indexedStepProductionRegisters w) : Straight n start start) 98 := by
  let r := indexedStepProductionRegisters
  have hp := ((acrossSmallPatch n start 7 inverseFirst di1_facts.1 di1_facts.2.1 di1_facts.2.2).joinLiteral
    ((Patch.refl (literalProgram ([.CX r.phase1 r.control,.CX r.phase2 r.control]) : Straight n start start)).joinLiteral
      ((quotientPatch n start w).joinLiteral
        ((Patch.refl (literalProgram ([.CX r.phase2 r.control,.CX r.phase1 r.control]) : Straight n start start)).joinLiteral
          (acrossSmallPatch n start 7 inverseLast di3_facts.1 di3_facts.2.1 di3_facts.2.2))))).castSaving (show 7+(0+(84+(0+7)))=98 by omega)
  simpa only [blockDInverse,inverseFirst,inverseLast,List.append_assoc] using hp

def upperPatch (n start T : Nat) :
    Patch (upperEndProgram n start (indexedStepProductionRegisters.endIteration 256 T) 256 (endIterationWindowsAt 256 T)).2 56 := by
  have hv := endpoint_views T
  unfold upperEndProgram ltUpdateProgram
  dsimp only
  refine (surroundPatch (a:=28) (b:=0) (c:=28) _ _ _ ?_ (Patch.refl _) ?_).castSaving (by omega)
  · simpa only [hv.1,hv.2] using (acrossSmallPatch n start 28 _ hUpper_facts.1 hUpper_facts.2.1 hUpper_facts.2.2)
  · intro cursor
    simpa only [hv.1,hv.2] using (acrossSmallPatch n cursor 28 _ hUpper_facts.1 hUpper_facts.2.1 hUpper_facts.2.2)

def lowerPatch (n start T : Nat) :
    Patch (lowerEndProgram n start (indexedStepProductionRegisters.endIteration 256 T) 256 (endIterationWindowsAt 256 T)).2 42 := by
  have hv := endpoint_views T
  unfold lowerEndProgram lrpUpdateProgram
  dsimp only
  refine (surroundPatch (a:=21) (b:=0) (c:=21) _ _ _ ?_ (Patch.refl _) ?_).castSaving (by omega)
  · simpa only [hv.1,hv.2] using (acrossSmallPatch n start 21 _ hLowerAdd_facts.1 hLowerAdd_facts.2.1 hLowerAdd_facts.2.2)
  · intro cursor
    simpa only [hv.1,hv.2] using (acrossSmallPatch n cursor 21 _ hLowerSub_facts.1 hLowerSub_facts.2.1 hLowerSub_facts.2.2)

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

private def ofCompiledEq {n start d} {p q : (count : Nat) × Straight n start (start+count)}
    (he : p = q) (hp : Patch q.2 d) : Patch p.2 d := by cases he; exact hp

def hPatch (n start T : Nat) :
    Patch (hProgram n start indexedStepProductionRegisters 256 T).2 (hSaving T) := by
  by_cases ht : T%4=0
  · rw [hSaving, if_pos ht]
    exact ofCompiledEq (p := hProgram n start indexedStepProductionRegisters 256 T)
      (by simp only [hProgram, if_pos ht]; rfl)
      (Patch.surroundCompiled _ _ _ (endPatch n start T))
  · rw [hSaving, if_neg ht]
    exact ofCompiledEq (p := hProgram n start indexedStepProductionRegisters 256 T)
      (q := ⟨0, .done⟩) (by simp only [hProgram, if_neg ht]) (Patch.refl _)

def hInversePatch (n start T : Nat) :
    Patch (hInverseProgram n start indexedStepProductionRegisters 256 T).2 (hSaving T) := by
  by_cases ht : T%4=0
  · rw [hSaving, if_pos ht]
    exact ofCompiledEq (p := hInverseProgram n start indexedStepProductionRegisters 256 T)
      (by simp only [hInverseProgram, if_pos ht]; rfl)
      (Patch.surroundCompiled _ _ _ (endInversePatch n start T))
  · rw [hSaving, if_neg ht]
    exact ofCompiledEq (p := hInverseProgram n start indexedStepProductionRegisters 256 T)
      (q := ⟨0, .done⟩) (by simp only [hInverseProgram, if_neg ht]) (Patch.refl _)

def reverseCleanSource : Circuit :=
  let r := indexedStepProductionRegisters
  prepareLatestPaperTBoundary r.tBoundary 256 ++ computeControl [r.phase1] 1 r.control r.blockScratch

def reversePrepSource : Circuit :=
  let r := indexedStepProductionRegisters
  computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++
    computeControl [r.phase1,r.terminal] 1 r.control r.blockScratch ++
    computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++ restoreLatestPaperTBoundary r.tBoundary 256

theorem ePrep_facts : Facts ePrepSource 70 := by
  unfold Facts CircuitWellFormed Classical.HPFree optimized
  decide +kernel

theorem eClean_facts : Facts eCleanSource 70 := by
  unfold Facts CircuitWellFormed Classical.HPFree optimized
  decide +kernel

theorem eInverseClean_facts : Facts reverseCleanSource 70 := by
  unfold Facts CircuitWellFormed Classical.HPFree optimized
  decide +kernel

theorem eInversePrep_facts : Facts reversePrepSource 70 := by
  unfold Facts CircuitWellFormed Classical.HPFree optimized
  decide +kernel

def ePrepPatch (n s : Nat) : Patch (literalProgram ePrepSource : Straight n s s) 70 :=
  acrossSmallPatch n s 70 _ ePrep_facts.1 ePrep_facts.2.1 ePrep_facts.2.2

def eCleanPatch (n s : Nat) : Patch (literalProgram eCleanSource : Straight n s s) 70 :=
  acrossSmallPatch n s 70 _ eClean_facts.1 eClean_facts.2.1 eClean_facts.2.2

def reverseCleanPatch (n s : Nat) : Patch (literalProgram reverseCleanSource : Straight n s s) 70 :=
  acrossSmallPatch n s 70 _ eInverseClean_facts.1 eInverseClean_facts.2.1 eInverseClean_facts.2.2

def reversePrepPatch (n s : Nat) : Patch (literalProgram reversePrepSource : Straight n s s) 70 :=
  acrossSmallPatch n s 70 _ eInversePrep_facts.1 eInversePrep_facts.2.1 eInversePrep_facts.2.2

end AcrossDHE



def ePrepPatch (n start : Nat) : Patch (literalProgram ePrepSource : Straight n start start) 70 :=
  AcrossDHE.ePrepPatch n start

def eCleanPatch (n start : Nat) : Patch (literalProgram eCleanSource : Straight n start start) 70 :=
  AcrossDHE.eCleanPatch n start

def coefficientPatch (n start : Nat) (w : ActiveWindow) :
    Patch (coefficientBlockProgram n start indexedStepProductionRegisters 256 w).2 140 := by
  unfold coefficientBlockProgram coefficientBlockSegments
  refine (Patch.sequenceCons (d := 70) (f := 70) _ _ (ePrepPatch n _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 70) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 70) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 70) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := 70) (f := 0) _ _ (eCleanPatch n _) (Patch.refl _)).castSaving (by omega)

def hSaving (T : Nat) : Nat := if T%4=0 then 98 else 0

def hPatch (n start T : Nat) : Patch (hProgram n start indexedStepProductionRegisters 256 T).2 (hSaving T) :=
  AcrossDHE.hPatch n start T

def hInversePatch (n start T : Nat) : Patch (hInverseProgram n start indexedStepProductionRegisters 256 T).2 (hSaving T) :=
  AcrossDHE.hInversePatch n start T

def dPatch (n s : Nat) (w : ActiveWindow) :
    Patch (literalProgram (blockDForward indexedStepProductionRegisters w) : Straight n s s) 98 :=
  AcrossDHE.dForwardPatch n s w

def dInversePatch (n s : Nat) (w : ActiveWindow) :
    Patch (literalProgram (blockDInverse indexedStepProductionRegisters w) : Straight n s s) 98 :=
  AcrossDHE.dInversePatch n s w

def epochDPatch (n s : Nat) (w : ActiveWindow) :
    Patch (literalProgram (Cancellation.epochSource ++ blockDForward indexedStepProductionRegisters w) : Straight n s s) 210 := by
  have hp := ((epochPatch n s ([] : Circuit)).joinLiteral (dPatch n s w)).castSaving (show 112+98=210 by omega)
  simpa only [List.append_nil] using hp

def candidateStepPatch (n start T : Nat) :
    Patch (measuredStepProgram n start indexedStepProductionRegisters 256 T).2 (1680+hSaving T) := by
  unfold measuredStepProgram measuredStepSegments
  refine (Patch.sequenceCons (d := 140) (f := 1540+hSaving T) _ _ (aPatch n _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 1155) (f := 385+hSaving T) _ _ (remainderPatchAll n _ _ (certified_remainder_count T)) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 210) (f := 175+hSaving T) _ _ (epochDPatch n _ _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 140) (f := 35+hSaving T) _ _ (coefficientPatch n _ _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 35) (f := hSaving T) _ _ (fPatch n _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := hSaving T) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := hSaving T) (f := 0) _ _ (hPatch n _ T) (Patch.refl _)).castSaving (by omega)

/-- The remainder block with its two intervals cancelled across their shared boundary. -/
def crossStepPatch (n start T : Nat) (hT : T < 1542) :
    Patch (measuredStepProgram n start indexedStepProductionRegisters 256 T).2 (1820+hSaving T) := by
  have hi := early_cross_inputs T hT
  unfold measuredStepProgram measuredStepSegments
  refine (Patch.sequenceCons (d := 140) (f := 1680+hSaving T) _ _ (aPatch n _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 1295) (f := 385+hSaving T) _ _ (remainderCrossPatch n _ _ hi.1 hi.2.1 hi.2.2.2) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 210) (f := 175+hSaving T) _ _ (epochDPatch n _ _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 140) (f := 35+hSaving T) _ _ (coefficientPatch n _ _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 35) (f := hSaving T) _ _ (fPatch n _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := hSaving T) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := hSaving T) (f := 0) _ _ (hPatch n _ T) (Patch.refl _)).castSaving (by omega)

/-- Exact per-step saving.  The late steps use a remainder carry wire shared with the fixed
remainder controls, so their cross-boundary cancellation is not claimed. -/
def stepSaving (T : Nat) : Nat := (if T < 1542 then 1820 else 1680) + hSaving T

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

private theorem scheduleSaving_full : scheduleSaving 1620 1 = 2977030 := by decide

def eeaForwardPatch (n start : Nat) :
    Patch (measuredEEAForwardProgram n start indexedStepProductionRegisters).2 2977030 := by
  unfold measuredEEAForwardProgram
  exact (schedulePatch n 1620 1 start).castSaving scheduleSaving_full


attribute [local irreducible] lengthInitialize FanoutInitializer.program
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
      ((List.range' 7 256).reverse.take 254) (2^256-2^32-977)) : Straight n start start) 912135 :=
  Patch.literalChecked _ _ FanoutInitializer.initializer_bound FanoutInitializer.initializer_run

def setupPatch (n start : Nat) : Patch (literalProgram eeaLengthSetup : Straight n start start) 912135 := by
  exact (((Patch.refl (literalProgram (xorConstant (List.range' 531 9) 511) : Straight n start start)).joinInitializerLiteral
    (Patch.refl (literalProgram (xorConstant (List.range' 540 9) 511) : Straight n start start))).joinInitializerLiteral
    (initialPatch n start)).castSaving (by omega)

def undoPatch (n start : Nat) : Patch (literalProgram eeaLengthUndo : Straight n start start) 912135 := by
  exact (((initialPatch n start).joinInitializerLiteral
    (Patch.refl (literalProgram (xorConstant (List.range' 531 9) 511) : Straight n start start))).joinInitializerLiteral
    (Patch.refl (literalProgram (xorConstant (List.range' 540 9) 511) : Straight n start start))).castSaving (by omega)

def preprocessPatch (n start : Nat) : Patch (preprocessProgram n start).2 912135 := by
  unfold preprocessProgram surroundCompiled prependCompiled
  exact ((Patch.refl _).append
    (Patch.appendCompiled _ _ (Patch.refl _) (setupPatch n _))).castSaving (by omega)

def unpreprocessPatch (n start : Nat) : Patch (unpreprocessProgram n start).2 912135 := by
  unfold unpreprocessProgram surroundCompiled prependCompiled
  exact ((undoPatch n start).append (Patch.refl _)).castSaving (by omega)

def wrapperPatch (n start : Nat) :
    Patch (measuredForwardWrapperProgram n start).2 3889165 := by
  unfold measuredForwardWrapperProgram measuredForwardWrapperSegments
  refine (Patch.sequenceCons (d := 912135) (f := 2977030) _ _ (preprocessPatch n _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := 2977030) (f := 0) _ _ (eeaForwardPatch n _) (Patch.refl _)).castSaving (by omega)


def reverseCleanSource : Circuit :=
  let r := indexedStepProductionRegisters
  prepareLatestPaperTBoundary r.tBoundary 256 ++ computeControl [r.phase1] 1 r.control r.blockScratch

def reversePrepSource : Circuit :=
  let r := indexedStepProductionRegisters
  computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++
    computeControl [r.phase1,r.terminal] 1 r.control r.blockScratch ++
    computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++ restoreLatestPaperTBoundary r.tBoundary 256

def reverseCleanPatch (n s : Nat) : Patch (literalProgram reverseCleanSource : Straight n s s) 70 :=
  AcrossDHE.reverseCleanPatch n s

def reversePrepPatch (n s : Nat) : Patch (literalProgram reversePrepSource : Straight n s s) 70 :=
  AcrossDHE.reversePrepPatch n s

def reverseEpochPatch (n s : Nat) :
    Patch (literalProgram (blockCInverse indexedStepProductionRegisters) : Straight n s s) 112 :=
  optimizedLiteralPatch n s 112 _ (by unfold CircuitWellFormed; decide +kernel) (by decide +kernel)

/-- The reverse A literal is split around the terminal-padding epoch test.
Source arithmetic: VerifiedQC/ShorECDLP PR #551, Apache-2.0. -/
def aInversePatch (n start : Nat) :
    Patch (literalProgram (blockAInverse indexedStepProductionRegisters) : Straight n start start) 140 :=
  AdjacentArithmetic.aInversePatch n start

def fInversePatch (n start : Nat) :
    Patch (literalProgram (blockFForward indexedStepProductionRegisters).adjoint : Straight n start start) 35 :=
  AdjacentArithmetic.fInversePatch n start

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
      (([.CCX r.phase2 r.sign r.terminal] ++ rControlNonterminal [r.phase1,r.terminal] 0 r.control r.lengthRPrime (r.blockScratch.getD 0 0) (r.blockScratch.drop 1)) ++ [.CCX r.phase2 r.sign r.terminal])) : Straight n s s) 364 := by
  have hp := ((((reversePrepPatch n s).joinLiteral
    (dInversePatch n s w)).joinLiteral
    (reverseEpochPatch n s)).joinLiteral (b3Patch n s)).castSaving
    (show 70+98+112+84=364 by omega)
  simpa only [reversePrepSource, b3Source, List.append_assoc] using hp

def reverseRemainderPatch (n s : Nat) :
    Patch (literalProgram (b3Source ++ b2Source ++ b1Source) : Straight n s s) 441 :=
  smallPatch n s 441 _ (by unfold CircuitWellFormed; decide +kernel)
    (by unfold Classical.HPFree; decide +kernel) (by decide +kernel)

def reverseStepPatch (n start T : Nat) :
    Patch (measuredInverseStepProgram n start indexedStepProductionRegisters T).2 (1596+hSaving T) := by
  unfold measuredInverseStepProgram measuredInverseStepSegments
  refine (Patch.sequenceCons (d := hSaving T) (f := 1596) _ _ (hInversePatch n _ T) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 1596) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 105) (f := 1491) _ _ ?_ ?_).castSaving (by omega)
  · exact reverseFrontPatch n _
  refine (Patch.sequenceCons (d := 0) (f := 1491) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 1491) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 1491) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 364) (f := 1127) _ _ ?_ ?_).castSaving (by omega)
  · exact reverseCombinedPatch n _ (certifiedActiveWindows 256 T).quotientSwap
  refine (Patch.sequenceCons (d := 224) (f := 903) _ _ ?_ ?_).castSaving (by omega)
  · unfold intervalInverseProgram
    exact remainderIntervalPatch n _ _ (certified_remainder_count T) _ _ _
  refine (Patch.sequenceCons (d := 441) (f := 462) _ _ ?_ ?_).castSaving (by omega)
  · exact reverseRemainderPatch n _
  refine (Patch.sequenceCons (d := 224) (f := 238) _ _ ?_ ?_).castSaving (by omega)
  · unfold intervalInverseProgram
    exact remainderIntervalPatch n _ _ (certified_remainder_count T) _ _ _
  exact (Patch.sequenceCons (d := 238) (f := 0) _ _
    (((b1Patch n _).joinLiteral (aInversePatch n _)).castSaving (by omega)) (Patch.refl _)).castSaving (by omega)

def reverseCrossStepPatch (n start T : Nat) (hT : T < 1542) :
    Patch (measuredInverseStepProgram n start indexedStepProductionRegisters T).2 (1820+hSaving T) := by
  have hi := early_cross_inputs T hT
  unfold measuredInverseStepProgram measuredInverseStepSegments
  refine (Patch.sequenceCons (d := hSaving T) (f := 1820) _ _ (hInversePatch n _ T) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 1820) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 105) (f := 1715) _ _ ?_ ?_).castSaving (by omega)
  · exact reverseFrontPatch n _
  refine (Patch.sequenceCons (d := 0) (f := 1715) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 1715) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 1715) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact reverseTailCrossPatch n _ _ _ _ hi.1 hi.2.2.1 hi.2.2.2
    (reverseCombinedPatch n _ (certifiedActiveWindows 256 T).quotientSwap)
    (fun s => ((b1Patch n s).joinLiteral (aInversePatch n s)).castSaving (show 98 + 140 = 238 by omega))

def reverseCombinedOnePatch (n s : Nat) :
    Patch (literalProgram (reverseCombinedSource 1) : Straight n s s) 700 :=
  acrossSmallPatch n s 700 _ (by unfold reverseCombinedSource CircuitWellFormed; decide +kernel)
    (by unfold reverseCombinedSource Classical.HPFree; decide +kernel) (by decide +kernel)

def reverseCrossStepOnePatch (n start : Nat) :
    Patch (measuredInverseStepProgram n start indexedStepProductionRegisters 1).2 (2156+hSaving 1) := by
  have hi := early_cross_inputs 1 (by decide)
  unfold measuredInverseStepProgram measuredInverseStepSegments
  refine (Patch.sequenceCons (d := hSaving 1) (f := 2156) _ _ (hInversePatch n _ 1) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 2156) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 105) (f := 2051) _ _ ?_ ?_).castSaving (by omega)
  · exact reverseFrontPatch n _
  refine (Patch.sequenceCons (d := 0) (f := 2051) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 2051) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 2051) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact reverseTailCrossPatch n _ _ _ _ hi.1 hi.2.2.1 hi.2.2.2
    (by simpa only [reverseCombinedSource] using reverseCombinedOnePatch n _)
    (fun s => ((b1Patch n s).joinLiteral (aInversePatch n s)).castSaving (show 98 + 140 = 238 by omega))

def reverseStepSaving (T : Nat) : Nat := (if T < 1542 then 1820 else 1596) + hSaving T + if T = 1 then 336 else 0

def reverseStepPatchT (n start T : Nat) :
    Patch (measuredInverseStepProgram n start indexedStepProductionRegisters T).2 (reverseStepSaving T) := by
  by_cases h : T = 1
  · subst T
    exact (reverseCrossStepOnePatch n start).castSaving (by simp [reverseStepSaving,hSaving])
  · by_cases ht : T < 1542
    · exact (reverseCrossStepPatch n start T ht).castSaving (by simp [reverseStepSaving,h,ht])
    · exact (reverseStepPatch n start T).castSaving (by simp [reverseStepSaving,h,ht])

def reverseScheduleSaving : Nat → Nat → Nat
  | 0, _ => 0
  | count+1, first => reverseStepSaving first + reverseScheduleSaving count (first+1)

def reverseSchedulePatch (n : Nat) : (count first start : Nat) →
    Patch (measuredInverseScheduleProgram n indexedStepProductionRegisters count first start).2
      (reverseScheduleSaving count first)
  | 0, _, _ => Patch.refl _
  | count+1, first, start => by
    simp only [measuredInverseScheduleProgram]
    exact (Patch.appendCompiled _ _ (reverseSchedulePatch n count (first+1) start)
      (reverseStepPatchT n _ first)).castSaving (by simp only [reverseScheduleSaving]; omega)

private theorem reverseScheduleSaving_full : reverseScheduleSaving 1620 1 = 2970730 := by decide

def eeaReversePatch (n start : Nat) :
    Patch (measuredEEAReverseProgram n start indexedStepProductionRegisters).2 2970730 := by
  unfold measuredEEAReverseProgram
  exact (reverseSchedulePatch n 1620 1 start).castSaving reverseScheduleSaving_full

def reverseWrapperPatch (n start : Nat) :
    Patch (measuredReverseWrapperProgram n start).2 3882865 := by
  unfold measuredReverseWrapperProgram measuredReverseWrapperSegments
  refine (Patch.sequenceCons (d := 0) (f := 3882865) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 3882865) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 3882865) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 2970730) (f := 912135) _ _ (eeaReversePatch n _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := 912135) (f := 0) _ _ (unpreprocessPatch n _) (Patch.refl _)).castSaving (by omega)

def Patch.relabelCompiled {n start d} (e : Wire ≃ Wire)
    (p : (count : Nat) × Straight n start (start+count)) (hp : Patch p.2 d) :
    Patch (Paper2607_13816.ChallengeMigration.relabelCompiled e p).2 d :=
  hp.relabel e

def forwardDataPatch (n start : Nat) : Patch (measuredForwardDataBankProgram n start).2 3889165 := by
  unfold measuredForwardDataBankProgram
  exact Patch.relabelCompiled eeaWorkspaceExchange _ (wrapperPatch n start)

def reverseDataPatch (n start : Nat) : Patch (measuredReverseDataBankProgram n start).2 3882865 := by
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
    Patch (divisionAfterResetProgram n start prior).2 3882865 := by
  unfold divisionAfterResetProgram appendRetaining
  exact (Patch.appendCompiled (d := 3882865) (f := 0) _ _
    ((Patch.appendCompiled (d := 3882865) (f := 0) _ _ (reverseDataPatch n start) (Patch.refl _)).castSaving (by omega))
    (Patch.refl _)).castSaving (by omega)


namespace MeasuredArithmetic
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
def aPatch (n start : Nat) : Patch (literalProgram aSource : Straight n start start) 140 :=
  AdjacentArithmetic.aPatch n start

def fPatch (n start : Nat) : Patch (literalProgram (blockFForward indexedStepProductionRegisters) : Straight n start start) 35 :=
  AdjacentArithmetic.fPatch n start

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000


def quotientPatch (n start : Nat) (w : ActiveWindow) :
    Patch (MeasuredQuotient.program n start (indexedStepProductionRegisters.quotient w) w.start w.stop).2 84 := by
  have hv := AcrossDHE.quotient_views w
  unfold MeasuredQuotient.program
  refine (AcrossDHE.surroundPatch (a:=42) (b:=0) (c:=42) _ _ _ ?_ (Patch.refl _) ?_).castSaving (by omega)
  · simpa only [AcrossDHE.dPrefix,hv.1] using AcrossDHE.dPrefixPatch n start _ hv.2
  · intro cursor
    simpa only [AcrossDHE.dSuffix,hv.1] using AcrossDHE.dSuffixPatch n cursor _ hv.2

def d2Patch (n start : Nat) (w : ActiveWindow) :
    Patch (MeasuredQuotient.d2Program n start indexedStepProductionRegisters w).2 84 := by
  unfold MeasuredQuotient.d2Program
  exact Patch.surroundCompiled _ _ _ (quotientPatch n start w)

def dPatch (n start : Nat) (w : ActiveWindow) :
    Patch (MeasuredQuotient.dProgram n start indexedStepProductionRegisters w).2 98 := by
  unfold MeasuredQuotient.dProgram
  refine (AcrossDHE.surroundPatch (a:=7) (b:=84) (c:=7) _ _ _ ?_ (d2Patch n start w) ?_).castSaving (by omega)
  · exact acrossSmallPatch n start 7 _ AcrossDHE.d1_facts.1 AcrossDHE.d1_facts.2.1 AcrossDHE.d1_facts.2.2
  · intro cursor
    exact acrossSmallPatch n cursor 7 _ AcrossDHE.d3_facts.1 AcrossDHE.d3_facts.2.1 AcrossDHE.d3_facts.2.2

def epochDPatch (n start T : Nat) :
    Patch (MeasuredQuotient.cdProgram n start indexedStepProductionRegisters 256 T).2 210 := by
  unfold MeasuredQuotient.cdProgram
  refine (Patch.prependLiteral (d:=112) (f:=98) _ _ ?_ (dPatch n start _)).castSaving (by omega)
  simpa only [List.append_nil] using epochPatch n start ([] : Circuit)

def ePrepPatch (n start : Nat) : Patch (literalProgram ePrepSource : Straight n start start) 70 :=
  AcrossDHE.ePrepPatch n start

def eCleanPatch (n start : Nat) : Patch (literalProgram eCleanSource : Straight n start start) 70 :=
  AcrossDHE.eCleanPatch n start

def coefficientPatch (n start : Nat) (w : ActiveWindow) :
    Patch (coefficientBlockProgram n start indexedStepProductionRegisters 256 w).2 140 := by
  unfold coefficientBlockProgram coefficientBlockSegments
  refine (Patch.sequenceCons (d := 70) (f := 70) _ _ (ePrepPatch n _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 70) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 70) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 70) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := 70) (f := 0) _ _ (eCleanPatch n _) (Patch.refl _)).castSaving (by omega)

def hSaving (T : Nat) : Nat := if T%4=0 then 98 else 0

def hPatch (n start T : Nat) : Patch (hProgram n start indexedStepProductionRegisters 256 T).2 (hSaving T) :=
  AcrossDHE.hPatch n start T

def hInversePatch (n start T : Nat) : Patch (hInverseProgram n start indexedStepProductionRegisters 256 T).2 (hSaving T) :=
  AcrossDHE.hInversePatch n start T

def candidateStepPatch (n start T : Nat) :
    Patch (MeasuredQuotient.stepProgram n start indexedStepProductionRegisters 256 T).2 (1680+hSaving T) := by
  unfold MeasuredQuotient.stepProgram MeasuredQuotient.stepSegments
  refine (Patch.sequenceCons (d := 140) (f := 1540+hSaving T) _ _ (aPatch n _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 1155) (f := 385+hSaving T) _ _ (remainderPatchAll n _ _ (certified_remainder_count T)) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 210) (f := 175+hSaving T) _ _ (epochDPatch n _ _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 140) (f := 35+hSaving T) _ _ (coefficientPatch n _ _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 35) (f := hSaving T) _ _ (fPatch n _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := hSaving T) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := hSaving T) (f := 0) _ _ (hPatch n _ T) (Patch.refl _)).castSaving (by omega)

/-- The remainder block with its two intervals cancelled across their shared boundary. -/
def crossStepPatch (n start T : Nat) (hT : T < 1542) :
    Patch (MeasuredQuotient.stepProgram n start indexedStepProductionRegisters 256 T).2 (1820+hSaving T) := by
  have hi := early_cross_inputs T hT
  unfold MeasuredQuotient.stepProgram MeasuredQuotient.stepSegments
  refine (Patch.sequenceCons (d := 140) (f := 1680+hSaving T) _ _ (aPatch n _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 1295) (f := 385+hSaving T) _ _ (remainderCrossPatch n _ _ hi.1 hi.2.1 hi.2.2.2) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 210) (f := 175+hSaving T) _ _ (epochDPatch n _ _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 140) (f := 35+hSaving T) _ _ (coefficientPatch n _ _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 35) (f := hSaving T) _ _ (fPatch n _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := hSaving T) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := hSaving T) (f := 0) _ _ (hPatch n _ T) (Patch.refl _)).castSaving (by omega)

/-- Exact per-step saving.  The late steps use a remainder carry wire shared with the fixed
remainder controls, so their cross-boundary cancellation is not claimed. -/
def stepSaving (T : Nat) : Nat := (if T < 1542 then 1820 else 1680) + hSaving T

/-- Optimize the fixed A, remainder-control, epoch and coefficient-boundary literals. -/
def stepPatch (n start T : Nat) :
    Patch (MeasuredQuotient.stepProgram n start indexedStepProductionRegisters 256 T).2 (stepSaving T) :=
  if hT : T < 1542 then (crossStepPatch n start T hT).castSaving (by simp [stepSaving, hT])
  else (candidateStepPatch n start T).castSaving (by simp [stepSaving, hT])

def scheduleSaving : Nat → Nat → Nat
  | 0, _ => 0
  | count+1, first => stepSaving first + scheduleSaving count (first+1)

/-- Exact per-step savings accumulate through the fixed 1,620-step schedule. -/

def schedulePatch (n : Nat) : (count first start : Nat) →
    Patch (MeasuredQuotient.scheduleProgram n indexedStepProductionRegisters 256 count first start).2
      (scheduleSaving count first)
  | 0, _, _ => Patch.refl _
  | count+1, first, start => by
    simp only [MeasuredQuotient.scheduleProgram]
    exact (Patch.appendCompiled _ _ (stepPatch n start first)
      (schedulePatch n count (first+1) _)).castSaving (by simp only [scheduleSaving])

private theorem scheduleSaving_full : scheduleSaving 1620 1 = 2977030 := by decide

def eeaForwardPatch (n start : Nat) :
    Patch (MeasuredQuotient.forwardProgram n start indexedStepProductionRegisters).2 2977030 := by
  unfold MeasuredQuotient.forwardProgram
  exact (schedulePatch n 1620 1 start).castSaving scheduleSaving_full


def initialPatch (n start : Nat) :
    Patch (literalProgram (lengthInitialize (List.range' 266 256) (List.range' 549 9) 558
      ((List.range' 7 256).reverse.take 254) (2^256-2^32-977)) : Straight n start start) 912135 :=
  Patch.literalChecked _ _ FanoutInitializer.initializer_bound FanoutInitializer.initializer_run

def setupPatch (n start : Nat) : Patch (literalProgram eeaLengthSetup : Straight n start start) 912135 := by
  exact (((Patch.refl (literalProgram (xorConstant (List.range' 531 9) 511) : Straight n start start)).joinLiteral
    (Patch.refl (literalProgram (xorConstant (List.range' 540 9) 511) : Straight n start start))).joinLiteral
    (initialPatch n start)).castSaving (by omega)

def undoPatch (n start : Nat) : Patch (literalProgram eeaLengthUndo : Straight n start start) 912135 := by
  exact (((initialPatch n start).joinLiteral
    (Patch.refl (literalProgram (xorConstant (List.range' 531 9) 511) : Straight n start start))).joinLiteral
    (Patch.refl (literalProgram (xorConstant (List.range' 540 9) 511) : Straight n start start))).castSaving (by omega)

def preprocessPatch (n start : Nat) : Patch (preprocessProgram n start).2 912135 := by
  unfold preprocessProgram surroundCompiled prependCompiled
  exact ((Patch.refl _).append
    (Patch.appendCompiled _ _ (Patch.refl _) (setupPatch n _))).castSaving (by omega)

def unpreprocessPatch (n start : Nat) : Patch (unpreprocessProgram n start).2 912135 := by
  unfold unpreprocessProgram surroundCompiled prependCompiled
  exact ((undoPatch n start).append (Patch.refl _)).castSaving (by omega)

def wrapperPatch (n start : Nat) :
    Patch (MeasuredQuotient.wrapperProgram n start).2 3889165 := by
  unfold MeasuredQuotient.wrapperProgram MeasuredQuotient.wrapperSegments
  refine (Patch.sequenceCons (d := 912135) (f := 2977030) _ _ (preprocessPatch n _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := 2977030) (f := 0) _ _ (eeaForwardPatch n _) (Patch.refl _)).castSaving (by omega)



end MeasuredArithmetic

namespace ReverseMeasuredArithmetic
attribute [local irreducible] MeasuredQuotient.Reverse.program
  MeasuredQuotient.Reverse.wrapperProgram

def dPatch (n start : Nat) (w : ActiveWindow) :
    Patch (MeasuredQuotient.Reverse.program n start indexedStepProductionRegisters w).2 98 := by
  unfold MeasuredQuotient.Reverse.program
  refine (AcrossDHE.surroundPatch (a:=7) (b:=84) (c:=7) _ _ _ ?_
    (MeasuredArithmetic.d2Patch n start w) ?_).castSaving (by omega)
  · exact acrossSmallPatch n start 7 _ AcrossDHE.di1_facts.1 AcrossDHE.di1_facts.2.1 AcrossDHE.di1_facts.2.2
  · intro cursor
    exact acrossSmallPatch n cursor 7 _ AcrossDHE.di3_facts.1 AcrossDHE.di3_facts.2.1 AcrossDHE.di3_facts.2.2

def entryBeforePatch (n start : Nat) :
    Patch (literalProgram (MeasuredQuotient.Reverse.entryBefore indexedStepProductionRegisters 256) : Straight n start start) 70 :=
  reversePrepPatch n start

def entryAfterPatch (n start : Nat) :
    Patch (literalProgram (MeasuredQuotient.Reverse.entryAfter indexedStepProductionRegisters) : Straight n start start) 196 := by
  exact ((reverseEpochPatch n start).joinLiteral
    (b3Patch n start)).castSaving (by omega)
def reverseStepPatch (n start T : Nat) :
    Patch (MeasuredQuotient.Reverse.stepProgram n start indexedStepProductionRegisters T).2 (1596+hSaving T) := by
  unfold MeasuredQuotient.Reverse.stepProgram MeasuredQuotient.Reverse.stepSegments
  refine (Patch.sequenceCons (d := hSaving T) (f := 1596) _ _ (hInversePatch n _ T) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 1596) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 105) (f := 1491) _ _ ?_ ?_).castSaving (by omega)
  · exact reverseFrontPatch n _
  refine (Patch.sequenceCons (d := 0) (f := 1491) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 1491) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 1491) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 70) (f := 1421) _ _ (entryBeforePatch n _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 98) (f := 1323) _ _ (dPatch n _ _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 196) (f := 1127) _ _ (entryAfterPatch n _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 224) (f := 903) _ _ ?_ ?_).castSaving (by omega)
  · unfold intervalInverseProgram
    exact remainderIntervalPatch n _ _ (certified_remainder_count T) _ _ _
  refine (Patch.sequenceCons (d := 441) (f := 462) _ _ ?_ ?_).castSaving (by omega)
  · exact reverseRemainderPatch n _
  refine (Patch.sequenceCons (d := 224) (f := 238) _ _ ?_ ?_).castSaving (by omega)
  · unfold intervalInverseProgram
    exact remainderIntervalPatch n _ _ (certified_remainder_count T) _ _ _
  exact (Patch.sequenceCons (d := 238) (f := 0) _ _
    (((b1Patch n _).joinLiteral (aInversePatch n _)).castSaving (by omega)) (Patch.refl _)).castSaving (by omega)

def reverseCrossStepPatch (n start T : Nat) (hT : T < 1542) :
    Patch (MeasuredQuotient.Reverse.stepProgram n start indexedStepProductionRegisters T).2 (1820+hSaving T) := by
  have hi := early_cross_inputs T hT
  unfold MeasuredQuotient.Reverse.stepProgram MeasuredQuotient.Reverse.stepSegments
  refine (Patch.sequenceCons (d := hSaving T) (f := 1820) _ _ (hInversePatch n _ T) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 1820) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 105) (f := 1715) _ _ ?_ ?_).castSaving (by omega)
  · exact reverseFrontPatch n _
  refine (Patch.sequenceCons (d := 0) (f := 1715) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 1715) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 1715) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 70) (f := 1645) _ _ (entryBeforePatch n _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 98) (f := 1547) _ _ (dPatch n _ _) ?_).castSaving (by omega)
  exact reverseTailCrossPatch n _ _ _ _ hi.1 hi.2.2.1 hi.2.2.2
    (entryAfterPatch n _)
    (fun s => ((b1Patch n s).joinLiteral (aInversePatch n s)).castSaving (show 98 + 140 = 238 by omega))

end ReverseMeasuredArithmetic

/-- A literal-word patch transports to three consecutive literal segments. -/
def Patch.splitLiteralTriple {n start d : Nat} (a b c : Circuit) (tail : List (FixedSegment n))
    (hp : Patch (sequenceProgram n ((fun _ => ⟨0,literalProgram (a++b++c)⟩)::tail) start).2 d) :
    Patch (sequenceProgram n ((fun _ => ⟨0,literalProgram a⟩)::
      (fun _ => ⟨0,literalProgram b⟩)::(fun _ => ⟨0,literalProgram c⟩)::tail) start).2 d := by
  have hc : start+(sequenceProgram n ((fun _ => ⟨0,literalProgram (a++b++c)⟩)::tail) start).1 =
      start+(sequenceProgram n ((fun _ => ⟨0,literalProgram a⟩)::
        (fun _ => ⟨0,literalProgram b⟩)::(fun _ => ⟨0,literalProgram c⟩)::tail) start).1 := by
    simp only [sequenceProgram,Paper2607_13816.ChallengeMigration.appendCompiled,Nat.add_zero,Nat.zero_add]
  refine (hp.castFinish hc).congr ?_
  apply flat_inj
  rw [flat_castFinish]
  simp only [sequenceProgram,Paper2607_13816.ChallengeMigration.appendCompiled,flat_castFinish,flat_append,flat_literal,
    List.map_append,List.append_assoc,Nat.add_zero]
namespace ReverseMeasuredArithmetic700
private theorem literal_append {n s : Nat} (xs ys : Circuit) :
    (literalProgram (xs ++ ys) : Straight n s s) =
      (literalProgram xs).append (literalProgram ys) := by
  induction xs with
  | nil => simp only [List.nil_append,literalProgram,List.map_nil,gateProgram,Straight.append]
  | cons g xs ih =>
    simpa only [literalProgram,List.map_cons,gateProgram,Straight.append] using
      congrArg (Straight.gate (.literal g)) ih

private theorem surround_literal (n start : Nat) (before middle after : Circuit) :
    surroundCompiled before after (⟨0,literalProgram middle⟩ : (count : Nat) × Straight n start (start+count)) =
      ⟨0,literalProgram (before ++ middle ++ after)⟩ := by
  rw [List.append_assoc]
  simp only [surroundCompiled,prependCompiled,appendCompiled,Nat.add_zero,castFinish,literal_append]

private def w : ActiveWindow := (certifiedActiveWindows 256 1).quotientSwap
private def r : QuotientSwapRegisters := indexedStepProductionRegisters.quotient w
private theorem tree_leaf : quotientSwapTree r w.start w.stop = .leaf w.start := by decide +kernel

/-- The first quotient selector has no measured internal node. -/
theorem quotient_literal (n start : Nat) :
    MeasuredQuotient.program n start r w.start w.stop =
      ⟨0,literalProgram (quotientSwapUnitary r w.start w.stop)⟩ := by
  unfold MeasuredQuotient.program quotientSwapUnitary
  rw [tree_leaf]
  simp only [unaryProgram,unaryActionUnitary,surround_literal,List.append_assoc]

/-- The entire inverse quotient block at the first step is a literal compiler. -/
theorem inverse_block_literal (n start : Nat) :
    MeasuredQuotient.Reverse.program n start indexedStepProductionRegisters w =
      ⟨0,literalProgram (blockDInverse indexedStepProductionRegisters w)⟩ := by
  unfold MeasuredQuotient.Reverse.program MeasuredQuotient.d2Program
  have hq := quotient_literal n start
  dsimp only [r] at hq
  rw [hq]
  simp only [surround_literal,blockDInverse,MeasuredQuotient.Reverse.first,MeasuredQuotient.Reverse.last,
    MeasuredQuotient.before,MeasuredQuotient.after,List.append_assoc]
  rfl


attribute [local irreducible] MeasuredQuotient.Reverse.program MeasuredQuotient.Reverse.wrapperProgram
def reverseCrossStepOnePatch (n start : Nat) :
    Patch (MeasuredQuotient.Reverse.stepProgram n start indexedStepProductionRegisters 1).2 (2156+hSaving 1) := by
  let wr := (certifiedActiveWindows 256 1).remainder
  have hc : (indexedStepProductionRegisters.remainder wr).carry wr.start wr.stop ∈ List.range' 569 9 := by decide +kernel
  have hc' : (indexedStepProductionRegisters.remainder wr).carry wr.start wr.stop ∈ List.range' 568 10 := by
    simp only [List.mem_range'_1] at hc ⊢; omega
  have he : (indexedStepProductionRegisters.remainder wr).endpointScratch = List.range' 559 9 := by decide +kernel
  have hd (cursor : Nat) := inverse_block_literal n cursor
  dsimp only [w] at hd
  unfold MeasuredQuotient.Reverse.stepProgram MeasuredQuotient.Reverse.stepSegments
  refine (Patch.sequenceCons (d := hSaving 1) (f := 2156) _ _ (hInversePatch n _ 1) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 2156) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 105) (f := 2051) _ _ ?_ ?_).castSaving (by omega)
  · exact reverseFrontPatch n _
  refine (Patch.sequenceCons (d := 0) (f := 2051) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 2051) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 2051) _ _ (Patch.refl _) ?_).castSaving (by omega)
  rw [show (fun cursor => MeasuredQuotient.Reverse.program n cursor indexedStepProductionRegisters
      (certifiedActiveWindows 256 1).quotientSwap) =
    (fun _ => ⟨0,literalProgram (blockDInverse indexedStepProductionRegisters
      (certifiedActiveWindows 256 1).quotientSwap)⟩) from funext hd]
  apply Patch.splitLiteralTriple
  exact reverseTailCrossPatch n _ wr _ _ (endpoint_facts _ hc') (reverse_cross_facts _ hc) he
    (by simpa only [MeasuredQuotient.Reverse.entryBefore_view,MeasuredQuotient.Reverse.entryAfter_view,
      reverseCombinedSource,List.append_assoc] using Optimization.reverseCombinedOnePatch n _)
    (fun s => ((b1Patch n s).joinLiteral (aInversePatch n s)).castSaving (show 98+140=238 by omega))

def reverseStepPatchT (n start T : Nat) :
    Patch (MeasuredQuotient.Reverse.stepProgram n start indexedStepProductionRegisters T).2 (reverseStepSaving T) := by
  by_cases h : T = 1
  · subst T
    exact (reverseCrossStepOnePatch n start).castSaving (by simp [reverseStepSaving,hSaving])
  · by_cases ht : T < 1542
    · exact (ReverseMeasuredArithmetic.reverseCrossStepPatch n start T ht).castSaving (by simp [reverseStepSaving,h,ht])
    · exact (ReverseMeasuredArithmetic.reverseStepPatch n start T).castSaving (by simp [reverseStepSaving,h,ht])

def reverseSchedulePatch (n : Nat) : (count first start : Nat) →
    Patch (MeasuredQuotient.Reverse.scheduleProgram n indexedStepProductionRegisters count first start).2
      (reverseScheduleSaving count first)
  | 0, _, _ => Patch.refl _
  | count+1, first, start => by
    simp only [MeasuredQuotient.Reverse.scheduleProgram]
    exact (Patch.appendCompiled _ _ (reverseSchedulePatch n count (first+1) start)
      (reverseStepPatchT n _ first)).castSaving (by simp only [reverseScheduleSaving]; omega)

def eeaReversePatch (n start : Nat) :
    Patch (MeasuredQuotient.Reverse.reverseProgram n start indexedStepProductionRegisters).2 2970730 := by
  unfold MeasuredQuotient.Reverse.reverseProgram
  exact (reverseSchedulePatch n 1620 1 start).castSaving (by decide)

def reverseWrapperPatch (n start : Nat) :
    Patch (MeasuredQuotient.Reverse.wrapperProgram n start).2 3882865 := by
  unfold MeasuredQuotient.Reverse.wrapperProgram MeasuredQuotient.Reverse.wrapperSegments
  refine (Patch.sequenceCons (d := 0) (f := 3882865) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 3882865) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 3882865) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 2970730) (f := 912135) _ _ (eeaReversePatch n _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := 912135) (f := 0) _ _ (unpreprocessPatch n _) (Patch.refl _)).castSaving (by omega)

attribute [local irreducible] reverseWrapperPatch

def bankWrapperPatch (n start : Nat) :
    Patch (MeasuredQuotient.Reverse.bankWrapperProgram n start).2 3882865 := by
  unfold MeasuredQuotient.Reverse.bankWrapperProgram
  exact Patch.relabelCompiled eeaWorkspaceExchange _ (reverseWrapperPatch n start)

def divisionAfterResetPatch (n start : Nat) (prior : List (Fin start)) :
    Patch (MeasuredQuotient.Reverse.divisionAfterResetProgram n start prior).2 3882865 := by
  unfold MeasuredQuotient.Reverse.divisionAfterResetProgram appendRetaining
  exact (Patch.appendCompiled (d := 3882865) (f := 0) _ _
    ((Patch.appendCompiled (d := 3882865) (f := 0) _ _ (bankWrapperPatch n start) (Patch.refl _)).castSaving (by omega))
    (Patch.refl _)).castSaving (by omega)
end ReverseMeasuredArithmetic700

def divisionPatch (n start : Nat) : Patch (MeasuredQuotient.Reverse.divisionProgram n start).2 7772030 := by
  unfold MeasuredQuotient.Reverse.divisionProgram
  exact (Patch.appendCompiled (d := 3889165) (f := 3882865) _ _
    ((Patch.appendCompiled (d := 3889165) (f := 0) _ _ (MeasuredArithmetic.wrapperPatch n start) (Patch.refl _)).castSaving (by omega))
    (collectPatch _ (ReverseMeasuredArithmetic700.divisionAfterResetPatch n) _ _ _)).castSaving (by omega)

def multiplicationCleanupPatch (n start : Nat) :
    Patch (multiplicationCleanupProgram n start).2 3882865 := by
  unfold multiplicationCleanupProgram
  exact (Patch.appendCompiled (d := 0) (f := 3882865) _ _ (Patch.refl _)
    (Patch.appendLiteral _ _ (Optimization.reverseDataPatch n _))).castSaving (Nat.zero_add _)

def multiplicationCorrectionPatch (n start : Nat) (prior : List (Fin start)) :
    Patch (multiplicationCorrectionProgram n start prior).2 3882865 := by
  unfold multiplicationCorrectionProgram
  exact (Patch.appendCompiled (d := 0) (f := 3882865)
    (correctionCompiled n start (List.range' 580 256) prior) (multiplicationCleanupProgram n start)
    (Patch.refl _) (multiplicationCleanupPatch n start)).castSaving (show 0+3882865=3882865 by omega)

namespace MeasuredArithmetic
attribute [local irreducible] wrapperPatch

def bankWrapperPatch (n start : Nat) :
    Patch (MeasuredQuotient.bankWrapperProgram n start).2 3889165 := by
  unfold MeasuredQuotient.bankWrapperProgram
  exact Patch.relabelCompiled eeaWorkspaceExchange _ (wrapperPatch n start)

end MeasuredArithmetic

def multiplicationAfterResetPatch (n start : Nat) (prior : List (Fin start)) :
    Patch (MeasuredQuotient.multiplicationAfterResetProgram n start prior).2 7772030 := by
  unfold MeasuredQuotient.multiplicationAfterResetProgram appendRetaining
  exact (Patch.appendCompiled (d := 3889165) (f := 3882865) _ _
    ((Patch.appendCompiled (d := 3889165) (f := 0) _ _ (MeasuredArithmetic.bankWrapperPatch n _) (Patch.refl _)).castSaving (by omega))
    (multiplicationCorrectionPatch n _ _)).castSaving (by omega)

namespace ReverseMeasuredArithmetic700
attribute [local irreducible] MeasuredQuotient.Reverse.bankWrapperProgram MeasuredQuotient.bankWrapperProgram
def multiplicationCleanupPatch (n start : Nat) :
    Patch (MeasuredQuotient.Reverse.multiplicationCleanupProgram n start).2 3882865 := by
  unfold MeasuredQuotient.Reverse.multiplicationCleanupProgram
  exact (Patch.appendCompiled (d := 0) (f := 3882865) _ _ (Patch.refl _)
    (Patch.appendLiteral _ _ (bankWrapperPatch n _))).castSaving (Nat.zero_add _)

def multiplicationCorrectionPatch (n start : Nat) (prior : List (Fin start)) :
    Patch (MeasuredQuotient.Reverse.multiplicationCorrectionProgram n start prior).2 3882865 := by
  unfold MeasuredQuotient.Reverse.multiplicationCorrectionProgram
  exact (Patch.appendCompiled (d := 0) (f := 3882865)
    (correctionCompiled n start (List.range' 580 256) prior) (MeasuredQuotient.Reverse.multiplicationCleanupProgram n start)
    (Patch.refl _) (multiplicationCleanupPatch n start)).castSaving (show 0+3882865=3882865 by omega)

def multiplicationAfterResetPatch (n start : Nat) (prior : List (Fin start)) :
    Patch (MeasuredQuotient.Reverse.multiplicationAfterResetProgram n start prior).2 7772030 := by
  unfold MeasuredQuotient.Reverse.multiplicationAfterResetProgram appendRetaining
  exact (Patch.appendCompiled (d := 3889165) (f := 3882865) _ _
    ((Patch.appendCompiled (d := 3889165) (f := 0) _ _ (MeasuredArithmetic.bankWrapperPatch n _) (Patch.refl _)).castSaving (by omega))
    (multiplicationCorrectionPatch n _ _)).castSaving (by omega)

end ReverseMeasuredArithmetic700

def multiplicationPatch (n start : Nat) : Patch (MeasuredQuotient.Reverse.multiplicationProgram n start).2 7772030 := by
  unfold MeasuredQuotient.Reverse.multiplicationProgram
  exact (Patch.appendCompiled (d := 0) (f := 7772030) _ _ (Patch.refl _)
    (collectPatch _ (ReverseMeasuredArithmetic700.multiplicationAfterResetPatch n) _ _ _)).castSaving (by omega)



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
    Patch (ShorECDLP.Entrant.BorrowFlag.divisionProgram n start).2 7772030 := by
  unfold ShorECDLP.Entrant.BorrowFlag.divisionProgram
  exact borrowedFieldPatch n start (MeasuredQuotient.Reverse.divisionProgram n) (divisionPatch n)

def zeroMultiplicationPatch (n start : Nat) :
    Patch (ShorECDLP.Entrant.BorrowFlag.multiplicationProgram n start).2 7772030 := by
  unfold ShorECDLP.Entrant.BorrowFlag.multiplicationProgram
  exact borrowedFieldPatch n start (MeasuredQuotient.Reverse.multiplicationProgram n) (multiplicationPatch n)

def coordinatePatch (start : Nat) : Patch (ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateProgram start).2 15544060 := by
  unfold ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateProgram ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateSegments
  refine (Patch.sequenceCons (d := 0) (f := 15544060) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 15544060) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 7772030) (f := 7772030) _ _ (zeroDivisionPatch 32768 _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 7772030) _ _ (Patch.refl _) ?_).castSaving (by omega)
  refine (Patch.sequenceCons (d := 0) (f := 7772030) _ _ (Patch.refl _) ?_).castSaving (by omega)
  exact (Patch.sequenceCons (d := 7772030) (f := 0) _ _ (zeroMultiplicationPatch 32768 _) (Patch.refl _)).castSaving (by omega)

def corePatch (start : Nat) : Patch (Single.Physical.core start).2 15544060 := by
  unfold Single.Physical.core Single.Physical.segments
  exact (Patch.sequenceCons (d := 15544060) (f := 0) _ _ (coordinatePatch start) (Patch.refl _)).castSaving (by omega)

def preparedPatch (start : Nat) : Patch (Single.Physical.prepared start).2 15544060 := by
  unfold Single.Physical.prepared
  exact Patch.surroundCompiled _ _ _ (corePatch start)

def actualPatch (start : Nat) : Patch (Single.Physical.actual.program start) 15544060 := by
  unfold Single.Physical.actual closedWindow
  exact (((preparedPatch 0).relabel (windowAddressPerm 855 (by decide))).castFinish _).shift start

def signedPatch (w : Single.SignedWindow) (start : Nat) :
    Patch ((Single.signedWindow w).program start) 15544060 := by
  unfold Single.signedWindow
  exact (actualPatch start).reindex (Single.signedRow w)

def preparePatch {n s e d} (ws : List Wire) {p : Straight n s e} (hp : Patch p d) :
    Patch (prepareOuterBank ws p) d := by
  induction ws with
  | nil => exact hp
  | cons w ws ih => exact Patch.gate (.literal (.H w)) ih

structure PatchedWindow (n : Nat) where
  source : Single.Window n
  saving : Nat
  patch : ∀ start, Patch (source.program start) saving

def signedSaving : Single.SignedWindow → Nat
  | .left15 _ | .right15 _ => 18181884
  | _ => 15544060

def signedAliasPatch (w : Single.SignedWindow) (start : Nat) :
    Patch ((Single.signedWindow w).program start) (signedSaving w) := by
  cases w with
  | left16 j => exact signedPatch (.left16 j) start
  | left15 j => exact AliasLookup.left15AliasPatch (zeroDivisionPatch 32768) (zeroMultiplicationPatch 32768) j start
  | right15 j => exact AliasLookup.right15AliasPatch (zeroDivisionPatch 32768) (zeroMultiplicationPatch 32768) j start
  | right16 j => exact signedPatch (.right16 j) start

def leftPatches : List (PatchedWindow 901120) :=
  ⟨Single.firstWindow,0,fun _ => Patch.refl _⟩ ::
    Single.leftSigned.map (fun w => ⟨Single.signedWindow w,signedSaving w,signedAliasPatch w⟩)
def rightPatches : List (PatchedWindow 901120) :=
  Single.rightSigned.map (fun w => ⟨Single.signedWindow w,signedSaving w,signedAliasPatch w⟩)
private theorem leftPatches_source : leftPatches.map PatchedWindow.source = Single.leftWindows := by
  simp [leftPatches, Single.leftWindows]
private theorem rightPatches_source : rightPatches.map PatchedWindow.source = Single.rightWindows := by
  simp [rightPatches, Single.rightWindows]
private theorem leftPatches_saving : (leftPatches.map PatchedWindow.saving).sum = 275083200 := by
  simp [leftPatches, Single.leftSigned, signedSaving]
private theorem rightPatches_saving : (rightPatches.map PatchedWindow.saving).sum = 204710604 := by
  simp [rightPatches, Single.rightSigned, signedSaving]

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

def trialPatch (start : Nat) : Patch (Single.trial start) 479793804 := by
  have hl := (axisPatchFor leftPatches Single.leftWindows leftPatches_source start List.nil).castSaving leftPatches_saving
  have hr := (axisPatchFor rightPatches Single.rightWindows rightPatches_source
    (start+Single.axisCount Single.leftWindows) List.nil).castSaving rightPatches_saving
  unfold Single.trial
  exact (Patch.framed _ _ _ _ hl hr).castSaving (by decide)

def programPatch : Patch Single.program 479793804 := by
  unfold Single.program
  exact (trialPatch 0).castFinish _

def Patch.fixedEntry {n e d} (f : Fin n → PointCoeff) (p : Straight n 0 e) (hp : Patch p d) :
    Patch (Single.fixedEntry f p).program d := by
  unfold Single.fixedEntry
  exact hp.reindex _

def entryPatch : Patch Rounded.entry.program 479793804 := by
  unfold Rounded.entry Rounded.program
  exact Patch.fixedEntry Single.mixedCoefficientAt _
    ((Patch.append programPatch (Patch.refl Rounded.readout)).castSaving (by omega))
end
end ShorECDLP.Entrant.Optimization

namespace ShorECDLP.Entrant.Parent
open Challenge
noncomputable def entry : StraightEntry := Optimization.replaceEntry Rounded.entry Optimization.entryPatch.program
def layout : DecodeLayout := Rounded.layout
def bounds : Bounds := ⟨Rounded.bounds.qubits, Rounded.bounds.tModel - 479793804, Rounded.bounds.measurements⟩
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
  unfold multiplicationCleanupProgram
  exact (AtLeast.appendCompiled (d := 1110533) (f := 15772489) _ _ (unmultiplyDataCount n _)
    (AtLeast.appendLiteral _ _ (reverseBankCount n _))).castCount (by omega)

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
  unfold multiplicationCleanupProgram
  exact (AtLeast.appendCompiled (d := 1110533) (f := 15910015) _ _ (unmultiplyDataCount n _)
    (AtLeast.appendLiteral _ _ (reverseBankCompleteCount n _))).castCount (by omega)

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
    AtLeast (ShorECDLP.Entrant.BorrowFlag.divisionProgram n start).2 34668561 := by
  unfold ShorECDLP.Entrant.BorrowFlag.divisionProgram
  exact borrowedFieldCount n start 34668561 _ (FullCredit.ReverseMeasuredCredit.divisionCount n)

theorem borrowedMultiplicationCount (n start : Nat) :
    AtLeast (ShorECDLP.Entrant.BorrowFlag.multiplicationProgram n start).2 34668561 := by
  unfold ShorECDLP.Entrant.BorrowFlag.multiplicationProgram
  exact borrowedFieldCount n start 34668561 _ (FullCredit.ReverseMeasuredCredit.multiplicationCount n)

theorem borrowedCoordinateAllCount (start : Nat) : AtLeast (ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateProgram start).2 71165730 := by
  unfold ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateProgram ShorECDLP.Entrant.BorrowFlag.adaptiveCoordinateSegments
  refine (AtLeast.sequenceCons (d := 65534) (f := 71100196) _ _ (fieldAddCount _ _ _) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 65534) (f := 71034662) _ _ (signedFieldCount _ _) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 34668561) (f := 36366101) _ _ (borrowedDivisionCount _ _) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 1500938) (f := 34865163) _ _ (FullCredit.paddedSquareCount _ _) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 65534) (f := 34799629) _ _ (fieldAddCount _ _ _) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 34668561) (f := 131068) _ _ (borrowedMultiplicationCount _ _) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 0) (f := 131068) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 65534) (f := 65534) _ _ (fieldAddCount _ _ _) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 65534) (f := 0) _ _ (signedFieldCount _ _) ?_).castCount (by omega)
  exact AtLeast.zero _

theorem coreCount (start : Nat) : AtLeast (Single.Physical.core start).2 71591701 := by
  unfold Single.Physical.core Single.Physical.segments
  refine (AtLeast.sequenceCons (d := 71165730) (f := 425971) _ _ (borrowedCoordinateAllCount start) ?_).castCount (by omega)
  refine (AtLeast.sequenceCons (d := 0) (f := 425971) _ _ (AtLeast.zero _) ?_).castCount (by omega)
  exact (AtLeast.sequenceCons (d := 425971) (f := 0) _ _ (correctionQueryCount _) (AtLeast.zero _)).castCount (by omega)

theorem preparedCount (start : Nat) : AtLeast (Single.Physical.prepared start).2 71591701 := by
  unfold Single.Physical.prepared
  exact AtLeast.surroundCompiled _ _ _ (coreCount start)

theorem actualCount (start : Nat) : AtLeast (Single.Physical.actual.program start) 71591701 := by
  unfold Single.Physical.actual closedWindow
  exact (((preparedCount 0).relabel (windowAddressPerm 855 (by decide))).castFinish _).shift start

theorem signedCount (w : Single.SignedWindow) (start : Nat) :
    AtLeast ((Single.signedWindow w).program start) 71634364 :=
  FullCredit.signedFullCount w start

theorem prepareCount {n s e d} (ws : List Wire) {p : Straight n s e} (hp : AtLeast p d) :
    AtLeast (prepareOuterBank ws p) d := by
  induction ws with
  | nil => exact hp
  | cons w ws ih => exact AtLeast.gate (.literal (.H w)) ih

structure CountedWindow (n : Nat) where
  source : Single.Window n
  saving : Nat
  countProof : ∀ start, AtLeast (source.program start) saving

def leftCountes : List (CountedWindow 901120) :=
  ⟨Single.firstWindow,131071,FullCredit.firstFullCount⟩ ::
    Single.leftSigned.map (fun w => ⟨Single.signedWindow w,71634364,signedCount w⟩)
def rightCountes : List (CountedWindow 901120) :=
  Single.rightSigned.map (fun w => ⟨Single.signedWindow w,71634364,signedCount w⟩)
private theorem leftCountes_source : leftCountes.map CountedWindow.source = Single.leftWindows := by
  simp [leftCountes, Single.leftWindows]
private theorem rightCountes_source : rightCountes.map CountedWindow.source = Single.rightWindows := by
  simp [rightCountes, Single.rightWindows]
private theorem leftCountes_saving : (leftCountes.map CountedWindow.saving).sum = 1146280895 := by
  simp [leftCountes, Single.leftSigned]
private theorem rightCountes_saving : (rightCountes.map CountedWindow.saving).sum = 931246732 := by
  simp [rightCountes, Single.rightSigned]

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

theorem trialCount (start : Nat) : AtLeast (Single.trial start) 2077527627 := by
  have hl := (axisCountFor leftCountes Single.leftWindows leftCountes_source start List.nil).castCount leftCountes_saving
  have hr := (axisCountFor rightCountes Single.rightWindows rightCountes_source
    (start+Single.axisCount Single.leftWindows) List.nil).castCount rightCountes_saving
  unfold Single.trial
  exact (AtLeast.framed _ _ _ _ hl hr).castCount (by decide)

theorem programCount : AtLeast Single.program 2077527627 := by
  unfold Single.program
  exact (trialCount 0).castFinish _

theorem AtLeast.fixedEntry {n e d} (f : Fin n → PointCoeff) (p : Straight n 0 e) (hp : AtLeast p d) :
    AtLeast (Single.fixedEntry f p).program d := by
  unfold Single.fixedEntry
  exact hp.reindex _

theorem entryCount : AtLeast Rounded.entry.program 2077527627 := by
  unfold Rounded.entry Rounded.program
  apply AtLeast.fixedEntry
  exact ((AtLeast.append programCount (AtLeast.zero Rounded.readout)).castCount (by omega))

theorem ccxCount_eea (gs : Circuit) : ccxCount gs = eeaToffoliCount gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => cases g <;> simp_all [ccxCount,eeaToffoliCount,Nat.add_comm]

theorem dropped_added {n s e d} {p q : Straight n s e} (h : Optimization.Drops p q d) :
    7 * added p ≤ 7 * added q + d := by
  induction h with
  | replaceLiteral xs ys k hb h ih =>
    simp only [Optimization.literalPrefix,added_append,added_literal,ccxCount_eea]
    have hc := hb.eligible
    omega
  | refl => omega
  | skip g h ih => cases g <;> simp_all [added, tCost] <;> omega
  | gate g h ih =>
    cases g with
    | literal g => cases g <;> simp_all [added] <;> omega
    | whenBit => exact ih
  | skipRecord => assumption
  | record => assumption
  | measure => assumption

attribute [local irreducible] added lower lowerEntry lowerLayout Optimization.entryPatch



theorem parent_added_lower : 2008985655 ≤ added Parent.entry.program := by
  have h := dropped_added Optimization.entryPatch.drops
  have hc := entryCount
  change 2077527627 ≤ added Rounded.entry.program at hc
  unfold Parent.entry Optimization.replaceEntry
  change 2008985655 ≤ added Optimization.entryPatch.program
  omega
theorem within_reindex {n m s e} (p : Straight n s e) (f : Fin n → Fin m) (ws : List Wire)
    (hp : Within ws p) : Within ws (reindexStraight f p) := by
  induction p with
  | done => trivial
  | gate g p ih => cases g <;> exact ⟨hp.1, ih hp.2⟩
  | recordGate => exact ⟨hp.1, by apply_assumption; exact hp.2⟩
  | measure => exact ⟨hp.1, by apply_assumption; exact hp.2⟩


theorem within_drops {n s e d} {p q : Straight n s e} (h : Optimization.Drops p q d)
    (ws : List Wire) (hp : Within ws p) : Within ws q := by
  apply within_of_instantiate q ws
  intro read history w hw
  exact hp.instantiate read history (h.wires read history w hw)


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

theorem parent_added_upper : added Parent.entry.program ≤ 7347416100 := by
  have h := lower_t 1024 Parent.entry.program 0 Fin.elim0
    (readConstant Parent.entry.coefficients.get 0) Fin.elim0 Fin.elim0
    (by funext i; exact Fin.elim0 i)
  have ht := (Parent.certificate.resources 0).2.1
  change (Parent.entry.program.instantiate (readConstant Parent.entry.coefficients.get 0) Fin.elim0).tCount ≤ 14062955359 at ht
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
def bounds : Bounds := ⟨855, 10044984049, 8266128294⟩

private theorem resourceArithmetic (a slots cursor oldT newT maxSlots maxRecords newRecords : Nat)
    (ha : a ≤ 7347416100) (hl : 2008985655 ≤ a) (hs : slots ≤ 90000176648)
    (hc : cursor ≤ 918695052) (ho : oldT ≤ 14062955359) (hn : 10044984049 ≤ newT)
    (hls : 4000000000000000 ≤ maxSlots) (hlm : 47471340504 ≤ maxRecords)
    (hnm : 8266128294 ≤ newRecords) :
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
namespace ShorECDLP.Entrant
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

private theorem saved_bound (a b s : Nat) (he : s = a+b) (hl : 2008985655 ≤ a) :
    2008985655 ≤ s := by omega

private theorem five_saved : 2008985655 ≤ Catalyst.saved Five.entry.program :=
  saved_bound (added Parent.entry.program) (Catalyst.saved Parent.entry.program)
    (Catalyst.saved Five.entry.program) (lowerEntry_saved 1024 Parent.entry) parent_added_lower

private theorem slots_bound (old new a : Nat) (he : new = old + 18*a)
    (hs : old ≤ 90000176648) (ha : a ≤ 7347416100) : new ≤ 230352365419 := by omega

private theorem five_slots : Five.entry.program.gateSlots ≤ 230352365419 :=
  slots_bound Parent.entry.program.gateSlots Five.entry.program.gateSlots
    (added Parent.entry.program) (lowerEntry_slots 1024 Parent.entry) parent_slots parent_added_upper

noncomputable def entry : StraightEntry := Catalyst.compileEntry 1025 Five.entry
noncomputable def layout : DecodeLayout := Five.layout
def bounds : Bounds := ⟨856, 8035998395, 8266128294⟩

private theorem resourceArithmetic (s a c oldT newT maxSlots m : Nat)
    (hs : s ≤ 230352365419) (ha : a ≤ s) (hl : 2008985655 ≤ a)
    (hc : c ≤ 8266128294) (ho : oldT ≤ 10044984049) (hn : 8035998395 ≤ newT)
    (hls : 4000000000000000 ≤ maxSlots) (hm : 8266128294 ≤ m) :
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
end ShorECDLP.Entrant
end
end
