import ShorECDLP.Submission.Entrant.RootWindows
namespace ShorECDLP.Entrant.NarrowRoot
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration RootPass ConstRoot
open AndGadget WEXCredit ConditionalCatalyst MeasuredClear WEX WEXUnlookup PathShare
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 500000
attribute [local irreducible] readOnlyProgram
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
theorem clearP7_readOnly {n} (B : PathShare.Bank) (hB : PathShare.BankOK B)
    (site : WEXUnlookup.MaskedSite n) (hk : WEXUnlookup.SiteKind site)
    (hp : windowRoot∉B.paths) (ht : windowRoot∉portTargets site.ports) (start : Nat) :
    readOnlyProgram windowRoot (PathShare.clearP B site start) := by
  rw [PathShare.clearP]
  apply measuredClear7_readOnly windowRoot _ _ _ _ _ _ _ _
  · intro i
    simp only [WEXUnlookup.low,windowRoot]
    dsimp only [Wire] at *
    omega
  · intro i he
    exact ht (he ▸ (WEXUnlookup.kind_facts site hk).2.2.2.1 i)
  · intro he
    have hm := (WEXUnlookup.kind_facts site hk).2.2.2.2.1
    have hb := (WEXUnlookup.kind_facts site hk).2.1 _ hm
    rw [he] at hb
    dsimp only [windowRoot,Wire] at hb
    omega
  · intro w hw he
    have hh : w∈B.high := by rw [←hB.index]; exact List.mem_dedup.mpr hw
    have hb := hB.high w hh
    dsimp only [windowRoot,Wire] at *
    omega
  · intro w hw he
    exact hp (he ▸ hB.sub w hw)
  · intro p hm he
    apply ht
    rw [←WEXUnlookup.clearData_targets]
    exact List.mem_map.mpr ⟨p,hm,he⟩

theorem blockProg7_readOnly {n} (B : PathShare.Bank) (hB : PathShare.BankOK B)
    (hb : windowRoot∉B.bits) (hp : windowRoot∉B.paths) (hn : B.bits.Nodup)
    (b : WEXUnlookup.Block2 n) (hg : PathShare.BlockGeoP2 B b) (start : Nat) :
    readOnlyProgram windowRoot (PathShare.blockProgP2 B b start) := by
  cases b with
  | plain code =>
    exact compile_readOnly B.bits B.paths windowRoot (normalizeW code) hb hp hn
      (codeReadOnly_normalize windowRoot code (codeReadOnly_litAvoid B.bits code hg)) start
  | unit u =>
    have hall : codeReadOnly windowRoot u.code := codeReadOnly_placed _ _ _ _ hg.placed
    have hpre : codeReadOnly windowRoot u.pre := codeReadOnly_subset _ _ _ (List.subset_append_left _ _) hall
    have ht : windowRoot∉portTargets u.clear.ports :=
      hall (.lookup (some u.clear.guard) u.clear.ports) (by simp [WEXUnlookup.UnitSite.code])
    rw [PathShare.blockProgP2,readOnlyProgram_cast,readOnlyProgram_append]
    exact ⟨compile_readOnly B.bits B.paths windowRoot _ hb hp hn
      (codeReadOnly_normalize _ _ hpre) start,clearP7_readOnly B hB u.clear hg.site.kind hp ht _⟩

theorem programP7_readOnly {n} (B : PathShare.Bank) (hB : PathShare.BankOK B)
    (hb : windowRoot∉B.bits) (hp : windowRoot∉B.paths) (hn : B.bits.Nodup)
    (code : WEXUnlookup.Code2 n) (hg : ∀ b∈code,PathShare.BlockGeoP2 B b) (start : Nat) :
    readOnlyProgram windowRoot (PathShare.programP2 B code start) := by
  induction code generalizing start with
  | nil => simp [PathShare.programP2,ConstRoot.readOnlyProgram]
  | cons b code ih =>
    rw [PathShare.programP2,readOnlyProgram_cast,readOnlyProgram_append]
    exact ⟨blockProg7_readOnly B hB hb hp hn b (hg b (by simp)) start,
      ih (fun x hx => hg x (by simp [hx])) _⟩


open WEXFast


namespace Narrow_three
variable {n : Nat} (f : WEXFast.FastSite n) (hg : WEXFast.FastGeometry f)
include hg

theorem regs_noRoot : windowRoot∉portTargets f.site.ports++f.garb := by
  intro h
  have hb := (FastSite.facts f hg).2.2.2.2.2.2 windowRoot h
  dsimp only [windowRoot,Wire] at hb
  omega

theorem sel_readOnly (start : Nat) : readOnlyProgram windowRoot (f.selProgram start) := by
  rw [FastSite.selProgram]
  apply compile_readOnly selBits selPaths windowRoot f.selCode (by decide) (by decide) (by decide) _ start
  apply codeReadOnly_placed
  intro i hi
  simp only [FastSite.selCode,List.mem_singleton] at hi
  subst i
  exact placed_implies_pair _ _ _ _ (FastSite.sel_placed f hg)

theorem swap_readOnly (start : Nat) : readOnlyProgram windowRoot (f.swapProgram start) := by
  rw [FastSite.swapProgram]
  apply literalFixed_readOnly
  intro h
  have hm := List.mem_toFinset.mp (FastSite.swapNet_wires f h)
  have hn : windowRoot∉855 :: 856 :: portTargets f.site.ports++f.garb := by
    simpa [windowRoot] using regs_noRoot f hg
  exact hn hm

theorem arith_readOnly (start : Nat) : readOnlyProgram windowRoot (f.arithProgram start) := by
  rw [FastSite.arithProgram]
  exact compile_readOnly windowBits pathBank windowRoot _ (by decide) (by decide) (by decide)
    (codeReadOnly_normalize _ _ (codeReadOnly_placed _ _ _ _ (FastSite.arith_pair f hg))) start

theorem gclear_readOnly (start : Nat) : readOnlyProgram windowRoot (f.gclearProgram start) := by
  rw [FastSite.gclearProgram]
  apply measuredClear7_readOnly windowRoot _ _ _ _ _ _ _ _
  · intro i
    simp only [WEXUnlookup.low,windowRoot]
    dsimp only [Wire] at *
    omega
  · intro i he
    have hb := FastSite.hot_bound f hg i
    rw [he] at hb
    dsimp only [windowRoot,Wire] at hb
    omega
  · intro he
    have hb := FastSite.scratch_bound f hg
    rw [he] at hb
    dsimp only [windowRoot,Wire] at hb
    omega
  · intro w hw he
    subst w
    have hm : windowRoot∈high := by
      rw [←tableAddressTree_index high 0 1 (by decide)]
      exact List.mem_dedup.mpr hw
    exact (by decide : windowRoot∉high) hm
  · intro w hw he
    exact (by decide : windowRoot∉bankHp) (he ▸ hw)
  · intro p hp he
    have hm : windowRoot∈portTargets f.garbPorts := by
      rw [←WEXUnlookup.clearData_targets]
      exact List.mem_map.mpr ⟨p,hp,he⟩
    rw [FastSite.garbPorts_targets f hg] at hm
    have hb := hg.bounds windowRoot hm
    dsimp only [windowRoot,Wire] at hb
    omega

theorem fast_readOnly (start : Nat) : readOnlyProgram windowRoot (f.fastProgram start) := by
  have ht : windowRoot∉portTargets f.site.ports := fun h => regs_noRoot f hg (List.mem_append_left _ h)
  rw [FastSite.fastProgram,readOnlyProgram_cast]
  simp only [readOnlyProgram_append]
  exact ⟨⟨⟨⟨sel_readOnly f hg start,swap_readOnly f hg _⟩,gclear_readOnly f hg _⟩,
    arith_readOnly f hg _⟩,clearP7_readOnly PathShare.bank15 PathShare.bank15_ok f.site hg.site.kind (by decide) ht _⟩

end Narrow_three

namespace Narrow_one
variable {n : Nat} (f : WEXFast.FastSite1 n) (hg : WEXFast.FastGeometry1 f)
include hg

theorem regs_noRoot : windowRoot∉portTargets f.site.ports++f.garb := by
  intro h
  have hb := (FastSite1.facts f hg).2.2.2.2.2.2 windowRoot h
  dsimp only [windowRoot,Wire] at hb
  omega

theorem sel_readOnly (start : Nat) : readOnlyProgram windowRoot (f.selProgram start) := by
  rw [FastSite1.selProgram]
  apply compile_readOnly selBits1 selPaths1 windowRoot f.selCode (by decide) (by decide) (by decide) _ start
  apply codeReadOnly_placed
  intro i hi
  simp only [FastSite1.selCode,List.mem_singleton] at hi
  subst i
  exact placed_implies_pair _ _ _ _ (FastSite1.sel_placed f hg)

theorem swap_readOnly (start : Nat) : readOnlyProgram windowRoot (f.swapProgram start) := by
  rw [FastSite1.swapProgram]
  apply literalFixed_readOnly
  intro h
  have hm := List.mem_toFinset.mp (FastSite1.swapNet_wires f h)
  have hn : windowRoot∉855 :: portTargets f.site.ports++f.garb := by
    simpa [windowRoot] using regs_noRoot f hg
  exact hn hm

theorem arith_readOnly (start : Nat) : readOnlyProgram windowRoot (f.arithProgram start) := by
  rw [FastSite1.arithProgram]
  exact compile_readOnly windowBits pathBank windowRoot _ (by decide) (by decide) (by decide)
    (codeReadOnly_normalize _ _ (codeReadOnly_placed _ _ _ _ (FastSite1.arith_pair f hg))) start

theorem gclear_readOnly (start : Nat) : readOnlyProgram windowRoot (f.gclearProgram start) := by
  rw [FastSite1.gclearProgram]
  apply measuredClear7_readOnly windowRoot _ _ _ _ _ _ _ _
  · intro i
    simp only [WEXUnlookup.low,windowRoot]
    dsimp only [Wire] at *
    omega
  · intro i he
    have hb := FastSite1.hot_bound f hg i
    rw [he] at hb
    dsimp only [windowRoot,Wire] at hb
    omega
  · intro he
    have hb := FastSite1.scratch_bound f hg
    rw [he] at hb
    dsimp only [windowRoot,Wire] at hb
    omega
  · intro w hw he
    subst w
    have hm : windowRoot∈high := by
      rw [←tableAddressTree_index high 0 1 (by decide)]
      exact List.mem_dedup.mpr hw
    exact (by decide : windowRoot∉high) hm
  · intro w hw he
    exact (by decide : windowRoot∉bankHp) (he ▸ hw)
  · intro p hp he
    have hm : windowRoot∈portTargets f.garbPorts := by
      rw [←WEXUnlookup.clearData_targets]
      exact List.mem_map.mpr ⟨p,hp,he⟩
    rw [FastSite1.garbPorts_targets f hg] at hm
    have hb := hg.bounds windowRoot hm
    dsimp only [windowRoot,Wire] at hb
    omega

theorem fast_readOnly (start : Nat) : readOnlyProgram windowRoot (f.fastProgram start) := by
  have ht : windowRoot∉portTargets f.site.ports := fun h => regs_noRoot f hg (List.mem_append_left _ h)
  rw [FastSite1.fastProgram,readOnlyProgram_cast]
  simp only [readOnlyProgram_append]
  exact ⟨⟨⟨⟨sel_readOnly f hg start,swap_readOnly f hg _⟩,gclear_readOnly f hg _⟩,
    arith_readOnly f hg _⟩,clearP7_readOnly PathShare.bank15 PathShare.bank15_ok f.site hg.site.kind (by decide) ht _⟩

end Narrow_one


open WEXFast
namespace SeedNarrow
open WEXFast

def chosen {n} : FBlock2 n → Bool
  | .std (.plain _) => false
  | _ => true

def closedBlock {n} (b : FBlock2 n) : Straight n 0 (0+fblockRec b) :=
  if chosen b then RootPass.seedProgram windowRoot (fblockProg b 0) else fblockProg b 0

def blockSource {n} (read : ConstantBit n→Bool) (b : FBlock2 n) : AdaptiveCircuit :=
  (closedBlock b).instantiate read Fin.elim0

theorem chosen_readOnly {n} (b : FBlock2 n) (hg : FBlockGeo b) (hc : chosen b=true) (start : Nat) :
    readOnlyProgram windowRoot (fblockProg b start) := by
  cases b with
  | std b =>
    cases b with
    | plain code => simp [chosen] at hc
    | unit u => exact blockProg7_readOnly PathShare.bank15 PathShare.bank15_ok (by decide) (by decide) (by decide) (.unit u) hg start
  | fast f => exact Narrow_three.fast_readOnly f hg start
  | fast1 f => exact Narrow_one.fast_readOnly f hg start


theorem block_sim {n} (read : ConstantBit n→Bool) (b : FBlock2 n) (hg : FBlockGeo b) :
    ∃ cs : List ℂ,List.Forall₂ (FBlockSim read b) (blockSource read b).run cs ∧
      (cs.map Complex.normSq).sum=1 := by
  obtain ⟨cs,ha,hm⟩ := fblock_sim read b hg
  refine ⟨cs,?_,hm⟩
  unfold blockSource closedBlock
  by_cases hc : chosen b=true
  · rw [if_pos hc,RootPass.seedProgram_instantiate]
    have hsafe := RootPass.safeProgram_instantiate windowRoot (fblockProg b 0) read Fin.elim0
      (readOnlyProgram_safe windowRoot _ (chosen_readOnly b hg hc 0))
    have he := RootPass.adaptive_relation windowRoot ((fblockProg b 0).instantiate read Fin.elim0) hsafe
    rw [fblockProg_run] at he
    apply aligned_pull he ha
    intro bnew bold c he hb
    obtain ⟨m,hlen,hb⟩ := hb
    refine ⟨m,hlen,?_⟩
    intro a st hs hclean hsafe
    rw [he (Bridge.signedKet st) (by
      unfold Bridge.signedKet
      apply supported_smul
      exact supportedOn_ket _ _ hs.2)]
    exact hb a st hs hclean hsafe
  · rw [if_neg hc,fblockProg_run]
    exact ha


def blockProgram {n} (b : FBlock2 n) (start : Nat) : Straight n start (start+fblockRec b) :=
  castFinish (by omega) (Bridge.shiftStraight start (closedBlock b))

def program {n} : (code : FCode2 n) → (start : Nat) → Straight n start (start+frecs code)
  | [],_ => .done
  | b::code,start => castFinish (by simp [frecs]; omega)
      ((blockProgram b start).append (program code (start+fblockRec b)))

def source {n} (read : ConstantBit n→Bool) : FCode2 n→AdaptiveCircuit
  | [] => .done
  | b::code => (blockSource read b).seq (source read code)

theorem blockProgram_run {n} (read : ConstantBit n→Bool) (b : FBlock2 n) (start : Nat)
    (hist : Fin start→Bool) : ((blockProgram b start).instantiate read hist).run=(blockSource read b).run := by
  rw [blockProgram,castFinish_instantiate,Bridge.shiftStraight_closed]
  rfl

theorem program_run {n} (read : ConstantBit n→Bool) (code : FCode2 n) (start : Nat)
    (hist : Fin start→Bool) : ((program code start).instantiate read hist).run=(source read code).run := by
  induction code generalizing start with
  | nil => rfl
  | cons b code ih =>
    rw [program,castFinish_instantiate,append_run_fixed _ _ _ _ _ (ih _),
      AdaptiveCircuit.run_seq,blockProgram_run]
    simp only [source,AdaptiveCircuit.run_seq]
theorem source_sim {n} (read : ConstantBit n → Bool) (code : FCode2 n) (hg : ∀ b ∈ code, FBlockGeo b) :
    ∃ cs : List ℂ, List.Forall₂ (FSim read code) (source read code).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  induction code with
  | nil =>
    refine ⟨[1], .cons ?_ .nil, by simp⟩
    exact ⟨[], rfl, fun a st _ _ _ => by
      simp [reference2, erase2, fforget, specialize, ECDSAAdd.ShorPort.Tmpl.instantiate, ECDSAAdd.run]⟩
  | cons b code ih =>
    obtain ⟨cs₁, h₁, mass₁⟩ := block_sim read b (hg b (by simp))
    obtain ⟨cs₂, h₂, mass₂⟩ := ih (fun c hc => hg c (by simp [hc]))
    refine ⟨coherentSeqCoefficients cs₁ cs₂, ?_, ?_⟩
    · rw [source, AdaptiveCircuit.run_seq]
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
        have hn := fblock_addr read b (hg b (by simp)) a st hs hc.1 m₁
        change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
        rw [run₁ a st hs hc.1 hsafe.1, map_smul,
          run₂ a (ECDSAAdd.run (blockReference2 read a b.forget) m₁ st) hn (hc.2 m₁ hm) (hsafe.2 m₁ hm),
          reference2_cons, run_append_records _ _ m₁ m₂ st hm]
        simp [smul_smul]
    · rw [simulationCoefficients_mass, mass₁, mass₂]
      norm_num

theorem program_coherent {n} (read : ConstantBit n → Bool) (code : FCode2 n) (hg : ∀ b ∈ code, FBlockGeo b)
    (Valid : BasisState → Prop) (result : BasisState → BasisState)
    (hsafe : ∀ s, Valid s → Safe2 read (tableAddressValue windowBits s) (fforget code) ⟨false,s⟩)
    (hclean : ∀ s, Valid s → FCodeClean read (tableAddressValue windowBits s) code ⟨false,s⟩)
    (hrun : ∀ s, Valid s → ∀ m,
      ECDSAAdd.run (reference2 read (tableAddressValue windowBits s) (fforget code)) m ⟨false,s⟩ = ⟨false,result s⟩)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((program code start).instantiate read history)
      (Finsupp.lmapDomain ℂ ℂ result) (fun s => s windowRoot = true ∧ Valid s) := by
  obtain ⟨cs, aligned, mass⟩ := source_sim read code hg
  refine ⟨cs, ?_, mass⟩
  rw [program_run]
  apply aligned.imp
  intro b c hb s hs
  obtain ⟨m, _, h⟩ := hb
  have he := h (tableAddressValue windowBits s) ⟨false,s⟩ ⟨rfl, hs.1⟩ (hclean s hs.2) (hsafe s hs.2)
  rw [Bridge.signedKet_false, hrun s hs.2 m, Bridge.signedKet_false] at he
  simpa [ket] using he



theorem old_block_credit {n} (b : FBlock2 n) (hg : FBlockGeo b) (start : Nat) :
    ProgramCredit (fblockProg b start) (fblockTP b) := by
  have hz : residue (fblockProg b start)=0 := by
    cases b with
    | std b => exact PathShare.blockH_residue PathShare.bank15 b start
    | fast f => exact f.fast_residue start
    | fast1 f => exact f.fast_residue start
  refine ⟨hz,?_⟩
  have ht := fblock_tCount (fun _=>false) b hg start (fun _=>false)
  have he := exact_t (fblockProg b start) hz (fun _=>false) (fun _=>false)
  omega

def savings {n} (b : FBlock2 n) : Nat :=
  if chosen b then RootPass.literalHits windowRoot (fblockProg b 0) else 0

def blockCredit {n} (b : FBlock2 n) : Nat := fblockTP b-savings b

theorem closed_credit {n} (b : FBlock2 n) (hg : FBlockGeo b) : ProgramCredit (closedBlock b) (blockCredit b) := by
  unfold closedBlock blockCredit savings
  split
  · exact RootPass.seedProgram_credit windowRoot _ _ (old_block_credit b hg 0)
  · simpa using old_block_credit b hg 0

theorem shift_added {n s e} (p : Straight n s e) (offset : Nat) :
    added (Bridge.shiftStraight offset p)=added p := by
  induction p with
  | done => rfl
  | gate g p ih =>
    cases g with
    | literal g => cases g <;> simp_all [Bridge.shiftStraight,added]
    | whenBit => exact ih
  | recordGate i v g p ih => exact ih
  | measure w p ih => exact ih

theorem shift_residue {n s e} (p : Straight n s e) (offset : Nat) :
    residue (Bridge.shiftStraight offset p)=residue p := by
  induction p with
  | done => rfl
  | gate g p ih => cases g <;> simp_all [Bridge.shiftStraight,residue]
  | recordGate i v g p ih => simp_all [Bridge.shiftStraight,residue]
  | measure w p ih => exact ih


theorem blockProgram_credit {n} (b : FBlock2 n) (hg : FBlockGeo b) (start : Nat) :
    ProgramCredit (blockProgram b start) (blockCredit b) := by
  rw [blockProgram]
  apply credit_cast
  have hc := closed_credit b hg
  exact ⟨by rw [shift_residue]; exact hc.1,by rw [shift_added]; exact hc.2⟩

def creditSum {n} : FCode2 n→Nat
  | [] => 0
  | b::code => blockCredit b+creditSum code

def savedSum {n} : FCode2 n→Nat
  | [] => 0
  | b::code => savings b+savedSum code

theorem savings_le {n} (b : FBlock2 n) (hg : FBlockGeo b) : savings b≤fblockTP b := by
  unfold savings
  split
  · have h := RootPass.seedProgram_added windowRoot (fblockProg b 0)
    rw [(old_block_credit b hg 0).2] at h
    omega
  · omega

theorem credit_balance {n} (code : FCode2 n) (hg : ∀ b∈code,FBlockGeo b) :
    creditSum code+savedSum code=fcodeTP code := by
  induction code with
  | nil => rfl
  | cons b code ih =>
    have hb := savings_le b (hg b (by simp))
    have ht := ih (fun c hc=>hg c (by simp [hc]))
    simp only [creditSum,savedSum,fcodeTP,blockCredit]
    omega

theorem program_credit {n} (code : FCode2 n) (hg : ∀ b∈code,FBlockGeo b) (start : Nat) :
    ProgramCredit (program code start) (creditSum code) := by
  induction code generalizing start with
  | nil => exact ⟨rfl,rfl⟩
  | cons b code ih =>
    rw [program]
    apply credit_cast
    have hb := blockProgram_credit b (hg b (by simp)) start
    have ht := ih (fun c hc=>hg c (by simp [hc])) (start+fblockRec b)
    exact ⟨by rw [residue_append,hb.1,ht.1],by rw [added_append,hb.2,ht.2]; rfl⟩

theorem blockProgram_wellFormed {n} (b : FBlock2 n) (hg : FBlockGeo b)
    (hp : ∀ p,WInstr.literal p∈b.forget.code→ECDSAAdd.Arithmetic.GatePhysical p) (start : Nat) :
    (blockProgram b start).WellFormed := by
  rw [blockProgram,castFinish_wellFormed]
  apply Bridge.shiftStraight_wellFormed
  have hb := fblock_wellFormed b hg hp 0
  unfold closedBlock
  split
  · exact RootPass.seedProgram_wellFormed windowRoot _ hb
  · exact hb

theorem program_wellFormed {n} (code : FCode2 n) (hg : ∀ b∈code,FBlockGeo b)
    (hp : ∀ p,WInstr.literal p∈erase2 (fforget code)→ECDSAAdd.Arithmetic.GatePhysical p) (start : Nat) :
    (program code start).WellFormed := by
  induction code generalizing start with
  | nil => trivial
  | cons b code ih =>
    rw [program,castFinish_wellFormed]
    apply straight_append_wellFormed
    · exact blockProgram_wellFormed b (hg b (by simp)) (fun p hm=>hp p (by simp [erase2_cons,hm])) start
    · exact ih (fun c hc=>hg c (by simp [hc])) (fun p hm=>hp p (by simp [erase2_cons,hm])) _

theorem blockProgram_slots {n} (b : FBlock2 n) (start : Nat) :
    (blockProgram b start).gateSlots=(fblockProg b 0).gateSlots := by
  rw [blockProgram,castFinish_gateSlots,Bridge.shiftStraight_gateSlots]
  unfold closedBlock
  split
  · exact RootPass.seedProgram_slots windowRoot _
  · rfl
theorem program_slots {n} (code : FCode2 n) (hg : ∀ b ∈ code, FBlockGeo b) (start : Nat) :
    (program code start).gateSlots ≤ PathShare.codeSP2 PathShare.bank15 (fforget code) + fslack code := by
  induction code generalizing start with
  | nil => simp [program, frecs, fslack, Straight.gateSlots, PathShare.codeSP2]
  | cons b code ih =>
    have ih' := ih (fun d hd => hg d (by simp [hd])) (start + fblockRec b)
    have hb : (blockProgram b start).gateSlots ≤ PathShare.blockSP2 PathShare.bank15 b.forget + fblockSlack b := by
      rw [blockProgram_slots]
      have hgb := hg b (by simp)
      cases b with
      | std b =>
        rw [show fblockProg (.std b) 0 = PathShare.blockProgH PathShare.bank15 b 0 from rfl]
        exact PathShare.blockH_slots PathShare.bank15 b (PathShare.geo_lay2 PathShare.bank15 PathShare.bank15_ok b hgb) 0
      | fast f => exact f.fast_slots hgb 0
      | fast1 f => exact f.fast_slots hgb 0
    rw [program, castFinish_gateSlots, Straight.gateSlots_append]
    simp only [fforget_cons, PathShare.codeSP2, fslack]
    omega




theorem shift_wires {n s e} (p : Straight n s e) (offset : Nat) :
    ChallengeMigration.straightWires (Bridge.shiftStraight offset p)=ChallengeMigration.straightWires p := by
  rw [RootPass.straightWires_eq_naive,Bridge.shiftStraight_straightWires]
  exact (RootPass.straightWires_eq_naive p).symm

theorem blockProgram_support {n} (b : FBlock2 n) (start : Nat) :
    ChallengeMigration.straightWires (blockProgram b start) ⊆ ChallengeMigration.straightWires (fblockProg b 0) := by
  rw [blockProgram,straightWires_castFinish,shift_wires]
  unfold closedBlock
  split
  · exact RootPass.seedProgram_wires windowRoot _
  · exact List.Subset.refl _


theorem fixup7_hits {n base} (known : Wire) (data : List (ClearPort n)) (refs : List (Fin base))
    (low : Fin 7 → Wire) (hot : Fin 128 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire)
    (hl : ∀ i,low i≠known) (hh : ∀ i,hot i≠known) :
    literalHits known (MeasuredClear.fixupProgram data refs low hot tree root scratch paths)=
      recordOpsHits known (recordUnaryOps tree root paths) := by
  obtain ⟨hn,hprep,_⟩ := fixup7_noRoot_parts (n:=n) known low hot hl hh
  have hz (start : Nat) : literalHits known (literalProgram (n:=n) (s:=start) (MeasuredClear.hotPrepare low hot))=0 :=
    literalHits_zero_of_not_mem known _ (literalProgram_noRoot known _ _ hprep hn)
  simp only [MeasuredClear.fixupProgram,literalHits_append,literalHits_cast,literalHits_recordLookupProgram,
    literalHits_hadamards,literalHits_adjoint_hadamards,literalHits_eraseNetwork,literalHits_X,hz,
    zero_add,add_zero]

theorem measured7_hits {n} (known : Wire) (data : List (ClearPort n))
    (low : Fin 7 → Wire) (hot : Fin 128 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire) (start : Nat)
    (hl : ∀ i,low i≠known) (hh : ∀ i,hot i≠known) :
    literalHits known (MeasuredClear.measuredClear data low hot tree root scratch paths start)=
      recordOpsHits known (recordUnaryOps tree root paths) := by
  rw [MeasuredClear.measuredClear,literalHits_cast]
  apply literalHits_measureThen
  intro cursor refs
  rw [literalHits_cast]
  exact fixup7_hits known data refs low hot tree root scratch paths hl hh



theorem record_root_hit_lower (root bit path : Wire) (zero one : UnaryActionTree) (rest : List Wire) :
    1≤RootPass.recordOpsHits root (recordUnaryOps (.node bit zero one) root (path::rest)) := by
  simp only [recordUnaryOps,RootPass.recordOpsHits,List.map_append,List.sum_append,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,RootPass.recordOpHits,
    computeZeroAnd,RootPass.hit,true_or,if_true]
  omega

theorem clearP_root_hit {n} (site : MaskedSite n) (hk : SiteKind site)
    (he : site.guard=windowRoot) (ht : windowRoot∉portTargets site.ports) (start : Nat) :
    1≤literalHits windowRoot (PathShare.clearP PathShare.bank15 site start) := by
  rw [PathShare.clearP,measured7_hits windowRoot _ _ _ _ _ _ _ _]
  · rw [he]
    exact record_root_hit_lower windowRoot 862 14832 _ _ _
  · intro i
    simp only [WEXUnlookup.low,windowRoot]
    dsimp only [Wire] at *
    omega
  · intro i he
    exact ht (he ▸ (WEXUnlookup.kind_facts site hk).2.2.2.1 i)


theorem unit_root_hits {n} (u : UnitSite n) (hg : UnitGeoP PathShare.bank15 u)
    (he : u.clear.guard=windowRoot) (start : Nat) :
    1≤literalHits windowRoot (fblockProg (.std (.unit u)) start) := by
  have hall := codeReadOnly_placed windowBits pathBank windowRoot u.code hg.placed
  have ht : windowRoot∉portTargets u.clear.ports :=
    hall (.lookup (some u.clear.guard) u.clear.ports) (by simp [UnitSite.code])
  have hc := clearP_root_hit u.clear hg.site.kind he ht (start+codeRecords PathShare.bank15.bits PathShare.bank15.paths windowRoot (normalizeW u.pre))
  change 1≤literalHits windowRoot (PathShare.blockProgP2 PathShare.bank15 (.unit u) start)
  rw [PathShare.blockProgP2,literalHits_cast,literalHits_append]
  omega

theorem gclear_three_root_hits {n} (f : WEXFast.FastSite n) (hg : WEXFast.FastGeometry f)
    (he : f.site.guard=windowRoot) (start : Nat) :
    1≤literalHits windowRoot (f.gclearProgram start) := by
  rw [FastSite.gclearProgram,measured7_hits windowRoot _ _ _ _ _ _ _ _]
  · rw [he]
    exact record_root_hit_lower windowRoot 862 14832 _ _ _
  · intro i
    simp only [WEXUnlookup.low,windowRoot]
    dsimp only [Wire] at *
    omega
  · intro i he
    have hb := FastSite.hot_bound f hg i
    rw [he] at hb
    dsimp only [windowRoot,Wire] at hb
    omega

theorem fast_three_root_hits {n} (f : WEXFast.FastSite n) (hg : WEXFast.FastGeometry f)
    (he : f.site.guard=windowRoot) (start : Nat) :
    2≤literalHits windowRoot (f.fastProgram start) := by
  have ht : windowRoot∉portTargets f.site.ports :=
    fun h=>Narrow_three.regs_noRoot f hg (List.mem_append_left _ h)
  rw [FastSite.fastProgram,literalHits_cast]
  simp only [literalHits_append]
  have hG := gclear_three_root_hits f hg he (start+codeRecords WEXFast.selBits WEXFast.selPaths windowRoot f.selCode+0)
  have hC := clearP_root_hit f.site hg.site.kind he ht (start+codeRecords WEXFast.selBits WEXFast.selPaths windowRoot f.selCode+0+(clearData f.garbPorts).length+(recordMeasurements (recordUnaryOps (tableAddressTree WEXUnlookup.high 0 1) f.site.guard WEXFast.bankHp)+127)+codeRecords windowBits pathBank windowRoot (normalizeW f.site.arithmetic))
  omega

theorem gclear_one_root_hits {n} (f : WEXFast.FastSite1 n) (hg : WEXFast.FastGeometry1 f)
    (he : f.site.guard=windowRoot) (start : Nat) :
    1≤literalHits windowRoot (f.gclearProgram start) := by
  rw [FastSite1.gclearProgram,measured7_hits windowRoot _ _ _ _ _ _ _ _]
  · rw [he]
    exact record_root_hit_lower windowRoot 862 14832 _ _ _
  · intro i
    simp only [WEXUnlookup.low,windowRoot]
    dsimp only [Wire] at *
    omega
  · intro i he
    have hb := FastSite1.hot_bound f hg i
    rw [he] at hb
    dsimp only [windowRoot,Wire] at hb
    omega

theorem fast_one_root_hits {n} (f : WEXFast.FastSite1 n) (hg : WEXFast.FastGeometry1 f)
    (he : f.site.guard=windowRoot) (start : Nat) :
    2≤literalHits windowRoot (f.fastProgram start) := by
  have ht : windowRoot∉portTargets f.site.ports :=
    fun h=>Narrow_one.regs_noRoot f hg (List.mem_append_left _ h)
  rw [FastSite1.fastProgram,literalHits_cast]
  simp only [literalHits_append]
  have hG := gclear_one_root_hits f hg he (start+codeRecords WEXFast.selBits1 WEXFast.selPaths1 windowRoot f.selCode+0)
  have hC := clearP_root_hit f.site hg.site.kind he ht (start+codeRecords WEXFast.selBits1 WEXFast.selPaths1 windowRoot f.selCode+0+(clearData f.garbPorts).length+(recordMeasurements (recordUnaryOps (tableAddressTree WEXUnlookup.high 0 1) f.site.guard WEXFast.bankHp)+127)+codeRecords windowBits pathBank windowRoot (normalizeW f.site.arithmetic))
  omega


def floor {n} : FBlock2 n→Nat
  | .std (.plain _) => 0
  | .std (.unit u) => if u.clear.guard=windowRoot then 1 else 0
  | .fast f => if f.site.guard=windowRoot then 2 else 0
  | .fast1 f => if f.site.guard=windowRoot then 2 else 0

def floorSum {n} : FCode2 n→Nat
  | [] => 0
  | b::code => floor b+floorSum code

theorem floor_le_savings {n} (b : FBlock2 n) (hg : FBlockGeo b) : floor b≤savings b := by
  cases b with
  | std b =>
    cases b with
    | plain code => exact Nat.zero_le _
    | unit u =>
      by_cases h : u.clear.guard=windowRoot
      · simpa only [floor,savings,chosen,h,if_true] using unit_root_hits u hg h 0
      · simp [floor,h]
  | fast f =>
    by_cases h : f.site.guard=windowRoot
    · simpa only [floor,savings,chosen,h,if_true] using fast_three_root_hits f hg h 0
    · simp [floor,h]
  | fast1 f =>
    by_cases h : f.site.guard=windowRoot
    · simpa only [floor,savings,chosen,h,if_true] using fast_one_root_hits f hg h 0
    · simp [floor,h]

theorem floorSum_lower {n} (code : FCode2 n) (hg : ∀ b∈code,FBlockGeo b) :
    floorSum code≤savedSum code := by
  induction code with
  | nil => exact le_rfl
  | cons b code ih =>
    exact Nat.add_le_add (floor_le_savings b (hg b (by simp))) (ih (fun c hc=>hg c (by simp [hc])))


theorem unary_root_hit_lower {n} (root bit path : Wire) (leaf : Nat→Wire→List (TemplateGate n))
    (zero one : UnaryActionTree) (rest : List Wire) :
    1≤opsHits root (unaryLookupOps leaf (.node bit zero one) root (path::rest)) := by
  simp only [unaryLookupOps,opsHits,List.map_append,List.sum_append,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,opHits,ordinaryOp,computeZeroAnd,List.map_map,templateHits,hit,true_or,if_true]
  omega

theorem port_root_hit_lower {n} (root : Wire) (bits paths : List Wire)
    (hb : bits≠[]) (hp : paths≠[]) (ps : List (LookupPort n)) :
    1≤opsHits root (portOps ps bits paths root) := by
  cases bits with
  | nil => contradiction
  | cons bit bits =>
    cases paths with
    | nil => contradiction
    | cons path paths => exact unary_root_hit_lower root bit path _ _ _ paths

def lookupCount {n} (root : Wire) : WCode n→Nat
  | [] => 0
  | .literal _::code => lookupCount root code
  | .lookup ctl _::code => (if lookupRoot root ctl=root then 1 else 0)+lookupCount root code

theorem lookupCount_normalize {n} (root : Wire) (code : WCode n) :
    lookupCount root (normalizeW code)=lookupCount root code := by
  induction code with
  | nil => rfl
  | cons i code ih => cases i <;> simpa [normalizeW,normalizeWInstr,lookupCount] using ih

theorem hits_naiveCast {n a b c} (root : Wire) (p : Straight n a b) (h : b=c) :
    literalHits root (NaiveChallenge.castFinish h p)=literalHits root p := by subst c; rfl

theorem compile_lookup_lower {n} (root : Wire) (bits paths : List Wire)
    (hb : bits≠[]) (hp : paths≠[]) (code : WCode n) (start : Nat) :
    lookupCount root code≤literalHits root (WEX.compile bits paths root code start) := by
  induction code generalizing start with
  | nil => exact le_rfl
  | cons i code ih =>
    cases i with
    | literal p =>
      rw [WEX.compile,hits_naiveCast,literalHits_append]
      have ht := ih (start+Bridge.tmplMeas (literalT (n:=n) p))
      simp only [lookupCount]
      omega
    | lookup ctl ps =>
      rw [WEX.compile,hits_naiveCast,literalHits_append,literalHits_lookupProgram]
      have ht := ih (start+lookupMeasurements (portOps ps bits paths (lookupRoot root ctl)))
      have hh : (if lookupRoot root ctl=root then 1 else 0)≤opsHits root (portOps ps bits paths (lookupRoot root ctl)) := by
        by_cases h : lookupRoot root ctl=root
        · rw [if_pos h,h]
          exact port_root_hit_lower root bits paths hb hp ps
        · rw [if_neg h]
          exact Nat.zero_le _
      simp only [lookupCount]
      omega


theorem unit_lookup_floor {n} (u : UnitSite n) (hg : UnitGeoP PathShare.bank15 u) (start : Nat) :
    lookupCount windowRoot u.pre+(if u.clear.guard=windowRoot then 1 else 0)≤
      literalHits windowRoot (fblockProg (.std (.unit u)) start) := by
  have hall := codeReadOnly_placed windowBits pathBank windowRoot u.code hg.placed
  have ht : windowRoot∉portTargets u.clear.ports :=
    hall (.lookup (some u.clear.guard) u.clear.ports) (by simp [UnitSite.code])
  have hp := compile_lookup_lower windowRoot PathShare.bank15.bits PathShare.bank15.paths
    (by decide) (by decide) (normalizeW u.pre) start
  rw [lookupCount_normalize] at hp
  have hc : (if u.clear.guard=windowRoot then 1 else 0)≤literalHits windowRoot
      (PathShare.clearP PathShare.bank15 u.clear
        (start+codeRecords PathShare.bank15.bits PathShare.bank15.paths windowRoot (normalizeW u.pre))) := by
    by_cases h : u.clear.guard=windowRoot
    · rw [if_pos h]
      exact clearP_root_hit u.clear hg.site.kind h ht _
    · rw [if_neg h]
      exact Nat.zero_le _
  change _≤literalHits windowRoot (PathShare.blockProgP2 PathShare.bank15 (.unit u) start)
  rw [PathShare.blockProgP2,literalHits_cast,literalHits_append]
  exact Nat.add_le_add hp hc

theorem fast_three_lookup_floor {n} (f : WEXFast.FastSite n) (hg : WEXFast.FastGeometry f) (start : Nat) :
    lookupCount windowRoot f.selCode+lookupCount windowRoot f.site.arithmetic+
      (if f.site.guard=windowRoot then 2 else 0)≤literalHits windowRoot (f.fastProgram start) := by
  have hS : lookupCount windowRoot f.selCode≤literalHits windowRoot (f.selProgram start) := by
    rw [FastSite.selProgram]
    exact compile_lookup_lower windowRoot WEXFast.selBits WEXFast.selPaths (by decide) (by decide) _ start
  have hA (j : Nat) : lookupCount windowRoot f.site.arithmetic≤literalHits windowRoot (f.arithProgram j) := by
    rw [FastSite.arithProgram]
    have h := compile_lookup_lower windowRoot windowBits pathBank
      (by decide) (by decide) (normalizeW f.site.arithmetic) j
    simpa only [lookupCount_normalize] using h
  have hAr := hA (start+codeRecords WEXFast.selBits WEXFast.selPaths windowRoot f.selCode+0+(clearData f.garbPorts).length+(recordMeasurements (recordUnaryOps (tableAddressTree WEXUnlookup.high 0 1) f.site.guard WEXFast.bankHp)+127))
  rw [FastSite.fastProgram,literalHits_cast]
  simp only [literalHits_append]
  by_cases h : f.site.guard=windowRoot
  · rw [if_pos h]
    have ht : windowRoot∉portTargets f.site.ports :=
      fun hm=>Narrow_three.regs_noRoot f hg (List.mem_append_left _ hm)
    have hG := gclear_three_root_hits f hg h (start+codeRecords WEXFast.selBits WEXFast.selPaths windowRoot f.selCode+0)
    have hC := clearP_root_hit f.site hg.site.kind h ht (start+codeRecords WEXFast.selBits WEXFast.selPaths windowRoot f.selCode+0+(clearData f.garbPorts).length+(recordMeasurements (recordUnaryOps (tableAddressTree WEXUnlookup.high 0 1) f.site.guard WEXFast.bankHp)+127)+codeRecords windowBits pathBank windowRoot (normalizeW f.site.arithmetic))
    omega
  · rw [if_neg h]
    omega

theorem fast_one_lookup_floor {n} (f : WEXFast.FastSite1 n) (hg : WEXFast.FastGeometry1 f) (start : Nat) :
    lookupCount windowRoot f.selCode+lookupCount windowRoot f.site.arithmetic+
      (if f.site.guard=windowRoot then 2 else 0)≤literalHits windowRoot (f.fastProgram start) := by
  have hS : lookupCount windowRoot f.selCode≤literalHits windowRoot (f.selProgram start) := by
    rw [FastSite1.selProgram]
    exact compile_lookup_lower windowRoot WEXFast.selBits1 WEXFast.selPaths1 (by decide) (by decide) _ start
  have hA (j : Nat) : lookupCount windowRoot f.site.arithmetic≤literalHits windowRoot (f.arithProgram j) := by
    rw [FastSite1.arithProgram]
    have h := compile_lookup_lower windowRoot windowBits pathBank
      (by decide) (by decide) (normalizeW f.site.arithmetic) j
    simpa only [lookupCount_normalize] using h
  have hAr := hA (start+codeRecords WEXFast.selBits1 WEXFast.selPaths1 windowRoot f.selCode+0+(clearData f.garbPorts).length+(recordMeasurements (recordUnaryOps (tableAddressTree WEXUnlookup.high 0 1) f.site.guard WEXFast.bankHp)+127))
  rw [FastSite1.fastProgram,literalHits_cast]
  simp only [literalHits_append]
  by_cases h : f.site.guard=windowRoot
  · rw [if_pos h]
    have ht : windowRoot∉portTargets f.site.ports :=
      fun hm=>Narrow_one.regs_noRoot f hg (List.mem_append_left _ hm)
    have hG := gclear_one_root_hits f hg h (start+codeRecords WEXFast.selBits1 WEXFast.selPaths1 windowRoot f.selCode+0)
    have hC := clearP_root_hit f.site hg.site.kind h ht (start+codeRecords WEXFast.selBits1 WEXFast.selPaths1 windowRoot f.selCode+0+(clearData f.garbPorts).length+(recordMeasurements (recordUnaryOps (tableAddressTree WEXUnlookup.high 0 1) f.site.guard WEXFast.bankHp)+127)+codeRecords windowBits pathBank windowRoot (normalizeW f.site.arithmetic))
    omega
  · rw [if_neg h]
    omega

def richFloor {n} : FBlock2 n→Nat
  | .std (.plain _) => 0
  | .std (.unit u) => lookupCount windowRoot u.pre+(if u.clear.guard=windowRoot then 1 else 0)
  | .fast f => lookupCount windowRoot f.selCode+lookupCount windowRoot f.site.arithmetic+(if f.site.guard=windowRoot then 2 else 0)
  | .fast1 f => lookupCount windowRoot f.selCode+lookupCount windowRoot f.site.arithmetic+(if f.site.guard=windowRoot then 2 else 0)

def richFloorSum {n} : FCode2 n→Nat
  | [] => 0
  | b::code => richFloor b+richFloorSum code

theorem richFloor_le_savings {n} (b : FBlock2 n) (hg : FBlockGeo b) : richFloor b≤savings b := by
  cases b with
  | std b =>
    cases b with
    | plain code => exact Nat.zero_le _
    | unit u => simpa only [richFloor,savings,chosen,if_true] using unit_lookup_floor u hg 0
  | fast f => simpa only [richFloor,savings,chosen,if_true] using fast_three_lookup_floor f hg 0
  | fast1 f => simpa only [richFloor,savings,chosen,if_true] using fast_one_lookup_floor f hg 0

theorem richFloorSum_lower {n} (code : FCode2 n) (hg : ∀ b∈code,FBlockGeo b) :
    richFloorSum code≤savedSum code := by
  induction code with
  | nil => exact le_rfl
  | cons b code ih =>
    exact Nat.add_le_add (richFloor_le_savings b (hg b (by simp))) (ih (fun c hc=>hg c (by simp [hc])))


theorem richFloor_concrete : richFloorSum WEXFast.rowCF=8 := by decide


theorem program_support (code : FCode2 32768) (hg : ∀ b ∈ code, FBlockGeo b)
    (hlit : ∀ p, WInstr.literal p ∈ erase2 (fforget code) → ∀ w ∈ ECDSAAdd.wires p,
      w = hostWire ∨ w = hostWire2 ∨ w = hostWire3 ∨ w ∈ newSourceH)
    (hstrict : ∀ b ∈ code, ∀ p, WInstr.literal p ∈ b.forget.code →
      (hostWire ∈ ECDSAAdd.wires p ∨ hostWire2 ∈ ECDSAAdd.wires p ∨ hostWire3 ∈ ECDSAAdd.wires p) →
      ∃ c, b = .std (.plain c))
    (hctl : ∀ b ∈ code, ∀ c, b = .std (.plain c) →
      hostWire2 ∈ ECDSAAdd.wires (litProg c) → hostCtl ∉ ECDSAAdd.wires (litProg c))
    (hctl3 : ∀ b ∈ code, ∀ c, b = .std (.plain c) →
      hostWire3 ∈ ECDSAAdd.wires (litProg c) → hostCtl3 ∉ ECDSAAdd.wires (litProg c))
    (hlook : ∀ c ps, WInstr.lookup c ps ∈ erase2 (fforget code) →
      (∀ q ∈ c, q ∈ newSourceH) ∧ portTargets ps ⊆ newSourceH)
    (hgarb : ∀ b ∈ code, FNoHost b)
    (start : Nat) : ChallengeMigration.straightWires (program code start) ⊆ newSourceH := by
  induction code generalizing start with
  | nil => simp [program, frecs, ChallengeMigration.straightWires]
  | cons b code ih =>
    rw [program, support_cast, straightWires_append]
    exact List.append_subset.mpr ⟨(blockProgram_support b start).trans (fblock_support b (hg b (by simp))
      (fun p hm => hlit p (by simp [erase2_cons, hm])) (hstrict b (by simp)) (hctl b (by simp)) (hctl3 b (by simp))
      (fun c ps hm => hlook c ps (by simp [erase2_cons, hm])) (hgarb b (by simp)) 0),
      ih (fun d hd => hg d (by simp [hd])) (fun p hm => hlit p (by simp [erase2_cons, hm]))
        (fun d hd => hstrict d (by simp [hd])) (fun d hd => hctl d (by simp [hd])) (fun d hd => hctl3 d (by simp [hd]))
        (fun c ps hm => hlook c ps (by simp [erase2_cons, hm])) (fun d hd => hgarb d (by simp [hd])) _⟩



open WEXFast.W15F
local notation "rowCredit" => creditSum WEXFast.rowCF
attribute [local irreducible] WEXFast.rowCF WEXUnlookup.rowC Nat.add Nat.mul

def addFixedCF (start : Nat) : Straight 32768 start (start+1653524) :=
  castFinish (congrArg (fun m=>start+m) WEXFast.W15F.rowCF_records) (program WEXFast.rowCF start)

theorem addFixedCF_run (read : ConstantBit 32768→Bool) (start : Nat) (history : Fin start→Bool) :
    ((addFixedCF start).instantiate read history).run=(source read WEXFast.rowCF).run := by
  rw [addFixedCF,castFinish_instantiate,program_run]

theorem addFixedCF_credit (start : Nat) : ProgramCredit (addFixedCF start) rowCredit := by
  rw [addFixedCF]
  exact credit_cast _ (program_credit WEXFast.rowCF WEXFast.rowCF_geo start)

theorem addFixedCF_slots (start : Nat) : (addFixedCF start).gateSlots≤
    codeSlots windowBits (normalizeW (erase2 WEXUnlookup.rowC))+418411946 := by
  rw [addFixedCF,castFinish_gateSlots]
  have h:=program_slots WEXFast.rowCF WEXFast.rowCF_geo start
  rw [WEXFast.fforget_rowCF,WEXFast.W15F.rowC_slotsP start,WEXFast.W15F.rowCF_slack] at h
  exact WEXFast.W15F.slots_arith _ _ h

theorem addFixedCF_wellFormed (start : Nat) : (addFixedCF start).WellFormed := by
  rw [addFixedCF,castFinish_wellFormed]
  apply program_wellFormed _ WEXFast.rowCF_geo
  rw [WEXFast.fforget_rowCF]
  exact WEXUnlookup.rowC_physical

theorem addFixedCF_support (start : Nat) : ChallengeMigration.straightWires (addFixedCF start)⊆newSourceH := by
  rw [addFixedCF,support_cast]
  exact program_support WEXFast.rowCF WEXFast.rowCF_geo (by rw [WEXFast.fforget_rowCF];exact rowC_lit_relaxed)
    WEXFast.W15F.rowCF_strict WEXFast.W15F.rowCF_ctl WEXFast.W15F.rowCF_ctl3
    (by rw [WEXFast.fforget_rowCF];exact rowC_look_newH) WEXFast.W15F.rowCF_nohost start

def rowSourceCF (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  source (readConstant coeffs Q) rowCF

theorem rowSourceCF_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) :
    CoherentlyImplementsOn (rowSourceCF coeffs Q) (Finsupp.lmapDomain ℂ ℂ (rowPointState coeffs Q)) LiveReady := by
  have h := program_coherent (readConstant coeffs Q) rowCF rowCF_geo liveReady (rowPointState coeffs Q)
    (fun s hs => by rw [fforget_rowCF]; exact (WEXUnlookup.rowC_safe_run coeffs Q hQ hn _ s hs).1)
    (fun s hs => rowCF_clean coeffs Q hQ hn _ s hs)
    (fun s hs m => by rw [fforget_rowCF]; exact WEXUnlookup.rowC_run_any _ coeffs Q hQ hn s hs m) 0 Fin.elim0
  obtain ⟨cs, aligned, mass⟩ := h
  refine ⟨cs, ?_, mass⟩
  rw [program_run] at aligned
  exact aligned.imp (fun b c hb s hs => hb s ⟨hs.1.2.2, hs.1⟩)

def fastMiddleSource (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  (fastSignSource.seq (rowSourceCF coeffs Q)).seq fastSignSource

theorem fastMiddle_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) :
    CoherentlyImplementsOn (fastMiddleSource coeffs Q) (Finsupp.lmapDomain ℂ ℂ (middleState coeffs Q)) LiveReady := by
  have first := composeCoherent fastSign_coherent (rowSourceCF_coherent coeffs Q hQ hn)
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

def fastBodyProgram (start : Nat) : Straight 32768 start (start+1654036) :=
  castFinish (by omega)
    (((((prefixProgram start).append (nFastProgram start)).append (addFixedCF (start+256))).append
      (nFastProgram (start+256+1653524))).append (suffixProgram (start+256+1653524+256)))

attribute [local irreducible] fastBodyProgram addFixedCF

theorem fastBodyProgram_run (start : Nat) (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (history : Fin start → Bool) :
    ((fastBodyProgram start).instantiate (readConstant coeffs Q) history).run = (fastBodySource coeffs Q).run := by
  have hr : ((fastBodyProgram start).instantiate (readConstant coeffs Q) history).run =
      ((prefixSource.seq ((fastSignSource.seq (source (readConstant coeffs Q) rowCF)).seq
        fastSignSource)).seq suffixSource).run := by
    rw [fastBodyProgram, castFinish_instantiate]
    exact five_run (readConstant coeffs Q) _ _ _ _ _ prefixSource fastSignSource
      (source (readConstant coeffs Q) rowCF) fastSignSource suffixSource
      (prefixProgram_run _ _) (nFastProgram_run _ _) (addFixedCF_run _ _)
      (nFastProgram_run _ _) (suffixProgram_run _ _) history
  have he : fastBodySource coeffs Q =
      ((prefixSource.seq ((fastSignSource.seq (source (readConstant coeffs Q) rowCF)).seq
        fastSignSource)).seq suffixSource) := by
    delta fastBodySource fastMiddleSource rowSourceCF
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
      rowCredit) := by
  let a := ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)
  have hl : ProgramCredit (nFastProgram start) a := WEX.nFastProgram_credit start
  have hr : ProgramCredit (nFastProgram (start+256+1653524)) a := WEX.nFastProgram_credit _
  rw [fastBodyProgram]
  apply credit_cast
  exact five_credit a (rowCredit) (prefix_credit start) hl (addFixedCF_credit (start+256)) hr
    (suffix_credit (start+256+1653524+256))

theorem fastBodyProgram_tCount (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((fastBodyProgram start).instantiate read history).tCount =
      7*(2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) +
        rowCredit) := by
  have hc := fastBodyProgram_credit start
  have h := exact_t (fastBodyProgram start) hc.1 read history
  rw [hc.2] at h
  exact h

attribute [local irreducible] Straight.WellFormed WEX.nFastProgram

theorem fastBodyProgram_wellFormed (start : Nat) : (fastBodyProgram start).WellFormed := by
  rw [fastBodyProgram, castFinish_wellFormed]
  apply straight_append_wellFormed
  · apply straight_append_wellFormed
    · apply straight_append_wellFormed
      · exact straight_append_wellFormed _ _ (prefixProgram_wellFormed start) (nFastProgram_wellFormed start)
      · exact addFixedCF_wellFormed _
    · exact nFastProgram_wellFormed _
  · exact suffixProgram_wellFormed _

theorem fastBodyProgram_support (start : Nat) :
    ChallengeMigration.straightWires (fastBodyProgram start) ⊆ newSourceH := by
  have hp : ChallengeMigration.straightWires (prefixProgram start) ⊆ newSourceH := by
    rw [prefixProgram, straightWires_append, literalProgram_support, literalProgram_support]
    apply newSourceH_of_bounds
    decide +kernel
  have hs (j : Nat) : ChallengeMigration.straightWires (suffixProgram j) ⊆ newSourceH := by
    rw [suffixProgram, straightWires_append, literalProgram_support, literalProgram_support]
    apply newSourceH_of_bounds
    decide +kernel
  rw [fastBodyProgram, support_cast]
  simp only [straightWires_append, List.append_subset]
  exact ⟨⟨⟨⟨hp, nFast_newH _⟩, addFixedCF_support _⟩, nFast_newH _⟩, hs _⟩

/-- The arithmetic of the body slot bound over plain variables; the row hypotheses are passed unchanged
(a defeq-only `simp` change of their types would be re-checked by the kernel on the whole row program). -/
theorem body_slot_arith (S A G C L L0 P P0 W T : Nat) (sign : S ≤ 3 * G) (bound : G ≤ 100000)
    (ha : A ≤ C + 418411946) (hc : C ≤ 3 * L + 2 ^ W * P + 10 * T * (2 ^ W - 1)) (hW : W = 15) (hT : T = 9)
    (hl2 : L ≤ L0 + 93082 + 513) (hl : L0 ≤ 50021565) (hp2 : P ≤ P0 + 3) (hp : P0 ≤ 20000) :
    0 + 1 + 30 + S + A + S + (30 + (0 + 1)) ≤ 2000000000 := by
  subst hW hT
  rw [show (2 : Nat) ^ 15 = 32768 from rfl, show 10 * 9 * (32768 - 1) = 2949030 from rfl] at hc
  omega

attribute [local irreducible] WEX.literalSlotSum WEX.portTotal WEX.traversals in
theorem fastBodyProgram_slots_upper (start : Nat) : (fastBodyProgram start).gateSlots ≤ 2000000000 := by
  rw [fastBodyProgram, castFinish_gateSlots]
  simp only [Straight.gateSlots_append, nFastProgram_slots, prefixProgram, suffixProgram, literalProgram_slots]
  have ha := addFixedCF_slots (start+256)
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
  generalize codeSlots windowBits (normalizeW (erase2 WEXUnlookup.rowC)) = C at hc ha
  generalize (addFixedCF (start + 256)).gateSlots = A at ha ⊢
  generalize ECDSAAdd.Challenge.gateSlots fastWindowSignProgram = G at sign bound
  generalize Bridge.tmplSlots (literalT (n := 32768) (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)) = S
    at sign ⊢
  exact body_slot_arith S A G C _ _ _ _ windowBits.length _ sign bound ha hc rfl hm.2.1 hm.2.2.1 hl hm.2.2.2.1 hp

def compactProgram (start : Nat) : Straight 32768 start (start+1654036) :=
  relabelStraight piH (fastBodyProgram start)


theorem credit_bound : 2*ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram)+rowCredit≤2253182 := by
  have ho:=WEXFast.W15F.fastCount_upper
  have hb:=credit_balance WEXFast.rowCF WEXFast.rowCF_geo
  have hs:=richFloorSum_lower WEXFast.rowCF WEXFast.rowCF_geo
  rw [richFloor_concrete] at hs
  omega


def narrowCF15 : Schedule33.Flexible.ModNarrow PathShare.bodyCF 15 where
  records := 1654036
  tBound := 15772274
  credit := 2*ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram)+rowCredit
  program := compactProgram
  coherent := fun coeffs Q hQ hn _ start history =>
    PathShare.relabelH_coherent _ coeffs Q history (fastBodyProgram_coherent coeffs Q hQ hn start history)
  wellFormed := fun start => (relabelStraight_wellFormed piH (fastBodyProgram start)).mpr
    (fastBodyProgram_wellFormed start)
  slots := fun start => (relabelStraight_slots piH (fastBodyProgram start)).trans_le
    (fastBodyProgram_slots_upper start)
  wires := fun start => PathShare.relabelH_support _ (fastBodyProgram_support start)
  tCount := by
    intro start read history
    rw [compactProgram,relabelStraight_instantiate,AdaptiveCircuit.relabel_tCount,fastBodyProgram_tCount]
    have h:=credit_bound
    omega
  zero := by
    intro start
    rw [compactProgram,WEXUnlookup.residue_relabel]
    exact (fastBodyProgram_credit start).1
  count_eq := by
    intro start
    rw [compactProgram,AndGadget.added_relabel]
    exact (fastBodyProgram_credit start).2


end SeedNarrow
end
end ShorECDLP.Entrant.NarrowRoot
