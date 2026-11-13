import ShorECDLP.Submission.Entrant.KnownRoot
import ShorECDLP.Submission.Entrant.First18Loader
set_option Elab.async false
namespace ShorECDLP.Entrant.RootPass
open Quantum Challenge AndGadget Paper2607_13816 Paper2607_13816.ChallengeMigration
noncomputable section
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

theorem supported_add (P : BasisState → Prop) (a b : State) (ha : SupportedOn P a) (hb : SupportedOn P b) :
    SupportedOn P (a+b) := by
  intro s hs
  by_cases h : a s = 0
  · apply hb s
    simpa [Finsupp.add_apply,h] using hs
  · exact ha s h

theorem supported_smul (P : BasisState → Prop) (c : ℂ) (a : State) (ha : SupportedOn P a) :
    SupportedOn P (c • a) := by
  intro s hs
  apply ha s
  intro h
  exact hs (by simp [h])

theorem linear_on_supported (P : BasisState → Prop) (f g : State →ₗ[ℂ] State)
    (h : ∀ s,P s → f (ket s)=g (ket s)) (psi : State) (hp : SupportedOn P psi) : f psi=g psi := by
  induction psi using Finsupp.induction with
  | zero => simp
  | single_add s c psi hs hc ih =>
    have hzero : psi s=0 := by simpa using hs
    have hsP : P s := by apply hp s; simp [hzero,hc]
    have hpP : SupportedOn P psi := by
      intro u hu
      apply hp u
      by_cases he : u=s
      · subst u; exact (hu hzero).elim
      · simp [he,hu]
    have hsingle : Finsupp.single s c=c • ket s := by ext u; simp [ket]
    rw [map_add,map_add,hsingle,map_smul,map_smul,h s hsP,ih hpP]

theorem linear_preserves_supported (P : BasisState → Prop) (f : State →ₗ[ℂ] State)
    (h : ∀ s,P s → SupportedOn P (f (ket s))) (psi : State) (hp : SupportedOn P psi) : SupportedOn P (f psi) := by
  induction psi using Finsupp.induction with
  | zero => simpa only [map_zero] using supportedOn_zero P
  | single_add s c psi hs hc ih =>
    have hzero : psi s=0 := by simpa using hs
    have hsP : P s := by apply hp s; simp [hzero,hc]
    have hpP : SupportedOn P psi := by
      intro u hu
      apply hp u
      by_cases he : u=s
      · subst u; exact (hu hzero).elim
      · simp [he,hu]
    have hsingle : Finsupp.single s c=c • ket s := by ext u; simp [ket]
    rw [map_add,hsingle,map_smul]
    exact supported_add P _ _ (supported_smul P c _ (h s hsP)) (ih hpP)

def safe (root : Wire) : Gate → Prop
  | .X t | .H t | .CX _ t | .CCX _ _ t => t≠root
  | .P _ _ _ => True

def seed (root : Wire) : Gate → Gate
  | .CCX a b t => if a=root then .CX b t else if b=root then .CX a t else .CCX a b t
  | g => g

theorem gate_preserves_basis (root : Wire) (g : Gate) (s : BasisState) (hs : s root=true) (hg : safe root g) :
    SupportedOn (fun u => u root=true) (applyGate g (ket s)) := by
  cases g with
  | X t =>
    rw [applyGate_X_ket]
    apply supportedOn_ket
    simpa [upd,Ne.symm hg] using hs
  | CX c t =>
    rw [applyGate_CX_ket]
    apply supportedOn_ket
    simpa [upd,Ne.symm hg] using hs
  | CCX a b t =>
    rw [applyGate_CCX_ket]
    apply supportedOn_ket
    simpa [upd,Ne.symm hg] using hs
  | P dir k t =>
    rw [applyGate_P_ket]
    exact supported_smul _ _ _ (supportedOn_ket _ _ hs)
  | H t =>
    rw [applyGate_H_ket]
    apply supported_add
    · apply supported_smul
      apply supportedOn_ket
      simpa [upd,Ne.symm hg] using hs
    · apply supported_smul
      apply supportedOn_ket
      simpa [upd,Ne.symm hg] using hs

theorem seed_basis (root : Wire) (g : Gate) (s : BasisState) (hs : s root=true) :
    applyGate (seed root g) (ket s)=applyGate g (ket s) := by
  cases g with
  | X t => rfl
  | H t => rfl
  | CX c t => rfl
  | P dir k t => rfl
  | CCX a b t =>
    by_cases ha : a=root
    · subst a; simp [seed,hs,onKet]
    · by_cases hb : b=root
      · subst b; simp [seed,hs,ha,onKet]
      · simp [seed,ha,hb]

theorem gate_preserves (root : Wire) (g : Gate) (psi : State)
    (hp : SupportedOn (fun u => u root=true) psi) (hg : safe root g) :
    SupportedOn (fun u => u root=true) (applyGate g psi) :=
  linear_preserves_supported _ _ (fun s hs => gate_preserves_basis root g s hs hg) psi hp

theorem seed_eq (root : Wire) (g : Gate) (psi : State)
    (hp : SupportedOn (fun u => u root=true) psi) : applyGate (seed root g) psi=applyGate g psi :=
  linear_on_supported _ _ _ (fun s hs => seed_basis root g s hs) psi hp


def safeCircuit (root : Wire) (cs : Circuit) : Prop := ∀ g∈cs,safe root g

def seedCircuit (root : Wire) (cs : Circuit) : Circuit := cs.map (seed root)

theorem circuit_eq_preserves (root : Wire) (cs : Circuit) (psi : State)
    (hp : SupportedOn (fun s => s root=true) psi) (hc : safeCircuit root cs) :
    Quantum.run (seedCircuit root cs) psi=Quantum.run cs psi ∧
      SupportedOn (fun s => s root=true) (Quantum.run cs psi) := by
  induction cs generalizing psi with
  | nil => exact ⟨rfl,hp⟩
  | cons g gs ih =>
    have hg := hc g (by simp)
    have ht := ih (applyGate g psi) (gate_preserves root g psi hp hg) (by intro a ha; exact hc a (by simp [ha]))
    constructor
    · simp only [seedCircuit,List.map_cons,Quantum.run_cons]
      rw [seed_eq root g psi hp]
      exact ht.1
    · exact ht.2

def safeAdaptive (root : Wire) : AdaptiveCircuit → Prop
  | .done => True
  | .unitary cs p => safeCircuit root cs ∧ safeAdaptive root p
  | .xMeasureReset w p0 p1 => w≠root ∧ safeAdaptive root p0 ∧ safeAdaptive root p1

def seedAdaptive (root : Wire) : AdaptiveCircuit → AdaptiveCircuit
  | .done => .done
  | .unitary cs p => .unitary (seedCircuit root cs) (seedAdaptive root p)
  | .xMeasureReset w p0 p1 => .xMeasureReset w (seedAdaptive root p0) (seedAdaptive root p1)

theorem reset_preserves (root w : Wire) (b : Bool) (psi : State) (hw : root≠w)
    (hp : SupportedOn (fun s => s root=true) psi) :
    SupportedOn (fun s => s root=true) (xResetKraus w b psi) := by
  apply AdaptiveCircuit.branch_frame (.xMeasureReset w .done .done) root true
    (by simpa [AdaptiveCircuit.wires] using hw)
    ⟨[b],xResetKraus w b⟩ ?_ psi hp
  cases b <;> simp only [AdaptiveCircuit.run,List.map_singleton,List.mem_append,List.mem_singleton]
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem adaptive_relation (root : Wire) (p : AdaptiveCircuit) (hp : safeAdaptive root p) :
    List.Forall₂ (fun bnew bold => ∀ psi,SupportedOn (fun s => s root=true) psi →
        bnew.kraus psi=bold.kraus psi) (seedAdaptive root p).run p.run := by
  induction p with
  | done => exact .cons (by intro psi hp; rfl) .nil
  | unitary cs p ih =>
    simp only [seedAdaptive,AdaptiveCircuit.run,List.forall₂_map_left_iff,List.forall₂_map_right_iff]
    apply (ih hp.2).imp
    intro bnew bold hb psi hs
    change bnew.kraus (Quantum.run (seedCircuit root cs) psi)=bold.kraus (Quantum.run cs psi)
    have h := circuit_eq_preserves root cs psi hs hp.1
    rw [h.1]
    exact hb _ h.2
  | xMeasureReset w p0 p1 ih0 ih1 =>
    simp only [seedAdaptive,AdaptiveCircuit.run]
    apply List.rel_append
    · simp only [List.forall₂_map_left_iff,List.forall₂_map_right_iff]
      apply (ih0 hp.2.1).imp
      intro bnew bold hb psi hs
      change bnew.kraus (xResetKraus w false psi)=bold.kraus (xResetKraus w false psi)
      exact hb _ (reset_preserves root w false psi (Ne.symm hp.1) hs)
    · simp only [List.forall₂_map_left_iff,List.forall₂_map_right_iff]
      apply (ih1 hp.2.2).imp
      intro bnew bold hb psi hs
      change bnew.kraus (xResetKraus w true psi)=bold.kraus (xResetKraus w true psi)
      exact hb _ (reset_preserves root w true psi (Ne.symm hp.1) hs)

theorem coherent_transfer (root : Wire) (p : AdaptiveCircuit) (ideal : State →ₗ[ℂ] State)
    (Valid : BasisState → Prop) (hs : safeAdaptive root p) (hr : ∀ s,Valid s→s root=true)
    (hc : CoherentlyImplementsOn p ideal Valid) :
    CoherentlyImplementsOn (seedAdaptive root p) ideal Valid := by
  obtain ⟨cs,ha,hm⟩ := hc
  refine ⟨cs,?_,hm⟩
  clear hm
  have he := adaptive_relation root p hs
  generalize hn : (seedAdaptive root p).run = new at he ⊢
  generalize ho : p.run = old at he ha
  clear hn ho
  induction he generalizing cs with
  | nil => cases ha; exact .nil
  | @cons bnew bold new old he ht ih =>
    cases ha with
    | cons hb hc =>
      apply List.Forall₂.cons
      · intro s hs
        rw [he (ket s) (supportedOn_ket _ _ (hr s hs))]
        exact hb s hs
      · exact ih _ hc


def seedTemplate {n} (root : Wire) : TemplateGate n → TemplateGate n
  | .literal g => .literal (seed root g)
  | .whenBit i v g => .whenBit i v (seed root g)

def safeTemplate {n} (root : Wire) : TemplateGate n → Prop
  | .literal g | .whenBit _ _ g => safe root g

def seedProgram {n s e} (root : Wire) : Straight n s e → Straight n s e
  | .done => .done
  | .gate g p => .gate (seedTemplate root g) (seedProgram root p)
  | .recordGate i v g p => .recordGate i v (seed root g) (seedProgram root p)
  | .measure w p => .measure w (seedProgram root p)

def safeProgram {n s e} (root : Wire) : Straight n s e → Prop
  | .done => True
  | .gate g p => safeTemplate root g ∧ safeProgram root p
  | .recordGate _ _ g p => safe root g ∧ safeProgram root p
  | .measure w p => w≠root ∧ safeProgram root p

theorem seedTemplate_instantiate {n} (root : Wire) (g : TemplateGate n)
    (read : ConstantBit n → Bool) :
    (seedTemplate root g).instantiate read = seedCircuit root (g.instantiate read) := by
  cases g with
  | literal g => rfl
  | whenBit i v g =>
    simp only [seedTemplate,TemplateGate.instantiate]
    split <;> rfl

theorem safeTemplate_instantiate {n} (root : Wire) (g : TemplateGate n)
    (read : ConstantBit n → Bool) (h : safeTemplate root g) :
    safeCircuit root (g.instantiate read) := by
  cases g with
  | literal g => simpa [TemplateGate.instantiate,safeCircuit] using h
  | whenBit i v g =>
    simp only [TemplateGate.instantiate]
    split <;> simp_all [safeCircuit,safeTemplate]

theorem seedProgram_instantiate {n s e} (root : Wire) (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    (seedProgram root p).instantiate read history = seedAdaptive root (p.instantiate read history) := by
  induction p with
  | done => rfl
  | gate g p ih => simp only [seedProgram,Straight.instantiate,seedAdaptive,seedTemplate_instantiate,ih]
  | recordGate i v g p ih =>
    simp only [seedProgram,Straight.instantiate,seedAdaptive,ih]
    congr 1
    split <;> rfl
  | measure w p ih => simp only [seedProgram,Straight.instantiate,seedAdaptive,ih]

theorem safeProgram_instantiate {n s e} (root : Wire) (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) (h : safeProgram root p) :
    safeAdaptive root (p.instantiate read history) := by
  induction p with
  | done => trivial
  | gate g p ih => exact ⟨safeTemplate_instantiate root g read h.1,ih history h.2⟩
  | recordGate i v g p ih =>
    refine ⟨?_,ih history h.2⟩
    simp only [safeCircuit]
    split <;> simp_all [safeProgram]
  | measure w p ih => exact ⟨h.1,ih _ h.2,ih _ h.2⟩

theorem seedProgram_coherent {n s e} (root : Wire) (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool)
    (ideal : State →ₗ[ℂ] State) (Valid : BasisState → Prop)
    (hs : safeProgram root p) (hr : ∀ s,Valid s→s root=true)
    (hc : CoherentlyImplementsOn (p.instantiate read history) ideal Valid) :
    CoherentlyImplementsOn ((seedProgram root p).instantiate read history) ideal Valid := by
  rw [seedProgram_instantiate]
  exact coherent_transfer root _ ideal Valid (safeProgram_instantiate root p read history hs) hr hc


theorem seed_wellFormed (root : Wire) (g : Gate) (h : g.WellFormed) : (seed root g).WellFormed := by
  cases g <;> simp only [seed] <;> try exact h
  split
  · exact h.2.2
  · split
    · exact h.2.1
    · exact h

theorem seedTemplate_wellFormed {n} (root : Wire) (g : TemplateGate n)
    (h : g.WellFormed) : (seedTemplate root g).WellFormed := by
  cases g <;> exact seed_wellFormed root _ h

theorem seedProgram_wellFormed {n s e} (root : Wire) (p : Straight n s e)
    (h : p.WellFormed) : (seedProgram root p).WellFormed := by
  induction p with
  | done => trivial
  | gate g p ih => exact ⟨seedTemplate_wellFormed root g h.1,ih h.2⟩
  | recordGate i v g p ih => exact ⟨seed_wellFormed root g h.1,ih h.2⟩
  | measure w p ih => exact ih h

theorem seedProgram_slots {n s e} (root : Wire) (p : Straight n s e) :
    (seedProgram root p).gateSlots=p.gateSlots := by
  induction p <;> simp_all [seedProgram,Straight.gateSlots]

def hit (root : Wire) : Gate → Nat
  | .CCX a b _ => if a=root ∨ b=root then 1 else 0
  | _ => 0

theorem seed_literal_weight (root : Wire) (g : Gate) :
    ConditionalCatalyst.weightedLiteral (seed root g)+4*hit root g=ConditionalCatalyst.weightedLiteral g := by
  cases g <;> simp only [seed,hit]
  all_goals first | rfl | skip
  split <;> split <;> simp_all [ConditionalCatalyst.weightedLiteral,ConditionalCatalyst.weightedGate,
    ShorECDLP.tCost,ConditionalCatalyst.phaseTwoGate]

theorem seed_conditional_weight (root : Wire) (g : Gate) :
    ConditionalCatalyst.weightedGate (seed root g)+7*hit root g=ConditionalCatalyst.weightedGate g := by
  cases g <;> simp only [seed,hit]
  all_goals first | rfl | skip
  split <;> split <;> simp_all [ConditionalCatalyst.weightedGate,
    ShorECDLP.tCost,ConditionalCatalyst.phaseTwoGate]

def literalHits {n s e} (root : Wire) : Straight n s e → Nat
  | .done => 0
  | .gate (.literal g) p => hit root g+literalHits root p
  | .gate (.whenBit _ _ _) p => literalHits root p
  | .recordGate _ _ _ p => literalHits root p
  | .measure _ p => literalHits root p

def conditionalHits {n s e} (root : Wire) : Straight n s e → Nat
  | .done => 0
  | .gate (.literal _) p => conditionalHits root p
  | .gate (.whenBit _ _ g) p => hit root g+conditionalHits root p
  | .recordGate _ _ g p => hit root g+conditionalHits root p
  | .measure _ p => conditionalHits root p

theorem seedProgram_weight {n s e} (root : Wire) (p : Straight n s e) :
    ConditionalCatalyst.weight4 (seedProgram root p)+4*literalHits root p+7*conditionalHits root p=
      ConditionalCatalyst.weight4 p := by
  induction p with
  | done => rfl
  | gate g p ih =>
    cases g with
    | literal g =>
      have h := seed_literal_weight root g
      simp only [seedProgram,seedTemplate,ConditionalCatalyst.weight4,literalHits,conditionalHits]
      omega
    | whenBit i v g =>
      have h := seed_conditional_weight root g
      simp only [seedProgram,seedTemplate,ConditionalCatalyst.weight4,literalHits,conditionalHits]
      omega
  | recordGate i v g p ih =>
    have h := seed_conditional_weight root g
    simp only [seedProgram,ConditionalCatalyst.weight4,literalHits,conditionalHits]
    omega
  | measure w p ih => exact ih


theorem seed_wires (root : Wire) (g : Gate) : gateWires (seed root g) ⊆ gateWires g := by
  cases g <;> simp only [seed] <;> try exact List.Subset.refl _
  split
  · simp [gateWires,List.Subset]
  · split
    · simp [gateWires,List.Subset]
    · exact List.Subset.refl _

theorem seedTemplate_wires {n} (root : Wire) (g : TemplateGate n) :
    templateGateWires (seedTemplate root g) ⊆ templateGateWires g := by
  cases g <;> exact seed_wires root _

theorem seedProgram_wires {n s e} (root : Wire) (p : Straight n s e) :
    straightWires (seedProgram root p) ⊆ straightWires p := by
  induction p with
  | done => exact List.Subset.refl _
  | gate g p ih =>
    exact List.append_subset.mpr ⟨(seedTemplate_wires root g).trans (List.subset_append_left _ _),
      ih.trans (List.subset_append_right _ _)⟩
  | recordGate i v g p ih =>
    exact List.append_subset.mpr ⟨(seed_wires root g).trans (List.subset_append_left _ _),
      ih.trans (List.subset_append_right _ _)⟩
  | measure w p ih =>
    intro x hx
    simp only [seedProgram,straightWires,List.mem_cons] at hx ⊢
    exact hx.imp id (fun h => ih h)

theorem seed_literalCCX (root : Wire) (g : Gate) :
    ConditionalCatalyst.literalCCX (seed root g)+hit root g=ConditionalCatalyst.literalCCX g := by
  cases g <;> simp only [seed,hit]
  all_goals first | rfl | skip
  split <;> split <;> simp_all [ConditionalCatalyst.literalCCX]

theorem seedProgram_added {n s e} (root : Wire) (p : Straight n s e) :
    added (seedProgram root p)+literalHits root p=added p := by
  induction p with
  | done => rfl
  | gate g p ih =>
    cases g with
    | literal g =>
      have h := seed_literalCCX root g
      have ha {a b : Nat} (g : Gate) (q : Straight n a b) :
          added (.gate (.literal g) q)=ConditionalCatalyst.literalCCX g+added q := by cases g <;> simp [added,ConditionalCatalyst.literalCCX]
      rw [seedProgram,seedTemplate,ha,ha]
      simp only [literalHits]
      omega
    | whenBit i v g => exact ih
  | recordGate i v g p ih => exact ih
  | measure w p ih => exact ih


theorem safeProgram_append {n a b c} (root : Wire) (p : Straight n a b) (q : Straight n b c) :
    safeProgram root (p.append q) ↔ safeProgram root p ∧ safeProgram root q := by
  induction p <;> simp_all [Straight.append,safeProgram,and_assoc]

theorem safeProgram_cast {n a b c} (root : Wire) (p : Straight n a b) (h : b=c) :
    safeProgram root (castFinish h p) ↔ safeProgram root p := by subst c; rfl

theorem gateProgram_safe {n start} (root : Wire) (gs : List (TemplateGate n))
    (h : ∀ g∈gs,safeTemplate root g) : safeProgram root (gateProgram (cursor:=start) gs) := by
  induction gs with
  | nil => trivial
  | cons g gs ih => exact ⟨h g (by simp),ih (fun x hx => h x (by simp [hx]))⟩

theorem recordGates_safe {n s e} (root : Wire) (i : Fin s) (gs : Circuit) (p : Straight n s e)
    (hg : safeCircuit root gs) (hp : safeProgram root p) : safeProgram root (recordGates i gs p) := by
  induction gs with
  | nil => exact hp
  | cons g gs ih => exact ⟨hg g (by simp),ih (fun x hx => hg x (by simp [hx]))⟩

def safeOp {n} (root : Wire) : LookupOp n → Prop
  | .gates gs => ∀ g∈gs,safeTemplate root g
  | .erase _ b t => b≠root ∧ t≠root

theorem lookupProgram_safe {n} (root : Wire) (ops : List (LookupOp n)) (start : Nat)
    (h : ∀ op∈ops,safeOp root op) : safeProgram root (lookupProgram n ops start) := by
  induction ops generalizing start with
  | nil => trivial
  | cons op ops ih =>
    have hh := h op (by simp)
    have ht (j : Nat) := ih j (fun op ho => h op (by simp [ho]))
    cases op with
    | gates gs =>
      rw [lookupProgram,safeProgram_append]
      exact ⟨gateProgram_safe root gs hh,ht start⟩
    | erase a b t =>
      rw [lookupProgram,safeProgram_cast,safeProgram_append]
      refine ⟨?_,ht (start+1)⟩
      simp only [andEraseProgram,safeProgram]
      refine ⟨hh.2,recordGates_safe root _ _ _ ?_ trivial⟩
      simp [safeCircuit,controlledZ,safe,hh.1]

theorem ordinaryOp_safe {n} (root : Wire) (gs : Circuit) (h : safeCircuit root gs) :
    safeOp root (ordinaryOp (n:=n) gs) := by
  intro g hg
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hg
  exact h x hx

theorem unaryOps_safe {n} (root : Wire) (leaf : Nat → Wire → List (TemplateGate n))
    (tree : UnaryActionTree) (q : Wire) (paths : List Wire)
    (hl : ∀ label c g,g∈leaf label c → safeTemplate root g)
    (hb : ∀ w∈tree.indexWires,w≠root) (hp : ∀ w∈paths,w≠root) :
    ∀ op∈unaryLookupOps leaf tree q paths,safeOp root op := by
  induction tree generalizing q paths with
  | leaf label => simpa [unaryLookupOps,safeOp] using hl label q
  | node bit zero one iz io =>
    cases paths with
    | nil => simp [unaryLookupOps]
    | cons path rest =>
      have hbit : bit≠root := hb bit (by simp [UnaryActionTree.indexWires])
      have hpath : path≠root := hp path (by simp)
      have hz := iz path rest (fun w hw => hb w (by simp [UnaryActionTree.indexWires,hw]))
        (fun w hw => hp w (by simp [hw]))
      have ho := io path rest (fun w hw => hb w (by simp [UnaryActionTree.indexWires,hw]))
        (fun w hw => hp w (by simp [hw]))
      have h0 : safeOp root (ordinaryOp (n:=n) (computeZeroAnd q bit path)) := by
        apply ordinaryOp_safe
        simp [safeCircuit,computeZeroAnd,safe,hbit,hpath]
      have hc : safeOp root (ordinaryOp (n:=n) [.CX q path]) := by
        apply ordinaryOp_safe
        simp [safeCircuit,safe,hpath]
      have hx : safeOp root (ordinaryOp (n:=n) [.X bit]) := by
        apply ordinaryOp_safe
        simp [safeCircuit,safe,hbit]
      intro op hop
      simp only [unaryLookupOps,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hop
      rcases hop with (((rfl | hz') | rfl) | ho') | rfl | rfl | rfl | rfl
      · exact h0
      · exact hz _ hz'
      · exact hc
      · exact ho _ ho'
      · exact hc
      · exact hx
      · exact ⟨hbit,hpath⟩
      · exact hx



def templateHits {n} (root : Wire) : TemplateGate n → Nat
  | .literal g => hit root g
  | .whenBit _ _ _ => 0

def opHits {n} (root : Wire) : LookupOp n → Nat
  | .gates gs => (gs.map (templateHits root)).sum
  | .erase _ _ _ => 0

def opsHits {n} (root : Wire) (ops : List (LookupOp n)) : Nat := (ops.map (opHits root)).sum

theorem literalHits_append {n a b c} (root : Wire) (p : Straight n a b) (q : Straight n b c) :
    literalHits root (p.append q)=literalHits root p+literalHits root q := by
  induction p with
  | done => simp [Straight.append,literalHits]
  | gate g p ih => cases g <;> simp_all [Straight.append,literalHits,Nat.add_assoc]
  | recordGate i v g p ih => exact ih q
  | measure w p ih => exact ih q

theorem literalHits_cast {n a b c} (root : Wire) (p : Straight n a b) (h : b=c) :
    literalHits root (castFinish h p)=literalHits root p := by subst c; rfl

theorem literalHits_gateProgram {n start} (root : Wire) (gs : List (TemplateGate n)) :
    literalHits root (gateProgram (cursor:=start) gs)=(gs.map (templateHits root)).sum := by
  induction gs with
  | nil => rfl
  | cons g gs ih => cases g <;> simp_all [gateProgram,literalHits,templateHits]

theorem literalHits_recordGates {n s e} (root : Wire) (i : Fin s) (gs : Circuit) (p : Straight n s e) :
    literalHits root (recordGates i gs p)=literalHits root p := by
  induction gs <;> simp_all [recordGates,literalHits]

theorem literalHits_lookupProgram {n} (root : Wire) (ops : List (LookupOp n)) (start : Nat) :
    literalHits root (lookupProgram n ops start)=opsHits root ops := by
  induction ops generalizing start with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | gates gs =>
      simp only [lookupProgram,literalHits_append,literalHits_gateProgram,ih,opsHits,
        List.map_cons,List.sum_cons,opHits]
    | erase a b t =>
      simp only [lookupProgram,literalHits_cast,literalHits_append,andEraseProgram,
        literalHits,literalHits_recordGates,ih,opsHits,List.map_cons,List.sum_cons,opHits,zero_add]

theorem opsHits_append {n} (root : Wire) (a b : List (LookupOp n)) :
    opsHits root (a++b)=opsHits root a+opsHits root b := by simp [opsHits]

theorem unaryOps_hits_zero {n} (root : Wire) (leaf : Nat → Wire → List (TemplateGate n))
    (tree : UnaryActionTree) (q : Wire) (paths : List Wire)
    (hl : ∀ label c,(leaf label c |>.map (templateHits root)).sum=0)
    (hq : q≠root) (hb : ∀ w∈tree.indexWires,w≠root) (hp : ∀ w∈paths,w≠root) :
    opsHits root (unaryLookupOps leaf tree q paths)=0 := by
  induction tree generalizing q paths with
  | leaf label => simpa [unaryLookupOps,opsHits,opHits] using hl label q
  | node bit zero one iz io =>
    cases paths with
    | nil => rfl
    | cons path rest =>
      have hbit : bit≠root := hb bit (by simp [UnaryActionTree.indexWires])
      have hpath : path≠root := hp path (by simp)
      have hz := iz path rest hpath (fun w hw => hb w (by simp [UnaryActionTree.indexWires,hw]))
        (fun w hw => hp w (by simp [hw]))
      have ho := io path rest hpath (fun w hw => hb w (by simp [UnaryActionTree.indexWires,hw]))
        (fun w hw => hp w (by simp [hw]))
      simp only [unaryLookupOps,opsHits_append]
      rw [hz,ho]
      simp [opsHits,opHits,ordinaryOp,computeZeroAnd,templateHits,hit,hq,hbit]

theorem unaryOps_hits_one {n} (root bit path : Wire) (leaf : Nat → Wire → List (TemplateGate n))
    (zero one : UnaryActionTree) (rest : List Wire)
    (hl : ∀ label c,(leaf label c |>.map (templateHits root)).sum=0)
    (hb : ∀ w∈(UnaryActionTree.node bit zero one).indexWires,w≠root)
    (hp : ∀ w∈path::rest,w≠root) :
    opsHits root (unaryLookupOps leaf (.node bit zero one) root (path::rest))=1 := by
  have hpath : path≠root := hp path (by simp)
  have hz := unaryOps_hits_zero root leaf zero path rest hl hpath
    (fun w hw => hb w (by simp [UnaryActionTree.indexWires,hw])) (fun w hw => hp w (by simp [hw]))
  have ho := unaryOps_hits_zero root leaf one path rest hl hpath
    (fun w hw => hb w (by simp [UnaryActionTree.indexWires,hw])) (fun w hw => hp w (by simp [hw]))
  simp only [unaryLookupOps,opsHits_append]
  rw [hz,ho]
  simp [opsHits,opHits,ordinaryOp,computeZeroAnd,templateHits,hit]


open MeasuredClear

def safeRecordOp (root : Wire) : RecordLookupOp → Prop
  | .gates gs => safeCircuit root gs
  | .leaf _ _ => True
  | .erase _ b t => b≠root ∧ t≠root

theorem recordLeaf_safe {n base} (root : Wire) (ports : List (RecordPort n base))
    (scratch row control start : Nat) (hb : base≤start)
    (hs : scratch≠root) (ht : ∀ p∈ports,p.target≠root) :
    safeProgram root (recordLeaf ports scratch row control start hb) := by
  induction ports with
  | nil => trivial
  | cons p ps ih =>
    rw [recordLeaf,safeProgram_append]
    refine ⟨?_,ih (fun p hp => ht p (by simp [hp]))⟩
    simp [mixedCX,safeProgram,safeTemplate,safe,hs,ht p (by simp)]

theorem recordLookupProgram_safe {n base} (root : Wire) (ports : List (RecordPort n base))
    (scratch : Wire) (ops : List RecordLookupOp) (start : Nat) (hb : base≤start)
    (hs : scratch≠root) (ht : ∀ p∈ports,p.target≠root)
    (h : ∀ op∈ops,safeRecordOp root op) :
    safeProgram root (recordLookupProgram ports scratch ops start hb) := by
  induction ops generalizing start with
  | nil => trivial
  | cons op ops ih =>
    have hh := h op (by simp)
    have htail (j : Nat) (hj : base≤j) := ih j hj (fun op ho => h op (by simp [ho]))
    cases op with
    | gates gs =>
      rw [recordLookupProgram,safeProgram_append]
      refine ⟨gateProgram_safe root _ ?_,htail start hb⟩
      intro g hg
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hg
      exact hh x hx
    | leaf row control =>
      rw [recordLookupProgram,safeProgram_append]
      exact ⟨recordLeaf_safe root ports scratch row control start hb hs ht,htail start hb⟩
    | erase a b t =>
      rw [recordLookupProgram,safeProgram_cast,safeProgram_append]
      refine ⟨?_,htail (start+1) (hb.trans (Nat.le_succ start))⟩
      simp only [andEraseProgram,safeProgram]
      refine ⟨hh.2,recordGates_safe root _ _ _ ?_ trivial⟩
      simp [safeCircuit,controlledZ,safe,hh.1]

theorem recordUnaryOps_safe (root : Wire) (tree : UnaryActionTree) (q : Wire) (paths : List Wire)
    (hb : ∀ w∈tree.indexWires,w≠root) (hp : ∀ w∈paths,w≠root) :
    ∀ op∈recordUnaryOps tree q paths,safeRecordOp root op := by
  induction tree generalizing q paths with
  | leaf label => simp [recordUnaryOps,safeRecordOp]
  | node bit zero one iz io =>
    cases paths with
    | nil => simp [recordUnaryOps]
    | cons path rest =>
      have hbit : bit≠root := hb bit (by simp [UnaryActionTree.indexWires])
      have hpath : path≠root := hp path (by simp)
      have hz := iz path rest (fun w hw => hb w (by simp [UnaryActionTree.indexWires,hw]))
        (fun w hw => hp w (by simp [hw]))
      have ho := io path rest (fun w hw => hb w (by simp [UnaryActionTree.indexWires,hw]))
        (fun w hw => hp w (by simp [hw]))
      have h0 : safeRecordOp root (.gates (computeZeroAnd q bit path)) := by
        simp [safeRecordOp,safeCircuit,computeZeroAnd,safe,hbit,hpath]
      have hc : safeRecordOp root (.gates [.CX q path]) := by simp [safeRecordOp,safeCircuit,safe,hpath]
      have hx : safeRecordOp root (.gates [.X bit]) := by simp [safeRecordOp,safeCircuit,safe,hbit]
      intro op hop
      simp only [recordUnaryOps,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hop
      rcases hop with (((rfl | hz') | rfl) | ho') | rfl | rfl | rfl | rfl
      · exact h0
      · exact hz _ hz'
      · exact hc
      · exact ho _ ho'
      · exact hc
      · exact hx
      · exact ⟨hbit,hpath⟩
      · exact hx


def recordOpHits (root : Wire) : RecordLookupOp → Nat
  | .gates gs => (gs.map (hit root)).sum
  | _ => 0

def recordOpsHits (root : Wire) (ops : List RecordLookupOp) : Nat := (ops.map (recordOpHits root)).sum

theorem literalHits_recordLeaf {n base} (root : Wire) (ports : List (RecordPort n base))
    (scratch row control start : Nat) (hb : base≤start) :
    literalHits root (recordLeaf ports scratch row control start hb)=0 := by
  induction ports with
  | nil => rfl
  | cons p ps ih =>
    rw [recordLeaf,literalHits_append]
    simpa [mixedCX,literalHits] using ih

theorem literalHits_recordLookupProgram {n base} (root : Wire) (ports : List (RecordPort n base))
    (scratch : Wire) (ops : List RecordLookupOp) (start : Nat) (hb : base≤start) :
    literalHits root (recordLookupProgram ports scratch ops start hb)=recordOpsHits root ops := by
  induction ops generalizing start with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | gates gs =>
      simp [recordLookupProgram,literalHits_append,literalProgram,literalHits_gateProgram,ih,
        recordOpsHits,List.map_map,Function.comp_def,templateHits,recordOpHits]
    | leaf row control =>
      simp [recordLookupProgram,literalHits_append,literalHits_recordLeaf,ih,recordOpsHits,recordOpHits]
    | erase a b t =>
      simp [recordLookupProgram,literalHits_cast,literalHits_append,andEraseProgram,literalHits,
        literalHits_recordGates,ih,recordOpsHits,recordOpHits]

theorem recordOpsHits_append (root : Wire) (a b : List RecordLookupOp) :
    recordOpsHits root (a++b)=recordOpsHits root a+recordOpsHits root b := by simp [recordOpsHits]
theorem recordUnaryOps_hits_zero (root : Wire) (tree : UnaryActionTree) (q : Wire) (paths : List Wire)
    (hq : q≠root) (hb : ∀ w∈tree.indexWires,w≠root) (hp : ∀ w∈paths,w≠root) :
    recordOpsHits root (recordUnaryOps tree q paths)=0 := by
  induction tree generalizing q paths with
  | leaf label => simp [recordUnaryOps,recordOpsHits,recordOpHits]
  | node bit zero one iz io =>
    cases paths with
    | nil => rfl
    | cons path rest =>
      have hbit : bit≠root := hb bit (by simp [UnaryActionTree.indexWires])
      have hpath : path≠root := hp path (by simp)
      have hz := iz path rest hpath (fun w hw => hb w (by simp [UnaryActionTree.indexWires,hw]))
        (fun w hw => hp w (by simp [hw]))
      have ho := io path rest hpath (fun w hw => hb w (by simp [UnaryActionTree.indexWires,hw]))
        (fun w hw => hp w (by simp [hw]))
      simp only [recordUnaryOps,recordOpsHits_append]
      rw [hz,ho]
      simp [recordOpsHits,recordOpHits,computeZeroAnd,hit,hq,hbit]

theorem recordUnaryOps_hits_one (root bit path : Wire) (zero one : UnaryActionTree) (rest : List Wire)
    (hb : ∀ w∈(UnaryActionTree.node bit zero one).indexWires,w≠root)
    (hp : ∀ w∈path::rest,w≠root) :
    recordOpsHits root (recordUnaryOps (.node bit zero one) root (path::rest))=1 := by
  have hpath : path≠root := hp path (by simp)
  have hz := recordUnaryOps_hits_zero root zero path rest hpath
    (fun w hw => hb w (by simp [UnaryActionTree.indexWires,hw])) (fun w hw => hp w (by simp [hw]))
  have ho := recordUnaryOps_hits_zero root one path rest hpath
    (fun w hw => hb w (by simp [UnaryActionTree.indexWires,hw])) (fun w hw => hp w (by simp [hw]))
  simp only [recordUnaryOps,recordOpsHits_append]
  rw [hz,ho]
  simp [recordOpsHits,recordOpHits,computeZeroAnd,hit]



open WEXCredit
set_option linter.unnecessarySeqFocus false

theorem seed_phaseCost (root : Wire) (g : Gate) : primitivePhaseCost (seed root g)=primitivePhaseCost g := by
  cases g <;> simp only [seed] <;> try rfl
  split <;> first | rfl | skip
  split <;> rfl

theorem seed_tCost_le (root : Wire) (g : Gate) : tCost (seed root g)≤tCost g := by
  cases g <;> simp only [seed] <;> try exact le_rfl
  split
  · simp [tCost]
  · split <;> simp [tCost]

theorem seedProgram_residue_le {n s e} (root : Wire) (p : Straight n s e) :
    residue (seedProgram root p)≤residue p := by
  induction p with
  | done => exact le_rfl
  | gate g p ih =>
    cases g with
    | literal g =>
      simp only [seedProgram,seedTemplate,residue,seed_phaseCost]
      exact Nat.add_le_add_left ih _
    | whenBit i v g => exact Nat.add_le_add (seed_tCost_le root g) ih
  | recordGate i v g p ih => exact Nat.add_le_add (seed_tCost_le root g) ih
  | measure w p ih => exact ih

theorem seedProgram_credit {n s e} (root : Wire) (p : Straight n s e) (credit : Nat)
    (h : ProgramCredit p credit) : ProgramCredit (seedProgram root p) (credit-literalHits root p) := by
  constructor
  · have hh := seedProgram_residue_le root p
    rw [h.1] at hh
    exact Nat.eq_zero_of_le_zero hh
  · have hh := seedProgram_added root p
    rw [h.2] at hh
    omega

theorem safe_of_not_mem (root : Wire) (g : Gate) (h : root∉gateWires g) : safe root g := by
  cases g <;> simp_all [gateWires,safe] <;> aesop

theorem hit_zero_of_not_mem (root : Wire) (g : Gate) (h : root∉gateWires g) : hit root g=0 := by
  cases g <;> simp_all [gateWires,hit] <;> aesop

theorem safeTemplate_of_not_mem {n} (root : Wire) (g : TemplateGate n)
    (h : root∉templateGateWires g) : safeTemplate root g := by
  cases g <;> exact safe_of_not_mem root _ h

theorem safeProgram_of_not_mem {n s e} (root : Wire) (p : Straight n s e)
    (h : root∉straightWires p) : safeProgram root p := by
  induction p with
  | done => trivial
  | gate g p ih =>
    exact ⟨safeTemplate_of_not_mem root g (fun hw => h (List.mem_append_left _ hw)),
      ih (fun hw => h (List.mem_append_right _ hw))⟩
  | recordGate i v g p ih =>
    exact ⟨safe_of_not_mem root g (fun hw => h (List.mem_append_left _ hw)),
      ih (fun hw => h (List.mem_append_right _ hw))⟩
  | measure w p ih =>
    exact ⟨fun he => h (by simp [straightWires,he]),ih (fun hw => h (by simp [straightWires,hw]))⟩

theorem literalHits_zero_of_not_mem {n s e} (root : Wire) (p : Straight n s e)
    (h : root∉straightWires p) : literalHits root p=0 := by
  induction p with
  | done => rfl
  | gate g p ih =>
    have ht := ih (fun hw => h (List.mem_append_right _ hw))
    cases g with
    | literal g =>
      have hg := hit_zero_of_not_mem root g (fun hw => h (List.mem_append_left _ hw))
      simpa only [literalHits,hg,zero_add] using ht
    | whenBit i v g => exact ht
  | recordGate i v g p ih => exact ih (fun hw => h (List.mem_append_right _ hw))
  | measure w p ih => exact ih (fun hw => h (by simp [straightWires,hw]))


theorem literalProgram_noRoot {n start} (root : Wire) (gs : Circuit) (S : List Wire)
    (hg : circuitWires gs⊆S) (hn : root∉S) : root∉straightWires (literalProgram (n:=n) (s:=start) gs) := by
  rw [literalProgram_support]
  exact fun h => hn (hg h)

theorem measureThen_safe {n R} (root : Wire)
    (next : (cursor : Nat) → List (Fin cursor) → Straight n cursor (cursor+R))
    (hn : ∀ cursor refs,safeProgram root (next cursor refs))
    (wires : List Wire) (start : Nat) (refs : List (Fin start))
    (hw : ∀ w∈wires,w≠root) : safeProgram root (measureThen next wires start refs) := by
  induction wires generalizing start with
  | nil => exact hn start refs
  | cons w ws ih =>
    rw [measureThen,safeProgram_cast]
    exact ⟨hw w (by simp),ih (start+1) _ (fun x hx => hw x (by simp [hx]))⟩

theorem literalHits_measureThen {n R} (root : Wire) (count : Nat)
    (next : (cursor : Nat) → List (Fin cursor) → Straight n cursor (cursor+R))
    (hn : ∀ cursor refs,literalHits root (next cursor refs)=count)
    (wires : List Wire) (start : Nat) (refs : List (Fin start)) :
    literalHits root (measureThen next wires start refs)=count := by
  induction wires generalizing start with
  | nil => exact hn start refs
  | cons w ws ih =>
    rw [measureThen,literalHits_cast]
    exact ih (start+1) _

theorem straightWires_eq_naive {n s e} (p : Straight n s e) :
    straightWires p=NaiveChallenge.straightWires p := by
  induction p with
  | done => rfl
  | gate g p ih => cases g <;> simp_all [straightWires,NaiveChallenge.straightWires,templateGateWires,NaiveChallenge.slotGate]
  | recordGate i v g p ih => simp_all [straightWires,NaiveChallenge.straightWires]
  | measure w p ih => simp_all [straightWires,NaiveChallenge.straightWires]

theorem fixup9_noRoot_parts {n} (known : Wire) (low : Fin 9 → Wire) (hot : Fin 512 → Wire)
    (hl : ∀ i,low i≠known) (hh : ∀ i,hot i≠known) :
    let S := List.ofFn low++hotBank9 hot
    known∉S ∧ (circuitWires (hotPrepare9 low hot)⊆S) ∧
      (∀ start,straightWires (eraseNetwork n (hotNetwork9 low hot) start)⊆S) := by
  dsimp
  have hn : known∉List.ofFn low++hotBank9 hot := by
    simp only [List.mem_append,hotBank9,List.mem_ofFn,not_or,not_exists]
    exact ⟨fun i he => hl i he,fun i he => hh i he⟩
  have hb := hotNetwork_within9 low hot (List.ofFn low++hotBank9 hot)
    (fun i => List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
    (fun i => List.mem_append_right _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
  refine ⟨hn,hotPrepare_within9 low hot _ ?_ ?_,fun start => by rw [straightWires_eq_naive]; exact eraseNetwork_within n _ start _ hb⟩
  · intro i; exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
  · intro i; exact List.mem_append_right _ (List.mem_ofFn.mpr ⟨i,rfl⟩)

theorem fixupProgram9_safe {n base} (known : Wire) (data : List (ClearPort n)) (refs : List (Fin base))
    (low : Fin 9 → Wire) (hot : Fin 512 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire)
    (hl : ∀ i,low i≠known) (hh : ∀ i,hot i≠known) (hs : scratch≠known)
    (hb : ∀ w∈tree.indexWires,w≠known) (hp : ∀ w∈paths,w≠known) :
    safeProgram known (fixupProgram9 data refs low hot tree root scratch paths) := by
  obtain ⟨hn,hprep,herase⟩ := fixup9_noRoot_parts (n:=n) known low hot hl hh
  have hbank : known∉hotBank9 hot := fun h => hn (List.mem_append_right _ h)
  have hhad : ∀ start,safeProgram known (literalProgram (n:=n) (s:=start) ((hotBank9 hot).map Gate.H)) := by
    intro start
    apply safeProgram_of_not_mem
    rw [literalProgram_support,hadamards_wires]
    exact hbank
  have hadj : ∀ start,safeProgram known (literalProgram (n:=n) (s:=start) (Circuit.adjoint ((hotBank9 hot).map Gate.H))) := by
    intro start
    apply safeProgram_of_not_mem
    rw [literalProgram_support,hadamards_adjoint_wires]
    exact fun h => hbank (List.mem_reverse.mp h)
  simp only [fixupProgram9,safeProgram_append,safeProgram_cast]
  refine ⟨safeProgram_of_not_mem known _ (literalProgram_noRoot known _ _ hprep hn),
    hhad _,recordLookupProgram_safe known _ scratch _ base (Nat.le_refl base) hs ?_
      (recordUnaryOps_safe known tree root paths hb hp),hadj _,safeProgram_of_not_mem known _ ?_,?_⟩
  · intro p h
    have ht := phasePorts_targets9 hot (data.zip refs) p h
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp ht
    exact hi ▸ hh i
  · exact fun h => hn (herase _ h)
  · apply safeProgram_of_not_mem
    rw [literalProgram_support]
    simpa [circuitWires,gateWires,eq_comm] using hh 0


theorem literalHits_hadamards {n start} (root : Wire) (ws : List Wire) :
    literalHits root (literalProgram (n:=n) (s:=start) (ws.map Gate.H))=0 := by
  simp [literalProgram,literalHits_gateProgram,List.map_map,Function.comp_def,templateHits,hit]

theorem literalHits_adjoint_hadamards {n start} (root : Wire) (ws : List Wire) :
    literalHits root (literalProgram (n:=n) (s:=start) (Circuit.adjoint (ws.map Gate.H)))=0 := by
  simp [literalProgram,literalHits_gateProgram,Circuit.adjoint,List.map_map,Function.comp_def,templateHits,hit,Gate.adjoint]

theorem literalHits_eraseNetwork (root : Wire) (n : Nat) (cs : List SplitCell) (start : Nat) :
    literalHits root (eraseNetwork n cs start)=0 := by
  induction cs generalizing start with
  | nil => rfl
  | cons c cs ih =>
    rw [eraseNetwork,literalHits_cast,literalHits_append,ih]
    simp [eraseSplit,andEraseProgram,literalHits,literalHits_recordGates,hit]

theorem literalHits_X {n start} (root w : Wire) :
    literalHits root (literalProgram (n:=n) (s:=start) [.X w])=0 := rfl

theorem fixupProgram9_hits {n base} (known : Wire) (data : List (ClearPort n)) (refs : List (Fin base))
    (low : Fin 9 → Wire) (hot : Fin 512 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire)
    (hl : ∀ i,low i≠known) (hh : ∀ i,hot i≠known) :
    literalHits known (fixupProgram9 data refs low hot tree root scratch paths)=
      recordOpsHits known (recordUnaryOps tree root paths) := by
  obtain ⟨hn,hprep,_⟩ := fixup9_noRoot_parts (n:=n) known low hot hl hh
  have hz (start : Nat) : literalHits known (literalProgram (n:=n) (s:=start) (hotPrepare9 low hot))=0 :=
    literalHits_zero_of_not_mem known _ (literalProgram_noRoot known _ _ hprep hn)
  simp only [fixupProgram9,literalHits_append,literalHits_cast,literalHits_recordLookupProgram,
    literalHits_hadamards,literalHits_adjoint_hadamards,literalHits_eraseNetwork,literalHits_X,hz,
    zero_add,add_zero]

theorem measuredClear9_safe {n} (known : Wire) (data : List (ClearPort n))
    (low : Fin 9 → Wire) (hot : Fin 512 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire) (start : Nat)
    (hl : ∀ i,low i≠known) (hh : ∀ i,hot i≠known) (hs : scratch≠known)
    (hb : ∀ w∈tree.indexWires,w≠known) (hp : ∀ w∈paths,w≠known)
    (hd : ∀ p∈data,p.target≠known) :
    safeProgram known (measuredClear9 data low hot tree root scratch paths start) := by
  rw [measuredClear9,safeProgram_cast]
  apply measureThen_safe
  · intro cursor refs
    rw [safeProgram_cast]
    exact fixupProgram9_safe known data refs low hot tree root scratch paths hl hh hs hb hp
  · intro w hw
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hw
    exact hd p hp

theorem measuredClear9_hits {n} (known : Wire) (data : List (ClearPort n))
    (low : Fin 9 → Wire) (hot : Fin 512 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire) (start : Nat)
    (hl : ∀ i,low i≠known) (hh : ∀ i,hot i≠known) :
    literalHits known (measuredClear9 data low hot tree root scratch paths start)=
      recordOpsHits known (recordUnaryOps tree root paths) := by
  rw [measuredClear9,literalHits_cast]
  apply literalHits_measureThen
  intro cursor refs
  rw [literalHits_cast]
  exact fixupProgram9_hits known data refs low hot tree root scratch paths hl hh


attribute [local irreducible] KnownRoot.first18_seededOps
  KnownRoot.first18_seededSel KnownRoot.first18_seededProgram

theorem layout_avoids {tree : UnaryActionTree} {root : Wire} {paths : List Wire}
    (h : tree.Layout root paths) :
    (∀ w∈tree.indexWires,w≠root) ∧ (∀ w∈paths,w≠root) := by
  have hn := (List.nodup_cons.mp (unaryLayout_decoderNodup h)).1
  constructor
  · intro w hw he
    subst w
    exact hn (List.mem_append_left _ (List.mem_dedup.mpr hw))
  · intro w hw he
    subst w
    exact hn (List.mem_append_right _ hw)

theorem unaryOps_root_hits {n} (root : Wire) (leaf : Nat → Wire → List (TemplateGate n))
    (tree : UnaryActionTree) (paths : List Wire) (h : tree.Layout root paths)
    (hn : 0<tree.internalNodes)
    (hl : ∀ label c,(leaf label c |>.map (templateHits root)).sum=0) :
    opsHits root (unaryLookupOps leaf tree root paths)=1 := by
  obtain ⟨hb,hp⟩ := layout_avoids h
  cases h with
  | leaf label root paths _ => simp [UnaryActionTree.internalNodes] at hn
  | node bit root path zero one rest _ _ _ => exact unaryOps_hits_one root bit path leaf zero one rest hl hb hp

theorem recordUnaryOps_root_hits (root : Wire) (tree : UnaryActionTree) (paths : List Wire)
    (h : tree.Layout root paths) (hn : 0<tree.internalNodes) :
    recordOpsHits root (recordUnaryOps tree root paths)=1 := by
  obtain ⟨hb,hp⟩ := layout_avoids h
  cases h with
  | leaf label root paths _ => simp [UnaryActionTree.internalNodes] at hn
  | node bit root path zero one rest _ _ _ => exact recordUnaryOps_hits_one root bit path zero one rest hb hp

theorem first18_leaf_safe (label : Nat) (control : Wire) (g : TemplateGate 262144)
    (hg : g∈First18.selLeaf label control) : safeTemplate 836 g := by
  simp only [First18.selLeaf,lookupLeafGates,List.mem_map] at hg
  obtain ⟨⟨ref,target⟩,hm,rfl⟩ := hg
  change target≠836
  have ht : target∈pointLogicalWires ∨ target∈First18.garb := by
    rcases List.mem_append.mp hm with h | h
    · exact Or.inl (List.of_mem_zip h).2
    · exact Or.inr (List.of_mem_zip h).2
  intro he
  subst target
  rcases ht with hp | hg
  · have h := First18.mem_point hp
    omega
  · have h := First18.mem_garb hg
    omega

theorem first18_leaf_hits (label : Nat) (control : Wire) :
    ((First18.selLeaf label control).map (templateHits 836)).sum=0 := by
  simp [First18.selLeaf,lookupLeafGates,List.map_map,Function.comp_def,templateHits]

theorem first18_selOps_safe : ∀ op∈First18.selOps,safeOp 836 op := by
  rw [First18.selOps]
  obtain ⟨hb,hp⟩ := layout_avoids First18.sel_layout
  exact unaryOps_safe 836 First18.selLeaf _ _ _ first18_leaf_safe hb hp

theorem first18_selOps_hits : opsHits 836 First18.selOps=1 := by
  rw [First18.selOps]
  exact unaryOps_root_hits 836 First18.selLeaf _ _ First18.sel_layout
    (by rw [First18.sel_nodes]; decide) first18_leaf_hits

theorem first18_seededOps_safe : ∀ op∈KnownRoot.first18_seededOps,safeOp 836 op := by
  intro op hop
  rw [KnownRoot.first18_seededOps] at hop
  rcases List.mem_cons.mp hop with rfl | ht
  · apply ordinaryOp_safe
    simp [safeCircuit,KnownRoot.seededZeroAnd,safe]
  · exact first18_selOps_safe op (List.mem_of_mem_tail ht)

theorem prefix_hits_drop {n} (root bit path : Wire) (ops : List (LookupOp n))
    (h : opsHits root (ordinaryOp (computeZeroAnd root bit path)::ops)=1) :
    opsHits root (ordinaryOp (KnownRoot.seededZeroAnd root bit path)::ops)=0 := by
  simp [opsHits,opHits,ordinaryOp,computeZeroAnd,KnownRoot.seededZeroAnd,templateHits,hit] at h ⊢
  omega

theorem first18_seededOps_hits : opsHits 836 KnownRoot.first18_seededOps=0 := by
  have h := congrArg (opsHits 836) KnownRoot.first18_head
  rw [first18_selOps_hits] at h
  rw [KnownRoot.first18_seededOps]
  exact prefix_hits_drop 836 856 519 First18.selOps.tail h.symm

theorem first18_seededSel_safe (start : Nat) : safeProgram 836 (KnownRoot.first18_seededSel start) := by
  rw [KnownRoot.first18_seededSel,safeProgram_cast]
  exact lookupProgram_safe 836 _ start first18_seededOps_safe

theorem first18_seededSel_hits (start : Nat) : literalHits 836 (KnownRoot.first18_seededSel start)=0 := by
  rw [KnownRoot.first18_seededSel,literalHits_cast,literalHits_lookupProgram,first18_seededOps_hits]

theorem first18_swap_noRoot (start : Nat) : 836∉straightWires (First18.swapProgram start) := by
  rw [First18.swapProgram,literalProgram_support]
  intro h
  rcases First18.swap_wires 836 h with h | h | h
  · dsimp only [Wire] at *; omega
  · have h := First18.mem_point h
    dsimp only [Wire] at *; omega
  · have h := First18.mem_garb h
    dsimp only [Wire] at *; omega

theorem first18_low_ne (i : Fin 9) : First18.low i≠836 := by
  simp only [First18.low]
  dsimp only [Wire] at *
  omega

theorem first18_hot_ne (i : Fin 512) : First18.hot i≠836 := by
  simp only [First18.hot]
  dsimp only [Wire] at *
  omega

theorem first18_clear_safe (start : Nat) : safeProgram 836 (First18.clearProgram start) := by
  obtain ⟨hb,hp⟩ := layout_avoids First18.clear_layout
  rw [First18.clearProgram,safeProgram_cast]
  apply measuredClear9_safe 836 _ _ _ _ _ _ _ _ first18_low_ne first18_hot_ne (by decide) hb hp
  intro p hp he
  apply First18.tree_not_targets 836 (by simp)
  exact List.mem_map.mpr ⟨p,hp,he⟩

theorem first18_clear_hits (start : Nat) : literalHits 836 (First18.clearProgram start)=1 := by
  rw [First18.clearProgram,literalHits_cast,measuredClear9_hits 836 _ _ _ _ _ _ _ _ first18_low_ne first18_hot_ne]
  exact recordUnaryOps_root_hits 836 _ _ First18.clear_layout (by rw [First18.clear_nodes]; decide)

theorem first18_program_safe (start : Nat) : safeProgram 836 (KnownRoot.first18_seededProgram start) := by
  simp only [KnownRoot.first18_seededProgram,safeProgram_cast,safeProgram_append]
  exact ⟨⟨first18_seededSel_safe start,safeProgram_of_not_mem 836 _ (first18_swap_noRoot _)⟩,first18_clear_safe _⟩

theorem first18_program_hits (start : Nat) : literalHits 836 (KnownRoot.first18_seededProgram start)=1 := by
  simp only [KnownRoot.first18_seededProgram,literalHits_cast,literalHits_append,first18_seededSel_hits,
    first18_clear_hits,literalHits_zero_of_not_mem 836 _ (first18_swap_noRoot _),zero_add]


open ConditionalCatalyst Secp256k1
set_option maxHeartbeats 2000000

def first18_rootProgram (start : Nat) : Straight 262144 start (start+132606) :=
  seedProgram 836 (KnownRoot.first18_seededProgram start)

theorem first18_rootProgram_coherent (coeffs : Fin 262144 → PointCoeff) (Q : Point)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((first18_rootProgram start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (fun s => pointWrite (SelectSchedule18.tablePoint coeffs Q
        (tableAddressValue SelectSchedule18.bits s)) s)) SelectSchedule18.Input := by
  apply seedProgram_coherent 836 _ _ _ _ _ (first18_program_safe start) (fun _ hs => hs.1)
  exact KnownRoot.first18_seededProgram_coherent coeffs Q start history

theorem first18_rootProgram_residue (start : Nat) : residue (first18_rootProgram start)=0 := by
  have h := seedProgram_residue_le 836 (KnownRoot.first18_seededProgram start)
  rw [KnownRoot.first18_seededProgram_residue] at h
  exact Nat.eq_zero_of_le_zero h

theorem first18_rootProgram_added (start : Nat) : added (first18_rootProgram start)=132595 := by
  have h := seedProgram_added 836 (KnownRoot.first18_seededProgram start)
  rw [KnownRoot.first18_seededProgram_added,first18_program_hits] at h
  change added (seedProgram 836 (KnownRoot.first18_seededProgram start))=132595
  omega

theorem first18_rootProgram_slots (start : Nat) : (first18_rootProgram start).gateSlots≤1000000000 := by
  rw [first18_rootProgram,seedProgram_slots]
  exact KnownRoot.first18_seededProgram_slots start

theorem first18_rootProgram_support (start : Nat) :
    straightWires (first18_rootProgram start)⊆First18.support :=
  (seedProgram_wires 836 _).trans (KnownRoot.first18_seededProgram_support start)

theorem first18_rootProgram_wellFormed (start : Nat) : (first18_rootProgram start).WellFormed :=
  seedProgram_wellFormed 836 _ (KnownRoot.first18_seededProgram_wellFormed start)

def windowGeneric {n : Nat} (rows : Fin 262144 → Fin n) : Single.Window n :=
  ⟨SelectSchedule18.bits.reverse,132606,fun start => reindexStraight rows (first18_rootProgram start)⟩

theorem program_tCount (coeffs : Fin 262144 → PointCoeff) (Q : Secp256k1.Point) (start : Nat) (history : Fin start → Bool) :
    ((first18_rootProgram start).instantiate (readConstant coeffs Q) history).tCount = 928165 := by
  rw [exact_t _ (first18_rootProgram_residue start),first18_rootProgram_added]

theorem window_law_generic {n : Nat} (coeffs : Fin n → PointCoeff) (rows : Fin 262144 → Fin n)
    (init : Point → Nat → Point)
    (hcoeff : ∀ Q, order • Q = 0 → ∀ a : Fin 262144,
      constantPoint Q (coeffs (rows a)) = init Q a.val) :
    Single.WindowLaw coeffs (windowGeneric rows) (SelectSchedule18.update init)
      SelectSchedule18.Input := by
  intro Q hQ hn start history
  have hvalid := first18_rootProgram_coherent (fun a => coeffs (rows a)) Q start history
  have hupdate : (fun s => pointWrite
      (SelectSchedule18.tablePoint (fun a => coeffs (rows a)) Q
        (tableAddressValue SelectSchedule18.bits s)) s) = SelectSchedule18.update init Q := by
    funext s
    unfold SelectSchedule18.tablePoint SelectSchedule18.update
    have hbound : tableAddressValue SelectSchedule18.bits s < 262144 := by
      have hb := tableAddressValue_lt SelectSchedule18.bits s
      have hlen : SelectSchedule18.bits.length = 18 := by decide +kernel
      simpa only [hlen] using hb
    simp only [Nat.mod_eq_of_lt hbound]
    rw [hcoeff Q hQ]
  rw [hupdate] at hvalid
  unfold windowGeneric
  rw [reindexStraight_instantiate,
    readConstant_reindex rows (fun a => coeffs (rows a)) coeffs Q (fun _ => rfl)]
  exact hvalid

theorem window_wellFormed {n : Nat} (rows : Fin 262144 → Fin n) (start : Nat) :
    ((windowGeneric rows).program start).WellFormed := by
  unfold windowGeneric
  exact (reindexStraight_wellFormed rows (first18_rootProgram start)).mpr (first18_rootProgram_wellFormed start)

theorem window_slots {n : Nat} (rows : Fin 262144 → Fin n) (start : Nat) :
    ((windowGeneric rows).program start).gateSlots ≤ 1000000000 := by
  unfold windowGeneric
  rw [reindexStraight_gateSlots]
  exact first18_rootProgram_slots start

theorem window_support {n : Nat} (rows : Fin 262144 → Fin n) (start : Nat) :
    straightWires ((windowGeneric rows).program start) ⊆ First18.support := by
  unfold windowGeneric
  rw [straightWires_reindex]
  exact first18_rootProgram_support start

theorem window_t {n : Nat} (coeffs : Fin n → PointCoeff) (rows : Fin 262144 → Fin n)
    (Q : Point) (start : Nat) (history : Fin start → Bool) :
    (((windowGeneric rows).program start).instantiate (readConstant coeffs Q) history).tCount = 928165 := by
  unfold windowGeneric
  rw [reindexStraight_instantiate,
    readConstant_reindex rows (fun a => coeffs (rows a)) coeffs Q (fun _ => rfl)]
  exact program_tCount (fun a => coeffs (rows a)) Q start history

theorem window_credit {n : Nat} (_coeffs : Fin n → PointCoeff) (rows : Fin 262144 → Fin n)
    (_Q : Point) (start : Nat) (_history : Fin start → Bool) :
    added ((windowGeneric rows).program start) = 132595 := by
  unfold windowGeneric
  rw [added_reindex]
  exact first18_rootProgram_added start


#print axioms first18_rootProgram_coherent
#print axioms first18_rootProgram_added
#print axioms window_law_generic
end
end ShorECDLP.Entrant.RootPass
