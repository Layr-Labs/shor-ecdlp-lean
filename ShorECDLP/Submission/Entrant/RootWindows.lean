import ShorECDLP.Submission.Entrant.WideBank8
import ShorECDLP.Submission.Entrant.RootPass
namespace ShorECDLP.Entrant.ConstRoot
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration RootPass
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

open AndGadget WEXCredit ConditionalCatalyst MeasuredClear
def readOnly (root : Wire) : Gate → Prop
  | .X t | .H t | .CX _ t | .CCX _ _ t | .P _ _ t => t≠root

def readOnlyTemplate {n} (root : Wire) : TemplateGate n → Prop
  | .literal g | .whenBit _ _ g => readOnly root g

def readOnlyCircuit (root : Wire) (cs : Circuit) : Prop := ∀ g∈cs,readOnly root g

def readOnlyProgram {n s e} (root : Wire) : Straight n s e → Prop
  | .done => True
  | .gate g p => readOnlyTemplate root g ∧ readOnlyProgram root p
  | .recordGate _ _ g p => readOnly root g ∧ readOnlyProgram root p
  | .measure w p => w≠root ∧ readOnlyProgram root p

theorem readOnly_of_not_mem (root : Wire) (g : Gate) (h : root∉gateWires g) : readOnly root g := by
  cases g <;> simp_all [gateWires,readOnly] <;> aesop

theorem readOnlyTemplate_of_not_mem {n} (root : Wire) (g : TemplateGate n)
    (h : root∉templateGateWires g) : readOnlyTemplate root g := by
  cases g <;> exact readOnly_of_not_mem root _ h

theorem readOnlyProgram_of_not_mem {n s e} (root : Wire) (p : Straight n s e)
    (h : root∉straightWires p) : readOnlyProgram root p := by
  induction p with
  | done => trivial
  | gate g p ih =>
    exact ⟨readOnlyTemplate_of_not_mem root g (fun hw => h (List.mem_append_left _ hw)),
      ih (fun hw => h (List.mem_append_right _ hw))⟩
  | recordGate i v g p ih =>
    exact ⟨readOnly_of_not_mem root g (fun hw => h (List.mem_append_left _ hw)),
      ih (fun hw => h (List.mem_append_right _ hw))⟩
  | measure w p ih =>
    exact ⟨fun he => h (by simp [straightWires,he]),ih (fun hw => h (by simp [straightWires,hw]))⟩

theorem readOnlyProgram_append {n a b c} (root : Wire) (p : Straight n a b) (q : Straight n b c) :
    readOnlyProgram root (p.append q) ↔ readOnlyProgram root p ∧ readOnlyProgram root q := by
  induction p <;> simp_all [Straight.append,readOnlyProgram,and_assoc]

theorem readOnlyProgram_cast {n a b c} (root : Wire) (p : Straight n a b) (h : b=c) :
    readOnlyProgram root (castFinish h p) ↔ readOnlyProgram root p := by subst c; rfl

theorem gateProgram_readOnly {n start} (root : Wire) (gs : List (TemplateGate n))
    (h : ∀ g∈gs,readOnlyTemplate root g) : readOnlyProgram root (gateProgram (cursor:=start) gs) := by
  induction gs with
  | nil => trivial
  | cons g gs ih => exact ⟨h g (by simp),ih (fun x hx => h x (by simp [hx]))⟩

theorem recordGates_readOnly {n s e} (root : Wire) (i : Fin s) (gs : Circuit) (p : Straight n s e)
    (hg : readOnlyCircuit root gs) (hp : readOnlyProgram root p) : readOnlyProgram root (recordGates i gs p) := by
  induction gs with
  | nil => exact hp
  | cons g gs ih => exact ⟨hg g (by simp),ih (fun x hx => hg x (by simp [hx]))⟩

def readOnlyOp {n} (root : Wire) : LookupOp n → Prop
  | .gates gs => ∀ g∈gs,readOnlyTemplate root g
  | .erase _ b t => b≠root ∧ t≠root

theorem lookupProgram_readOnly {n} (root : Wire) (ops : List (LookupOp n)) (start : Nat)
    (h : ∀ op∈ops,readOnlyOp root op) : readOnlyProgram root (lookupProgram n ops start) := by
  induction ops generalizing start with
  | nil => trivial
  | cons op ops ih =>
    have hh := h op (by simp)
    have ht (j : Nat) := ih j (fun op ho => h op (by simp [ho]))
    cases op with
    | gates gs =>
      rw [lookupProgram,readOnlyProgram_append]
      exact ⟨gateProgram_readOnly root gs hh,ht start⟩
    | erase a b t =>
      rw [lookupProgram,readOnlyProgram_cast,readOnlyProgram_append]
      refine ⟨?_,ht (start+1)⟩
      simp only [andEraseProgram,readOnlyProgram]
      refine ⟨hh.2,recordGates_readOnly root _ _ _ ?_ trivial⟩
      simp [readOnlyCircuit,controlledZ,readOnly,hh.1]

theorem ordinaryOp_readOnly {n} (root : Wire) (gs : Circuit) (h : readOnlyCircuit root gs) :
    readOnlyOp root (ordinaryOp (n:=n) gs) := by
  intro g hg
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hg
  exact h x hx
theorem unaryOps_readOnly {n} (root : Wire) (leaf : Nat → Wire → List (TemplateGate n))
    (tree : UnaryActionTree) (q : Wire) (paths : List Wire)
    (hl : ∀ label c g,g∈leaf label c → readOnlyTemplate root g)
    (hb : ∀ w∈tree.indexWires,w≠root) (hp : ∀ w∈paths,w≠root) :
    ∀ op∈unaryLookupOps leaf tree q paths,readOnlyOp root op := by
  induction tree generalizing q paths with
  | leaf label => simpa [unaryLookupOps,readOnlyOp] using hl label q
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
      have h0 : readOnlyOp root (ordinaryOp (n:=n) (computeZeroAnd q bit path)) := by
        apply ordinaryOp_readOnly
        simp [readOnlyCircuit,computeZeroAnd,readOnly,hbit,hpath]
      have hc : readOnlyOp root (ordinaryOp (n:=n) [.CX q path]) := by
        apply ordinaryOp_readOnly
        simp [readOnlyCircuit,readOnly,hpath]
      have hx : readOnlyOp root (ordinaryOp (n:=n) [.X bit]) := by
        apply ordinaryOp_readOnly
        simp [readOnlyCircuit,readOnly,hbit]
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




open MeasuredClear
def readOnlyRecordOp (root : Wire) : RecordLookupOp → Prop
  | .gates gs => readOnlyCircuit root gs
  | .leaf _ _ => True
  | .erase _ b t => b≠root ∧ t≠root

theorem recordLeaf_readOnly {n base} (root : Wire) (ports : List (RecordPort n base))
    (scratch row control start : Nat) (hb : base≤start)
    (hs : scratch≠root) (ht : ∀ p∈ports,p.target≠root) :
    readOnlyProgram root (recordLeaf ports scratch row control start hb) := by
  induction ports with
  | nil => trivial
  | cons p ps ih =>
    rw [recordLeaf,readOnlyProgram_append]
    refine ⟨?_,ih (fun p hp => ht p (by simp [hp]))⟩
    simp [mixedCX,readOnlyProgram,readOnlyTemplate,readOnly,hs,ht p (by simp)]

theorem recordLookupProgram_readOnly {n base} (root : Wire) (ports : List (RecordPort n base))
    (scratch : Wire) (ops : List RecordLookupOp) (start : Nat) (hb : base≤start)
    (hs : scratch≠root) (ht : ∀ p∈ports,p.target≠root)
    (h : ∀ op∈ops,readOnlyRecordOp root op) :
    readOnlyProgram root (recordLookupProgram ports scratch ops start hb) := by
  induction ops generalizing start with
  | nil => trivial
  | cons op ops ih =>
    have hh := h op (by simp)
    have htail (j : Nat) (hj : base≤j) := ih j hj (fun op ho => h op (by simp [ho]))
    cases op with
    | gates gs =>
      rw [recordLookupProgram,readOnlyProgram_append]
      refine ⟨gateProgram_readOnly root _ ?_,htail start hb⟩
      intro g hg
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hg
      exact hh x hx
    | leaf row control =>
      rw [recordLookupProgram,readOnlyProgram_append]
      exact ⟨recordLeaf_readOnly root ports scratch row control start hb hs ht,htail start hb⟩
    | erase a b t =>
      rw [recordLookupProgram,readOnlyProgram_cast,readOnlyProgram_append]
      refine ⟨?_,htail (start+1) (hb.trans (Nat.le_succ start))⟩
      simp only [andEraseProgram,readOnlyProgram]
      refine ⟨hh.2,recordGates_readOnly root _ _ _ ?_ trivial⟩
      simp [readOnlyCircuit,controlledZ,readOnly,hh.1]

theorem recordUnaryOps_readOnly (root : Wire) (tree : UnaryActionTree) (q : Wire) (paths : List Wire)
    (hb : ∀ w∈tree.indexWires,w≠root) (hp : ∀ w∈paths,w≠root) :
    ∀ op∈recordUnaryOps tree q paths,readOnlyRecordOp root op := by
  induction tree generalizing q paths with
  | leaf label => simp [recordUnaryOps,readOnlyRecordOp]
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
      have h0 : readOnlyRecordOp root (.gates (computeZeroAnd q bit path)) := by
        simp [readOnlyRecordOp,readOnlyCircuit,computeZeroAnd,readOnly,hbit,hpath]
      have hc : readOnlyRecordOp root (.gates [.CX q path]) := by simp [readOnlyRecordOp,readOnlyCircuit,readOnly,hpath]
      have hx : readOnlyRecordOp root (.gates [.X bit]) := by simp [readOnlyRecordOp,readOnlyCircuit,readOnly,hbit]
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

theorem measureThen_readOnly {n R} (root : Wire)
    (next : (cursor : Nat) → List (Fin cursor) → Straight n cursor (cursor+R))
    (hn : ∀ cursor refs,readOnlyProgram root (next cursor refs))
    (wires : List Wire) (start : Nat) (refs : List (Fin start))
    (hw : ∀ w∈wires,w≠root) : readOnlyProgram root (measureThen next wires start refs) := by
  induction wires generalizing start with
  | nil => exact hn start refs
  | cons w ws ih =>
    rw [measureThen,readOnlyProgram_cast]
    exact ⟨hw w (by simp),ih (start+1) _ (fun x hx => hw x (by simp [hx]))⟩

theorem fixup8_noRoot_parts {n} (known : Wire) (low : Fin 8 → Wire) (hot : Fin 256 → Wire)
    (hl : ∀ i,low i≠known) (hh : ∀ i,hot i≠known) :
    let S := List.ofFn low++hotBank8 hot
    known∉S ∧ (circuitWires (hotPrepare8 low hot)⊆S) ∧
      (∀ start,straightWires (eraseNetwork n (hotNetwork8 low hot) start)⊆S) := by
  dsimp
  have hn : known∉List.ofFn low++hotBank8 hot := by
    simp only [List.mem_append,hotBank8,List.mem_ofFn,not_or,not_exists]
    exact ⟨fun i he => hl i he,fun i he => hh i he⟩
  have hb := hotNetwork_within8 low hot (List.ofFn low++hotBank8 hot)
    (fun i => List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
    (fun i => List.mem_append_right _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
  refine ⟨hn,hotPrepare_within8 low hot _ ?_ ?_,fun start => by rw [straightWires_eq_naive]; exact eraseNetwork_within n _ start _ hb⟩
  · intro i; exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
  · intro i; exact List.mem_append_right _ (List.mem_ofFn.mpr ⟨i,rfl⟩)

theorem fixupProgram8_readOnly {n base} (known : Wire) (data : List (ClearPort n)) (refs : List (Fin base))
    (low : Fin 8 → Wire) (hot : Fin 256 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire)
    (hl : ∀ i,low i≠known) (hh : ∀ i,hot i≠known) (hs : scratch≠known)
    (hb : ∀ w∈tree.indexWires,w≠known) (hp : ∀ w∈paths,w≠known) :
    readOnlyProgram known (fixupProgram8 data refs low hot tree root scratch paths) := by
  obtain ⟨hn,hprep,herase⟩ := fixup8_noRoot_parts (n:=n) known low hot hl hh
  have hbank : known∉hotBank8 hot := fun h => hn (List.mem_append_right _ h)
  have hhad : ∀ start,readOnlyProgram known (literalProgram (n:=n) (s:=start) ((hotBank8 hot).map Gate.H)) := by
    intro start
    apply readOnlyProgram_of_not_mem
    rw [literalProgram_support,hadamards_wires]
    exact hbank
  have hadj : ∀ start,readOnlyProgram known (literalProgram (n:=n) (s:=start) (Circuit.adjoint ((hotBank8 hot).map Gate.H))) := by
    intro start
    apply readOnlyProgram_of_not_mem
    rw [literalProgram_support,hadamards_adjoint_wires]
    exact fun h => hbank (List.mem_reverse.mp h)
  simp only [fixupProgram8,readOnlyProgram_append,readOnlyProgram_cast]
  refine ⟨readOnlyProgram_of_not_mem known _ (literalProgram_noRoot known _ _ hprep hn),
    hhad _,recordLookupProgram_readOnly known _ scratch _ base (Nat.le_refl base) hs ?_
      (recordUnaryOps_readOnly known tree root paths hb hp),hadj _,readOnlyProgram_of_not_mem known _ ?_,?_⟩
  · intro p h
    have ht := phasePorts_targets8 hot (data.zip refs) p h
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp ht
    exact hi ▸ hh i
  · exact fun h => hn (herase _ h)
  · apply readOnlyProgram_of_not_mem
    rw [literalProgram_support]
    simpa [circuitWires,gateWires,eq_comm] using hh 0


theorem measuredClear8_readOnly {n} (known : Wire) (data : List (ClearPort n))
    (low : Fin 8 → Wire) (hot : Fin 256 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire) (start : Nat)
    (hl : ∀ i,low i≠known) (hh : ∀ i,hot i≠known) (hs : scratch≠known)
    (hb : ∀ w∈tree.indexWires,w≠known) (hp : ∀ w∈paths,w≠known)
    (hd : ∀ p∈data,p.target≠known) :
    readOnlyProgram known (measuredClear8 data low hot tree root scratch paths start) := by
  rw [measuredClear8,readOnlyProgram_cast]
  apply measureThen_readOnly
  · intro cursor refs
    rw [readOnlyProgram_cast]
    exact fixupProgram8_readOnly known data refs low hot tree root scratch paths hl hh hs hb hp
  · intro w hw
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hw
    exact hd p hp

theorem fixup7_noRoot_parts {n} (known : Wire) (low : Fin 7 → Wire) (hot : Fin 128 → Wire)
    (hl : ∀ i,low i≠known) (hh : ∀ i,hot i≠known) :
    let S := List.ofFn low++hotBank hot
    known∉S ∧ (circuitWires (hotPrepare low hot)⊆S) ∧
      (∀ start,straightWires (eraseNetwork n (hotNetwork low hot) start)⊆S) := by
  dsimp
  have hn : known∉List.ofFn low++hotBank hot := by
    simp only [List.mem_append,hotBank,List.mem_ofFn,not_or,not_exists]
    exact ⟨fun i he => hl i he,fun i he => hh i he⟩
  have hb := hotNetwork_within low hot (List.ofFn low++hotBank hot)
    (fun i => List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
    (fun i => List.mem_append_right _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
  refine ⟨hn,hotPrepare_within low hot _ ?_ ?_,fun start => by rw [straightWires_eq_naive]; exact eraseNetwork_within n _ start _ hb⟩
  · intro i; exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
  · intro i; exact List.mem_append_right _ (List.mem_ofFn.mpr ⟨i,rfl⟩)

theorem fixupProgram7_readOnly {n base} (known : Wire) (data : List (ClearPort n)) (refs : List (Fin base))
    (low : Fin 7 → Wire) (hot : Fin 128 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire)
    (hl : ∀ i,low i≠known) (hh : ∀ i,hot i≠known) (hs : scratch≠known)
    (hb : ∀ w∈tree.indexWires,w≠known) (hp : ∀ w∈paths,w≠known) :
    readOnlyProgram known (fixupProgram data refs low hot tree root scratch paths) := by
  obtain ⟨hn,hprep,herase⟩ := fixup7_noRoot_parts (n:=n) known low hot hl hh
  have hbank : known∉hotBank hot := fun h => hn (List.mem_append_right _ h)
  have hhad : ∀ start,readOnlyProgram known (literalProgram (n:=n) (s:=start) ((hotBank hot).map Gate.H)) := by
    intro start
    apply readOnlyProgram_of_not_mem
    rw [literalProgram_support,hadamards_wires]
    exact hbank
  have hadj : ∀ start,readOnlyProgram known (literalProgram (n:=n) (s:=start) (Circuit.adjoint ((hotBank hot).map Gate.H))) := by
    intro start
    apply readOnlyProgram_of_not_mem
    rw [literalProgram_support,hadamards_adjoint_wires]
    exact fun h => hbank (List.mem_reverse.mp h)
  simp only [fixupProgram,readOnlyProgram_append,readOnlyProgram_cast]
  refine ⟨readOnlyProgram_of_not_mem known _ (literalProgram_noRoot known _ _ hprep hn),
    hhad _,recordLookupProgram_readOnly known _ scratch _ base (Nat.le_refl base) hs ?_
      (recordUnaryOps_readOnly known tree root paths hb hp),hadj _,readOnlyProgram_of_not_mem known _ ?_,?_⟩
  · intro p h
    have ht := phasePorts_targets hot (data.zip refs) p h
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp ht
    exact hi ▸ hh i
  · exact fun h => hn (herase _ h)
  · apply readOnlyProgram_of_not_mem
    rw [literalProgram_support]
    simpa [circuitWires,gateWires,eq_comm] using hh 0


theorem measuredClear7_readOnly {n} (known : Wire) (data : List (ClearPort n))
    (low : Fin 7 → Wire) (hot : Fin 128 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire) (start : Nat)
    (hl : ∀ i,low i≠known) (hh : ∀ i,hot i≠known) (hs : scratch≠known)
    (hb : ∀ w∈tree.indexWires,w≠known) (hp : ∀ w∈paths,w≠known)
    (hd : ∀ p∈data,p.target≠known) :
    readOnlyProgram known (measuredClear data low hot tree root scratch paths start) := by
  rw [measuredClear,readOnlyProgram_cast]
  apply measureThen_readOnly
  · intro cursor refs
    rw [readOnlyProgram_cast]
    exact fixupProgram7_readOnly known data refs low hot tree root scratch paths hl hh hs hb hp
  · intro w hw
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hw
    exact hd p hp


open WEX PathShare

theorem readOnlyProgram_naiveCast {n a b c} (root : Wire) (p : Straight n a b) (h : b=c) :
    readOnlyProgram root (NaiveChallenge.castFinish h p) ↔ readOnlyProgram root p := by subst c; rfl

theorem literal_translate_readOnly {n} (root : Wire) (p : ECDSAAdd.Program) (start : Nat)
    (h : root∉ECDSAAdd.wires p) : readOnlyProgram root (Bridge.translate (literalT (n:=n) p) start) := by
  apply readOnlyProgram_of_not_mem
  have hs := literal_translate_support (n:=n) p (ECDSAAdd.wires p).toList (by simp) start
  intro hm
  exact h (Finset.mem_toList.mp (hs hm))

theorem literalFixed_readOnly {n} (root : Wire) (p : ECDSAAdd.Program) (m : Nat)
    (hm : Bridge.tmplMeas (literalT (n:=n) p)=m) (start : Nat) (h : root∉ECDSAAdd.wires p) :
    readOnlyProgram root (literalFixed p m hm start) := by
  rw [literalFixed,readOnlyProgram_naiveCast]
  exact literal_translate_readOnly root p start h

def codeReadOnly {n} (root : Wire) (code : WCode n) : Prop :=
  ∀ i∈code,match i with
  | .literal p => root∉ECDSAAdd.wires p
  | .lookup _ ports => root∉portTargets ports

theorem codeReadOnly_normalize {n} (root : Wire) (code : WCode n) (h : codeReadOnly root code) :
    codeReadOnly root (normalizeW code) := by
  intro i hi
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
  have hh := h j hj
  cases j <;> simpa [normalizeWInstr,ECDSAAdd.Baselines.normalize_wires] using hh

theorem codeReadOnly_placed {n} (bits paths : List Wire) (root : Wire) (code : WCode n)
    (h : ∀ i∈code,PlacedPair bits paths root i) : codeReadOnly root code := by
  intro i hi
  have hh := h i hi
  cases i with
  | literal p => exact hh root (by simp)
  | lookup control ports => exact fun hm => List.disjoint_left.mp hh.2.2.2 (by simp) hm

theorem codeReadOnly_litAvoid {n} (bits : List Wire) (code : WCode n) (h : LitAvoid bits code) :
    codeReadOnly windowRoot code := by
  intro i hi
  obtain ⟨p,rfl,hp⟩ := h i hi
  exact hp windowRoot (by simp)

theorem portLeaf_readOnly {n} (root : Wire) (ports : List (LookupPort n))
    (h : root∉portTargets ports) (label : Nat) (control : Wire) :
    ∀ g∈portLeaf ports label control,readOnlyTemplate root g := by
  intro g hg
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hg
  change p.target≠root
  intro he
  exact h (List.mem_map.mpr ⟨p,hp,he⟩)

theorem compile_readOnly {n} (bits paths : List Wire) (root : Wire) (code : WCode n)
    (hb : root∉bits) (hp : root∉paths) (hn : bits.Nodup) (hc : codeReadOnly root code) (start : Nat) :
    readOnlyProgram root (WEX.compile bits paths root code start) := by
  induction code generalizing start with
  | nil => trivial
  | cons i code ih =>
    have hh := hc i (by simp)
    have ht (j : Nat) := ih (fun i hi => hc i (by simp [hi])) j
    cases i with
    | literal p =>
      rw [WEX.compile,readOnlyProgram_naiveCast,readOnlyProgram_append]
      exact ⟨literal_translate_readOnly root p start hh,ht _⟩
    | lookup control ports =>
      rw [WEX.compile,readOnlyProgram_naiveCast,readOnlyProgram_append]
      refine ⟨lookupProgram_readOnly root _ start ?_,ht _⟩
      apply unaryOps_readOnly root (portLeaf ports) (tableAddressTree bits 0 1)
        (lookupRoot root control) paths (portLeaf_readOnly root ports hh)
      · intro w hw he
        subst w
        apply hb
        rw [←tableAddressTree_index bits 0 1 hn]
        exact List.mem_dedup.mpr hw
      · intro w hw he
        exact hp (he ▸ hw)


theorem codeReadOnly_subset {n} (root : Wire) (small big : WCode n)
    (h : small⊆big) (hc : codeReadOnly root big) : codeReadOnly root small :=
  fun i hi => hc i (h hi)

theorem clearP8_readOnly {n} (B : PathShare.Bank) (hB : WideBank8.BankOK B)
    (site : WEXUnlookup.MaskedSite n) (hk : WEXUnlookup.SiteKind site)
    (hp : windowRoot∉B.paths) (ht : windowRoot∉portTargets site.ports) (start : Nat) :
    readOnlyProgram windowRoot (WideBank8.clearP B site start) := by
  rw [WideBank8.clearP]
  apply measuredClear8_readOnly windowRoot _ _ _ _ _ _ _ _
  · intro i
    simp only [WideBank8.low8,windowRoot]
    dsimp only [Wire] at *
    omega
  · intro i he
    exact ht (he ▸ WideBank8.kind_hot8 site hk i)
  · decide
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

theorem blockProg8_readOnly {n} (B : PathShare.Bank) (hB : WideBank8.BankOK B)
    (hb : windowRoot∉B.bits) (hp : windowRoot∉B.paths) (hn : B.bits.Nodup)
    (b : WEXUnlookup.Block2 n) (hg : PathShare.BlockGeoP2 B b) (start : Nat) :
    readOnlyProgram windowRoot (WideBank8.blockProgP2 B b start) := by
  cases b with
  | plain code =>
    exact compile_readOnly B.bits B.paths windowRoot (normalizeW code) hb hp hn
      (codeReadOnly_normalize windowRoot code (codeReadOnly_litAvoid B.bits code hg)) start
  | unit u =>
    have hall : codeReadOnly windowRoot u.code := codeReadOnly_placed _ _ _ _ hg.placed
    have hpre : codeReadOnly windowRoot u.pre := codeReadOnly_subset _ _ _ (List.subset_append_left _ _) hall
    have ht : windowRoot∉portTargets u.clear.ports :=
      hall (.lookup (some u.clear.guard) u.clear.ports) (by simp [WEXUnlookup.UnitSite.code])
    rw [WideBank8.blockProgP2,readOnlyProgram_cast,readOnlyProgram_append]
    exact ⟨compile_readOnly B.bits B.paths windowRoot _ hb hp hn
      (codeReadOnly_normalize _ _ hpre) start,clearP8_readOnly B hB u.clear hg.site.kind hp ht _⟩

theorem programP8_readOnly {n} (B : PathShare.Bank) (hB : WideBank8.BankOK B)
    (hb : windowRoot∉B.bits) (hp : windowRoot∉B.paths) (hn : B.bits.Nodup)
    (code : WEXUnlookup.Code2 n) (hg : ∀ b∈code,PathShare.BlockGeoP2 B b) (start : Nat) :
    readOnlyProgram windowRoot (WideBank8.programP2 B code start) := by
  induction code generalizing start with
  | nil => trivial
  | cons b code ih =>
    rw [WideBank8.programP2,readOnlyProgram_cast,readOnlyProgram_append]
    exact ⟨blockProg8_readOnly B hB hb hp hn b (hg b (by simp)) start,
      ih (fun x hx => hg x (by simp [hx])) _⟩


open WideBank8.Fast16
attribute [local irreducible] readOnlyProgram

namespace Wide8_three
variable {n : Nat} (f : WideBank8.Fast16.FastSite n) (hg : WideBank8.Fast16.FastGeometry f)
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
  exact compile_readOnly WideBank8.Fast16.windowBits WideBank8.Fast16.pathBank windowRoot _ (by decide) (by decide) (by decide)
    (codeReadOnly_normalize _ _ (codeReadOnly_placed _ _ _ _ (FastSite.arith_pair f hg))) start

theorem gclear_readOnly (start : Nat) : readOnlyProgram windowRoot (f.gclearProgram start) := by
  rw [FastSite.gclearProgram]
  apply measuredClear8_readOnly windowRoot _ _ _ _ _ _ _ _
  · intro i
    simp only [WideBank8.low8,windowRoot]
    dsimp only [Wire] at *
    omega
  · intro i he
    have hb := FastSite.hot_bound f hg i
    rw [he] at hb
    dsimp only [windowRoot,Wire] at hb
    omega
  · decide
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
    arith_readOnly f hg _⟩,clearP8_readOnly WideBank8.Fast16.bank15 WideBank8.Fast16.bank15_ok f.site hg.site.kind (by decide) ht _⟩

end Wide8_three

namespace Wide8_one
variable {n : Nat} (f : WideBank8.Fast16.FastSite1 n) (hg : WideBank8.Fast16.FastGeometry1 f)
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
  exact compile_readOnly WideBank8.Fast16.windowBits WideBank8.Fast16.pathBank windowRoot _ (by decide) (by decide) (by decide)
    (codeReadOnly_normalize _ _ (codeReadOnly_placed _ _ _ _ (FastSite1.arith_pair f hg))) start

theorem gclear_readOnly (start : Nat) : readOnlyProgram windowRoot (f.gclearProgram start) := by
  rw [FastSite1.gclearProgram]
  apply measuredClear8_readOnly windowRoot _ _ _ _ _ _ _ _
  · intro i
    simp only [WideBank8.low8,windowRoot]
    dsimp only [Wire] at *
    omega
  · intro i he
    have hb := FastSite1.hot_bound f hg i
    rw [he] at hb
    dsimp only [windowRoot,Wire] at hb
    omega
  · decide
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
    arith_readOnly f hg _⟩,clearP8_readOnly WideBank8.Fast16.bank15 WideBank8.Fast16.bank15_ok f.site hg.site.kind (by decide) ht _⟩

end Wide8_one


end
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration RootPass
open AndGadget WEXCredit ConditionalCatalyst MeasuredClear WEX WEXUnlookup PathShare WideBank8.Fast16

noncomputable section
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
theorem readOnly_safe (root : Wire) (g : Gate) (h : readOnly root g) : RootPass.safe root g := by
  cases g <;> first | exact h | trivial


theorem readOnlyProgram_safe {n s e} (root : Wire) (p : Straight n s e)
    (h : readOnlyProgram root p) : RootPass.safeProgram root p := by
  induction p with
  | done => trivial
  | gate g p ih =>
    exact ⟨by cases g <;> exact readOnly_safe root _ h.1,ih h.2⟩
  | recordGate i v g p ih => exact ⟨readOnly_safe root _ h.1,ih h.2⟩
  | measure w p ih => exact ⟨h.1,ih h.2⟩


theorem aligned_pull {A B C : Type*} {E : A→B→Prop} {R : B→C→Prop} {S : A→C→Prop}
    {xs : List A} {ys : List B} {cs : List C} (he : List.Forall₂ E xs ys)
    (hr : List.Forall₂ R ys cs) (h : ∀ a b c,E a b→R b c→S a c) : List.Forall₂ S xs cs := by
  induction he generalizing cs with
  | nil => cases hr; exact .nil
  | cons hab ht ih => cases hr with
    | cons hbc ht' => exact .cons (h _ _ _ hab hbc) (ih ht')

attribute [local irreducible] readOnlyProgram
namespace SeedWide
open WideBank8.Fast16

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
    | unit u => exact blockProg8_readOnly WideBank8.Fast16.bank15 WideBank8.Fast16.bank15_ok (by decide) (by decide) (by decide) (.unit u) hg start
  | fast f => exact Wide8_three.fast_readOnly f hg start
  | fast1 f => exact Wide8_one.fast_readOnly f hg start


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
    (hsafe : ∀ s, Valid s → Safe2 read (tableAddressValue WideBank8.Fast16.windowBits s) (fforget code) ⟨false,s⟩)
    (hclean : ∀ s, Valid s → FCodeClean read (tableAddressValue WideBank8.Fast16.windowBits s) code ⟨false,s⟩)
    (hrun : ∀ s, Valid s → ∀ m,
      ECDSAAdd.run (reference2 read (tableAddressValue WideBank8.Fast16.windowBits s) (fforget code)) m ⟨false,s⟩ = ⟨false,result s⟩)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((program code start).instantiate read history)
      (Finsupp.lmapDomain ℂ ℂ result) (fun s => s windowRoot = true ∧ Valid s) := by
  obtain ⟨cs, aligned, mass⟩ := source_sim read code hg
  refine ⟨cs, ?_, mass⟩
  rw [program_run]
  apply aligned.imp
  intro b c hb s hs
  obtain ⟨m, _, h⟩ := hb
  have he := h (tableAddressValue WideBank8.Fast16.windowBits s) ⟨false,s⟩ ⟨rfl, hs.1⟩ (hclean s hs.2) (hsafe s hs.2)
  rw [Bridge.signedKet_false, hrun s hs.2 m, Bridge.signedKet_false] at he
  simpa [ket] using he



theorem old_block_credit {n} (b : FBlock2 n) (hg : FBlockGeo b) (start : Nat) :
    ProgramCredit (fblockProg b start) (fblockTP b) := by
  have hz : residue (fblockProg b start)=0 := by
    cases b with
    | std b => exact WideBank8.blockH_residue WideBank8.Fast16.bank15 b start
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
    (program code start).gateSlots ≤ WideBank8.codeSP2 WideBank8.Fast16.bank15 (fforget code) + fslack code := by
  induction code generalizing start with
  | nil => simp [program, frecs, fslack, Straight.gateSlots, WideBank8.codeSP2]
  | cons b code ih =>
    have ih' := ih (fun d hd => hg d (by simp [hd])) (start + fblockRec b)
    have hb : (blockProgram b start).gateSlots ≤ WideBank8.blockSP2 WideBank8.Fast16.bank15 b.forget + fblockSlack b := by
      rw [blockProgram_slots]
      have hgb := hg b (by simp)
      cases b with
      | std b =>
        rw [show fblockProg (.std b) 0 = WideBank8.blockProgH WideBank8.Fast16.bank15 b 0 from rfl]
        exact WideBank8.blockH_slots WideBank8.Fast16.bank15 b (WideBank8.geo_lay2 WideBank8.Fast16.bank15 WideBank8.Fast16.bank15_ok b hgb) 0
      | fast f => exact f.fast_slots hgb 0
      | fast1 f => exact f.fast_slots hgb 0
    rw [program, castFinish_gateSlots, Straight.gateSlots_append]
    simp only [fforget_cons, WideBank8.codeSP2, fslack]
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

open WideBank8.Fast16.Tight
theorem program_support (code : FCode2 65536) (hg : ∀ b ∈ code, FBlockGeo b)
    (hlit : ∀ p, WInstr.literal p ∈ erase2 (fforget code) → ∀ w ∈ ECDSAAdd.wires p,
      w = hostWire ∨ w = hostWire2 ∨ w = hostWire3 ∨ w ∈ WideBank8.Fast16.Tight.support)
    (hstrict : ∀ b ∈ code, ∀ p, WInstr.literal p ∈ b.forget.code →
      (hostWire ∈ ECDSAAdd.wires p ∨ hostWire2 ∈ ECDSAAdd.wires p ∨ hostWire3 ∈ ECDSAAdd.wires p) →
      ∃ c, b = .std (.plain c))
    (hctl : ∀ b ∈ code, ∀ c, b = .std (.plain c) →
      hostWire2 ∈ ECDSAAdd.wires (litProg c) → hostCtl ∉ ECDSAAdd.wires (litProg c))
    (hctl3 : ∀ b ∈ code, ∀ c, b = .std (.plain c) →
      hostWire3 ∈ ECDSAAdd.wires (litProg c) → hostCtl3 ∉ ECDSAAdd.wires (litProg c))
    (hlook : ∀ c ps, WInstr.lookup c ps ∈ erase2 (fforget code) →
      (∀ q ∈ c, q ∈ WideBank8.Fast16.Tight.support) ∧ portTargets ps ⊆ WideBank8.Fast16.Tight.support)
    (hgarb : ∀ b ∈ code, NoHost3 b)
    (start : Nat) : ChallengeMigration.straightWires (program code start) ⊆ WideBank8.Fast16.Tight.support := by
  induction code generalizing start with
  | nil => simp [program, frecs, ChallengeMigration.straightWires]
  | cons b code ih =>
    rw [program, straightWires_castFinish, straightWires_append]
    exact List.append_subset.mpr ⟨(blockProgram_support b start).trans (WideBank8.Fast16.Tight.fblock_support b (hg b (by simp))
      (fun p hm => hlit p (by simp [erase2_cons, hm])) (hstrict b (by simp)) (hctl b (by simp)) (hctl3 b (by simp))
      (fun c ps hm => hlook c ps (by simp [erase2_cons, hm])) (hgarb b (by simp)) 0),
      ih (fun d hd => hg d (by simp [hd])) (fun p hm => hlit p (by simp [erase2_cons, hm]))
        (fun d hd => hstrict d (by simp [hd])) (fun d hd => hctl d (by simp [hd])) (fun d hd => hctl3 d (by simp [hd]))
        (fun c ps hm => hlook c ps (by simp [erase2_cons, hm])) (fun d hd => hgarb d (by simp [hd])) _⟩





theorem fixup8_hits {n base} (known : Wire) (data : List (ClearPort n)) (refs : List (Fin base))
    (low : Fin 8 → Wire) (hot : Fin 256 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire)
    (hl : ∀ i,low i≠known) (hh : ∀ i,hot i≠known) :
    literalHits known (MeasuredClear.fixupProgram8 data refs low hot tree root scratch paths)=
      recordOpsHits known (recordUnaryOps tree root paths) := by
  obtain ⟨hn,hprep,_⟩ := fixup8_noRoot_parts (n:=n) known low hot hl hh
  have hz (start : Nat) : literalHits known (literalProgram (n:=n) (s:=start) (MeasuredClear.hotPrepare8 low hot))=0 :=
    literalHits_zero_of_not_mem known _ (literalProgram_noRoot known _ _ hprep hn)
  simp only [MeasuredClear.fixupProgram8,literalHits_append,literalHits_cast,literalHits_recordLookupProgram,
    literalHits_hadamards,literalHits_adjoint_hadamards,literalHits_eraseNetwork,literalHits_X,hz,
    zero_add,add_zero]

theorem measured8_hits {n} (known : Wire) (data : List (ClearPort n))
    (low : Fin 8 → Wire) (hot : Fin 256 → Wire) (tree : UnaryActionTree)
    (root scratch : Wire) (paths : List Wire) (start : Nat)
    (hl : ∀ i,low i≠known) (hh : ∀ i,hot i≠known) :
    literalHits known (MeasuredClear.measuredClear8 data low hot tree root scratch paths start)=
      recordOpsHits known (recordUnaryOps tree root paths) := by
  rw [MeasuredClear.measuredClear8,literalHits_cast]
  apply literalHits_measureThen
  intro cursor refs
  rw [literalHits_cast]
  exact fixup8_hits known data refs low hot tree root scratch paths hl hh



theorem record_root_hit_lower (root bit path : Wire) (zero one : UnaryActionTree) (rest : List Wire) :
    1≤RootPass.recordOpsHits root (recordUnaryOps (.node bit zero one) root (path::rest)) := by
  simp only [recordUnaryOps,RootPass.recordOpsHits,List.map_append,List.sum_append,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,RootPass.recordOpHits,
    computeZeroAnd,RootPass.hit,true_or,if_true]
  omega

theorem clearP_root_hit {n} (site : MaskedSite n) (hk : SiteKind site)
    (he : site.guard=windowRoot) (ht : windowRoot∉portTargets site.ports) (start : Nat) :
    1≤literalHits windowRoot (WideBank8.clearP WideBank8.Fast16.bank15 site start) := by
  rw [WideBank8.clearP,measured8_hits windowRoot _ _ _ _ _ _ _ _]
  · rw [he]
    exact record_root_hit_lower windowRoot 863 14832 _ _ _
  · intro i
    simp only [WideBank8.low8,windowRoot]
    dsimp only [Wire] at *
    omega
  · intro i he
    exact ht (he ▸ WideBank8.kind_hot8 site hk i)


theorem unit_root_hits {n} (u : UnitSite n) (hg : UnitGeoP WideBank8.Fast16.bank15 u)
    (he : u.clear.guard=windowRoot) (start : Nat) :
    1≤literalHits windowRoot (fblockProg (.std (.unit u)) start) := by
  have hall := codeReadOnly_placed WideBank8.Fast16.windowBits WideBank8.Fast16.pathBank windowRoot u.code hg.placed
  have ht : windowRoot∉portTargets u.clear.ports :=
    hall (.lookup (some u.clear.guard) u.clear.ports) (by simp [UnitSite.code])
  have hc := clearP_root_hit u.clear hg.site.kind he ht (start+codeRecords WideBank8.Fast16.bank15.bits WideBank8.Fast16.bank15.paths windowRoot (normalizeW u.pre))
  change 1≤literalHits windowRoot (WideBank8.blockProgP2 WideBank8.Fast16.bank15 (.unit u) start)
  rw [WideBank8.blockProgP2,literalHits_cast,literalHits_append]
  omega

theorem gclear_three_root_hits {n} (f : WideBank8.Fast16.FastSite n) (hg : WideBank8.Fast16.FastGeometry f)
    (he : f.site.guard=windowRoot) (start : Nat) :
    1≤literalHits windowRoot (f.gclearProgram start) := by
  rw [FastSite.gclearProgram,measured8_hits windowRoot _ _ _ _ _ _ _ _]
  · rw [he]
    exact record_root_hit_lower windowRoot 863 14832 _ _ _
  · intro i
    simp only [WideBank8.low8,windowRoot]
    dsimp only [Wire] at *
    omega
  · intro i he
    have hb := FastSite.hot_bound f hg i
    rw [he] at hb
    dsimp only [windowRoot,Wire] at hb
    omega

theorem fast_three_root_hits {n} (f : WideBank8.Fast16.FastSite n) (hg : WideBank8.Fast16.FastGeometry f)
    (he : f.site.guard=windowRoot) (start : Nat) :
    2≤literalHits windowRoot (f.fastProgram start) := by
  have ht : windowRoot∉portTargets f.site.ports :=
    fun h=>Wide8_three.regs_noRoot f hg (List.mem_append_left _ h)
  rw [FastSite.fastProgram,literalHits_cast]
  simp only [literalHits_append]
  have hG := gclear_three_root_hits f hg he (start+codeRecords WideBank8.Fast16.selBits WideBank8.Fast16.selPaths windowRoot f.selCode+0)
  have hC := clearP_root_hit f.site hg.site.kind he ht (start+codeRecords WideBank8.Fast16.selBits WideBank8.Fast16.selPaths windowRoot f.selCode+0+(clearData f.garbPorts).length+(recordMeasurements (recordUnaryOps (tableAddressTree WideBank8.Fast16.high 0 1) f.site.guard WideBank8.Fast16.bankHp)+255)+codeRecords WideBank8.Fast16.windowBits WideBank8.Fast16.pathBank windowRoot (normalizeW f.site.arithmetic))
  omega

theorem gclear_one_root_hits {n} (f : WideBank8.Fast16.FastSite1 n) (hg : WideBank8.Fast16.FastGeometry1 f)
    (he : f.site.guard=windowRoot) (start : Nat) :
    1≤literalHits windowRoot (f.gclearProgram start) := by
  rw [FastSite1.gclearProgram,measured8_hits windowRoot _ _ _ _ _ _ _ _]
  · rw [he]
    exact record_root_hit_lower windowRoot 863 14832 _ _ _
  · intro i
    simp only [WideBank8.low8,windowRoot]
    dsimp only [Wire] at *
    omega
  · intro i he
    have hb := FastSite1.hot_bound f hg i
    rw [he] at hb
    dsimp only [windowRoot,Wire] at hb
    omega

theorem fast_one_root_hits {n} (f : WideBank8.Fast16.FastSite1 n) (hg : WideBank8.Fast16.FastGeometry1 f)
    (he : f.site.guard=windowRoot) (start : Nat) :
    2≤literalHits windowRoot (f.fastProgram start) := by
  have ht : windowRoot∉portTargets f.site.ports :=
    fun h=>Wide8_one.regs_noRoot f hg (List.mem_append_left _ h)
  rw [FastSite1.fastProgram,literalHits_cast]
  simp only [literalHits_append]
  have hG := gclear_one_root_hits f hg he (start+codeRecords WideBank8.Fast16.selBits1 WideBank8.Fast16.selPaths1 windowRoot f.selCode+0)
  have hC := clearP_root_hit f.site hg.site.kind he ht (start+codeRecords WideBank8.Fast16.selBits1 WideBank8.Fast16.selPaths1 windowRoot f.selCode+0+(clearData f.garbPorts).length+(recordMeasurements (recordUnaryOps (tableAddressTree WideBank8.Fast16.high 0 1) f.site.guard WideBank8.Fast16.bankHp)+255)+codeRecords WideBank8.Fast16.windowBits WideBank8.Fast16.pathBank windowRoot (normalizeW f.site.arithmetic))
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


theorem unit_lookup_floor {n} (u : UnitSite n) (hg : UnitGeoP WideBank8.Fast16.bank15 u) (start : Nat) :
    lookupCount windowRoot u.pre+(if u.clear.guard=windowRoot then 1 else 0)≤
      literalHits windowRoot (fblockProg (.std (.unit u)) start) := by
  have hall := codeReadOnly_placed WideBank8.Fast16.windowBits WideBank8.Fast16.pathBank windowRoot u.code hg.placed
  have ht : windowRoot∉portTargets u.clear.ports :=
    hall (.lookup (some u.clear.guard) u.clear.ports) (by simp [UnitSite.code])
  have hp := compile_lookup_lower windowRoot WideBank8.Fast16.bank15.bits WideBank8.Fast16.bank15.paths
    (by decide) (by decide) (normalizeW u.pre) start
  rw [lookupCount_normalize] at hp
  have hc : (if u.clear.guard=windowRoot then 1 else 0)≤literalHits windowRoot
      (WideBank8.clearP WideBank8.Fast16.bank15 u.clear
        (start+codeRecords WideBank8.Fast16.bank15.bits WideBank8.Fast16.bank15.paths windowRoot (normalizeW u.pre))) := by
    by_cases h : u.clear.guard=windowRoot
    · rw [if_pos h]
      exact clearP_root_hit u.clear hg.site.kind h ht _
    · rw [if_neg h]
      exact Nat.zero_le _
  change _≤literalHits windowRoot (WideBank8.blockProgP2 WideBank8.Fast16.bank15 (.unit u) start)
  rw [WideBank8.blockProgP2,literalHits_cast,literalHits_append]
  exact Nat.add_le_add hp hc

theorem fast_three_lookup_floor {n} (f : WideBank8.Fast16.FastSite n) (hg : WideBank8.Fast16.FastGeometry f) (start : Nat) :
    lookupCount windowRoot f.selCode+lookupCount windowRoot f.site.arithmetic+
      (if f.site.guard=windowRoot then 2 else 0)≤literalHits windowRoot (f.fastProgram start) := by
  have hS : lookupCount windowRoot f.selCode≤literalHits windowRoot (f.selProgram start) := by
    rw [FastSite.selProgram]
    exact compile_lookup_lower windowRoot WideBank8.Fast16.selBits WideBank8.Fast16.selPaths (by decide) (by decide) _ start
  have hA (j : Nat) : lookupCount windowRoot f.site.arithmetic≤literalHits windowRoot (f.arithProgram j) := by
    rw [FastSite.arithProgram]
    have h := compile_lookup_lower windowRoot WideBank8.Fast16.windowBits WideBank8.Fast16.pathBank
      (by decide) (by decide) (normalizeW f.site.arithmetic) j
    simpa only [lookupCount_normalize] using h
  have hAr := hA (start+codeRecords WideBank8.Fast16.selBits WideBank8.Fast16.selPaths windowRoot f.selCode+0+(clearData f.garbPorts).length+(recordMeasurements (recordUnaryOps (tableAddressTree WideBank8.Fast16.high 0 1) f.site.guard WideBank8.Fast16.bankHp)+255))
  rw [FastSite.fastProgram,literalHits_cast]
  simp only [literalHits_append]
  by_cases h : f.site.guard=windowRoot
  · rw [if_pos h]
    have ht : windowRoot∉portTargets f.site.ports :=
      fun hm=>Wide8_three.regs_noRoot f hg (List.mem_append_left _ hm)
    have hG := gclear_three_root_hits f hg h (start+codeRecords WideBank8.Fast16.selBits WideBank8.Fast16.selPaths windowRoot f.selCode+0)
    have hC := clearP_root_hit f.site hg.site.kind h ht (start+codeRecords WideBank8.Fast16.selBits WideBank8.Fast16.selPaths windowRoot f.selCode+0+(clearData f.garbPorts).length+(recordMeasurements (recordUnaryOps (tableAddressTree WideBank8.Fast16.high 0 1) f.site.guard WideBank8.Fast16.bankHp)+255)+codeRecords WideBank8.Fast16.windowBits WideBank8.Fast16.pathBank windowRoot (normalizeW f.site.arithmetic))
    omega
  · rw [if_neg h]
    omega

theorem fast_one_lookup_floor {n} (f : WideBank8.Fast16.FastSite1 n) (hg : WideBank8.Fast16.FastGeometry1 f) (start : Nat) :
    lookupCount windowRoot f.selCode+lookupCount windowRoot f.site.arithmetic+
      (if f.site.guard=windowRoot then 2 else 0)≤literalHits windowRoot (f.fastProgram start) := by
  have hS : lookupCount windowRoot f.selCode≤literalHits windowRoot (f.selProgram start) := by
    rw [FastSite1.selProgram]
    exact compile_lookup_lower windowRoot WideBank8.Fast16.selBits1 WideBank8.Fast16.selPaths1 (by decide) (by decide) _ start
  have hA (j : Nat) : lookupCount windowRoot f.site.arithmetic≤literalHits windowRoot (f.arithProgram j) := by
    rw [FastSite1.arithProgram]
    have h := compile_lookup_lower windowRoot WideBank8.Fast16.windowBits WideBank8.Fast16.pathBank
      (by decide) (by decide) (normalizeW f.site.arithmetic) j
    simpa only [lookupCount_normalize] using h
  have hAr := hA (start+codeRecords WideBank8.Fast16.selBits1 WideBank8.Fast16.selPaths1 windowRoot f.selCode+0+(clearData f.garbPorts).length+(recordMeasurements (recordUnaryOps (tableAddressTree WideBank8.Fast16.high 0 1) f.site.guard WideBank8.Fast16.bankHp)+255))
  rw [FastSite1.fastProgram,literalHits_cast]
  simp only [literalHits_append]
  by_cases h : f.site.guard=windowRoot
  · rw [if_pos h]
    have ht : windowRoot∉portTargets f.site.ports :=
      fun hm=>Wide8_one.regs_noRoot f hg (List.mem_append_left _ hm)
    have hG := gclear_one_root_hits f hg h (start+codeRecords WideBank8.Fast16.selBits1 WideBank8.Fast16.selPaths1 windowRoot f.selCode+0)
    have hC := clearP_root_hit f.site hg.site.kind h ht (start+codeRecords WideBank8.Fast16.selBits1 WideBank8.Fast16.selPaths1 windowRoot f.selCode+0+(clearData f.garbPorts).length+(recordMeasurements (recordUnaryOps (tableAddressTree WideBank8.Fast16.high 0 1) f.site.guard WideBank8.Fast16.bankHp)+255)+codeRecords WideBank8.Fast16.windowBits WideBank8.Fast16.pathBank windowRoot (normalizeW f.site.arithmetic))
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


theorem richFloor_concrete : richFloorSum WideBank8.Row16.code=8 := by decide

namespace Concrete
open Secp256k1 WideSigned
attribute [local irreducible] WideBank8.Row16.code WEXFast.rowCF WEXUnlookup.rowC
  Straight.instantiate AdaptiveCircuit.run

def rowProgram (start : Nat) : Straight 65536 start (start+1744532) :=
  castFinish (congrArg (fun m=>start+m) WideBank8.Row16.row_records)
    (SeedWide.program WideBank8.Row16.code start)

local notation "rowCredit" => (creditSum WideBank8.Row16.code)

theorem row_credit (start : Nat) : ProgramCredit (rowProgram start) rowCredit := by
  rw [rowProgram]
  exact credit_cast _ (program_credit _ WideBank8.Row16.geometry start)

theorem row_wellFormed (start : Nat) : (rowProgram start).WellFormed := by
  rw [rowProgram,castFinish_wellFormed]
  apply program_wellFormed _ WideBank8.Row16.geometry
  rw [WideBank8.Row16.forget]
  exact Geometry.row_physical .w16

theorem row_coherent (coeffs : Fin 65536→PointCoeff) (Q : Point)
    (hQ : order • Q=0) (hn : ∀ i,constantPoint Q (coeffs i)≠0)
    (start : Nat) (history : Fin start→Bool) :
    CoherentlyImplementsOn ((rowProgram start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (Add.update .w16 coeffs Q)) liveReady := by
  rw [rowProgram,castFinish_instantiate]
  have h := SeedWide.program_coherent (readConstant coeffs Q) WideBank8.Row16.code WideBank8.Row16.geometry liveReady (Add.update .w16 coeffs Q)
    (fun s hs => by rw [WideBank8.Row16.forget]; exact Rows.row_safe _ _ _ hQ hn _ s hs)
    (fun s hs => by
      rw [WideBank8.Row16.code]
      exact WideBank8.Row16.clean_lift coeffs Q _ _ (fun _ h => h) _
        (WEXFast.rowCF_clean (fun _ => coeffs (WideBank8.Row16.rows (tableAddressValue WideBank8.Fast16.windowBits s))) Q hQ
        (fun _ => hn _) _ s hs) (fun v hv => hs.2.1 v (List.mem_append_right _ hv)))
    (fun s hs m => by rw [WideBank8.Row16.forget]; exact Rows.row_run _ _ _ hQ hn _ s hs m) start history
  obtain ⟨cs,aligned,mass⟩ := h
  exact ⟨cs,aligned.imp (fun b c hb s hs=>hb s ⟨hs.2.2,hs⟩),mass⟩

theorem row_support (start : Nat) :
    ChallengeMigration.straightWires (rowProgram start) ⊆ WideBank8.Fast16.Tight.support := by
  rw [rowProgram,straightWires_castFinish]
  exact program_support WideBank8.Row16.code WideBank8.Row16.geometry
    WideBank8.Fast16.Tight.row_literals WideBank8.Row16.strict WideBank8.Row16.ctl WideBank8.Row16.ctl3
    WideBank8.Fast16.Tight.row_lookups WideBank8.Fast16.Tight.row_nohost start

theorem row_slots (start : Nat) : (rowProgram start).gateSlots≤2475408934 := by
  rw [rowProgram,castFinish_gateSlots]
  have h := program_slots WideBank8.Row16.code WideBank8.Row16.geometry start
  rw [WideBank8.Row16.forget,WideBank8.Row16.slack] at h
  have hn : WideBank8.codeSP2 WideBank8.Fast16.bank15 (Geometry.row .w16)≤2139852992 :=
    WideBank8.Row16.standard_slots.trans (by decide)
  omega


def rowSource (coeffs : Fin 65536→PointCoeff) (Q : Point) : AdaptiveCircuit :=
  SeedWide.source (readConstant coeffs Q) WideBank8.Row16.code

theorem row_run (read : ConstantBit 65536→Bool) (start : Nat) (hist : Fin start→Bool) :
    ((rowProgram start).instantiate read hist).run=(SeedWide.source read WideBank8.Row16.code).run := by
  rw [rowProgram,castFinish_instantiate,program_run]

theorem row_source_coherent (coeffs : Fin 65536→PointCoeff) (Q : Point)
    (hQ : order • Q=0) (hn : ∀ i,constantPoint Q (coeffs i)≠0) :
    CoherentlyImplementsOn (rowSource coeffs Q)
      (Finsupp.lmapDomain ℂ ℂ (Add.update .w16 coeffs Q)) liveReady := by
  obtain ⟨cs,aligned,mass⟩ := row_coherent coeffs Q hQ hn 0 Fin.elim0
  exact ⟨cs,by simpa only [row_run,rowSource] using aligned,mass⟩

def records : Nat := 1745044
abbrev credit : Nat := 2*Body.signCredit+rowCredit

def signedProgram (start : Nat) : Straight 65536 start (start+1745044) :=
  castFinish (congrArg (fun m=>start+m) (by decide : 512+1744532=1745044))
    (Frame16.program 1744532 rowProgram start)

attribute [local irreducible] signedProgram rowProgram Frame16.program ProgramCredit Nat.add Nat.mul Straight.WellFormed
def source (coeffs : Fin 65536 → PointCoeff) (Q : Point) : AdaptiveCircuit :=
  (Body.prefixSource .w16).seq ((Body.signSource.seq ((rowSource coeffs Q).seq Body.signSource)).seq
    (Body.suffixSource .w16))

theorem source_coherent (coeffs : Fin 65536 → PointCoeff) (Q : Point)
    (hQ : order • Q = 0) (hn : ∀ i, constantPoint Q (coeffs i) ≠ 0) :
    CoherentlyImplementsOn (source coeffs Q)
      (Finsupp.lmapDomain ℂ ℂ (Body.state .w16 coeffs Q)) windowReady := by
  have hs : CoherentlyImplementsOn Body.signSource (Finsupp.lmapDomain ℂ ℂ signPointState) liveReady :=
    fastWindowSign_coherent
  have ha := composeCoherent hs (row_source_coherent coeffs Q hQ hn) (fun s h => liveReady_write _ s h)
  have hb := composeCoherent ha hs (fun s h => liveReady_write _ _ (liveReady_write _ s h))
  have hc := composeCoherent (Body.prefix_coherent .w16) hb
    (fun s h => Body.prepare_live .w16 _ (rootFlip_live s h))
  have hd := composeCoherent hc (Body.suffix_coherent .w16) (fun _ _ => trivial)
  simpa only [source, Body.state, adaptive_seq_assoc] using hd

theorem run (coeffs : Fin 65536 → PointCoeff) (Q : Point) (start : Nat) (history : Fin start → Bool) :
    ((signedProgram start).instantiate (readConstant coeffs Q) history).run = (source coeffs Q).run := by
  rw [signedProgram, castFinish_instantiate]
  have hr (j : Nat) (hist : Fin j → Bool) :
      ((rowProgram j).instantiate (readConstant coeffs Q) hist).run = (rowSource coeffs Q).run := by
    rw [row_run]
    rfl
  simpa only [source] using Frame16.run 1744532 rowProgram (rowSource coeffs Q)
    (readConstant coeffs Q) hr start history


theorem coherent (coeffs : Fin 65536 → PointCoeff) (Q : Point)
    (hQ : order • Q = 0) (hn : ∀ i, constantPoint Q (coeffs i) ≠ 0)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((signedProgram start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (Body.state .w16 coeffs Q)) windowReady := by
  unfold CoherentlyImplementsOn
  rw [run]
  exact source_coherent coeffs Q hQ hn


def window : Single.Window 65536 := ⟨(Body.logicalBank .w16).reverse, 1745044, signedProgram⟩
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


theorem signed_credit (start : Nat) : ProgramCredit (signedProgram start) (2*Body.signCredit+rowCredit) := by
  rw [signedProgram]
  apply credit_cast
  exact Frame16.credit 1744532 rowCredit rowProgram row_credit start

theorem wellFormed (start : Nat) : (signedProgram start).WellFormed := by
  rw [signedProgram,castFinish_wellFormed]
  exact Frame16.wellFormed _ rowProgram row_wellFormed start

theorem signed_support (start : Nat) :
    ChallengeMigration.straightWires (signedProgram start) ⊆ WideBank8.Fast16.Tight.support := by
  rw [signedProgram,straightWires_castFinish]
  exact TightSupport.frame_support _ rowProgram row_support start

theorem packed_support (start : Nat) :
    ChallengeMigration.straightWires (relabelStraight TightSupport.compact (signedProgram start)) ⊆ List.range 1618 := by
  rw [straightWires_relabel]
  intro v hv
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv
  exact List.mem_range.mpr (TightSupport.compact_bound u (signed_support start hu))

theorem slots (start : Nat) : (signedProgram start).gateSlots≤2500000000 := by
  have hrow := row_slots (start+256)
  have hsign (j : Nat) : (Body.nProgram .w16 j).gateSlots≤300000 := by
    rw [Body.nProgram,reindexStraight_gateSlots,nFastProgram_slots]
    have h := literal_slot_bound (n:=32768) (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)
    rw [ECDSAAdd.Baselines.normalize_slots] at h
    have hmax := fastWindowSign_slots
    omega
  rw [signedProgram,castFinish_gateSlots,Frame16.slots]
  have h1 := hsign start
  have h2 := hsign (start+256+1744532)
  omega


open Single Single.Distribution
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



theorem row_savings : 8≤savedSum WideBank8.Row16.code := by
  have h := richFloorSum_lower WideBank8.Row16.code WideBank8.Row16.geometry
  rw [richFloor_concrete] at h
  exact h

theorem credit_bound : 2*Body.signCredit+rowCredit≤2344183 := by
  have hOld := WideBank8.Signed16.credit_bound
  have hBalance := credit_balance WideBank8.Row16.code WideBank8.Row16.geometry
  have hSaved := row_savings
  omega


end Concrete
end SeedWide
end
end ShorECDLP.Entrant.ConstRoot
