import ShorECDLP.Submission.Entrant.FusedRow14

/-! Lookup paths on idle dialog-pool wires.

The window lookups used a private bank of fifteen path wires. Those wires are idle while the
field arithmetic runs, and the dialog pool has wires that only the plain generic-branch arithmetic
uses, which starts and ends with a clean pool. This module compiles the same rows with such pool
wires as the lookup path bank.

The compile layer of `StackBase` asks every literal segment to avoid the path bank. Here a literal
segment only has to keep the root and the address bits. In exchange, the simulation asks for clean
paths before every lookup of the reference run (`PathsClean`), and the block layer asks for a clean
bank at the start of every masked site (`CodeClean`). Inside a masked site every instruction still
avoids the bank, so the bank stays clean through the load, the arithmetic and the measured clear. -/

namespace ShorECDLP.Entrant.PathShare
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-! ### Straight code with a shared path bank -/

/-- Literal segments may use the path bank; only the root and the address bits are frozen. -/
def LPlaced {n : Nat} (bits paths : List Wire) (root : Wire) : WInstr n → Prop
  | .literal p => ∀ w ∈ root :: bits, w ∉ ECDSAAdd.wires p
  | .lookup ctl ports => PlacedPair bits paths root (.lookup ctl ports)

def AddrValid (bits : List Wire) (root address : Nat) (st : ECDSAAdd.State) : Prop :=
  tableAddressValue bits st.basis = address ∧ st.basis root = true

/-- The path bank is clean before every lookup of the reference run. -/
def PathsClean {n : Nat} (read : ConstantBit n → Bool) (paths : List Wire) (address : Nat) :
    WCode n → ECDSAAdd.State → Prop
  | [], _ => True
  | .literal p :: code, st => ∀ m, PathsClean read paths address code (ECDSAAdd.run p m st)
  | .lookup c ps :: code, st => Clean paths st.basis ∧
      ∀ m, PathsClean read paths address code
        (ECDSAAdd.run ((portTemplate c ps address).instantiate read) m st)

theorem literal_addr {n : Nat} (p : ECDSAAdd.Program) (bits paths : List Wire) (root address : Nat)
    (hp : LPlaced (n := n) bits paths root (.literal p))
    (st : ECDSAAdd.State) (hs : AddrValid bits root address st) (m : List Bool) :
    AddrValid bits root address (ECDSAAdd.run p m st) := by
  have frame (w : Wire) (hw : w ∈ root :: bits) :
      (ECDSAAdd.run p m st).basis w = st.basis w :=
    ECDSAAdd.run_preserves_outside p m st w (hp w hw)
  refine ⟨?_, ?_⟩
  · rw [WEX.tableAddressValue_congr bits _ _ (fun w hw => frame w (by simp [hw]))]
    exact hs.1
  · rw [frame root (by simp)]
    exact hs.2

theorem pair_lookup_addr {n : Nat} (read : ConstantBit n → Bool)
    (control : Option Wire) (ports : List (LookupPort n)) (bits paths : List Wire)
    (root address : Nat) (hp : PlacedPair bits paths root (.lookup control ports))
    (st : ECDSAAdd.State) (hs : AddrValid bits root address st) :
    AddrValid bits root address
      ⟨st.phase, tableXorState (portMask read (ports.drop 258) address)
        (st.basis (lookupRoot root control))
        (tableXorState (portMask read (ports.take 258) address)
          (st.basis (lookupRoot root control)) st.basis)⟩ := by
  dsimp only [PlacedPair] at hp
  have frame (w : Wire) (hw : w ∈ root :: bits) :
      tableXorState (portMask read (ports.drop 258) address) (st.basis (lookupRoot root control))
        (tableXorState (portMask read (ports.take 258) address) (st.basis (lookupRoot root control)) st.basis) w =
        st.basis w := by
    have hd (v : Wire) (h : v ∈ portTargets ports) : v ≠ w := by
      intro e; subst v
      exact List.disjoint_left.mp hp.2.2.2 (by
        rcases List.mem_cons.mp hw with rfl | hw
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hw))) h
    have htake : w ∉ portMask read (ports.take 258) address := by
      intro h
      have h' := tableBitsMask_subset _ _ h
      rw [portTargets, List.map_take] at h'
      exact hd w (List.take_subset _ _ h') rfl
    have hdrop : w ∉ portMask read (ports.drop 258) address := by
      intro h
      have h' := tableBitsMask_subset _ _ h
      rw [portTargets, List.map_drop] at h'
      exact hd w (List.drop_subset _ _ h') rfl
    rw [tableXorState_outside _ _ _ _ hdrop, tableXorState_outside _ _ _ _ htake]
  refine ⟨?_, ?_⟩
  · rw [WEX.tableAddressValue_congr bits _ _ (fun w hw => frame w (by simp [hw]))]
    exact hs.1
  · exact (frame root (by simp)).trans hs.2

def LBranch {n : Nat} (read : ConstantBit n → Bool) (code : WCode n)
    (bits paths : List Wire) (root : Wire) (b : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords code ∧
    ∀ address st, AddrValid bits root address st → PathsClean read paths address code st →
      b.kraus (Bridge.signedKet st) =
        c • Bridge.signedKet (ECDSAAdd.run ((specialize code address).instantiate read) m st)

/-- `pair_source_simulation` with path-sharing literals: one coefficient list for every address. -/
theorem lsource_simulation {n : Nat} (read : ConstantBit n → Bool)
    (bits paths : List Wire) (root : Wire) (hl : bits.length ≤ paths.length) (code : WCode n)
    (hp : ∀ i ∈ code, LPlaced bits paths root i) :
    ∃ cs : List ℂ, List.Forall₂ (LBranch read code bits paths root)
      (source read bits paths root code).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
  induction code with
  | nil =>
    refine ⟨[1], .cons ?_ .nil, by simp⟩
    refine ⟨[], rfl, ?_⟩
    intro address st _ _
    simp [specialize, ECDSAAdd.ShorPort.Tmpl.instantiate, ECDSAAdd.run]
  | cons i code ih =>
    have htail := ih (fun j hj => hp j (List.mem_cons_of_mem _ hj))
    obtain ⟨tailCs, tailAligned, tailMass⟩ := htail
    have hi := hp i (by simp)
    cases i with
    | literal p =>
      obtain ⟨cs, aligned, mass⟩ := literal_simulation p
      refine ⟨coherentSeqCoefficients cs tailCs, ?_, ?_⟩
      · rw [source, AdaptiveCircuit.run_seq]
        apply simulationAligned_seq aligned tailAligned
        intro b₁ c₁ b₂ c₂ h₁ h₂
        obtain ⟨m₂, hm₂, h₂⟩ := h₂
        refine ⟨b₁.history ++ m₂, ?_, ?_⟩
        · simp [literalRecords, List.length_append, h₁.1, hm₂]
        · intro address st hs hc
          have hc' : ∀ m, PathsClean read paths address code (ECDSAAdd.run p m st) := hc
          change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
          rw [h₁.2 st, map_smul,
            h₂ address (ECDSAAdd.run p b₁.history st)
              (literal_addr p bits paths root address hi st hs b₁.history) (hc' b₁.history)]
          simp only [specialize, List.flatMap_cons, WInstr.specialize,
            ECDSAAdd.ShorPort.Tmpl.instantiate_append, ECDSAAdd.ShorPort.Tmpl.instantiate_lit]
          rw [run_append_records _ _ _ _ _ h₁.1]
          simp [smul_smul]
      · rw [simulationCoefficients_mass, mass, tailMass]
        norm_num
    | lookup control ports =>
      have hpp : PlacedPair bits paths root (.lookup control ports : WInstr n) := hi
      have hi' := hpp
      dsimp only [PlacedPair] at hi'
      have hsep : (lookupRoot root control :: bits ++ paths).Disjoint (portTargets ports) := by
        apply List.disjoint_left.mpr
        intro w hw hm
        exact List.disjoint_left.mp hi'.2.2.2 (List.mem_cons_of_mem root hw) hm
      have hlookup := pairPort_source_state read ports bits paths (lookupRoot root control)
        hl hi'.1 hi'.2.1 hi'.2.2.1 hsep
      obtain ⟨cs, aligned, mass⟩ := hlookup
      refine ⟨coherentSeqCoefficients cs tailCs, ?_, ?_⟩
      · rw [source, AdaptiveCircuit.run_seq]
        apply simulationAligned_seq aligned tailAligned
        intro b₁ c₁ b₂ c₂ h₁ h₂
        obtain ⟨m₂, hm₂, h₂⟩ := h₂
        refine ⟨m₂, hm₂, ?_⟩
        intro address st hs hc
        have hc' : Clean paths st.basis ∧ ∀ m, PathsClean read paths address code
            (ECDSAAdd.run ((portTemplate control ports address).instantiate read) m st) := hc
        let next : ECDSAAdd.State := ⟨st.phase,
          tableXorState (portMask read (ports.drop 258) address) (st.basis (lookupRoot root control))
            (tableXorState (portMask read (ports.take 258) address) (st.basis (lookupRoot root control)) st.basis)⟩
        have hqa : lookupRoot root control ∉ portTargets (ports.take 258) := by
          intro hm; apply List.disjoint_left.mp hsep (show lookupRoot root control ∈ lookupRoot root control :: bits ++ paths from by simp)
          rw [portTargets, List.map_take] at hm
          exact List.take_subset _ _ hm
        have hqb : lookupRoot root control ∉ portTargets (ports.drop 258) := by
          intro hm; apply List.disjoint_left.mp hsep (show lookupRoot root control ∈ lookupRoot root control :: bits ++ paths from by simp)
          rw [portTargets, List.map_drop] at hm
          exact List.drop_subset _ _ hm
        have hra : root ∉ portTargets (ports.take 258) := by
          intro hm; apply List.disjoint_left.mp hi'.2.2.2 (show root ∈ root :: lookupRoot root control :: bits ++ paths from by simp)
          rw [portTargets, List.map_take] at hm
          exact List.take_subset _ _ hm
        have hspec := pairPort_specialize_run_control read control (ports.take 258) (ports.drop 258)
          address root ([] : List Bool) st hi'.2.1 hi'.2.2.1 hqa hqb hra hs.2
        rw [List.take_append_drop] at hspec
        have hnext : PathsClean read paths address code next := by
          have h := hc'.2 []
          rw [hspec] at h
          exact h
        have step : b₁.kraus (Bridge.signedKet st) = c₁ • Bridge.signedKet next := by
          have hstep : b₁.kraus (ket st.basis) = c₁ • ket next.basis := by
            simpa [ket, next, hs.1] using h₁ st.basis hc'.1
          simp only [Bridge.signedKet, map_smul, hstep]
          simp [next, smul_smul, mul_comm]
        change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
        rw [step, map_smul, h₂ address next
          (pair_lookup_addr read control ports bits paths root address hpp st hs) hnext]
        simp only [specialize, List.flatMap_cons, WInstr.specialize,
          ECDSAAdd.ShorPort.Tmpl.instantiate_append]
        rw [ECDSAAdd.run_append, (portTemplate_counts read control ports address).2,
          List.take_zero, List.drop_zero, hspec]
        simp [next, smul_smul]
      · rw [simulationCoefficients_mass, mass, tailMass]
        norm_num

/-- Strictly placed code keeps the address, the root and a clean bank on every reference record. -/
theorem strict_preserves {n} (read : ConstantBit n → Bool) (bits paths : List Wire) (code : WCode n)
    (a : Nat) (hp : ∀ i ∈ code, PlacedPair bits paths windowRoot i)
    (st : ECDSAAdd.State) (hs : SimulationValid bits paths windowRoot a st) (m : List Bool) :
    SimulationValid bits paths windowRoot a (ECDSAAdd.run ((specialize code a).instantiate read) m st) := by
  induction code generalizing st m with
  | nil => simpa [specialize, ECDSAAdd.ShorPort.Tmpl.instantiate, ECDSAAdd.run] using hs
  | cons i code ih =>
    have ht := fun j hj => hp j (List.mem_cons_of_mem i hj)
    have hi := hp i (by simp)
    simp only [specialize,List.flatMap_cons,ECDSAAdd.ShorPort.Tmpl.instantiate_append,ECDSAAdd.run_append]
    cases i with
    | literal p =>
      simp only [WInstr.specialize,ECDSAAdd.ShorPort.Tmpl.instantiate_lit]
      apply ih ht
      have hip : Placed bits paths windowRoot (.literal p : WInstr n) := by
        simpa only [Placed, PlacedPair] using hi
      exact literal_preserves_simulation (n := n) p _ _ _ _ hip st hs _
    | lookup control ps =>
      have hip := hi
      dsimp only [PlacedPair] at hip
      have hmemq : lookupRoot windowRoot control ∈ windowRoot :: lookupRoot windowRoot control :: bits ++ paths := by simp
      have hmemr : windowRoot ∈ windowRoot :: lookupRoot windowRoot control :: bits ++ paths := by simp
      have hqa : lookupRoot windowRoot control ∉ portTargets (ps.take 258) := by
        intro hm; rw [portTargets,List.map_take] at hm
        exact List.disjoint_left.mp hip.2.2.2 hmemq (List.take_subset _ _ hm)
      have hqb : lookupRoot windowRoot control ∉ portTargets (ps.drop 258) := by
        intro hm; rw [portTargets,List.map_drop] at hm
        exact List.disjoint_left.mp hip.2.2.2 hmemq (List.drop_subset _ _ hm)
      have hra : windowRoot ∉ portTargets (ps.take 258) := by
        intro hm; rw [portTargets,List.map_take] at hm
        exact List.disjoint_left.mp hip.2.2.2 hmemr (List.take_subset _ _ hm)
      have hspec (m' : List Bool) := pairPort_specialize_run_control read control (ps.take 258) (ps.drop 258)
        a windowRoot m' st hip.2.1 hip.2.2.1 hqa hqb hra hs.2.2
      simp only [List.take_append_drop] at hspec
      rw [WInstr.specialize,hspec]
      apply ih ht
      exact pair_lookup_preserves_simulation read control ps _ _ _ _ hi st hs

/-- Strictly placed code needs only a clean bank at its start. -/
theorem strict_pathsClean {n} (read : ConstantBit n → Bool) (bits paths : List Wire) (code : WCode n)
    (a : Nat) (hp : ∀ i ∈ code, PlacedPair bits paths windowRoot i)
    (st : ECDSAAdd.State) (hs : SimulationValid bits paths windowRoot a st) :
    PathsClean read paths a code st := by
  induction code generalizing st with
  | nil => trivial
  | cons i code ih =>
    have ht := fun j hj => hp j (List.mem_cons_of_mem i hj)
    have hi := hp i (by simp)
    cases i with
    | literal p =>
      intro m
      have hip : Placed bits paths windowRoot (.literal p : WInstr n) := by
        simpa only [Placed, PlacedPair] using hi
      exact ih ht _ (literal_preserves_simulation (n := n) p _ _ _ _ hip st hs m)
    | lookup control ps =>
      refine ⟨hs.1, fun m => ?_⟩
      have h := strict_preserves read bits paths ([.lookup control ps] : WCode n) a
        (fun j hj => by rw [List.mem_singleton.mp hj]; exact hi) st hs m
      simp only [specialize, List.flatMap_cons, List.flatMap_nil, List.append_nil, WInstr.specialize] at h
      exact ih ht _ h

/-- Literal-only code has no lookup, so it needs no clean bank. -/
def LitAvoid {n} (bits : List Wire) (code : WCode n) : Prop :=
  ∀ i ∈ code, ∃ p, i = .literal p ∧ ∀ w ∈ windowRoot :: bits, w ∉ ECDSAAdd.wires p

theorem litAvoid_pathsClean {n} (read : ConstantBit n → Bool) (bits paths : List Wire) (code : WCode n)
    (a : Nat) (h : LitAvoid bits code) (st : ECDSAAdd.State) : PathsClean read paths a code st := by
  induction code generalizing st with
  | nil => trivial
  | cons i code ih =>
    obtain ⟨p, rfl, -⟩ := h i (by simp)
    intro m
    exact ih (fun j hj => h j (List.mem_cons_of_mem _ hj)) _

theorem litAvoid_placed {n} (bits paths : List Wire) (code : WCode n) (h : LitAvoid bits code) :
    ∀ i ∈ code, LPlaced bits paths windowRoot i := by
  intro i hi
  obtain ⟨p, rfl, hp⟩ := h i hi
  exact hp

theorem litAvoid_addr {n} (read : ConstantBit n → Bool) (bits : List Wire) (code : WCode n) (a : Nat)
    (h : LitAvoid bits code) (st : ECDSAAdd.State) (hs : AddrValid bits windowRoot a st) (m : List Bool) :
    AddrValid bits windowRoot a (ECDSAAdd.run ((specialize code a).instantiate read) m st) := by
  induction code generalizing st m with
  | nil => simpa [specialize, ECDSAAdd.ShorPort.Tmpl.instantiate, ECDSAAdd.run] using hs
  | cons i code ih =>
    obtain ⟨p, rfl, hp⟩ := h i (by simp)
    simp only [specialize,List.flatMap_cons,ECDSAAdd.ShorPort.Tmpl.instantiate_append,ECDSAAdd.run_append,
      WInstr.specialize,ECDSAAdd.ShorPort.Tmpl.instantiate_lit]
    exact ih (fun j hj => h j (List.mem_cons_of_mem _ hj)) _
      (literal_addr (n := n) p bits ([] : List Wire) windowRoot a hp st hs _) _

/-! ### Measured clear on a pool path bank -/

theorem clear_coherent_bank {n} (read : ConstantBit n → Bool) (site : MaskedSite n) (hk : SiteKind site)
    (bitsW H P : List Wire)
    (hsplit : ∀ s : BasisState, 128 * (tableAddressTree H 0 1).routeLabel s + MeasuredClear.hotAddress low s =
      tableAddressValue bitsW s)
    (hH : ∀ w ∈ H, 862 ≤ w ∧ w < 871) (hP : ∀ w ∈ P, 871 ≤ w ∧ w ∉ portTargets site.ports)
    (hPg : site.guard ∉ P) (hindex : (tableAddressTree H 0 1).indexWires.dedup = H)
    (hnd : (H ++ P).Nodup) (hhl : H.length ≤ P.length)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((MeasuredClear.measuredClear (clearData site.ports) low (clearHot site)
        (tableAddressTree H 0 1) site.guard (scratch site) P start).instantiate read history)
      (Finsupp.lmapDomain ℂ ℂ (clearRegister (portTargets site.ports)))
      (fun s => Clean P s ∧
        ∀ p ∈ site.ports, s p.target = (s site.guard && decide (read (p.ref (tableAddressValue bitsW s)) = p.value))) := by
  obtain ⟨hn,hbd,hhot,hmem,hsm,hg,-⟩ := kind_facts site hk
  have hgl : site.guard < 14115 := by rcases hg with e | e <;> rw [e] <;> decide
  have notT : ∀ w ∈ site.guard :: List.ofFn low ++ H ++ P, w ∉ portTargets site.ports := by
    intro w hw ht
    have h2 := (hbd w ht).1
    simp only [List.mem_append,List.mem_cons] at hw
    rcases hw with ((h | h) | h) | h
    · rw [h] at h2; dsimp only [Wire] at *; omega
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
      have := low_lt i
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
  have hc := MeasuredClear.measuredClear_recycled_coherent (clearData site.ports) read low (clearHot site)
    (tableAddressTree H 0 1) site.guard (scratch site) P hl
    (by intro i j he; apply Fin.ext; rw [hhot i,hhot j] at he; dsimp only [Wire] at he; omega)
    (by
      intro i j he
      have h1 := (hbd _ (hmem j)).1
      have h2 := low_lt i
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
      exact notT _ (by simp only [List.mem_append,List.mem_cons] at hm ⊢; tauto) hsm)
    (by
      intro hm
      obtain ⟨i,hi⟩ := List.mem_ofFn.mp hm
      rw [hhot i] at hi
      dsimp only [Wire] at hi
      omega)
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
  simpa [MeasuredClear.LoadedClear,clearData,hsplit] using hs.2 q hq

end
end ShorECDLP.Entrant.PathShare

/-! ### Blocks compiled on a bank -/

namespace ShorECDLP.Entrant.PathShare
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-- Address bits, high clear bits, the clear's path bank and the lookup path bank. -/
structure Bank where
  bits : List Wire
  high : List Wire
  hp : List Wire
  paths : List Wire

structure BankOK (B : Bank) : Prop where
  split : ∀ s : BasisState, 128 * (tableAddressTree B.high 0 1).routeLabel s + MeasuredClear.hotAddress low s =
    tableAddressValue B.bits s
  high : ∀ w ∈ B.high, 862 ≤ w ∧ w < 871
  index : (tableAddressTree B.high 0 1).indexWires.dedup = B.high
  nodup : (B.high ++ B.hp).Nodup
  len : B.high.length ≤ B.hp.length
  sub : ∀ w ∈ B.hp, w ∈ B.paths
  out : ∀ w ∈ B.hp, 871 ≤ w
  bitsLen : B.bits.length ≤ B.paths.length

def clearP {n} (B : Bank) (site : MaskedSite n) (start : Nat) :=
  MeasuredClear.measuredClear (clearData site.ports) low (clearHot site) (tableAddressTree B.high 0 1)
    site.guard (scratch site) B.hp start

def clearSourceP {n} (B : Bank) (read : ConstantBit n → Bool) (site : MaskedSite n) : AdaptiveCircuit :=
  (clearP B site 0).instantiate read Fin.elim0

theorem clearP_run {n} (B : Bank) (read : ConstantBit n → Bool) (site : MaskedSite n)
    (start : Nat) (history : Fin start → Bool) :
    ((clearP B site start).instantiate read history).run = (clearSourceP B read site).run := by
  simp only [clearP,clearSourceP,MeasuredClear.measuredClear_run]

def blockRecP {n} (B : Bank) : Block n → Nat
  | .plain code => codeRecords B.bits B.paths windowRoot (normalizeW code)
  | .masked site => codeRecords B.bits B.paths windowRoot (normalizeW site.prefix) +
      site.ports.length + (MeasuredClear.recordMeasurements
        (MeasuredClear.recordUnaryOps (tableAddressTree B.high 0 1) site.guard B.hp)+127)

def blockProgP {n} (B : Bank) (b : Block n) (start : Nat) : Straight n start (start+blockRecP B b) :=
  match b with
  | .plain code => compile B.bits B.paths windowRoot (normalizeW code) start
  | .masked site => castFinish (by simp [blockRecP,clearData]; omega)
      ((compile B.bits B.paths windowRoot (normalizeW site.prefix) start).append
        (clearP B site (start+codeRecords B.bits B.paths windowRoot (normalizeW site.prefix))))

def recordsP {n} (B : Bank) : Code n → Nat
  | [] => 0
  | b::code => blockRecP B b + recordsP B code

def programP {n} (B : Bank) : (code : Code n) → (start : Nat) → Straight n start (start+recordsP B code)
  | [], _ => .done
  | b::code, start => castFinish (by simp [recordsP]; omega)
      ((blockProgP B b start).append (programP B code (start+blockRecP B b)))

def blockSourceP {n} (B : Bank) (read : ConstantBit n → Bool) : Block n → AdaptiveCircuit
  | .plain code => source read B.bits B.paths windowRoot (normalizeW code)
  | .masked site => (source read B.bits B.paths windowRoot (normalizeW site.prefix)).seq
      (clearSourceP B read site)

def sourceCodeP {n} (B : Bank) (read : ConstantBit n → Bool) : Code n → AdaptiveCircuit
  | [] => .done
  | b::code => (blockSourceP B read b).seq (sourceCodeP B read code)

theorem blockProgP_run {n} (B : Bank) (read : ConstantBit n → Bool) (b : Block n)
    (start : Nat) (history : Fin start → Bool) :
    ((blockProgP B b start).instantiate read history).run = (blockSourceP B read b).run := by
  cases b with
  | plain code => exact compile_run read _ _ _ _ _ _
  | masked site =>
    rw [blockProgP,castFinish_instantiate,append_run_fixed _ _ _ _ _ (fun h => clearP_run B read site _ h),
      AdaptiveCircuit.run_seq,compile_run]
    simp only [blockSourceP,AdaptiveCircuit.run_seq]

theorem programP_run {n} (B : Bank) (read : ConstantBit n → Bool) (code : Code n)
    (start : Nat) (history : Fin start → Bool) :
    ((programP B code start).instantiate read history).run = (sourceCodeP B read code).run := by
  induction code generalizing start with
  | nil => rfl
  | cons b code ih =>
    rw [programP,castFinish_instantiate,append_run_fixed _ _ _ _ _ (ih _),AdaptiveCircuit.run_seq,blockProgP_run]
    simp only [sourceCodeP,AdaptiveCircuit.run_seq]

structure SiteGeoP {n} (B : Bank) (site : MaskedSite n) : Prop where
  placed : ∀ i ∈ site.code, Placed B.bits B.paths windowRoot i
  kind : SiteKind site

/-- Plain blocks are literal and keep root and address; masked sites avoid the whole bank. -/
def BlockGeoP {n} (B : Bank) : Block n → Prop
  | .plain code => LitAvoid B.bits code
  | .masked site => SiteGeoP B site

def BlockClean {n} (P : List Wire) : Block n → ECDSAAdd.State → Prop
  | .plain _, _ => True
  | .masked _, st => Clean P st.basis

/-- The bank is clean at the start of every masked site of the reference run. -/
def CodeClean {n} (read : ConstantBit n → Bool) (P : List Wire) (address : Nat) :
    Code n → ECDSAAdd.State → Prop
  | [], _ => True
  | b :: code, st => BlockClean P b st ∧
      ∀ m, m.length = ECDSAAdd.measurementCount (blockReference read address b) →
        CodeClean read P address code (ECDSAAdd.run (blockReference read address b) m st)

theorem clean_append {n} (read : ConstantBit n → Bool) (P : List Wire) (address : Nat) (a b : Code n)
    (st : ECDSAAdd.State) (ha : CodeClean read P address a st)
    (hb : ∀ m, m.length = ECDSAAdd.measurementCount (reference read address a) →
      CodeClean read P address b (ECDSAAdd.run (reference read address a) m st)) :
    CodeClean read P address (a++b) st := by
  induction a generalizing st with
  | nil => simpa [CodeClean,ECDSAAdd.run] using hb [] rfl
  | cons x xs ih =>
    refine ⟨ha.1,?_⟩
    intro m hm
    apply ih _ (ha.2 m hm)
    intro tail ht
    have hc := hb (m++tail) (by simp [ECDSAAdd.measurementCount_append,hm,ht])
    rw [reference_cons,run_append_records _ _ m tail st hm] at hc
    exact hc

theorem pair_of_placed_lit {n} (bits paths : List Wire) (i : WInstr n)
    (h : PlacedPair bits paths windowRoot i) : LPlaced bits paths windowRoot i := by
  cases i with
  | literal p =>
    intro w hw
    apply h w
    rcases List.mem_cons.mp hw with e | e
    · exact List.mem_cons.mpr (Or.inl e)
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ e)
  | lookup c ps => exact h

theorem clearP_coherent {n} (read : ConstantBit n → Bool) (B : Bank) (hB : BankOK B)
    (site : MaskedSite n) (hg : SiteGeoP B site) (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((clearP B site start).instantiate read history)
      (Finsupp.lmapDomain ℂ ℂ (clearRegister (portTargets site.ports)))
      (fun s => Clean B.hp s ∧
        ∀ p ∈ site.ports, s p.target = (s site.guard && decide (read (p.ref (tableAddressValue B.bits s)) = p.value))) := by
  have hlast := hg.placed (.lookup (some site.guard) site.ports) (by simp [MaskedSite.code])
  dsimp only [Placed] at hlast
  unfold clearP
  apply clear_coherent_bank read site hg.kind B.bits B.high B.hp hB.split hB.high
  · intro w hw
    refine ⟨hB.out w hw, fun ht => ?_⟩
    exact List.disjoint_left.mp hlast.2.2
      (show w ∈ windowRoot :: lookupRoot windowRoot (some site.guard) :: B.bits ++ B.paths by
        simp [hB.sub w hw]) ht
  · intro hg'
    have hn := hlast.1
    simp only [lookupRoot, Option.getD_some, List.cons_append, List.nodup_cons] at hn
    exact hn.1 (List.mem_append_right _ (hB.sub _ hg'))
  · exact hB.index
  · exact hB.nodup
  · exact hB.len

theorem masked_runP {n} (read : ConstantBit n → Bool) (B : Bank) (site : MaskedSite n)
    (hg : SiteGeoP B site) (a : Nat) (st : ECDSAAdd.State) (m : List Bool)
    (hs : SimulationValid B.bits B.paths windowRoot a st) :
    ECDSAAdd.run ((specialize site.code a).instantiate read) m st =
      let next := ECDSAAdd.run ((specialize site.prefix a).instantiate read) m st
      ⟨next.phase,tableXorState (portMask read site.ports a) (next.basis site.guard) next.basis⟩ := by
  have hp : ∀ i ∈ site.prefix, PlacedPair B.bits B.paths windowRoot i := by
    intro i hi; exact placed_implies_pair _ _ _ _ (hg.placed i (List.mem_append_left _ hi))
  have hnext := strict_preserves read B.bits B.paths site.prefix a hp st hs m
  have hlast := hg.placed (.lookup (some site.guard) site.ports) (by simp [MaskedSite.code])
  have hroot : site.guard ∉ portTargets site.ports := List.disjoint_left.mp hlast.2.2 (by simp [lookupRoot])
  simp only [MaskedSite.code,specialize_append,ECDSAAdd.ShorPort.Tmpl.instantiate_append,
    ECDSAAdd.run_append,ECDSAAdd.run_take]
  simpa [specialize,WInstr.specialize] using portTemplate_run read (some site.guard) site.ports a windowRoot
    (m.drop (ECDSAAdd.measurementCount ((specialize site.prefix a).instantiate read)))
    (ECDSAAdd.run ((specialize site.prefix a).instantiate read) m st)
    hlast.2.1 hroot hnext.2.2

theorem lplaced_normalize {n} (bits paths : List Wire) (root : Wire) (code : WCode n)
    (hp : ∀ i ∈ code, LPlaced bits paths root i) : ∀ i ∈ normalizeW code, LPlaced bits paths root i := by
  intro i hi
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
  have h := hp j hj
  cases j with
  | literal p => simpa [normalizeWInstr, LPlaced, ECDSAAdd.Baselines.normalize_wires] using h
  | lookup c p => exact h

theorem pathsClean_normalize {n} (read : ConstantBit n → Bool) (paths : List Wire) (a : Nat)
    (code : WCode n) (st : ECDSAAdd.State) (h : PathsClean read paths a code st) :
    PathsClean read paths a (normalizeW code) st := by
  induction code generalizing st with
  | nil => trivial
  | cons i code ih =>
    cases i with
    | literal p =>
      have h' : ∀ m, PathsClean read paths a code (ECDSAAdd.run p m st) := h
      show ∀ m, PathsClean read paths a (normalizeW code)
        (ECDSAAdd.run (ECDSAAdd.Baselines.normalizeProgram p) m st)
      intro m
      rw [ECDSAAdd.Baselines.normalize_run]
      exact ih _ (h' m)
    | lookup c ps =>
      have h' : Clean paths st.basis ∧ ∀ m, PathsClean read paths a code
          (ECDSAAdd.run ((portTemplate c ps a).instantiate read) m st) := h
      exact ⟨h'.1, fun m => ih _ (h'.2 m)⟩

theorem lnormalized_simulation {n} (read : ConstantBit n → Bool) (bits paths : List Wire)
    (hl : bits.length ≤ paths.length) (code : WCode n) (hp : ∀ i ∈ code, LPlaced bits paths windowRoot i) :
    ∃ cs : List ℂ, List.Forall₂ (LBranch read code bits paths windowRoot)
      (source read bits paths windowRoot (normalizeW code)).run cs ∧ (cs.map Complex.normSq).sum = 1 := by
  obtain ⟨cs,aligned,mass⟩ := lsource_simulation read bits paths windowRoot hl (normalizeW code)
    (lplaced_normalize _ _ _ _ hp)
  refine ⟨cs,aligned.imp ?_,mass⟩
  intro b c hb
  obtain ⟨m,hm,hb⟩ := hb
  refine ⟨m,by simpa [literalRecords_normalize] using hm,?_⟩
  intro address st hs hc
  simpa only [specialize_normalize_run] using hb address st hs (pathsClean_normalize read paths address code st hc)

def BlockSimP {n} (read : ConstantBit n → Bool) (B : Bank) (block : Block n)
    (branch : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords block.code ∧
    ∀ address st, AddrValid B.bits windowRoot address st → BlockClean B.paths block st →
      BlockSafe read address block st →
      branch.kraus (Bridge.signedKet st) =
        c • Bridge.signedKet (ECDSAAdd.run (blockReference read address block) m st)

theorem block_simulationP {n} (read : ConstantBit n → Bool) (B : Bank) (hB : BankOK B)
    (block : Block n) (hg : BlockGeoP B block) :
    ∃ cs : List ℂ, List.Forall₂ (BlockSimP read B block) (blockSourceP B read block).run cs ∧
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
  | masked site =>
    have hg' : SiteGeoP B site := hg
    have hp : ∀ i ∈ site.prefix, PlacedPair B.bits B.paths windowRoot i := by
      intro i hi; exact placed_implies_pair _ _ _ _ (hg'.placed i (List.mem_append_left _ hi))
    obtain ⟨preCs,preAligned,preMass⟩ := lnormalized_simulation read B.bits B.paths hB.bitsLen site.prefix
      (fun i hi => pair_of_placed_lit _ _ i (hp i hi))
    obtain ⟨cs,aligned,mass⟩ := clearP_coherent read B hB site hg' 0 Fin.elim0
    refine ⟨coherentSeqCoefficients preCs cs,?_,?_⟩
    · rw [blockSourceP,AdaptiveCircuit.run_seq]
      apply simulationAligned_seq preAligned aligned
      intro b₁ c₁ b₂ c₂ h₁ h₂
      obtain ⟨m,hm,h₁⟩ := h₁
      refine ⟨m,?_,?_⟩
      · simpa [Block.code,MaskedSite.code,literalRecords] using hm
      · intro a st hs hcl hsafe
        have hcl' : Clean B.paths st.basis := hcl
        have hsv : SimulationValid B.bits B.paths windowRoot a st := ⟨hcl',hs.1,hs.2⟩
        let next := ECDSAAdd.run ((specialize site.prefix a).instantiate read) m st
        have hn := strict_preserves read B.bits B.paths site.prefix a hp st hsv m
        have hrun := masked_runP read B site hg' a st m hsv
        have hclean : Clean (portTargets site.ports)
            (tableXorState (portMask read site.ports a) (next.basis site.guard) next.basis) := by
          have h := hsafe m
          rw [hrun] at h
          exact h
        have hlast := hg'.placed (.lookup (some site.guard) site.ports) (by simp [MaskedSite.code])
        have hvalid : Clean B.hp next.basis ∧
            ∀ p ∈ site.ports, next.basis p.target = (next.basis site.guard &&
              decide (read (p.ref (tableAddressValue B.bits next.basis)) = p.value)) := by
          refine ⟨fun w hw => hn.1 w (hB.sub w hw),?_⟩
          rw [hn.2.1]
          exact loaded_of_clean_unload read site.ports a site.guard next.basis hlast.2.1 hclean
        have hclear : b₂.kraus (ket next.basis) =
            c₂ • ket (tableXorState (portMask read site.ports a) (next.basis site.guard) next.basis) := by
          rw [← clear_eq_unload read site.ports a site.guard next.basis hclean]
          simpa [ket] using h₂ next.basis hvalid
        have hsigned : b₂.kraus (Bridge.signedKet next) = c₂ •
            Bridge.signedKet (ECDSAAdd.run ((specialize site.code a).instantiate read) m st) := by
          rw [hrun]
          change b₂.kraus (Bridge.signedKet next) = c₂ • Bridge.signedKet
            ⟨next.phase,tableXorState (portMask read site.ports a) (next.basis site.guard) next.basis⟩
          cases hphase : next.phase <;> simp [Bridge.signedKet,hphase,hclear,map_neg]
        change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
        rw [h₁ a st hs (strict_pathsClean read B.bits B.paths site.prefix a hp st hsv),map_smul,hsigned]
        simp [smul_smul,blockReference,Block.code]
    · rw [simulationCoefficients_mass,preMass,mass]
      norm_num

theorem block_addr {n} (read : ConstantBit n → Bool) (B : Bank) (b : Block n) (hg : BlockGeoP B b)
    (a : Nat) (st : ECDSAAdd.State) (hs : AddrValid B.bits windowRoot a st)
    (hc : BlockClean B.paths b st) (m : List Bool) :
    AddrValid B.bits windowRoot a (ECDSAAdd.run (blockReference read a b) m st) := by
  cases b with
  | plain code => exact litAvoid_addr read B.bits code a hg st hs m
  | masked site =>
    have hg' : SiteGeoP B site := hg
    have hp : ∀ i ∈ site.code, PlacedPair B.bits B.paths windowRoot i :=
      fun i hi => placed_implies_pair _ _ _ _ (hg'.placed i hi)
    have h := strict_preserves read B.bits B.paths site.code a hp st ⟨hc,hs.1,hs.2⟩ m
    exact ⟨h.2.1,h.2.2⟩

def SimP {n} (read : ConstantBit n → Bool) (B : Bank) (code : Code n)
    (b : InstrumentBranch) (c : ℂ) : Prop :=
  ∃ m : List Bool, m.length = literalRecords (erase code) ∧
    ∀ a st, AddrValid B.bits windowRoot a st → CodeClean read B.paths a code st → Safe read a code st →
      b.kraus (Bridge.signedKet st) = c • Bridge.signedKet (ECDSAAdd.run (reference read a code) m st)

theorem source_simulationP {n} (read : ConstantBit n → Bool) (B : Bank) (hB : BankOK B) (code : Code n)
    (hg : ∀ b ∈ code, BlockGeoP B b) :
    ∃ cs : List ℂ, List.Forall₂ (SimP read B code) (sourceCodeP B read code).run cs ∧
      (cs.map Complex.normSq).sum = 1 := by
  induction code with
  | nil =>
    refine ⟨[1],.cons ?_ .nil,by simp⟩
    exact ⟨[],rfl,fun a st _ _ _ => by simp [reference,erase,specialize,ECDSAAdd.ShorPort.Tmpl.instantiate,ECDSAAdd.run]⟩
  | cons b code ih =>
    obtain ⟨cs₁,h₁,mass₁⟩ := block_simulationP read B hB b (hg b (by simp))
    obtain ⟨cs₂,h₂,mass₂⟩ := ih (fun c hc => hg c (by simp [hc]))
    refine ⟨coherentSeqCoefficients cs₁ cs₂,?_,?_⟩
    · rw [sourceCodeP,AdaptiveCircuit.run_seq]
      apply simulationAligned_seq h₁ h₂
      intro b₁ c₁ b₂ c₂ hb₁ hb₂
      obtain ⟨m₁,len₁,run₁⟩ := hb₁
      obtain ⟨m₂,len₂,run₂⟩ := hb₂
      refine ⟨m₁++m₂,?_,?_⟩
      · simp [erase,List.length_append,len₁,len₂]
      · intro a st hs hc hsafe
        have hm : m₁.length = ECDSAAdd.measurementCount (blockReference read a b) :=
          len₁.trans (specialize_counts read b.code a).2.symm
        have hn := block_addr read B b (hg b (by simp)) a st hs hc.1 m₁
        change b₂.kraus (b₁.kraus (Bridge.signedKet st)) = _
        rw [run₁ a st hs hc.1 hsafe.1,map_smul,
          run₂ a (ECDSAAdd.run (blockReference read a b) m₁ st) hn (hc.2 m₁ hm) (hsafe.2 m₁ hm),
          reference_cons,run_append_records _ _ m₁ m₂ st hm]
        simp [smul_smul]
    · rw [simulationCoefficients_mass,mass₁,mass₂]
      norm_num

/-- All addresses share one normalized branch coefficient list. -/
theorem program_coherentP {n} (read : ConstantBit n → Bool) (B : Bank) (hB : BankOK B) (code : Code n)
    (hg : ∀ b ∈ code, BlockGeoP B b)
    (Valid : BasisState → Prop) (result : BasisState → BasisState)
    (hsafe : ∀ s, Valid s → Safe read (tableAddressValue B.bits s) code ⟨false,s⟩)
    (hclean : ∀ s, Valid s → CodeClean read B.paths (tableAddressValue B.bits s) code ⟨false,s⟩)
    (hrun : ∀ s, Valid s → ∀ m,
      ECDSAAdd.run (reference read (tableAddressValue B.bits s) code) m ⟨false,s⟩ = ⟨false,result s⟩)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((programP B code start).instantiate read history)
      (Finsupp.lmapDomain ℂ ℂ result) (fun s => s windowRoot = true ∧ Valid s) := by
  obtain ⟨cs,aligned,mass⟩ := source_simulationP read B hB code hg
  refine ⟨cs,?_,mass⟩
  rw [programP_run]
  apply aligned.imp
  intro b c hb s hs
  obtain ⟨m,_,h⟩ := hb
  have he := h (tableAddressValue B.bits s) ⟨false,s⟩ ⟨rfl,hs.1⟩ (hclean s hs.2) (hsafe s hs.2)
  rw [Bridge.signedKet_false,hrun s hs.2 m,Bridge.signedKet_false] at he
  simpa [ket] using he

end
end ShorECDLP.Entrant.PathShare

/-! ### Clean bank at the masked sites of the fused generic branch -/

namespace ShorECDLP.Entrant.PathShare
open ECDSAAdd Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Arithmetic.CompressedPointDialog
noncomputable section
set_option maxRecDepth 30000
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-- An arithmetic contract that also keeps the bank clean at every masked-site start. -/
structure CheckedC {n} (read : ConstantBit n → Bool) (address : Nat) (P : List Wire)
    (Pre : BasisState → Prop) (code : Code n) (Post : BasisState → Prop) : Prop where
  checked : Checked read address Pre code Post
  clean : ∀ st, Pre st.basis → CodeClean read P address code st

namespace CheckedC
variable {n : Nat} {read : ConstantBit n → Bool} {address : Nat} {P : List Wire}
variable {A B C : BasisState → Prop} {a b : Code n}

theorem seq (ha : CheckedC read address P A a B) (hb : CheckedC read address P B b C) :
    CheckedC read address P A (a++b) C :=
  ⟨ha.checked.seq hb.checked, fun st hs => clean_append read P address a b st (ha.clean st hs)
    (fun m _ => hb.clean _ (ha.checked.correct st m hs).2)⟩

theorem plain {code : WCode n} (h : Checked read address A ([.plain code] : Code n) B) :
    CheckedC read address P A ([.plain code] : Code n) B :=
  ⟨h, fun _ _ => ⟨trivial, fun _ _ => trivial⟩⟩

theorem masked {site : MaskedSite n} (h : Checked read address A ([.masked site] : Code n) B)
    (hc : ∀ s, A s → Clean P s) : CheckedC read address P A ([.masked site] : Code n) B :=
  ⟨h, fun _ hs => ⟨hc _ hs, fun _ _ => trivial⟩⟩

end CheckedC

def InPool (P : List Wire) : Prop := ∀ w ∈ P, w ∈ streamLayout.dialogPool

theorem values_clean {P : List Wire} (hP : InPool P) {X Y : ECDSAAdd.Fp} {G : Bool} {base s : BasisState}
    (h : PointDialogValues streamLayout X Y G base s) : Clean P s :=
  fun w hw => (ECDSAAdd.Arithmetic.regValue_zero _ _).mp h.clean w (hP w hw)

theorem literal_checkedC {n} (read : ConstantBit n → Bool) (address : Nat) (P : List Wire)
    (p : ECDSAAdd.Program) (A B : BasisState → Prop) (h : ECDSAAdd.Triple A p B) :
    CheckedC read address P A ([.plain (wLiteral p)] : Code n) B :=
  CheckedC.plain (literal_checked read address p A B h)

theorem recovery2_checkedC {n} (read : ConstantBit n → Bool) (address : Nat) (P : List Wire) (hP : InPool P)
    (rows : Nat → Fin n) {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (hr : RowReads read (rows address) (.some hc))
    (X Y : ECDSAAdd.Fp) (G : Bool) (base : BasisState) :
    CheckedC read address P (PointDialogValues streamLayout X Y G base) (recovery2 rows)
      (PointDialogValues streamLayout (if G then cx-X else X) (if G then Y-cy else Y) G base) := by
  have hw := streamLayout_widths
  have hn := streamLayout_nodup
  have a := literal_checkedC read address P _ _ _ (pointRecoveryReflection_step streamLayout hw hn X Y G base)
  have c := literal_checkedC read address P _ _ _
    (dialogStep_addX streamLayout hw hn (if G then -1-X else X) Y G base 1)
  have d := CheckedC.masked (P := P) (pair_checked read address ((if G then -1-X else X)+(if G then 1 else 0)) Y G base cx (-cy)
    (wFields rows .x) (wFields rows .negY)
    (row_bits hc hr .x cx (field_some_x hc)) (row_bits hc hr .negY (-cy) (field_some_negY hc)))
    (fun _ h => values_clean hP h)
  have all := (a.seq c).seq d
  have hx : ((if G then -1-X else X)+(if G then 1 else 0))+(if G then cx else 0)=
      (if G then cx-X else X) := by cases G <;> simp; ring
  have hy : Y+(if G then -cy else 0)=(if G then Y-cy else Y) := by cases G <;> simp [sub_eq_add_neg]
  rw [hx,hy] at all
  simpa only [recovery2,pairAdd,List.cons_append,List.nil_append,List.append_assoc] using all

theorem core2_checkedC_true {n} (read : ConstantBit n → Bool) (address : Nat) (P : List Wire) (hP : InPool P)
    (rows : Nat → Fin n) {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (hr : RowReads read (rows address) (.some hc))
    (X Y : ECDSAAdd.Fp) (base : BasisState) (hX : X≠cx) (hd : cx-genericX X Y cx cy≠0) :
    CheckedC read address P (PointDialogValues streamLayout X Y true base) (core2 rows)
      (PointDialogValues streamLayout (genericX X Y cx cy) (genericY X Y cx cy) true base) := by
  have hw := streamLayout_widths
  have hn := streamLayout_nodup
  let a := genericSlope X Y cx cy
  let d := cx-genericX X Y cx cy
  have hv := generic_inplace_values X Y cx cy hX
  have h12 := CheckedC.masked (P := P) (pair_checked read address X Y true base (-cx) (-cy)
    (wFields rows .negX) (wFields rows .negY)
    (row_bits hc hr .negX (-cx) (field_some_negX hc)) (row_bits hc hr .negY (-cy) (field_some_negY hc)))
    (fun _ h => values_clean hP h)
  simp only [if_true,←sub_eq_add_neg] at h12
  have h3 := literal_checkedC read address P _ _ _
    (ECDSAAdd.Frontier.arith3F_step streamLayout hw hn (X-cx) (Y-cy) true base false (sub_ne_zero.mpr hX))
  have ha : (Y-cy)/(X-cx)=a := rfl
  simp only [Bool.false_eq_true,if_false,ha] at h3
  have h4 := literal_checkedC read address P _ _ _
    (ECDSAAdd.Frontier.GenericOB5.square_step streamLayout hw hn (X-cx) a true base)
  simp only [if_true] at h4
  have h5 := CheckedC.masked (P := P) (addX_checked read address streamLayout hw hn ((X-cx)-a*a) a true base (3*cx)
    (wFields rows .tripleX) (row_bits hc hr .tripleX (3*cx) (field_some_tripleX hc)))
    (fun _ h => values_clean hP h)
  simp only [if_true] at h5
  rw [show (X-cx)-a*a+3*cx=d from hv.2.1] at h5
  have h6 := literal_checkedC read address P _ _ _
    (ECDSAAdd.Frontier.arith3F_step streamLayout hw hn d a true base true hd)
  simp only [if_true] at h6
  have r := recovery2_checkedC read address P hP rows hc hr d (a*d) true base
  simp only [if_true] at r
  rw [show cx-d=genericX X Y cx cy by dsimp [d];ring] at r
  rw [show a*d-cy=genericY X Y cx cy from hv.2.2] at r
  have h := ((((h12.seq h3).seq h4).seq h5).seq h6).seq r
  simpa only [core2,pairAdd,constAdd,List.append_assoc,List.cons_append,List.nil_append] using h

theorem core2_checkedC_false {n} (read : ConstantBit n → Bool) (address : Nat) (P : List Wire) (hP : InPool P)
    (rows : Nat → Fin n) {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (hr : RowReads read (rows address) (.some hc))
    (X Y : ECDSAAdd.Fp) (base : BasisState) (hX0 : X ≠ 0) :
    CheckedC read address P (PointDialogValues streamLayout X Y false base) (core2 rows)
      (PointDialogValues streamLayout X Y false base) := by
  have hw := streamLayout_widths
  have hn := streamLayout_nodup
  have h12 := CheckedC.masked (P := P) (pair_checked read address X Y false base (-cx) (-cy)
    (wFields rows .negX) (wFields rows .negY)
    (row_bits hc hr .negX (-cx) (field_some_negX hc)) (row_bits hc hr .negY (-cy) (field_some_negY hc)))
    (fun _ h => values_clean hP h)
  have h3 := literal_checkedC read address P _ _ _
    (ECDSAAdd.Frontier.arith3F_step streamLayout hw hn X Y false base false hX0)
  have h4 := literal_checkedC read address P _ _ _
    (ECDSAAdd.Frontier.GenericOB5.square_step streamLayout hw hn X (Y/X) false base)
  have h5 := CheckedC.masked (P := P) (addX_checked read address streamLayout hw hn X (Y/X) false base (3*cx)
    (wFields rows .tripleX) (row_bits hc hr .tripleX (3*cx) (field_some_tripleX hc)))
    (fun _ h => values_clean hP h)
  have h6 := literal_checkedC read address P _ _ _
    (ECDSAAdd.Frontier.arith3F_step streamLayout hw hn X (Y/X) false base true hX0)
  have r := recovery2_checkedC read address P hP rows hc hr X Y false base
  simp only [Bool.false_eq_true,if_false,if_true,add_zero,sub_zero] at h12 h3 h4 h5 h6 r
  rw [div_mul_cancel₀ Y hX0] at h6
  have h := ((((h12.seq h3).seq h4).seq h5).seq h6).seq r
  simpa only [core2,pairAdd,constAdd,List.append_assoc,List.cons_append,List.nil_append] using h

theorem checkedC_clean {n} {read : ConstantBit n → Bool} {address : Nat} {P : List Wire} (hP : InPool P)
    {code : Code n} {A : BasisState → Prop} {X Y : ECDSAAdd.Fp} {G : Bool} {base : BasisState}
    (h : CheckedC read address P A code (PointDialogValues streamLayout X Y G base))
    (st : ECDSAAdd.State) (ha : A st.basis) :
    CodeClean read P address code st ∧ ∀ m, Clean P (ECDSAAdd.run (reference read address code) m st).basis :=
  ⟨h.clean st ha, fun m => values_clean hP (h.checked.correct st m ha).2⟩

/-- At every generic boundary the bank is clean at each fused site and after the branch. -/
theorem generic2_clean {n} (read : ConstantBit n → Bool) (address : Nat) (P : List Wire) (hP : InPool P)
    (rows : Nat → Fin n) (R : Point) (b : Bool) (f : BasisState)
    {cx cy : ECDSAAdd.Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (hr : RowReads read (rows address) (.some hc))
    (hg : f streamLayout.core.generic=true → R≠0 ∧ R≠(.some hc : Point) ∧ R≠-(.some hc : Point) ∧
      R≠dialogExceptionPoint (.some hc))
    (st : ECDSAAdd.State) (hs : PointDialogBoundary streamLayout R b f st.basis) :
    CodeClean read P address (generic2 rows) st ∧
      ∀ m, Clean P (ECDSAAdd.run (reference read address (generic2 rows)) m st).basis := by
  have hw := streamLayout_widths
  have hn := streamLayout_nodup
  have hp := (point_holds _ _ _).mp hs.point
  have hgen : st.basis streamLayout.core.generic = f streamLayout.core.generic :=
    hs.flags _ (by simp [inPlaceFlags])
  show CodeClean read P address ([.plain (wLiteral (ECDSAAdd.Frontier.zrep streamLayout))] ++ core2 rows ++
      [.plain (wLiteral (ECDSAAdd.Frontier.zrep streamLayout))]) st ∧
    ∀ m, Clean P (ECDSAAdd.run (reference read address ([.plain (wLiteral (ECDSAAdd.Frontier.zrep streamLayout))] ++
      core2 rows ++ [.plain (wLiteral (ECDSAAdd.Frontier.zrep streamLayout))])) m st).basis
  cases R with
  | zero =>
    have hG : f streamLayout.core.generic = false := by
      cases h : f streamLayout.core.generic
      · rfl
      · exact absurd rfl (hg h).1
    have values : PointDialogValues streamLayout 0 0 false st.basis st.basis :=
      ⟨hp.2.1,hp.2.2,hgen.trans hG,hs.clean,fun _ _=>rfl⟩
    have hfin : st.basis streamLayout.point.finite = false := hp.1
    have z1 := literal_checkedC read address P _ _ _ (Frontier.zrep_step streamLayout hw hn 0 5 0 false st.basis
      (by rw [hfin,Frontier.finFive_val]; rfl))
    have mid2 := core2_checkedC_false read address P hP rows hc hr 5 0 st.basis Frontier.finFive_ne_zero
    have z2 := literal_checkedC read address P _ _ _ (Frontier.zrep_step streamLayout hw hn 5 0 0 false st.basis
      (by rw [hfin,Frontier.finFive_val]; rfl))
    exact checkedC_clean hP ((z1.seq mid2).seq z2) st values
  | @some x y hrp =>
    have hfin : st.basis streamLayout.point.finite = true := hp.1
    cases hG : f streamLayout.core.generic with
    | false =>
      have values : PointDialogValues streamLayout x y false st.basis st.basis :=
        ⟨hp.2.1,hp.2.2,hgen.trans hG,hs.clean,fun _ _=>rfl⟩
      have z1 := literal_checkedC read address P _ _ _
        (Frontier.zrep_step streamLayout hw hn x x y false st.basis (by rw [hfin]; simp))
      have mid2 := core2_checkedC_false read address P hP rows hc hr x y st.basis (Frontier.curve_x_ne_zero hrp)
      have z2 := literal_checkedC read address P _ _ _
        (Frontier.zrep_step streamLayout hw hn x x y false st.basis (by rw [hfin]; simp))
      exact checkedC_clean hP ((z1.seq mid2).seq z2) st values
    | true =>
      have he := hg hG
      have den := dialog_denominators_ne_zero hrp hc he.2.1 he.2.2.1 he.2.2.2
      have values : PointDialogValues streamLayout x y true st.basis st.basis :=
        ⟨hp.2.1,hp.2.2,hgen.trans hG,hs.clean,fun _ _=>rfl⟩
      have z1 := literal_checkedC read address P _ _ _
        (Frontier.zrep_step streamLayout hw hn x x y true st.basis (by rw [hfin]; simp))
      have mid2 := core2_checkedC_true read address P hP rows hc hr x y st.basis den.1 den.2
      have z2 := literal_checkedC read address P _ _ _ (Frontier.zrep_step streamLayout hw hn (genericX x y cx cy)
        (genericX x y cx cy) (genericY x y cx cy) true st.basis (by rw [hfin]; simp))
      exact checkedC_clean hP ((z1.seq mid2).seq z2) st values

end
end ShorECDLP.Entrant.PathShare

/-! ### Clean bank along the fused row -/

namespace ShorECDLP.Entrant.PathShare
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Secp256k1
open ECDSAAdd.ShorPort ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
attribute [local irreducible] ECDSAAdd.run

def scrHeadProgram : ECDSAAdd.Program :=
  [.CX streamLayout.control streamLayout.core.double] ++ [.CX streamLayout.control streamLayout.core.equalX] ++
    ECDSAAdd.Entrant.zeroFlag streamLayout.point.finite streamLayout.control streamLayout.infinitySelect

theorem scrHead_reference (read : ConstantBit 32768 → Bool) (a : Nat) :
    blockReference read a (.plain scrHead : Block 32768) = scrHeadProgram := by
  simp only [blockReference,Block.code,scrHead,scrHeadProgram,specialize_append,specialize_literal,
    ECDSAAdd.ShorPort.Tmpl.instantiate_append,ECDSAAdd.ShorPort.Tmpl.instantiate_lit]

theorem flip_reference (read : ConstantBit 32768 → Bool) (a : Nat) :
    blockReference read a (.plain (wLiteral [.X 838]) : Block 32768) = [.X 838] := by
  simp only [blockReference,Block.code,specialize_literal,ECDSAAdd.ShorPort.Tmpl.instantiate_lit]

local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨ShorECDLP.Secp256k1.p_prime⟩

/-- From a live state, the bank is clean at every masked site of `row2`, at any address. -/
theorem row2_clean (P : List Wire) (hP : InPool P)
    (hflip : ∀ w ∈ P, w ∉ ECDSAAdd.wires ([.X 838] : ECDSAAdd.Program))
    (hhead : ∀ w ∈ P, w ∉ ECDSAAdd.wires scrHeadProgram)
    (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (a : Nat) (s : BasisState) (hs : liveReady s) :
    CodeClean (readConstant coeffs Q) P a row2 ⟨false,s⟩ := by
  let C := Single.Physical.tablePoint coeffs Q a
  have hC : C ≠ 0 := hn _
  have hord : ShorECDLP.order • C = 0 := Single.Physical.tablePoint_order coeffs Q hQ a
  obtain ⟨P0,hP0⟩ := hs.1.2
  have work : ECDSAAdd.regValue streamLayout.work s = 0 :=
    (regValue_zero _ _).mpr (fun w hw => hs.2.1 w (List.mem_append_left _ hw))
  have h838 : (838 : Wire) ∉ streamLayout.work := by
    intro hm; have h := streamWork_lower _ hm; norm_num at h
  have pool : ECDSAAdd.regValue streamLayout.work (flipInfinity s) = 0 :=
    (reg_update_outside _ _ _ _ h838).trans work
  have clean (w : Wire) (hw : w ∈ streamLayout.inPlaceFlags ++ streamLayout.dialogPool) :
      flipInfinity s w = false := (regValue_zero _ _).mp pool w (one_boundary_work_subset streamLayout hw)
  have initial : PointDialogBoundary streamLayout (Bridge.toB P0) true (fun _=>false) (flipInfinity s) := by
    refine ⟨flipInfinity_holds s (Bridge.toB P0) (StreamPoint.of_coordinates s P0 hs.1.1.1.1 hP0),?_,?_,?_⟩
    · simpa [streamLayout_control,flipInfinity,ECDSAAdd.writeBit] using hs.1.1.1.2
    · intro w hw; exact clean w (by simp [hw])
    · exact (regValue_zero _ _).mpr (fun w hw => clean w (by simp [hw]))
  have sclean : Clean P s := fun w hw =>
    hs.2.1 w (List.mem_append_left _ (one_boundary_work_subset streamLayout (List.mem_append_right _ (hP w hw))))
  have pre : CodeClean (readConstant coeffs Q) P a rowPre ⟨false,s⟩ := by
    refine ⟨trivial, fun m _ => ⟨trivial, fun m' _ => ⟨?_, fun _ _ => ⟨trivial, fun _ _ => trivial⟩⟩⟩⟩
    intro w hw
    rw [scrHead_reference, flip_reference,
      ECDSAAdd.run_preserves_outside _ _ _ w (hhead w hw),
      ECDSAAdd.run_preserves_outside _ _ _ w (hflip w hw)]
    exact sclean w hw
  cases he : Bridge.toB C with
  | zero =>
    have hzero : C = 0 := congrArg ECDSAAdd.ShorPort.toA he
    exact (hC hzero).elim
  | @some cx cy hc =>
    have ce : C = toA (.some hc) := congrArg toA he
    have hr : RowReads (readConstant coeffs Q) (probeRows a) (.some hc) :=
      readConstant_rowReads coeffs Q _ _ ce
    have ho : ShorECDLP.order • (.some hc : Point) = 0 := by rw [← he]; exact hord
    have hp2 := torsion_unit_remainder_ne_zero (.some hc) ShorECDLP.order 2
      (WeierstrassCurve.Affine.Point.some_ne_zero hc) ho (by norm_num [ShorECDLP.order])
    have hp3 := torsion_unit_remainder_ne_zero (.some hc) ShorECDLP.order 3
      (WeierstrassCurve.Affine.Point.some_ne_zero hc) ho (by norm_num [ShorECDLP.order])
    have hd : (.some hc : Point)+.some hc ≠ 0 := by simpa only [two_nsmul] using hp2
    have ht : (.some hc : Point)+.some hc+.some hc ≠ 0 := by
      simpa only [show (3 : Nat) = 2+1 from rfl,succ_nsmul,two_nsmul] using hp3
    have en := enables_true hc hd ht
    have hdo : ShorECDLP.order • ((.some hc : Point)+.some hc) = 0 := by rw [nsmul_add,ho,zero_add]
    rw [row2_split]
    apply clean_append _ _ _ rowPre _ _ pre
    intro m _
    have bd := rowPre_boundary (readConstant coeffs Q) a (Bridge.toB P0) hc hr en.1 en.2 hd hdo s initial hs.2.2 m
    have g := generic2_clean (readConstant coeffs Q) a P hP probeRows (Bridge.toB P0) true
      (flags streamLayout (Bridge.toB P0) (.some hc) true cy) hc hr (flags_generic (Bridge.toB P0) hc) _ bd
    apply clean_append _ _ _ (generic2 probeRows) rowPost _ g.1
    intro m' _
    exact ⟨g.2 m', fun _ _ => ⟨trivial, fun _ _ => ⟨trivial, fun _ _ => trivial⟩⟩⟩

end
end ShorECDLP.Entrant.PathShare

/-! ### Resources of a bank program -/

namespace ShorECDLP.Entrant.PathShare
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-- Every traversal and every measured clear has a valid layout. -/
def BlockLay {n} (B : Bank) : Block n → Prop
  | .plain code => LookupLayouts B.bits B.paths windowRoot (normalizeW code)
  | .masked site => LookupLayouts B.bits B.paths windowRoot (normalizeW site.prefix) ∧
      (tableAddressTree B.high 0 1).Layout site.guard B.hp

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

def blockTP {n} (B : Bank) : Block n → Nat
  | .plain code => literalToffolis (normalizeW code) + traversals code * (2^B.bits.length - 1)
  | .masked site => literalToffolis (normalizeW site.prefix) + traversals site.prefix * (2^B.bits.length - 1) +
      ((tableAddressTree B.high 0 1).internalNodes + 127)

def codeTP {n} (B : Bank) : Code n → Nat
  | [] => 0
  | b::code => blockTP B b + codeTP B code

theorem clearP_tCount {n} (read : ConstantBit n → Bool) (B : Bank) (site : MaskedSite n)
    (hl : (tableAddressTree B.high 0 1).Layout site.guard B.hp) (start : Nat) (history : Fin start → Bool) :
    ((clearP B site start).instantiate read history).tCount =
      7 * ((tableAddressTree B.high 0 1).internalNodes + 127) := by
  unfold clearP
  exact MeasuredClear.measuredClear_tCount _ _ _ _ _ _ _ hl read start history

theorem blockProgP_tCount {n} (read : ConstantBit n → Bool) (B : Bank) (b : Block n) (hl : BlockLay B b)
    (start : Nat) (history : Fin start → Bool) :
    ((blockProgP B b start).instantiate read history).tCount = 7 * blockTP B b := by
  cases b with
  | plain code =>
    have hl' : LookupLayouts B.bits B.paths windowRoot (normalizeW code) := hl
    rw [blockProgP, WEX.compile_tCount read _ _ _ _ hl' start history, traversals_normalize]
    simp only [blockTP]; ring
  | masked site =>
    obtain ⟨h1, h2⟩ := hl
    rw [blockProgP, castFinish_instantiate,
      append_tCount_fixed _ _ _ _ _ (fun h => clearP_tCount read B site h2 _ h),
      WEX.compile_tCount read _ _ _ _ h1 start history, traversals_normalize]
    simp only [blockTP]; ring

theorem programP_tCount {n} (read : ConstantBit n → Bool) (B : Bank) (code : Code n)
    (hl : ∀ b ∈ code, BlockLay B b) (start : Nat) (history : Fin start → Bool) :
    ((programP B code start).instantiate read history).tCount = 7 * codeTP B code := by
  induction code generalizing start with
  | nil => simp [programP, recordsP, codeTP, Straight.instantiate, AdaptiveCircuit.tCount]
  | cons b code ih =>
    rw [programP, castFinish_instantiate,
      append_tCount_fixed _ _ _ _ _ (fun h => ih (fun d hd => hl d (by simp [hd])) _ h),
      blockProgP_tCount read B b (hl b (by simp))]
    simp only [codeTP]; ring

def blockSP {n} (B : Bank) : Block n → Nat
  | .plain code => codeSlots B.bits (normalizeW code)
  | .masked site => codeSlots B.bits (normalizeW site.prefix) +
      (512 * site.ports.length * (tableAddressTree B.high 0 1).leaves +
        10 * (tableAddressTree B.high 0 1).internalNodes + 1020)

def codeSP {n} (B : Bank) : Code n → Nat
  | [] => 0
  | b::code => blockSP B b + codeSP B code

theorem blockProgP_slots {n} (B : Bank) (b : Block n) (hl : BlockLay B b) (start : Nat) :
    (blockProgP B b start).gateSlots = blockSP B b := by
  cases b with
  | plain code =>
    have hl' : LookupLayouts B.bits B.paths windowRoot (normalizeW code) := hl
    rw [blockProgP, WEX.compile_slots _ _ _ _ hl' start]
    rfl
  | masked site =>
    obtain ⟨h1, h2⟩ := hl
    rw [blockProgP, castFinish_gateSlots, Straight.gateSlots_append, WEX.compile_slots _ _ _ _ h1 start]
    have hc : (clearP B site (start + codeRecords B.bits B.paths windowRoot (normalizeW site.prefix))).gateSlots =
        512 * site.ports.length * (tableAddressTree B.high 0 1).leaves +
          10 * (tableAddressTree B.high 0 1).internalNodes + 1020 := by
      unfold clearP
      rw [MeasuredClear.measuredClear_slots _ _ _ _ _ _ _ h2]
      simp [clearData]
    rw [hc]
    rfl

theorem programP_slots {n} (B : Bank) (code : Code n) (hl : ∀ b ∈ code, BlockLay B b) (start : Nat) :
    (programP B code start).gateSlots = codeSP B code := by
  induction code generalizing start with
  | nil => rfl
  | cons b code ih =>
    rw [programP, castFinish_gateSlots, Straight.gateSlots_append, blockProgP_slots B b (hl b (by simp)),
      ih (fun d hd => hl d (by simp [hd]))]
    rfl

theorem codeSP_congr {n} (B B' : Bank) (hb : B.bits = B'.bits) (hh : B.high = B'.high) (code : Code n) :
    codeSP B code = codeSP B' code := by
  induction code with
  | nil => rfl
  | cons b code ih => cases b <;> simp [codeSP, blockSP, hb, hh, ih]

theorem codeTP_congr {n} (B B' : Bank) (hb : B.bits = B'.bits) (hh : B.high = B'.high) (code : Code n) :
    codeTP B code = codeTP B' code := by
  induction code with
  | nil => rfl
  | cons b code ih => cases b <;> simp [codeTP, blockTP, hb, hh, ih]

theorem blockRecP_eq {n} (B B' : Bank) (hb : B.bits = B'.bits) (hh : B.high = B'.high) (b : Block n)
    (hl : BlockLay B b) (hl' : BlockLay B' b) : blockRecP B b = blockRecP B' b := by
  cases b with
  | plain code =>
    have h : LookupLayouts B.bits B.paths windowRoot (normalizeW code) := hl
    have h' : LookupLayouts B'.bits B'.paths windowRoot (normalizeW code) := hl'
    simp only [blockRecP]
    rw [codeRecords_eq _ _ _ _ h, codeRecords_eq _ _ _ _ h', hb]
  | masked site =>
    obtain ⟨h1,h2⟩ := hl
    obtain ⟨h1',h2'⟩ := hl'
    simp only [blockRecP]
    rw [codeRecords_eq _ _ _ _ h1, codeRecords_eq _ _ _ _ h1', hb,
      (MeasuredClear.recordUnary_counts _ _ _ h2 0).1, (MeasuredClear.recordUnary_counts _ _ _ h2' 0).1, hh]

theorem recordsP_eq {n} (B B' : Bank) (hb : B.bits = B'.bits) (hh : B.high = B'.high) (code : Code n)
    (hl : ∀ b ∈ code, BlockLay B b) (hl' : ∀ b ∈ code, BlockLay B' b) : recordsP B code = recordsP B' code := by
  induction code with
  | nil => rfl
  | cons b code ih =>
    simp only [recordsP]
    rw [blockRecP_eq B B' hb hh b (hl b (by simp)) (hl' b (by simp)),
      ih (fun d hd => hl d (by simp [hd])) (fun d hd => hl' d (by simp [hd]))]

theorem programP_residue {n} (B : Bank) (code : Code n) (start : Nat) :
    AndGadget.residue (programP B code start) = 0 := by
  induction code generalizing start with
  | nil => simp [programP, recordsP]
  | cons b code ih =>
    have hb : AndGadget.residue (blockProgP B b start) = 0 := by
      cases b with
      | plain code => exact WEXCredit.compile_residue _ _ _ _ _
      | masked site =>
        simp [blockProgP, AndGadget.residue_cast, AndGadget.residue_append, WEXCredit.compile_residue,
          clearP, MeasuredClear.measuredClear_residue]
    simp [programP, AndGadget.residue_cast, AndGadget.residue_append, hb, ih]

theorem compile_wellFormedL {n : Nat} (bits paths : List Wire) (root : Wire) (code : WCode n)
    (hl : bits.length ≤ paths.length) (hp : ∀ i ∈ code, LPlaced bits paths root i)
    (hv : ∀ p, WInstr.literal p ∈ code → ∀ i ∈ p, ECDSAAdd.Challenge.instructionValid i)
    (start : Nat) : (compile bits paths root code start).WellFormed := by
  induction code generalizing start with
  | nil => trivial
  | cons i code ih =>
    have ht := ih (fun j hj => hp j (List.mem_cons_of_mem _ hj))
      (fun p hm => hv p (List.mem_cons_of_mem _ hm))
    have hi := hp i (by simp)
    cases i with
    | literal p =>
      simp only [compile, NaiveChallenge.wellFormed_castFinish]
      apply straight_append_wellFormed
      · apply Bridge.translate_wellFormed
        intro j hj
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hj
        exact hv p (by simp) k hk
      · exact ht _
    | lookup c p =>
      have hi' : PlacedPair bits paths root (.lookup c p : WInstr n) := hi
      dsimp only [PlacedPair] at hi'
      simp only [compile, NaiveChallenge.wellFormed_castFinish]
      apply straight_append_wellFormed
      · apply portProgram_wellFormed _ _ _ _ _ hl hi'.1
        exact List.disjoint_left.mpr (fun w hw hm =>
          List.disjoint_left.mp hi'.2.2.2 (List.mem_cons_of_mem root hw) hm)
      · exact ht _

theorem clearP_wellFormed {n} (B : Bank) (hB : BankOK B) (site : MaskedSite n) (hg : SiteGeoP B site)
    (start : Nat) : (clearP B site start).WellFormed := by
  obtain ⟨-,hbd,hhot,hmem,hsm,hgl,-⟩ := kind_facts site hg.kind
  have hlast := hg.placed (.lookup (some site.guard) site.ports) (by simp [MaskedSite.code])
  dsimp only [Placed] at hlast
  have notT : ∀ w ∈ site.guard :: B.high ++ B.hp, w ∉ portTargets site.ports := by
    intro w hw ht
    have h2 := (hbd w ht).1
    simp only [List.mem_append,List.mem_cons] at hw
    rcases hw with (h | h) | h
    · rw [h] at h2; rcases hgl with e | e <;> rw [e] at h2 <;> dsimp only [Wire] at h2 <;> omega
    · have := hB.high w h
      dsimp only [Wire] at *; omega
    · exact List.disjoint_left.mp hlast.2.2
        (show w ∈ windowRoot :: lookupRoot windowRoot (some site.guard) :: B.bits ++ B.paths by
          simp [hB.sub w h]) ht
  unfold clearP
  apply MeasuredClear.measuredClear_wellFormed
  · exact tableAddressTree_layout B.high B.hp site.guard 0 1 hB.len (site_tree_nodup B hB site hg)
  · intro i j he; apply Fin.ext; rw [hhot i,hhot j] at he; dsimp only [Wire] at he; omega
  · intro i j he
    have h1 := (hbd _ (hmem j)).1
    have h2 := low_lt i
    rw [← he] at h1
    dsimp only [Wire] at *
    omega
  · rw [hB.index]
    intro hm
    exact notT _ (by simp only [List.mem_append,List.mem_cons] at hm ⊢; tauto) hsm
  · intro hm
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hm
    rw [hhot i] at hi
    dsimp only [Wire] at hi
    omega

theorem programP_wellFormed {n} (B : Bank) (hB : BankOK B) (code : Code n) (hg : ∀ b ∈ code, BlockGeoP B b)
    (hp : ∀ p, WInstr.literal p ∈ erase code → ECDSAAdd.Arithmetic.GatePhysical p) (start : Nat) :
    (programP B code start).WellFormed := by
  induction code generalizing start with
  | nil => trivial
  | cons b code ih =>
    rw [programP,castFinish_wellFormed]
    apply straight_append_wellFormed
    · have hgb := hg b (by simp)
      have hpb : ∀ p, WInstr.literal p ∈ b.code → ECDSAAdd.Arithmetic.GatePhysical p := fun p hm => hp p (by simp [erase_cons,hm])
      cases b with
      | plain code =>
        have hg' : LitAvoid B.bits code := hgb
        exact compile_wellFormedL _ _ _ _ hB.bitsLen (lplaced_normalize _ _ _ _ (litAvoid_placed _ _ code hg'))
          (normalized_literals_valid code hpb) start
      | masked site =>
        have hg' : SiteGeoP B site := hgb
        have hpref : ∀ i ∈ site.prefix, LPlaced B.bits B.paths windowRoot i := fun i hi =>
          pair_of_placed_lit _ _ i (placed_implies_pair _ _ _ _ (hg'.placed i (List.mem_append_left _ hi)))
        have hphys : ∀ p, WInstr.literal p ∈ site.prefix → ECDSAAdd.Arithmetic.GatePhysical p := by
          intro p hm; exact hpb p (List.mem_append_left _ hm)
        rw [blockProgP,castFinish_wellFormed]
        exact straight_append_wellFormed _ _
          (compile_wellFormedL _ _ _ _ hB.bitsLen (lplaced_normalize _ _ _ _ hpref)
            (normalized_literals_valid site.prefix hphys) start)
          (clearP_wellFormed B hB site hg' _)
    · exact ih (fun d hd => hg d (by simp [hd])) (fun p hm => hp p (by simp [erase_cons,hm])) _

end
end ShorECDLP.Entrant.PathShare

namespace ShorECDLP.Entrant.PathShare
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

theorem clearP_support {n} (B : Bank) (hB : BankOK B) (site : MaskedSite n) (hk : SiteKind site)
    (S : List Wire) (hS : portTargets site.ports ⊆ S) (hgS : site.guard ∈ S) (hlow : ∀ i, low i ∈ S)
    (hhigh : B.high ⊆ S) (hpaths : B.paths ⊆ S) (start : Nat) :
    ChallengeMigration.straightWires (clearP B site start) ⊆ S := by
  obtain ⟨-,-,-,hmem,hsm,-,-⟩ := kind_facts site hk
  have hscratch : scratch site ∈ (clearData site.ports).map MeasuredClear.ClearPort.target := by
    rw [clearData_targets]
    exact hsm
  unfold clearP
  rw [support_agrees]
  apply List.Subset.trans (MeasuredClear.measuredClear_static _ _ _ _ _ _ _ hscratch start)
  intro w hw
  simp only [MeasuredClear.clearSupport,clearData_targets,hB.index,MeasuredClear.hotBank,
    List.mem_append,List.mem_cons,or_assoc] at hw
  rcases hw with hs | hl | hh | hr | hb | hp
  · exact hS hs
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hl
    exact hlow i
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hh
    exact hS (hmem i)
  · rw [hr]; exact hgS
  · exact hhigh hb
  · exact hpaths (hB.sub _ hp)

theorem normalized_lit_support {n} (code : WCode n) (S : List Wire)
    (h : ∀ p, WInstr.literal p ∈ code → ECDSAAdd.wires p ⊆ S.toFinset) :
    ∀ p, WInstr.literal p ∈ normalizeW code → ECDSAAdd.wires p ⊆ S.toFinset := by
  intro p hp
  rw [normalizeW] at hp
  obtain ⟨j,hj,he⟩ := List.mem_map.mp hp
  cases j with
  | literal q =>
    cases he
    rw [ECDSAAdd.Baselines.normalize_wires]
    exact h q hj
  | lookup c ps => cases he

theorem normalized_look_support {n} (code : WCode n) (S : List Wire)
    (h : ∀ c ps, WInstr.lookup c ps ∈ code → (∀ q ∈ c, q ∈ S) ∧ portTargets ps ⊆ S) :
    ∀ c ps, WInstr.lookup c ps ∈ normalizeW code → (∀ q ∈ c, q ∈ S) ∧ portTargets ps ⊆ S := by
  intro c ps hp
  rw [normalizeW] at hp
  obtain ⟨j,hj,he⟩ := List.mem_map.mp hp
  cases j with
  | literal q => cases he
  | lookup d qs => cases he; exact h c ps hj

theorem programP_support {n} (B : Bank) (hB : BankOK B) (code : Code n) (hg : ∀ b ∈ code, BlockGeoP B b)
    (S : List Wire) (hroot : windowRoot ∈ S) (hbits : B.bits ⊆ S) (hpaths : B.paths ⊆ S)
    (hlow : ∀ i, low i ∈ S) (hhigh : B.high ⊆ S)
    (hlit : ∀ p, WInstr.literal p ∈ erase code → ECDSAAdd.wires p ⊆ S.toFinset)
    (hlook : ∀ c ps, WInstr.lookup c ps ∈ erase code → (∀ q ∈ c, q ∈ S) ∧ portTargets ps ⊆ S)
    (start : Nat) : ChallengeMigration.straightWires (programP B code start) ⊆ S := by
  induction code generalizing start with
  | nil => simp [programP,recordsP,ChallengeMigration.straightWires]
  | cons b code ih =>
    have hlb : ∀ p, WInstr.literal p ∈ b.code → ECDSAAdd.wires p ⊆ S.toFinset :=
      fun p hm => hlit p (by simp [erase_cons,hm])
    have hkb : ∀ c ps, WInstr.lookup c ps ∈ b.code → (∀ q ∈ c, q ∈ S) ∧ portTargets ps ⊆ S :=
      fun c ps hm => hlook c ps (by simp [erase_cons,hm])
    rw [programP,support_cast,straightWires_append]
    refine List.append_subset.mpr ⟨?_, ih (fun d hd => hg d (by simp [hd]))
      (fun p hm => hlit p (by simp [erase_cons,hm])) (fun c ps hm => hlook c ps (by simp [erase_cons,hm])) _⟩
    cases b with
    | plain code =>
      exact compile_support _ _ _ _ S hroot hbits hpaths (normalized_lit_support code S hlb)
        (normalized_look_support code S hkb) start
    | masked site =>
      have hg' : SiteGeoP B site := hg (.masked site) (by simp)
      have hpl : ∀ p, WInstr.literal p ∈ site.prefix → ECDSAAdd.wires p ⊆ S.toFinset :=
        fun p hm => hlb p (List.mem_append_left _ hm)
      have hpk : ∀ c ps, WInstr.lookup c ps ∈ site.prefix → (∀ q ∈ c, q ∈ S) ∧ portTargets ps ⊆ S :=
        fun c ps hm => hkb c ps (List.mem_append_left _ hm)
      have hlast := hkb (some site.guard) site.ports (by simp [Block.code,MaskedSite.code])
      rw [blockProgP,support_cast,straightWires_append]
      exact List.append_subset.mpr ⟨compile_support _ _ _ _ S hroot hbits hpaths
        (normalized_lit_support _ S hpl) (normalized_look_support _ S hpk) start,
        clearP_support B hB site hg'.kind S hlast.2 (hlast.1 site.guard (Option.mem_def.mpr rfl)) hlow hhigh hpaths _⟩

end
end ShorECDLP.Entrant.PathShare

/-! ### The pool path bank of the fused row -/

namespace ShorECDLP.Entrant.PathShare
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 40000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-- Fifteen dialog-pool wires used only by the plain arithmetic of the generic branch. -/
def pathBank : List Wire := List.range' 14832 15

def bank15 : Bank := ⟨windowBits, WEXUnlookup.high, pathBank.take 8, pathBank⟩
def old15 : Bank := ⟨windowBits, WEXUnlookup.high, WEXUnlookup.highPaths, windowPaths⟩
def bank14 : Bank := ⟨WEXUnlookupWidth14.bits, WEXUnlookupWidth14.high, pathBank.take 7, pathBank⟩
def old14 : Bank := ⟨WEXUnlookupWidth14.bits, WEXUnlookupWidth14.high, WEXUnlookupWidth14.highPaths, windowPaths⟩

theorem pathBank_pool : InPool pathBank := by
  intro q hq
  rw [pathBank,List.mem_range'_1] at hq
  have hp : streamLayout.dialogPool = ((List.range' 4115 5699).map streamWire).take 2613 := rfl
  rw [hp,List.mem_iff_getElem]
  refine ⟨q - 14115,by simp only [List.length_take,List.length_map,List.length_range']; rw [Nat.min_eq_left (by norm_num)]; omega,?_⟩
  simp only [List.getElem_take,List.getElem_map,List.getElem_range']
  unfold streamWire
  dsimp only [Wire] at *
  split_ifs <;> omega

/-- Disjointness from the bank by a single pass over the other list. -/
theorem pathBank_not_of (L : List Wire) (hL : (L.all fun b => decide (b < 14832 ∨ 14847 ≤ b)) = true) :
    ∀ w ∈ pathBank, w ∉ L := by
  intro w hw hm
  have h1 := List.all_eq_true.mp hL w hm
  simp only [decide_eq_true_eq] at h1
  simp only [pathBank, List.mem_range'_1] at hw
  dsimp only [Wire] at *
  omega

theorem pathBank_nodup : pathBank.Nodup := List.nodup_range'

theorem pathBank_window : ∀ w ∈ windowRoot :: windowBits ++ windowPaths, w ∉ pathBank := by
  intro w hw hp
  exact pathBank_not_of _ (by decide +kernel) w hp hw

theorem pathBank_out : ∀ w ∈ pathBank, 871 ≤ w := by
  unfold pathBank
  decide +kernel

theorem pathBank_flip : ∀ w ∈ pathBank, w ∉ ECDSAAdd.wires ([.X 838] : ECDSAAdd.Program) := by
  intro w hw hm
  simp [ECDSAAdd.wires, ECDSAAdd.Instr.wires] at hm
  subst hm
  revert hw
  unfold pathBank
  decide +kernel


theorem bank15_ok : BankOK bank15 where
  split := WEXUnlookup.splitAddress
  high := by
    unfold bank15 WEXUnlookup.high
    decide +kernel
  index := tableAddressTree_index _ 0 1 (by decide +kernel)
  nodup := by decide +kernel
  len := by decide +kernel
  sub := fun _ hw => List.mem_of_mem_take hw
  out := fun w hw => pathBank_out w (List.mem_of_mem_take hw)
  bitsLen := by decide +kernel

theorem bank14_ok : BankOK bank14 where
  split := WEXUnlookupWidth14.splitAddress
  high := by
    unfold bank14 WEXUnlookupWidth14.high
    decide +kernel
  index := tableAddressTree_index _ 0 1 (by decide +kernel)
  nodup := by decide +kernel
  len := by decide +kernel
  sub := fun _ hw => List.mem_of_mem_take hw
  out := fun w hw => pathBank_out w (List.mem_of_mem_take hw)
  bitsLen := by decide +kernel

/-! A Boolean wire check, so concrete sites are discharged by `decide +kernel`. -/

def corrList : List ECDSAAdd.Correction → List Wire
  | [] => []
  | .Z t :: cs => t :: corrList cs
  | .CZ a b :: cs => a :: b :: corrList cs

def instrList : ECDSAAdd.Instr → List Wire
  | .X t => [t]
  | .CX c t => [c, t]
  | .CCX a b t => [a, b, t]
  | .measureX t c₀ c₁ => t :: (corrList c₀ ++ corrList c₁)

def progAvoid (P : List Wire) (p : ECDSAAdd.Program) : Bool :=
  p.all fun i => (instrList i).all fun w => !(P.contains w)

def avoidW {n} (P : List Wire) : WInstr n → Bool
  | .literal p => progAvoid P p
  | .lookup c ps => (portTargets ps).all (fun w => !(P.contains w)) && c.all (fun q => !(P.contains q))

theorem corr_mem (cs : List ECDSAAdd.Correction) (w : Wire) (h : w ∈ ECDSAAdd.correctionWires cs) :
    w ∈ corrList cs := by
  induction cs with
  | nil => simp [ECDSAAdd.correctionWires] at h
  | cons c cs ih =>
    cases c with
    | Z t =>
      simp only [ECDSAAdd.correctionWires, Finset.mem_union, Finset.mem_singleton] at h
      rcases h with h | h
      · simp [corrList, h]
      · exact List.mem_cons_of_mem _ (ih h)
    | CZ a b =>
      simp only [ECDSAAdd.correctionWires, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with (h | h) | h
      · simp [corrList, h]
      · simp [corrList, h]
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih h))

theorem instr_mem (i : ECDSAAdd.Instr) (w : Wire) (h : w ∈ i.wires) : w ∈ instrList i := by
  cases i with
  | X t => simpa [ECDSAAdd.Instr.wires, instrList] using h
  | CX c t => simpa [ECDSAAdd.Instr.wires, instrList] using h
  | CCX a b t => simpa [ECDSAAdd.Instr.wires, instrList] using h
  | measureX t c₀ c₁ =>
    simp only [ECDSAAdd.Instr.wires, Finset.mem_union, Finset.mem_singleton] at h
    simp only [instrList, List.mem_cons, List.mem_append]
    rcases h with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (corr_mem _ _ h))
    · exact Or.inr (Or.inr (corr_mem _ _ h))

theorem progAvoid_sound (P : List Wire) (p : ECDSAAdd.Program) (h : progAvoid P p = true) :
    ∀ w ∈ P, w ∉ ECDSAAdd.wires p := by
  intro w hw hm
  induction p with
  | nil => simp [ECDSAAdd.wires] at hm
  | cons i p ih =>
    simp only [progAvoid, List.all_cons, Bool.and_eq_true] at h
    simp only [ECDSAAdd.wires, Finset.mem_union] at hm
    rcases hm with hm | hm
    · have := List.all_eq_true.mp h.1 w (instr_mem i w hm)
      simp at this
      exact this hw
    · exact ih h.2 hm

theorem pathBank_head : ∀ w ∈ pathBank, w ∉ ECDSAAdd.wires scrHeadProgram :=
  progAvoid_sound pathBank scrHeadProgram (by unfold pathBank scrHeadProgram; decide +kernel)

theorem avoidW_lookup {n} (P : List Wire) (c : Option Wire) (ps : List (LookupPort n))
    (h : avoidW P (.lookup c ps) = true) :
    (∀ w ∈ P, w ∉ portTargets ps) ∧ ∀ q ∈ c, q ∉ P := by
  unfold avoidW at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun w hw ht => ?_, fun q hq hp => ?_⟩
  · have := List.all_eq_true.mp h1 w ht
    simp at this
    exact this hw
  · cases c with
    | none => simp at hq
    | some q' =>
      simp only [Option.mem_def, Option.some.injEq] at hq
      subst hq
      simp [Option.all] at h2
      exact h2 hp

end
end ShorECDLP.Entrant.PathShare

namespace ShorECDLP.Entrant.PathShare
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 40000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-- Every literal and every lookup of the code avoids the pool path bank. -/
def Avoids (code : WCode 32768) : Prop :=
  (∀ p, WInstr.literal p ∈ code → ∀ w ∈ pathBank, w ∉ ECDSAAdd.wires p) ∧
    (∀ c ps, WInstr.lookup c ps ∈ code → (∀ w ∈ pathBank, w ∉ portTargets ps) ∧ ∀ q ∈ c, q ∉ pathBank)

theorem avoids_of_all (code : WCode 32768) (h : code.all (avoidW pathBank) = true) : Avoids code :=
  ⟨fun p hp => progAvoid_sound pathBank p (List.all_eq_true.mp h _ hp),
    fun c ps hp => avoidW_lookup pathBank c ps (List.all_eq_true.mp h _ hp)⟩

theorem avoids_append {a b : WCode 32768} (ha : Avoids a) (hb : Avoids b) : Avoids (a ++ b) := by
  refine ⟨fun p hp => ?_, fun c ps hp => ?_⟩
  · rcases List.mem_append.mp hp with h | h
    · exact ha.1 p h
    · exact hb.1 p h
  · rcases List.mem_append.mp hp with h | h
    · exact ha.2 c ps h
    · exact hb.2 c ps h

theorem avoids_lit (p : ECDSAAdd.Program) (h : ∀ w ∈ pathBank, w ∉ ECDSAAdd.wires p) :
    Avoids (wLiteral (n := 32768) p) := by
  refine ⟨fun q hq => ?_, fun c ps hp => ?_⟩
  · simp only [wLiteral, List.mem_singleton, WInstr.literal.injEq] at hq
    rw [hq]; exact h
  · simp [wLiteral] at hp

theorem scrNegP_avoid : ∀ w ∈ pathBank, w ∉ ECDSAAdd.wires WEX.scrNegP :=
  WEX.neg_disjoint (negateYLayout streamLayout) streamLayout.core.equalNegY ECDSAAdd.p SquareReduction.c
    (negateYLayout_widths streamLayout streamLayout_widths).2 pathBank (pathBank_not_of _ (by decide +kernel))

/-! The scratch wire lists in explicit form (pool position `i` is wire `14115 + i`), so the kernel
checks below never evaluate pool positions through the layout. -/

theorem pbPairWires_eq : WEX.scrPairWires = 14373 :: List.range' 14374 256 ++ [14883] := by
  simp only [WEX.scrPairWires, WEX.map_poolWire _ _ (by norm_num : 259 + 256 ≤ 5699),
    WEX.poolWire_eq _ (by norm_num : 258 < 5699), WEX.poolWire_eq _ (by norm_num : 768 < 5699)]

theorem pbShortWires_eq : WEX.scrShortWires = 14884 :: List.range' 14885 256 ++ [15141] := by
  simp only [WEX.scrShortWires, WEX.map_poolWire _ _ (by norm_num : 770 + 256 ≤ 5699),
    WEX.poolWire_eq _ (by norm_num : 769 < 5699), WEX.poolWire_eq _ (by norm_num : 1026 < 5699)]

theorem pbExtraWires_eq : WEX.scrDExtraWires = List.range' 15399 255 := by
  simp only [WEX.scrDExtraWires, WEX.map_poolWire _ _ (by norm_num : 1284 + 255 ≤ 5699)]

theorem avoids_lookup {c : Option Wire} {ps : List (LookupPort 32768)}
    (ht : ∀ w ∈ pathBank, w ∉ portTargets ps) (hc : ∀ q ∈ c, q ∉ pathBank) :
    Avoids [.lookup c ps] := by
  refine ⟨fun p hp => ?_, fun c' ps' hp => ?_⟩
  · simp at hp
  · simp only [List.mem_singleton, WInstr.lookup.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    exact ⟨ht, hc⟩

theorem scrDLookup_avoids : Avoids [WInstr.lookup (some windowRoot) (WEX.scrDPorts probeRows)] := by
  refine avoids_lookup ?_ ?_
  · rw [WEX.scrDPorts_targets, WEX.scrAllWires, WEX.scrWires, pbPairWires_eq, pbShortWires_eq,
      pbExtraWires_eq]
    exact pathBank_not_of _ (by decide +kernel)
  · intro q hq
    rw [Option.mem_def, Option.some.injEq] at hq
    subst hq
    exact fun h => pathBank_not_of [windowRoot] (by decide +kernel) _ h List.mem_cons_self

theorem sfxCC_avoids : Avoids WEX.sfxCC := by
  simp only [WEX.sfxCC, WEX.scrDWires, pbShortWires_eq, pbExtraWires_eq]
  exact avoids_of_all _ (by unfold pathBank; decide +kernel)

theorem scrDMiddle_avoids : Avoids WEX.scrDMiddle := by
  simp only [WEX.scrDMiddle, pbPairWires_eq, pbShortWires_eq]
  repeat' (with_reducible apply avoids_append)
  all_goals exact avoids_of_all _ (by unfold pathBank; decide +kernel)

/-- The output site, split so that the negation program is bounded by its layout. -/
theorem scrD_avoids : Avoids scrDSite.code := by
  have hP : Avoids (wLiteral (n := 32768) WEX.scrNegP) := avoids_lit _ scrNegP_avoid
  rw [scrDSite_code, WEX.sfxMidF, WEX.cornersE_split]
  repeat' (with_reducible apply avoids_append)
  all_goals first
    | (with_reducible exact hP)
    | exact scrDLookup_avoids
    | exact sfxCC_avoids
    | exact scrDMiddle_avoids
    | exact avoids_of_all _ (by unfold pathBank; decide +kernel)

theorem pair_avoid (refsA refsB : Nat → Nat → ConstantBit 32768) :
    (∀ p, WInstr.literal p ∈ (pairSite refsA refsB).code → ∀ w ∈ pathBank, w ∉ ECDSAAdd.wires p) ∧
    (∀ c ps, WInstr.lookup c ps ∈ (pairSite refsA refsB).code →
      (∀ w ∈ pathBank, w ∉ portTargets ps) ∧ ∀ q ∈ c, q ∉ pathBank) := by
  have hw : ∀ w ∈ pathBank, w ∉ pairWireList := pathBank_not_of _ (by decide +kernel)
  have ht : ∀ w ∈ pathBank, w ∉ pairTargets := pathBank_not_of _ (by decide +kernel)
  have hg : streamLayout.core.generic ∉ pathBank := fun h =>
    pathBank_not_of [streamLayout.core.generic] (by decide +kernel) _ h List.mem_cons_self
  rw [pairSite_code]
  refine ⟨fun p hp => ?_, fun c ps hp => ?_⟩
  · rcases List.mem_cons.mp hp with h | h
    · cases h
    rcases List.mem_cons.mp h with h | h
    · cases h
      exact wires_avoid_of pairArith_subset hw
    · cases List.mem_singleton.mp h
  · have hp' : c = some streamLayout.core.generic ∧ ps = (pairSite refsA refsB).ports := by
      rcases List.mem_cons.mp hp with h | h
      · exact WInstr.lookup.inj h
      rcases List.mem_cons.mp h with h | h
      · cases h
      · exact WInstr.lookup.inj (List.mem_singleton.mp h)
    obtain ⟨rfl, rfl⟩ := hp'
    refine ⟨fun w hw' hm => ht w hw' (by rw [pairSite_targets] at hm; exact hm), fun q hq => ?_⟩
    rw [Option.mem_def, Option.some.injEq] at hq
    subst hq
    exact hg

theorem triple_avoid :
    (∀ p, WInstr.literal p ∈ (constSite streamLayout streamLayout.point.x (wFields probeRows .tripleX)).code →
      ∀ w ∈ pathBank, w ∉ ECDSAAdd.wires p) ∧
    (∀ c ps, WInstr.lookup c ps ∈ (constSite streamLayout streamLayout.point.x (wFields probeRows .tripleX)).code →
      (∀ w ∈ pathBank, w ∉ portTargets ps) ∧ ∀ q ∈ c, q ∉ pathBank) := by
  have hw : ∀ w ∈ pathBank, w ∉ (streamLayout.recoveryConstant streamLayout.point.x).wires :=
    pathBank_not_of _ (by decide +kernel)
  have ht : ∀ w ∈ pathBank, w ∉ (streamLayout.recoveryConstant streamLayout.point.x).src :=
    pathBank_not_of _ (by decide +kernel)
  have hg : streamLayout.core.generic ∉ pathBank := fun h =>
    pathBank_not_of [streamLayout.core.generic] (by decide +kernel) _ h List.mem_cons_self
  rw [constSite_code]
  refine ⟨fun p hp => ?_, fun c ps hp => ?_⟩
  · rcases List.mem_cons.mp hp with h | h
    · cases h
    rcases List.mem_cons.mp h with h | h
    · cases h
      exact wires_avoid_of (MeasuredCanonicalModLayout.program_wires_subset _ _ _) hw
    · cases List.mem_singleton.mp h
  · have hp' : c = some streamLayout.core.generic ∧
        ps = indexedPorts (streamLayout.recoveryConstant streamLayout.point.x).src (wFields probeRows .tripleX) true := by
      rcases List.mem_cons.mp hp with h | h
      · exact WInstr.lookup.inj h
      rcases List.mem_cons.mp h with h | h
      · cases h
      · exact WInstr.lookup.inj (List.mem_singleton.mp h)
    obtain ⟨rfl, rfl⟩ := hp'
    refine ⟨fun w hw' hm => ht w hw' (by rw [indexed_targets] at hm; exact hm), fun q hq => ?_⟩
    rw [Option.mem_def, Option.some.injEq] at hq
    subst hq
    exact hg

theorem scrIn_avoid : (WEX.scrInSite probeRows).code.all (avoidW pathBank) = true := by
  have hl : [WInstr.lookup (some windowRoot) (WEX.scrInPorts probeRows)].all (avoidW pathBank) = true := by
    simp only [List.all_cons, List.all_nil, Bool.and_true, avoidW, WEX.scrInPorts_targets, WEX.scrWires,
      pbPairWires_eq, pbShortWires_eq]
    unfold pathBank
    decide +kernel
  rw [WEX.scrInSite_code]
  simp only [List.all_append, Bool.and_eq_true]
  refine ⟨⟨hl, ?_⟩, hl⟩
  simp only [WEX.scrInArith, WEX.scrInMid, pbPairWires_eq, pbShortWires_eq]
  unfold pathBank
  decide +kernel


end
end ShorECDLP.Entrant.PathShare

/-! ### Geometry of the fused row on the pool bank -/

namespace ShorECDLP.Entrant.PathShare
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.ControlledPointLayout ECDSAAdd.Entrant
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 40000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

theorem plain_geoP (B : Bank) (hbits : ∀ w ∈ B.bits, w ∈ windowBits) (code : WCode 32768)
    (hold : ∀ i ∈ code, PlacedPair windowBits windowPaths windowRoot i)
    (hlit : ∀ i ∈ code, ∃ p, i = .literal p) : LitAvoid B.bits code := by
  intro i hi
  obtain ⟨p, rfl⟩ := hlit i hi
  refine ⟨p, rfl, ?_⟩
  intro w hw
  apply hold _ hi w
  rcases List.mem_cons.mp hw with h | h
  · simp [h]
  · simp [hbits w h]

theorem site_geoP (B : Bank) (hbits : ∀ w ∈ B.bits, w ∈ windowBits) (hbn : B.bits.Nodup)
    (hpaths : B.paths = pathBank) (site : MaskedSite 32768) (hold : WEXUnlookup.SiteGeometry site)
    (hlit : ∀ p, WInstr.literal p ∈ site.code → ∀ w ∈ pathBank, w ∉ ECDSAAdd.wires p)
    (hlook : ∀ c ps, WInstr.lookup c ps ∈ site.code →
      (∀ w ∈ pathBank, w ∉ portTargets ps) ∧ ∀ q ∈ c, q ∉ pathBank) :
    SiteGeoP B site := by
  refine ⟨?_, hold.kind⟩
  intro i hi
  have ho := hold.placed i hi
  rw [hpaths]
  cases i with
  | literal p =>
    intro w hw
    simp only [List.mem_cons, List.mem_append, or_assoc] at hw
    rcases hw with h | h | h
    · exact ho w (by simp [h])
    · exact ho w (by simp [hbits w h])
    · exact hlit p hi w h
  | lookup c ps =>
    dsimp only [Placed] at ho ⊢
    obtain ⟨hT, hC⟩ := hlook c ps hi
    have hq : lookupRoot windowRoot c ∉ pathBank := by
      cases c with
      | none => exact pathBank_window windowRoot (by simp)
      | some q => exact hC q (Option.mem_def.mpr rfl)
    have hqb : lookupRoot windowRoot c ∉ windowBits := by
      have h0 := ho.1
      rw [List.cons_append] at h0
      have := (List.nodup_cons.mp h0).1
      exact fun h => this (List.mem_append_left _ h)
    refine ⟨?_, ho.2.1, ?_⟩
    · rw [List.cons_append, List.nodup_cons]
      refine ⟨fun h => ?_, ?_⟩
      · rcases List.mem_append.mp h with h | h
        · exact hqb (hbits _ h)
        · exact hq h
      · rw [List.nodup_append]
        refine ⟨hbn, pathBank_nodup, ?_⟩
        intro a ha b hb e
        subst e
        exact pathBank_window a (by simp [hbits a ha]) hb
    · apply List.disjoint_left.mpr
      intro w hw ht
      simp only [List.mem_cons, List.mem_append, or_assoc] at hw
      rcases hw with h | h | h | h
      · exact List.disjoint_left.mp ho.2.2 (by simp [h]) ht
      · exact List.disjoint_left.mp ho.2.2 (by simp [h]) ht
      · exact List.disjoint_left.mp ho.2.2 (by simp [hbits w h]) ht
      · exact hT w h ht

theorem row2_masked_cases (site : MaskedSite 32768) (hb : Block.masked site ∈ row2) :
    site = WEX.scrInSite probeRows ∨ site = pairSite (wFields probeRows .negX) (wFields probeRows .negY) ∨
      site = constSite streamLayout streamLayout.point.x (wFields probeRows .tripleX) ∨
      site = pairSite (wFields probeRows .x) (wFields probeRows .negY) ∨ site = scrDSite := by
  rw [row2_split, generic2_list] at hb
  simp only [rowPre, rowPost, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    Block.masked.injEq, reduceCtorEq, false_or] at hb
  tauto

def isLit {n} : WInstr n → Bool
  | .literal _ => true
  | .lookup _ _ => false

def plainLit {n} : Block n → Bool
  | .plain c => c.all isLit
  | .masked _ => true

theorem row2_plainLit : row2.all plainLit = true := by
  decide +kernel

theorem row2_plain_lit (code : WCode 32768) (hb : Block.plain code ∈ row2) : WEX.LitOnly code := by
  have h : code.all isLit = true := List.all_eq_true.mp row2_plainLit _ hb
  intro i hi
  have hi' := List.all_eq_true.mp h i hi
  cases i with
  | literal p => exact ⟨p, rfl⟩
  | lookup c ps => simp [isLit] at hi'

theorem row2_geoP (B : Bank) (hbits : ∀ w ∈ B.bits, w ∈ windowBits) (hbn : B.bits.Nodup)
    (hpaths : B.paths = pathBank) : ∀ b ∈ row2, BlockGeoP B b := by
  intro b hb
  have old := WEXUnlookup.row2_geometry b hb
  cases b with
  | plain code => exact plain_geoP B hbits code old.1 (row2_plain_lit code hb)
  | masked site =>
    have avoid : Avoids site.code := by
      rcases row2_masked_cases site hb with rfl | rfl | rfl | rfl | rfl
      · exact avoids_of_all _ scrIn_avoid
      · exact pair_avoid _ _
      · exact triple_avoid
      · exact pair_avoid _ _
      · exact scrD_avoids
    exact site_geoP B hbits hbn hpaths site old avoid.1 avoid.2

theorem row2_geo15 : ∀ b ∈ row2, BlockGeoP bank15 b :=
  row2_geoP bank15 (fun _ h => h) (by decide +kernel) rfl

theorem row2_geo14 : ∀ b ∈ row2, BlockGeoP bank14 b :=
  row2_geoP bank14 (by decide +kernel) (by decide +kernel) rfl


end
end ShorECDLP.Entrant.PathShare

/-! ### Supports and the compact labels without the old path bank -/

namespace ShorECDLP.Entrant.PathShare
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 40000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-- The body's source labels without the fifteen retired path wires. -/
def retired (w : Nat) : Prop := 10000 ≤ w ∧ w < 10015
instance : DecidablePred retired := fun w => inferInstanceAs (Decidable (10000 ≤ w ∧ w < 10015))

def newSource : List Wire := sourceSupport.filter (fun w => decide (¬retired w))

theorem newSource_mem (w : Nat) :
    w ∈ newSource ↔ (fixedPort w ∨ oldWork w) ∧ ¬retired w := by
  rw [newSource, List.mem_filter, sourceSupport_mem, decide_eq_true_eq]

theorem newSource_of_bounds (xs : List Wire)
    (h : ∀ w ∈ xs, (fixedPort w ∨ oldWork w) ∧ ¬retired w) : xs ⊆ newSource :=
  fun w hw => (newSource_mem w).mpr (h w hw)

theorem newSource_of_old (w : Nat) (h1 : w ∈ sourceSupport) (h2 : w ∉ windowPaths) : w ∈ newSource := by
  rw [newSource_mem]
  refine ⟨(sourceSupport_mem w).mp h1, fun h => h2 ?_⟩
  unfold retired at h
  simp only [windowPaths, List.mem_range'_1]
  omega

/-- Swap the retired path labels with the sources of the top fifteen compact labels. -/
def tauWire (w : Nat) : Nat :=
  if 10000 ≤ w ∧ w < 10012 then w + 5644
  else if 10012 ≤ w ∧ w < 10015 then w + 9802
  else if 15644 ≤ w ∧ w < 15656 then w - 5644
  else if 19814 ≤ w ∧ w < 19817 then w - 9802
  else w

theorem tauWire_involutive : Function.Involutive tauWire := by
  intro w
  unfold tauWire
  split_ifs <;> omega

def tau : Wire ≃ Wire := ⟨tauWire, tauWire, tauWire_involutive, tauWire_involutive⟩

/-- Compact labels: the old compaction after the swap. -/
def pi : Wire ≃ Wire := tau.trans compactPerm

theorem pi_apply (w : Wire) : pi w = compactWire (tauWire w) := rfl

theorem pi_fixed (w : Wire) (h : fixedPort w) : pi w = w := by
  have ht : tauWire w = w := by unfold tauWire fixedPort at *; split_ifs <;> omega
  rw [pi_apply, ht]
  exact compactPerm_fixed w h

theorem pi_hot (i : Fin 128) : pi (hot i) = hot i := by
  have hi := i.isLt
  have ht : tauWire (hot i) = hot i := by unfold tauWire hot; split_ifs <;> omega
  rw [pi_apply, ht]
  exact compactPerm_hot i

theorem pi_bound (w : Nat) (hw : w ∈ newSource) : compactWire (tauWire w) < 1619 := by
  obtain ⟨h1, h2⟩ := (newSource_mem w).mp hw
  unfold retired at h2
  by_cases hA : 15644 ≤ w ∧ w < 15656
  · have ht : tauWire w = w - 5644 := by unfold tauWire; split_ifs <;> omega
    have ho : oldWork (w - 5644) := by unfold oldWork; omega
    rw [ht, compactWire, if_pos ho]
    unfold freeAt oldRank
    split_ifs <;> omega
  by_cases hB : 19814 ≤ w ∧ w < 19817
  · have ht : tauWire w = w - 9802 := by unfold tauWire; split_ifs <;> omega
    have ho : oldWork (w - 9802) := by unfold oldWork; omega
    rw [ht, compactWire, if_pos ho]
    unfold freeAt oldRank
    split_ifs <;> omega
  have ht : tauWire w = w := by unfold tauWire; split_ifs <;> omega
  rw [ht]
  rcases h1 with hf | ho
  · have he : compactWire w = w := compactPerm_fixed w hf
    rw [he]
    unfold fixedPort at hf
    omega
  · rw [compactWire, if_pos ho]
    unfold oldWork at ho
    unfold freeAt oldRank
    split_ifs <;> omega

theorem pi_point (w : Wire) (h : w ∈ pointLogicalWires) : pi w = w := by
  apply pi_fixed
  simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1] at h
  unfold fixedPort; dsimp only [Wire] at *; omega

theorem pi_address (w : Wire) (h : w ∈ streamAddress) : pi w = w := by
  apply pi_fixed
  exact Or.inr (Or.inr (Or.inr (by simpa [streamAddress] using h)))

def pull2 (s : BasisState) : BasisState := relabelBasis pi.symm s

theorem pull2_at (s : BasisState) (w : Wire) (h : fixedPort w) : pull2 s w = s w := by
  simp only [pull2,relabelBasis,Equiv.symm_symm,pi_fixed w h]

theorem pull2_hot (s : BasisState) (i : Fin 128) : pull2 s (hot i) = s (hot i) := by
  simp only [pull2,relabelBasis,Equiv.symm_symm,pi_hot]

theorem pull2_write (P : ShorECDLP.Secp256k1.Point) (s : BasisState) :
    pull2 (pointWrite P s) = pointWrite P (pull2 s) := by
  funext w
  by_cases hw : w ∈ pointLogicalWires
  · have he := pi_point w hw
    simp only [pull2,relabelBasis,Equiv.symm_symm,pointWrite,he,if_pos hw]
  · have hn : pi w ∉ pointLogicalWires := by
      intro hh
      have he := pi_point _ hh
      have : pi w = w := pi.injective he
      exact hw (this ▸ hh)
    simp only [pull2,relabelBasis,Equiv.symm_symm,pointWrite,if_neg hw,if_neg hn]

theorem push2_write (P : ShorECDLP.Secp256k1.Point) (s : BasisState) :
    relabelBasis pi (pointWrite P (pull2 s)) = pointWrite P s := by
  have h := congrArg (relabelBasis pi) (pull2_write P s)
  have hi (t : BasisState) : relabelBasis pi (pull2 t) = t := by
    simpa only [pull2,Equiv.symm_symm] using relabelBasis_symm pi.symm t
  rw [hi] at h
  exact h.symm

theorem pull2_coordinates (s : BasisState) :
    pointStateCoordinates (pull2 s) = pointStateCoordinates s := by
  have he (ws : List Wire) (hw : ∀ w ∈ ws, fixedPort w) :
      wireValues ws (pull2 s) = wireValues ws s := by
    apply List.map_congr_left
    intro w hm; exact pull2_at s w (hw w hm)
  have hx := he (List.range' 263 256) (by
    intro w hw; exact Or.inl (List.mem_range'_1.mp hw))
  have hy := he (List.range' 580 256) (by
    intro w hw
    have hw := List.mem_range'_1.mp hw
    apply Or.inr; apply Or.inl; dsimp only [Wire] at *; omega)
  simp only [pointStateCoordinates,hx,hy,pull2_at s 838 (by decide +kernel)]

theorem pull2_digit (s : BasisState) : windowRawDigit 0 (pull2 s) = windowRawDigit 0 s := by
  have he : wireValues (List.range' 855 15) (pull2 s) = wireValues (List.range' 855 15) s := by
    apply List.map_congr_left
    intro w hw
    apply pull2_at
    have hw := List.mem_range'_1.mp hw
    apply Or.inr; apply Or.inr; apply Or.inr; dsimp only [Wire] at *; omega
  simp only [windowRawDigit,windowAddressBits,windowBankStart,Nat.mul_zero,Nat.add_zero,he,
    pull2_at s 870 (by decide +kernel)]

def ready2 (s : BasisState) : Prop := windowReady (pull2 s) ∧ MeasuredClear.HotClean hot s

theorem ready2_active (s : BasisState) (h : ready2 s) : s 836 = true := by
  simpa only [pull2_at s 836 (by decide +kernel)] using windowReady_active (pull2 s) h.1

theorem ready2_write (P : ShorECDLP.Secp256k1.Point) (s : BasisState) (h : ready2 s) :
    ready2 (pointWrite P s) := by
  refine ⟨?_, pointWrite_hot P s h.2⟩
  rw [pull2_write]
  exact windowReady_write P (pull2 s) h.1

theorem pull2_address (s : BasisState) (v : Wire) (hv : v ∈ streamAddress) (b : Bool) :
    pull2 (s[v ↦ b]) = (pull2 s)[v ↦ b] := by
  have hh' : pi.symm v = v := by
    rw [Equiv.symm_apply_eq]; exact (pi_address v hv).symm
  simp only [pull2,relabelBasis_upd,hh']

theorem ready2_address (s : BasisState) (h : ready2 s)
    (v : Wire) (hv : v ∈ streamAddress) (b : Bool) : ready2 (s[v ↦ b]) := by
  refine ⟨?_, ?_⟩
  · rw [pull2_address s v hv b]
    exact windowReady_address (pull2 s) h.1 v hv b
  · intro i
    have hn : hot i ≠ v := fun he => hot_outside_address i (he.symm ▸ hv)
    exact (upd_other s v b hn).trans (h.2 i)

theorem pull2_first (s : BasisState) (h : FirstWindowInput s) : FirstWindowInput (pull2 s) := by
  constructor
  · simpa only [pull2_at s 836 (by decide +kernel)] using h.1
  · intro w hw ha
    change s (pi w) = false
    apply h.2
    · intro hh
      have hfix : pi 836 = 836 := pi_fixed _ (by decide +kernel)
      exact hw (pi.injective (hh.trans hfix.symm))
    · intro hh
      have hfix := pi_address _ hh
      have he : pi w = w := pi.injective hfix
      exact ha (he ▸ hh)

theorem ready2_first (s : BasisState) (h : FirstWindowInput s) (P : ShorECDLP.Secp256k1.Point) :
    ready2 (pointWrite P s) := by
  refine ⟨?_, ?_⟩
  · rw [pull2_write]
    exact windowReady_first (pull2 s) (pull2_first s h) P
  · apply pointWrite_hot P s
    intro i
    apply h.2
    · have hi := i.isLt
      simp only [hot]
      dsimp only [Wire] at *
      omega
    · exact hot_outside_address i

def state2 (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point) (s : BasisState) : BasisState :=
  relabelBasis pi (bodyState coeffs Q (pull2 s))

theorem state2_correct (coeffs : Fin 32768 → PointCoeff) (Q : ShorECDLP.Secp256k1.Point)
    (s : BasisState) (hs : ready2 s) (P : ShorECDLP.Secp256k1.Point)
    (hP : pointStateCoordinates s = fig14PointEncoding P) :
    state2 coeffs Q s = pointWrite
      (P + if s 836 then
        (if s 870 then constantPoint Q (coeffs ⟨signedTableAddress 32768
          (windowRawDigit 0 s),signedTableAddress_bound 32768 _ (windowRawDigit_bound 0 s)⟩)
         else -constantPoint Q (coeffs ⟨signedTableAddress 32768
          (windowRawDigit 0 s),signedTableAddress_bound 32768 _ (windowRawDigit_bound 0 s)⟩))
        else 0) s := by
  unfold state2
  rw [bodyState_correct coeffs Q (pull2 s) hs.1 P ((pull2_coordinates s).trans hP),push2_write]
  simp only [pull2_at s 836 (by decide +kernel),pull2_at s 870 (by decide +kernel),pull2_digit]

/-- Transport a coherent source body to the new compact labels. -/
theorem relabel2_coherent {s e : Nat} (p : Straight 32768 s e) (coeffs : Fin 32768 → PointCoeff)
    (Q : ShorECDLP.Secp256k1.Point) (history : Fin s → Bool)
    (hc : CoherentlyImplementsOn (p.instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)) Ready) :
    CoherentlyImplementsOn ((relabelStraight pi p).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (state2 coeffs Q))
      (fun s => ready2 s ∧ ∃ P, pointStateCoordinates s = fig14PointEncoding P) := by
  have h := hc.relabel pi
  have hr : CoherentlyImplementsOn
      ((p.instantiate (readConstant coeffs Q) history).relabel pi)
      ((relabelState pi).comp ((Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)).comp
        (relabelState pi.symm)))
      (fun s => ready2 s ∧ ∃ P, pointStateCoordinates s = fig14PointEncoding P) := by
    obtain ⟨cs,aligned,mass⟩ := h
    refine ⟨cs,aligned.imp ?_,mass⟩
    intro b c hb s hs
    apply hb s
    refine ⟨hs.1.1,?_⟩
    intro i
    exact (pull2_hot s i).trans (hs.1.2 i)
  have he := hr.congrIdeal (secondIdeal := Finsupp.lmapDomain ℂ ℂ (state2 coeffs Q))
    (by intro s _; simp [state2,pull2,LinearMap.comp_apply,relabelState,ket])
  rw [relabelStraight_instantiate]
  exact he

theorem relabel2_support {s e : Nat} (p : Straight 32768 s e)
    (h : ChallengeMigration.straightWires p ⊆ newSource) :
    ChallengeMigration.straightWires (relabelStraight pi p) ⊆ List.range 1619 := by
  rw [straightWires_relabel]
  intro w hw
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
  exact List.mem_range.mpr ((pi_apply v).trans_lt (pi_bound v (h hv)))

theorem base_support2 : completeBatchedSupport ⊆ List.range 1619 := by
  intro w hw
  simp only [completeBatchedSupport,resetWires,List.mem_cons,List.mem_append,
    List.mem_range,List.mem_range'_1,List.not_mem_nil,or_false] at hw
  apply List.mem_range.mpr
  dsimp only [Wire] at *; omega

end
end ShorECDLP.Entrant.PathShare

/-! ### The width-15 body on the pool bank -/

namespace ShorECDLP.Entrant.PathShare.W15
open Quantum Challenge AndGadget WEXCredit Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
open ShorECDLP.Entrant.Schedule33.Flexible ShorECDLP.Entrant.PathShare
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

theorem lay15 : ∀ b ∈ row2, BlockLay bank15 b := fun b hb => geo_lay bank15 bank15_ok b (row2_geo15 b hb)

theorem old15_lay : ∀ b ∈ row2, BlockLay old15 b := by
  intro b hb
  have hg := WEXUnlookup.row2_geometry b hb
  cases b with
  | plain code =>
    exact pair_layouts_of_placed _ _ _ _ (by simp [old15,windowBits,windowPaths]) (pair_placed_normalize _ _ _ _ hg.1)
  | masked site =>
    have hp : ∀ i ∈ site.prefix, PlacedPair windowBits windowPaths windowRoot i := fun i hi =>
      placed_implies_pair _ _ _ _ (hg.placed i (List.mem_append_left _ hi))
    exact ⟨pair_layouts_of_placed _ _ _ _ (by simp [old15,windowBits,windowPaths]) (pair_placed_normalize _ _ _ _ hp),
      WEXUnlookup.site_high_layout site hg⟩

theorem recordsP_old15 (code : Code 32768) : recordsP old15 code = WEXUnlookup.records code := by
  induction code with
  | nil => rfl
  | cons b code ih =>
    simp only [recordsP, WEXUnlookup.records, ih]
    cases b <;> rfl

theorem row2_recordsP : recordsP bank15 row2 = 1757978 := by
  rw [recordsP_eq bank15 old15 rfl rfl row2 lay15 old15_lay, recordsP_old15]
  exact WEXUnlookup.row2_records

theorem codeTP15 (code : Code 32768) : codeTP bank15 code = WEXUnlookup.ccx code := by
  induction code with
  | nil => rfl
  | cons b code ih =>
    have hl : 2 ^ bank15.bits.length - 1 = 32767 := by simp [bank15, windowBits]
    have hn : (tableAddressTree bank15.high 0 1).internalNodes = 255 := WEXUnlookup.high_nodes
    simp only [codeTP, WEXUnlookup.ccx, ih]
    cases b <;> simp only [blockTP, WEXUnlookup.blockCCX, hl, hn]

theorem program_slots_old15 (code : Code 32768) (hl : ∀ b ∈ code, BlockLay old15 b) (start : Nat) :
    (WEXUnlookup.program code start).gateSlots = codeSP old15 code := by
  induction code generalizing start with
  | nil => rfl
  | cons b code ih =>
    have hb : (WEXUnlookup.blockProgram b start).gateSlots = (blockProgP old15 b start).gateSlots := by
      cases b <;> rfl
    rw [WEXUnlookup.program, castFinish_gateSlots, Straight.gateSlots_append, ih (fun d hd => hl d (by simp [hd])),
      hb, blockProgP_slots old15 b (hl b (by simp))]
    rfl

attribute [local irreducible] programP blockProgP clearP WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  WEX.literalToffolis WEX.normalizeW ccx Nat.add Nat.mul

def addFixedP (start : Nat) : Straight 32768 start (start+1757978) :=
  castFinish (congrArg (fun m => start+m) row2_recordsP) (programP bank15 row2 start)

theorem addFixedP_run (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((addFixedP start).instantiate read history).run = (sourceCodeP bank15 read row2).run := by
  rw [addFixedP,castFinish_instantiate,programP_run]

theorem addFixedP_tCount (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((addFixedP start).instantiate read history).tCount = 7*ccx row2 := by
  rw [addFixedP,castFinish_instantiate,programP_tCount read bank15 row2 lay15,codeTP15]

theorem addFixedP_slots (start : Nat) : (addFixedP start).gateSlots =
    codeSlots windowBits (normalizeW (erase row2)) + 250725868 := by
  rw [addFixedP,castFinish_gateSlots,programP_slots bank15 row2 lay15,codeSP_congr bank15 old15 rfl rfl,
    ← program_slots_old15 row2 old15_lay start]
  exact WEXUnlookup.row2_slots start

theorem addFixedP_wellFormed (start : Nat) : (addFixedP start).WellFormed := by
  rw [addFixedP,castFinish_wellFormed]
  exact programP_wellFormed bank15 bank15_ok row2 row2_geo15 row2_physical start

theorem addFixedP_residue (start : Nat) : residue (addFixedP start) = 0 := by
  rw [addFixedP,residue_cast]
  exact programP_residue bank15 row2 start

theorem addFixedP_credit (start : Nat) : ProgramCredit (addFixedP start) (ccx row2) := by
  have hz := addFixedP_residue start
  refine ⟨hz,?_⟩
  have he := exact_t (addFixedP start) hz (fun _ => false) (fun _ => false)
  have ht := addFixedP_tCount (fun _ => false) start (fun _ => false)
  omega

theorem row2_placed_old : ∀ i ∈ erase row2, PlacedPair windowBits windowPaths windowRoot i := by
  intro i hi
  obtain ⟨b, hb, hib⟩ := List.mem_flatMap.mp hi
  exact (block_placed b (WEXUnlookup.row2_geometry b hb)).1 i hib

theorem wires_new_of {p : ECDSAAdd.Program} {l : List Wire} (hs : ECDSAAdd.wires p ⊆ l.toFinset)
    (h : ∀ w ∈ l, w ∈ ECDSAAdd.wires p → w ∈ newSource) : ECDSAAdd.wires p ⊆ newSource.toFinset :=
  fun w hw => List.mem_toFinset.mpr (h w (List.mem_toFinset.mp (hs hw)) hw)

theorem row2_lit_new (p : ECDSAAdd.Program) (hp : WInstr.literal p ∈ erase row2) :
    ECDSAAdd.wires p ⊆ newSource.toFinset :=
  wires_new_of (row2_oldWithin.1 p hp) (fun w h1 hw => newSource_of_old w h1
    (fun hm => row2_placed_old _ hp w (by simp [hm]) hw))


theorem row2_look_new (c : Option Wire) (ps : List (LookupPort 32768)) (hp : WInstr.lookup c ps ∈ erase row2) :
    (∀ q ∈ c, q ∈ newSource) ∧ portTargets ps ⊆ newSource := by
  have h1 := row2_oldWithin.2 c ps hp
  have h2 := row2_placed_old _ hp
  dsimp only [PlacedPair] at h2
  refine ⟨fun q hq => newSource_of_old q (h1.1 q hq) fun hm => ?_, fun w hw => newSource_of_old w (h1.2 hw) fun hm => ?_⟩
  · have hq' : lookupRoot windowRoot c = q := by
      cases c with
      | none => simp at hq
      | some q' => simp only [Option.mem_def, Option.some.injEq] at hq; simp [lookupRoot, hq]
    have h0 := h2.1
    rw [List.cons_append] at h0
    have hn := (List.nodup_cons.mp h0).1
    exact hn (by rw [hq']; exact List.mem_append_right _ hm)
  · exact List.disjoint_left.mp h2.2.2.2 (by simp [hm]) hw

theorem addFixedP_support (start : Nat) : ChallengeMigration.straightWires (addFixedP start) ⊆ newSource := by
  rw [addFixedP,support_cast]
  apply programP_support bank15 bank15_ok row2 row2_geo15 newSource
  · exact newSource_of_bounds [windowRoot] (by decide +kernel) (List.mem_singleton_self _)
  · exact newSource_of_bounds _ (by simp only [bank15, windowBits]; decide +kernel)
  · exact newSource_of_bounds _ (by simp only [bank15, pathBank]; decide +kernel)
  · intro i
    exact newSource_of_bounds [low i] (by
      have hi := i.isLt
      intro w hw
      simp only [List.mem_singleton] at hw
      subst hw
      simp only [low, fixedPort, oldWork, retired]
      omega) (List.mem_singleton_self _)
  · exact newSource_of_bounds _ (by simp only [bank15, WEXUnlookup.high]; decide +kernel)
  · exact row2_lit_new
  · exact row2_look_new

def rowSourceP (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  sourceCodeP bank15 (readConstant coeffs Q) row2

theorem rowSourceP_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) :
    CoherentlyImplementsOn (rowSourceP coeffs Q) (Finsupp.lmapDomain ℂ ℂ (rowPointState coeffs Q)) LiveReady := by
  have h := program_coherentP (readConstant coeffs Q) bank15 bank15_ok row2 row2_geo15 liveReady
    (rowPointState coeffs Q)
    (fun s hs => (row2_safe_run coeffs Q hQ hn _ s hs).1)
    (fun s hs => row2_clean pathBank pathBank_pool pathBank_flip pathBank_head coeffs Q hQ hn _ s hs)
    (fun s hs m => row2_run_any _ coeffs Q hQ hn s hs m) 0 Fin.elim0
  obtain ⟨cs,aligned,mass⟩ := h
  refine ⟨cs,?_,mass⟩
  rw [programP_run] at aligned
  exact aligned.imp (fun b c hb s hs => hb s ⟨hs.1.2.2, hs.1⟩)

def fastMiddleSource (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  (fastSignSource.seq (rowSourceP coeffs Q)).seq fastSignSource

theorem fastMiddle_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) :
    CoherentlyImplementsOn (fastMiddleSource coeffs Q) (Finsupp.lmapDomain ℂ ℂ (middleState coeffs Q)) LiveReady := by
  have first := composeCoherent fastSign_coherent (rowSourceP_coherent coeffs Q hQ hn)
    (fun s hs => live_write _ s hs)
  exact composeCoherent (f := fun s => rowPointState coeffs Q (signPointState s)) (g := signPointState)
    first fastSign_coherent (fun s hs => live_write _ _ (live_write _ s hs))

def fastBodySource (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  (prefixSource.seq (fastMiddleSource coeffs Q)).seq suffixSource

theorem fastBodySource_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0) :
    CoherentlyImplementsOn (fastBodySource coeffs Q) (Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)) Ready := by
  have h := composeCoherent WEXUnlookup.prefix_coherent (fastMiddle_coherent coeffs Q hQ hn)
    (fun s hs => ⟨windowPrepare_live _ (rootFlip_live s hs.1),prefix_hot s hs.2⟩)
  exact composeCoherent (f := fun s => middleState coeffs Q (prefixState s)) (g := suffixState)
    h WEX.suffix_coherent (fun _ _ => True.intro)

def fastBodyProgram (start : Nat) : Straight 32768 start (start+1758490) :=
  castFinish (by omega)
    (((((prefixProgram start).append (nFastProgram start)).append (addFixedP (start+256))).append
      (nFastProgram (start+256+1757978))).append (suffixProgram (start+256+1757978+256)))

attribute [local irreducible] fastBodyProgram addFixedP

theorem fastBodyProgram_run (start : Nat) (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (history : Fin start → Bool) :
    ((fastBodyProgram start).instantiate (readConstant coeffs Q) history).run = (fastBodySource coeffs Q).run := by
  have hr : ((fastBodyProgram start).instantiate (readConstant coeffs Q) history).run =
      ((prefixSource.seq ((fastSignSource.seq (sourceCodeP bank15 (readConstant coeffs Q) row2)).seq
        fastSignSource)).seq suffixSource).run := by
    rw [fastBodyProgram,castFinish_instantiate]
    exact five_run (readConstant coeffs Q) _ _ _ _ _ prefixSource fastSignSource
      (sourceCodeP bank15 (readConstant coeffs Q) row2) fastSignSource suffixSource
      (prefixProgram_run _ _) (nFastProgram_run _ _) (addFixedP_run _ _)
      (nFastProgram_run _ _) (suffixProgram_run _ _) history
  have he : fastBodySource coeffs Q =
      ((prefixSource.seq ((fastSignSource.seq (sourceCodeP bank15 (readConstant coeffs Q) row2)).seq
        fastSignSource)).seq suffixSource) := by
    delta fastBodySource fastMiddleSource rowSourceP
    rfl
  exact hr.trans (congrArg AdaptiveCircuit.run he.symm)

theorem fastBodyProgram_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((fastBodyProgram start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)) Ready := by
  obtain ⟨cs,aligned,mass⟩ := fastBodySource_coherent coeffs Q hQ hn
  refine ⟨cs,?_,mass⟩
  rw [fastBodyProgram_run]
  exact aligned

theorem fastBodyProgram_credit (start : Nat) : ProgramCredit (fastBodyProgram start)
    (2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) + ccx row2) := by
  let a := ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)
  have hl : ProgramCredit (nFastProgram start) a := WEX.nFastProgram_credit start
  have hr : ProgramCredit (nFastProgram (start+256+1757978)) a := WEX.nFastProgram_credit _
  rw [fastBodyProgram]
  apply credit_cast
  exact five_credit a (ccx row2) (prefix_credit start) hl (addFixedP_credit (start+256)) hr
    (suffix_credit (start+256+1757978+256))

theorem fastBodyProgram_tCount (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((fastBodyProgram start).instantiate read history).tCount =
      7*(2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) + ccx row2) := by
  have hc := fastBodyProgram_credit start
  have h := exact_t (fastBodyProgram start) hc.1 read history
  rw [hc.2] at h
  exact h

theorem fastBodyProgram_wellFormed (start : Nat) : (fastBodyProgram start).WellFormed := by
  rw [fastBodyProgram,castFinish_wellFormed]
  apply straight_append_wellFormed
  · apply straight_append_wellFormed
    · apply straight_append_wellFormed
      · exact straight_append_wellFormed _ _ (prefixProgram_wellFormed start) (nFastProgram_wellFormed start)
      · exact addFixedP_wellFormed _
    · exact nFastProgram_wellFormed _
  · exact suffixProgram_wellFormed _

theorem nFast_new (start : Nat) : ChallengeMigration.straightWires (nFastProgram start) ⊆ newSource := by
  apply literalFixed_support (n := 32768) (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram) 256
    ((literal_meas (n := 32768) _).trans fastWindowSign_normalized_counts.2) newSource (start := start)
  rw [ECDSAAdd.Baselines.normalize_wires]
  have hs := WEX.finiteSignMeasured_support (negateYLayout streamLayout) 870 838 streamLayout.core.generic ECDSAAdd.p
  have cover : 870 :: 838 :: (negateYLayout streamLayout).wires streamLayout.core.generic ⊆ newSource := by
    apply newSource_of_bounds; decide +kernel
  have sub : ECDSAAdd.wires fastWindowSignProgram ⊆ ECDSAAdd.wires
      (WEX.finiteSignMeasured (negateYLayout streamLayout) 870 838 streamLayout.core.generic ECDSAAdd.p) := by
    simp only [fastWindowSignProgram, WEX.finiteSignMeasured, ECDSAAdd.wires_append]
    exact Finset.union_subset_union (Finset.union_subset_union (fun _ h => h) WEX.TrimmedSign.reflection_wires)
      (fun _ h => h)
  exact sub.trans (hs.trans (fun w hw => List.mem_toFinset.mpr (cover (List.mem_toFinset.mp hw))))

theorem fastBodyProgram_support (start : Nat) :
    ChallengeMigration.straightWires (fastBodyProgram start) ⊆ newSource := by
  have hp : ChallengeMigration.straightWires (prefixProgram start) ⊆ newSource := by
    rw [prefixProgram,straightWires_append,literalProgram_support,literalProgram_support]
    apply newSource_of_bounds
    decide +kernel
  have hs (j : Nat) : ChallengeMigration.straightWires (suffixProgram j) ⊆ newSource := by
    rw [suffixProgram,straightWires_append,literalProgram_support,literalProgram_support]
    apply newSource_of_bounds
    decide +kernel
  rw [fastBodyProgram,support_cast]
  simp only [straightWires_append,List.append_subset]
  exact ⟨⟨⟨⟨hp,nFast_new _⟩,addFixedP_support _⟩,nFast_new _⟩,hs _⟩

attribute [local irreducible] WEX.literalSlotSum WEX.portTotal WEX.traversals in
theorem fastBodyProgram_slots_upper (start : Nat) : (fastBodyProgram start).gateSlots ≤ 2000000000 := by
  rw [fastBodyProgram,castFinish_gateSlots]
  simp only [Straight.gateSlots_append,nFastProgram_slots,addFixedP_slots,
    prefixProgram,suffixProgram,literalProgram_slots]
  have len : (signedAddressCircuit 836 870 windowBits).length = 30 := by decide +kernel
  simp only [len,List.length_cons,List.length_nil]
  have hc := WEX.codeSlots_bound windowBits (normalizeW (erase row2))
  rw [literalSlotSum_normalize,portTotal_normalize,traversals_normalize] at hc
  have hl := WEX.clearReferenceRow_literal_slots_bound
  have hp := WEX.clearReferenceRow_portTotal
  have hm := WEXUnlookup.row2_measures
  have hl2 := hm.2.2.1
  rw [← hm.2.2.2.1] at hp
  rw [hm.2.1] at hc
  have sign := literal_slot_bound (n := 32768) (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)
  rw [ECDSAAdd.Baselines.normalize_slots] at sign
  have bound := fastWindowSign_slots
  norm_num [windowBits] at hc
  simp only [windowBits]
  omega

def compactProgram (start : Nat) : Straight 32768 start (start+1758490) :=
  relabelStraight pi (fastBodyProgram start)

end
end ShorECDLP.Entrant.PathShare.W15

/-! ### The width-14 body on the pool bank -/

namespace ShorECDLP.Entrant.PathShare.W14
open Quantum Challenge AndGadget WEXCredit Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
open ShorECDLP.Entrant.Schedule33.Flexible ShorECDLP.Entrant.PathShare
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

theorem lay14 : ∀ b ∈ row2, BlockLay bank14 b := fun b hb => geo_lay bank14 bank14_ok b (row2_geo14 b hb)

theorem old14_lay : ∀ b ∈ row2, BlockLay old14 b := by
  intro b hb
  have hg := WEXUnlookupWidth14.row2_geometry b hb
  cases b with
  | plain code =>
    exact pair_layouts_of_placed _ _ _ _ (by simp [old14,WEXUnlookupWidth14.bits,WEX.widthBits,windowPaths])
      (pair_placed_normalize _ _ _ _ hg.1)
  | masked site =>
    have hp : ∀ i ∈ site.prefix, PlacedPair WEXUnlookupWidth14.bits windowPaths windowRoot i := fun i hi =>
      placed_implies_pair _ _ _ _ (hg.placed i (List.mem_append_left _ hi))
    exact ⟨pair_layouts_of_placed _ _ _ _ (by simp [old14,WEXUnlookupWidth14.bits,WEX.widthBits,windowPaths])
      (pair_placed_normalize _ _ _ _ hp), WEXUnlookupWidth14.site_high_layout site hg.original⟩

theorem recordsP_old14 (code : Code 32768) : recordsP old14 code = WEXUnlookupWidth14.records code := by
  induction code with
  | nil => rfl
  | cons b code ih =>
    simp only [recordsP, WEXUnlookupWidth14.records, ih]
    cases b <;> rfl

theorem row2_recordsP : recordsP bank14 row2 = 1659034 := by
  rw [recordsP_eq bank14 old14 rfl rfl row2 lay14 old14_lay, recordsP_old14]
  exact WEXUnlookupWidth14.row2_records

theorem codeTP14 (code : Code 32768) : codeTP bank14 code = WEXUnlookupWidth14.ccx code := by
  induction code with
  | nil => rfl
  | cons b code ih =>
    have hl : 2 ^ bank14.bits.length - 1 = 16383 := by simp [bank14, WEXUnlookupWidth14.bits, WEX.widthBits]
    have hn : (tableAddressTree bank14.high 0 1).internalNodes = 127 := WEXUnlookupWidth14.high_nodes
    simp only [codeTP, WEXUnlookupWidth14.ccx, ih]
    cases b <;> simp only [blockTP, WEXUnlookupWidth14.blockCCX, hl, hn]

theorem program_slots_old14 (code : Code 32768) (hl : ∀ b ∈ code, BlockLay old14 b) (start : Nat) :
    (WEXUnlookupWidth14.program code start).gateSlots = codeSP old14 code := by
  induction code generalizing start with
  | nil => rfl
  | cons b code ih =>
    have hb : (WEXUnlookupWidth14.blockProgram b start).gateSlots = (blockProgP old14 b start).gateSlots := by
      cases b <;> rfl
    rw [WEXUnlookupWidth14.program, castFinish_gateSlots, Straight.gateSlots_append,
      ih (fun d hd => hl d (by simp [hd])), hb, blockProgP_slots old14 b (hl b (by simp))]
    rfl

attribute [local irreducible] programP blockProgP clearP WEX.compile Bridge.translate
  ECDSAAdd.Baselines.normalizeProgram ECDSAAdd.toffoliCount ECDSAAdd.measurementCount WEX.codeRecords
  WEX.literalToffolis WEX.normalizeW WEXUnlookupWidth14.ccx Nat.add Nat.mul

def addFixedP (start : Nat) : Straight 32768 start (start+1659034) :=
  castFinish (congrArg (fun m => start+m) row2_recordsP) (programP bank14 row2 start)

theorem addFixedP_run (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((addFixedP start).instantiate read history).run = (sourceCodeP bank14 read row2).run := by
  rw [addFixedP,castFinish_instantiate,programP_run]

theorem addFixedP_tCount (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((addFixedP start).instantiate read history).tCount = 7*WEXUnlookupWidth14.ccx row2 := by
  rw [addFixedP,castFinish_instantiate,programP_tCount read bank14 row2 lay14,codeTP14]

theorem addFixedP_slots_upper (start : Nat) : (addFixedP start).gateSlots ≤ 1000000000 := by
  rw [addFixedP,castFinish_gateSlots,programP_slots bank14 row2 lay14,codeSP_congr bank14 old14 rfl rfl,
    ← program_slots_old14 row2 old14_lay start]
  exact WEXUnlookupWidth14.row2_slots_upper start

theorem addFixedP_wellFormed (start : Nat) : (addFixedP start).WellFormed := by
  rw [addFixedP,castFinish_wellFormed]
  exact programP_wellFormed bank14 bank14_ok row2 row2_geo14 row2_physical start

theorem addFixedP_residue (start : Nat) : residue (addFixedP start) = 0 := by
  rw [addFixedP,residue_cast]
  exact programP_residue bank14 row2 start

theorem addFixedP_credit (start : Nat) : ProgramCredit (addFixedP start) (WEXUnlookupWidth14.ccx row2) := by
  have hz := addFixedP_residue start
  refine ⟨hz,?_⟩
  have he := exact_t (addFixedP start) hz (fun _ => false) (fun _ => false)
  have ht := addFixedP_tCount (fun _ => false) start (fun _ => false)
  omega

theorem addFixedP_support (start : Nat) : ChallengeMigration.straightWires (addFixedP start) ⊆ newSource := by
  rw [addFixedP,support_cast]
  apply programP_support bank14 bank14_ok row2 row2_geo14 newSource
  · exact newSource_of_bounds [windowRoot] (by decide +kernel) (List.mem_singleton_self _)
  · exact newSource_of_bounds _ (by simp only [bank14, WEXUnlookupWidth14.bits, WEX.widthBits]; decide +kernel)
  · exact newSource_of_bounds _ (by simp only [bank14, pathBank]; decide +kernel)
  · intro i
    exact newSource_of_bounds [low i] (by
      have hi := i.isLt
      intro w hw
      simp only [List.mem_singleton] at hw
      subst hw
      simp only [low, fixedPort, oldWork, retired]
      omega) (List.mem_singleton_self _)
  · exact newSource_of_bounds _ (by simp only [bank14, WEXUnlookupWidth14.high]; decide +kernel)
  · exact W15.row2_lit_new
  · exact W15.row2_look_new

def rowSourceP (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  sourceCodeP bank14 (readConstant coeffs Q) row2

theorem rowSourceP_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : ShorECDLP.order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (halias : WEX.WidthAliased 14 coeffs) :
    CoherentlyImplementsOn (rowSourceP coeffs Q) (Finsupp.lmapDomain ℂ ℂ (rowPointState coeffs Q)) LiveReady := by
  have h := program_coherentP (readConstant coeffs Q) bank14 bank14_ok row2 row2_geo14 liveReady
    (WEXUnlookupWidth14.rowState coeffs Q)
    (fun s hs => (row2_safe_run coeffs Q hQ hn _ s hs).1)
    (fun s hs => row2_clean pathBank pathBank_pool pathBank_flip pathBank_head coeffs Q hQ hn _ s hs)
    (fun s hs m => by
      simpa only [WEXUnlookupWidth14.rowState] using
        row2_run_any (tableAddressValue WEXUnlookupWidth14.bits s) coeffs Q hQ hn s hs m) 0 Fin.elim0
  have he : WEXUnlookupWidth14.rowState coeffs Q = rowPointState coeffs Q := by
    funext s
    unfold WEXUnlookupWidth14.rowState rowPointState
    rw [show tableAddressValue WEXUnlookupWidth14.bits s = tableAddressValue (WEX.widthBits 14) s from rfl,
      WEX.width_table 14 (by omega) coeffs Q halias s]
  rw [he] at h
  obtain ⟨cs,aligned,mass⟩ := h
  refine ⟨cs,?_,mass⟩
  rw [programP_run] at aligned
  exact aligned.imp (fun b c hb s hs => hb s ⟨hs.1.2.2, hs.1⟩)

def fastMiddleSource (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  (fastSignSource.seq (rowSourceP coeffs Q)).seq fastSignSource

theorem fastMiddle_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (halias : WEX.WidthAliased 14 coeffs) :
    CoherentlyImplementsOn (fastMiddleSource coeffs Q) (Finsupp.lmapDomain ℂ ℂ (middleState coeffs Q)) LiveReady := by
  have first := composeCoherent fastSign_coherent (rowSourceP_coherent coeffs Q hQ hn halias)
    (fun s hs => live_write _ s hs)
  exact composeCoherent (f := fun s => rowPointState coeffs Q (signPointState s)) (g := signPointState)
    first fastSign_coherent (fun s hs => live_write _ _ (live_write _ s hs))

def fastBodySource (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point) : AdaptiveCircuit :=
  (prefixSource.seq (fastMiddleSource coeffs Q)).seq suffixSource

theorem fastBodySource_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (halias : WEX.WidthAliased 14 coeffs) :
    CoherentlyImplementsOn (fastBodySource coeffs Q) (Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)) Ready := by
  have h := composeCoherent WEXUnlookup.prefix_coherent (fastMiddle_coherent coeffs Q hQ hn halias)
    (fun s hs => ⟨windowPrepare_live _ (rootFlip_live s hs.1),prefix_hot s hs.2⟩)
  exact composeCoherent (f := fun s => middleState coeffs Q (prefixState s)) (g := suffixState)
    h WEX.suffix_coherent (fun _ _ => True.intro)

def fastBodyProgram (start : Nat) : Straight 32768 start (start+1659546) :=
  castFinish (by omega)
    (((((prefixProgram start).append (nFastProgram start)).append (addFixedP (start+256))).append
      (nFastProgram (start+256+1659034))).append (suffixProgram (start+256+1659034+256)))

attribute [local irreducible] fastBodyProgram addFixedP

theorem fastBodyProgram_run (start : Nat) (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (history : Fin start → Bool) :
    ((fastBodyProgram start).instantiate (readConstant coeffs Q) history).run = (fastBodySource coeffs Q).run := by
  have hr : ((fastBodyProgram start).instantiate (readConstant coeffs Q) history).run =
      ((prefixSource.seq ((fastSignSource.seq (sourceCodeP bank14 (readConstant coeffs Q) row2)).seq
        fastSignSource)).seq suffixSource).run := by
    rw [fastBodyProgram,castFinish_instantiate]
    exact five_run (readConstant coeffs Q) _ _ _ _ _ prefixSource fastSignSource
      (sourceCodeP bank14 (readConstant coeffs Q) row2) fastSignSource suffixSource
      (prefixProgram_run _ _) (nFastProgram_run _ _) (addFixedP_run _ _)
      (nFastProgram_run _ _) (suffixProgram_run _ _) history
  have he : fastBodySource coeffs Q =
      ((prefixSource.seq ((fastSignSource.seq (sourceCodeP bank14 (readConstant coeffs Q) row2)).seq
        fastSignSource)).seq suffixSource) := by
    delta fastBodySource fastMiddleSource rowSourceP
    rfl
  exact hr.trans (congrArg AdaptiveCircuit.run he.symm)

theorem fastBodyProgram_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Secp256k1.Point)
    (hQ : order • Q = 0) (hn : ∀ a, constantPoint Q (coeffs a) ≠ 0)
    (halias : WEX.WidthAliased 14 coeffs) (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((fastBodyProgram start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (bodyState coeffs Q)) Ready := by
  obtain ⟨cs,aligned,mass⟩ := fastBodySource_coherent coeffs Q hQ hn halias
  refine ⟨cs,?_,mass⟩
  rw [fastBodyProgram_run]
  exact aligned

theorem fastBodyProgram_credit (start : Nat) : ProgramCredit (fastBodyProgram start)
    (2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) +
      WEXUnlookupWidth14.ccx row2) := by
  let a := ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)
  have hl : ProgramCredit (nFastProgram start) a := WEX.nFastProgram_credit start
  have hr : ProgramCredit (nFastProgram (start+256+1659034)) a := WEX.nFastProgram_credit _
  rw [fastBodyProgram]
  apply credit_cast
  exact five_credit a (WEXUnlookupWidth14.ccx row2) (prefix_credit start) hl (addFixedP_credit (start+256)) hr
    (suffix_credit (start+256+1659034+256))

theorem fastBodyProgram_tCount (read : ConstantBit 32768 → Bool) (start : Nat) (history : Fin start → Bool) :
    ((fastBodyProgram start).instantiate read history).tCount =
      7*(2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) +
        WEXUnlookupWidth14.ccx row2) := by
  have hc := fastBodyProgram_credit start
  have h := exact_t (fastBodyProgram start) hc.1 read history
  rw [hc.2] at h
  exact h

theorem fastBodyProgram_wellFormed (start : Nat) : (fastBodyProgram start).WellFormed := by
  rw [fastBodyProgram,castFinish_wellFormed]
  apply straight_append_wellFormed
  · apply straight_append_wellFormed
    · apply straight_append_wellFormed
      · exact straight_append_wellFormed _ _ (prefixProgram_wellFormed start) (nFastProgram_wellFormed start)
      · exact addFixedP_wellFormed _
    · exact nFastProgram_wellFormed _
  · exact suffixProgram_wellFormed _

theorem fastBodyProgram_support (start : Nat) :
    ChallengeMigration.straightWires (fastBodyProgram start) ⊆ newSource := by
  have hp : ChallengeMigration.straightWires (prefixProgram start) ⊆ newSource := by
    rw [prefixProgram,straightWires_append,literalProgram_support,literalProgram_support]
    apply newSource_of_bounds
    decide +kernel
  have hs (j : Nat) : ChallengeMigration.straightWires (suffixProgram j) ⊆ newSource := by
    rw [suffixProgram,straightWires_append,literalProgram_support,literalProgram_support]
    apply newSource_of_bounds
    decide +kernel
  rw [fastBodyProgram,support_cast]
  simp only [straightWires_append,List.append_subset]
  exact ⟨⟨⟨⟨hp,W15.nFast_new _⟩,addFixedP_support _⟩,W15.nFast_new _⟩,hs _⟩

theorem fastBodyProgram_slots_upper (start : Nat) : (fastBodyProgram start).gateSlots ≤ 1100000000 := by
  have hr := addFixedP_slots_upper (start+256)
  rw [fastBodyProgram,castFinish_gateSlots]
  simp only [Straight.gateSlots_append,nFastProgram_slots,
    prefixProgram,suffixProgram,literalProgram_slots]
  have len : (signedAddressCircuit 836 870 windowBits).length = 30 := by decide +kernel
  simp only [len,List.length_cons,List.length_nil]
  have sign := literal_slot_bound (n := 32768) (ECDSAAdd.Baselines.normalizeProgram fastWindowSignProgram)
  rw [ECDSAAdd.Baselines.normalize_slots] at sign
  have bound := fastWindowSign_slots
  omega

def compactProgram (start : Nat) : Straight 32768 start (start+1659546) :=
  relabelStraight pi (fastBodyProgram start)

end
end ShorECDLP.Entrant.PathShare.W14

/-! ### The body with the pool path bank, and its narrow programs -/

namespace ShorECDLP.Entrant.PathShare
open Quantum Challenge Paper2607_13816 Paper2607_13816.ChallengeMigration WEX WEXUnlookup
open ShorECDLP.Entrant.Schedule33.Flexible
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

attribute [local irreducible] W15.fastBodyProgram W14.fastBodyProgram

def body2 : Single.WindowBody where
  records := 1758490
  tBound := 16536856
  slotBound := 2000000000
  support := List.range 1619
  reset := resetWires
  ready := ready2
  active := ready2_active
  ready_write := ready2_write
  ready_address := ready2_address
  ready_first := ready2_first
  program := W15.compactProgram
  update := state2
  correct := fun coeffs Q _ _ s hs P hP => state2_correct coeffs Q s hs P hP
  coherent := fun coeffs Q hQ hn start history =>
    relabel2_coherent _ coeffs Q history (W15.fastBodyProgram_coherent coeffs Q hQ hn start history)
  wellFormed := fun start => (relabelStraight_wellFormed pi (W15.fastBodyProgram start)).mpr
    (W15.fastBodyProgram_wellFormed start)
  slots := fun start => (relabelStraight_slots pi (W15.fastBodyProgram start)).trans_le
    (W15.fastBodyProgram_slots_upper start)
  tCount := by
    intro coeffs Q start history
    rw [W15.compactProgram,relabelStraight_instantiate,AdaptiveCircuit.relabel_tCount,W15.fastBodyProgram_tCount]
    have h := Width15Fused.fastCount_upper
    omega
  wires := fun start => relabel2_support _ (W15.fastBodyProgram_support start)
  reset_support := fun _ hw => base_support2 (List.mem_cons_of_mem 837 hw)
  skeleton_support := base_support2

def narrow15 : ModNarrow body2 15 where
  records := 1758490
  tBound := 16536856
  credit := 2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) + ccx row2
  program := W15.compactProgram
  coherent := fun coeffs Q hQ hn _ start history => body2.coherent coeffs Q hQ hn start history
  wellFormed := body2.wellFormed
  slots := body2.slots
  wires := body2.wires
  tCount := by
    intro start read history
    rw [W15.compactProgram,relabelStraight_instantiate,AdaptiveCircuit.relabel_tCount,W15.fastBodyProgram_tCount]
    have h := Width15Fused.fastCount_upper
    omega
  zero := by
    intro start
    rw [W15.compactProgram,WEXUnlookup.residue_relabel]
    exact (W15.fastBodyProgram_credit start).1
  count_eq := by
    intro start
    rw [W15.compactProgram,AndGadget.added_relabel]
    exact (W15.fastBodyProgram_credit start).2

def narrow14 : ModNarrow body2 14 where
  records := 1659546
  tBound := 15844248
  credit := 2 * ECDSAAdd.toffoliCount (ECDSAAdd.Baselines.normalizeProgram WEX.fastWindowSignProgram) +
    WEXUnlookupWidth14.ccx row2
  program := W14.compactProgram
  coherent := by
    intro coeffs Q hQ hn halias start history
    have ha : WEX.WidthAliased 14 coeffs := by simpa only [WEX.WidthAliased, ModAliased, reducedAddress] using halias
    exact relabel2_coherent _ coeffs Q history (W14.fastBodyProgram_coherent coeffs Q hQ hn ha start history)
  wellFormed := fun start => (relabelStraight_wellFormed pi (W14.fastBodyProgram start)).mpr
    (W14.fastBodyProgram_wellFormed start)
  slots := fun start => (relabelStraight_slots pi (W14.fastBodyProgram start)).trans_le
    ((W14.fastBodyProgram_slots_upper start).trans (by show (1100000000 : Nat) ≤ 2000000000; decide))
  wires := fun start => relabel2_support _ (W14.fastBodyProgram_support start)
  tCount := by
    intro start read history
    rw [W14.compactProgram,relabelStraight_instantiate,AdaptiveCircuit.relabel_tCount,W14.fastBodyProgram_tCount]
    have h := WEXUnlookupWidth14.Fused.fastCount_upper
    omega
  zero := by
    intro start
    rw [W14.compactProgram,WEXUnlookup.residue_relabel]
    exact (W14.fastBodyProgram_credit start).1
  count_eq := by
    intro start
    rw [W14.compactProgram,AndGadget.added_relabel]
    exact (W14.fastBodyProgram_credit start).2

theorem alias13_14 (coeffs : Fin 32768 → PointCoeff) (h : ModAliased 13 coeffs) : ModAliased 14 coeffs := by
  intro a
  have e : reducedAddress 13 (reducedAddress 14 a) = reducedAddress 13 a := by
    apply Fin.ext
    simp only [reducedAddress]
    omega
  rw [h a, h (reducedAddress 14 a), e]

/-- No 14-bit physical windows are scheduled; the width-14 program serves them as well. -/
def narrow13 : ModNarrow body2 13 where
  records := narrow14.records
  tBound := narrow14.tBound
  credit := narrow14.credit
  program := narrow14.program
  coherent := fun coeffs Q hQ hn halias start history =>
    narrow14.coherent coeffs Q hQ hn (alias13_14 coeffs halias) start history
  wellFormed := narrow14.wellFormed
  slots := narrow14.slots
  wires := narrow14.wires
  tCount := narrow14.tCount
  zero := narrow14.zero
  count_eq := narrow14.count_eq

theorem body2_ledger : body2.support.length = 1619 ∧ body2.reset.length = 854 := by
  constructor
  · simp [body2]
  · simp [body2, resetWires]

end
end ShorECDLP.Entrant.PathShare
