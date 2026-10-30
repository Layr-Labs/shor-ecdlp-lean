# WEX skeleton interface — 2026-10-30

Status: initial contract, before the first remote elaboration. This exact declaration
is committed in the skeleton stream. Later corrections will be appended with dates.
The frozen interface is `ShorECDLP.Entrant.Single.WindowBody` below.

The body consumes a local 32,768-row coefficient reader. The skeleton reindexes
every field with `signedRow w`; it supplies the initial table, signed-digit offsets,
Fourier preparation, semiclassical feedback, sparse positions, terminal reset, and
protected nearest-pair decoder. The selected table point must be nonzero for the
semantic theorem; resource bounds hold for every Q and every coefficient reader.

## Port conventions

Canonical x is wires 263 through 518 in little-endian order; y is 580 through 835;
infinity is 838, with the Streaming polarity (true means infinity). Fourier/address
bank is 855 through 870: magnitude wires 855 through 869, sign 870. For a 15-bit
signed digit, wire 869 is zero padding and the logical bank is 855 through 868 then
870. For a 16-bit signed digit all sixteen wires participate.

The persistent QROM control is 836 and is true on the skeleton invariant. The full
coherent law states its conditional action explicitly. Sign true means +C, sign
false means -C. The program includes signed-address preparation and its inverse,
and any two sign negations needed to turn an unsigned finite-addend body into this
signed contract. The raw Fourier digit is in the bank on entry and is restored.
The prepared selected address is `signedTableAddress 32768 (windowRawDigit 0 s)`.

Native arithmetic must be renamed onto these ports before constructing `WindowBody`.
In particular, the ecdsa finite flag has the opposite polarity to Streaming infinity;
the body adapter must perform the free flag inversions. Work wires may be chosen
freely outside the declared ports. `ready` states their cleanliness. It must survive
point writes and arbitrary bank-bit writes, and follow every initial direct load.
The coherent state map restores every wire outside the point ports. Thus the
contract is coherent across different addresses and inputs, with no per-address
choice of branch coefficients.

The initial lookup uses path wires 519 through 534. The inherited static skeleton
support is `completeBatchedSupport` (855 wires); the first version requires it inside
the body's declared support. This conservative support requirement may be reduced
by a dated additive interface extension. `reset` is independently chosen, with its
exact length included in records and its wires included in support. It need not
reset clean arithmetic scratch a second time.

## Exact Lean declaration

```lean
/-- Canonical ports: accumulator x=263..518, y=580..835, infinity=838;
address=855..869, sign=870, persistent lookup control=836. Programs include
signed-address preparation and the two sign conjugations. -/
structure WindowBody where
  records : Nat
  tBound : Nat
  slotBound : Nat
  support : List Wire
  reset : List Wire
  ready : BasisState → Prop
  active : ∀ s, ready s → s 836 = true
  ready_write : ∀ P s, ready s → ready (pointWrite P s)
  ready_address : ∀ s, ready s → ∀ v ∈ streamAddress, ∀ bit, ready (s[v ↦ bit])
  ready_first : ∀ s, FirstWindowInput s → ∀ P, ready (pointWrite P s)
  program : (start : Nat) → Straight 32768 start (start + records)
  update : (Fin 32768 → PointCoeff) → Point → BasisState → BasisState
  correct : ∀ coeffs Q, order • Q = 0 → (∀ a, constantPoint Q (coeffs a) ≠ 0) →
    ∀ s, ready s → ∀ P, pointStateCoordinates s = fig14PointEncoding P →
      update coeffs Q s = pointWrite
        (P + if s 836 then
          (if s 870 then constantPoint Q (coeffs ⟨signedTableAddress 32768
            (windowRawDigit 0 s), signedTableAddress_bound 32768 _ (windowRawDigit_bound 0 s)⟩)
           else -constantPoint Q (coeffs ⟨signedTableAddress 32768
            (windowRawDigit 0 s), signedTableAddress_bound 32768 _ (windowRawDigit_bound 0 s)⟩))
          else 0) s
  coherent : ∀ coeffs Q, order • Q = 0 → (∀ a, constantPoint Q (coeffs a) ≠ 0) →
    ∀ start history, CoherentlyImplementsOn
      ((program start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (update coeffs Q))
      (fun s => ready s ∧ ∃ P, pointStateCoordinates s = fig14PointEncoding P)
  wellFormed : ∀ start, (program start).WellFormed
  slots : ∀ start, (program start).gateSlots ≤ slotBound
  tCount : ∀ coeffs Q start history,
    ((program start).instantiate (readConstant coeffs Q) history).tCount ≤ tBound
  wires : ∀ start, straightWires (program start) ⊆ support
  reset_support : reset ⊆ support
  skeleton_support : completeBatchedSupport ⊆ support

/-- A body may demand its own clean work bank; its point coordinates remain explicit. -/
def BodyValid (b : WindowBody) (s : BasisState) : Prop :=
  b.ready s ∧ ∃ P, pointStateCoordinates s = fig14PointEncoding P
```

## Resource formulas

Let R = body.records, M = body.reset.length, T = body.tBound, S = body.slotBound.
There is one first load and 33 signed bodies. The left cursor advances by
65,535 + 16R + 263, the right by 17R + 263. Total records are
65,535 + 33R + 526 + M. The T bound is 458,745 + 33T + 68,906.
The gate-slot bound is 34 * max(3,000,000,000, S) + 69,434.
The qubit upper bound is the declared support cardinality (deduplicated).
There are 851,968 table rows and one decoder candidate check.
Official-limit obligations are supplied to the final generic certificate theorem;
the body theorem cannot assert that arbitrary resource parameters fit the limits.

## Skeleton choice and lookup-width convention

The integration uses the requested 263/263 nearest-pair fallback. The existing
rounded wrapped-shift tree also uses 15-bit physical lookup addresses for its
16-bit signed digits. It does not actually double a physical traversal relative
to the full-width nearest-pair windows. A separate cost table will distinguish
logical signed widths from physical address widths and will retain both the
brief's 16-bit lookup interpretation and the source's 15-bit implementation.

2026-10-30 amendment 1: the unchanged structure is registered with
`attribute [class] WindowBody`. Generic declarations take `[b : WindowBody]`;
instantiate locally with `letI : WindowBody := body`, or use their explicit
`@` forms. The declared support bound used by the first implementation is
`body.support.length`; callers may supply a deduplicated list. The T ledger uses
separate tagged costs, so no restriction such as `body.records != 65535` is needed.

2026-10-30 amendment 2: the completed interface, generic certificate and regression
are bundled in `ShorECDLP.Submission.Entrant.Single.Skeleton` (one module).
The public semantic exports are `Single.Distribution.program_success` and
`Single.program_resource_facts`. The final theorem is:

```lean
theorem Single.certificate [b : Single.WindowBody]
    (hSlots : 34 * Single.windowSlots + 69434 ≤ officialLimits.gateSlots)
    (hRecords : 65535 + 33 * b.records + 526 + b.reset.length ≤ officialLimits.measurements) :
    Certificate officialLimits Single.layout Single.entry Single.bounds
```

Here `Single.windowSlots = max 3000000000 b.slotBound`, and `Single.bounds` is
`⟨b.support.length, 458745 + 33 * b.tBound + 68906,
65535 + 33 * b.records + 526 + b.reset.length⟩`.
The generic proof and the EEA regression root have passed remote builds.

2026-10-30 amendment 3 (29-window neighbor producer, implementation in progress):
`WindowBody` is unchanged, including its canonical ports and all readiness fields.
The port to c96133a0 uses 266/208 physical bits, 29 corrected additions and 55
explicit protected wrapped-shift trials sharing one left sample. Its table has
917,504 rows. The 34-window branch remains unchanged and verified.

The neighboring-word suffix requires reset wires 0 and 1. To preserve the body
structure while admitting the target's sharper 854-wire EEA support, the port
adds a companion class `Single.ProducerResources (b : WindowBody)` with:
`support : List Wire`, `body_wires : ∀ start, straightWires (b.program start) ⊆ support`,
`initial_support : resetWires ⊆ support`, `reset_support : b.reset ⊆ support`,
`reset_nodup : b.reset.Nodup`, `reset_zero : 0 ∈ b.reset`, `reset_one : 1 ∈ b.reset`.
This is additional producer evidence, not a modification of `WindowBody`. In
particular its support may be smaller than `b.support` when a stronger static
proof is available. WEX can use its existing support as the companion support.

For this producer the left cursor is `65535 + 16R + 266`; the right adds
`13R + 208`; the terminal reset adds M, and the neighbor suffix adds 34,114
records. Total records are `65535 + 29R + 474 + M + 34114`. The T bound is
`458745 + 29T + 56773`; the slot bound is
`30 * max(3000000000, S) + 176648`. The final certificate's support bound is
`ProducerResources.support.length`. The two generic compiler stages can be
applied after this producer and its layout have been constructed.

2026-10-30 amendment 4: the companion evidence has a convenience constructor
`ProducerResources.ofBody body reset_nodup reset_zero reset_one`, which reuses the
existing `body.support`, `body.wires` and support inclusion proofs. An adapter
already targeting the 34-window contract therefore only supplies the terminal
reset-list evidence for the new neighboring-word readout. The EEA regression
uses the same body contract with a sharper, separately proved 854-wire support.
The generic pre-compiler entry/certificate are named `Rounded.entry`,
`Rounded.layout`, `Rounded.bounds` and `Rounded.certificate` on the new branch.
The old 34-window `Single.certificate` remains available on its unchanged branch.

2026-10-30 amendment 5: `Single.neighbor_certificate` is a convenience export of
`Rounded.certificate` for the 29-addition producer. `Rounded.program_resource_facts`
exports the every-Q qubit/T bounds and exact record formula. The actual recorded
suffix is transported by `castFinish` from `start + 2 + 164*208` to
`start + 34114`; this does not add gates or records. The unchanged body structure
was checked byte-for-byte against the verified 34-window branch. The generic
neighbor certificate and the cancelled EEA body adapter have passed builds.

2026-10-30 amendment 6: the new producer, EEA regression root and both compiler
support exports now build. Bind companion instances to the chosen body instance
explicitly, as follows (the body structure itself is still unchanged):

```lean
local instance bodyInstance : Single.WindowBody := WEX.body
local instance resourcesInstance : Single.ProducerResources bodyInstance :=
  Single.ProducerResources.ofBody WEX.body reset_nodup reset_zero reset_one
```

`Rounded.compiler_within` proves the source-support premise of measured-AND
lowering, and `Rounded.lowered_within q` proves it after the first compiler.
The catalyst may then use a second wire fresh for that enlarged support. The
compiler's fresh wires are parameters; 1024/1025 are not reserved WEX ports.
The consolidated producer remains imported as
`ShorECDLP.Submission.Entrant.Single.Skeleton`; generic compiler interfaces are
imported as `ShorECDLP.Submission.Entrant.CompilerStage`.

2026-10-30 amendment 7 (compiler credit companion): `WindowBody` and
`ProducerResources` remain unchanged. The five-module assembly adds a separate
`WEXCredit.BodyCredit (body : Single.WindowBody) (count : Nat) : Prop`, with
`zero : ∀ start, AndGadget.residue (body.program start) = 0` and
`count_eq : ∀ start, AndGadget.added (body.program start) = count`.
The count is the actual emitted count after literal normalization. The companion
is passed explicitly; no readiness, port or coherent-update obligation changes.
`WEXCredit.windowBody_four_certificate` transports the 29-window producer through
both public compiler stages, using source credit `65535 + 29 * count`, Fourier
allowance 56773 and one T unit for Y-state preparation. Its remaining premises
are the existing producer budgets, two fresh wires, and the transformed slot and
record budgets. The resulting T bound is `4 * (65535 + 29 * count) + 56773 + 1`.
The arithmetic, traversal and sign-wrapper lemmas live in Main under
`ShorECDLP.Entrant.WEXCredit`, so they add no Entrant module. The unchanged
34-window contract remains usable by its existing instance.
